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
size_t v_x_1695__boxed_190_; size_t v_x_1696__boxed_191_; lean_object* v_res_192_; 
v_x_1695__boxed_190_ = lean_unbox_usize(v_x_186_);
lean_dec(v_x_186_);
v_x_1696__boxed_191_ = lean_unbox_usize(v_x_187_);
lean_dec(v_x_187_);
v_res_192_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg(v_x_185_, v_x_1695__boxed_190_, v_x_1696__boxed_191_, v_x_188_, v_x_189_);
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
lean_object* v___x_204_; lean_object* v_mctx_205_; lean_object* v_cache_206_; lean_object* v_zetaDeltaFVarIds_207_; lean_object* v_postponed_208_; lean_object* v_diag_209_; lean_object* v___x_211_; uint8_t v_isShared_212_; uint8_t v_isSharedCheck_238_; 
v___x_204_ = lean_st_ref_take(v___y_202_);
v_mctx_205_ = lean_ctor_get(v___x_204_, 0);
v_cache_206_ = lean_ctor_get(v___x_204_, 1);
v_zetaDeltaFVarIds_207_ = lean_ctor_get(v___x_204_, 2);
v_postponed_208_ = lean_ctor_get(v___x_204_, 3);
v_diag_209_ = lean_ctor_get(v___x_204_, 4);
v_isSharedCheck_238_ = !lean_is_exclusive(v___x_204_);
if (v_isSharedCheck_238_ == 0)
{
v___x_211_ = v___x_204_;
v_isShared_212_ = v_isSharedCheck_238_;
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
v_isShared_212_ = v_isSharedCheck_238_;
goto v_resetjp_210_;
}
v_resetjp_210_:
{
lean_object* v_depth_213_; lean_object* v_levelAssignDepth_214_; lean_object* v_lmvarCounter_215_; lean_object* v_mvarCounter_216_; lean_object* v_lDecls_217_; lean_object* v_decls_218_; lean_object* v_userNames_219_; lean_object* v_lAssignment_220_; lean_object* v_eAssignment_221_; lean_object* v_dAssignment_222_; lean_object* v_instanceTypedMVars_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_237_; 
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
v_isSharedCheck_237_ = !lean_is_exclusive(v_mctx_205_);
if (v_isSharedCheck_237_ == 0)
{
v___x_225_ = v_mctx_205_;
v_isShared_226_ = v_isSharedCheck_237_;
goto v_resetjp_224_;
}
else
{
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
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_237_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_230_; 
v___x_227_ = lean_box(0);
v___x_228_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0___redArg(v_eAssignment_221_, v_mvarId_200_, v_val_201_);
if (v_isShared_226_ == 0)
{
lean_ctor_set(v___x_225_, 8, v___x_228_);
v___x_230_ = v___x_225_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v_depth_213_);
lean_ctor_set(v_reuseFailAlloc_236_, 1, v_levelAssignDepth_214_);
lean_ctor_set(v_reuseFailAlloc_236_, 2, v_lmvarCounter_215_);
lean_ctor_set(v_reuseFailAlloc_236_, 3, v_mvarCounter_216_);
lean_ctor_set(v_reuseFailAlloc_236_, 4, v_lDecls_217_);
lean_ctor_set(v_reuseFailAlloc_236_, 5, v_decls_218_);
lean_ctor_set(v_reuseFailAlloc_236_, 6, v_userNames_219_);
lean_ctor_set(v_reuseFailAlloc_236_, 7, v_lAssignment_220_);
lean_ctor_set(v_reuseFailAlloc_236_, 8, v___x_228_);
lean_ctor_set(v_reuseFailAlloc_236_, 9, v_dAssignment_222_);
lean_ctor_set(v_reuseFailAlloc_236_, 10, v_instanceTypedMVars_223_);
v___x_230_ = v_reuseFailAlloc_236_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
lean_object* v___x_232_; 
if (v_isShared_212_ == 0)
{
lean_ctor_set(v___x_211_, 0, v___x_230_);
v___x_232_ = v___x_211_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v___x_230_);
lean_ctor_set(v_reuseFailAlloc_235_, 1, v_cache_206_);
lean_ctor_set(v_reuseFailAlloc_235_, 2, v_zetaDeltaFVarIds_207_);
lean_ctor_set(v_reuseFailAlloc_235_, 3, v_postponed_208_);
lean_ctor_set(v_reuseFailAlloc_235_, 4, v_diag_209_);
v___x_232_ = v_reuseFailAlloc_235_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_233_ = lean_st_ref_put(v___y_202_, v___x_232_);
v___x_234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_234_, 0, v___x_227_);
return v___x_234_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0___redArg___boxed(lean_object* v_mvarId_239_, lean_object* v_val_240_, lean_object* v___y_241_, lean_object* v___y_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0___redArg(v_mvarId_239_, v_val_240_, v___y_241_);
lean_dec(v___y_241_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetEq___lam__0(lean_object* v_mvarId_249_, lean_object* v___x_250_, lean_object* v_targetNew_251_, lean_object* v_eqProof_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_){
_start:
{
lean_object* v___x_258_; 
lean_inc(v_mvarId_249_);
v___x_258_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_249_, v___x_250_, v___y_253_, v___y_254_, v___y_255_, v___y_256_);
if (lean_obj_tag(v___x_258_) == 0)
{
lean_object* v___x_259_; 
lean_dec_ref_known(v___x_258_, 1);
lean_inc(v_mvarId_249_);
v___x_259_ = l_Lean_MVarId_getTag(v_mvarId_249_, v___y_253_, v___y_254_, v___y_255_, v___y_256_);
if (lean_obj_tag(v___x_259_) == 0)
{
lean_object* v_a_260_; lean_object* v___x_261_; 
v_a_260_ = lean_ctor_get(v___x_259_, 0);
lean_inc(v_a_260_);
lean_dec_ref_known(v___x_259_, 1);
lean_inc_ref(v_targetNew_251_);
v___x_261_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_targetNew_251_, v_a_260_, v___y_253_, v___y_254_, v___y_255_, v___y_256_);
if (lean_obj_tag(v___x_261_) == 0)
{
lean_object* v_a_262_; lean_object* v___x_263_; 
v_a_262_ = lean_ctor_get(v___x_261_, 0);
lean_inc(v_a_262_);
lean_dec_ref_known(v___x_261_, 1);
lean_inc(v_mvarId_249_);
v___x_263_ = l_Lean_MVarId_getType(v_mvarId_249_, v___y_253_, v___y_254_, v___y_255_, v___y_256_);
if (lean_obj_tag(v___x_263_) == 0)
{
lean_object* v_a_264_; lean_object* v___x_265_; 
v_a_264_ = lean_ctor_get(v___x_263_, 0);
lean_inc_n(v_a_264_, 2);
lean_dec_ref_known(v___x_263_, 1);
v___x_265_ = l_Lean_Meta_getLevel(v_a_264_, v___y_253_, v___y_254_, v___y_255_, v___y_256_);
if (lean_obj_tag(v___x_265_) == 0)
{
lean_object* v_a_266_; lean_object* v___x_267_; 
v_a_266_ = lean_ctor_get(v___x_265_, 0);
lean_inc(v_a_266_);
lean_dec_ref_known(v___x_265_, 1);
lean_inc_ref(v_targetNew_251_);
lean_inc(v_a_264_);
v___x_267_ = l_Lean_Meta_mkEq(v_a_264_, v_targetNew_251_, v___y_253_, v___y_254_, v___y_255_, v___y_256_);
if (lean_obj_tag(v___x_267_) == 0)
{
lean_object* v_a_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_289_; 
v_a_268_ = lean_ctor_get(v___x_267_, 0);
lean_inc(v_a_268_);
lean_dec_ref_known(v___x_267_, 1);
v___x_269_ = l_Lean_Meta_mkExpectedPropHint(v_eqProof_252_, v_a_268_);
v___x_270_ = ((lean_object*)(l_Lean_MVarId_replaceTargetEq___lam__0___closed__2));
v___x_271_ = lean_box(0);
v___x_272_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_272_, 0, v_a_266_);
lean_ctor_set(v___x_272_, 1, v___x_271_);
v___x_273_ = l_Lean_mkConst(v___x_270_, v___x_272_);
v___x_274_ = lean_unsigned_to_nat(4u);
v___x_275_ = lean_mk_empty_array_with_capacity(v___x_274_);
v___x_276_ = lean_array_push(v___x_275_, v_a_264_);
v___x_277_ = lean_array_push(v___x_276_, v_targetNew_251_);
v___x_278_ = lean_array_push(v___x_277_, v___x_269_);
lean_inc(v_a_262_);
v___x_279_ = lean_array_push(v___x_278_, v_a_262_);
v___x_280_ = l_Lean_mkAppN(v___x_273_, v___x_279_);
lean_dec_ref(v___x_279_);
v___x_281_ = l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0___redArg(v_mvarId_249_, v___x_280_, v___y_254_);
v_isSharedCheck_289_ = !lean_is_exclusive(v___x_281_);
if (v_isSharedCheck_289_ == 0)
{
lean_object* v_unused_290_; 
v_unused_290_ = lean_ctor_get(v___x_281_, 0);
lean_dec(v_unused_290_);
v___x_283_ = v___x_281_;
v_isShared_284_ = v_isSharedCheck_289_;
goto v_resetjp_282_;
}
else
{
lean_dec(v___x_281_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_289_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v___x_285_; lean_object* v___x_287_; 
v___x_285_ = l_Lean_Expr_mvarId_x21(v_a_262_);
lean_dec(v_a_262_);
if (v_isShared_284_ == 0)
{
lean_ctor_set(v___x_283_, 0, v___x_285_);
v___x_287_ = v___x_283_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v___x_285_);
v___x_287_ = v_reuseFailAlloc_288_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
return v___x_287_;
}
}
}
else
{
lean_object* v_a_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_298_; 
lean_dec(v_a_266_);
lean_dec(v_a_264_);
lean_dec(v_a_262_);
lean_dec_ref(v_eqProof_252_);
lean_dec_ref(v_targetNew_251_);
lean_dec(v_mvarId_249_);
v_a_291_ = lean_ctor_get(v___x_267_, 0);
v_isSharedCheck_298_ = !lean_is_exclusive(v___x_267_);
if (v_isSharedCheck_298_ == 0)
{
v___x_293_ = v___x_267_;
v_isShared_294_ = v_isSharedCheck_298_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_a_291_);
lean_dec(v___x_267_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_298_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v___x_296_; 
if (v_isShared_294_ == 0)
{
v___x_296_ = v___x_293_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v_a_291_);
v___x_296_ = v_reuseFailAlloc_297_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
return v___x_296_;
}
}
}
}
else
{
lean_object* v_a_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_306_; 
lean_dec(v_a_264_);
lean_dec(v_a_262_);
lean_dec_ref(v_eqProof_252_);
lean_dec_ref(v_targetNew_251_);
lean_dec(v_mvarId_249_);
v_a_299_ = lean_ctor_get(v___x_265_, 0);
v_isSharedCheck_306_ = !lean_is_exclusive(v___x_265_);
if (v_isSharedCheck_306_ == 0)
{
v___x_301_ = v___x_265_;
v_isShared_302_ = v_isSharedCheck_306_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_a_299_);
lean_dec(v___x_265_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_306_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
lean_object* v___x_304_; 
if (v_isShared_302_ == 0)
{
v___x_304_ = v___x_301_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v_a_299_);
v___x_304_ = v_reuseFailAlloc_305_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
return v___x_304_;
}
}
}
}
else
{
lean_object* v_a_307_; lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_314_; 
lean_dec(v_a_262_);
lean_dec_ref(v_eqProof_252_);
lean_dec_ref(v_targetNew_251_);
lean_dec(v_mvarId_249_);
v_a_307_ = lean_ctor_get(v___x_263_, 0);
v_isSharedCheck_314_ = !lean_is_exclusive(v___x_263_);
if (v_isSharedCheck_314_ == 0)
{
v___x_309_ = v___x_263_;
v_isShared_310_ = v_isSharedCheck_314_;
goto v_resetjp_308_;
}
else
{
lean_inc(v_a_307_);
lean_dec(v___x_263_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_314_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
lean_object* v___x_312_; 
if (v_isShared_310_ == 0)
{
v___x_312_ = v___x_309_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v_a_307_);
v___x_312_ = v_reuseFailAlloc_313_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
return v___x_312_;
}
}
}
}
else
{
lean_object* v_a_315_; lean_object* v___x_317_; uint8_t v_isShared_318_; uint8_t v_isSharedCheck_322_; 
lean_dec_ref(v_eqProof_252_);
lean_dec_ref(v_targetNew_251_);
lean_dec(v_mvarId_249_);
v_a_315_ = lean_ctor_get(v___x_261_, 0);
v_isSharedCheck_322_ = !lean_is_exclusive(v___x_261_);
if (v_isSharedCheck_322_ == 0)
{
v___x_317_ = v___x_261_;
v_isShared_318_ = v_isSharedCheck_322_;
goto v_resetjp_316_;
}
else
{
lean_inc(v_a_315_);
lean_dec(v___x_261_);
v___x_317_ = lean_box(0);
v_isShared_318_ = v_isSharedCheck_322_;
goto v_resetjp_316_;
}
v_resetjp_316_:
{
lean_object* v___x_320_; 
if (v_isShared_318_ == 0)
{
v___x_320_ = v___x_317_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v_a_315_);
v___x_320_ = v_reuseFailAlloc_321_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
return v___x_320_;
}
}
}
}
else
{
lean_object* v_a_323_; lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_330_; 
lean_dec_ref(v_eqProof_252_);
lean_dec_ref(v_targetNew_251_);
lean_dec(v_mvarId_249_);
v_a_323_ = lean_ctor_get(v___x_259_, 0);
v_isSharedCheck_330_ = !lean_is_exclusive(v___x_259_);
if (v_isSharedCheck_330_ == 0)
{
v___x_325_ = v___x_259_;
v_isShared_326_ = v_isSharedCheck_330_;
goto v_resetjp_324_;
}
else
{
lean_inc(v_a_323_);
lean_dec(v___x_259_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_330_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
lean_object* v___x_328_; 
if (v_isShared_326_ == 0)
{
v___x_328_ = v___x_325_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v_a_323_);
v___x_328_ = v_reuseFailAlloc_329_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
return v___x_328_;
}
}
}
}
else
{
lean_object* v_a_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_338_; 
lean_dec_ref(v_eqProof_252_);
lean_dec_ref(v_targetNew_251_);
lean_dec(v_mvarId_249_);
v_a_331_ = lean_ctor_get(v___x_258_, 0);
v_isSharedCheck_338_ = !lean_is_exclusive(v___x_258_);
if (v_isSharedCheck_338_ == 0)
{
v___x_333_ = v___x_258_;
v_isShared_334_ = v_isSharedCheck_338_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_a_331_);
lean_dec(v___x_258_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_338_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v___x_336_; 
if (v_isShared_334_ == 0)
{
v___x_336_ = v___x_333_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v_a_331_);
v___x_336_ = v_reuseFailAlloc_337_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
return v___x_336_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetEq___lam__0___boxed(lean_object* v_mvarId_339_, lean_object* v___x_340_, lean_object* v_targetNew_341_, lean_object* v_eqProof_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Lean_MVarId_replaceTargetEq___lam__0(v_mvarId_339_, v___x_340_, v_targetNew_341_, v_eqProof_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_);
lean_dec(v___y_346_);
lean_dec_ref(v___y_345_);
lean_dec(v___y_344_);
lean_dec_ref(v___y_343_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetEq(lean_object* v_mvarId_352_, lean_object* v_targetNew_353_, lean_object* v_eqProof_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_){
_start:
{
lean_object* v___x_360_; lean_object* v___f_361_; lean_object* v___x_362_; 
v___x_360_ = ((lean_object*)(l_Lean_MVarId_replaceTargetEq___closed__1));
lean_inc(v_mvarId_352_);
v___f_361_ = lean_alloc_closure((void*)(l_Lean_MVarId_replaceTargetEq___lam__0___boxed), 9, 4);
lean_closure_set(v___f_361_, 0, v_mvarId_352_);
lean_closure_set(v___f_361_, 1, v___x_360_);
lean_closure_set(v___f_361_, 2, v_targetNew_353_);
lean_closure_set(v___f_361_, 3, v_eqProof_354_);
v___x_362_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(v_mvarId_352_, v___f_361_, v_a_355_, v_a_356_, v_a_357_, v_a_358_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetEq___boxed(lean_object* v_mvarId_363_, lean_object* v_targetNew_364_, lean_object* v_eqProof_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Lean_MVarId_replaceTargetEq(v_mvarId_363_, v_targetNew_364_, v_eqProof_365_, v_a_366_, v_a_367_, v_a_368_, v_a_369_);
lean_dec(v_a_369_);
lean_dec_ref(v_a_368_);
lean_dec(v_a_367_);
lean_dec_ref(v_a_366_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0(lean_object* v_mvarId_372_, lean_object* v_val_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_){
_start:
{
lean_object* v___x_379_; 
v___x_379_ = l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0___redArg(v_mvarId_372_, v_val_373_, v___y_375_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0___boxed(lean_object* v_mvarId_380_, lean_object* v_val_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0(v_mvarId_380_, v_val_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_);
lean_dec(v___y_385_);
lean_dec_ref(v___y_384_);
lean_dec(v___y_383_);
lean_dec_ref(v___y_382_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0(lean_object* v_00_u03b2_388_, lean_object* v_x_389_, lean_object* v_x_390_, lean_object* v_x_391_){
_start:
{
lean_object* v___x_392_; 
v___x_392_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0___redArg(v_x_389_, v_x_390_, v_x_391_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_393_, lean_object* v_x_394_, size_t v_x_395_, size_t v_x_396_, lean_object* v_x_397_, lean_object* v_x_398_){
_start:
{
lean_object* v___x_399_; 
v___x_399_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg(v_x_394_, v_x_395_, v_x_396_, v_x_397_, v_x_398_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_400_, lean_object* v_x_401_, lean_object* v_x_402_, lean_object* v_x_403_, lean_object* v_x_404_, lean_object* v_x_405_){
_start:
{
size_t v_x_2146__boxed_406_; size_t v_x_2147__boxed_407_; lean_object* v_res_408_; 
v_x_2146__boxed_406_ = lean_unbox_usize(v_x_402_);
lean_dec(v_x_402_);
v_x_2147__boxed_407_ = lean_unbox_usize(v_x_403_);
lean_dec(v_x_403_);
v_res_408_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2(v_00_u03b2_400_, v_x_401_, v_x_2146__boxed_406_, v_x_2147__boxed_407_, v_x_404_, v_x_405_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_409_, lean_object* v_n_410_, lean_object* v_k_411_, lean_object* v_v_412_){
_start:
{
lean_object* v___x_413_; 
v___x_413_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__3___redArg(v_n_410_, v_k_411_, v_v_412_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_414_, size_t v_depth_415_, lean_object* v_keys_416_, lean_object* v_vals_417_, lean_object* v_heq_418_, lean_object* v_i_419_, lean_object* v_entries_420_){
_start:
{
lean_object* v___x_421_; 
v___x_421_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_415_, v_keys_416_, v_vals_417_, v_i_419_, v_entries_420_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03b2_422_, lean_object* v_depth_423_, lean_object* v_keys_424_, lean_object* v_vals_425_, lean_object* v_heq_426_, lean_object* v_i_427_, lean_object* v_entries_428_){
_start:
{
size_t v_depth_boxed_429_; lean_object* v_res_430_; 
v_depth_boxed_429_ = lean_unbox_usize(v_depth_423_);
lean_dec(v_depth_423_);
v_res_430_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__4(v_00_u03b2_422_, v_depth_boxed_429_, v_keys_424_, v_vals_425_, v_heq_426_, v_i_427_, v_entries_428_);
lean_dec_ref(v_vals_425_);
lean_dec_ref(v_keys_424_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_431_, lean_object* v_x_432_, lean_object* v_x_433_, lean_object* v_x_434_, lean_object* v_x_435_){
_start:
{
lean_object* v___x_436_; 
v___x_436_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v_x_432_, v_x_433_, v_x_434_, v_x_435_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_replaceTargetDefEq_spec__0___redArg(lean_object* v_e_437_, lean_object* v___y_438_){
_start:
{
uint8_t v___x_440_; 
v___x_440_ = l_Lean_Expr_hasMVar(v_e_437_);
if (v___x_440_ == 0)
{
lean_object* v___x_441_; 
v___x_441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_441_, 0, v_e_437_);
return v___x_441_;
}
else
{
lean_object* v___x_442_; lean_object* v_mctx_443_; lean_object* v___x_444_; lean_object* v_fst_445_; lean_object* v_snd_446_; lean_object* v___x_447_; lean_object* v_cache_448_; lean_object* v_zetaDeltaFVarIds_449_; lean_object* v_postponed_450_; lean_object* v_diag_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_460_; 
v___x_442_ = lean_st_ref_get(v___y_438_);
v_mctx_443_ = lean_ctor_get(v___x_442_, 0);
lean_inc_ref(v_mctx_443_);
lean_dec(v___x_442_);
v___x_444_ = l_Lean_instantiateMVarsCore(v_mctx_443_, v_e_437_);
v_fst_445_ = lean_ctor_get(v___x_444_, 0);
lean_inc(v_fst_445_);
v_snd_446_ = lean_ctor_get(v___x_444_, 1);
lean_inc(v_snd_446_);
lean_dec_ref(v___x_444_);
v___x_447_ = lean_st_ref_take(v___y_438_);
v_cache_448_ = lean_ctor_get(v___x_447_, 1);
v_zetaDeltaFVarIds_449_ = lean_ctor_get(v___x_447_, 2);
v_postponed_450_ = lean_ctor_get(v___x_447_, 3);
v_diag_451_ = lean_ctor_get(v___x_447_, 4);
v_isSharedCheck_460_ = !lean_is_exclusive(v___x_447_);
if (v_isSharedCheck_460_ == 0)
{
lean_object* v_unused_461_; 
v_unused_461_ = lean_ctor_get(v___x_447_, 0);
lean_dec(v_unused_461_);
v___x_453_ = v___x_447_;
v_isShared_454_ = v_isSharedCheck_460_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_diag_451_);
lean_inc(v_postponed_450_);
lean_inc(v_zetaDeltaFVarIds_449_);
lean_inc(v_cache_448_);
lean_dec(v___x_447_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_460_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___x_456_; 
if (v_isShared_454_ == 0)
{
lean_ctor_set(v___x_453_, 0, v_snd_446_);
v___x_456_ = v___x_453_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v_snd_446_);
lean_ctor_set(v_reuseFailAlloc_459_, 1, v_cache_448_);
lean_ctor_set(v_reuseFailAlloc_459_, 2, v_zetaDeltaFVarIds_449_);
lean_ctor_set(v_reuseFailAlloc_459_, 3, v_postponed_450_);
lean_ctor_set(v_reuseFailAlloc_459_, 4, v_diag_451_);
v___x_456_ = v_reuseFailAlloc_459_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_457_ = lean_st_ref_put(v___y_438_, v___x_456_);
v___x_458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_458_, 0, v_fst_445_);
return v___x_458_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_replaceTargetDefEq_spec__0___redArg___boxed(lean_object* v_e_462_, lean_object* v___y_463_, lean_object* v___y_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l_Lean_instantiateMVars___at___00Lean_MVarId_replaceTargetDefEq_spec__0___redArg(v_e_462_, v___y_463_);
lean_dec(v___y_463_);
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_replaceTargetDefEq_spec__0(lean_object* v_e_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_){
_start:
{
lean_object* v___x_472_; 
v___x_472_ = l_Lean_instantiateMVars___at___00Lean_MVarId_replaceTargetDefEq_spec__0___redArg(v_e_466_, v___y_468_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_replaceTargetDefEq_spec__0___boxed(lean_object* v_e_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_){
_start:
{
lean_object* v_res_479_; 
v_res_479_ = l_Lean_instantiateMVars___at___00Lean_MVarId_replaceTargetDefEq_spec__0(v_e_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_);
lean_dec(v___y_477_);
lean_dec_ref(v___y_476_);
lean_dec(v___y_475_);
lean_dec_ref(v___y_474_);
return v_res_479_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetDefEq___lam__0(lean_object* v_mvarId_480_, lean_object* v___x_481_, lean_object* v_targetNew_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_){
_start:
{
lean_object* v___x_488_; 
lean_inc(v_mvarId_480_);
v___x_488_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_480_, v___x_481_, v___y_483_, v___y_484_, v___y_485_, v___y_486_);
if (lean_obj_tag(v___x_488_) == 0)
{
lean_object* v___x_489_; 
lean_dec_ref_known(v___x_488_, 1);
lean_inc(v_mvarId_480_);
v___x_489_ = l_Lean_MVarId_getType(v_mvarId_480_, v___y_483_, v___y_484_, v___y_485_, v___y_486_);
if (lean_obj_tag(v___x_489_) == 0)
{
lean_object* v_a_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_560_; 
v_a_490_ = lean_ctor_get(v___x_489_, 0);
v_isSharedCheck_560_ = !lean_is_exclusive(v___x_489_);
if (v_isSharedCheck_560_ == 0)
{
v___x_492_ = v___x_489_;
v_isShared_493_ = v_isSharedCheck_560_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_a_490_);
lean_dec(v___x_489_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_560_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
uint8_t v___x_494_; 
v___x_494_ = lean_expr_equal(v_a_490_, v_targetNew_482_);
if (v___x_494_ == 0)
{
lean_object* v___x_495_; lean_object* v_a_496_; lean_object* v___x_497_; lean_object* v_a_498_; uint8_t v___x_499_; 
lean_del_object(v___x_492_);
v___x_495_ = l_Lean_instantiateMVars___at___00Lean_MVarId_replaceTargetDefEq_spec__0___redArg(v_a_490_, v___y_484_);
v_a_496_ = lean_ctor_get(v___x_495_, 0);
lean_inc(v_a_496_);
lean_dec_ref(v___x_495_);
v___x_497_ = l_Lean_instantiateMVars___at___00Lean_MVarId_replaceTargetDefEq_spec__0___redArg(v_targetNew_482_, v___y_484_);
v_a_498_ = lean_ctor_get(v___x_497_, 0);
lean_inc(v_a_498_);
lean_dec_ref(v___x_497_);
v___x_499_ = lean_expr_equal(v_a_496_, v_a_498_);
if (v___x_499_ == 0)
{
lean_object* v___x_500_; 
lean_inc(v_mvarId_480_);
v___x_500_ = l_Lean_MVarId_getTag(v_mvarId_480_, v___y_483_, v___y_484_, v___y_485_, v___y_486_);
if (lean_obj_tag(v___x_500_) == 0)
{
lean_object* v_a_501_; lean_object* v___x_502_; 
v_a_501_ = lean_ctor_get(v___x_500_, 0);
lean_inc(v_a_501_);
lean_dec_ref_known(v___x_500_, 1);
v___x_502_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_498_, v_a_501_, v___y_483_, v___y_484_, v___y_485_, v___y_486_);
if (lean_obj_tag(v___x_502_) == 0)
{
lean_object* v_a_503_; lean_object* v___x_504_; 
v_a_503_ = lean_ctor_get(v___x_502_, 0);
lean_inc_n(v_a_503_, 2);
lean_dec_ref_known(v___x_502_, 1);
v___x_504_ = l_Lean_Meta_mkExpectedTypeHint(v_a_503_, v_a_496_, v___y_483_, v___y_484_, v___y_485_, v___y_486_);
if (lean_obj_tag(v___x_504_) == 0)
{
lean_object* v_a_505_; lean_object* v___x_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_514_; 
v_a_505_ = lean_ctor_get(v___x_504_, 0);
lean_inc(v_a_505_);
lean_dec_ref_known(v___x_504_, 1);
v___x_506_ = l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0___redArg(v_mvarId_480_, v_a_505_, v___y_484_);
v_isSharedCheck_514_ = !lean_is_exclusive(v___x_506_);
if (v_isSharedCheck_514_ == 0)
{
lean_object* v_unused_515_; 
v_unused_515_ = lean_ctor_get(v___x_506_, 0);
lean_dec(v_unused_515_);
v___x_508_ = v___x_506_;
v_isShared_509_ = v_isSharedCheck_514_;
goto v_resetjp_507_;
}
else
{
lean_dec(v___x_506_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_514_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_510_; lean_object* v___x_512_; 
v___x_510_ = l_Lean_Expr_mvarId_x21(v_a_503_);
lean_dec(v_a_503_);
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 0, v___x_510_);
v___x_512_ = v___x_508_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v___x_510_);
v___x_512_ = v_reuseFailAlloc_513_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
return v___x_512_;
}
}
}
else
{
lean_object* v_a_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_523_; 
lean_dec(v_a_503_);
lean_dec(v_mvarId_480_);
v_a_516_ = lean_ctor_get(v___x_504_, 0);
v_isSharedCheck_523_ = !lean_is_exclusive(v___x_504_);
if (v_isSharedCheck_523_ == 0)
{
v___x_518_ = v___x_504_;
v_isShared_519_ = v_isSharedCheck_523_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_a_516_);
lean_dec(v___x_504_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_523_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
lean_object* v___x_521_; 
if (v_isShared_519_ == 0)
{
v___x_521_ = v___x_518_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v_a_516_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
return v___x_521_;
}
}
}
}
else
{
lean_object* v_a_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_531_; 
lean_dec(v_a_496_);
lean_dec(v_mvarId_480_);
v_a_524_ = lean_ctor_get(v___x_502_, 0);
v_isSharedCheck_531_ = !lean_is_exclusive(v___x_502_);
if (v_isSharedCheck_531_ == 0)
{
v___x_526_ = v___x_502_;
v_isShared_527_ = v_isSharedCheck_531_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_a_524_);
lean_dec(v___x_502_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_531_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v___x_529_; 
if (v_isShared_527_ == 0)
{
v___x_529_ = v___x_526_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v_a_524_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
}
}
else
{
lean_object* v_a_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_539_; 
lean_dec(v_a_498_);
lean_dec(v_a_496_);
lean_dec(v_mvarId_480_);
v_a_532_ = lean_ctor_get(v___x_500_, 0);
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_500_);
if (v_isSharedCheck_539_ == 0)
{
v___x_534_ = v___x_500_;
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_a_532_);
lean_dec(v___x_500_);
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
lean_dec(v_a_498_);
lean_inc(v_mvarId_480_);
v___x_540_ = l_Lean_MVarId_setType___redArg(v_mvarId_480_, v_a_496_, v___y_484_);
if (lean_obj_tag(v___x_540_) == 0)
{
lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_547_; 
v_isSharedCheck_547_ = !lean_is_exclusive(v___x_540_);
if (v_isSharedCheck_547_ == 0)
{
lean_object* v_unused_548_; 
v_unused_548_ = lean_ctor_get(v___x_540_, 0);
lean_dec(v_unused_548_);
v___x_542_ = v___x_540_;
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
else
{
lean_dec(v___x_540_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_545_; 
if (v_isShared_543_ == 0)
{
lean_ctor_set(v___x_542_, 0, v_mvarId_480_);
v___x_545_ = v___x_542_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v_mvarId_480_);
v___x_545_ = v_reuseFailAlloc_546_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
return v___x_545_;
}
}
}
else
{
lean_object* v_a_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_556_; 
lean_dec(v_mvarId_480_);
v_a_549_ = lean_ctor_get(v___x_540_, 0);
v_isSharedCheck_556_ = !lean_is_exclusive(v___x_540_);
if (v_isSharedCheck_556_ == 0)
{
v___x_551_ = v___x_540_;
v_isShared_552_ = v_isSharedCheck_556_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_a_549_);
lean_dec(v___x_540_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_556_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v___x_554_; 
if (v_isShared_552_ == 0)
{
v___x_554_ = v___x_551_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v_a_549_);
v___x_554_ = v_reuseFailAlloc_555_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
return v___x_554_;
}
}
}
}
}
else
{
lean_object* v___x_558_; 
lean_dec(v_a_490_);
lean_dec_ref(v_targetNew_482_);
if (v_isShared_493_ == 0)
{
lean_ctor_set(v___x_492_, 0, v_mvarId_480_);
v___x_558_ = v___x_492_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v_mvarId_480_);
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
lean_object* v_a_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_568_; 
lean_dec_ref(v_targetNew_482_);
lean_dec(v_mvarId_480_);
v_a_561_ = lean_ctor_get(v___x_489_, 0);
v_isSharedCheck_568_ = !lean_is_exclusive(v___x_489_);
if (v_isSharedCheck_568_ == 0)
{
v___x_563_ = v___x_489_;
v_isShared_564_ = v_isSharedCheck_568_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_a_561_);
lean_dec(v___x_489_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_568_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v___x_566_; 
if (v_isShared_564_ == 0)
{
v___x_566_ = v___x_563_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v_a_561_);
v___x_566_ = v_reuseFailAlloc_567_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
return v___x_566_;
}
}
}
}
else
{
lean_object* v_a_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_576_; 
lean_dec_ref(v_targetNew_482_);
lean_dec(v_mvarId_480_);
v_a_569_ = lean_ctor_get(v___x_488_, 0);
v_isSharedCheck_576_ = !lean_is_exclusive(v___x_488_);
if (v_isSharedCheck_576_ == 0)
{
v___x_571_ = v___x_488_;
v_isShared_572_ = v_isSharedCheck_576_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_a_569_);
lean_dec(v___x_488_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_576_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
lean_object* v___x_574_; 
if (v_isShared_572_ == 0)
{
v___x_574_ = v___x_571_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v_a_569_);
v___x_574_ = v_reuseFailAlloc_575_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
return v___x_574_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetDefEq___lam__0___boxed(lean_object* v_mvarId_577_, lean_object* v___x_578_, lean_object* v_targetNew_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l_Lean_MVarId_replaceTargetDefEq___lam__0(v_mvarId_577_, v___x_578_, v_targetNew_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
lean_dec(v___y_583_);
lean_dec_ref(v___y_582_);
lean_dec(v___y_581_);
lean_dec_ref(v___y_580_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetDefEq(lean_object* v_mvarId_589_, lean_object* v_targetNew_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_){
_start:
{
lean_object* v___x_596_; lean_object* v___f_597_; lean_object* v___x_598_; 
v___x_596_ = ((lean_object*)(l_Lean_MVarId_replaceTargetDefEq___closed__1));
lean_inc(v_mvarId_589_);
v___f_597_ = lean_alloc_closure((void*)(l_Lean_MVarId_replaceTargetDefEq___lam__0___boxed), 8, 3);
lean_closure_set(v___f_597_, 0, v_mvarId_589_);
lean_closure_set(v___f_597_, 1, v___x_596_);
lean_closure_set(v___f_597_, 2, v_targetNew_590_);
v___x_598_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(v_mvarId_589_, v___f_597_, v_a_591_, v_a_592_, v_a_593_, v_a_594_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetDefEq___boxed(lean_object* v_mvarId_599_, lean_object* v_targetNew_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_){
_start:
{
lean_object* v_res_606_; 
v_res_606_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_599_, v_targetNew_600_, v_a_601_, v_a_602_, v_a_603_, v_a_604_);
lean_dec(v_a_604_);
lean_dec_ref(v_a_603_);
lean_dec(v_a_602_);
lean_dec_ref(v_a_601_);
return v_res_606_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replace___lam__0(lean_object* v_mvarId_607_, lean_object* v_fvarId_608_, lean_object* v_val_609_, lean_object* v_userName_x3f_610_, lean_object* v_type_x3f_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_){
_start:
{
lean_object* v___y_618_; lean_object* v_a_619_; lean_object* v_a_650_; 
if (lean_obj_tag(v_type_x3f_611_) == 0)
{
lean_object* v___x_663_; 
lean_inc(v___y_615_);
lean_inc_ref(v___y_614_);
lean_inc(v___y_613_);
lean_inc_ref(v___y_612_);
lean_inc_ref(v_val_609_);
v___x_663_ = lean_infer_type(v_val_609_, v___y_612_, v___y_613_, v___y_614_, v___y_615_);
if (lean_obj_tag(v___x_663_) == 0)
{
lean_object* v_a_664_; 
v_a_664_ = lean_ctor_get(v___x_663_, 0);
lean_inc(v_a_664_);
lean_dec_ref_known(v___x_663_, 1);
v_a_650_ = v_a_664_;
goto v___jp_649_;
}
else
{
lean_object* v_a_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_672_; 
lean_dec(v___y_615_);
lean_dec_ref(v___y_614_);
lean_dec(v___y_613_);
lean_dec_ref(v___y_612_);
lean_dec(v_userName_x3f_610_);
lean_dec_ref(v_val_609_);
lean_dec(v_fvarId_608_);
lean_dec(v_mvarId_607_);
v_a_665_ = lean_ctor_get(v___x_663_, 0);
v_isSharedCheck_672_ = !lean_is_exclusive(v___x_663_);
if (v_isSharedCheck_672_ == 0)
{
v___x_667_ = v___x_663_;
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_a_665_);
lean_dec(v___x_663_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v___x_670_; 
if (v_isShared_668_ == 0)
{
v___x_670_ = v___x_667_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_a_665_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
return v___x_670_;
}
}
}
}
else
{
lean_object* v_val_673_; 
v_val_673_ = lean_ctor_get(v_type_x3f_611_, 0);
lean_inc(v_val_673_);
lean_dec_ref_known(v_type_x3f_611_, 1);
v_a_650_ = v_val_673_;
goto v___jp_649_;
}
v___jp_617_:
{
lean_object* v___x_620_; 
lean_inc(v_fvarId_608_);
v___x_620_ = l_Lean_MVarId_assertAfter_x27(v_mvarId_607_, v_fvarId_608_, v_a_619_, v___y_618_, v_val_609_, v___y_612_, v___y_613_, v___y_614_, v___y_615_);
if (lean_obj_tag(v___x_620_) == 0)
{
lean_object* v_a_621_; lean_object* v_fvarId_622_; lean_object* v_mvarId_623_; lean_object* v_subst_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_648_; 
v_a_621_ = lean_ctor_get(v___x_620_, 0);
lean_inc(v_a_621_);
lean_dec_ref_known(v___x_620_, 1);
v_fvarId_622_ = lean_ctor_get(v_a_621_, 0);
v_mvarId_623_ = lean_ctor_get(v_a_621_, 1);
v_subst_624_ = lean_ctor_get(v_a_621_, 2);
v_isSharedCheck_648_ = !lean_is_exclusive(v_a_621_);
if (v_isSharedCheck_648_ == 0)
{
v___x_626_ = v_a_621_;
v_isShared_627_ = v_isSharedCheck_648_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_subst_624_);
lean_inc(v_mvarId_623_);
lean_inc(v_fvarId_622_);
lean_dec(v_a_621_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_648_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v___x_628_; 
v___x_628_ = l_Lean_MVarId_tryClear(v_mvarId_623_, v_fvarId_608_, v___y_612_, v___y_613_, v___y_614_, v___y_615_);
lean_dec(v___y_615_);
lean_dec_ref(v___y_614_);
lean_dec(v___y_613_);
lean_dec_ref(v___y_612_);
if (lean_obj_tag(v___x_628_) == 0)
{
lean_object* v_a_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_639_; 
v_a_629_ = lean_ctor_get(v___x_628_, 0);
v_isSharedCheck_639_ = !lean_is_exclusive(v___x_628_);
if (v_isSharedCheck_639_ == 0)
{
v___x_631_ = v___x_628_;
v_isShared_632_ = v_isSharedCheck_639_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_a_629_);
lean_dec(v___x_628_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_639_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v___x_634_; 
if (v_isShared_627_ == 0)
{
lean_ctor_set(v___x_626_, 1, v_a_629_);
v___x_634_ = v___x_626_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v_fvarId_622_);
lean_ctor_set(v_reuseFailAlloc_638_, 1, v_a_629_);
lean_ctor_set(v_reuseFailAlloc_638_, 2, v_subst_624_);
v___x_634_ = v_reuseFailAlloc_638_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
lean_object* v___x_636_; 
if (v_isShared_632_ == 0)
{
lean_ctor_set(v___x_631_, 0, v___x_634_);
v___x_636_ = v___x_631_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v___x_634_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
return v___x_636_;
}
}
}
}
else
{
lean_object* v_a_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_647_; 
lean_del_object(v___x_626_);
lean_dec(v_subst_624_);
lean_dec(v_fvarId_622_);
v_a_640_ = lean_ctor_get(v___x_628_, 0);
v_isSharedCheck_647_ = !lean_is_exclusive(v___x_628_);
if (v_isSharedCheck_647_ == 0)
{
v___x_642_ = v___x_628_;
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_a_640_);
lean_dec(v___x_628_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_645_; 
if (v_isShared_643_ == 0)
{
v___x_645_ = v___x_642_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_a_640_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
}
}
}
else
{
lean_dec(v___y_615_);
lean_dec_ref(v___y_614_);
lean_dec(v___y_613_);
lean_dec_ref(v___y_612_);
lean_dec(v_fvarId_608_);
return v___x_620_;
}
}
v___jp_649_:
{
if (lean_obj_tag(v_userName_x3f_610_) == 0)
{
lean_object* v___x_651_; 
lean_inc(v_fvarId_608_);
v___x_651_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_608_, v___y_612_, v___y_614_, v___y_615_);
if (lean_obj_tag(v___x_651_) == 0)
{
lean_object* v_a_652_; lean_object* v___x_653_; 
v_a_652_ = lean_ctor_get(v___x_651_, 0);
lean_inc(v_a_652_);
lean_dec_ref_known(v___x_651_, 1);
v___x_653_ = l_Lean_LocalDecl_userName(v_a_652_);
lean_dec(v_a_652_);
v___y_618_ = v_a_650_;
v_a_619_ = v___x_653_;
goto v___jp_617_;
}
else
{
lean_object* v_a_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_661_; 
lean_dec_ref(v_a_650_);
lean_dec(v___y_615_);
lean_dec_ref(v___y_614_);
lean_dec(v___y_613_);
lean_dec_ref(v___y_612_);
lean_dec_ref(v_val_609_);
lean_dec(v_fvarId_608_);
lean_dec(v_mvarId_607_);
v_a_654_ = lean_ctor_get(v___x_651_, 0);
v_isSharedCheck_661_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_661_ == 0)
{
v___x_656_ = v___x_651_;
v_isShared_657_ = v_isSharedCheck_661_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_a_654_);
lean_dec(v___x_651_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_661_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v___x_659_; 
if (v_isShared_657_ == 0)
{
v___x_659_ = v___x_656_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v_a_654_);
v___x_659_ = v_reuseFailAlloc_660_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
return v___x_659_;
}
}
}
}
else
{
lean_object* v_val_662_; 
v_val_662_ = lean_ctor_get(v_userName_x3f_610_, 0);
lean_inc(v_val_662_);
lean_dec_ref_known(v_userName_x3f_610_, 1);
v___y_618_ = v_a_650_;
v_a_619_ = v_val_662_;
goto v___jp_617_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replace___lam__0___boxed(lean_object* v_mvarId_674_, lean_object* v_fvarId_675_, lean_object* v_val_676_, lean_object* v_userName_x3f_677_, lean_object* v_type_x3f_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_){
_start:
{
lean_object* v_res_684_; 
v_res_684_ = l_Lean_MVarId_replace___lam__0(v_mvarId_674_, v_fvarId_675_, v_val_676_, v_userName_x3f_677_, v_type_x3f_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_);
return v_res_684_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replace(lean_object* v_mvarId_685_, lean_object* v_fvarId_686_, lean_object* v_val_687_, lean_object* v_type_x3f_688_, lean_object* v_userName_x3f_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_){
_start:
{
lean_object* v___f_695_; lean_object* v___x_696_; 
lean_inc(v_mvarId_685_);
v___f_695_ = lean_alloc_closure((void*)(l_Lean_MVarId_replace___lam__0___boxed), 10, 5);
lean_closure_set(v___f_695_, 0, v_mvarId_685_);
lean_closure_set(v___f_695_, 1, v_fvarId_686_);
lean_closure_set(v___f_695_, 2, v_val_687_);
lean_closure_set(v___f_695_, 3, v_userName_x3f_689_);
lean_closure_set(v___f_695_, 4, v_type_x3f_688_);
v___x_696_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(v_mvarId_685_, v___f_695_, v_a_690_, v_a_691_, v_a_692_, v_a_693_);
return v___x_696_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replace___boxed(lean_object* v_mvarId_697_, lean_object* v_fvarId_698_, lean_object* v_val_699_, lean_object* v_type_x3f_700_, lean_object* v_userName_x3f_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_){
_start:
{
lean_object* v_res_707_; 
v_res_707_ = l_Lean_MVarId_replace(v_mvarId_697_, v_fvarId_698_, v_val_699_, v_type_x3f_700_, v_userName_x3f_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_);
lean_dec(v_a_705_);
lean_dec_ref(v_a_704_);
lean_dec(v_a_703_);
lean_dec_ref(v_a_702_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceLocalDecl___lam__0(lean_object* v_eqProof_708_, lean_object* v___x_709_, lean_object* v_typeNew_710_, lean_object* v_mvarId_711_, lean_object* v_fvarId_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_){
_start:
{
lean_object* v___x_718_; 
v___x_718_ = l_Lean_Meta_mkEqMP(v_eqProof_708_, v___x_709_, v___y_713_, v___y_714_, v___y_715_, v___y_716_);
if (lean_obj_tag(v___x_718_) == 0)
{
lean_object* v_a_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
v_a_719_ = lean_ctor_get(v___x_718_, 0);
lean_inc(v_a_719_);
lean_dec_ref_known(v___x_718_, 1);
v___x_720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_720_, 0, v_typeNew_710_);
v___x_721_ = lean_box(0);
v___x_722_ = l_Lean_MVarId_replace(v_mvarId_711_, v_fvarId_712_, v_a_719_, v___x_720_, v___x_721_, v___y_713_, v___y_714_, v___y_715_, v___y_716_);
return v___x_722_;
}
else
{
lean_object* v_a_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_730_; 
lean_dec(v_fvarId_712_);
lean_dec(v_mvarId_711_);
lean_dec_ref(v_typeNew_710_);
v_a_723_ = lean_ctor_get(v___x_718_, 0);
v_isSharedCheck_730_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_730_ == 0)
{
v___x_725_ = v___x_718_;
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_a_723_);
lean_dec(v___x_718_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v___x_728_; 
if (v_isShared_726_ == 0)
{
v___x_728_ = v___x_725_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v_a_723_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
return v___x_728_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceLocalDecl___lam__0___boxed(lean_object* v_eqProof_731_, lean_object* v___x_732_, lean_object* v_typeNew_733_, lean_object* v_mvarId_734_, lean_object* v_fvarId_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_){
_start:
{
lean_object* v_res_741_; 
v_res_741_ = l_Lean_MVarId_replaceLocalDecl___lam__0(v_eqProof_731_, v___x_732_, v_typeNew_733_, v_mvarId_734_, v_fvarId_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_);
lean_dec(v___y_739_);
lean_dec_ref(v___y_738_);
lean_dec(v___y_737_);
lean_dec_ref(v___y_736_);
return v_res_741_;
}
}
static lean_object* _init_l_Lean_MVarId_replaceLocalDecl___closed__0(void){
_start:
{
lean_object* v___x_742_; 
v___x_742_ = l_instMonadEIO___redArg();
return v___x_742_;
}
}
static lean_object* _init_l_Lean_MVarId_replaceLocalDecl___closed__1(void){
_start:
{
lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_743_ = lean_obj_once(&l_Lean_MVarId_replaceLocalDecl___closed__0, &l_Lean_MVarId_replaceLocalDecl___closed__0_once, _init_l_Lean_MVarId_replaceLocalDecl___closed__0);
v___x_744_ = l_StateRefT_x27_instMonad___redArg(v___x_743_);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceLocalDecl(lean_object* v_mvarId_749_, lean_object* v_fvarId_750_, lean_object* v_typeNew_751_, lean_object* v_eqProof_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_){
_start:
{
lean_object* v___x_758_; lean_object* v_toApplicative_759_; lean_object* v_toFunctor_760_; lean_object* v_toSeq_761_; lean_object* v_toSeqLeft_762_; lean_object* v_toSeqRight_763_; lean_object* v___f_764_; lean_object* v___f_765_; lean_object* v___f_766_; lean_object* v___f_767_; lean_object* v___x_768_; lean_object* v___f_769_; lean_object* v___f_770_; lean_object* v___f_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v_toApplicative_777_; lean_object* v_toFunctor_778_; lean_object* v_toSeq_779_; lean_object* v_toSeqLeft_780_; lean_object* v_toSeqRight_781_; lean_object* v___f_782_; lean_object* v___f_783_; lean_object* v___x_784_; lean_object* v___f_785_; lean_object* v___f_786_; lean_object* v___f_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v_toApplicative_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_822_; 
v___x_758_ = lean_obj_once(&l_Lean_MVarId_replaceLocalDecl___closed__1, &l_Lean_MVarId_replaceLocalDecl___closed__1_once, _init_l_Lean_MVarId_replaceLocalDecl___closed__1);
v_toApplicative_759_ = lean_ctor_get(v___x_758_, 0);
v_toFunctor_760_ = lean_ctor_get(v_toApplicative_759_, 0);
v_toSeq_761_ = lean_ctor_get(v_toApplicative_759_, 2);
v_toSeqLeft_762_ = lean_ctor_get(v_toApplicative_759_, 3);
v_toSeqRight_763_ = lean_ctor_get(v_toApplicative_759_, 4);
v___f_764_ = ((lean_object*)(l_Lean_MVarId_replaceLocalDecl___closed__2));
v___f_765_ = ((lean_object*)(l_Lean_MVarId_replaceLocalDecl___closed__3));
lean_inc_ref_n(v_toFunctor_760_, 2);
v___f_766_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_766_, 0, v_toFunctor_760_);
v___f_767_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_767_, 0, v_toFunctor_760_);
v___x_768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_768_, 0, v___f_766_);
lean_ctor_set(v___x_768_, 1, v___f_767_);
lean_inc(v_toSeqRight_763_);
v___f_769_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_769_, 0, v_toSeqRight_763_);
lean_inc(v_toSeqLeft_762_);
v___f_770_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_770_, 0, v_toSeqLeft_762_);
lean_inc(v_toSeq_761_);
v___f_771_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_771_, 0, v_toSeq_761_);
v___x_772_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_772_, 0, v___x_768_);
lean_ctor_set(v___x_772_, 1, v___f_764_);
lean_ctor_set(v___x_772_, 2, v___f_771_);
lean_ctor_set(v___x_772_, 3, v___f_770_);
lean_ctor_set(v___x_772_, 4, v___f_769_);
v___x_773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_773_, 0, v___x_772_);
lean_ctor_set(v___x_773_, 1, v___f_765_);
v___x_774_ = l_StateRefT_x27_instMonad___redArg(v___x_773_);
v___x_775_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(v___x_775_, 0, lean_box(0));
lean_closure_set(v___x_775_, 1, lean_box(0));
lean_closure_set(v___x_775_, 2, v___x_774_);
v___x_776_ = l_instMonadControlTOfPure___redArg(v___x_775_);
v_toApplicative_777_ = lean_ctor_get(v___x_758_, 0);
v_toFunctor_778_ = lean_ctor_get(v_toApplicative_777_, 0);
v_toSeq_779_ = lean_ctor_get(v_toApplicative_777_, 2);
v_toSeqLeft_780_ = lean_ctor_get(v_toApplicative_777_, 3);
v_toSeqRight_781_ = lean_ctor_get(v_toApplicative_777_, 4);
lean_inc_ref_n(v_toFunctor_778_, 2);
v___f_782_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_782_, 0, v_toFunctor_778_);
v___f_783_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_783_, 0, v_toFunctor_778_);
v___x_784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_784_, 0, v___f_782_);
lean_ctor_set(v___x_784_, 1, v___f_783_);
lean_inc(v_toSeqRight_781_);
v___f_785_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_785_, 0, v_toSeqRight_781_);
lean_inc(v_toSeqLeft_780_);
v___f_786_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_786_, 0, v_toSeqLeft_780_);
lean_inc(v_toSeq_779_);
v___f_787_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_787_, 0, v_toSeq_779_);
v___x_788_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_788_, 0, v___x_784_);
lean_ctor_set(v___x_788_, 1, v___f_764_);
lean_ctor_set(v___x_788_, 2, v___f_787_);
lean_ctor_set(v___x_788_, 3, v___f_786_);
lean_ctor_set(v___x_788_, 4, v___f_785_);
v___x_789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_789_, 0, v___x_788_);
lean_ctor_set(v___x_789_, 1, v___f_765_);
v___x_790_ = l_StateRefT_x27_instMonad___redArg(v___x_789_);
v_toApplicative_791_ = lean_ctor_get(v___x_790_, 0);
v_isSharedCheck_822_ = !lean_is_exclusive(v___x_790_);
if (v_isSharedCheck_822_ == 0)
{
lean_object* v_unused_823_; 
v_unused_823_ = lean_ctor_get(v___x_790_, 1);
lean_dec(v_unused_823_);
v___x_793_ = v___x_790_;
v_isShared_794_ = v_isSharedCheck_822_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_toApplicative_791_);
lean_dec(v___x_790_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_822_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v_toFunctor_795_; lean_object* v_toSeq_796_; lean_object* v_toSeqLeft_797_; lean_object* v_toSeqRight_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_820_; 
v_toFunctor_795_ = lean_ctor_get(v_toApplicative_791_, 0);
v_toSeq_796_ = lean_ctor_get(v_toApplicative_791_, 2);
v_toSeqLeft_797_ = lean_ctor_get(v_toApplicative_791_, 3);
v_toSeqRight_798_ = lean_ctor_get(v_toApplicative_791_, 4);
v_isSharedCheck_820_ = !lean_is_exclusive(v_toApplicative_791_);
if (v_isSharedCheck_820_ == 0)
{
lean_object* v_unused_821_; 
v_unused_821_ = lean_ctor_get(v_toApplicative_791_, 1);
lean_dec(v_unused_821_);
v___x_800_ = v_toApplicative_791_;
v_isShared_801_ = v_isSharedCheck_820_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_toSeqRight_798_);
lean_inc(v_toSeqLeft_797_);
lean_inc(v_toSeq_796_);
lean_inc(v_toFunctor_795_);
lean_dec(v_toApplicative_791_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_820_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___f_802_; lean_object* v___f_803_; lean_object* v___f_804_; lean_object* v___f_805_; lean_object* v___x_806_; lean_object* v___f_807_; lean_object* v___f_808_; lean_object* v___f_809_; lean_object* v___x_811_; 
v___f_802_ = ((lean_object*)(l_Lean_MVarId_replaceLocalDecl___closed__4));
v___f_803_ = ((lean_object*)(l_Lean_MVarId_replaceLocalDecl___closed__5));
lean_inc_ref(v_toFunctor_795_);
v___f_804_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_804_, 0, v_toFunctor_795_);
v___f_805_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_805_, 0, v_toFunctor_795_);
v___x_806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_806_, 0, v___f_804_);
lean_ctor_set(v___x_806_, 1, v___f_805_);
v___f_807_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_807_, 0, v_toSeqRight_798_);
v___f_808_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_808_, 0, v_toSeqLeft_797_);
v___f_809_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_809_, 0, v_toSeq_796_);
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 4, v___f_807_);
lean_ctor_set(v___x_800_, 3, v___f_808_);
lean_ctor_set(v___x_800_, 2, v___f_809_);
lean_ctor_set(v___x_800_, 1, v___f_802_);
lean_ctor_set(v___x_800_, 0, v___x_806_);
v___x_811_ = v___x_800_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v___x_806_);
lean_ctor_set(v_reuseFailAlloc_819_, 1, v___f_802_);
lean_ctor_set(v_reuseFailAlloc_819_, 2, v___f_809_);
lean_ctor_set(v_reuseFailAlloc_819_, 3, v___f_808_);
lean_ctor_set(v_reuseFailAlloc_819_, 4, v___f_807_);
v___x_811_ = v_reuseFailAlloc_819_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
lean_object* v___x_813_; 
if (v_isShared_794_ == 0)
{
lean_ctor_set(v___x_793_, 1, v___f_803_);
lean_ctor_set(v___x_793_, 0, v___x_811_);
v___x_813_ = v___x_793_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v___x_811_);
lean_ctor_set(v_reuseFailAlloc_818_, 1, v___f_803_);
v___x_813_ = v_reuseFailAlloc_818_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
lean_object* v___x_814_; lean_object* v___f_815_; lean_object* v___x_124__overap_816_; lean_object* v___x_817_; 
lean_inc(v_fvarId_750_);
v___x_814_ = l_Lean_mkFVar(v_fvarId_750_);
lean_inc(v_mvarId_749_);
v___f_815_ = lean_alloc_closure((void*)(l_Lean_MVarId_replaceLocalDecl___lam__0___boxed), 10, 5);
lean_closure_set(v___f_815_, 0, v_eqProof_752_);
lean_closure_set(v___f_815_, 1, v___x_814_);
lean_closure_set(v___f_815_, 2, v_typeNew_751_);
lean_closure_set(v___f_815_, 3, v_mvarId_749_);
lean_closure_set(v___f_815_, 4, v_fvarId_750_);
v___x_124__overap_816_ = l_Lean_MVarId_withContext___redArg(v___x_776_, v___x_813_, v_mvarId_749_, v___f_815_);
lean_inc(v_a_756_);
lean_inc_ref(v_a_755_);
lean_inc(v_a_754_);
lean_inc_ref(v_a_753_);
v___x_817_ = lean_apply_5(v___x_124__overap_816_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, lean_box(0));
return v___x_817_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceLocalDecl___boxed(lean_object* v_mvarId_824_, lean_object* v_fvarId_825_, lean_object* v_typeNew_826_, lean_object* v_eqProof_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l_Lean_MVarId_replaceLocalDecl(v_mvarId_824_, v_fvarId_825_, v_typeNew_826_, v_eqProof_827_, v_a_828_, v_a_829_, v_a_830_, v_a_831_);
lean_dec(v_a_831_);
lean_dec_ref(v_a_830_);
lean_dec(v_a_829_);
lean_dec_ref(v_a_828_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalInstances___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__0___redArg(lean_object* v_decls_834_, lean_object* v_x_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_){
_start:
{
lean_object* v___x_841_; 
v___x_841_ = l_Lean_Meta_withLocalInstancesImp___redArg(v_decls_834_, v_x_835_, v___y_836_, v___y_837_, v___y_838_, v___y_839_);
if (lean_obj_tag(v___x_841_) == 0)
{
lean_object* v_a_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_849_; 
v_a_842_ = lean_ctor_get(v___x_841_, 0);
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_849_ == 0)
{
v___x_844_ = v___x_841_;
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_a_842_);
lean_dec(v___x_841_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_847_; 
if (v_isShared_845_ == 0)
{
v___x_847_ = v___x_844_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v_a_842_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
}
else
{
lean_object* v_a_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_857_; 
v_a_850_ = lean_ctor_get(v___x_841_, 0);
v_isSharedCheck_857_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_857_ == 0)
{
v___x_852_ = v___x_841_;
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_a_850_);
lean_dec(v___x_841_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v___x_855_; 
if (v_isShared_853_ == 0)
{
v___x_855_ = v___x_852_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v_a_850_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
return v___x_855_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalInstances___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__0___redArg___boxed(lean_object* v_decls_858_, lean_object* v_x_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_){
_start:
{
lean_object* v_res_865_; 
v_res_865_ = l_Lean_Meta_withLocalInstances___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__0___redArg(v_decls_858_, v_x_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_);
lean_dec(v___y_863_);
lean_dec_ref(v___y_862_);
lean_dec(v___y_861_);
lean_dec_ref(v___y_860_);
lean_dec(v_decls_858_);
return v_res_865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalInstances___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__0(lean_object* v_00_u03b1_866_, lean_object* v_decls_867_, lean_object* v_x_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_){
_start:
{
lean_object* v___x_874_; 
v___x_874_ = l_Lean_Meta_withLocalInstances___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__0___redArg(v_decls_867_, v_x_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalInstances___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__0___boxed(lean_object* v_00_u03b1_875_, lean_object* v_decls_876_, lean_object* v_x_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_){
_start:
{
lean_object* v_res_883_; 
v_res_883_ = l_Lean_Meta_withLocalInstances___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__0(v_00_u03b1_875_, v_decls_876_, v_x_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_);
lean_dec(v___y_881_);
lean_dec_ref(v___y_880_);
lean_dec(v___y_879_);
lean_dec_ref(v___y_878_);
lean_dec(v_decls_876_);
return v_res_883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__1___redArg(lean_object* v_lctx_884_, lean_object* v_x_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_){
_start:
{
lean_object* v_keyedConfig_891_; uint8_t v_trackZetaDelta_892_; lean_object* v_zetaDeltaSet_893_; lean_object* v_localInstances_894_; lean_object* v_defEqCtx_x3f_895_; lean_object* v_synthPendingDepth_896_; lean_object* v_customCanUnfoldPredicate_x3f_897_; uint8_t v_univApprox_898_; uint8_t v_inTypeClassResolution_899_; uint8_t v_cacheInferType_900_; lean_object* v___x_901_; lean_object* v___x_902_; 
v_keyedConfig_891_ = lean_ctor_get(v___y_886_, 0);
v_trackZetaDelta_892_ = lean_ctor_get_uint8(v___y_886_, sizeof(void*)*7);
v_zetaDeltaSet_893_ = lean_ctor_get(v___y_886_, 1);
v_localInstances_894_ = lean_ctor_get(v___y_886_, 3);
v_defEqCtx_x3f_895_ = lean_ctor_get(v___y_886_, 4);
v_synthPendingDepth_896_ = lean_ctor_get(v___y_886_, 5);
v_customCanUnfoldPredicate_x3f_897_ = lean_ctor_get(v___y_886_, 6);
v_univApprox_898_ = lean_ctor_get_uint8(v___y_886_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_899_ = lean_ctor_get_uint8(v___y_886_, sizeof(void*)*7 + 2);
v_cacheInferType_900_ = lean_ctor_get_uint8(v___y_886_, sizeof(void*)*7 + 3);
lean_inc(v_customCanUnfoldPredicate_x3f_897_);
lean_inc(v_synthPendingDepth_896_);
lean_inc(v_defEqCtx_x3f_895_);
lean_inc_ref(v_localInstances_894_);
lean_inc(v_zetaDeltaSet_893_);
lean_inc_ref(v_keyedConfig_891_);
v___x_901_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_901_, 0, v_keyedConfig_891_);
lean_ctor_set(v___x_901_, 1, v_zetaDeltaSet_893_);
lean_ctor_set(v___x_901_, 2, v_lctx_884_);
lean_ctor_set(v___x_901_, 3, v_localInstances_894_);
lean_ctor_set(v___x_901_, 4, v_defEqCtx_x3f_895_);
lean_ctor_set(v___x_901_, 5, v_synthPendingDepth_896_);
lean_ctor_set(v___x_901_, 6, v_customCanUnfoldPredicate_x3f_897_);
lean_ctor_set_uint8(v___x_901_, sizeof(void*)*7, v_trackZetaDelta_892_);
lean_ctor_set_uint8(v___x_901_, sizeof(void*)*7 + 1, v_univApprox_898_);
lean_ctor_set_uint8(v___x_901_, sizeof(void*)*7 + 2, v_inTypeClassResolution_899_);
lean_ctor_set_uint8(v___x_901_, sizeof(void*)*7 + 3, v_cacheInferType_900_);
lean_inc(v___y_889_);
lean_inc_ref(v___y_888_);
lean_inc(v___y_887_);
v___x_902_ = lean_apply_5(v_x_885_, v___x_901_, v___y_887_, v___y_888_, v___y_889_, lean_box(0));
return v___x_902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__1___redArg___boxed(lean_object* v_lctx_903_, lean_object* v_x_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_){
_start:
{
lean_object* v_res_910_; 
v_res_910_ = l_Lean_Meta_withLCtx_x27___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__1___redArg(v_lctx_903_, v_x_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_);
lean_dec(v___y_908_);
lean_dec_ref(v___y_907_);
lean_dec(v___y_906_);
lean_dec_ref(v___y_905_);
return v_res_910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__1(lean_object* v_00_u03b1_911_, lean_object* v_lctx_912_, lean_object* v_x_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_){
_start:
{
lean_object* v___x_919_; 
v___x_919_ = l_Lean_Meta_withLCtx_x27___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__1___redArg(v_lctx_912_, v_x_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_);
return v___x_919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__1___boxed(lean_object* v_00_u03b1_920_, lean_object* v_lctx_921_, lean_object* v_x_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_){
_start:
{
lean_object* v_res_928_; 
v_res_928_ = l_Lean_Meta_withLCtx_x27___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__1(v_00_u03b1_920_, v_lctx_921_, v_x_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_);
lean_dec(v___y_926_);
lean_dec_ref(v___y_925_);
lean_dec(v___y_924_);
lean_dec_ref(v___y_923_);
return v_res_928_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_setFVarType___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2___redArg(lean_object* v_mvarId_929_, lean_object* v_fvarId_930_, lean_object* v_type_931_, lean_object* v___y_932_){
_start:
{
lean_object* v___x_934_; lean_object* v_mctx_935_; lean_object* v_cache_936_; lean_object* v_zetaDeltaFVarIds_937_; lean_object* v_postponed_938_; lean_object* v_diag_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_950_; 
v___x_934_ = lean_st_ref_take(v___y_932_);
v_mctx_935_ = lean_ctor_get(v___x_934_, 0);
v_cache_936_ = lean_ctor_get(v___x_934_, 1);
v_zetaDeltaFVarIds_937_ = lean_ctor_get(v___x_934_, 2);
v_postponed_938_ = lean_ctor_get(v___x_934_, 3);
v_diag_939_ = lean_ctor_get(v___x_934_, 4);
v_isSharedCheck_950_ = !lean_is_exclusive(v___x_934_);
if (v_isSharedCheck_950_ == 0)
{
v___x_941_ = v___x_934_;
v_isShared_942_ = v_isSharedCheck_950_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_diag_939_);
lean_inc(v_postponed_938_);
lean_inc(v_zetaDeltaFVarIds_937_);
lean_inc(v_cache_936_);
lean_inc(v_mctx_935_);
lean_dec(v___x_934_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_950_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_946_; 
v___x_943_ = lean_box(0);
v___x_944_ = l_Lean_MetavarContext_setFVarType(v_mctx_935_, v_mvarId_929_, v_fvarId_930_, v_type_931_);
if (v_isShared_942_ == 0)
{
lean_ctor_set(v___x_941_, 0, v___x_944_);
v___x_946_ = v___x_941_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v___x_944_);
lean_ctor_set(v_reuseFailAlloc_949_, 1, v_cache_936_);
lean_ctor_set(v_reuseFailAlloc_949_, 2, v_zetaDeltaFVarIds_937_);
lean_ctor_set(v_reuseFailAlloc_949_, 3, v_postponed_938_);
lean_ctor_set(v_reuseFailAlloc_949_, 4, v_diag_939_);
v___x_946_ = v_reuseFailAlloc_949_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_947_ = lean_st_ref_put(v___y_932_, v___x_946_);
v___x_948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_948_, 0, v___x_943_);
return v___x_948_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_setFVarType___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2___redArg___boxed(lean_object* v_mvarId_951_, lean_object* v_fvarId_952_, lean_object* v_type_953_, lean_object* v___y_954_, lean_object* v___y_955_){
_start:
{
lean_object* v_res_956_; 
v_res_956_ = l_Lean_MVarId_setFVarType___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2___redArg(v_mvarId_951_, v_fvarId_952_, v_type_953_, v___y_954_);
lean_dec(v___y_954_);
return v_res_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_setFVarType___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2(lean_object* v_mvarId_957_, lean_object* v_fvarId_958_, lean_object* v_type_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_){
_start:
{
lean_object* v___x_965_; 
v___x_965_ = l_Lean_MVarId_setFVarType___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2___redArg(v_mvarId_957_, v_fvarId_958_, v_type_959_, v___y_961_);
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_setFVarType___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2___boxed(lean_object* v_mvarId_966_, lean_object* v_fvarId_967_, lean_object* v_type_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = l_Lean_MVarId_setFVarType___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2(v_mvarId_966_, v_fvarId_967_, v_type_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_);
lean_dec(v___y_972_);
lean_dec_ref(v___y_971_);
lean_dec(v___y_970_);
lean_dec_ref(v___y_969_);
return v_res_974_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceLocalDeclDefEq___lam__0(lean_object* v_mvarId_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_){
_start:
{
lean_object* v___x_981_; 
lean_inc(v_mvarId_975_);
v___x_981_ = l_Lean_MVarId_getDecl(v_mvarId_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_);
if (lean_obj_tag(v___x_981_) == 0)
{
lean_object* v_a_982_; lean_object* v_userName_983_; lean_object* v_type_984_; uint8_t v_kind_985_; lean_object* v___x_986_; lean_object* v___x_987_; 
v_a_982_ = lean_ctor_get(v___x_981_, 0);
lean_inc(v_a_982_);
lean_dec_ref_known(v___x_981_, 1);
v_userName_983_ = lean_ctor_get(v_a_982_, 0);
lean_inc(v_userName_983_);
v_type_984_ = lean_ctor_get(v_a_982_, 2);
lean_inc_ref(v_type_984_);
v_kind_985_ = lean_ctor_get_uint8(v_a_982_, sizeof(void*)*7);
lean_dec(v_a_982_);
v___x_986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_986_, 0, v_type_984_);
v___x_987_ = l_Lean_Meta_mkFreshExprMVar(v___x_986_, v_kind_985_, v_userName_983_, v___y_976_, v___y_977_, v___y_978_, v___y_979_);
if (lean_obj_tag(v___x_987_) == 0)
{
lean_object* v_a_988_; lean_object* v___x_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_997_; 
v_a_988_ = lean_ctor_get(v___x_987_, 0);
lean_inc_n(v_a_988_, 2);
lean_dec_ref_known(v___x_987_, 1);
v___x_989_ = l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0___redArg(v_mvarId_975_, v_a_988_, v___y_977_);
v_isSharedCheck_997_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_997_ == 0)
{
lean_object* v_unused_998_; 
v_unused_998_ = lean_ctor_get(v___x_989_, 0);
lean_dec(v_unused_998_);
v___x_991_ = v___x_989_;
v_isShared_992_ = v_isSharedCheck_997_;
goto v_resetjp_990_;
}
else
{
lean_dec(v___x_989_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_997_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v___x_993_; lean_object* v___x_995_; 
v___x_993_ = l_Lean_Expr_mvarId_x21(v_a_988_);
lean_dec(v_a_988_);
if (v_isShared_992_ == 0)
{
lean_ctor_set(v___x_991_, 0, v___x_993_);
v___x_995_ = v___x_991_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v___x_993_);
v___x_995_ = v_reuseFailAlloc_996_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
return v___x_995_;
}
}
}
else
{
lean_object* v_a_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1006_; 
lean_dec(v_mvarId_975_);
v_a_999_ = lean_ctor_get(v___x_987_, 0);
v_isSharedCheck_1006_ = !lean_is_exclusive(v___x_987_);
if (v_isSharedCheck_1006_ == 0)
{
v___x_1001_ = v___x_987_;
v_isShared_1002_ = v_isSharedCheck_1006_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_a_999_);
lean_dec(v___x_987_);
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
lean_dec(v_mvarId_975_);
v_a_1007_ = lean_ctor_get(v___x_981_, 0);
v_isSharedCheck_1014_ = !lean_is_exclusive(v___x_981_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_1009_ = v___x_981_;
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_a_1007_);
lean_dec(v___x_981_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceLocalDeclDefEq___lam__0___boxed(lean_object* v_mvarId_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_){
_start:
{
lean_object* v_res_1021_; 
v_res_1021_ = l_Lean_MVarId_replaceLocalDeclDefEq___lam__0(v_mvarId_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_);
lean_dec(v___y_1019_);
lean_dec_ref(v___y_1018_);
lean_dec(v___y_1017_);
lean_dec_ref(v___y_1016_);
return v_res_1021_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceLocalDeclDefEq___lam__1(lean_object* v_fvarId_1022_, lean_object* v_typeNew_1023_, lean_object* v___f_1024_, lean_object* v_mvarId_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_){
_start:
{
lean_object* v___x_1031_; 
lean_inc(v_fvarId_1022_);
v___x_1031_ = l_Lean_FVarId_getType___redArg(v_fvarId_1022_, v___y_1026_, v___y_1028_, v___y_1029_);
if (lean_obj_tag(v___x_1031_) == 0)
{
lean_object* v_a_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1061_; 
v_a_1032_ = lean_ctor_get(v___x_1031_, 0);
v_isSharedCheck_1061_ = !lean_is_exclusive(v___x_1031_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1034_ = v___x_1031_;
v_isShared_1035_ = v_isSharedCheck_1061_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_a_1032_);
lean_dec(v___x_1031_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1061_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
uint8_t v___x_1036_; 
v___x_1036_ = lean_expr_equal(v_a_1032_, v_typeNew_1023_);
if (v___x_1036_ == 0)
{
lean_object* v___x_1037_; lean_object* v_a_1038_; lean_object* v___x_1039_; lean_object* v_a_1040_; uint8_t v___x_1041_; 
lean_del_object(v___x_1034_);
v___x_1037_ = l_Lean_instantiateMVars___at___00Lean_MVarId_replaceTargetDefEq_spec__0___redArg(v_a_1032_, v___y_1027_);
v_a_1038_ = lean_ctor_get(v___x_1037_, 0);
lean_inc(v_a_1038_);
lean_dec_ref(v___x_1037_);
v___x_1039_ = l_Lean_instantiateMVars___at___00Lean_MVarId_replaceTargetDefEq_spec__0___redArg(v_typeNew_1023_, v___y_1027_);
v_a_1040_ = lean_ctor_get(v___x_1039_, 0);
lean_inc(v_a_1040_);
lean_dec_ref(v___x_1039_);
v___x_1041_ = lean_expr_equal(v_a_1038_, v_a_1040_);
if (v___x_1041_ == 0)
{
lean_object* v_lctx_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; 
lean_dec(v_a_1038_);
lean_dec(v_mvarId_1025_);
v_lctx_1042_ = lean_ctor_get(v___y_1026_, 2);
lean_inc(v_fvarId_1022_);
lean_inc_ref(v_lctx_1042_);
v___x_1043_ = l_Lean_LocalContext_setType(v_lctx_1042_, v_fvarId_1022_, v_a_1040_);
lean_inc_ref(v___x_1043_);
v___x_1044_ = l_Lean_LocalContext_get_x21(v___x_1043_, v_fvarId_1022_);
v___x_1045_ = lean_box(0);
v___x_1046_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1044_);
lean_ctor_set(v___x_1046_, 1, v___x_1045_);
v___x_1047_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalInstances___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__0___boxed), 8, 3);
lean_closure_set(v___x_1047_, 0, lean_box(0));
lean_closure_set(v___x_1047_, 1, v___x_1046_);
lean_closure_set(v___x_1047_, 2, v___f_1024_);
v___x_1048_ = l_Lean_Meta_withLCtx_x27___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__1___redArg(v___x_1043_, v___x_1047_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_);
lean_dec_ref(v___y_1026_);
return v___x_1048_;
}
else
{
lean_object* v___x_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1056_; 
lean_dec(v_a_1040_);
lean_dec_ref(v___y_1026_);
lean_dec_ref(v___f_1024_);
lean_inc(v_mvarId_1025_);
v___x_1049_ = l_Lean_MVarId_setFVarType___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2___redArg(v_mvarId_1025_, v_fvarId_1022_, v_a_1038_, v___y_1027_);
v_isSharedCheck_1056_ = !lean_is_exclusive(v___x_1049_);
if (v_isSharedCheck_1056_ == 0)
{
lean_object* v_unused_1057_; 
v_unused_1057_ = lean_ctor_get(v___x_1049_, 0);
lean_dec(v_unused_1057_);
v___x_1051_ = v___x_1049_;
v_isShared_1052_ = v_isSharedCheck_1056_;
goto v_resetjp_1050_;
}
else
{
lean_dec(v___x_1049_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1056_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v___x_1054_; 
if (v_isShared_1052_ == 0)
{
lean_ctor_set(v___x_1051_, 0, v_mvarId_1025_);
v___x_1054_ = v___x_1051_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v_mvarId_1025_);
v___x_1054_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
return v___x_1054_;
}
}
}
}
else
{
lean_object* v___x_1059_; 
lean_dec(v_a_1032_);
lean_dec_ref(v___y_1026_);
lean_dec_ref(v___f_1024_);
lean_dec_ref(v_typeNew_1023_);
lean_dec(v_fvarId_1022_);
if (v_isShared_1035_ == 0)
{
lean_ctor_set(v___x_1034_, 0, v_mvarId_1025_);
v___x_1059_ = v___x_1034_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v_mvarId_1025_);
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
else
{
lean_object* v_a_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1069_; 
lean_dec_ref(v___y_1026_);
lean_dec(v_mvarId_1025_);
lean_dec_ref(v___f_1024_);
lean_dec_ref(v_typeNew_1023_);
lean_dec(v_fvarId_1022_);
v_a_1062_ = lean_ctor_get(v___x_1031_, 0);
v_isSharedCheck_1069_ = !lean_is_exclusive(v___x_1031_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_1064_ = v___x_1031_;
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_a_1062_);
lean_dec(v___x_1031_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v___x_1067_; 
if (v_isShared_1065_ == 0)
{
v___x_1067_ = v___x_1064_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v_a_1062_);
v___x_1067_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
return v___x_1067_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceLocalDeclDefEq___lam__1___boxed(lean_object* v_fvarId_1070_, lean_object* v_typeNew_1071_, lean_object* v___f_1072_, lean_object* v_mvarId_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_){
_start:
{
lean_object* v_res_1079_; 
v_res_1079_ = l_Lean_MVarId_replaceLocalDeclDefEq___lam__1(v_fvarId_1070_, v_typeNew_1071_, v___f_1072_, v_mvarId_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_);
lean_dec(v___y_1077_);
lean_dec_ref(v___y_1076_);
lean_dec(v___y_1075_);
return v_res_1079_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceLocalDeclDefEq(lean_object* v_mvarId_1080_, lean_object* v_fvarId_1081_, lean_object* v_typeNew_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_){
_start:
{
lean_object* v___f_1088_; lean_object* v___f_1089_; lean_object* v___x_1090_; 
lean_inc_n(v_mvarId_1080_, 2);
v___f_1088_ = lean_alloc_closure((void*)(l_Lean_MVarId_replaceLocalDeclDefEq___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1088_, 0, v_mvarId_1080_);
v___f_1089_ = lean_alloc_closure((void*)(l_Lean_MVarId_replaceLocalDeclDefEq___lam__1___boxed), 9, 4);
lean_closure_set(v___f_1089_, 0, v_fvarId_1081_);
lean_closure_set(v___f_1089_, 1, v_typeNew_1082_);
lean_closure_set(v___f_1089_, 2, v___f_1088_);
lean_closure_set(v___f_1089_, 3, v_mvarId_1080_);
v___x_1090_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(v_mvarId_1080_, v___f_1089_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_);
return v___x_1090_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceLocalDeclDefEq___boxed(lean_object* v_mvarId_1091_, lean_object* v_fvarId_1092_, lean_object* v_typeNew_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_){
_start:
{
lean_object* v_res_1099_; 
v_res_1099_ = l_Lean_MVarId_replaceLocalDeclDefEq(v_mvarId_1091_, v_fvarId_1092_, v_typeNew_1093_, v_a_1094_, v_a_1095_, v_a_1096_, v_a_1097_);
lean_dec(v_a_1097_);
lean_dec_ref(v_a_1096_);
lean_dec(v_a_1095_);
lean_dec_ref(v_a_1094_);
return v_res_1099_;
}
}
static lean_object* _init_l_Lean_MVarId_change___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___x_1101_ = ((lean_object*)(l_Lean_MVarId_change___lam__0___closed__0));
v___x_1102_ = l_Lean_stringToMessageData(v___x_1101_);
return v___x_1102_;
}
}
static lean_object* _init_l_Lean_MVarId_change___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1104_ = ((lean_object*)(l_Lean_MVarId_change___lam__0___closed__2));
v___x_1105_ = l_Lean_stringToMessageData(v___x_1104_);
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_change___lam__0(lean_object* v_mvarId_1106_, uint8_t v_checkDefEq_1107_, lean_object* v_targetNew_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_){
_start:
{
lean_object* v___x_1114_; 
lean_inc(v_mvarId_1106_);
v___x_1114_ = l_Lean_MVarId_getType(v_mvarId_1106_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_);
if (lean_obj_tag(v___x_1114_) == 0)
{
if (v_checkDefEq_1107_ == 0)
{
lean_object* v___x_1115_; 
lean_dec_ref_known(v___x_1114_, 1);
v___x_1115_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_1106_, v_targetNew_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_);
return v___x_1115_;
}
else
{
lean_object* v_a_1116_; lean_object* v___x_1117_; 
v_a_1116_ = lean_ctor_get(v___x_1114_, 0);
lean_inc_n(v_a_1116_, 2);
lean_dec_ref_known(v___x_1114_, 1);
lean_inc_ref(v_targetNew_1108_);
v___x_1117_ = l_Lean_Meta_isExprDefEq(v_a_1116_, v_targetNew_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_);
if (lean_obj_tag(v___x_1117_) == 0)
{
lean_object* v_a_1118_; uint8_t v___x_1119_; 
v_a_1118_ = lean_ctor_get(v___x_1117_, 0);
lean_inc(v_a_1118_);
lean_dec_ref_known(v___x_1117_, 1);
v___x_1119_ = lean_unbox(v_a_1118_);
lean_dec(v_a_1118_);
if (v___x_1119_ == 0)
{
lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; 
v___x_1120_ = ((lean_object*)(l_Lean_MVarId_replaceTargetDefEq___closed__1));
v___x_1121_ = lean_obj_once(&l_Lean_MVarId_change___lam__0___closed__1, &l_Lean_MVarId_change___lam__0___closed__1_once, _init_l_Lean_MVarId_change___lam__0___closed__1);
lean_inc_ref(v_targetNew_1108_);
v___x_1122_ = l_Lean_indentExpr(v_targetNew_1108_);
v___x_1123_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1123_, 0, v___x_1121_);
lean_ctor_set(v___x_1123_, 1, v___x_1122_);
v___x_1124_ = lean_obj_once(&l_Lean_MVarId_change___lam__0___closed__3, &l_Lean_MVarId_change___lam__0___closed__3_once, _init_l_Lean_MVarId_change___lam__0___closed__3);
v___x_1125_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1125_, 0, v___x_1123_);
lean_ctor_set(v___x_1125_, 1, v___x_1124_);
v___x_1126_ = l_Lean_indentExpr(v_a_1116_);
v___x_1127_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1127_, 0, v___x_1125_);
lean_ctor_set(v___x_1127_, 1, v___x_1126_);
v___x_1128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1128_, 0, v___x_1127_);
lean_inc(v_mvarId_1106_);
v___x_1129_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1120_, v_mvarId_1106_, v___x_1128_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_);
if (lean_obj_tag(v___x_1129_) == 0)
{
lean_object* v___x_1130_; 
lean_dec_ref_known(v___x_1129_, 1);
v___x_1130_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_1106_, v_targetNew_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_);
return v___x_1130_;
}
else
{
lean_object* v_a_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1138_; 
lean_dec_ref(v_targetNew_1108_);
lean_dec(v_mvarId_1106_);
v_a_1131_ = lean_ctor_get(v___x_1129_, 0);
v_isSharedCheck_1138_ = !lean_is_exclusive(v___x_1129_);
if (v_isSharedCheck_1138_ == 0)
{
v___x_1133_ = v___x_1129_;
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_a_1131_);
lean_dec(v___x_1129_);
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
lean_object* v___x_1139_; 
lean_dec(v_a_1116_);
v___x_1139_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_1106_, v_targetNew_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_);
return v___x_1139_;
}
}
else
{
lean_object* v_a_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1147_; 
lean_dec(v_a_1116_);
lean_dec_ref(v_targetNew_1108_);
lean_dec(v_mvarId_1106_);
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
else
{
lean_object* v_a_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1155_; 
lean_dec_ref(v_targetNew_1108_);
lean_dec(v_mvarId_1106_);
v_a_1148_ = lean_ctor_get(v___x_1114_, 0);
v_isSharedCheck_1155_ = !lean_is_exclusive(v___x_1114_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1150_ = v___x_1114_;
v_isShared_1151_ = v_isSharedCheck_1155_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_a_1148_);
lean_dec(v___x_1114_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1155_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v___x_1153_; 
if (v_isShared_1151_ == 0)
{
v___x_1153_ = v___x_1150_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v_a_1148_);
v___x_1153_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
return v___x_1153_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_change___lam__0___boxed(lean_object* v_mvarId_1156_, lean_object* v_checkDefEq_1157_, lean_object* v_targetNew_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_){
_start:
{
uint8_t v_checkDefEq_boxed_1164_; lean_object* v_res_1165_; 
v_checkDefEq_boxed_1164_ = lean_unbox(v_checkDefEq_1157_);
v_res_1165_ = l_Lean_MVarId_change___lam__0(v_mvarId_1156_, v_checkDefEq_boxed_1164_, v_targetNew_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_);
lean_dec(v___y_1162_);
lean_dec_ref(v___y_1161_);
lean_dec(v___y_1160_);
lean_dec_ref(v___y_1159_);
return v_res_1165_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_change(lean_object* v_mvarId_1166_, lean_object* v_targetNew_1167_, uint8_t v_checkDefEq_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_){
_start:
{
lean_object* v___x_1174_; lean_object* v___f_1175_; lean_object* v___x_1176_; 
v___x_1174_ = lean_box(v_checkDefEq_1168_);
lean_inc(v_mvarId_1166_);
v___f_1175_ = lean_alloc_closure((void*)(l_Lean_MVarId_change___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1175_, 0, v_mvarId_1166_);
lean_closure_set(v___f_1175_, 1, v___x_1174_);
lean_closure_set(v___f_1175_, 2, v_targetNew_1167_);
v___x_1176_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(v_mvarId_1166_, v___f_1175_, v_a_1169_, v_a_1170_, v_a_1171_, v_a_1172_);
return v___x_1176_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_change___boxed(lean_object* v_mvarId_1177_, lean_object* v_targetNew_1178_, lean_object* v_checkDefEq_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_){
_start:
{
uint8_t v_checkDefEq_boxed_1185_; lean_object* v_res_1186_; 
v_checkDefEq_boxed_1185_ = lean_unbox(v_checkDefEq_1179_);
v_res_1186_ = l_Lean_MVarId_change(v_mvarId_1177_, v_targetNew_1178_, v_checkDefEq_boxed_1185_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_);
lean_dec(v_a_1183_);
lean_dec_ref(v_a_1182_);
lean_dec(v_a_1181_);
lean_dec_ref(v_a_1180_);
return v_res_1186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0_spec__0___redArg(lean_object* v_t_1187_, lean_object* v___y_1188_){
_start:
{
lean_object* v___x_1190_; lean_object* v_infoState_1191_; uint8_t v_enabled_1192_; 
v___x_1190_ = lean_st_ref_get(v___y_1188_);
v_infoState_1191_ = lean_ctor_get(v___x_1190_, 8);
lean_inc_ref(v_infoState_1191_);
lean_dec(v___x_1190_);
v_enabled_1192_ = lean_ctor_get_uint8(v_infoState_1191_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1191_);
if (v_enabled_1192_ == 0)
{
lean_object* v___x_1193_; lean_object* v___x_1194_; 
lean_dec_ref(v_t_1187_);
v___x_1193_ = lean_box(0);
v___x_1194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1194_, 0, v___x_1193_);
return v___x_1194_;
}
else
{
lean_object* v___x_1195_; lean_object* v_infoState_1196_; lean_object* v_env_1197_; lean_object* v_nextMacroScope_1198_; lean_object* v_ngen_1199_; lean_object* v_auxDeclNGen_1200_; lean_object* v_traceState_1201_; lean_object* v_cache_1202_; lean_object* v_recordedDeps_1203_; lean_object* v_messages_1204_; lean_object* v_snapshotTasks_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1227_; 
v___x_1195_ = lean_st_ref_take(v___y_1188_);
v_infoState_1196_ = lean_ctor_get(v___x_1195_, 8);
v_env_1197_ = lean_ctor_get(v___x_1195_, 0);
v_nextMacroScope_1198_ = lean_ctor_get(v___x_1195_, 1);
v_ngen_1199_ = lean_ctor_get(v___x_1195_, 2);
v_auxDeclNGen_1200_ = lean_ctor_get(v___x_1195_, 3);
v_traceState_1201_ = lean_ctor_get(v___x_1195_, 4);
v_cache_1202_ = lean_ctor_get(v___x_1195_, 5);
v_recordedDeps_1203_ = lean_ctor_get(v___x_1195_, 6);
v_messages_1204_ = lean_ctor_get(v___x_1195_, 7);
v_snapshotTasks_1205_ = lean_ctor_get(v___x_1195_, 9);
v_isSharedCheck_1227_ = !lean_is_exclusive(v___x_1195_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1207_ = v___x_1195_;
v_isShared_1208_ = v_isSharedCheck_1227_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_snapshotTasks_1205_);
lean_inc(v_infoState_1196_);
lean_inc(v_messages_1204_);
lean_inc(v_recordedDeps_1203_);
lean_inc(v_cache_1202_);
lean_inc(v_traceState_1201_);
lean_inc(v_auxDeclNGen_1200_);
lean_inc(v_ngen_1199_);
lean_inc(v_nextMacroScope_1198_);
lean_inc(v_env_1197_);
lean_dec(v___x_1195_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1227_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
uint8_t v_enabled_1209_; lean_object* v_assignment_1210_; lean_object* v_lazyAssignment_1211_; lean_object* v_trees_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1226_; 
v_enabled_1209_ = lean_ctor_get_uint8(v_infoState_1196_, sizeof(void*)*3);
v_assignment_1210_ = lean_ctor_get(v_infoState_1196_, 0);
v_lazyAssignment_1211_ = lean_ctor_get(v_infoState_1196_, 1);
v_trees_1212_ = lean_ctor_get(v_infoState_1196_, 2);
v_isSharedCheck_1226_ = !lean_is_exclusive(v_infoState_1196_);
if (v_isSharedCheck_1226_ == 0)
{
v___x_1214_ = v_infoState_1196_;
v_isShared_1215_ = v_isSharedCheck_1226_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_trees_1212_);
lean_inc(v_lazyAssignment_1211_);
lean_inc(v_assignment_1210_);
lean_dec(v_infoState_1196_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1226_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1219_; 
v___x_1216_ = lean_box(0);
v___x_1217_ = l_Lean_PersistentArray_push___redArg(v_trees_1212_, v_t_1187_);
if (v_isShared_1215_ == 0)
{
lean_ctor_set(v___x_1214_, 2, v___x_1217_);
v___x_1219_ = v___x_1214_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v_assignment_1210_);
lean_ctor_set(v_reuseFailAlloc_1225_, 1, v_lazyAssignment_1211_);
lean_ctor_set(v_reuseFailAlloc_1225_, 2, v___x_1217_);
lean_ctor_set_uint8(v_reuseFailAlloc_1225_, sizeof(void*)*3, v_enabled_1209_);
v___x_1219_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
lean_object* v___x_1221_; 
if (v_isShared_1208_ == 0)
{
lean_ctor_set(v___x_1207_, 8, v___x_1219_);
v___x_1221_ = v___x_1207_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v_env_1197_);
lean_ctor_set(v_reuseFailAlloc_1224_, 1, v_nextMacroScope_1198_);
lean_ctor_set(v_reuseFailAlloc_1224_, 2, v_ngen_1199_);
lean_ctor_set(v_reuseFailAlloc_1224_, 3, v_auxDeclNGen_1200_);
lean_ctor_set(v_reuseFailAlloc_1224_, 4, v_traceState_1201_);
lean_ctor_set(v_reuseFailAlloc_1224_, 5, v_cache_1202_);
lean_ctor_set(v_reuseFailAlloc_1224_, 6, v_recordedDeps_1203_);
lean_ctor_set(v_reuseFailAlloc_1224_, 7, v_messages_1204_);
lean_ctor_set(v_reuseFailAlloc_1224_, 8, v___x_1219_);
lean_ctor_set(v_reuseFailAlloc_1224_, 9, v_snapshotTasks_1205_);
v___x_1221_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
lean_object* v___x_1222_; lean_object* v___x_1223_; 
v___x_1222_ = lean_st_ref_put(v___y_1188_, v___x_1221_);
v___x_1223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1223_, 0, v___x_1216_);
return v___x_1223_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0_spec__0___redArg___boxed(lean_object* v_t_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_){
_start:
{
lean_object* v_res_1231_; 
v_res_1231_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0_spec__0___redArg(v_t_1228_, v___y_1229_);
lean_dec(v___y_1229_);
return v_res_1231_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; 
v___x_1232_ = lean_unsigned_to_nat(32u);
v___x_1233_ = lean_mk_empty_array_with_capacity(v___x_1232_);
v___x_1234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1234_, 0, v___x_1233_);
return v___x_1234_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0___closed__1(void){
_start:
{
size_t v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; 
v___x_1235_ = ((size_t)5ULL);
v___x_1236_ = lean_unsigned_to_nat(0u);
v___x_1237_ = lean_unsigned_to_nat(32u);
v___x_1238_ = lean_mk_empty_array_with_capacity(v___x_1237_);
v___x_1239_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0___closed__0);
v___x_1240_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1240_, 0, v___x_1239_);
lean_ctor_set(v___x_1240_, 1, v___x_1238_);
lean_ctor_set(v___x_1240_, 2, v___x_1236_);
lean_ctor_set(v___x_1240_, 3, v___x_1236_);
lean_ctor_set_usize(v___x_1240_, 4, v___x_1235_);
return v___x_1240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0(lean_object* v_t_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_){
_start:
{
lean_object* v___x_1247_; lean_object* v_infoState_1248_; uint8_t v_enabled_1249_; 
v___x_1247_ = lean_st_ref_get(v___y_1245_);
v_infoState_1248_ = lean_ctor_get(v___x_1247_, 8);
lean_inc_ref(v_infoState_1248_);
lean_dec(v___x_1247_);
v_enabled_1249_ = lean_ctor_get_uint8(v_infoState_1248_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1248_);
if (v_enabled_1249_ == 0)
{
lean_object* v___x_1250_; lean_object* v___x_1251_; 
lean_dec_ref(v_t_1241_);
v___x_1250_ = lean_box(0);
v___x_1251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1251_, 0, v___x_1250_);
return v___x_1251_;
}
else
{
lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; 
v___x_1252_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0___closed__1);
v___x_1253_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1253_, 0, v_t_1241_);
lean_ctor_set(v___x_1253_, 1, v___x_1252_);
v___x_1254_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0_spec__0___redArg(v___x_1253_, v___y_1245_);
return v___x_1254_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0___boxed(lean_object* v_t_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_){
_start:
{
lean_object* v_res_1261_; 
v_res_1261_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0(v_t_1255_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_);
lean_dec(v___y_1259_);
lean_dec_ref(v___y_1258_);
lean_dec(v___y_1257_);
lean_dec_ref(v___y_1256_);
return v_res_1261_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_withReverted_spec__1(lean_object* v_as_1262_, size_t v_sz_1263_, size_t v_i_1264_, lean_object* v_b_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_){
_start:
{
lean_object* v_a_1272_; uint8_t v___x_1276_; 
v___x_1276_ = lean_usize_dec_lt(v_i_1264_, v_sz_1263_);
if (v___x_1276_ == 0)
{
lean_object* v___x_1277_; 
v___x_1277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1277_, 0, v_b_1265_);
return v___x_1277_;
}
else
{
lean_object* v_array_1278_; lean_object* v_start_1279_; lean_object* v_stop_1280_; uint8_t v___x_1281_; 
v_array_1278_ = lean_ctor_get(v_b_1265_, 0);
v_start_1279_ = lean_ctor_get(v_b_1265_, 1);
v_stop_1280_ = lean_ctor_get(v_b_1265_, 2);
v___x_1281_ = lean_nat_dec_lt(v_start_1279_, v_stop_1280_);
if (v___x_1281_ == 0)
{
lean_object* v___x_1282_; 
v___x_1282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1282_, 0, v_b_1265_);
return v___x_1282_;
}
else
{
lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1321_; 
lean_inc(v_stop_1280_);
lean_inc(v_start_1279_);
lean_inc_ref(v_array_1278_);
v_isSharedCheck_1321_ = !lean_is_exclusive(v_b_1265_);
if (v_isSharedCheck_1321_ == 0)
{
lean_object* v_unused_1322_; lean_object* v_unused_1323_; lean_object* v_unused_1324_; 
v_unused_1322_ = lean_ctor_get(v_b_1265_, 2);
lean_dec(v_unused_1322_);
v_unused_1323_ = lean_ctor_get(v_b_1265_, 1);
lean_dec(v_unused_1323_);
v_unused_1324_ = lean_ctor_get(v_b_1265_, 0);
lean_dec(v_unused_1324_);
v___x_1284_ = v_b_1265_;
v_isShared_1285_ = v_isSharedCheck_1321_;
goto v_resetjp_1283_;
}
else
{
lean_dec(v_b_1265_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1321_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
lean_object* v_a_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1291_; 
v_a_1286_ = lean_array_uget(v_as_1262_, v_i_1264_);
v___x_1287_ = lean_array_fget(v_array_1278_, v_start_1279_);
v___x_1288_ = lean_unsigned_to_nat(1u);
v___x_1289_ = lean_nat_add(v_start_1279_, v___x_1288_);
lean_dec(v_start_1279_);
if (v_isShared_1285_ == 0)
{
lean_ctor_set(v___x_1284_, 1, v___x_1289_);
v___x_1291_ = v___x_1284_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v_array_1278_);
lean_ctor_set(v_reuseFailAlloc_1320_, 1, v___x_1289_);
lean_ctor_set(v_reuseFailAlloc_1320_, 2, v_stop_1280_);
v___x_1291_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
if (lean_obj_tag(v_a_1286_) == 1)
{
lean_object* v_val_1292_; lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1319_; 
v_val_1292_ = lean_ctor_get(v_a_1286_, 0);
v_isSharedCheck_1319_ = !lean_is_exclusive(v_a_1286_);
if (v_isSharedCheck_1319_ == 0)
{
v___x_1294_ = v_a_1286_;
v_isShared_1295_ = v_isSharedCheck_1319_;
goto v_resetjp_1293_;
}
else
{
lean_inc(v_val_1292_);
lean_dec(v_a_1286_);
v___x_1294_ = lean_box(0);
v_isShared_1295_ = v_isSharedCheck_1319_;
goto v_resetjp_1293_;
}
v_resetjp_1293_:
{
lean_object* v___x_1296_; 
lean_inc(v___x_1287_);
v___x_1296_ = l_Lean_FVarId_getUserName___redArg(v___x_1287_, v___y_1266_, v___y_1268_, v___y_1269_);
if (lean_obj_tag(v___x_1296_) == 0)
{
lean_object* v_a_1297_; lean_object* v___x_1298_; lean_object* v___x_1300_; 
v_a_1297_ = lean_ctor_get(v___x_1296_, 0);
lean_inc(v_a_1297_);
lean_dec_ref_known(v___x_1296_, 1);
v___x_1298_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1298_, 0, v_a_1297_);
lean_ctor_set(v___x_1298_, 1, v___x_1287_);
lean_ctor_set(v___x_1298_, 2, v_val_1292_);
if (v_isShared_1295_ == 0)
{
lean_ctor_set_tag(v___x_1294_, 11);
lean_ctor_set(v___x_1294_, 0, v___x_1298_);
v___x_1300_ = v___x_1294_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v___x_1298_);
v___x_1300_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
lean_object* v___x_1301_; 
v___x_1301_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0(v___x_1300_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_);
if (lean_obj_tag(v___x_1301_) == 0)
{
lean_dec_ref_known(v___x_1301_, 1);
v_a_1272_ = v___x_1291_;
goto v___jp_1271_;
}
else
{
lean_object* v_a_1302_; lean_object* v___x_1304_; uint8_t v_isShared_1305_; uint8_t v_isSharedCheck_1309_; 
lean_dec_ref(v___x_1291_);
v_a_1302_ = lean_ctor_get(v___x_1301_, 0);
v_isSharedCheck_1309_ = !lean_is_exclusive(v___x_1301_);
if (v_isSharedCheck_1309_ == 0)
{
v___x_1304_ = v___x_1301_;
v_isShared_1305_ = v_isSharedCheck_1309_;
goto v_resetjp_1303_;
}
else
{
lean_inc(v_a_1302_);
lean_dec(v___x_1301_);
v___x_1304_ = lean_box(0);
v_isShared_1305_ = v_isSharedCheck_1309_;
goto v_resetjp_1303_;
}
v_resetjp_1303_:
{
lean_object* v___x_1307_; 
if (v_isShared_1305_ == 0)
{
v___x_1307_ = v___x_1304_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1308_; 
v_reuseFailAlloc_1308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1308_, 0, v_a_1302_);
v___x_1307_ = v_reuseFailAlloc_1308_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
return v___x_1307_;
}
}
}
}
}
else
{
lean_object* v_a_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1318_; 
lean_del_object(v___x_1294_);
lean_dec(v_val_1292_);
lean_dec_ref(v___x_1291_);
lean_dec(v___x_1287_);
v_a_1311_ = lean_ctor_get(v___x_1296_, 0);
v_isSharedCheck_1318_ = !lean_is_exclusive(v___x_1296_);
if (v_isSharedCheck_1318_ == 0)
{
v___x_1313_ = v___x_1296_;
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_a_1311_);
lean_dec(v___x_1296_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v___x_1316_; 
if (v_isShared_1314_ == 0)
{
v___x_1316_ = v___x_1313_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v_a_1311_);
v___x_1316_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
return v___x_1316_;
}
}
}
}
}
else
{
lean_dec(v___x_1287_);
lean_dec(v_a_1286_);
v_a_1272_ = v___x_1291_;
goto v___jp_1271_;
}
}
}
}
}
v___jp_1271_:
{
size_t v___x_1273_; size_t v___x_1274_; 
v___x_1273_ = ((size_t)1ULL);
v___x_1274_ = lean_usize_add(v_i_1264_, v___x_1273_);
v_i_1264_ = v___x_1274_;
v_b_1265_ = v_a_1272_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_withReverted_spec__1___boxed(lean_object* v_as_1325_, lean_object* v_sz_1326_, lean_object* v_i_1327_, lean_object* v_b_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_){
_start:
{
size_t v_sz_boxed_1334_; size_t v_i_boxed_1335_; lean_object* v_res_1336_; 
v_sz_boxed_1334_ = lean_unbox_usize(v_sz_1326_);
lean_dec(v_sz_1326_);
v_i_boxed_1335_ = lean_unbox_usize(v_i_1327_);
lean_dec(v_i_1327_);
v_res_1336_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_withReverted_spec__1(v_as_1325_, v_sz_boxed_1334_, v_i_boxed_1335_, v_b_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_);
lean_dec(v___y_1332_);
lean_dec_ref(v___y_1331_);
lean_dec(v___y_1330_);
lean_dec_ref(v___y_1329_);
lean_dec_ref(v_as_1325_);
return v_res_1336_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withReverted___redArg___lam__0(lean_object* v_fst_1337_, size_t v_sz_1338_, size_t v___x_1339_, lean_object* v___x_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_){
_start:
{
lean_object* v___x_1346_; 
v___x_1346_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_withReverted_spec__1(v_fst_1337_, v_sz_1338_, v___x_1339_, v___x_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_);
if (lean_obj_tag(v___x_1346_) == 0)
{
lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1354_; 
v_isSharedCheck_1354_ = !lean_is_exclusive(v___x_1346_);
if (v_isSharedCheck_1354_ == 0)
{
lean_object* v_unused_1355_; 
v_unused_1355_ = lean_ctor_get(v___x_1346_, 0);
lean_dec(v_unused_1355_);
v___x_1348_ = v___x_1346_;
v_isShared_1349_ = v_isSharedCheck_1354_;
goto v_resetjp_1347_;
}
else
{
lean_dec(v___x_1346_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1354_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v___x_1350_; lean_object* v___x_1352_; 
v___x_1350_ = lean_box(0);
if (v_isShared_1349_ == 0)
{
lean_ctor_set(v___x_1348_, 0, v___x_1350_);
v___x_1352_ = v___x_1348_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v___x_1350_);
v___x_1352_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
return v___x_1352_;
}
}
}
else
{
lean_object* v_a_1356_; lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1363_; 
v_a_1356_ = lean_ctor_get(v___x_1346_, 0);
v_isSharedCheck_1363_ = !lean_is_exclusive(v___x_1346_);
if (v_isSharedCheck_1363_ == 0)
{
v___x_1358_ = v___x_1346_;
v_isShared_1359_ = v_isSharedCheck_1363_;
goto v_resetjp_1357_;
}
else
{
lean_inc(v_a_1356_);
lean_dec(v___x_1346_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1363_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
lean_object* v___x_1361_; 
if (v_isShared_1359_ == 0)
{
v___x_1361_ = v___x_1358_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v_a_1356_);
v___x_1361_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
return v___x_1361_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withReverted___redArg___lam__0___boxed(lean_object* v_fst_1364_, lean_object* v_sz_1365_, lean_object* v___x_1366_, lean_object* v___x_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_){
_start:
{
size_t v_sz_boxed_1373_; size_t v___x_3383__boxed_1374_; lean_object* v_res_1375_; 
v_sz_boxed_1373_ = lean_unbox_usize(v_sz_1365_);
lean_dec(v_sz_1365_);
v___x_3383__boxed_1374_ = lean_unbox_usize(v___x_1366_);
lean_dec(v___x_1366_);
v_res_1375_ = l_Lean_MVarId_withReverted___redArg___lam__0(v_fst_1364_, v_sz_boxed_1373_, v___x_3383__boxed_1374_, v___x_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_);
lean_dec(v___y_1371_);
lean_dec_ref(v___y_1370_);
lean_dec(v___y_1369_);
lean_dec_ref(v___y_1368_);
lean_dec_ref(v_fst_1364_);
return v_res_1375_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withReverted___redArg(lean_object* v_mvarId_1378_, lean_object* v_fvarIds_1379_, lean_object* v_k_1380_, uint8_t v_clearAuxDeclsInsteadOfRevert_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_){
_start:
{
uint8_t v___x_1387_; lean_object* v___x_1388_; 
v___x_1387_ = 1;
v___x_1388_ = l_Lean_MVarId_revert(v_mvarId_1378_, v_fvarIds_1379_, v___x_1387_, v_clearAuxDeclsInsteadOfRevert_1381_, v_a_1382_, v_a_1383_, v_a_1384_, v_a_1385_);
if (lean_obj_tag(v___x_1388_) == 0)
{
lean_object* v_a_1389_; lean_object* v_fst_1390_; lean_object* v_snd_1391_; lean_object* v___x_1392_; 
v_a_1389_ = lean_ctor_get(v___x_1388_, 0);
lean_inc(v_a_1389_);
lean_dec_ref_known(v___x_1388_, 1);
v_fst_1390_ = lean_ctor_get(v_a_1389_, 0);
lean_inc(v_fst_1390_);
v_snd_1391_ = lean_ctor_get(v_a_1389_, 1);
lean_inc(v_snd_1391_);
lean_dec(v_a_1389_);
lean_inc(v_a_1385_);
lean_inc_ref(v_a_1384_);
lean_inc(v_a_1383_);
lean_inc_ref(v_a_1382_);
v___x_1392_ = lean_apply_7(v_k_1380_, v_snd_1391_, v_fst_1390_, v_a_1382_, v_a_1383_, v_a_1384_, v_a_1385_, lean_box(0));
if (lean_obj_tag(v___x_1392_) == 0)
{
lean_object* v_a_1393_; lean_object* v_snd_1394_; lean_object* v_fst_1395_; lean_object* v_fst_1396_; lean_object* v_snd_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; uint8_t v___x_1400_; lean_object* v___x_1401_; 
v_a_1393_ = lean_ctor_get(v___x_1392_, 0);
lean_inc(v_a_1393_);
lean_dec_ref_known(v___x_1392_, 1);
v_snd_1394_ = lean_ctor_get(v_a_1393_, 1);
lean_inc(v_snd_1394_);
v_fst_1395_ = lean_ctor_get(v_a_1393_, 0);
lean_inc(v_fst_1395_);
lean_dec(v_a_1393_);
v_fst_1396_ = lean_ctor_get(v_snd_1394_, 0);
lean_inc(v_fst_1396_);
v_snd_1397_ = lean_ctor_get(v_snd_1394_, 1);
lean_inc(v_snd_1397_);
lean_dec(v_snd_1394_);
v___x_1398_ = lean_array_get_size(v_fst_1396_);
v___x_1399_ = lean_box(0);
v___x_1400_ = 0;
v___x_1401_ = l_Lean_Meta_introNCore(v_snd_1397_, v___x_1398_, v___x_1399_, v___x_1400_, v___x_1387_, v_a_1382_, v_a_1383_, v_a_1384_, v_a_1385_);
if (lean_obj_tag(v___x_1401_) == 0)
{
lean_object* v_a_1402_; lean_object* v_fst_1403_; lean_object* v_snd_1404_; lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1435_; 
v_a_1402_ = lean_ctor_get(v___x_1401_, 0);
lean_inc(v_a_1402_);
lean_dec_ref_known(v___x_1401_, 1);
v_fst_1403_ = lean_ctor_get(v_a_1402_, 0);
v_snd_1404_ = lean_ctor_get(v_a_1402_, 1);
v_isSharedCheck_1435_ = !lean_is_exclusive(v_a_1402_);
if (v_isSharedCheck_1435_ == 0)
{
v___x_1406_ = v_a_1402_;
v_isShared_1407_ = v_isSharedCheck_1435_;
goto v_resetjp_1405_;
}
else
{
lean_inc(v_snd_1404_);
lean_inc(v_fst_1403_);
lean_dec(v_a_1402_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1435_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; size_t v_sz_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___f_1414_; lean_object* v___x_1415_; 
v___x_1408_ = lean_unsigned_to_nat(0u);
v___x_1409_ = lean_array_get_size(v_fst_1403_);
v___x_1410_ = l_Array_toSubarray___redArg(v_fst_1403_, v___x_1408_, v___x_1409_);
v_sz_1411_ = lean_array_size(v_fst_1396_);
v___x_1412_ = lean_box_usize(v_sz_1411_);
v___x_1413_ = ((lean_object*)(l_Lean_MVarId_withReverted___redArg___boxed__const__1));
v___f_1414_ = lean_alloc_closure((void*)(l_Lean_MVarId_withReverted___redArg___lam__0___boxed), 9, 4);
lean_closure_set(v___f_1414_, 0, v_fst_1396_);
lean_closure_set(v___f_1414_, 1, v___x_1412_);
lean_closure_set(v___f_1414_, 2, v___x_1413_);
lean_closure_set(v___f_1414_, 3, v___x_1410_);
lean_inc(v_snd_1404_);
v___x_1415_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(v_snd_1404_, v___f_1414_, v_a_1382_, v_a_1383_, v_a_1384_, v_a_1385_);
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1425_; 
v_isSharedCheck_1425_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1425_ == 0)
{
lean_object* v_unused_1426_; 
v_unused_1426_ = lean_ctor_get(v___x_1415_, 0);
lean_dec(v_unused_1426_);
v___x_1417_ = v___x_1415_;
v_isShared_1418_ = v_isSharedCheck_1425_;
goto v_resetjp_1416_;
}
else
{
lean_dec(v___x_1415_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1425_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v___x_1420_; 
if (v_isShared_1407_ == 0)
{
lean_ctor_set(v___x_1406_, 0, v_fst_1395_);
v___x_1420_ = v___x_1406_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v_fst_1395_);
lean_ctor_set(v_reuseFailAlloc_1424_, 1, v_snd_1404_);
v___x_1420_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
lean_object* v___x_1422_; 
if (v_isShared_1418_ == 0)
{
lean_ctor_set(v___x_1417_, 0, v___x_1420_);
v___x_1422_ = v___x_1417_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v___x_1420_);
v___x_1422_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
return v___x_1422_;
}
}
}
}
else
{
lean_object* v_a_1427_; lean_object* v___x_1429_; uint8_t v_isShared_1430_; uint8_t v_isSharedCheck_1434_; 
lean_del_object(v___x_1406_);
lean_dec(v_snd_1404_);
lean_dec(v_fst_1395_);
v_a_1427_ = lean_ctor_get(v___x_1415_, 0);
v_isSharedCheck_1434_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1434_ == 0)
{
v___x_1429_ = v___x_1415_;
v_isShared_1430_ = v_isSharedCheck_1434_;
goto v_resetjp_1428_;
}
else
{
lean_inc(v_a_1427_);
lean_dec(v___x_1415_);
v___x_1429_ = lean_box(0);
v_isShared_1430_ = v_isSharedCheck_1434_;
goto v_resetjp_1428_;
}
v_resetjp_1428_:
{
lean_object* v___x_1432_; 
if (v_isShared_1430_ == 0)
{
v___x_1432_ = v___x_1429_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v_a_1427_);
v___x_1432_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
return v___x_1432_;
}
}
}
}
}
else
{
lean_object* v_a_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1443_; 
lean_dec(v_fst_1396_);
lean_dec(v_fst_1395_);
v_a_1436_ = lean_ctor_get(v___x_1401_, 0);
v_isSharedCheck_1443_ = !lean_is_exclusive(v___x_1401_);
if (v_isSharedCheck_1443_ == 0)
{
v___x_1438_ = v___x_1401_;
v_isShared_1439_ = v_isSharedCheck_1443_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_a_1436_);
lean_dec(v___x_1401_);
v___x_1438_ = lean_box(0);
v_isShared_1439_ = v_isSharedCheck_1443_;
goto v_resetjp_1437_;
}
v_resetjp_1437_:
{
lean_object* v___x_1441_; 
if (v_isShared_1439_ == 0)
{
v___x_1441_ = v___x_1438_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v_a_1436_);
v___x_1441_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
return v___x_1441_;
}
}
}
}
else
{
lean_object* v_a_1444_; lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1451_; 
v_a_1444_ = lean_ctor_get(v___x_1392_, 0);
v_isSharedCheck_1451_ = !lean_is_exclusive(v___x_1392_);
if (v_isSharedCheck_1451_ == 0)
{
v___x_1446_ = v___x_1392_;
v_isShared_1447_ = v_isSharedCheck_1451_;
goto v_resetjp_1445_;
}
else
{
lean_inc(v_a_1444_);
lean_dec(v___x_1392_);
v___x_1446_ = lean_box(0);
v_isShared_1447_ = v_isSharedCheck_1451_;
goto v_resetjp_1445_;
}
v_resetjp_1445_:
{
lean_object* v___x_1449_; 
if (v_isShared_1447_ == 0)
{
v___x_1449_ = v___x_1446_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v_a_1444_);
v___x_1449_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
return v___x_1449_;
}
}
}
}
else
{
lean_object* v_a_1452_; lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1459_; 
lean_dec_ref(v_k_1380_);
v_a_1452_ = lean_ctor_get(v___x_1388_, 0);
v_isSharedCheck_1459_ = !lean_is_exclusive(v___x_1388_);
if (v_isSharedCheck_1459_ == 0)
{
v___x_1454_ = v___x_1388_;
v_isShared_1455_ = v_isSharedCheck_1459_;
goto v_resetjp_1453_;
}
else
{
lean_inc(v_a_1452_);
lean_dec(v___x_1388_);
v___x_1454_ = lean_box(0);
v_isShared_1455_ = v_isSharedCheck_1459_;
goto v_resetjp_1453_;
}
v_resetjp_1453_:
{
lean_object* v___x_1457_; 
if (v_isShared_1455_ == 0)
{
v___x_1457_ = v___x_1454_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v_a_1452_);
v___x_1457_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
return v___x_1457_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withReverted___redArg___boxed(lean_object* v_mvarId_1460_, lean_object* v_fvarIds_1461_, lean_object* v_k_1462_, lean_object* v_clearAuxDeclsInsteadOfRevert_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_){
_start:
{
uint8_t v_clearAuxDeclsInsteadOfRevert_boxed_1469_; lean_object* v_res_1470_; 
v_clearAuxDeclsInsteadOfRevert_boxed_1469_ = lean_unbox(v_clearAuxDeclsInsteadOfRevert_1463_);
v_res_1470_ = l_Lean_MVarId_withReverted___redArg(v_mvarId_1460_, v_fvarIds_1461_, v_k_1462_, v_clearAuxDeclsInsteadOfRevert_boxed_1469_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_);
lean_dec(v_a_1467_);
lean_dec_ref(v_a_1466_);
lean_dec(v_a_1465_);
lean_dec_ref(v_a_1464_);
return v_res_1470_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withReverted(lean_object* v_00_u03b1_1471_, lean_object* v_mvarId_1472_, lean_object* v_fvarIds_1473_, lean_object* v_k_1474_, uint8_t v_clearAuxDeclsInsteadOfRevert_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_){
_start:
{
lean_object* v___x_1481_; 
v___x_1481_ = l_Lean_MVarId_withReverted___redArg(v_mvarId_1472_, v_fvarIds_1473_, v_k_1474_, v_clearAuxDeclsInsteadOfRevert_1475_, v_a_1476_, v_a_1477_, v_a_1478_, v_a_1479_);
return v___x_1481_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withReverted___boxed(lean_object* v_00_u03b1_1482_, lean_object* v_mvarId_1483_, lean_object* v_fvarIds_1484_, lean_object* v_k_1485_, lean_object* v_clearAuxDeclsInsteadOfRevert_1486_, lean_object* v_a_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_){
_start:
{
uint8_t v_clearAuxDeclsInsteadOfRevert_boxed_1492_; lean_object* v_res_1493_; 
v_clearAuxDeclsInsteadOfRevert_boxed_1492_ = lean_unbox(v_clearAuxDeclsInsteadOfRevert_1486_);
v_res_1493_ = l_Lean_MVarId_withReverted(v_00_u03b1_1482_, v_mvarId_1483_, v_fvarIds_1484_, v_k_1485_, v_clearAuxDeclsInsteadOfRevert_boxed_1492_, v_a_1487_, v_a_1488_, v_a_1489_, v_a_1490_);
lean_dec(v_a_1490_);
lean_dec_ref(v_a_1489_);
lean_dec(v_a_1488_);
lean_dec_ref(v_a_1487_);
return v_res_1493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0_spec__0(lean_object* v_t_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_){
_start:
{
lean_object* v___x_1500_; 
v___x_1500_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0_spec__0___redArg(v_t_1494_, v___y_1498_);
return v___x_1500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0_spec__0___boxed(lean_object* v_t_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_){
_start:
{
lean_object* v_res_1507_; 
v_res_1507_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0_spec__0(v_t_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_);
lean_dec(v___y_1505_);
lean_dec_ref(v___y_1504_);
lean_dec(v___y_1503_);
lean_dec_ref(v___y_1502_);
return v_res_1507_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withRevertedFrom___redArg(lean_object* v_mvarId_1508_, lean_object* v_fvarId_1509_, lean_object* v_k_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_){
_start:
{
lean_object* v___x_1516_; 
v___x_1516_ = l_Lean_MVarId_revertFrom(v_mvarId_1508_, v_fvarId_1509_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_);
if (lean_obj_tag(v___x_1516_) == 0)
{
lean_object* v_a_1517_; lean_object* v_fst_1518_; lean_object* v_snd_1519_; lean_object* v___x_1520_; 
v_a_1517_ = lean_ctor_get(v___x_1516_, 0);
lean_inc(v_a_1517_);
lean_dec_ref_known(v___x_1516_, 1);
v_fst_1518_ = lean_ctor_get(v_a_1517_, 0);
lean_inc(v_fst_1518_);
v_snd_1519_ = lean_ctor_get(v_a_1517_, 1);
lean_inc(v_snd_1519_);
lean_dec(v_a_1517_);
lean_inc(v_a_1514_);
lean_inc_ref(v_a_1513_);
lean_inc(v_a_1512_);
lean_inc_ref(v_a_1511_);
v___x_1520_ = lean_apply_7(v_k_1510_, v_snd_1519_, v_fst_1518_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_, lean_box(0));
if (lean_obj_tag(v___x_1520_) == 0)
{
lean_object* v_a_1521_; lean_object* v_snd_1522_; lean_object* v_fst_1523_; lean_object* v_fst_1524_; lean_object* v_snd_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; uint8_t v___x_1528_; uint8_t v___x_1529_; lean_object* v___x_1530_; 
v_a_1521_ = lean_ctor_get(v___x_1520_, 0);
lean_inc(v_a_1521_);
lean_dec_ref_known(v___x_1520_, 1);
v_snd_1522_ = lean_ctor_get(v_a_1521_, 1);
lean_inc(v_snd_1522_);
v_fst_1523_ = lean_ctor_get(v_a_1521_, 0);
lean_inc(v_fst_1523_);
lean_dec(v_a_1521_);
v_fst_1524_ = lean_ctor_get(v_snd_1522_, 0);
lean_inc(v_fst_1524_);
v_snd_1525_ = lean_ctor_get(v_snd_1522_, 1);
lean_inc(v_snd_1525_);
lean_dec(v_snd_1522_);
v___x_1526_ = lean_array_get_size(v_fst_1524_);
v___x_1527_ = lean_box(0);
v___x_1528_ = 0;
v___x_1529_ = 1;
v___x_1530_ = l_Lean_Meta_introNCore(v_snd_1525_, v___x_1526_, v___x_1527_, v___x_1528_, v___x_1529_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_);
if (lean_obj_tag(v___x_1530_) == 0)
{
lean_object* v_a_1531_; lean_object* v_fst_1532_; lean_object* v_snd_1533_; lean_object* v___x_1535_; uint8_t v_isShared_1536_; uint8_t v_isSharedCheck_1564_; 
v_a_1531_ = lean_ctor_get(v___x_1530_, 0);
lean_inc(v_a_1531_);
lean_dec_ref_known(v___x_1530_, 1);
v_fst_1532_ = lean_ctor_get(v_a_1531_, 0);
v_snd_1533_ = lean_ctor_get(v_a_1531_, 1);
v_isSharedCheck_1564_ = !lean_is_exclusive(v_a_1531_);
if (v_isSharedCheck_1564_ == 0)
{
v___x_1535_ = v_a_1531_;
v_isShared_1536_ = v_isSharedCheck_1564_;
goto v_resetjp_1534_;
}
else
{
lean_inc(v_snd_1533_);
lean_inc(v_fst_1532_);
lean_dec(v_a_1531_);
v___x_1535_ = lean_box(0);
v_isShared_1536_ = v_isSharedCheck_1564_;
goto v_resetjp_1534_;
}
v_resetjp_1534_:
{
lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; size_t v_sz_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___f_1543_; lean_object* v___x_1544_; 
v___x_1537_ = lean_unsigned_to_nat(0u);
v___x_1538_ = lean_array_get_size(v_fst_1532_);
v___x_1539_ = l_Array_toSubarray___redArg(v_fst_1532_, v___x_1537_, v___x_1538_);
v_sz_1540_ = lean_array_size(v_fst_1524_);
v___x_1541_ = lean_box_usize(v_sz_1540_);
v___x_1542_ = ((lean_object*)(l_Lean_MVarId_withReverted___redArg___boxed__const__1));
v___f_1543_ = lean_alloc_closure((void*)(l_Lean_MVarId_withReverted___redArg___lam__0___boxed), 9, 4);
lean_closure_set(v___f_1543_, 0, v_fst_1524_);
lean_closure_set(v___f_1543_, 1, v___x_1541_);
lean_closure_set(v___f_1543_, 2, v___x_1542_);
lean_closure_set(v___f_1543_, 3, v___x_1539_);
lean_inc(v_snd_1533_);
v___x_1544_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(v_snd_1533_, v___f_1543_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_);
if (lean_obj_tag(v___x_1544_) == 0)
{
lean_object* v___x_1546_; uint8_t v_isShared_1547_; uint8_t v_isSharedCheck_1554_; 
v_isSharedCheck_1554_ = !lean_is_exclusive(v___x_1544_);
if (v_isSharedCheck_1554_ == 0)
{
lean_object* v_unused_1555_; 
v_unused_1555_ = lean_ctor_get(v___x_1544_, 0);
lean_dec(v_unused_1555_);
v___x_1546_ = v___x_1544_;
v_isShared_1547_ = v_isSharedCheck_1554_;
goto v_resetjp_1545_;
}
else
{
lean_dec(v___x_1544_);
v___x_1546_ = lean_box(0);
v_isShared_1547_ = v_isSharedCheck_1554_;
goto v_resetjp_1545_;
}
v_resetjp_1545_:
{
lean_object* v___x_1549_; 
if (v_isShared_1536_ == 0)
{
lean_ctor_set(v___x_1535_, 0, v_fst_1523_);
v___x_1549_ = v___x_1535_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v_fst_1523_);
lean_ctor_set(v_reuseFailAlloc_1553_, 1, v_snd_1533_);
v___x_1549_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1548_;
}
v_reusejp_1548_:
{
lean_object* v___x_1551_; 
if (v_isShared_1547_ == 0)
{
lean_ctor_set(v___x_1546_, 0, v___x_1549_);
v___x_1551_ = v___x_1546_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v___x_1549_);
v___x_1551_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
return v___x_1551_;
}
}
}
}
else
{
lean_object* v_a_1556_; lean_object* v___x_1558_; uint8_t v_isShared_1559_; uint8_t v_isSharedCheck_1563_; 
lean_del_object(v___x_1535_);
lean_dec(v_snd_1533_);
lean_dec(v_fst_1523_);
v_a_1556_ = lean_ctor_get(v___x_1544_, 0);
v_isSharedCheck_1563_ = !lean_is_exclusive(v___x_1544_);
if (v_isSharedCheck_1563_ == 0)
{
v___x_1558_ = v___x_1544_;
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
else
{
lean_inc(v_a_1556_);
lean_dec(v___x_1544_);
v___x_1558_ = lean_box(0);
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
v_resetjp_1557_:
{
lean_object* v___x_1561_; 
if (v_isShared_1559_ == 0)
{
v___x_1561_ = v___x_1558_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v_a_1556_);
v___x_1561_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
return v___x_1561_;
}
}
}
}
}
else
{
lean_object* v_a_1565_; lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1572_; 
lean_dec(v_fst_1524_);
lean_dec(v_fst_1523_);
v_a_1565_ = lean_ctor_get(v___x_1530_, 0);
v_isSharedCheck_1572_ = !lean_is_exclusive(v___x_1530_);
if (v_isSharedCheck_1572_ == 0)
{
v___x_1567_ = v___x_1530_;
v_isShared_1568_ = v_isSharedCheck_1572_;
goto v_resetjp_1566_;
}
else
{
lean_inc(v_a_1565_);
lean_dec(v___x_1530_);
v___x_1567_ = lean_box(0);
v_isShared_1568_ = v_isSharedCheck_1572_;
goto v_resetjp_1566_;
}
v_resetjp_1566_:
{
lean_object* v___x_1570_; 
if (v_isShared_1568_ == 0)
{
v___x_1570_ = v___x_1567_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v_a_1565_);
v___x_1570_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
return v___x_1570_;
}
}
}
}
else
{
lean_object* v_a_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1580_; 
v_a_1573_ = lean_ctor_get(v___x_1520_, 0);
v_isSharedCheck_1580_ = !lean_is_exclusive(v___x_1520_);
if (v_isSharedCheck_1580_ == 0)
{
v___x_1575_ = v___x_1520_;
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_a_1573_);
lean_dec(v___x_1520_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
lean_object* v___x_1578_; 
if (v_isShared_1576_ == 0)
{
v___x_1578_ = v___x_1575_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v_a_1573_);
v___x_1578_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
return v___x_1578_;
}
}
}
}
else
{
lean_object* v_a_1581_; lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1588_; 
lean_dec_ref(v_k_1510_);
v_a_1581_ = lean_ctor_get(v___x_1516_, 0);
v_isSharedCheck_1588_ = !lean_is_exclusive(v___x_1516_);
if (v_isSharedCheck_1588_ == 0)
{
v___x_1583_ = v___x_1516_;
v_isShared_1584_ = v_isSharedCheck_1588_;
goto v_resetjp_1582_;
}
else
{
lean_inc(v_a_1581_);
lean_dec(v___x_1516_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1588_;
goto v_resetjp_1582_;
}
v_resetjp_1582_:
{
lean_object* v___x_1586_; 
if (v_isShared_1584_ == 0)
{
v___x_1586_ = v___x_1583_;
goto v_reusejp_1585_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v_a_1581_);
v___x_1586_ = v_reuseFailAlloc_1587_;
goto v_reusejp_1585_;
}
v_reusejp_1585_:
{
return v___x_1586_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withRevertedFrom___redArg___boxed(lean_object* v_mvarId_1589_, lean_object* v_fvarId_1590_, lean_object* v_k_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_){
_start:
{
lean_object* v_res_1597_; 
v_res_1597_ = l_Lean_MVarId_withRevertedFrom___redArg(v_mvarId_1589_, v_fvarId_1590_, v_k_1591_, v_a_1592_, v_a_1593_, v_a_1594_, v_a_1595_);
lean_dec(v_a_1595_);
lean_dec_ref(v_a_1594_);
lean_dec(v_a_1593_);
lean_dec_ref(v_a_1592_);
return v_res_1597_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withRevertedFrom(lean_object* v_00_u03b1_1598_, lean_object* v_mvarId_1599_, lean_object* v_fvarId_1600_, lean_object* v_k_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_){
_start:
{
lean_object* v___x_1607_; 
v___x_1607_ = l_Lean_MVarId_withRevertedFrom___redArg(v_mvarId_1599_, v_fvarId_1600_, v_k_1601_, v_a_1602_, v_a_1603_, v_a_1604_, v_a_1605_);
return v___x_1607_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withRevertedFrom___boxed(lean_object* v_00_u03b1_1608_, lean_object* v_mvarId_1609_, lean_object* v_fvarId_1610_, lean_object* v_k_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_){
_start:
{
lean_object* v_res_1617_; 
v_res_1617_ = l_Lean_MVarId_withRevertedFrom(v_00_u03b1_1608_, v_mvarId_1609_, v_fvarId_1610_, v_k_1611_, v_a_1612_, v_a_1613_, v_a_1614_, v_a_1615_);
lean_dec(v_a_1615_);
lean_dec_ref(v_a_1614_);
lean_dec(v_a_1613_);
lean_dec_ref(v_a_1612_);
return v_res_1617_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_changeLocalDecl___lam__0(uint8_t v_checkDefEq_1618_, lean_object* v_typeNew_1619_, lean_object* v___x_1620_, lean_object* v_mvarId_1621_, lean_object* v_typeOld_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_){
_start:
{
if (v_checkDefEq_1618_ == 0)
{
lean_object* v___x_1628_; lean_object* v___x_1629_; 
lean_dec_ref(v_typeOld_1622_);
lean_dec(v_mvarId_1621_);
lean_dec(v___x_1620_);
lean_dec_ref(v_typeNew_1619_);
v___x_1628_ = lean_box(0);
v___x_1629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1629_, 0, v___x_1628_);
return v___x_1629_;
}
else
{
lean_object* v___x_1630_; 
lean_inc_ref(v_typeOld_1622_);
lean_inc_ref(v_typeNew_1619_);
v___x_1630_ = l_Lean_Meta_isExprDefEq(v_typeNew_1619_, v_typeOld_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_);
if (lean_obj_tag(v___x_1630_) == 0)
{
lean_object* v_a_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1649_; 
v_a_1631_ = lean_ctor_get(v___x_1630_, 0);
v_isSharedCheck_1649_ = !lean_is_exclusive(v___x_1630_);
if (v_isSharedCheck_1649_ == 0)
{
v___x_1633_ = v___x_1630_;
v_isShared_1634_ = v_isSharedCheck_1649_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_a_1631_);
lean_dec(v___x_1630_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1649_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
uint8_t v___x_1635_; 
v___x_1635_ = lean_unbox(v_a_1631_);
lean_dec(v_a_1631_);
if (v___x_1635_ == 0)
{
lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; 
lean_del_object(v___x_1633_);
v___x_1636_ = lean_obj_once(&l_Lean_MVarId_change___lam__0___closed__1, &l_Lean_MVarId_change___lam__0___closed__1_once, _init_l_Lean_MVarId_change___lam__0___closed__1);
v___x_1637_ = l_Lean_indentExpr(v_typeNew_1619_);
v___x_1638_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1638_, 0, v___x_1636_);
lean_ctor_set(v___x_1638_, 1, v___x_1637_);
v___x_1639_ = lean_obj_once(&l_Lean_MVarId_change___lam__0___closed__3, &l_Lean_MVarId_change___lam__0___closed__3_once, _init_l_Lean_MVarId_change___lam__0___closed__3);
v___x_1640_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1640_, 0, v___x_1638_);
lean_ctor_set(v___x_1640_, 1, v___x_1639_);
v___x_1641_ = l_Lean_indentExpr(v_typeOld_1622_);
v___x_1642_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1642_, 0, v___x_1640_);
lean_ctor_set(v___x_1642_, 1, v___x_1641_);
v___x_1643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1643_, 0, v___x_1642_);
v___x_1644_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1620_, v_mvarId_1621_, v___x_1643_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_);
return v___x_1644_;
}
else
{
lean_object* v___x_1645_; lean_object* v___x_1647_; 
lean_dec_ref(v_typeOld_1622_);
lean_dec(v_mvarId_1621_);
lean_dec(v___x_1620_);
lean_dec_ref(v_typeNew_1619_);
v___x_1645_ = lean_box(0);
if (v_isShared_1634_ == 0)
{
lean_ctor_set(v___x_1633_, 0, v___x_1645_);
v___x_1647_ = v___x_1633_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v___x_1645_);
v___x_1647_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
return v___x_1647_;
}
}
}
}
else
{
lean_object* v_a_1650_; lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1657_; 
lean_dec_ref(v_typeOld_1622_);
lean_dec(v_mvarId_1621_);
lean_dec(v___x_1620_);
lean_dec_ref(v_typeNew_1619_);
v_a_1650_ = lean_ctor_get(v___x_1630_, 0);
v_isSharedCheck_1657_ = !lean_is_exclusive(v___x_1630_);
if (v_isSharedCheck_1657_ == 0)
{
v___x_1652_ = v___x_1630_;
v_isShared_1653_ = v_isSharedCheck_1657_;
goto v_resetjp_1651_;
}
else
{
lean_inc(v_a_1650_);
lean_dec(v___x_1630_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1657_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
lean_object* v___x_1655_; 
if (v_isShared_1653_ == 0)
{
v___x_1655_ = v___x_1652_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v_a_1650_);
v___x_1655_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
return v___x_1655_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_changeLocalDecl___lam__0___boxed(lean_object* v_checkDefEq_1658_, lean_object* v_typeNew_1659_, lean_object* v___x_1660_, lean_object* v_mvarId_1661_, lean_object* v_typeOld_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_){
_start:
{
uint8_t v_checkDefEq_boxed_1668_; lean_object* v_res_1669_; 
v_checkDefEq_boxed_1668_ = lean_unbox(v_checkDefEq_1658_);
v_res_1669_ = l_Lean_MVarId_changeLocalDecl___lam__0(v_checkDefEq_boxed_1668_, v_typeNew_1659_, v___x_1660_, v_mvarId_1661_, v_typeOld_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_);
lean_dec(v___y_1666_);
lean_dec_ref(v___y_1665_);
lean_dec(v___y_1664_);
lean_dec_ref(v___y_1663_);
return v_res_1669_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_changeLocalDecl_spec__0(size_t v_sz_1670_, size_t v_i_1671_, lean_object* v_bs_1672_){
_start:
{
uint8_t v___x_1673_; 
v___x_1673_ = lean_usize_dec_lt(v_i_1671_, v_sz_1670_);
if (v___x_1673_ == 0)
{
return v_bs_1672_;
}
else
{
lean_object* v_v_1674_; lean_object* v___x_1675_; lean_object* v_bs_x27_1676_; lean_object* v___x_1677_; size_t v___x_1678_; size_t v___x_1679_; lean_object* v___x_1680_; 
v_v_1674_ = lean_array_uget(v_bs_1672_, v_i_1671_);
v___x_1675_ = lean_unsigned_to_nat(0u);
v_bs_x27_1676_ = lean_array_uset(v_bs_1672_, v_i_1671_, v___x_1675_);
v___x_1677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1677_, 0, v_v_1674_);
v___x_1678_ = ((size_t)1ULL);
v___x_1679_ = lean_usize_add(v_i_1671_, v___x_1678_);
v___x_1680_ = lean_array_uset(v_bs_x27_1676_, v_i_1671_, v___x_1677_);
v_i_1671_ = v___x_1679_;
v_bs_1672_ = v___x_1680_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_changeLocalDecl_spec__0___boxed(lean_object* v_sz_1682_, lean_object* v_i_1683_, lean_object* v_bs_1684_){
_start:
{
size_t v_sz_boxed_1685_; size_t v_i_boxed_1686_; lean_object* v_res_1687_; 
v_sz_boxed_1685_ = lean_unbox_usize(v_sz_1682_);
lean_dec(v_sz_1682_);
v_i_boxed_1686_ = lean_unbox_usize(v_i_1683_);
lean_dec(v_i_1683_);
v_res_1687_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_changeLocalDecl_spec__0(v_sz_boxed_1685_, v_i_boxed_1686_, v_bs_1684_);
return v_res_1687_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_changeLocalDecl___lam__1(lean_object* v_mvarId_1688_, lean_object* v_fvars_1689_, lean_object* v_targetNew_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_){
_start:
{
lean_object* v___x_1696_; 
v___x_1696_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_1688_, v_targetNew_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_);
if (lean_obj_tag(v___x_1696_) == 0)
{
lean_object* v_a_1697_; lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_1710_; 
v_a_1697_ = lean_ctor_get(v___x_1696_, 0);
v_isSharedCheck_1710_ = !lean_is_exclusive(v___x_1696_);
if (v_isSharedCheck_1710_ == 0)
{
v___x_1699_ = v___x_1696_;
v_isShared_1700_ = v_isSharedCheck_1710_;
goto v_resetjp_1698_;
}
else
{
lean_inc(v_a_1697_);
lean_dec(v___x_1696_);
v___x_1699_ = lean_box(0);
v_isShared_1700_ = v_isSharedCheck_1710_;
goto v_resetjp_1698_;
}
v_resetjp_1698_:
{
lean_object* v___x_1701_; size_t v_sz_1702_; size_t v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1708_; 
v___x_1701_ = lean_box(0);
v_sz_1702_ = lean_array_size(v_fvars_1689_);
v___x_1703_ = ((size_t)0ULL);
v___x_1704_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_changeLocalDecl_spec__0(v_sz_1702_, v___x_1703_, v_fvars_1689_);
v___x_1705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1705_, 0, v___x_1704_);
lean_ctor_set(v___x_1705_, 1, v_a_1697_);
v___x_1706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1706_, 0, v___x_1701_);
lean_ctor_set(v___x_1706_, 1, v___x_1705_);
if (v_isShared_1700_ == 0)
{
lean_ctor_set(v___x_1699_, 0, v___x_1706_);
v___x_1708_ = v___x_1699_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v___x_1706_);
v___x_1708_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
return v___x_1708_;
}
}
}
else
{
lean_object* v_a_1711_; lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1718_; 
lean_dec_ref(v_fvars_1689_);
v_a_1711_ = lean_ctor_get(v___x_1696_, 0);
v_isSharedCheck_1718_ = !lean_is_exclusive(v___x_1696_);
if (v_isSharedCheck_1718_ == 0)
{
v___x_1713_ = v___x_1696_;
v_isShared_1714_ = v_isSharedCheck_1718_;
goto v_resetjp_1712_;
}
else
{
lean_inc(v_a_1711_);
lean_dec(v___x_1696_);
v___x_1713_ = lean_box(0);
v_isShared_1714_ = v_isSharedCheck_1718_;
goto v_resetjp_1712_;
}
v_resetjp_1712_:
{
lean_object* v___x_1716_; 
if (v_isShared_1714_ == 0)
{
v___x_1716_ = v___x_1713_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v_a_1711_);
v___x_1716_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
return v___x_1716_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_changeLocalDecl___lam__1___boxed(lean_object* v_mvarId_1719_, lean_object* v_fvars_1720_, lean_object* v_targetNew_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_){
_start:
{
lean_object* v_res_1727_; 
v_res_1727_ = l_Lean_MVarId_changeLocalDecl___lam__1(v_mvarId_1719_, v_fvars_1720_, v_targetNew_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_);
lean_dec(v___y_1725_);
lean_dec_ref(v___y_1724_);
lean_dec(v___y_1723_);
lean_dec_ref(v___y_1722_);
return v_res_1727_;
}
}
static lean_object* _init_l_Lean_MVarId_changeLocalDecl___lam__2___closed__2(void){
_start:
{
lean_object* v___x_1731_; lean_object* v___x_1732_; 
v___x_1731_ = ((lean_object*)(l_Lean_MVarId_changeLocalDecl___lam__2___closed__1));
v___x_1732_ = l_Lean_MessageData_ofFormat(v___x_1731_);
return v___x_1732_;
}
}
static lean_object* _init_l_Lean_MVarId_changeLocalDecl___lam__2___closed__3(void){
_start:
{
lean_object* v___x_1733_; lean_object* v___x_1734_; 
v___x_1733_ = lean_obj_once(&l_Lean_MVarId_changeLocalDecl___lam__2___closed__2, &l_Lean_MVarId_changeLocalDecl___lam__2___closed__2_once, _init_l_Lean_MVarId_changeLocalDecl___lam__2___closed__2);
v___x_1734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1734_, 0, v___x_1733_);
return v___x_1734_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_changeLocalDecl___lam__2(lean_object* v_mvarId_1735_, lean_object* v___f_1736_, lean_object* v_typeNew_1737_, lean_object* v___f_1738_, lean_object* v___x_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_){
_start:
{
lean_object* v___x_1745_; 
lean_inc(v_mvarId_1735_);
v___x_1745_ = l_Lean_MVarId_getType(v_mvarId_1735_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_);
if (lean_obj_tag(v___x_1745_) == 0)
{
lean_object* v_a_1746_; 
v_a_1746_ = lean_ctor_get(v___x_1745_, 0);
lean_inc(v_a_1746_);
lean_dec_ref_known(v___x_1745_, 1);
switch(lean_obj_tag(v_a_1746_))
{
case 7:
{
lean_object* v_binderName_1747_; lean_object* v_binderType_1748_; lean_object* v_body_1749_; uint8_t v_binderInfo_1750_; lean_object* v___x_1751_; 
lean_dec(v___x_1739_);
lean_dec(v_mvarId_1735_);
v_binderName_1747_ = lean_ctor_get(v_a_1746_, 0);
lean_inc(v_binderName_1747_);
v_binderType_1748_ = lean_ctor_get(v_a_1746_, 1);
lean_inc_ref(v_binderType_1748_);
v_body_1749_ = lean_ctor_get(v_a_1746_, 2);
lean_inc_ref(v_body_1749_);
v_binderInfo_1750_ = lean_ctor_get_uint8(v_a_1746_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_1746_, 3);
lean_inc(v___y_1743_);
lean_inc_ref(v___y_1742_);
lean_inc(v___y_1741_);
lean_inc_ref(v___y_1740_);
v___x_1751_ = lean_apply_6(v___f_1736_, v_binderType_1748_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_, lean_box(0));
if (lean_obj_tag(v___x_1751_) == 0)
{
lean_object* v___x_1752_; lean_object* v___x_1753_; 
lean_dec_ref_known(v___x_1751_, 1);
v___x_1752_ = l_Lean_Expr_forallE___override(v_binderName_1747_, v_typeNew_1737_, v_body_1749_, v_binderInfo_1750_);
v___x_1753_ = lean_apply_6(v___f_1738_, v___x_1752_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_, lean_box(0));
return v___x_1753_;
}
else
{
lean_object* v_a_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1761_; 
lean_dec_ref(v_body_1749_);
lean_dec(v_binderName_1747_);
lean_dec(v___y_1743_);
lean_dec_ref(v___y_1742_);
lean_dec(v___y_1741_);
lean_dec_ref(v___y_1740_);
lean_dec_ref(v___f_1738_);
lean_dec_ref(v_typeNew_1737_);
v_a_1754_ = lean_ctor_get(v___x_1751_, 0);
v_isSharedCheck_1761_ = !lean_is_exclusive(v___x_1751_);
if (v_isSharedCheck_1761_ == 0)
{
v___x_1756_ = v___x_1751_;
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_a_1754_);
lean_dec(v___x_1751_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v___x_1759_; 
if (v_isShared_1757_ == 0)
{
v___x_1759_ = v___x_1756_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v_a_1754_);
v___x_1759_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
return v___x_1759_;
}
}
}
}
case 8:
{
lean_object* v_declName_1762_; lean_object* v_type_1763_; lean_object* v_value_1764_; lean_object* v_body_1765_; uint8_t v_nondep_1766_; lean_object* v___x_1767_; 
lean_dec(v___x_1739_);
lean_dec(v_mvarId_1735_);
v_declName_1762_ = lean_ctor_get(v_a_1746_, 0);
lean_inc(v_declName_1762_);
v_type_1763_ = lean_ctor_get(v_a_1746_, 1);
lean_inc_ref(v_type_1763_);
v_value_1764_ = lean_ctor_get(v_a_1746_, 2);
lean_inc_ref(v_value_1764_);
v_body_1765_ = lean_ctor_get(v_a_1746_, 3);
lean_inc_ref(v_body_1765_);
v_nondep_1766_ = lean_ctor_get_uint8(v_a_1746_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_a_1746_, 4);
lean_inc(v___y_1743_);
lean_inc_ref(v___y_1742_);
lean_inc(v___y_1741_);
lean_inc_ref(v___y_1740_);
v___x_1767_ = lean_apply_6(v___f_1736_, v_type_1763_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_, lean_box(0));
if (lean_obj_tag(v___x_1767_) == 0)
{
lean_object* v___x_1768_; lean_object* v___x_1769_; 
lean_dec_ref_known(v___x_1767_, 1);
v___x_1768_ = l_Lean_Expr_letE___override(v_declName_1762_, v_typeNew_1737_, v_value_1764_, v_body_1765_, v_nondep_1766_);
v___x_1769_ = lean_apply_6(v___f_1738_, v___x_1768_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_, lean_box(0));
return v___x_1769_;
}
else
{
lean_object* v_a_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1777_; 
lean_dec_ref(v_body_1765_);
lean_dec_ref(v_value_1764_);
lean_dec(v_declName_1762_);
lean_dec(v___y_1743_);
lean_dec_ref(v___y_1742_);
lean_dec(v___y_1741_);
lean_dec_ref(v___y_1740_);
lean_dec_ref(v___f_1738_);
lean_dec_ref(v_typeNew_1737_);
v_a_1770_ = lean_ctor_get(v___x_1767_, 0);
v_isSharedCheck_1777_ = !lean_is_exclusive(v___x_1767_);
if (v_isSharedCheck_1777_ == 0)
{
v___x_1772_ = v___x_1767_;
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_a_1770_);
lean_dec(v___x_1767_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v___x_1775_; 
if (v_isShared_1773_ == 0)
{
v___x_1775_ = v___x_1772_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v_a_1770_);
v___x_1775_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
return v___x_1775_;
}
}
}
}
default: 
{
lean_object* v___x_1778_; lean_object* v___x_1779_; 
lean_dec(v_a_1746_);
lean_dec_ref(v___f_1738_);
lean_dec_ref(v_typeNew_1737_);
lean_dec_ref(v___f_1736_);
v___x_1778_ = lean_obj_once(&l_Lean_MVarId_changeLocalDecl___lam__2___closed__3, &l_Lean_MVarId_changeLocalDecl___lam__2___closed__3_once, _init_l_Lean_MVarId_changeLocalDecl___lam__2___closed__3);
v___x_1779_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1739_, v_mvarId_1735_, v___x_1778_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_);
lean_dec(v___y_1743_);
lean_dec_ref(v___y_1742_);
lean_dec(v___y_1741_);
lean_dec_ref(v___y_1740_);
return v___x_1779_;
}
}
}
else
{
lean_object* v_a_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1787_; 
lean_dec(v___y_1743_);
lean_dec_ref(v___y_1742_);
lean_dec(v___y_1741_);
lean_dec_ref(v___y_1740_);
lean_dec(v___x_1739_);
lean_dec_ref(v___f_1738_);
lean_dec_ref(v_typeNew_1737_);
lean_dec_ref(v___f_1736_);
lean_dec(v_mvarId_1735_);
v_a_1780_ = lean_ctor_get(v___x_1745_, 0);
v_isSharedCheck_1787_ = !lean_is_exclusive(v___x_1745_);
if (v_isSharedCheck_1787_ == 0)
{
v___x_1782_ = v___x_1745_;
v_isShared_1783_ = v_isSharedCheck_1787_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_a_1780_);
lean_dec(v___x_1745_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1787_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
lean_object* v___x_1785_; 
if (v_isShared_1783_ == 0)
{
v___x_1785_ = v___x_1782_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v_a_1780_);
v___x_1785_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
return v___x_1785_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_changeLocalDecl___lam__2___boxed(lean_object* v_mvarId_1788_, lean_object* v___f_1789_, lean_object* v_typeNew_1790_, lean_object* v___f_1791_, lean_object* v___x_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_){
_start:
{
lean_object* v_res_1798_; 
v_res_1798_ = l_Lean_MVarId_changeLocalDecl___lam__2(v_mvarId_1788_, v___f_1789_, v_typeNew_1790_, v___f_1791_, v___x_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_);
return v_res_1798_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_changeLocalDecl___lam__3(uint8_t v_checkDefEq_1799_, lean_object* v_typeNew_1800_, lean_object* v___x_1801_, lean_object* v_mvarId_1802_, lean_object* v_fvars_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_){
_start:
{
lean_object* v___x_1809_; lean_object* v___f_1810_; lean_object* v___f_1811_; lean_object* v___f_1812_; lean_object* v___x_1813_; 
v___x_1809_ = lean_box(v_checkDefEq_1799_);
lean_inc_n(v_mvarId_1802_, 3);
lean_inc(v___x_1801_);
lean_inc_ref(v_typeNew_1800_);
v___f_1810_ = lean_alloc_closure((void*)(l_Lean_MVarId_changeLocalDecl___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1810_, 0, v___x_1809_);
lean_closure_set(v___f_1810_, 1, v_typeNew_1800_);
lean_closure_set(v___f_1810_, 2, v___x_1801_);
lean_closure_set(v___f_1810_, 3, v_mvarId_1802_);
v___f_1811_ = lean_alloc_closure((void*)(l_Lean_MVarId_changeLocalDecl___lam__1___boxed), 8, 2);
lean_closure_set(v___f_1811_, 0, v_mvarId_1802_);
lean_closure_set(v___f_1811_, 1, v_fvars_1803_);
v___f_1812_ = lean_alloc_closure((void*)(l_Lean_MVarId_changeLocalDecl___lam__2___boxed), 10, 5);
lean_closure_set(v___f_1812_, 0, v_mvarId_1802_);
lean_closure_set(v___f_1812_, 1, v___f_1810_);
lean_closure_set(v___f_1812_, 2, v_typeNew_1800_);
lean_closure_set(v___f_1812_, 3, v___f_1811_);
lean_closure_set(v___f_1812_, 4, v___x_1801_);
v___x_1813_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(v_mvarId_1802_, v___f_1812_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_);
return v___x_1813_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_changeLocalDecl___lam__3___boxed(lean_object* v_checkDefEq_1814_, lean_object* v_typeNew_1815_, lean_object* v___x_1816_, lean_object* v_mvarId_1817_, lean_object* v_fvars_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_){
_start:
{
uint8_t v_checkDefEq_boxed_1824_; lean_object* v_res_1825_; 
v_checkDefEq_boxed_1824_ = lean_unbox(v_checkDefEq_1814_);
v_res_1825_ = l_Lean_MVarId_changeLocalDecl___lam__3(v_checkDefEq_boxed_1824_, v_typeNew_1815_, v___x_1816_, v_mvarId_1817_, v_fvars_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_);
lean_dec(v___y_1822_);
lean_dec_ref(v___y_1821_);
lean_dec(v___y_1820_);
lean_dec_ref(v___y_1819_);
return v_res_1825_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_changeLocalDecl(lean_object* v_mvarId_1829_, lean_object* v_fvarId_1830_, lean_object* v_typeNew_1831_, uint8_t v_checkDefEq_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_){
_start:
{
lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___f_1840_; lean_object* v___x_1841_; 
v___x_1838_ = ((lean_object*)(l_Lean_MVarId_changeLocalDecl___closed__1));
v___x_1839_ = lean_box(v_checkDefEq_1832_);
v___f_1840_ = lean_alloc_closure((void*)(l_Lean_MVarId_changeLocalDecl___lam__3___boxed), 10, 3);
lean_closure_set(v___f_1840_, 0, v___x_1839_);
lean_closure_set(v___f_1840_, 1, v_typeNew_1831_);
lean_closure_set(v___f_1840_, 2, v___x_1838_);
lean_inc(v_mvarId_1829_);
v___x_1841_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_1829_, v___x_1838_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_);
if (lean_obj_tag(v___x_1841_) == 0)
{
lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; uint8_t v___x_1845_; lean_object* v___x_1846_; 
lean_dec_ref_known(v___x_1841_, 1);
v___x_1842_ = lean_unsigned_to_nat(1u);
v___x_1843_ = lean_mk_empty_array_with_capacity(v___x_1842_);
v___x_1844_ = lean_array_push(v___x_1843_, v_fvarId_1830_);
v___x_1845_ = 0;
v___x_1846_ = l_Lean_MVarId_withReverted___redArg(v_mvarId_1829_, v___x_1844_, v___f_1840_, v___x_1845_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_);
if (lean_obj_tag(v___x_1846_) == 0)
{
lean_object* v_a_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1855_; 
v_a_1847_ = lean_ctor_get(v___x_1846_, 0);
v_isSharedCheck_1855_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1855_ == 0)
{
v___x_1849_ = v___x_1846_;
v_isShared_1850_ = v_isSharedCheck_1855_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_a_1847_);
lean_dec(v___x_1846_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1855_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
lean_object* v_snd_1851_; lean_object* v___x_1853_; 
v_snd_1851_ = lean_ctor_get(v_a_1847_, 1);
lean_inc(v_snd_1851_);
lean_dec(v_a_1847_);
if (v_isShared_1850_ == 0)
{
lean_ctor_set(v___x_1849_, 0, v_snd_1851_);
v___x_1853_ = v___x_1849_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v_snd_1851_);
v___x_1853_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
return v___x_1853_;
}
}
}
else
{
lean_object* v_a_1856_; lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1863_; 
v_a_1856_ = lean_ctor_get(v___x_1846_, 0);
v_isSharedCheck_1863_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1863_ == 0)
{
v___x_1858_ = v___x_1846_;
v_isShared_1859_ = v_isSharedCheck_1863_;
goto v_resetjp_1857_;
}
else
{
lean_inc(v_a_1856_);
lean_dec(v___x_1846_);
v___x_1858_ = lean_box(0);
v_isShared_1859_ = v_isSharedCheck_1863_;
goto v_resetjp_1857_;
}
v_resetjp_1857_:
{
lean_object* v___x_1861_; 
if (v_isShared_1859_ == 0)
{
v___x_1861_ = v___x_1858_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1862_; 
v_reuseFailAlloc_1862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1862_, 0, v_a_1856_);
v___x_1861_ = v_reuseFailAlloc_1862_;
goto v_reusejp_1860_;
}
v_reusejp_1860_:
{
return v___x_1861_;
}
}
}
}
else
{
lean_object* v_a_1864_; lean_object* v___x_1866_; uint8_t v_isShared_1867_; uint8_t v_isSharedCheck_1871_; 
lean_dec_ref(v___f_1840_);
lean_dec(v_fvarId_1830_);
lean_dec(v_mvarId_1829_);
v_a_1864_ = lean_ctor_get(v___x_1841_, 0);
v_isSharedCheck_1871_ = !lean_is_exclusive(v___x_1841_);
if (v_isSharedCheck_1871_ == 0)
{
v___x_1866_ = v___x_1841_;
v_isShared_1867_ = v_isSharedCheck_1871_;
goto v_resetjp_1865_;
}
else
{
lean_inc(v_a_1864_);
lean_dec(v___x_1841_);
v___x_1866_ = lean_box(0);
v_isShared_1867_ = v_isSharedCheck_1871_;
goto v_resetjp_1865_;
}
v_resetjp_1865_:
{
lean_object* v___x_1869_; 
if (v_isShared_1867_ == 0)
{
v___x_1869_ = v___x_1866_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v_a_1864_);
v___x_1869_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
return v___x_1869_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_changeLocalDecl___boxed(lean_object* v_mvarId_1872_, lean_object* v_fvarId_1873_, lean_object* v_typeNew_1874_, lean_object* v_checkDefEq_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_){
_start:
{
uint8_t v_checkDefEq_boxed_1881_; lean_object* v_res_1882_; 
v_checkDefEq_boxed_1881_ = lean_unbox(v_checkDefEq_1875_);
v_res_1882_ = l_Lean_MVarId_changeLocalDecl(v_mvarId_1872_, v_fvarId_1873_, v_typeNew_1874_, v_checkDefEq_boxed_1881_, v_a_1876_, v_a_1877_, v_a_1878_, v_a_1879_);
lean_dec(v_a_1879_);
lean_dec_ref(v_a_1878_);
lean_dec(v_a_1877_);
lean_dec_ref(v_a_1876_);
return v_res_1882_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyTarget___lam__0(lean_object* v_mvarId_1883_, lean_object* v___x_1884_, lean_object* v_f_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_){
_start:
{
lean_object* v___x_1891_; 
lean_inc(v_mvarId_1883_);
v___x_1891_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_1883_, v___x_1884_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_);
if (lean_obj_tag(v___x_1891_) == 0)
{
lean_object* v___x_1892_; 
lean_dec_ref_known(v___x_1891_, 1);
lean_inc(v_mvarId_1883_);
v___x_1892_ = l_Lean_MVarId_getType(v_mvarId_1883_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_);
if (lean_obj_tag(v___x_1892_) == 0)
{
lean_object* v_a_1893_; lean_object* v___x_1894_; 
v_a_1893_ = lean_ctor_get(v___x_1892_, 0);
lean_inc(v_a_1893_);
lean_dec_ref_known(v___x_1892_, 1);
lean_inc(v___y_1889_);
lean_inc_ref(v___y_1888_);
lean_inc(v___y_1887_);
lean_inc_ref(v___y_1886_);
v___x_1894_ = lean_apply_6(v_f_1885_, v_a_1893_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, lean_box(0));
if (lean_obj_tag(v___x_1894_) == 0)
{
lean_object* v_a_1895_; uint8_t v___x_1896_; lean_object* v___x_1897_; 
v_a_1895_ = lean_ctor_get(v___x_1894_, 0);
lean_inc(v_a_1895_);
lean_dec_ref_known(v___x_1894_, 1);
v___x_1896_ = 0;
v___x_1897_ = l_Lean_MVarId_change(v_mvarId_1883_, v_a_1895_, v___x_1896_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_);
lean_dec(v___y_1889_);
lean_dec_ref(v___y_1888_);
lean_dec(v___y_1887_);
lean_dec_ref(v___y_1886_);
return v___x_1897_;
}
else
{
lean_object* v_a_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1905_; 
lean_dec(v___y_1889_);
lean_dec_ref(v___y_1888_);
lean_dec(v___y_1887_);
lean_dec_ref(v___y_1886_);
lean_dec(v_mvarId_1883_);
v_a_1898_ = lean_ctor_get(v___x_1894_, 0);
v_isSharedCheck_1905_ = !lean_is_exclusive(v___x_1894_);
if (v_isSharedCheck_1905_ == 0)
{
v___x_1900_ = v___x_1894_;
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_a_1898_);
lean_dec(v___x_1894_);
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
lean_dec(v___y_1889_);
lean_dec_ref(v___y_1888_);
lean_dec(v___y_1887_);
lean_dec_ref(v___y_1886_);
lean_dec_ref(v_f_1885_);
lean_dec(v_mvarId_1883_);
v_a_1906_ = lean_ctor_get(v___x_1892_, 0);
v_isSharedCheck_1913_ = !lean_is_exclusive(v___x_1892_);
if (v_isSharedCheck_1913_ == 0)
{
v___x_1908_ = v___x_1892_;
v_isShared_1909_ = v_isSharedCheck_1913_;
goto v_resetjp_1907_;
}
else
{
lean_inc(v_a_1906_);
lean_dec(v___x_1892_);
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
else
{
lean_object* v_a_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1921_; 
lean_dec(v___y_1889_);
lean_dec_ref(v___y_1888_);
lean_dec(v___y_1887_);
lean_dec_ref(v___y_1886_);
lean_dec_ref(v_f_1885_);
lean_dec(v_mvarId_1883_);
v_a_1914_ = lean_ctor_get(v___x_1891_, 0);
v_isSharedCheck_1921_ = !lean_is_exclusive(v___x_1891_);
if (v_isSharedCheck_1921_ == 0)
{
v___x_1916_ = v___x_1891_;
v_isShared_1917_ = v_isSharedCheck_1921_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_a_1914_);
lean_dec(v___x_1891_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_1921_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
lean_object* v___x_1919_; 
if (v_isShared_1917_ == 0)
{
v___x_1919_ = v___x_1916_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v_a_1914_);
v___x_1919_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1918_;
}
v_reusejp_1918_:
{
return v___x_1919_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyTarget___lam__0___boxed(lean_object* v_mvarId_1922_, lean_object* v___x_1923_, lean_object* v_f_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_){
_start:
{
lean_object* v_res_1930_; 
v_res_1930_ = l_Lean_MVarId_modifyTarget___lam__0(v_mvarId_1922_, v___x_1923_, v_f_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_);
return v_res_1930_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyTarget(lean_object* v_mvarId_1934_, lean_object* v_f_1935_, lean_object* v_a_1936_, lean_object* v_a_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_){
_start:
{
lean_object* v___x_1941_; lean_object* v___f_1942_; lean_object* v___x_1943_; 
v___x_1941_ = ((lean_object*)(l_Lean_MVarId_modifyTarget___closed__1));
lean_inc(v_mvarId_1934_);
v___f_1942_ = lean_alloc_closure((void*)(l_Lean_MVarId_modifyTarget___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1942_, 0, v_mvarId_1934_);
lean_closure_set(v___f_1942_, 1, v___x_1941_);
lean_closure_set(v___f_1942_, 2, v_f_1935_);
v___x_1943_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(v_mvarId_1934_, v___f_1942_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_);
return v___x_1943_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyTarget___boxed(lean_object* v_mvarId_1944_, lean_object* v_f_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_){
_start:
{
lean_object* v_res_1951_; 
v_res_1951_ = l_Lean_MVarId_modifyTarget(v_mvarId_1944_, v_f_1945_, v_a_1946_, v_a_1947_, v_a_1948_, v_a_1949_);
lean_dec(v_a_1949_);
lean_dec_ref(v_a_1948_);
lean_dec(v_a_1947_);
lean_dec_ref(v_a_1946_);
return v_res_1951_;
}
}
static lean_object* _init_l_Lean_MVarId_modifyTargetEqLHS___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1956_; lean_object* v___x_1957_; 
v___x_1956_ = ((lean_object*)(l_Lean_MVarId_modifyTargetEqLHS___lam__0___closed__2));
v___x_1957_ = l_Lean_stringToMessageData(v___x_1956_);
return v___x_1957_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyTargetEqLHS___lam__0(lean_object* v_f_1958_, lean_object* v_mvarId_1959_, lean_object* v_target_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_){
_start:
{
lean_object* v___x_1966_; 
lean_inc_ref(v_target_1960_);
v___x_1966_ = l_Lean_Meta_matchEq_x3f(v_target_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_);
if (lean_obj_tag(v___x_1966_) == 0)
{
lean_object* v_a_1967_; 
v_a_1967_ = lean_ctor_get(v___x_1966_, 0);
lean_inc(v_a_1967_);
lean_dec_ref_known(v___x_1966_, 1);
if (lean_obj_tag(v_a_1967_) == 1)
{
lean_object* v_val_1968_; lean_object* v_snd_1969_; lean_object* v_fst_1970_; lean_object* v_snd_1971_; lean_object* v___x_1972_; 
lean_dec_ref(v_target_1960_);
lean_dec(v_mvarId_1959_);
v_val_1968_ = lean_ctor_get(v_a_1967_, 0);
lean_inc(v_val_1968_);
lean_dec_ref_known(v_a_1967_, 1);
v_snd_1969_ = lean_ctor_get(v_val_1968_, 1);
lean_inc(v_snd_1969_);
lean_dec(v_val_1968_);
v_fst_1970_ = lean_ctor_get(v_snd_1969_, 0);
lean_inc(v_fst_1970_);
v_snd_1971_ = lean_ctor_get(v_snd_1969_, 1);
lean_inc(v_snd_1971_);
lean_dec(v_snd_1969_);
lean_inc(v___y_1964_);
lean_inc_ref(v___y_1963_);
lean_inc(v___y_1962_);
lean_inc_ref(v___y_1961_);
v___x_1972_ = lean_apply_6(v_f_1958_, v_fst_1970_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_, lean_box(0));
if (lean_obj_tag(v___x_1972_) == 0)
{
lean_object* v_a_1973_; lean_object* v___x_1974_; 
v_a_1973_ = lean_ctor_get(v___x_1972_, 0);
lean_inc(v_a_1973_);
lean_dec_ref_known(v___x_1972_, 1);
v___x_1974_ = l_Lean_Meta_mkEq(v_a_1973_, v_snd_1971_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_);
return v___x_1974_;
}
else
{
lean_dec(v_snd_1971_);
return v___x_1972_;
}
}
else
{
lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; 
lean_dec(v_a_1967_);
lean_dec_ref(v_f_1958_);
v___x_1975_ = ((lean_object*)(l_Lean_MVarId_modifyTargetEqLHS___lam__0___closed__1));
v___x_1976_ = lean_obj_once(&l_Lean_MVarId_modifyTargetEqLHS___lam__0___closed__3, &l_Lean_MVarId_modifyTargetEqLHS___lam__0___closed__3_once, _init_l_Lean_MVarId_modifyTargetEqLHS___lam__0___closed__3);
v___x_1977_ = l_Lean_indentExpr(v_target_1960_);
v___x_1978_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1978_, 0, v___x_1976_);
lean_ctor_set(v___x_1978_, 1, v___x_1977_);
v___x_1979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1979_, 0, v___x_1978_);
v___x_1980_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1975_, v_mvarId_1959_, v___x_1979_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_);
return v___x_1980_;
}
}
else
{
lean_object* v_a_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_1988_; 
lean_dec_ref(v_target_1960_);
lean_dec(v_mvarId_1959_);
lean_dec_ref(v_f_1958_);
v_a_1981_ = lean_ctor_get(v___x_1966_, 0);
v_isSharedCheck_1988_ = !lean_is_exclusive(v___x_1966_);
if (v_isSharedCheck_1988_ == 0)
{
v___x_1983_ = v___x_1966_;
v_isShared_1984_ = v_isSharedCheck_1988_;
goto v_resetjp_1982_;
}
else
{
lean_inc(v_a_1981_);
lean_dec(v___x_1966_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_1988_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v___x_1986_; 
if (v_isShared_1984_ == 0)
{
v___x_1986_ = v___x_1983_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v_a_1981_);
v___x_1986_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
return v___x_1986_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyTargetEqLHS___lam__0___boxed(lean_object* v_f_1989_, lean_object* v_mvarId_1990_, lean_object* v_target_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_){
_start:
{
lean_object* v_res_1997_; 
v_res_1997_ = l_Lean_MVarId_modifyTargetEqLHS___lam__0(v_f_1989_, v_mvarId_1990_, v_target_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_);
lean_dec(v___y_1995_);
lean_dec_ref(v___y_1994_);
lean_dec(v___y_1993_);
lean_dec_ref(v___y_1992_);
return v_res_1997_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyTargetEqLHS(lean_object* v_mvarId_1998_, lean_object* v_f_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_){
_start:
{
lean_object* v___f_2005_; lean_object* v___x_2006_; 
lean_inc(v_mvarId_1998_);
v___f_2005_ = lean_alloc_closure((void*)(l_Lean_MVarId_modifyTargetEqLHS___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2005_, 0, v_f_1999_);
lean_closure_set(v___f_2005_, 1, v_mvarId_1998_);
v___x_2006_ = l_Lean_MVarId_modifyTarget(v_mvarId_1998_, v___f_2005_, v_a_2000_, v_a_2001_, v_a_2002_, v_a_2003_);
return v___x_2006_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyTargetEqLHS___boxed(lean_object* v_mvarId_2007_, lean_object* v_f_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_){
_start:
{
lean_object* v_res_2014_; 
v_res_2014_ = l_Lean_MVarId_modifyTargetEqLHS(v_mvarId_2007_, v_f_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_);
lean_dec(v_a_2012_);
lean_dec_ref(v_a_2011_);
lean_dec(v_a_2010_);
lean_dec_ref(v_a_2009_);
return v_res_2014_;
}
}
static lean_object* _init_l_Lean_MVarId_clearValue___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2016_; lean_object* v___x_2017_; 
v___x_2016_ = ((lean_object*)(l_Lean_MVarId_clearValue___lam__0___closed__0));
v___x_2017_ = l_Lean_stringToMessageData(v___x_2016_);
return v___x_2017_;
}
}
static lean_object* _init_l_Lean_MVarId_clearValue___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2019_; lean_object* v___x_2020_; 
v___x_2019_ = ((lean_object*)(l_Lean_MVarId_clearValue___lam__0___closed__2));
v___x_2020_ = l_Lean_stringToMessageData(v___x_2019_);
return v___x_2020_;
}
}
static lean_object* _init_l_Lean_MVarId_clearValue___lam__0___closed__5(void){
_start:
{
lean_object* v___x_2022_; lean_object* v___x_2023_; 
v___x_2022_ = ((lean_object*)(l_Lean_MVarId_clearValue___lam__0___closed__4));
v___x_2023_ = l_Lean_stringToMessageData(v___x_2022_);
return v___x_2023_;
}
}
static lean_object* _init_l_Lean_MVarId_clearValue___lam__0___closed__7(void){
_start:
{
lean_object* v___x_2025_; lean_object* v___x_2026_; 
v___x_2025_ = ((lean_object*)(l_Lean_MVarId_clearValue___lam__0___closed__6));
v___x_2026_ = l_Lean_stringToMessageData(v___x_2025_);
return v___x_2026_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clearValue___lam__0(lean_object* v_mvarId_x27_2027_, lean_object* v_a_2028_, lean_object* v_fvars_2029_, lean_object* v_fvarId_2030_, lean_object* v___x_2031_, lean_object* v_mvarId_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_){
_start:
{
lean_object* v___x_2038_; 
lean_inc(v_mvarId_x27_2027_);
v___x_2038_ = l_Lean_MVarId_getType(v_mvarId_x27_2027_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_);
if (lean_obj_tag(v___x_2038_) == 0)
{
lean_object* v_a_2039_; lean_object* v___y_2041_; lean_object* v___y_2042_; lean_object* v___y_2043_; lean_object* v___y_2044_; lean_object* v___y_2045_; lean_object* v___y_2075_; lean_object* v___y_2076_; lean_object* v___y_2077_; lean_object* v___y_2078_; uint8_t v___x_2120_; 
v_a_2039_ = lean_ctor_get(v___x_2038_, 0);
lean_inc(v_a_2039_);
lean_dec_ref_known(v___x_2038_, 1);
v___x_2120_ = l_Lean_Expr_isLet(v_a_2039_);
if (v___x_2120_ == 0)
{
lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; 
v___x_2121_ = lean_obj_once(&l_Lean_MVarId_clearValue___lam__0___closed__5, &l_Lean_MVarId_clearValue___lam__0___closed__5_once, _init_l_Lean_MVarId_clearValue___lam__0___closed__5);
lean_inc(v_fvarId_2030_);
v___x_2122_ = l_Lean_Expr_fvar___override(v_fvarId_2030_);
v___x_2123_ = l_Lean_MessageData_ofExpr(v___x_2122_);
v___x_2124_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2124_, 0, v___x_2121_);
lean_ctor_set(v___x_2124_, 1, v___x_2123_);
v___x_2125_ = lean_obj_once(&l_Lean_MVarId_clearValue___lam__0___closed__7, &l_Lean_MVarId_clearValue___lam__0___closed__7_once, _init_l_Lean_MVarId_clearValue___lam__0___closed__7);
v___x_2126_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2126_, 0, v___x_2124_);
lean_ctor_set(v___x_2126_, 1, v___x_2125_);
v___x_2127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2127_, 0, v___x_2126_);
lean_inc_n(v_mvarId_2032_, 2);
lean_inc(v___x_2031_);
v___x_2128_ = lean_alloc_closure((void*)(l_Lean_Meta_throwTacticEx___boxed), 9, 4);
lean_closure_set(v___x_2128_, 0, lean_box(0));
lean_closure_set(v___x_2128_, 1, v___x_2031_);
lean_closure_set(v___x_2128_, 2, v_mvarId_2032_);
lean_closure_set(v___x_2128_, 3, v___x_2127_);
v___x_2129_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(v_mvarId_2032_, v___x_2128_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_);
if (lean_obj_tag(v___x_2129_) == 0)
{
lean_dec_ref_known(v___x_2129_, 1);
v___y_2075_ = v___y_2033_;
v___y_2076_ = v___y_2034_;
v___y_2077_ = v___y_2035_;
v___y_2078_ = v___y_2036_;
goto v___jp_2074_;
}
else
{
lean_object* v_a_2130_; lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2137_; 
lean_dec(v_a_2039_);
lean_dec(v_mvarId_2032_);
lean_dec(v___x_2031_);
lean_dec(v_fvarId_2030_);
lean_dec_ref(v_fvars_2029_);
lean_dec(v_a_2028_);
lean_dec(v_mvarId_x27_2027_);
v_a_2130_ = lean_ctor_get(v___x_2129_, 0);
v_isSharedCheck_2137_ = !lean_is_exclusive(v___x_2129_);
if (v_isSharedCheck_2137_ == 0)
{
v___x_2132_ = v___x_2129_;
v_isShared_2133_ = v_isSharedCheck_2137_;
goto v_resetjp_2131_;
}
else
{
lean_inc(v_a_2130_);
lean_dec(v___x_2129_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2137_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
lean_object* v___x_2135_; 
if (v_isShared_2133_ == 0)
{
v___x_2135_ = v___x_2132_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v_a_2130_);
v___x_2135_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
return v___x_2135_;
}
}
}
}
else
{
v___y_2075_ = v___y_2033_;
v___y_2076_ = v___y_2034_;
v___y_2077_ = v___y_2035_;
v___y_2078_ = v___y_2036_;
goto v___jp_2074_;
}
v___jp_2040_:
{
lean_object* v___x_2046_; 
v___x_2046_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___y_2041_, v_a_2028_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_);
if (lean_obj_tag(v___x_2046_) == 0)
{
lean_object* v_a_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2052_; uint8_t v_isShared_2053_; uint8_t v_isSharedCheck_2064_; 
v_a_2047_ = lean_ctor_get(v___x_2046_, 0);
lean_inc_n(v_a_2047_, 2);
lean_dec_ref_known(v___x_2046_, 1);
v___x_2048_ = l_Lean_Expr_letValue_x21(v_a_2039_);
lean_dec(v_a_2039_);
v___x_2049_ = l_Lean_Expr_app___override(v_a_2047_, v___x_2048_);
v___x_2050_ = l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0___redArg(v_mvarId_x27_2027_, v___x_2049_, v___y_2043_);
v_isSharedCheck_2064_ = !lean_is_exclusive(v___x_2050_);
if (v_isSharedCheck_2064_ == 0)
{
lean_object* v_unused_2065_; 
v_unused_2065_ = lean_ctor_get(v___x_2050_, 0);
lean_dec(v_unused_2065_);
v___x_2052_ = v___x_2050_;
v_isShared_2053_ = v_isSharedCheck_2064_;
goto v_resetjp_2051_;
}
else
{
lean_dec(v___x_2050_);
v___x_2052_ = lean_box(0);
v_isShared_2053_ = v_isSharedCheck_2064_;
goto v_resetjp_2051_;
}
v_resetjp_2051_:
{
lean_object* v___x_2054_; size_t v_sz_2055_; size_t v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2062_; 
v___x_2054_ = lean_box(0);
v_sz_2055_ = lean_array_size(v_fvars_2029_);
v___x_2056_ = ((size_t)0ULL);
v___x_2057_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_changeLocalDecl_spec__0(v_sz_2055_, v___x_2056_, v_fvars_2029_);
v___x_2058_ = l_Lean_Expr_mvarId_x21(v_a_2047_);
lean_dec(v_a_2047_);
v___x_2059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2059_, 0, v___x_2057_);
lean_ctor_set(v___x_2059_, 1, v___x_2058_);
v___x_2060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2060_, 0, v___x_2054_);
lean_ctor_set(v___x_2060_, 1, v___x_2059_);
if (v_isShared_2053_ == 0)
{
lean_ctor_set(v___x_2052_, 0, v___x_2060_);
v___x_2062_ = v___x_2052_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v___x_2060_);
v___x_2062_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
return v___x_2062_;
}
}
}
else
{
lean_object* v_a_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2073_; 
lean_dec(v_a_2039_);
lean_dec_ref(v_fvars_2029_);
lean_dec(v_mvarId_x27_2027_);
v_a_2066_ = lean_ctor_get(v___x_2046_, 0);
v_isSharedCheck_2073_ = !lean_is_exclusive(v___x_2046_);
if (v_isSharedCheck_2073_ == 0)
{
v___x_2068_ = v___x_2046_;
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_a_2066_);
lean_dec(v___x_2046_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v___x_2071_; 
if (v_isShared_2069_ == 0)
{
v___x_2071_ = v___x_2068_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v_a_2066_);
v___x_2071_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
return v___x_2071_;
}
}
}
}
v___jp_2074_:
{
lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; uint8_t v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v_a_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2119_; 
v___x_2079_ = l_Lean_Expr_letName_x21(v_a_2039_);
v___x_2080_ = l_Lean_Expr_letType_x21(v_a_2039_);
v___x_2081_ = l_Lean_Expr_letBody_x21(v_a_2039_);
v___x_2082_ = 0;
v___x_2083_ = l_Lean_Expr_forallE___override(v___x_2079_, v___x_2080_, v___x_2081_, v___x_2082_);
v___x_2084_ = l_Lean_instantiateMVars___at___00Lean_MVarId_replaceTargetDefEq_spec__0___redArg(v___x_2083_, v___y_2076_);
v_a_2085_ = lean_ctor_get(v___x_2084_, 0);
v_isSharedCheck_2119_ = !lean_is_exclusive(v___x_2084_);
if (v_isSharedCheck_2119_ == 0)
{
v___x_2087_ = v___x_2084_;
v_isShared_2088_ = v_isSharedCheck_2119_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_a_2085_);
lean_dec(v___x_2084_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2119_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
lean_object* v___x_2089_; 
lean_inc(v_a_2085_);
v___x_2089_ = l_Lean_Meta_isTypeCorrect(v_a_2085_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_);
if (lean_obj_tag(v___x_2089_) == 0)
{
lean_object* v_a_2090_; uint8_t v___x_2091_; 
v_a_2090_ = lean_ctor_get(v___x_2089_, 0);
lean_inc(v_a_2090_);
lean_dec_ref_known(v___x_2089_, 1);
v___x_2091_ = lean_unbox(v_a_2090_);
lean_dec(v_a_2090_);
if (v___x_2091_ == 0)
{
lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2099_; 
v___x_2092_ = lean_obj_once(&l_Lean_MVarId_clearValue___lam__0___closed__1, &l_Lean_MVarId_clearValue___lam__0___closed__1_once, _init_l_Lean_MVarId_clearValue___lam__0___closed__1);
v___x_2093_ = l_Lean_Expr_fvar___override(v_fvarId_2030_);
v___x_2094_ = l_Lean_MessageData_ofExpr(v___x_2093_);
v___x_2095_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2095_, 0, v___x_2092_);
lean_ctor_set(v___x_2095_, 1, v___x_2094_);
v___x_2096_ = lean_obj_once(&l_Lean_MVarId_clearValue___lam__0___closed__3, &l_Lean_MVarId_clearValue___lam__0___closed__3_once, _init_l_Lean_MVarId_clearValue___lam__0___closed__3);
v___x_2097_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2097_, 0, v___x_2095_);
lean_ctor_set(v___x_2097_, 1, v___x_2096_);
if (v_isShared_2088_ == 0)
{
lean_ctor_set_tag(v___x_2087_, 1);
lean_ctor_set(v___x_2087_, 0, v___x_2097_);
v___x_2099_ = v___x_2087_;
goto v_reusejp_2098_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v___x_2097_);
v___x_2099_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2098_;
}
v_reusejp_2098_:
{
lean_object* v___x_2100_; lean_object* v___x_2101_; 
lean_inc(v_mvarId_2032_);
v___x_2100_ = lean_alloc_closure((void*)(l_Lean_Meta_throwTacticEx___boxed), 9, 4);
lean_closure_set(v___x_2100_, 0, lean_box(0));
lean_closure_set(v___x_2100_, 1, v___x_2031_);
lean_closure_set(v___x_2100_, 2, v_mvarId_2032_);
lean_closure_set(v___x_2100_, 3, v___x_2099_);
v___x_2101_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(v_mvarId_2032_, v___x_2100_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_);
if (lean_obj_tag(v___x_2101_) == 0)
{
lean_dec_ref_known(v___x_2101_, 1);
v___y_2041_ = v_a_2085_;
v___y_2042_ = v___y_2075_;
v___y_2043_ = v___y_2076_;
v___y_2044_ = v___y_2077_;
v___y_2045_ = v___y_2078_;
goto v___jp_2040_;
}
else
{
lean_object* v_a_2102_; lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2109_; 
lean_dec(v_a_2085_);
lean_dec(v_a_2039_);
lean_dec_ref(v_fvars_2029_);
lean_dec(v_a_2028_);
lean_dec(v_mvarId_x27_2027_);
v_a_2102_ = lean_ctor_get(v___x_2101_, 0);
v_isSharedCheck_2109_ = !lean_is_exclusive(v___x_2101_);
if (v_isSharedCheck_2109_ == 0)
{
v___x_2104_ = v___x_2101_;
v_isShared_2105_ = v_isSharedCheck_2109_;
goto v_resetjp_2103_;
}
else
{
lean_inc(v_a_2102_);
lean_dec(v___x_2101_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2109_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
lean_object* v___x_2107_; 
if (v_isShared_2105_ == 0)
{
v___x_2107_ = v___x_2104_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v_a_2102_);
v___x_2107_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
return v___x_2107_;
}
}
}
}
}
else
{
lean_del_object(v___x_2087_);
lean_dec(v_mvarId_2032_);
lean_dec(v___x_2031_);
lean_dec(v_fvarId_2030_);
v___y_2041_ = v_a_2085_;
v___y_2042_ = v___y_2075_;
v___y_2043_ = v___y_2076_;
v___y_2044_ = v___y_2077_;
v___y_2045_ = v___y_2078_;
goto v___jp_2040_;
}
}
else
{
lean_object* v_a_2111_; lean_object* v___x_2113_; uint8_t v_isShared_2114_; uint8_t v_isSharedCheck_2118_; 
lean_del_object(v___x_2087_);
lean_dec(v_a_2085_);
lean_dec(v_a_2039_);
lean_dec(v_mvarId_2032_);
lean_dec(v___x_2031_);
lean_dec(v_fvarId_2030_);
lean_dec_ref(v_fvars_2029_);
lean_dec(v_a_2028_);
lean_dec(v_mvarId_x27_2027_);
v_a_2111_ = lean_ctor_get(v___x_2089_, 0);
v_isSharedCheck_2118_ = !lean_is_exclusive(v___x_2089_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_2113_ = v___x_2089_;
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
else
{
lean_inc(v_a_2111_);
lean_dec(v___x_2089_);
v___x_2113_ = lean_box(0);
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
v_resetjp_2112_:
{
lean_object* v___x_2116_; 
if (v_isShared_2114_ == 0)
{
v___x_2116_ = v___x_2113_;
goto v_reusejp_2115_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v_a_2111_);
v___x_2116_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2115_;
}
v_reusejp_2115_:
{
return v___x_2116_;
}
}
}
}
}
}
else
{
lean_object* v_a_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2145_; 
lean_dec(v_mvarId_2032_);
lean_dec(v___x_2031_);
lean_dec(v_fvarId_2030_);
lean_dec_ref(v_fvars_2029_);
lean_dec(v_a_2028_);
lean_dec(v_mvarId_x27_2027_);
v_a_2138_ = lean_ctor_get(v___x_2038_, 0);
v_isSharedCheck_2145_ = !lean_is_exclusive(v___x_2038_);
if (v_isSharedCheck_2145_ == 0)
{
v___x_2140_ = v___x_2038_;
v_isShared_2141_ = v_isSharedCheck_2145_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_a_2138_);
lean_dec(v___x_2038_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2145_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v___x_2143_; 
if (v_isShared_2141_ == 0)
{
v___x_2143_ = v___x_2140_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v_a_2138_);
v___x_2143_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
return v___x_2143_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clearValue___lam__0___boxed(lean_object* v_mvarId_x27_2146_, lean_object* v_a_2147_, lean_object* v_fvars_2148_, lean_object* v_fvarId_2149_, lean_object* v___x_2150_, lean_object* v_mvarId_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_){
_start:
{
lean_object* v_res_2157_; 
v_res_2157_ = l_Lean_MVarId_clearValue___lam__0(v_mvarId_x27_2146_, v_a_2147_, v_fvars_2148_, v_fvarId_2149_, v___x_2150_, v_mvarId_2151_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_);
lean_dec(v___y_2155_);
lean_dec_ref(v___y_2154_);
lean_dec(v___y_2153_);
lean_dec_ref(v___y_2152_);
return v_res_2157_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clearValue___lam__1(lean_object* v_a_2158_, lean_object* v_fvarId_2159_, lean_object* v___x_2160_, lean_object* v_mvarId_2161_, lean_object* v_mvarId_x27_2162_, lean_object* v_fvars_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_){
_start:
{
lean_object* v___f_2169_; lean_object* v___x_2170_; 
lean_inc(v_mvarId_x27_2162_);
v___f_2169_ = lean_alloc_closure((void*)(l_Lean_MVarId_clearValue___lam__0___boxed), 11, 6);
lean_closure_set(v___f_2169_, 0, v_mvarId_x27_2162_);
lean_closure_set(v___f_2169_, 1, v_a_2158_);
lean_closure_set(v___f_2169_, 2, v_fvars_2163_);
lean_closure_set(v___f_2169_, 3, v_fvarId_2159_);
lean_closure_set(v___f_2169_, 4, v___x_2160_);
lean_closure_set(v___f_2169_, 5, v_mvarId_2161_);
v___x_2170_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(v_mvarId_x27_2162_, v___f_2169_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_);
return v___x_2170_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clearValue___lam__1___boxed(lean_object* v_a_2171_, lean_object* v_fvarId_2172_, lean_object* v___x_2173_, lean_object* v_mvarId_2174_, lean_object* v_mvarId_x27_2175_, lean_object* v_fvars_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_){
_start:
{
lean_object* v_res_2182_; 
v_res_2182_ = l_Lean_MVarId_clearValue___lam__1(v_a_2171_, v_fvarId_2172_, v___x_2173_, v_mvarId_2174_, v_mvarId_x27_2175_, v_fvars_2176_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_);
lean_dec(v___y_2180_);
lean_dec_ref(v___y_2179_);
lean_dec(v___y_2178_);
lean_dec_ref(v___y_2177_);
return v_res_2182_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clearValue(lean_object* v_mvarId_2186_, lean_object* v_fvarId_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_, lean_object* v_a_2190_, lean_object* v_a_2191_){
_start:
{
lean_object* v___x_2193_; lean_object* v___x_2194_; 
v___x_2193_ = ((lean_object*)(l_Lean_MVarId_clearValue___closed__1));
lean_inc(v_mvarId_2186_);
v___x_2194_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_2186_, v___x_2193_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_);
if (lean_obj_tag(v___x_2194_) == 0)
{
lean_object* v___x_2195_; 
lean_dec_ref_known(v___x_2194_, 1);
lean_inc(v_mvarId_2186_);
v___x_2195_ = l_Lean_MVarId_getTag(v_mvarId_2186_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_);
if (lean_obj_tag(v___x_2195_) == 0)
{
lean_object* v_a_2196_; lean_object* v___f_2197_; lean_object* v___x_2198_; 
v_a_2196_ = lean_ctor_get(v___x_2195_, 0);
lean_inc(v_a_2196_);
lean_dec_ref_known(v___x_2195_, 1);
lean_inc(v_mvarId_2186_);
lean_inc(v_fvarId_2187_);
v___f_2197_ = lean_alloc_closure((void*)(l_Lean_MVarId_clearValue___lam__1___boxed), 11, 4);
lean_closure_set(v___f_2197_, 0, v_a_2196_);
lean_closure_set(v___f_2197_, 1, v_fvarId_2187_);
lean_closure_set(v___f_2197_, 2, v___x_2193_);
lean_closure_set(v___f_2197_, 3, v_mvarId_2186_);
v___x_2198_ = l_Lean_MVarId_withRevertedFrom___redArg(v_mvarId_2186_, v_fvarId_2187_, v___f_2197_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_);
if (lean_obj_tag(v___x_2198_) == 0)
{
lean_object* v_a_2199_; lean_object* v___x_2201_; uint8_t v_isShared_2202_; uint8_t v_isSharedCheck_2207_; 
v_a_2199_ = lean_ctor_get(v___x_2198_, 0);
v_isSharedCheck_2207_ = !lean_is_exclusive(v___x_2198_);
if (v_isSharedCheck_2207_ == 0)
{
v___x_2201_ = v___x_2198_;
v_isShared_2202_ = v_isSharedCheck_2207_;
goto v_resetjp_2200_;
}
else
{
lean_inc(v_a_2199_);
lean_dec(v___x_2198_);
v___x_2201_ = lean_box(0);
v_isShared_2202_ = v_isSharedCheck_2207_;
goto v_resetjp_2200_;
}
v_resetjp_2200_:
{
lean_object* v_snd_2203_; lean_object* v___x_2205_; 
v_snd_2203_ = lean_ctor_get(v_a_2199_, 1);
lean_inc(v_snd_2203_);
lean_dec(v_a_2199_);
if (v_isShared_2202_ == 0)
{
lean_ctor_set(v___x_2201_, 0, v_snd_2203_);
v___x_2205_ = v___x_2201_;
goto v_reusejp_2204_;
}
else
{
lean_object* v_reuseFailAlloc_2206_; 
v_reuseFailAlloc_2206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2206_, 0, v_snd_2203_);
v___x_2205_ = v_reuseFailAlloc_2206_;
goto v_reusejp_2204_;
}
v_reusejp_2204_:
{
return v___x_2205_;
}
}
}
else
{
lean_object* v_a_2208_; lean_object* v___x_2210_; uint8_t v_isShared_2211_; uint8_t v_isSharedCheck_2215_; 
v_a_2208_ = lean_ctor_get(v___x_2198_, 0);
v_isSharedCheck_2215_ = !lean_is_exclusive(v___x_2198_);
if (v_isSharedCheck_2215_ == 0)
{
v___x_2210_ = v___x_2198_;
v_isShared_2211_ = v_isSharedCheck_2215_;
goto v_resetjp_2209_;
}
else
{
lean_inc(v_a_2208_);
lean_dec(v___x_2198_);
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
else
{
lean_object* v_a_2216_; lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2223_; 
lean_dec(v_fvarId_2187_);
lean_dec(v_mvarId_2186_);
v_a_2216_ = lean_ctor_get(v___x_2195_, 0);
v_isSharedCheck_2223_ = !lean_is_exclusive(v___x_2195_);
if (v_isSharedCheck_2223_ == 0)
{
v___x_2218_ = v___x_2195_;
v_isShared_2219_ = v_isSharedCheck_2223_;
goto v_resetjp_2217_;
}
else
{
lean_inc(v_a_2216_);
lean_dec(v___x_2195_);
v___x_2218_ = lean_box(0);
v_isShared_2219_ = v_isSharedCheck_2223_;
goto v_resetjp_2217_;
}
v_resetjp_2217_:
{
lean_object* v___x_2221_; 
if (v_isShared_2219_ == 0)
{
v___x_2221_ = v___x_2218_;
goto v_reusejp_2220_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v_a_2216_);
v___x_2221_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2220_;
}
v_reusejp_2220_:
{
return v___x_2221_;
}
}
}
}
else
{
lean_object* v_a_2224_; lean_object* v___x_2226_; uint8_t v_isShared_2227_; uint8_t v_isSharedCheck_2231_; 
lean_dec(v_fvarId_2187_);
lean_dec(v_mvarId_2186_);
v_a_2224_ = lean_ctor_get(v___x_2194_, 0);
v_isSharedCheck_2231_ = !lean_is_exclusive(v___x_2194_);
if (v_isSharedCheck_2231_ == 0)
{
v___x_2226_ = v___x_2194_;
v_isShared_2227_ = v_isSharedCheck_2231_;
goto v_resetjp_2225_;
}
else
{
lean_inc(v_a_2224_);
lean_dec(v___x_2194_);
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
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clearValue___boxed(lean_object* v_mvarId_2232_, lean_object* v_fvarId_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_){
_start:
{
lean_object* v_res_2239_; 
v_res_2239_ = l_Lean_MVarId_clearValue(v_mvarId_2232_, v_fvarId_2233_, v_a_2234_, v_a_2235_, v_a_2236_, v_a_2237_);
lean_dec(v_a_2237_);
lean_dec_ref(v_a_2236_);
lean_dec(v_a_2235_);
lean_dec_ref(v_a_2234_);
return v_res_2239_;
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
