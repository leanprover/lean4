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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
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
lean_object* l_instMonadEIO(lean_object*);
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
v___x_86_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
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
lean_object* v_ks_138_; lean_object* v_vs_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_159_; 
v_ks_138_ = lean_ctor_get(v_x_87_, 0);
v_vs_139_ = lean_ctor_get(v_x_87_, 1);
v_isSharedCheck_159_ = !lean_is_exclusive(v_x_87_);
if (v_isSharedCheck_159_ == 0)
{
v___x_141_ = v_x_87_;
v_isShared_142_ = v_isSharedCheck_159_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_vs_139_);
lean_inc(v_ks_138_);
lean_dec(v_x_87_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_159_;
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
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v_ks_138_);
lean_ctor_set(v_reuseFailAlloc_158_, 1, v_vs_139_);
v___x_144_ = v_reuseFailAlloc_158_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
lean_object* v_newNode_145_; uint8_t v___y_147_; size_t v___x_153_; uint8_t v___x_154_; 
v_newNode_145_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__3___redArg(v___x_144_, v_x_90_, v_x_91_);
v___x_153_ = ((size_t)7ULL);
v___x_154_ = lean_usize_dec_le(v___x_153_, v_x_89_);
if (v___x_154_ == 0)
{
lean_object* v___x_155_; lean_object* v___x_156_; uint8_t v___x_157_; 
v___x_155_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_145_);
v___x_156_ = lean_unsigned_to_nat(4u);
v___x_157_ = lean_nat_dec_lt(v___x_155_, v___x_156_);
lean_dec(v___x_155_);
v___y_147_ = v___x_157_;
goto v___jp_146_;
}
else
{
v___y_147_ = v___x_154_;
goto v___jp_146_;
}
v___jp_146_:
{
if (v___y_147_ == 0)
{
lean_object* v_ks_148_; lean_object* v_vs_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v_ks_148_ = lean_ctor_get(v_newNode_145_, 0);
lean_inc_ref(v_ks_148_);
v_vs_149_ = lean_ctor_get(v_newNode_145_, 1);
lean_inc_ref(v_vs_149_);
lean_dec_ref(v_newNode_145_);
v___x_150_ = lean_unsigned_to_nat(0u);
v___x_151_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg___closed__0);
v___x_152_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__4___redArg(v_x_89_, v_ks_148_, v_vs_149_, v___x_150_, v___x_151_);
lean_dec_ref(v_vs_149_);
lean_dec_ref(v_ks_148_);
return v___x_152_;
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
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__4___redArg(size_t v_depth_160_, lean_object* v_keys_161_, lean_object* v_vals_162_, lean_object* v_i_163_, lean_object* v_entries_164_){
_start:
{
lean_object* v___x_165_; uint8_t v___x_166_; 
v___x_165_ = lean_array_get_size(v_keys_161_);
v___x_166_ = lean_nat_dec_lt(v_i_163_, v___x_165_);
if (v___x_166_ == 0)
{
lean_dec(v_i_163_);
return v_entries_164_;
}
else
{
lean_object* v_k_167_; lean_object* v_v_168_; uint64_t v___x_169_; size_t v_h_170_; size_t v___x_171_; lean_object* v___x_172_; size_t v___x_173_; size_t v___x_174_; size_t v___x_175_; size_t v_h_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
v_k_167_ = lean_array_fget_borrowed(v_keys_161_, v_i_163_);
v_v_168_ = lean_array_fget_borrowed(v_vals_162_, v_i_163_);
v___x_169_ = l_Lean_instHashableMVarId_hash(v_k_167_);
v_h_170_ = lean_uint64_to_usize(v___x_169_);
v___x_171_ = ((size_t)5ULL);
v___x_172_ = lean_unsigned_to_nat(1u);
v___x_173_ = ((size_t)1ULL);
v___x_174_ = lean_usize_sub(v_depth_160_, v___x_173_);
v___x_175_ = lean_usize_mul(v___x_171_, v___x_174_);
v_h_176_ = lean_usize_shift_right(v_h_170_, v___x_175_);
v___x_177_ = lean_nat_add(v_i_163_, v___x_172_);
lean_dec(v_i_163_);
lean_inc(v_v_168_);
lean_inc(v_k_167_);
v___x_178_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg(v_entries_164_, v_h_176_, v_depth_160_, v_k_167_, v_v_168_);
v_i_163_ = v___x_177_;
v_entries_164_ = v___x_178_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_depth_180_, lean_object* v_keys_181_, lean_object* v_vals_182_, lean_object* v_i_183_, lean_object* v_entries_184_){
_start:
{
size_t v_depth_boxed_185_; lean_object* v_res_186_; 
v_depth_boxed_185_ = lean_unbox_usize(v_depth_180_);
lean_dec(v_depth_180_);
v_res_186_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_boxed_185_, v_keys_181_, v_vals_182_, v_i_183_, v_entries_184_);
lean_dec_ref(v_vals_182_);
lean_dec_ref(v_keys_181_);
return v_res_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_x_187_, lean_object* v_x_188_, lean_object* v_x_189_, lean_object* v_x_190_, lean_object* v_x_191_){
_start:
{
size_t v_x_1688__boxed_192_; size_t v_x_1689__boxed_193_; lean_object* v_res_194_; 
v_x_1688__boxed_192_ = lean_unbox_usize(v_x_188_);
lean_dec(v_x_188_);
v_x_1689__boxed_193_ = lean_unbox_usize(v_x_189_);
lean_dec(v_x_189_);
v_res_194_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg(v_x_187_, v_x_1688__boxed_192_, v_x_1689__boxed_193_, v_x_190_, v_x_191_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0___redArg(lean_object* v_x_195_, lean_object* v_x_196_, lean_object* v_x_197_){
_start:
{
uint64_t v___x_198_; size_t v___x_199_; size_t v___x_200_; lean_object* v___x_201_; 
v___x_198_ = l_Lean_instHashableMVarId_hash(v_x_196_);
v___x_199_ = lean_uint64_to_usize(v___x_198_);
v___x_200_ = ((size_t)1ULL);
v___x_201_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg(v_x_195_, v___x_199_, v___x_200_, v_x_196_, v_x_197_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0___redArg(lean_object* v_mvarId_202_, lean_object* v_val_203_, lean_object* v___y_204_){
_start:
{
lean_object* v___x_206_; lean_object* v_mctx_207_; lean_object* v_cache_208_; lean_object* v_zetaDeltaFVarIds_209_; lean_object* v_postponed_210_; lean_object* v_diag_211_; lean_object* v___x_213_; uint8_t v_isShared_214_; uint8_t v_isSharedCheck_240_; 
v___x_206_ = lean_st_ref_take(v___y_204_);
v_mctx_207_ = lean_ctor_get(v___x_206_, 0);
v_cache_208_ = lean_ctor_get(v___x_206_, 1);
v_zetaDeltaFVarIds_209_ = lean_ctor_get(v___x_206_, 2);
v_postponed_210_ = lean_ctor_get(v___x_206_, 3);
v_diag_211_ = lean_ctor_get(v___x_206_, 4);
v_isSharedCheck_240_ = !lean_is_exclusive(v___x_206_);
if (v_isSharedCheck_240_ == 0)
{
v___x_213_ = v___x_206_;
v_isShared_214_ = v_isSharedCheck_240_;
goto v_resetjp_212_;
}
else
{
lean_inc(v_diag_211_);
lean_inc(v_postponed_210_);
lean_inc(v_zetaDeltaFVarIds_209_);
lean_inc(v_cache_208_);
lean_inc(v_mctx_207_);
lean_dec(v___x_206_);
v___x_213_ = lean_box(0);
v_isShared_214_ = v_isSharedCheck_240_;
goto v_resetjp_212_;
}
v_resetjp_212_:
{
lean_object* v_depth_215_; lean_object* v_levelAssignDepth_216_; lean_object* v_lmvarCounter_217_; lean_object* v_mvarCounter_218_; lean_object* v_lDecls_219_; lean_object* v_decls_220_; lean_object* v_userNames_221_; lean_object* v_lAssignment_222_; lean_object* v_eAssignment_223_; lean_object* v_dAssignment_224_; lean_object* v_instanceTypedMVars_225_; lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_239_; 
v_depth_215_ = lean_ctor_get(v_mctx_207_, 0);
v_levelAssignDepth_216_ = lean_ctor_get(v_mctx_207_, 1);
v_lmvarCounter_217_ = lean_ctor_get(v_mctx_207_, 2);
v_mvarCounter_218_ = lean_ctor_get(v_mctx_207_, 3);
v_lDecls_219_ = lean_ctor_get(v_mctx_207_, 4);
v_decls_220_ = lean_ctor_get(v_mctx_207_, 5);
v_userNames_221_ = lean_ctor_get(v_mctx_207_, 6);
v_lAssignment_222_ = lean_ctor_get(v_mctx_207_, 7);
v_eAssignment_223_ = lean_ctor_get(v_mctx_207_, 8);
v_dAssignment_224_ = lean_ctor_get(v_mctx_207_, 9);
v_instanceTypedMVars_225_ = lean_ctor_get(v_mctx_207_, 10);
v_isSharedCheck_239_ = !lean_is_exclusive(v_mctx_207_);
if (v_isSharedCheck_239_ == 0)
{
v___x_227_ = v_mctx_207_;
v_isShared_228_ = v_isSharedCheck_239_;
goto v_resetjp_226_;
}
else
{
lean_inc(v_instanceTypedMVars_225_);
lean_inc(v_dAssignment_224_);
lean_inc(v_eAssignment_223_);
lean_inc(v_lAssignment_222_);
lean_inc(v_userNames_221_);
lean_inc(v_decls_220_);
lean_inc(v_lDecls_219_);
lean_inc(v_mvarCounter_218_);
lean_inc(v_lmvarCounter_217_);
lean_inc(v_levelAssignDepth_216_);
lean_inc(v_depth_215_);
lean_dec(v_mctx_207_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_239_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
lean_object* v___x_229_; lean_object* v___x_231_; 
v___x_229_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0___redArg(v_eAssignment_223_, v_mvarId_202_, v_val_203_);
if (v_isShared_228_ == 0)
{
lean_ctor_set(v___x_227_, 8, v___x_229_);
v___x_231_ = v___x_227_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v_depth_215_);
lean_ctor_set(v_reuseFailAlloc_238_, 1, v_levelAssignDepth_216_);
lean_ctor_set(v_reuseFailAlloc_238_, 2, v_lmvarCounter_217_);
lean_ctor_set(v_reuseFailAlloc_238_, 3, v_mvarCounter_218_);
lean_ctor_set(v_reuseFailAlloc_238_, 4, v_lDecls_219_);
lean_ctor_set(v_reuseFailAlloc_238_, 5, v_decls_220_);
lean_ctor_set(v_reuseFailAlloc_238_, 6, v_userNames_221_);
lean_ctor_set(v_reuseFailAlloc_238_, 7, v_lAssignment_222_);
lean_ctor_set(v_reuseFailAlloc_238_, 8, v___x_229_);
lean_ctor_set(v_reuseFailAlloc_238_, 9, v_dAssignment_224_);
lean_ctor_set(v_reuseFailAlloc_238_, 10, v_instanceTypedMVars_225_);
v___x_231_ = v_reuseFailAlloc_238_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
lean_object* v___x_233_; 
if (v_isShared_214_ == 0)
{
lean_ctor_set(v___x_213_, 0, v___x_231_);
v___x_233_ = v___x_213_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v___x_231_);
lean_ctor_set(v_reuseFailAlloc_237_, 1, v_cache_208_);
lean_ctor_set(v_reuseFailAlloc_237_, 2, v_zetaDeltaFVarIds_209_);
lean_ctor_set(v_reuseFailAlloc_237_, 3, v_postponed_210_);
lean_ctor_set(v_reuseFailAlloc_237_, 4, v_diag_211_);
v___x_233_ = v_reuseFailAlloc_237_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_234_ = lean_st_ref_put(v___y_204_, v___x_233_);
v___x_235_ = lean_box(0);
v___x_236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_236_, 0, v___x_235_);
return v___x_236_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0___redArg___boxed(lean_object* v_mvarId_241_, lean_object* v_val_242_, lean_object* v___y_243_, lean_object* v___y_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0___redArg(v_mvarId_241_, v_val_242_, v___y_243_);
lean_dec(v___y_243_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetEq___lam__0(lean_object* v_mvarId_251_, lean_object* v___x_252_, lean_object* v_targetNew_253_, lean_object* v_eqProof_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_){
_start:
{
lean_object* v___x_260_; 
lean_inc(v_mvarId_251_);
v___x_260_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_251_, v___x_252_, v___y_255_, v___y_256_, v___y_257_, v___y_258_);
if (lean_obj_tag(v___x_260_) == 0)
{
lean_object* v___x_261_; 
lean_dec_ref_known(v___x_260_, 1);
lean_inc(v_mvarId_251_);
v___x_261_ = l_Lean_MVarId_getTag(v_mvarId_251_, v___y_255_, v___y_256_, v___y_257_, v___y_258_);
if (lean_obj_tag(v___x_261_) == 0)
{
lean_object* v_a_262_; lean_object* v___x_263_; 
v_a_262_ = lean_ctor_get(v___x_261_, 0);
lean_inc(v_a_262_);
lean_dec_ref_known(v___x_261_, 1);
lean_inc_ref(v_targetNew_253_);
v___x_263_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_targetNew_253_, v_a_262_, v___y_255_, v___y_256_, v___y_257_, v___y_258_);
if (lean_obj_tag(v___x_263_) == 0)
{
lean_object* v_a_264_; lean_object* v___x_265_; 
v_a_264_ = lean_ctor_get(v___x_263_, 0);
lean_inc(v_a_264_);
lean_dec_ref_known(v___x_263_, 1);
lean_inc(v_mvarId_251_);
v___x_265_ = l_Lean_MVarId_getType(v_mvarId_251_, v___y_255_, v___y_256_, v___y_257_, v___y_258_);
if (lean_obj_tag(v___x_265_) == 0)
{
lean_object* v_a_266_; lean_object* v___x_267_; 
v_a_266_ = lean_ctor_get(v___x_265_, 0);
lean_inc_n(v_a_266_, 2);
lean_dec_ref_known(v___x_265_, 1);
v___x_267_ = l_Lean_Meta_getLevel(v_a_266_, v___y_255_, v___y_256_, v___y_257_, v___y_258_);
if (lean_obj_tag(v___x_267_) == 0)
{
lean_object* v_a_268_; lean_object* v___x_269_; 
v_a_268_ = lean_ctor_get(v___x_267_, 0);
lean_inc(v_a_268_);
lean_dec_ref_known(v___x_267_, 1);
lean_inc_ref(v_targetNew_253_);
lean_inc(v_a_266_);
v___x_269_ = l_Lean_Meta_mkEq(v_a_266_, v_targetNew_253_, v___y_255_, v___y_256_, v___y_257_, v___y_258_);
if (lean_obj_tag(v___x_269_) == 0)
{
lean_object* v_a_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_291_; 
v_a_270_ = lean_ctor_get(v___x_269_, 0);
lean_inc(v_a_270_);
lean_dec_ref_known(v___x_269_, 1);
v___x_271_ = l_Lean_Meta_mkExpectedPropHint(v_eqProof_254_, v_a_270_);
v___x_272_ = ((lean_object*)(l_Lean_MVarId_replaceTargetEq___lam__0___closed__2));
v___x_273_ = lean_box(0);
v___x_274_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_274_, 0, v_a_268_);
lean_ctor_set(v___x_274_, 1, v___x_273_);
v___x_275_ = l_Lean_mkConst(v___x_272_, v___x_274_);
v___x_276_ = lean_unsigned_to_nat(4u);
v___x_277_ = lean_mk_empty_array_with_capacity(v___x_276_);
v___x_278_ = lean_array_push(v___x_277_, v_a_266_);
v___x_279_ = lean_array_push(v___x_278_, v_targetNew_253_);
v___x_280_ = lean_array_push(v___x_279_, v___x_271_);
lean_inc(v_a_264_);
v___x_281_ = lean_array_push(v___x_280_, v_a_264_);
v___x_282_ = l_Lean_mkAppN(v___x_275_, v___x_281_);
lean_dec_ref(v___x_281_);
v___x_283_ = l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0___redArg(v_mvarId_251_, v___x_282_, v___y_256_);
v_isSharedCheck_291_ = !lean_is_exclusive(v___x_283_);
if (v_isSharedCheck_291_ == 0)
{
lean_object* v_unused_292_; 
v_unused_292_ = lean_ctor_get(v___x_283_, 0);
lean_dec(v_unused_292_);
v___x_285_ = v___x_283_;
v_isShared_286_ = v_isSharedCheck_291_;
goto v_resetjp_284_;
}
else
{
lean_dec(v___x_283_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_291_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v___x_287_; lean_object* v___x_289_; 
v___x_287_ = l_Lean_Expr_mvarId_x21(v_a_264_);
lean_dec(v_a_264_);
if (v_isShared_286_ == 0)
{
lean_ctor_set(v___x_285_, 0, v___x_287_);
v___x_289_ = v___x_285_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v___x_287_);
v___x_289_ = v_reuseFailAlloc_290_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
return v___x_289_;
}
}
}
else
{
lean_object* v_a_293_; lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_300_; 
lean_dec(v_a_268_);
lean_dec(v_a_266_);
lean_dec(v_a_264_);
lean_dec_ref(v_eqProof_254_);
lean_dec_ref(v_targetNew_253_);
lean_dec(v_mvarId_251_);
v_a_293_ = lean_ctor_get(v___x_269_, 0);
v_isSharedCheck_300_ = !lean_is_exclusive(v___x_269_);
if (v_isSharedCheck_300_ == 0)
{
v___x_295_ = v___x_269_;
v_isShared_296_ = v_isSharedCheck_300_;
goto v_resetjp_294_;
}
else
{
lean_inc(v_a_293_);
lean_dec(v___x_269_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_300_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
lean_object* v___x_298_; 
if (v_isShared_296_ == 0)
{
v___x_298_ = v___x_295_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v_a_293_);
v___x_298_ = v_reuseFailAlloc_299_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
return v___x_298_;
}
}
}
}
else
{
lean_object* v_a_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_308_; 
lean_dec(v_a_266_);
lean_dec(v_a_264_);
lean_dec_ref(v_eqProof_254_);
lean_dec_ref(v_targetNew_253_);
lean_dec(v_mvarId_251_);
v_a_301_ = lean_ctor_get(v___x_267_, 0);
v_isSharedCheck_308_ = !lean_is_exclusive(v___x_267_);
if (v_isSharedCheck_308_ == 0)
{
v___x_303_ = v___x_267_;
v_isShared_304_ = v_isSharedCheck_308_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_a_301_);
lean_dec(v___x_267_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_308_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v___x_306_; 
if (v_isShared_304_ == 0)
{
v___x_306_ = v___x_303_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v_a_301_);
v___x_306_ = v_reuseFailAlloc_307_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
return v___x_306_;
}
}
}
}
else
{
lean_object* v_a_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_316_; 
lean_dec(v_a_264_);
lean_dec_ref(v_eqProof_254_);
lean_dec_ref(v_targetNew_253_);
lean_dec(v_mvarId_251_);
v_a_309_ = lean_ctor_get(v___x_265_, 0);
v_isSharedCheck_316_ = !lean_is_exclusive(v___x_265_);
if (v_isSharedCheck_316_ == 0)
{
v___x_311_ = v___x_265_;
v_isShared_312_ = v_isSharedCheck_316_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_a_309_);
lean_dec(v___x_265_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_316_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___x_314_; 
if (v_isShared_312_ == 0)
{
v___x_314_ = v___x_311_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v_a_309_);
v___x_314_ = v_reuseFailAlloc_315_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
return v___x_314_;
}
}
}
}
else
{
lean_object* v_a_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_324_; 
lean_dec_ref(v_eqProof_254_);
lean_dec_ref(v_targetNew_253_);
lean_dec(v_mvarId_251_);
v_a_317_ = lean_ctor_get(v___x_263_, 0);
v_isSharedCheck_324_ = !lean_is_exclusive(v___x_263_);
if (v_isSharedCheck_324_ == 0)
{
v___x_319_ = v___x_263_;
v_isShared_320_ = v_isSharedCheck_324_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_a_317_);
lean_dec(v___x_263_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_324_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v___x_322_; 
if (v_isShared_320_ == 0)
{
v___x_322_ = v___x_319_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v_a_317_);
v___x_322_ = v_reuseFailAlloc_323_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
return v___x_322_;
}
}
}
}
else
{
lean_object* v_a_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_332_; 
lean_dec_ref(v_eqProof_254_);
lean_dec_ref(v_targetNew_253_);
lean_dec(v_mvarId_251_);
v_a_325_ = lean_ctor_get(v___x_261_, 0);
v_isSharedCheck_332_ = !lean_is_exclusive(v___x_261_);
if (v_isSharedCheck_332_ == 0)
{
v___x_327_ = v___x_261_;
v_isShared_328_ = v_isSharedCheck_332_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_a_325_);
lean_dec(v___x_261_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_332_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v___x_330_; 
if (v_isShared_328_ == 0)
{
v___x_330_ = v___x_327_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_a_325_);
v___x_330_ = v_reuseFailAlloc_331_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
return v___x_330_;
}
}
}
}
else
{
lean_object* v_a_333_; lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_340_; 
lean_dec_ref(v_eqProof_254_);
lean_dec_ref(v_targetNew_253_);
lean_dec(v_mvarId_251_);
v_a_333_ = lean_ctor_get(v___x_260_, 0);
v_isSharedCheck_340_ = !lean_is_exclusive(v___x_260_);
if (v_isSharedCheck_340_ == 0)
{
v___x_335_ = v___x_260_;
v_isShared_336_ = v_isSharedCheck_340_;
goto v_resetjp_334_;
}
else
{
lean_inc(v_a_333_);
lean_dec(v___x_260_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_340_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
lean_object* v___x_338_; 
if (v_isShared_336_ == 0)
{
v___x_338_ = v___x_335_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v_a_333_);
v___x_338_ = v_reuseFailAlloc_339_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
return v___x_338_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetEq___lam__0___boxed(lean_object* v_mvarId_341_, lean_object* v___x_342_, lean_object* v_targetNew_343_, lean_object* v_eqProof_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_Lean_MVarId_replaceTargetEq___lam__0(v_mvarId_341_, v___x_342_, v_targetNew_343_, v_eqProof_344_, v___y_345_, v___y_346_, v___y_347_, v___y_348_);
lean_dec(v___y_348_);
lean_dec_ref(v___y_347_);
lean_dec(v___y_346_);
lean_dec_ref(v___y_345_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetEq(lean_object* v_mvarId_354_, lean_object* v_targetNew_355_, lean_object* v_eqProof_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_){
_start:
{
lean_object* v___x_362_; lean_object* v___f_363_; lean_object* v___x_364_; 
v___x_362_ = ((lean_object*)(l_Lean_MVarId_replaceTargetEq___closed__1));
lean_inc(v_mvarId_354_);
v___f_363_ = lean_alloc_closure((void*)(l_Lean_MVarId_replaceTargetEq___lam__0___boxed), 9, 4);
lean_closure_set(v___f_363_, 0, v_mvarId_354_);
lean_closure_set(v___f_363_, 1, v___x_362_);
lean_closure_set(v___f_363_, 2, v_targetNew_355_);
lean_closure_set(v___f_363_, 3, v_eqProof_356_);
v___x_364_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(v_mvarId_354_, v___f_363_, v_a_357_, v_a_358_, v_a_359_, v_a_360_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetEq___boxed(lean_object* v_mvarId_365_, lean_object* v_targetNew_366_, lean_object* v_eqProof_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l_Lean_MVarId_replaceTargetEq(v_mvarId_365_, v_targetNew_366_, v_eqProof_367_, v_a_368_, v_a_369_, v_a_370_, v_a_371_);
lean_dec(v_a_371_);
lean_dec_ref(v_a_370_);
lean_dec(v_a_369_);
lean_dec_ref(v_a_368_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0(lean_object* v_mvarId_374_, lean_object* v_val_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0___redArg(v_mvarId_374_, v_val_375_, v___y_377_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0___boxed(lean_object* v_mvarId_382_, lean_object* v_val_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0(v_mvarId_382_, v_val_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_);
lean_dec(v___y_387_);
lean_dec_ref(v___y_386_);
lean_dec(v___y_385_);
lean_dec_ref(v___y_384_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0(lean_object* v_00_u03b2_390_, lean_object* v_x_391_, lean_object* v_x_392_, lean_object* v_x_393_){
_start:
{
lean_object* v___x_394_; 
v___x_394_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0___redArg(v_x_391_, v_x_392_, v_x_393_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_395_, lean_object* v_x_396_, size_t v_x_397_, size_t v_x_398_, lean_object* v_x_399_, lean_object* v_x_400_){
_start:
{
lean_object* v___x_401_; 
v___x_401_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg(v_x_396_, v_x_397_, v_x_398_, v_x_399_, v_x_400_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_402_, lean_object* v_x_403_, lean_object* v_x_404_, lean_object* v_x_405_, lean_object* v_x_406_, lean_object* v_x_407_){
_start:
{
size_t v_x_2143__boxed_408_; size_t v_x_2144__boxed_409_; lean_object* v_res_410_; 
v_x_2143__boxed_408_ = lean_unbox_usize(v_x_404_);
lean_dec(v_x_404_);
v_x_2144__boxed_409_ = lean_unbox_usize(v_x_405_);
lean_dec(v_x_405_);
v_res_410_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2(v_00_u03b2_402_, v_x_403_, v_x_2143__boxed_408_, v_x_2144__boxed_409_, v_x_406_, v_x_407_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_411_, lean_object* v_n_412_, lean_object* v_k_413_, lean_object* v_v_414_){
_start:
{
lean_object* v___x_415_; 
v___x_415_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__3___redArg(v_n_412_, v_k_413_, v_v_414_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_416_, size_t v_depth_417_, lean_object* v_keys_418_, lean_object* v_vals_419_, lean_object* v_heq_420_, lean_object* v_i_421_, lean_object* v_entries_422_){
_start:
{
lean_object* v___x_423_; 
v___x_423_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_417_, v_keys_418_, v_vals_419_, v_i_421_, v_entries_422_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03b2_424_, lean_object* v_depth_425_, lean_object* v_keys_426_, lean_object* v_vals_427_, lean_object* v_heq_428_, lean_object* v_i_429_, lean_object* v_entries_430_){
_start:
{
size_t v_depth_boxed_431_; lean_object* v_res_432_; 
v_depth_boxed_431_ = lean_unbox_usize(v_depth_425_);
lean_dec(v_depth_425_);
v_res_432_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__4(v_00_u03b2_424_, v_depth_boxed_431_, v_keys_426_, v_vals_427_, v_heq_428_, v_i_429_, v_entries_430_);
lean_dec_ref(v_vals_427_);
lean_dec_ref(v_keys_426_);
return v_res_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_433_, lean_object* v_x_434_, lean_object* v_x_435_, lean_object* v_x_436_, lean_object* v_x_437_){
_start:
{
lean_object* v___x_438_; 
v___x_438_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v_x_434_, v_x_435_, v_x_436_, v_x_437_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_replaceTargetDefEq_spec__0___redArg(lean_object* v_e_439_, lean_object* v___y_440_){
_start:
{
uint8_t v___x_442_; 
v___x_442_ = l_Lean_Expr_hasMVar(v_e_439_);
if (v___x_442_ == 0)
{
lean_object* v___x_443_; 
v___x_443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_443_, 0, v_e_439_);
return v___x_443_;
}
else
{
lean_object* v___x_444_; lean_object* v_mctx_445_; lean_object* v___x_446_; lean_object* v_fst_447_; lean_object* v_snd_448_; lean_object* v___x_449_; lean_object* v_cache_450_; lean_object* v_zetaDeltaFVarIds_451_; lean_object* v_postponed_452_; lean_object* v_diag_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_462_; 
v___x_444_ = lean_st_ref_get(v___y_440_);
v_mctx_445_ = lean_ctor_get(v___x_444_, 0);
lean_inc_ref(v_mctx_445_);
lean_dec(v___x_444_);
v___x_446_ = l_Lean_instantiateMVarsCore(v_mctx_445_, v_e_439_);
v_fst_447_ = lean_ctor_get(v___x_446_, 0);
lean_inc(v_fst_447_);
v_snd_448_ = lean_ctor_get(v___x_446_, 1);
lean_inc(v_snd_448_);
lean_dec_ref(v___x_446_);
v___x_449_ = lean_st_ref_take(v___y_440_);
v_cache_450_ = lean_ctor_get(v___x_449_, 1);
v_zetaDeltaFVarIds_451_ = lean_ctor_get(v___x_449_, 2);
v_postponed_452_ = lean_ctor_get(v___x_449_, 3);
v_diag_453_ = lean_ctor_get(v___x_449_, 4);
v_isSharedCheck_462_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_462_ == 0)
{
lean_object* v_unused_463_; 
v_unused_463_ = lean_ctor_get(v___x_449_, 0);
lean_dec(v_unused_463_);
v___x_455_ = v___x_449_;
v_isShared_456_ = v_isSharedCheck_462_;
goto v_resetjp_454_;
}
else
{
lean_inc(v_diag_453_);
lean_inc(v_postponed_452_);
lean_inc(v_zetaDeltaFVarIds_451_);
lean_inc(v_cache_450_);
lean_dec(v___x_449_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_462_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v___x_458_; 
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 0, v_snd_448_);
v___x_458_ = v___x_455_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v_snd_448_);
lean_ctor_set(v_reuseFailAlloc_461_, 1, v_cache_450_);
lean_ctor_set(v_reuseFailAlloc_461_, 2, v_zetaDeltaFVarIds_451_);
lean_ctor_set(v_reuseFailAlloc_461_, 3, v_postponed_452_);
lean_ctor_set(v_reuseFailAlloc_461_, 4, v_diag_453_);
v___x_458_ = v_reuseFailAlloc_461_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_459_ = lean_st_ref_put(v___y_440_, v___x_458_);
v___x_460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_460_, 0, v_fst_447_);
return v___x_460_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_replaceTargetDefEq_spec__0___redArg___boxed(lean_object* v_e_464_, lean_object* v___y_465_, lean_object* v___y_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_Lean_instantiateMVars___at___00Lean_MVarId_replaceTargetDefEq_spec__0___redArg(v_e_464_, v___y_465_);
lean_dec(v___y_465_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_replaceTargetDefEq_spec__0(lean_object* v_e_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_){
_start:
{
lean_object* v___x_474_; 
v___x_474_ = l_Lean_instantiateMVars___at___00Lean_MVarId_replaceTargetDefEq_spec__0___redArg(v_e_468_, v___y_470_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_replaceTargetDefEq_spec__0___boxed(lean_object* v_e_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l_Lean_instantiateMVars___at___00Lean_MVarId_replaceTargetDefEq_spec__0(v_e_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_);
lean_dec(v___y_479_);
lean_dec_ref(v___y_478_);
lean_dec(v___y_477_);
lean_dec_ref(v___y_476_);
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetDefEq___lam__0(lean_object* v_mvarId_482_, lean_object* v___x_483_, lean_object* v_targetNew_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_){
_start:
{
lean_object* v___x_490_; 
lean_inc(v_mvarId_482_);
v___x_490_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_482_, v___x_483_, v___y_485_, v___y_486_, v___y_487_, v___y_488_);
if (lean_obj_tag(v___x_490_) == 0)
{
lean_object* v___x_491_; 
lean_dec_ref_known(v___x_490_, 1);
lean_inc(v_mvarId_482_);
v___x_491_ = l_Lean_MVarId_getType(v_mvarId_482_, v___y_485_, v___y_486_, v___y_487_, v___y_488_);
if (lean_obj_tag(v___x_491_) == 0)
{
lean_object* v_a_492_; lean_object* v___x_494_; uint8_t v_isShared_495_; uint8_t v_isSharedCheck_562_; 
v_a_492_ = lean_ctor_get(v___x_491_, 0);
v_isSharedCheck_562_ = !lean_is_exclusive(v___x_491_);
if (v_isSharedCheck_562_ == 0)
{
v___x_494_ = v___x_491_;
v_isShared_495_ = v_isSharedCheck_562_;
goto v_resetjp_493_;
}
else
{
lean_inc(v_a_492_);
lean_dec(v___x_491_);
v___x_494_ = lean_box(0);
v_isShared_495_ = v_isSharedCheck_562_;
goto v_resetjp_493_;
}
v_resetjp_493_:
{
uint8_t v___x_496_; 
v___x_496_ = lean_expr_equal(v_a_492_, v_targetNew_484_);
if (v___x_496_ == 0)
{
lean_object* v___x_497_; lean_object* v_a_498_; lean_object* v___x_499_; lean_object* v_a_500_; uint8_t v___x_501_; 
lean_del_object(v___x_494_);
v___x_497_ = l_Lean_instantiateMVars___at___00Lean_MVarId_replaceTargetDefEq_spec__0___redArg(v_a_492_, v___y_486_);
v_a_498_ = lean_ctor_get(v___x_497_, 0);
lean_inc(v_a_498_);
lean_dec_ref(v___x_497_);
v___x_499_ = l_Lean_instantiateMVars___at___00Lean_MVarId_replaceTargetDefEq_spec__0___redArg(v_targetNew_484_, v___y_486_);
v_a_500_ = lean_ctor_get(v___x_499_, 0);
lean_inc(v_a_500_);
lean_dec_ref(v___x_499_);
v___x_501_ = lean_expr_equal(v_a_498_, v_a_500_);
if (v___x_501_ == 0)
{
lean_object* v___x_502_; 
lean_inc(v_mvarId_482_);
v___x_502_ = l_Lean_MVarId_getTag(v_mvarId_482_, v___y_485_, v___y_486_, v___y_487_, v___y_488_);
if (lean_obj_tag(v___x_502_) == 0)
{
lean_object* v_a_503_; lean_object* v___x_504_; 
v_a_503_ = lean_ctor_get(v___x_502_, 0);
lean_inc(v_a_503_);
lean_dec_ref_known(v___x_502_, 1);
v___x_504_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_500_, v_a_503_, v___y_485_, v___y_486_, v___y_487_, v___y_488_);
if (lean_obj_tag(v___x_504_) == 0)
{
lean_object* v_a_505_; lean_object* v___x_506_; 
v_a_505_ = lean_ctor_get(v___x_504_, 0);
lean_inc_n(v_a_505_, 2);
lean_dec_ref_known(v___x_504_, 1);
v___x_506_ = l_Lean_Meta_mkExpectedTypeHint(v_a_505_, v_a_498_, v___y_485_, v___y_486_, v___y_487_, v___y_488_);
if (lean_obj_tag(v___x_506_) == 0)
{
lean_object* v_a_507_; lean_object* v___x_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_516_; 
v_a_507_ = lean_ctor_get(v___x_506_, 0);
lean_inc(v_a_507_);
lean_dec_ref_known(v___x_506_, 1);
v___x_508_ = l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0___redArg(v_mvarId_482_, v_a_507_, v___y_486_);
v_isSharedCheck_516_ = !lean_is_exclusive(v___x_508_);
if (v_isSharedCheck_516_ == 0)
{
lean_object* v_unused_517_; 
v_unused_517_ = lean_ctor_get(v___x_508_, 0);
lean_dec(v_unused_517_);
v___x_510_ = v___x_508_;
v_isShared_511_ = v_isSharedCheck_516_;
goto v_resetjp_509_;
}
else
{
lean_dec(v___x_508_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_516_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v___x_512_; lean_object* v___x_514_; 
v___x_512_ = l_Lean_Expr_mvarId_x21(v_a_505_);
lean_dec(v_a_505_);
if (v_isShared_511_ == 0)
{
lean_ctor_set(v___x_510_, 0, v___x_512_);
v___x_514_ = v___x_510_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v___x_512_);
v___x_514_ = v_reuseFailAlloc_515_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
return v___x_514_;
}
}
}
else
{
lean_object* v_a_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_525_; 
lean_dec(v_a_505_);
lean_dec(v_mvarId_482_);
v_a_518_ = lean_ctor_get(v___x_506_, 0);
v_isSharedCheck_525_ = !lean_is_exclusive(v___x_506_);
if (v_isSharedCheck_525_ == 0)
{
v___x_520_ = v___x_506_;
v_isShared_521_ = v_isSharedCheck_525_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_a_518_);
lean_dec(v___x_506_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_525_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v___x_523_; 
if (v_isShared_521_ == 0)
{
v___x_523_ = v___x_520_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v_a_518_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
}
}
else
{
lean_object* v_a_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_533_; 
lean_dec(v_a_498_);
lean_dec(v_mvarId_482_);
v_a_526_ = lean_ctor_get(v___x_504_, 0);
v_isSharedCheck_533_ = !lean_is_exclusive(v___x_504_);
if (v_isSharedCheck_533_ == 0)
{
v___x_528_ = v___x_504_;
v_isShared_529_ = v_isSharedCheck_533_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_a_526_);
lean_dec(v___x_504_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_533_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v___x_531_; 
if (v_isShared_529_ == 0)
{
v___x_531_ = v___x_528_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v_a_526_);
v___x_531_ = v_reuseFailAlloc_532_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
return v___x_531_;
}
}
}
}
else
{
lean_object* v_a_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_541_; 
lean_dec(v_a_500_);
lean_dec(v_a_498_);
lean_dec(v_mvarId_482_);
v_a_534_ = lean_ctor_get(v___x_502_, 0);
v_isSharedCheck_541_ = !lean_is_exclusive(v___x_502_);
if (v_isSharedCheck_541_ == 0)
{
v___x_536_ = v___x_502_;
v_isShared_537_ = v_isSharedCheck_541_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_a_534_);
lean_dec(v___x_502_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_541_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_539_; 
if (v_isShared_537_ == 0)
{
v___x_539_ = v___x_536_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v_a_534_);
v___x_539_ = v_reuseFailAlloc_540_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
return v___x_539_;
}
}
}
}
else
{
lean_object* v___x_542_; 
lean_dec(v_a_500_);
lean_inc(v_mvarId_482_);
v___x_542_ = l_Lean_MVarId_setType___redArg(v_mvarId_482_, v_a_498_, v___y_486_);
if (lean_obj_tag(v___x_542_) == 0)
{
lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_549_; 
v_isSharedCheck_549_ = !lean_is_exclusive(v___x_542_);
if (v_isSharedCheck_549_ == 0)
{
lean_object* v_unused_550_; 
v_unused_550_ = lean_ctor_get(v___x_542_, 0);
lean_dec(v_unused_550_);
v___x_544_ = v___x_542_;
v_isShared_545_ = v_isSharedCheck_549_;
goto v_resetjp_543_;
}
else
{
lean_dec(v___x_542_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_549_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v___x_547_; 
if (v_isShared_545_ == 0)
{
lean_ctor_set(v___x_544_, 0, v_mvarId_482_);
v___x_547_ = v___x_544_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v_mvarId_482_);
v___x_547_ = v_reuseFailAlloc_548_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
return v___x_547_;
}
}
}
else
{
lean_object* v_a_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_558_; 
lean_dec(v_mvarId_482_);
v_a_551_ = lean_ctor_get(v___x_542_, 0);
v_isSharedCheck_558_ = !lean_is_exclusive(v___x_542_);
if (v_isSharedCheck_558_ == 0)
{
v___x_553_ = v___x_542_;
v_isShared_554_ = v_isSharedCheck_558_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_a_551_);
lean_dec(v___x_542_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_558_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
lean_object* v___x_556_; 
if (v_isShared_554_ == 0)
{
v___x_556_ = v___x_553_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v_a_551_);
v___x_556_ = v_reuseFailAlloc_557_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
return v___x_556_;
}
}
}
}
}
else
{
lean_object* v___x_560_; 
lean_dec(v_a_492_);
lean_dec_ref(v_targetNew_484_);
if (v_isShared_495_ == 0)
{
lean_ctor_set(v___x_494_, 0, v_mvarId_482_);
v___x_560_ = v___x_494_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v_mvarId_482_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
return v___x_560_;
}
}
}
}
else
{
lean_object* v_a_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_570_; 
lean_dec_ref(v_targetNew_484_);
lean_dec(v_mvarId_482_);
v_a_563_ = lean_ctor_get(v___x_491_, 0);
v_isSharedCheck_570_ = !lean_is_exclusive(v___x_491_);
if (v_isSharedCheck_570_ == 0)
{
v___x_565_ = v___x_491_;
v_isShared_566_ = v_isSharedCheck_570_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_a_563_);
lean_dec(v___x_491_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_570_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___x_568_; 
if (v_isShared_566_ == 0)
{
v___x_568_ = v___x_565_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v_a_563_);
v___x_568_ = v_reuseFailAlloc_569_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
return v___x_568_;
}
}
}
}
else
{
lean_object* v_a_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_578_; 
lean_dec_ref(v_targetNew_484_);
lean_dec(v_mvarId_482_);
v_a_571_ = lean_ctor_get(v___x_490_, 0);
v_isSharedCheck_578_ = !lean_is_exclusive(v___x_490_);
if (v_isSharedCheck_578_ == 0)
{
v___x_573_ = v___x_490_;
v_isShared_574_ = v_isSharedCheck_578_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_a_571_);
lean_dec(v___x_490_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_578_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v___x_576_; 
if (v_isShared_574_ == 0)
{
v___x_576_ = v___x_573_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v_a_571_);
v___x_576_ = v_reuseFailAlloc_577_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
return v___x_576_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetDefEq___lam__0___boxed(lean_object* v_mvarId_579_, lean_object* v___x_580_, lean_object* v_targetNew_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l_Lean_MVarId_replaceTargetDefEq___lam__0(v_mvarId_579_, v___x_580_, v_targetNew_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_);
lean_dec(v___y_585_);
lean_dec_ref(v___y_584_);
lean_dec(v___y_583_);
lean_dec_ref(v___y_582_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetDefEq(lean_object* v_mvarId_591_, lean_object* v_targetNew_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_){
_start:
{
lean_object* v___x_598_; lean_object* v___f_599_; lean_object* v___x_600_; 
v___x_598_ = ((lean_object*)(l_Lean_MVarId_replaceTargetDefEq___closed__1));
lean_inc(v_mvarId_591_);
v___f_599_ = lean_alloc_closure((void*)(l_Lean_MVarId_replaceTargetDefEq___lam__0___boxed), 8, 3);
lean_closure_set(v___f_599_, 0, v_mvarId_591_);
lean_closure_set(v___f_599_, 1, v___x_598_);
lean_closure_set(v___f_599_, 2, v_targetNew_592_);
v___x_600_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(v_mvarId_591_, v___f_599_, v_a_593_, v_a_594_, v_a_595_, v_a_596_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetDefEq___boxed(lean_object* v_mvarId_601_, lean_object* v_targetNew_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_, lean_object* v_a_606_, lean_object* v_a_607_){
_start:
{
lean_object* v_res_608_; 
v_res_608_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_601_, v_targetNew_602_, v_a_603_, v_a_604_, v_a_605_, v_a_606_);
lean_dec(v_a_606_);
lean_dec_ref(v_a_605_);
lean_dec(v_a_604_);
lean_dec_ref(v_a_603_);
return v_res_608_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replace___lam__0(lean_object* v_mvarId_609_, lean_object* v_fvarId_610_, lean_object* v_val_611_, lean_object* v_userName_x3f_612_, lean_object* v_type_x3f_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_){
_start:
{
lean_object* v___y_620_; lean_object* v_a_621_; lean_object* v_a_652_; 
if (lean_obj_tag(v_type_x3f_613_) == 0)
{
lean_object* v___x_665_; 
lean_inc(v___y_617_);
lean_inc_ref(v___y_616_);
lean_inc(v___y_615_);
lean_inc_ref(v___y_614_);
lean_inc_ref(v_val_611_);
v___x_665_ = lean_infer_type(v_val_611_, v___y_614_, v___y_615_, v___y_616_, v___y_617_);
if (lean_obj_tag(v___x_665_) == 0)
{
lean_object* v_a_666_; 
v_a_666_ = lean_ctor_get(v___x_665_, 0);
lean_inc(v_a_666_);
lean_dec_ref_known(v___x_665_, 1);
v_a_652_ = v_a_666_;
goto v___jp_651_;
}
else
{
lean_object* v_a_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_674_; 
lean_dec(v___y_617_);
lean_dec_ref(v___y_616_);
lean_dec(v___y_615_);
lean_dec_ref(v___y_614_);
lean_dec(v_userName_x3f_612_);
lean_dec_ref(v_val_611_);
lean_dec(v_fvarId_610_);
lean_dec(v_mvarId_609_);
v_a_667_ = lean_ctor_get(v___x_665_, 0);
v_isSharedCheck_674_ = !lean_is_exclusive(v___x_665_);
if (v_isSharedCheck_674_ == 0)
{
v___x_669_ = v___x_665_;
v_isShared_670_ = v_isSharedCheck_674_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_a_667_);
lean_dec(v___x_665_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_674_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v___x_672_; 
if (v_isShared_670_ == 0)
{
v___x_672_ = v___x_669_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v_a_667_);
v___x_672_ = v_reuseFailAlloc_673_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
return v___x_672_;
}
}
}
}
else
{
lean_object* v_val_675_; 
v_val_675_ = lean_ctor_get(v_type_x3f_613_, 0);
lean_inc(v_val_675_);
lean_dec_ref_known(v_type_x3f_613_, 1);
v_a_652_ = v_val_675_;
goto v___jp_651_;
}
v___jp_619_:
{
lean_object* v___x_622_; 
lean_inc(v_fvarId_610_);
v___x_622_ = l_Lean_MVarId_assertAfter_x27(v_mvarId_609_, v_fvarId_610_, v_a_621_, v___y_620_, v_val_611_, v___y_614_, v___y_615_, v___y_616_, v___y_617_);
if (lean_obj_tag(v___x_622_) == 0)
{
lean_object* v_a_623_; lean_object* v_fvarId_624_; lean_object* v_mvarId_625_; lean_object* v_subst_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_650_; 
v_a_623_ = lean_ctor_get(v___x_622_, 0);
lean_inc(v_a_623_);
lean_dec_ref_known(v___x_622_, 1);
v_fvarId_624_ = lean_ctor_get(v_a_623_, 0);
v_mvarId_625_ = lean_ctor_get(v_a_623_, 1);
v_subst_626_ = lean_ctor_get(v_a_623_, 2);
v_isSharedCheck_650_ = !lean_is_exclusive(v_a_623_);
if (v_isSharedCheck_650_ == 0)
{
v___x_628_ = v_a_623_;
v_isShared_629_ = v_isSharedCheck_650_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_subst_626_);
lean_inc(v_mvarId_625_);
lean_inc(v_fvarId_624_);
lean_dec(v_a_623_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_650_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v___x_630_; 
v___x_630_ = l_Lean_MVarId_tryClear(v_mvarId_625_, v_fvarId_610_, v___y_614_, v___y_615_, v___y_616_, v___y_617_);
lean_dec(v___y_617_);
lean_dec_ref(v___y_616_);
lean_dec(v___y_615_);
lean_dec_ref(v___y_614_);
if (lean_obj_tag(v___x_630_) == 0)
{
lean_object* v_a_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_641_; 
v_a_631_ = lean_ctor_get(v___x_630_, 0);
v_isSharedCheck_641_ = !lean_is_exclusive(v___x_630_);
if (v_isSharedCheck_641_ == 0)
{
v___x_633_ = v___x_630_;
v_isShared_634_ = v_isSharedCheck_641_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_a_631_);
lean_dec(v___x_630_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_641_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
lean_object* v___x_636_; 
if (v_isShared_629_ == 0)
{
lean_ctor_set(v___x_628_, 1, v_a_631_);
v___x_636_ = v___x_628_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v_fvarId_624_);
lean_ctor_set(v_reuseFailAlloc_640_, 1, v_a_631_);
lean_ctor_set(v_reuseFailAlloc_640_, 2, v_subst_626_);
v___x_636_ = v_reuseFailAlloc_640_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
lean_object* v___x_638_; 
if (v_isShared_634_ == 0)
{
lean_ctor_set(v___x_633_, 0, v___x_636_);
v___x_638_ = v___x_633_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v___x_636_);
v___x_638_ = v_reuseFailAlloc_639_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
return v___x_638_;
}
}
}
}
else
{
lean_object* v_a_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_649_; 
lean_del_object(v___x_628_);
lean_dec(v_subst_626_);
lean_dec(v_fvarId_624_);
v_a_642_ = lean_ctor_get(v___x_630_, 0);
v_isSharedCheck_649_ = !lean_is_exclusive(v___x_630_);
if (v_isSharedCheck_649_ == 0)
{
v___x_644_ = v___x_630_;
v_isShared_645_ = v_isSharedCheck_649_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_a_642_);
lean_dec(v___x_630_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_649_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
lean_object* v___x_647_; 
if (v_isShared_645_ == 0)
{
v___x_647_ = v___x_644_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v_a_642_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
return v___x_647_;
}
}
}
}
}
else
{
lean_dec(v___y_617_);
lean_dec_ref(v___y_616_);
lean_dec(v___y_615_);
lean_dec_ref(v___y_614_);
lean_dec(v_fvarId_610_);
return v___x_622_;
}
}
v___jp_651_:
{
if (lean_obj_tag(v_userName_x3f_612_) == 0)
{
lean_object* v___x_653_; 
lean_inc(v_fvarId_610_);
v___x_653_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_610_, v___y_614_, v___y_616_, v___y_617_);
if (lean_obj_tag(v___x_653_) == 0)
{
lean_object* v_a_654_; lean_object* v___x_655_; 
v_a_654_ = lean_ctor_get(v___x_653_, 0);
lean_inc(v_a_654_);
lean_dec_ref_known(v___x_653_, 1);
v___x_655_ = l_Lean_LocalDecl_userName(v_a_654_);
lean_dec(v_a_654_);
v___y_620_ = v_a_652_;
v_a_621_ = v___x_655_;
goto v___jp_619_;
}
else
{
lean_object* v_a_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_663_; 
lean_dec_ref(v_a_652_);
lean_dec(v___y_617_);
lean_dec_ref(v___y_616_);
lean_dec(v___y_615_);
lean_dec_ref(v___y_614_);
lean_dec_ref(v_val_611_);
lean_dec(v_fvarId_610_);
lean_dec(v_mvarId_609_);
v_a_656_ = lean_ctor_get(v___x_653_, 0);
v_isSharedCheck_663_ = !lean_is_exclusive(v___x_653_);
if (v_isSharedCheck_663_ == 0)
{
v___x_658_ = v___x_653_;
v_isShared_659_ = v_isSharedCheck_663_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_a_656_);
lean_dec(v___x_653_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_663_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v___x_661_; 
if (v_isShared_659_ == 0)
{
v___x_661_ = v___x_658_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v_a_656_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
}
}
}
}
else
{
lean_object* v_val_664_; 
v_val_664_ = lean_ctor_get(v_userName_x3f_612_, 0);
lean_inc(v_val_664_);
lean_dec_ref_known(v_userName_x3f_612_, 1);
v___y_620_ = v_a_652_;
v_a_621_ = v_val_664_;
goto v___jp_619_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replace___lam__0___boxed(lean_object* v_mvarId_676_, lean_object* v_fvarId_677_, lean_object* v_val_678_, lean_object* v_userName_x3f_679_, lean_object* v_type_x3f_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_){
_start:
{
lean_object* v_res_686_; 
v_res_686_ = l_Lean_MVarId_replace___lam__0(v_mvarId_676_, v_fvarId_677_, v_val_678_, v_userName_x3f_679_, v_type_x3f_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_);
return v_res_686_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replace(lean_object* v_mvarId_687_, lean_object* v_fvarId_688_, lean_object* v_val_689_, lean_object* v_type_x3f_690_, lean_object* v_userName_x3f_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_){
_start:
{
lean_object* v___f_697_; lean_object* v___x_698_; 
lean_inc(v_mvarId_687_);
v___f_697_ = lean_alloc_closure((void*)(l_Lean_MVarId_replace___lam__0___boxed), 10, 5);
lean_closure_set(v___f_697_, 0, v_mvarId_687_);
lean_closure_set(v___f_697_, 1, v_fvarId_688_);
lean_closure_set(v___f_697_, 2, v_val_689_);
lean_closure_set(v___f_697_, 3, v_userName_x3f_691_);
lean_closure_set(v___f_697_, 4, v_type_x3f_690_);
v___x_698_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(v_mvarId_687_, v___f_697_, v_a_692_, v_a_693_, v_a_694_, v_a_695_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replace___boxed(lean_object* v_mvarId_699_, lean_object* v_fvarId_700_, lean_object* v_val_701_, lean_object* v_type_x3f_702_, lean_object* v_userName_x3f_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_){
_start:
{
lean_object* v_res_709_; 
v_res_709_ = l_Lean_MVarId_replace(v_mvarId_699_, v_fvarId_700_, v_val_701_, v_type_x3f_702_, v_userName_x3f_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_);
lean_dec(v_a_707_);
lean_dec_ref(v_a_706_);
lean_dec(v_a_705_);
lean_dec_ref(v_a_704_);
return v_res_709_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceLocalDecl___lam__0(lean_object* v_eqProof_710_, lean_object* v___x_711_, lean_object* v_typeNew_712_, lean_object* v_mvarId_713_, lean_object* v_fvarId_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_){
_start:
{
lean_object* v___x_720_; 
v___x_720_ = l_Lean_Meta_mkEqMP(v_eqProof_710_, v___x_711_, v___y_715_, v___y_716_, v___y_717_, v___y_718_);
if (lean_obj_tag(v___x_720_) == 0)
{
lean_object* v_a_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; 
v_a_721_ = lean_ctor_get(v___x_720_, 0);
lean_inc(v_a_721_);
lean_dec_ref_known(v___x_720_, 1);
v___x_722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_722_, 0, v_typeNew_712_);
v___x_723_ = lean_box(0);
v___x_724_ = l_Lean_MVarId_replace(v_mvarId_713_, v_fvarId_714_, v_a_721_, v___x_722_, v___x_723_, v___y_715_, v___y_716_, v___y_717_, v___y_718_);
return v___x_724_;
}
else
{
lean_object* v_a_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_732_; 
lean_dec(v_fvarId_714_);
lean_dec(v_mvarId_713_);
lean_dec_ref(v_typeNew_712_);
v_a_725_ = lean_ctor_get(v___x_720_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_720_);
if (v_isSharedCheck_732_ == 0)
{
v___x_727_ = v___x_720_;
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_a_725_);
lean_dec(v___x_720_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_730_; 
if (v_isShared_728_ == 0)
{
v___x_730_ = v___x_727_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_a_725_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceLocalDecl___lam__0___boxed(lean_object* v_eqProof_733_, lean_object* v___x_734_, lean_object* v_typeNew_735_, lean_object* v_mvarId_736_, lean_object* v_fvarId_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_){
_start:
{
lean_object* v_res_743_; 
v_res_743_ = l_Lean_MVarId_replaceLocalDecl___lam__0(v_eqProof_733_, v___x_734_, v_typeNew_735_, v_mvarId_736_, v_fvarId_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_);
lean_dec(v___y_741_);
lean_dec_ref(v___y_740_);
lean_dec(v___y_739_);
lean_dec_ref(v___y_738_);
return v_res_743_;
}
}
static lean_object* _init_l_Lean_MVarId_replaceLocalDecl___closed__0(void){
_start:
{
lean_object* v___x_744_; 
v___x_744_ = l_instMonadEIO(lean_box(0));
return v___x_744_;
}
}
static lean_object* _init_l_Lean_MVarId_replaceLocalDecl___closed__1(void){
_start:
{
lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_745_ = lean_obj_once(&l_Lean_MVarId_replaceLocalDecl___closed__0, &l_Lean_MVarId_replaceLocalDecl___closed__0_once, _init_l_Lean_MVarId_replaceLocalDecl___closed__0);
v___x_746_ = l_StateRefT_x27_instMonad___redArg(v___x_745_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceLocalDecl(lean_object* v_mvarId_751_, lean_object* v_fvarId_752_, lean_object* v_typeNew_753_, lean_object* v_eqProof_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_){
_start:
{
lean_object* v___x_760_; lean_object* v_toApplicative_761_; lean_object* v_toFunctor_762_; lean_object* v_toSeq_763_; lean_object* v_toSeqLeft_764_; lean_object* v_toSeqRight_765_; lean_object* v___f_766_; lean_object* v___f_767_; lean_object* v___f_768_; lean_object* v___f_769_; lean_object* v___x_770_; lean_object* v___f_771_; lean_object* v___f_772_; lean_object* v___f_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v_toApplicative_779_; lean_object* v_toFunctor_780_; lean_object* v_toSeq_781_; lean_object* v_toSeqLeft_782_; lean_object* v_toSeqRight_783_; lean_object* v___f_784_; lean_object* v___f_785_; lean_object* v___x_786_; lean_object* v___f_787_; lean_object* v___f_788_; lean_object* v___f_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v_toApplicative_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_824_; 
v___x_760_ = lean_obj_once(&l_Lean_MVarId_replaceLocalDecl___closed__1, &l_Lean_MVarId_replaceLocalDecl___closed__1_once, _init_l_Lean_MVarId_replaceLocalDecl___closed__1);
v_toApplicative_761_ = lean_ctor_get(v___x_760_, 0);
v_toFunctor_762_ = lean_ctor_get(v_toApplicative_761_, 0);
v_toSeq_763_ = lean_ctor_get(v_toApplicative_761_, 2);
v_toSeqLeft_764_ = lean_ctor_get(v_toApplicative_761_, 3);
v_toSeqRight_765_ = lean_ctor_get(v_toApplicative_761_, 4);
v___f_766_ = ((lean_object*)(l_Lean_MVarId_replaceLocalDecl___closed__2));
v___f_767_ = ((lean_object*)(l_Lean_MVarId_replaceLocalDecl___closed__3));
lean_inc_ref_n(v_toFunctor_762_, 2);
v___f_768_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_768_, 0, v_toFunctor_762_);
v___f_769_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_769_, 0, v_toFunctor_762_);
v___x_770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_770_, 0, v___f_768_);
lean_ctor_set(v___x_770_, 1, v___f_769_);
lean_inc(v_toSeqRight_765_);
v___f_771_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_771_, 0, v_toSeqRight_765_);
lean_inc(v_toSeqLeft_764_);
v___f_772_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_772_, 0, v_toSeqLeft_764_);
lean_inc(v_toSeq_763_);
v___f_773_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_773_, 0, v_toSeq_763_);
v___x_774_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_774_, 0, v___x_770_);
lean_ctor_set(v___x_774_, 1, v___f_766_);
lean_ctor_set(v___x_774_, 2, v___f_773_);
lean_ctor_set(v___x_774_, 3, v___f_772_);
lean_ctor_set(v___x_774_, 4, v___f_771_);
v___x_775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_775_, 0, v___x_774_);
lean_ctor_set(v___x_775_, 1, v___f_767_);
v___x_776_ = l_StateRefT_x27_instMonad___redArg(v___x_775_);
v___x_777_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(v___x_777_, 0, lean_box(0));
lean_closure_set(v___x_777_, 1, lean_box(0));
lean_closure_set(v___x_777_, 2, v___x_776_);
v___x_778_ = l_instMonadControlTOfPure___redArg(v___x_777_);
v_toApplicative_779_ = lean_ctor_get(v___x_760_, 0);
v_toFunctor_780_ = lean_ctor_get(v_toApplicative_779_, 0);
v_toSeq_781_ = lean_ctor_get(v_toApplicative_779_, 2);
v_toSeqLeft_782_ = lean_ctor_get(v_toApplicative_779_, 3);
v_toSeqRight_783_ = lean_ctor_get(v_toApplicative_779_, 4);
lean_inc_ref_n(v_toFunctor_780_, 2);
v___f_784_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_784_, 0, v_toFunctor_780_);
v___f_785_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_785_, 0, v_toFunctor_780_);
v___x_786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_786_, 0, v___f_784_);
lean_ctor_set(v___x_786_, 1, v___f_785_);
lean_inc(v_toSeqRight_783_);
v___f_787_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_787_, 0, v_toSeqRight_783_);
lean_inc(v_toSeqLeft_782_);
v___f_788_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_788_, 0, v_toSeqLeft_782_);
lean_inc(v_toSeq_781_);
v___f_789_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_789_, 0, v_toSeq_781_);
v___x_790_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_790_, 0, v___x_786_);
lean_ctor_set(v___x_790_, 1, v___f_766_);
lean_ctor_set(v___x_790_, 2, v___f_789_);
lean_ctor_set(v___x_790_, 3, v___f_788_);
lean_ctor_set(v___x_790_, 4, v___f_787_);
v___x_791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_791_, 0, v___x_790_);
lean_ctor_set(v___x_791_, 1, v___f_767_);
v___x_792_ = l_StateRefT_x27_instMonad___redArg(v___x_791_);
v_toApplicative_793_ = lean_ctor_get(v___x_792_, 0);
v_isSharedCheck_824_ = !lean_is_exclusive(v___x_792_);
if (v_isSharedCheck_824_ == 0)
{
lean_object* v_unused_825_; 
v_unused_825_ = lean_ctor_get(v___x_792_, 1);
lean_dec(v_unused_825_);
v___x_795_ = v___x_792_;
v_isShared_796_ = v_isSharedCheck_824_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_toApplicative_793_);
lean_dec(v___x_792_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_824_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v_toFunctor_797_; lean_object* v_toSeq_798_; lean_object* v_toSeqLeft_799_; lean_object* v_toSeqRight_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_822_; 
v_toFunctor_797_ = lean_ctor_get(v_toApplicative_793_, 0);
v_toSeq_798_ = lean_ctor_get(v_toApplicative_793_, 2);
v_toSeqLeft_799_ = lean_ctor_get(v_toApplicative_793_, 3);
v_toSeqRight_800_ = lean_ctor_get(v_toApplicative_793_, 4);
v_isSharedCheck_822_ = !lean_is_exclusive(v_toApplicative_793_);
if (v_isSharedCheck_822_ == 0)
{
lean_object* v_unused_823_; 
v_unused_823_ = lean_ctor_get(v_toApplicative_793_, 1);
lean_dec(v_unused_823_);
v___x_802_ = v_toApplicative_793_;
v_isShared_803_ = v_isSharedCheck_822_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_toSeqRight_800_);
lean_inc(v_toSeqLeft_799_);
lean_inc(v_toSeq_798_);
lean_inc(v_toFunctor_797_);
lean_dec(v_toApplicative_793_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_822_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___f_804_; lean_object* v___f_805_; lean_object* v___f_806_; lean_object* v___f_807_; lean_object* v___x_808_; lean_object* v___f_809_; lean_object* v___f_810_; lean_object* v___f_811_; lean_object* v___x_813_; 
v___f_804_ = ((lean_object*)(l_Lean_MVarId_replaceLocalDecl___closed__4));
v___f_805_ = ((lean_object*)(l_Lean_MVarId_replaceLocalDecl___closed__5));
lean_inc_ref(v_toFunctor_797_);
v___f_806_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_806_, 0, v_toFunctor_797_);
v___f_807_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_807_, 0, v_toFunctor_797_);
v___x_808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_808_, 0, v___f_806_);
lean_ctor_set(v___x_808_, 1, v___f_807_);
v___f_809_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_809_, 0, v_toSeqRight_800_);
v___f_810_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_810_, 0, v_toSeqLeft_799_);
v___f_811_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_811_, 0, v_toSeq_798_);
if (v_isShared_803_ == 0)
{
lean_ctor_set(v___x_802_, 4, v___f_809_);
lean_ctor_set(v___x_802_, 3, v___f_810_);
lean_ctor_set(v___x_802_, 2, v___f_811_);
lean_ctor_set(v___x_802_, 1, v___f_804_);
lean_ctor_set(v___x_802_, 0, v___x_808_);
v___x_813_ = v___x_802_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v___x_808_);
lean_ctor_set(v_reuseFailAlloc_821_, 1, v___f_804_);
lean_ctor_set(v_reuseFailAlloc_821_, 2, v___f_811_);
lean_ctor_set(v_reuseFailAlloc_821_, 3, v___f_810_);
lean_ctor_set(v_reuseFailAlloc_821_, 4, v___f_809_);
v___x_813_ = v_reuseFailAlloc_821_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
lean_object* v___x_815_; 
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 1, v___f_805_);
lean_ctor_set(v___x_795_, 0, v___x_813_);
v___x_815_ = v___x_795_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v___x_813_);
lean_ctor_set(v_reuseFailAlloc_820_, 1, v___f_805_);
v___x_815_ = v_reuseFailAlloc_820_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
lean_object* v___x_816_; lean_object* v___f_817_; lean_object* v___x_17__overap_818_; lean_object* v___x_819_; 
lean_inc(v_fvarId_752_);
v___x_816_ = l_Lean_mkFVar(v_fvarId_752_);
lean_inc(v_mvarId_751_);
v___f_817_ = lean_alloc_closure((void*)(l_Lean_MVarId_replaceLocalDecl___lam__0___boxed), 10, 5);
lean_closure_set(v___f_817_, 0, v_eqProof_754_);
lean_closure_set(v___f_817_, 1, v___x_816_);
lean_closure_set(v___f_817_, 2, v_typeNew_753_);
lean_closure_set(v___f_817_, 3, v_mvarId_751_);
lean_closure_set(v___f_817_, 4, v_fvarId_752_);
v___x_17__overap_818_ = l_Lean_MVarId_withContext___redArg(v___x_778_, v___x_815_, v_mvarId_751_, v___f_817_);
lean_inc(v_a_758_);
lean_inc_ref(v_a_757_);
lean_inc(v_a_756_);
lean_inc_ref(v_a_755_);
v___x_819_ = lean_apply_5(v___x_17__overap_818_, v_a_755_, v_a_756_, v_a_757_, v_a_758_, lean_box(0));
return v___x_819_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceLocalDecl___boxed(lean_object* v_mvarId_826_, lean_object* v_fvarId_827_, lean_object* v_typeNew_828_, lean_object* v_eqProof_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_){
_start:
{
lean_object* v_res_835_; 
v_res_835_ = l_Lean_MVarId_replaceLocalDecl(v_mvarId_826_, v_fvarId_827_, v_typeNew_828_, v_eqProof_829_, v_a_830_, v_a_831_, v_a_832_, v_a_833_);
lean_dec(v_a_833_);
lean_dec_ref(v_a_832_);
lean_dec(v_a_831_);
lean_dec_ref(v_a_830_);
return v_res_835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalInstances___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__0___redArg(lean_object* v_decls_836_, lean_object* v_x_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_){
_start:
{
lean_object* v___x_843_; 
v___x_843_ = l_Lean_Meta_withLocalInstancesImp___redArg(v_decls_836_, v_x_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_);
if (lean_obj_tag(v___x_843_) == 0)
{
lean_object* v_a_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_851_; 
v_a_844_ = lean_ctor_get(v___x_843_, 0);
v_isSharedCheck_851_ = !lean_is_exclusive(v___x_843_);
if (v_isSharedCheck_851_ == 0)
{
v___x_846_ = v___x_843_;
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_a_844_);
lean_dec(v___x_843_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_849_; 
if (v_isShared_847_ == 0)
{
v___x_849_ = v___x_846_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v_a_844_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
return v___x_849_;
}
}
}
else
{
lean_object* v_a_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_859_; 
v_a_852_ = lean_ctor_get(v___x_843_, 0);
v_isSharedCheck_859_ = !lean_is_exclusive(v___x_843_);
if (v_isSharedCheck_859_ == 0)
{
v___x_854_ = v___x_843_;
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_a_852_);
lean_dec(v___x_843_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___x_857_; 
if (v_isShared_855_ == 0)
{
v___x_857_ = v___x_854_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v_a_852_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalInstances___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__0___redArg___boxed(lean_object* v_decls_860_, lean_object* v_x_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_){
_start:
{
lean_object* v_res_867_; 
v_res_867_ = l_Lean_Meta_withLocalInstances___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__0___redArg(v_decls_860_, v_x_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_);
lean_dec(v___y_865_);
lean_dec_ref(v___y_864_);
lean_dec(v___y_863_);
lean_dec_ref(v___y_862_);
lean_dec(v_decls_860_);
return v_res_867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalInstances___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__0(lean_object* v_00_u03b1_868_, lean_object* v_decls_869_, lean_object* v_x_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_){
_start:
{
lean_object* v___x_876_; 
v___x_876_ = l_Lean_Meta_withLocalInstances___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__0___redArg(v_decls_869_, v_x_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_);
return v___x_876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalInstances___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__0___boxed(lean_object* v_00_u03b1_877_, lean_object* v_decls_878_, lean_object* v_x_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_){
_start:
{
lean_object* v_res_885_; 
v_res_885_ = l_Lean_Meta_withLocalInstances___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__0(v_00_u03b1_877_, v_decls_878_, v_x_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_);
lean_dec(v___y_883_);
lean_dec_ref(v___y_882_);
lean_dec(v___y_881_);
lean_dec_ref(v___y_880_);
lean_dec(v_decls_878_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__1___redArg(lean_object* v_lctx_886_, lean_object* v_x_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_){
_start:
{
lean_object* v_keyedConfig_893_; uint8_t v_trackZetaDelta_894_; lean_object* v_zetaDeltaSet_895_; lean_object* v_localInstances_896_; lean_object* v_defEqCtx_x3f_897_; lean_object* v_synthPendingDepth_898_; lean_object* v_customCanUnfoldPredicate_x3f_899_; uint8_t v_univApprox_900_; uint8_t v_inTypeClassResolution_901_; uint8_t v_cacheInferType_902_; lean_object* v___x_903_; lean_object* v___x_904_; 
v_keyedConfig_893_ = lean_ctor_get(v___y_888_, 0);
v_trackZetaDelta_894_ = lean_ctor_get_uint8(v___y_888_, sizeof(void*)*7);
v_zetaDeltaSet_895_ = lean_ctor_get(v___y_888_, 1);
v_localInstances_896_ = lean_ctor_get(v___y_888_, 3);
v_defEqCtx_x3f_897_ = lean_ctor_get(v___y_888_, 4);
v_synthPendingDepth_898_ = lean_ctor_get(v___y_888_, 5);
v_customCanUnfoldPredicate_x3f_899_ = lean_ctor_get(v___y_888_, 6);
v_univApprox_900_ = lean_ctor_get_uint8(v___y_888_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_901_ = lean_ctor_get_uint8(v___y_888_, sizeof(void*)*7 + 2);
v_cacheInferType_902_ = lean_ctor_get_uint8(v___y_888_, sizeof(void*)*7 + 3);
lean_inc(v_customCanUnfoldPredicate_x3f_899_);
lean_inc(v_synthPendingDepth_898_);
lean_inc(v_defEqCtx_x3f_897_);
lean_inc_ref(v_localInstances_896_);
lean_inc(v_zetaDeltaSet_895_);
lean_inc_ref(v_keyedConfig_893_);
v___x_903_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_903_, 0, v_keyedConfig_893_);
lean_ctor_set(v___x_903_, 1, v_zetaDeltaSet_895_);
lean_ctor_set(v___x_903_, 2, v_lctx_886_);
lean_ctor_set(v___x_903_, 3, v_localInstances_896_);
lean_ctor_set(v___x_903_, 4, v_defEqCtx_x3f_897_);
lean_ctor_set(v___x_903_, 5, v_synthPendingDepth_898_);
lean_ctor_set(v___x_903_, 6, v_customCanUnfoldPredicate_x3f_899_);
lean_ctor_set_uint8(v___x_903_, sizeof(void*)*7, v_trackZetaDelta_894_);
lean_ctor_set_uint8(v___x_903_, sizeof(void*)*7 + 1, v_univApprox_900_);
lean_ctor_set_uint8(v___x_903_, sizeof(void*)*7 + 2, v_inTypeClassResolution_901_);
lean_ctor_set_uint8(v___x_903_, sizeof(void*)*7 + 3, v_cacheInferType_902_);
lean_inc(v___y_891_);
lean_inc_ref(v___y_890_);
lean_inc(v___y_889_);
v___x_904_ = lean_apply_5(v_x_887_, v___x_903_, v___y_889_, v___y_890_, v___y_891_, lean_box(0));
return v___x_904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__1___redArg___boxed(lean_object* v_lctx_905_, lean_object* v_x_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_){
_start:
{
lean_object* v_res_912_; 
v_res_912_ = l_Lean_Meta_withLCtx_x27___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__1___redArg(v_lctx_905_, v_x_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_);
lean_dec(v___y_910_);
lean_dec_ref(v___y_909_);
lean_dec(v___y_908_);
lean_dec_ref(v___y_907_);
return v_res_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__1(lean_object* v_00_u03b1_913_, lean_object* v_lctx_914_, lean_object* v_x_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_){
_start:
{
lean_object* v___x_921_; 
v___x_921_ = l_Lean_Meta_withLCtx_x27___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__1___redArg(v_lctx_914_, v_x_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__1___boxed(lean_object* v_00_u03b1_922_, lean_object* v_lctx_923_, lean_object* v_x_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_){
_start:
{
lean_object* v_res_930_; 
v_res_930_ = l_Lean_Meta_withLCtx_x27___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__1(v_00_u03b1_922_, v_lctx_923_, v_x_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_);
lean_dec(v___y_928_);
lean_dec_ref(v___y_927_);
lean_dec(v___y_926_);
lean_dec_ref(v___y_925_);
return v_res_930_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_setFVarType___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2___redArg(lean_object* v_mvarId_931_, lean_object* v_fvarId_932_, lean_object* v_type_933_, lean_object* v___y_934_){
_start:
{
lean_object* v___x_936_; lean_object* v_mctx_937_; lean_object* v_cache_938_; lean_object* v_zetaDeltaFVarIds_939_; lean_object* v_postponed_940_; lean_object* v_diag_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_952_; 
v___x_936_ = lean_st_ref_take(v___y_934_);
v_mctx_937_ = lean_ctor_get(v___x_936_, 0);
v_cache_938_ = lean_ctor_get(v___x_936_, 1);
v_zetaDeltaFVarIds_939_ = lean_ctor_get(v___x_936_, 2);
v_postponed_940_ = lean_ctor_get(v___x_936_, 3);
v_diag_941_ = lean_ctor_get(v___x_936_, 4);
v_isSharedCheck_952_ = !lean_is_exclusive(v___x_936_);
if (v_isSharedCheck_952_ == 0)
{
v___x_943_ = v___x_936_;
v_isShared_944_ = v_isSharedCheck_952_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_diag_941_);
lean_inc(v_postponed_940_);
lean_inc(v_zetaDeltaFVarIds_939_);
lean_inc(v_cache_938_);
lean_inc(v_mctx_937_);
lean_dec(v___x_936_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_952_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v___x_945_; lean_object* v___x_947_; 
v___x_945_ = l_Lean_MetavarContext_setFVarType(v_mctx_937_, v_mvarId_931_, v_fvarId_932_, v_type_933_);
if (v_isShared_944_ == 0)
{
lean_ctor_set(v___x_943_, 0, v___x_945_);
v___x_947_ = v___x_943_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v___x_945_);
lean_ctor_set(v_reuseFailAlloc_951_, 1, v_cache_938_);
lean_ctor_set(v_reuseFailAlloc_951_, 2, v_zetaDeltaFVarIds_939_);
lean_ctor_set(v_reuseFailAlloc_951_, 3, v_postponed_940_);
lean_ctor_set(v_reuseFailAlloc_951_, 4, v_diag_941_);
v___x_947_ = v_reuseFailAlloc_951_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
v___x_948_ = lean_st_ref_put(v___y_934_, v___x_947_);
v___x_949_ = lean_box(0);
v___x_950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_950_, 0, v___x_949_);
return v___x_950_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_setFVarType___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2___redArg___boxed(lean_object* v_mvarId_953_, lean_object* v_fvarId_954_, lean_object* v_type_955_, lean_object* v___y_956_, lean_object* v___y_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l_Lean_MVarId_setFVarType___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2___redArg(v_mvarId_953_, v_fvarId_954_, v_type_955_, v___y_956_);
lean_dec(v___y_956_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_setFVarType___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2(lean_object* v_mvarId_959_, lean_object* v_fvarId_960_, lean_object* v_type_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_){
_start:
{
lean_object* v___x_967_; 
v___x_967_ = l_Lean_MVarId_setFVarType___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2___redArg(v_mvarId_959_, v_fvarId_960_, v_type_961_, v___y_963_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_setFVarType___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2___boxed(lean_object* v_mvarId_968_, lean_object* v_fvarId_969_, lean_object* v_type_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_){
_start:
{
lean_object* v_res_976_; 
v_res_976_ = l_Lean_MVarId_setFVarType___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2(v_mvarId_968_, v_fvarId_969_, v_type_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_);
lean_dec(v___y_974_);
lean_dec_ref(v___y_973_);
lean_dec(v___y_972_);
lean_dec_ref(v___y_971_);
return v_res_976_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceLocalDeclDefEq___lam__0(lean_object* v_mvarId_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_){
_start:
{
lean_object* v___x_983_; 
lean_inc(v_mvarId_977_);
v___x_983_ = l_Lean_MVarId_getDecl(v_mvarId_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_);
if (lean_obj_tag(v___x_983_) == 0)
{
lean_object* v_a_984_; lean_object* v_userName_985_; lean_object* v_type_986_; uint8_t v_kind_987_; lean_object* v___x_988_; lean_object* v___x_989_; 
v_a_984_ = lean_ctor_get(v___x_983_, 0);
lean_inc(v_a_984_);
lean_dec_ref_known(v___x_983_, 1);
v_userName_985_ = lean_ctor_get(v_a_984_, 0);
lean_inc(v_userName_985_);
v_type_986_ = lean_ctor_get(v_a_984_, 2);
lean_inc_ref(v_type_986_);
v_kind_987_ = lean_ctor_get_uint8(v_a_984_, sizeof(void*)*7);
lean_dec(v_a_984_);
v___x_988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_988_, 0, v_type_986_);
v___x_989_ = l_Lean_Meta_mkFreshExprMVar(v___x_988_, v_kind_987_, v_userName_985_, v___y_978_, v___y_979_, v___y_980_, v___y_981_);
if (lean_obj_tag(v___x_989_) == 0)
{
lean_object* v_a_990_; lean_object* v___x_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_999_; 
v_a_990_ = lean_ctor_get(v___x_989_, 0);
lean_inc_n(v_a_990_, 2);
lean_dec_ref_known(v___x_989_, 1);
v___x_991_ = l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0___redArg(v_mvarId_977_, v_a_990_, v___y_979_);
v_isSharedCheck_999_ = !lean_is_exclusive(v___x_991_);
if (v_isSharedCheck_999_ == 0)
{
lean_object* v_unused_1000_; 
v_unused_1000_ = lean_ctor_get(v___x_991_, 0);
lean_dec(v_unused_1000_);
v___x_993_ = v___x_991_;
v_isShared_994_ = v_isSharedCheck_999_;
goto v_resetjp_992_;
}
else
{
lean_dec(v___x_991_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_999_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_995_; lean_object* v___x_997_; 
v___x_995_ = l_Lean_Expr_mvarId_x21(v_a_990_);
lean_dec(v_a_990_);
if (v_isShared_994_ == 0)
{
lean_ctor_set(v___x_993_, 0, v___x_995_);
v___x_997_ = v___x_993_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v___x_995_);
v___x_997_ = v_reuseFailAlloc_998_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
return v___x_997_;
}
}
}
else
{
lean_object* v_a_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1008_; 
lean_dec(v_mvarId_977_);
v_a_1001_ = lean_ctor_get(v___x_989_, 0);
v_isSharedCheck_1008_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_1003_ = v___x_989_;
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_a_1001_);
lean_dec(v___x_989_);
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
lean_object* v_a_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1016_; 
lean_dec(v_mvarId_977_);
v_a_1009_ = lean_ctor_get(v___x_983_, 0);
v_isSharedCheck_1016_ = !lean_is_exclusive(v___x_983_);
if (v_isSharedCheck_1016_ == 0)
{
v___x_1011_ = v___x_983_;
v_isShared_1012_ = v_isSharedCheck_1016_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_a_1009_);
lean_dec(v___x_983_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceLocalDeclDefEq___lam__0___boxed(lean_object* v_mvarId_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_){
_start:
{
lean_object* v_res_1023_; 
v_res_1023_ = l_Lean_MVarId_replaceLocalDeclDefEq___lam__0(v_mvarId_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_);
lean_dec(v___y_1021_);
lean_dec_ref(v___y_1020_);
lean_dec(v___y_1019_);
lean_dec_ref(v___y_1018_);
return v_res_1023_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceLocalDeclDefEq___lam__1(lean_object* v_fvarId_1024_, lean_object* v_typeNew_1025_, lean_object* v___f_1026_, lean_object* v_mvarId_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_){
_start:
{
lean_object* v___x_1033_; 
lean_inc(v_fvarId_1024_);
v___x_1033_ = l_Lean_FVarId_getType___redArg(v_fvarId_1024_, v___y_1028_, v___y_1030_, v___y_1031_);
if (lean_obj_tag(v___x_1033_) == 0)
{
lean_object* v_a_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1063_; 
v_a_1034_ = lean_ctor_get(v___x_1033_, 0);
v_isSharedCheck_1063_ = !lean_is_exclusive(v___x_1033_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1036_ = v___x_1033_;
v_isShared_1037_ = v_isSharedCheck_1063_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_a_1034_);
lean_dec(v___x_1033_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1063_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
uint8_t v___x_1038_; 
v___x_1038_ = lean_expr_equal(v_a_1034_, v_typeNew_1025_);
if (v___x_1038_ == 0)
{
lean_object* v___x_1039_; lean_object* v_a_1040_; lean_object* v___x_1041_; lean_object* v_a_1042_; uint8_t v___x_1043_; 
lean_del_object(v___x_1036_);
v___x_1039_ = l_Lean_instantiateMVars___at___00Lean_MVarId_replaceTargetDefEq_spec__0___redArg(v_a_1034_, v___y_1029_);
v_a_1040_ = lean_ctor_get(v___x_1039_, 0);
lean_inc(v_a_1040_);
lean_dec_ref(v___x_1039_);
v___x_1041_ = l_Lean_instantiateMVars___at___00Lean_MVarId_replaceTargetDefEq_spec__0___redArg(v_typeNew_1025_, v___y_1029_);
v_a_1042_ = lean_ctor_get(v___x_1041_, 0);
lean_inc(v_a_1042_);
lean_dec_ref(v___x_1041_);
v___x_1043_ = lean_expr_equal(v_a_1040_, v_a_1042_);
if (v___x_1043_ == 0)
{
lean_object* v_lctx_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; 
lean_dec(v_a_1040_);
lean_dec(v_mvarId_1027_);
v_lctx_1044_ = lean_ctor_get(v___y_1028_, 2);
lean_inc(v_fvarId_1024_);
lean_inc_ref(v_lctx_1044_);
v___x_1045_ = l_Lean_LocalContext_setType(v_lctx_1044_, v_fvarId_1024_, v_a_1042_);
lean_inc_ref(v___x_1045_);
v___x_1046_ = l_Lean_LocalContext_get_x21(v___x_1045_, v_fvarId_1024_);
v___x_1047_ = lean_box(0);
v___x_1048_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1048_, 0, v___x_1046_);
lean_ctor_set(v___x_1048_, 1, v___x_1047_);
v___x_1049_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalInstances___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__0___boxed), 8, 3);
lean_closure_set(v___x_1049_, 0, lean_box(0));
lean_closure_set(v___x_1049_, 1, v___x_1048_);
lean_closure_set(v___x_1049_, 2, v___f_1026_);
v___x_1050_ = l_Lean_Meta_withLCtx_x27___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__1___redArg(v___x_1045_, v___x_1049_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_);
lean_dec_ref(v___y_1028_);
return v___x_1050_;
}
else
{
lean_object* v___x_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1058_; 
lean_dec(v_a_1042_);
lean_dec_ref(v___y_1028_);
lean_dec_ref(v___f_1026_);
lean_inc(v_mvarId_1027_);
v___x_1051_ = l_Lean_MVarId_setFVarType___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2___redArg(v_mvarId_1027_, v_fvarId_1024_, v_a_1040_, v___y_1029_);
v_isSharedCheck_1058_ = !lean_is_exclusive(v___x_1051_);
if (v_isSharedCheck_1058_ == 0)
{
lean_object* v_unused_1059_; 
v_unused_1059_ = lean_ctor_get(v___x_1051_, 0);
lean_dec(v_unused_1059_);
v___x_1053_ = v___x_1051_;
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
else
{
lean_dec(v___x_1051_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v___x_1056_; 
if (v_isShared_1054_ == 0)
{
lean_ctor_set(v___x_1053_, 0, v_mvarId_1027_);
v___x_1056_ = v___x_1053_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v_mvarId_1027_);
v___x_1056_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
return v___x_1056_;
}
}
}
}
else
{
lean_object* v___x_1061_; 
lean_dec(v_a_1034_);
lean_dec_ref(v___y_1028_);
lean_dec_ref(v___f_1026_);
lean_dec_ref(v_typeNew_1025_);
lean_dec(v_fvarId_1024_);
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 0, v_mvarId_1027_);
v___x_1061_ = v___x_1036_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_mvarId_1027_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
}
}
else
{
lean_object* v_a_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1071_; 
lean_dec_ref(v___y_1028_);
lean_dec(v_mvarId_1027_);
lean_dec_ref(v___f_1026_);
lean_dec_ref(v_typeNew_1025_);
lean_dec(v_fvarId_1024_);
v_a_1064_ = lean_ctor_get(v___x_1033_, 0);
v_isSharedCheck_1071_ = !lean_is_exclusive(v___x_1033_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_1066_ = v___x_1033_;
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_a_1064_);
lean_dec(v___x_1033_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1069_; 
if (v_isShared_1067_ == 0)
{
v___x_1069_ = v___x_1066_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v_a_1064_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
return v___x_1069_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceLocalDeclDefEq___lam__1___boxed(lean_object* v_fvarId_1072_, lean_object* v_typeNew_1073_, lean_object* v___f_1074_, lean_object* v_mvarId_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_){
_start:
{
lean_object* v_res_1081_; 
v_res_1081_ = l_Lean_MVarId_replaceLocalDeclDefEq___lam__1(v_fvarId_1072_, v_typeNew_1073_, v___f_1074_, v_mvarId_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_);
lean_dec(v___y_1079_);
lean_dec_ref(v___y_1078_);
lean_dec(v___y_1077_);
return v_res_1081_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceLocalDeclDefEq(lean_object* v_mvarId_1082_, lean_object* v_fvarId_1083_, lean_object* v_typeNew_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_){
_start:
{
lean_object* v___f_1090_; lean_object* v___f_1091_; lean_object* v___x_1092_; 
lean_inc_n(v_mvarId_1082_, 2);
v___f_1090_ = lean_alloc_closure((void*)(l_Lean_MVarId_replaceLocalDeclDefEq___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1090_, 0, v_mvarId_1082_);
v___f_1091_ = lean_alloc_closure((void*)(l_Lean_MVarId_replaceLocalDeclDefEq___lam__1___boxed), 9, 4);
lean_closure_set(v___f_1091_, 0, v_fvarId_1083_);
lean_closure_set(v___f_1091_, 1, v_typeNew_1084_);
lean_closure_set(v___f_1091_, 2, v___f_1090_);
lean_closure_set(v___f_1091_, 3, v_mvarId_1082_);
v___x_1092_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(v_mvarId_1082_, v___f_1091_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_);
return v___x_1092_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceLocalDeclDefEq___boxed(lean_object* v_mvarId_1093_, lean_object* v_fvarId_1094_, lean_object* v_typeNew_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_){
_start:
{
lean_object* v_res_1101_; 
v_res_1101_ = l_Lean_MVarId_replaceLocalDeclDefEq(v_mvarId_1093_, v_fvarId_1094_, v_typeNew_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_);
lean_dec(v_a_1099_);
lean_dec_ref(v_a_1098_);
lean_dec(v_a_1097_);
lean_dec_ref(v_a_1096_);
return v_res_1101_;
}
}
static lean_object* _init_l_Lean_MVarId_change___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1103_; lean_object* v___x_1104_; 
v___x_1103_ = ((lean_object*)(l_Lean_MVarId_change___lam__0___closed__0));
v___x_1104_ = l_Lean_stringToMessageData(v___x_1103_);
return v___x_1104_;
}
}
static lean_object* _init_l_Lean_MVarId_change___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1106_ = ((lean_object*)(l_Lean_MVarId_change___lam__0___closed__2));
v___x_1107_ = l_Lean_stringToMessageData(v___x_1106_);
return v___x_1107_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_change___lam__0(lean_object* v_mvarId_1108_, uint8_t v_checkDefEq_1109_, lean_object* v_targetNew_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_){
_start:
{
lean_object* v___x_1116_; 
lean_inc(v_mvarId_1108_);
v___x_1116_ = l_Lean_MVarId_getType(v_mvarId_1108_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_);
if (lean_obj_tag(v___x_1116_) == 0)
{
if (v_checkDefEq_1109_ == 0)
{
lean_object* v___x_1117_; 
lean_dec_ref_known(v___x_1116_, 1);
v___x_1117_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_1108_, v_targetNew_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_);
return v___x_1117_;
}
else
{
lean_object* v_a_1118_; lean_object* v___x_1119_; 
v_a_1118_ = lean_ctor_get(v___x_1116_, 0);
lean_inc_n(v_a_1118_, 2);
lean_dec_ref_known(v___x_1116_, 1);
lean_inc_ref(v_targetNew_1110_);
v___x_1119_ = l_Lean_Meta_isExprDefEq(v_a_1118_, v_targetNew_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_);
if (lean_obj_tag(v___x_1119_) == 0)
{
lean_object* v_a_1120_; uint8_t v___x_1121_; 
v_a_1120_ = lean_ctor_get(v___x_1119_, 0);
lean_inc(v_a_1120_);
lean_dec_ref_known(v___x_1119_, 1);
v___x_1121_ = lean_unbox(v_a_1120_);
lean_dec(v_a_1120_);
if (v___x_1121_ == 0)
{
lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; 
v___x_1122_ = ((lean_object*)(l_Lean_MVarId_replaceTargetDefEq___closed__1));
v___x_1123_ = lean_obj_once(&l_Lean_MVarId_change___lam__0___closed__1, &l_Lean_MVarId_change___lam__0___closed__1_once, _init_l_Lean_MVarId_change___lam__0___closed__1);
lean_inc_ref(v_targetNew_1110_);
v___x_1124_ = l_Lean_indentExpr(v_targetNew_1110_);
v___x_1125_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1125_, 0, v___x_1123_);
lean_ctor_set(v___x_1125_, 1, v___x_1124_);
v___x_1126_ = lean_obj_once(&l_Lean_MVarId_change___lam__0___closed__3, &l_Lean_MVarId_change___lam__0___closed__3_once, _init_l_Lean_MVarId_change___lam__0___closed__3);
v___x_1127_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1127_, 0, v___x_1125_);
lean_ctor_set(v___x_1127_, 1, v___x_1126_);
v___x_1128_ = l_Lean_indentExpr(v_a_1118_);
v___x_1129_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1129_, 0, v___x_1127_);
lean_ctor_set(v___x_1129_, 1, v___x_1128_);
v___x_1130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1130_, 0, v___x_1129_);
lean_inc(v_mvarId_1108_);
v___x_1131_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1122_, v_mvarId_1108_, v___x_1130_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_);
if (lean_obj_tag(v___x_1131_) == 0)
{
lean_object* v___x_1132_; 
lean_dec_ref_known(v___x_1131_, 1);
v___x_1132_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_1108_, v_targetNew_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_);
return v___x_1132_;
}
else
{
lean_object* v_a_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1140_; 
lean_dec_ref(v_targetNew_1110_);
lean_dec(v_mvarId_1108_);
v_a_1133_ = lean_ctor_get(v___x_1131_, 0);
v_isSharedCheck_1140_ = !lean_is_exclusive(v___x_1131_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1135_ = v___x_1131_;
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_a_1133_);
lean_dec(v___x_1131_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1138_; 
if (v_isShared_1136_ == 0)
{
v___x_1138_ = v___x_1135_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v_a_1133_);
v___x_1138_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
return v___x_1138_;
}
}
}
}
else
{
lean_object* v___x_1141_; 
lean_dec(v_a_1118_);
v___x_1141_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_1108_, v_targetNew_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_);
return v___x_1141_;
}
}
else
{
lean_object* v_a_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1149_; 
lean_dec(v_a_1118_);
lean_dec_ref(v_targetNew_1110_);
lean_dec(v_mvarId_1108_);
v_a_1142_ = lean_ctor_get(v___x_1119_, 0);
v_isSharedCheck_1149_ = !lean_is_exclusive(v___x_1119_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1144_ = v___x_1119_;
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_a_1142_);
lean_dec(v___x_1119_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v___x_1147_; 
if (v_isShared_1145_ == 0)
{
v___x_1147_ = v___x_1144_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_a_1142_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
return v___x_1147_;
}
}
}
}
}
else
{
lean_object* v_a_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1157_; 
lean_dec_ref(v_targetNew_1110_);
lean_dec(v_mvarId_1108_);
v_a_1150_ = lean_ctor_get(v___x_1116_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1116_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1152_ = v___x_1116_;
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_a_1150_);
lean_dec(v___x_1116_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1155_; 
if (v_isShared_1153_ == 0)
{
v___x_1155_ = v___x_1152_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v_a_1150_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_change___lam__0___boxed(lean_object* v_mvarId_1158_, lean_object* v_checkDefEq_1159_, lean_object* v_targetNew_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_){
_start:
{
uint8_t v_checkDefEq_boxed_1166_; lean_object* v_res_1167_; 
v_checkDefEq_boxed_1166_ = lean_unbox(v_checkDefEq_1159_);
v_res_1167_ = l_Lean_MVarId_change___lam__0(v_mvarId_1158_, v_checkDefEq_boxed_1166_, v_targetNew_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_);
lean_dec(v___y_1164_);
lean_dec_ref(v___y_1163_);
lean_dec(v___y_1162_);
lean_dec_ref(v___y_1161_);
return v_res_1167_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_change(lean_object* v_mvarId_1168_, lean_object* v_targetNew_1169_, uint8_t v_checkDefEq_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_){
_start:
{
lean_object* v___x_1176_; lean_object* v___f_1177_; lean_object* v___x_1178_; 
v___x_1176_ = lean_box(v_checkDefEq_1170_);
lean_inc(v_mvarId_1168_);
v___f_1177_ = lean_alloc_closure((void*)(l_Lean_MVarId_change___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1177_, 0, v_mvarId_1168_);
lean_closure_set(v___f_1177_, 1, v___x_1176_);
lean_closure_set(v___f_1177_, 2, v_targetNew_1169_);
v___x_1178_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(v_mvarId_1168_, v___f_1177_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_change___boxed(lean_object* v_mvarId_1179_, lean_object* v_targetNew_1180_, lean_object* v_checkDefEq_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_){
_start:
{
uint8_t v_checkDefEq_boxed_1187_; lean_object* v_res_1188_; 
v_checkDefEq_boxed_1187_ = lean_unbox(v_checkDefEq_1181_);
v_res_1188_ = l_Lean_MVarId_change(v_mvarId_1179_, v_targetNew_1180_, v_checkDefEq_boxed_1187_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_);
lean_dec(v_a_1185_);
lean_dec_ref(v_a_1184_);
lean_dec(v_a_1183_);
lean_dec_ref(v_a_1182_);
return v_res_1188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0_spec__0___redArg(lean_object* v_t_1189_, lean_object* v___y_1190_){
_start:
{
lean_object* v___x_1192_; lean_object* v_infoState_1193_; uint8_t v_enabled_1194_; 
v___x_1192_ = lean_st_ref_get(v___y_1190_);
v_infoState_1193_ = lean_ctor_get(v___x_1192_, 7);
lean_inc_ref(v_infoState_1193_);
lean_dec(v___x_1192_);
v_enabled_1194_ = lean_ctor_get_uint8(v_infoState_1193_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1193_);
if (v_enabled_1194_ == 0)
{
lean_object* v___x_1195_; lean_object* v___x_1196_; 
lean_dec_ref(v_t_1189_);
v___x_1195_ = lean_box(0);
v___x_1196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1196_, 0, v___x_1195_);
return v___x_1196_;
}
else
{
lean_object* v___x_1197_; lean_object* v_infoState_1198_; lean_object* v_env_1199_; lean_object* v_nextMacroScope_1200_; lean_object* v_ngen_1201_; lean_object* v_auxDeclNGen_1202_; lean_object* v_traceState_1203_; lean_object* v_cache_1204_; lean_object* v_messages_1205_; lean_object* v_snapshotTasks_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1228_; 
v___x_1197_ = lean_st_ref_take(v___y_1190_);
v_infoState_1198_ = lean_ctor_get(v___x_1197_, 7);
v_env_1199_ = lean_ctor_get(v___x_1197_, 0);
v_nextMacroScope_1200_ = lean_ctor_get(v___x_1197_, 1);
v_ngen_1201_ = lean_ctor_get(v___x_1197_, 2);
v_auxDeclNGen_1202_ = lean_ctor_get(v___x_1197_, 3);
v_traceState_1203_ = lean_ctor_get(v___x_1197_, 4);
v_cache_1204_ = lean_ctor_get(v___x_1197_, 5);
v_messages_1205_ = lean_ctor_get(v___x_1197_, 6);
v_snapshotTasks_1206_ = lean_ctor_get(v___x_1197_, 8);
v_isSharedCheck_1228_ = !lean_is_exclusive(v___x_1197_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1208_ = v___x_1197_;
v_isShared_1209_ = v_isSharedCheck_1228_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_snapshotTasks_1206_);
lean_inc(v_infoState_1198_);
lean_inc(v_messages_1205_);
lean_inc(v_cache_1204_);
lean_inc(v_traceState_1203_);
lean_inc(v_auxDeclNGen_1202_);
lean_inc(v_ngen_1201_);
lean_inc(v_nextMacroScope_1200_);
lean_inc(v_env_1199_);
lean_dec(v___x_1197_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1228_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
uint8_t v_enabled_1210_; lean_object* v_assignment_1211_; lean_object* v_lazyAssignment_1212_; lean_object* v_trees_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1227_; 
v_enabled_1210_ = lean_ctor_get_uint8(v_infoState_1198_, sizeof(void*)*3);
v_assignment_1211_ = lean_ctor_get(v_infoState_1198_, 0);
v_lazyAssignment_1212_ = lean_ctor_get(v_infoState_1198_, 1);
v_trees_1213_ = lean_ctor_get(v_infoState_1198_, 2);
v_isSharedCheck_1227_ = !lean_is_exclusive(v_infoState_1198_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1215_ = v_infoState_1198_;
v_isShared_1216_ = v_isSharedCheck_1227_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_trees_1213_);
lean_inc(v_lazyAssignment_1212_);
lean_inc(v_assignment_1211_);
lean_dec(v_infoState_1198_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1227_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v___x_1217_; lean_object* v___x_1219_; 
v___x_1217_ = l_Lean_PersistentArray_push___redArg(v_trees_1213_, v_t_1189_);
if (v_isShared_1216_ == 0)
{
lean_ctor_set(v___x_1215_, 2, v___x_1217_);
v___x_1219_ = v___x_1215_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v_assignment_1211_);
lean_ctor_set(v_reuseFailAlloc_1226_, 1, v_lazyAssignment_1212_);
lean_ctor_set(v_reuseFailAlloc_1226_, 2, v___x_1217_);
lean_ctor_set_uint8(v_reuseFailAlloc_1226_, sizeof(void*)*3, v_enabled_1210_);
v___x_1219_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
lean_object* v___x_1221_; 
if (v_isShared_1209_ == 0)
{
lean_ctor_set(v___x_1208_, 7, v___x_1219_);
v___x_1221_ = v___x_1208_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v_env_1199_);
lean_ctor_set(v_reuseFailAlloc_1225_, 1, v_nextMacroScope_1200_);
lean_ctor_set(v_reuseFailAlloc_1225_, 2, v_ngen_1201_);
lean_ctor_set(v_reuseFailAlloc_1225_, 3, v_auxDeclNGen_1202_);
lean_ctor_set(v_reuseFailAlloc_1225_, 4, v_traceState_1203_);
lean_ctor_set(v_reuseFailAlloc_1225_, 5, v_cache_1204_);
lean_ctor_set(v_reuseFailAlloc_1225_, 6, v_messages_1205_);
lean_ctor_set(v_reuseFailAlloc_1225_, 7, v___x_1219_);
lean_ctor_set(v_reuseFailAlloc_1225_, 8, v_snapshotTasks_1206_);
v___x_1221_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___x_1222_ = lean_st_ref_put(v___y_1190_, v___x_1221_);
v___x_1223_ = lean_box(0);
v___x_1224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1223_);
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
v_infoState_1249_ = lean_ctor_get(v___x_1248_, 7);
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
size_t v_sz_boxed_1374_; size_t v___x_3386__boxed_1375_; lean_object* v_res_1376_; 
v_sz_boxed_1374_ = lean_unbox_usize(v_sz_1366_);
lean_dec(v_sz_1366_);
v___x_3386__boxed_1375_ = lean_unbox_usize(v___x_1367_);
lean_dec(v___x_1367_);
v_res_1376_ = l_Lean_MVarId_withReverted___redArg___lam__0(v_fst_1365_, v_sz_boxed_1374_, v___x_3386__boxed_1375_, v___x_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_);
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
lean_object* v___x_1839_; lean_object* v___x_1840_; 
v___x_1839_ = ((lean_object*)(l_Lean_MVarId_changeLocalDecl___closed__1));
lean_inc(v_mvarId_1830_);
v___x_1840_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_1830_, v___x_1839_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_);
if (lean_obj_tag(v___x_1840_) == 0)
{
lean_object* v___x_1841_; lean_object* v___f_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; uint8_t v___x_1846_; lean_object* v___x_1847_; 
lean_dec_ref_known(v___x_1840_, 1);
v___x_1841_ = lean_box(v_checkDefEq_1833_);
v___f_1842_ = lean_alloc_closure((void*)(l_Lean_MVarId_changeLocalDecl___lam__3___boxed), 10, 3);
lean_closure_set(v___f_1842_, 0, v___x_1841_);
lean_closure_set(v___f_1842_, 1, v_typeNew_1832_);
lean_closure_set(v___f_1842_, 2, v___x_1839_);
v___x_1843_ = lean_unsigned_to_nat(1u);
v___x_1844_ = lean_mk_empty_array_with_capacity(v___x_1843_);
v___x_1845_ = lean_array_push(v___x_1844_, v_fvarId_1831_);
v___x_1846_ = 0;
v___x_1847_ = l_Lean_MVarId_withReverted___redArg(v_mvarId_1830_, v___x_1845_, v___f_1842_, v___x_1846_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_);
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
lean_dec_ref(v_typeNew_1832_);
lean_dec(v_fvarId_1831_);
lean_dec(v_mvarId_1830_);
v_a_1865_ = lean_ctor_get(v___x_1840_, 0);
v_isSharedCheck_1872_ = !lean_is_exclusive(v___x_1840_);
if (v_isSharedCheck_1872_ == 0)
{
v___x_1867_ = v___x_1840_;
v_isShared_1868_ = v_isSharedCheck_1872_;
goto v_resetjp_1866_;
}
else
{
lean_inc(v_a_1865_);
lean_dec(v___x_1840_);
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
