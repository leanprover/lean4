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
size_t v_x_1698__boxed_198_; size_t v_x_1699__boxed_199_; lean_object* v_res_200_; 
v_x_1698__boxed_198_ = lean_unbox_usize(v_x_194_);
lean_dec(v_x_194_);
v_x_1699__boxed_199_ = lean_unbox_usize(v_x_195_);
lean_dec(v_x_195_);
v_res_200_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg(v_x_193_, v_x_1698__boxed_198_, v_x_1699__boxed_199_, v_x_196_, v_x_197_);
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
lean_object* v___x_212_; lean_object* v_mctx_213_; lean_object* v_cache_214_; lean_object* v_zetaDeltaFVarIds_215_; lean_object* v_postponed_216_; lean_object* v_diag_217_; lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_245_; 
v___x_212_ = lean_st_ref_take(v___y_210_);
v_mctx_213_ = lean_ctor_get(v___x_212_, 0);
v_cache_214_ = lean_ctor_get(v___x_212_, 1);
v_zetaDeltaFVarIds_215_ = lean_ctor_get(v___x_212_, 2);
v_postponed_216_ = lean_ctor_get(v___x_212_, 3);
v_diag_217_ = lean_ctor_get(v___x_212_, 4);
v_isSharedCheck_245_ = !lean_is_exclusive(v___x_212_);
if (v_isSharedCheck_245_ == 0)
{
v___x_219_ = v___x_212_;
v_isShared_220_ = v_isSharedCheck_245_;
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
v_isShared_220_ = v_isSharedCheck_245_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
lean_object* v_depth_221_; lean_object* v_levelAssignDepth_222_; lean_object* v_lmvarCounter_223_; lean_object* v_mvarCounter_224_; lean_object* v_lDecls_225_; lean_object* v_decls_226_; lean_object* v_userNames_227_; lean_object* v_lAssignment_228_; lean_object* v_eAssignment_229_; lean_object* v_dAssignment_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_244_; 
v_depth_221_ = lean_ctor_get(v_mctx_213_, 0);
v_levelAssignDepth_222_ = lean_ctor_get(v_mctx_213_, 1);
v_lmvarCounter_223_ = lean_ctor_get(v_mctx_213_, 2);
v_mvarCounter_224_ = lean_ctor_get(v_mctx_213_, 3);
v_lDecls_225_ = lean_ctor_get(v_mctx_213_, 4);
v_decls_226_ = lean_ctor_get(v_mctx_213_, 5);
v_userNames_227_ = lean_ctor_get(v_mctx_213_, 6);
v_lAssignment_228_ = lean_ctor_get(v_mctx_213_, 7);
v_eAssignment_229_ = lean_ctor_get(v_mctx_213_, 8);
v_dAssignment_230_ = lean_ctor_get(v_mctx_213_, 9);
v_isSharedCheck_244_ = !lean_is_exclusive(v_mctx_213_);
if (v_isSharedCheck_244_ == 0)
{
v___x_232_ = v_mctx_213_;
v_isShared_233_ = v_isSharedCheck_244_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_dAssignment_230_);
lean_inc(v_eAssignment_229_);
lean_inc(v_lAssignment_228_);
lean_inc(v_userNames_227_);
lean_inc(v_decls_226_);
lean_inc(v_lDecls_225_);
lean_inc(v_mvarCounter_224_);
lean_inc(v_lmvarCounter_223_);
lean_inc(v_levelAssignDepth_222_);
lean_inc(v_depth_221_);
lean_dec(v_mctx_213_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_244_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
lean_object* v___x_234_; lean_object* v___x_236_; 
v___x_234_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0___redArg(v_eAssignment_229_, v_mvarId_208_, v_val_209_);
if (v_isShared_233_ == 0)
{
lean_ctor_set(v___x_232_, 8, v___x_234_);
v___x_236_ = v___x_232_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v_depth_221_);
lean_ctor_set(v_reuseFailAlloc_243_, 1, v_levelAssignDepth_222_);
lean_ctor_set(v_reuseFailAlloc_243_, 2, v_lmvarCounter_223_);
lean_ctor_set(v_reuseFailAlloc_243_, 3, v_mvarCounter_224_);
lean_ctor_set(v_reuseFailAlloc_243_, 4, v_lDecls_225_);
lean_ctor_set(v_reuseFailAlloc_243_, 5, v_decls_226_);
lean_ctor_set(v_reuseFailAlloc_243_, 6, v_userNames_227_);
lean_ctor_set(v_reuseFailAlloc_243_, 7, v_lAssignment_228_);
lean_ctor_set(v_reuseFailAlloc_243_, 8, v___x_234_);
lean_ctor_set(v_reuseFailAlloc_243_, 9, v_dAssignment_230_);
v___x_236_ = v_reuseFailAlloc_243_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
lean_object* v___x_238_; 
if (v_isShared_220_ == 0)
{
lean_ctor_set(v___x_219_, 0, v___x_236_);
v___x_238_ = v___x_219_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v___x_236_);
lean_ctor_set(v_reuseFailAlloc_242_, 1, v_cache_214_);
lean_ctor_set(v_reuseFailAlloc_242_, 2, v_zetaDeltaFVarIds_215_);
lean_ctor_set(v_reuseFailAlloc_242_, 3, v_postponed_216_);
lean_ctor_set(v_reuseFailAlloc_242_, 4, v_diag_217_);
v___x_238_ = v_reuseFailAlloc_242_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_239_ = lean_st_ref_set(v___y_210_, v___x_238_);
v___x_240_ = lean_box(0);
v___x_241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_241_, 0, v___x_240_);
return v___x_241_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0___redArg___boxed(lean_object* v_mvarId_246_, lean_object* v_val_247_, lean_object* v___y_248_, lean_object* v___y_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0___redArg(v_mvarId_246_, v_val_247_, v___y_248_);
lean_dec(v___y_248_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetEq___lam__0(lean_object* v_mvarId_256_, lean_object* v___x_257_, lean_object* v_targetNew_258_, lean_object* v_eqProof_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_){
_start:
{
lean_object* v___x_265_; 
lean_inc(v_mvarId_256_);
v___x_265_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_256_, v___x_257_, v___y_260_, v___y_261_, v___y_262_, v___y_263_);
if (lean_obj_tag(v___x_265_) == 0)
{
lean_object* v___x_266_; 
lean_dec_ref(v___x_265_);
lean_inc(v_mvarId_256_);
v___x_266_ = l_Lean_MVarId_getTag(v_mvarId_256_, v___y_260_, v___y_261_, v___y_262_, v___y_263_);
if (lean_obj_tag(v___x_266_) == 0)
{
lean_object* v_a_267_; lean_object* v___x_268_; 
v_a_267_ = lean_ctor_get(v___x_266_, 0);
lean_inc(v_a_267_);
lean_dec_ref(v___x_266_);
lean_inc_ref(v_targetNew_258_);
v___x_268_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_targetNew_258_, v_a_267_, v___y_260_, v___y_261_, v___y_262_, v___y_263_);
if (lean_obj_tag(v___x_268_) == 0)
{
lean_object* v_a_269_; lean_object* v___x_270_; 
v_a_269_ = lean_ctor_get(v___x_268_, 0);
lean_inc(v_a_269_);
lean_dec_ref(v___x_268_);
lean_inc(v_mvarId_256_);
v___x_270_ = l_Lean_MVarId_getType(v_mvarId_256_, v___y_260_, v___y_261_, v___y_262_, v___y_263_);
if (lean_obj_tag(v___x_270_) == 0)
{
lean_object* v_a_271_; lean_object* v___x_272_; 
v_a_271_ = lean_ctor_get(v___x_270_, 0);
lean_inc_n(v_a_271_, 2);
lean_dec_ref(v___x_270_);
v___x_272_ = l_Lean_Meta_getLevel(v_a_271_, v___y_260_, v___y_261_, v___y_262_, v___y_263_);
if (lean_obj_tag(v___x_272_) == 0)
{
lean_object* v_a_273_; lean_object* v___x_274_; 
v_a_273_ = lean_ctor_get(v___x_272_, 0);
lean_inc(v_a_273_);
lean_dec_ref(v___x_272_);
lean_inc_ref(v_targetNew_258_);
lean_inc(v_a_271_);
v___x_274_ = l_Lean_Meta_mkEq(v_a_271_, v_targetNew_258_, v___y_260_, v___y_261_, v___y_262_, v___y_263_);
if (lean_obj_tag(v___x_274_) == 0)
{
lean_object* v_a_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_296_; 
v_a_275_ = lean_ctor_get(v___x_274_, 0);
lean_inc(v_a_275_);
lean_dec_ref(v___x_274_);
v___x_276_ = l_Lean_Meta_mkExpectedPropHint(v_eqProof_259_, v_a_275_);
v___x_277_ = ((lean_object*)(l_Lean_MVarId_replaceTargetEq___lam__0___closed__2));
v___x_278_ = lean_box(0);
v___x_279_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_279_, 0, v_a_273_);
lean_ctor_set(v___x_279_, 1, v___x_278_);
v___x_280_ = l_Lean_mkConst(v___x_277_, v___x_279_);
v___x_281_ = lean_unsigned_to_nat(4u);
v___x_282_ = lean_mk_empty_array_with_capacity(v___x_281_);
v___x_283_ = lean_array_push(v___x_282_, v_a_271_);
v___x_284_ = lean_array_push(v___x_283_, v_targetNew_258_);
v___x_285_ = lean_array_push(v___x_284_, v___x_276_);
lean_inc(v_a_269_);
v___x_286_ = lean_array_push(v___x_285_, v_a_269_);
v___x_287_ = l_Lean_mkAppN(v___x_280_, v___x_286_);
lean_dec_ref(v___x_286_);
v___x_288_ = l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0___redArg(v_mvarId_256_, v___x_287_, v___y_261_);
v_isSharedCheck_296_ = !lean_is_exclusive(v___x_288_);
if (v_isSharedCheck_296_ == 0)
{
lean_object* v_unused_297_; 
v_unused_297_ = lean_ctor_get(v___x_288_, 0);
lean_dec(v_unused_297_);
v___x_290_ = v___x_288_;
v_isShared_291_ = v_isSharedCheck_296_;
goto v_resetjp_289_;
}
else
{
lean_dec(v___x_288_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_296_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
lean_object* v___x_292_; lean_object* v___x_294_; 
v___x_292_ = l_Lean_Expr_mvarId_x21(v_a_269_);
lean_dec(v_a_269_);
if (v_isShared_291_ == 0)
{
lean_ctor_set(v___x_290_, 0, v___x_292_);
v___x_294_ = v___x_290_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v___x_292_);
v___x_294_ = v_reuseFailAlloc_295_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
return v___x_294_;
}
}
}
else
{
lean_object* v_a_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_305_; 
lean_dec(v_a_273_);
lean_dec(v_a_271_);
lean_dec(v_a_269_);
lean_dec_ref(v_eqProof_259_);
lean_dec_ref(v_targetNew_258_);
lean_dec(v_mvarId_256_);
v_a_298_ = lean_ctor_get(v___x_274_, 0);
v_isSharedCheck_305_ = !lean_is_exclusive(v___x_274_);
if (v_isSharedCheck_305_ == 0)
{
v___x_300_ = v___x_274_;
v_isShared_301_ = v_isSharedCheck_305_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_a_298_);
lean_dec(v___x_274_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_305_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v___x_303_; 
if (v_isShared_301_ == 0)
{
v___x_303_ = v___x_300_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v_a_298_);
v___x_303_ = v_reuseFailAlloc_304_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
return v___x_303_;
}
}
}
}
else
{
lean_object* v_a_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_313_; 
lean_dec(v_a_271_);
lean_dec(v_a_269_);
lean_dec_ref(v_eqProof_259_);
lean_dec_ref(v_targetNew_258_);
lean_dec(v_mvarId_256_);
v_a_306_ = lean_ctor_get(v___x_272_, 0);
v_isSharedCheck_313_ = !lean_is_exclusive(v___x_272_);
if (v_isSharedCheck_313_ == 0)
{
v___x_308_ = v___x_272_;
v_isShared_309_ = v_isSharedCheck_313_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_a_306_);
lean_dec(v___x_272_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_313_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v___x_311_; 
if (v_isShared_309_ == 0)
{
v___x_311_ = v___x_308_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v_a_306_);
v___x_311_ = v_reuseFailAlloc_312_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
return v___x_311_;
}
}
}
}
else
{
lean_object* v_a_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_321_; 
lean_dec(v_a_269_);
lean_dec_ref(v_eqProof_259_);
lean_dec_ref(v_targetNew_258_);
lean_dec(v_mvarId_256_);
v_a_314_ = lean_ctor_get(v___x_270_, 0);
v_isSharedCheck_321_ = !lean_is_exclusive(v___x_270_);
if (v_isSharedCheck_321_ == 0)
{
v___x_316_ = v___x_270_;
v_isShared_317_ = v_isSharedCheck_321_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_a_314_);
lean_dec(v___x_270_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_321_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
lean_object* v___x_319_; 
if (v_isShared_317_ == 0)
{
v___x_319_ = v___x_316_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v_a_314_);
v___x_319_ = v_reuseFailAlloc_320_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
return v___x_319_;
}
}
}
}
else
{
lean_object* v_a_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_329_; 
lean_dec_ref(v_eqProof_259_);
lean_dec_ref(v_targetNew_258_);
lean_dec(v_mvarId_256_);
v_a_322_ = lean_ctor_get(v___x_268_, 0);
v_isSharedCheck_329_ = !lean_is_exclusive(v___x_268_);
if (v_isSharedCheck_329_ == 0)
{
v___x_324_ = v___x_268_;
v_isShared_325_ = v_isSharedCheck_329_;
goto v_resetjp_323_;
}
else
{
lean_inc(v_a_322_);
lean_dec(v___x_268_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_329_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
lean_object* v___x_327_; 
if (v_isShared_325_ == 0)
{
v___x_327_ = v___x_324_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v_a_322_);
v___x_327_ = v_reuseFailAlloc_328_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
return v___x_327_;
}
}
}
}
else
{
lean_object* v_a_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_337_; 
lean_dec_ref(v_eqProof_259_);
lean_dec_ref(v_targetNew_258_);
lean_dec(v_mvarId_256_);
v_a_330_ = lean_ctor_get(v___x_266_, 0);
v_isSharedCheck_337_ = !lean_is_exclusive(v___x_266_);
if (v_isSharedCheck_337_ == 0)
{
v___x_332_ = v___x_266_;
v_isShared_333_ = v_isSharedCheck_337_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_a_330_);
lean_dec(v___x_266_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_337_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v___x_335_; 
if (v_isShared_333_ == 0)
{
v___x_335_ = v___x_332_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v_a_330_);
v___x_335_ = v_reuseFailAlloc_336_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
return v___x_335_;
}
}
}
}
else
{
lean_object* v_a_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_345_; 
lean_dec_ref(v_eqProof_259_);
lean_dec_ref(v_targetNew_258_);
lean_dec(v_mvarId_256_);
v_a_338_ = lean_ctor_get(v___x_265_, 0);
v_isSharedCheck_345_ = !lean_is_exclusive(v___x_265_);
if (v_isSharedCheck_345_ == 0)
{
v___x_340_ = v___x_265_;
v_isShared_341_ = v_isSharedCheck_345_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_a_338_);
lean_dec(v___x_265_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_345_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v___x_343_; 
if (v_isShared_341_ == 0)
{
v___x_343_ = v___x_340_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v_a_338_);
v___x_343_ = v_reuseFailAlloc_344_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
return v___x_343_;
}
}
}
}
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
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetEq(lean_object* v_mvarId_359_, lean_object* v_targetNew_360_, lean_object* v_eqProof_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_){
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
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetEq___boxed(lean_object* v_mvarId_370_, lean_object* v_targetNew_371_, lean_object* v_eqProof_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l_Lean_MVarId_replaceTargetEq(v_mvarId_370_, v_targetNew_371_, v_eqProof_372_, v_a_373_, v_a_374_, v_a_375_, v_a_376_);
lean_dec(v_a_376_);
lean_dec_ref(v_a_375_);
lean_dec(v_a_374_);
lean_dec_ref(v_a_373_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0(lean_object* v_mvarId_379_, lean_object* v_val_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_){
_start:
{
lean_object* v___x_386_; 
v___x_386_ = l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0___redArg(v_mvarId_379_, v_val_380_, v___y_382_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0___boxed(lean_object* v_mvarId_387_, lean_object* v_val_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0(v_mvarId_387_, v_val_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_);
lean_dec(v___y_392_);
lean_dec_ref(v___y_391_);
lean_dec(v___y_390_);
lean_dec_ref(v___y_389_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0(lean_object* v_00_u03b2_395_, lean_object* v_x_396_, lean_object* v_x_397_, lean_object* v_x_398_){
_start:
{
lean_object* v___x_399_; 
v___x_399_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0___redArg(v_x_396_, v_x_397_, v_x_398_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_400_, lean_object* v_x_401_, size_t v_x_402_, size_t v_x_403_, lean_object* v_x_404_, lean_object* v_x_405_){
_start:
{
lean_object* v___x_406_; 
v___x_406_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg(v_x_401_, v_x_402_, v_x_403_, v_x_404_, v_x_405_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_407_, lean_object* v_x_408_, lean_object* v_x_409_, lean_object* v_x_410_, lean_object* v_x_411_, lean_object* v_x_412_){
_start:
{
size_t v_x_2159__boxed_413_; size_t v_x_2160__boxed_414_; lean_object* v_res_415_; 
v_x_2159__boxed_413_ = lean_unbox_usize(v_x_409_);
lean_dec(v_x_409_);
v_x_2160__boxed_414_ = lean_unbox_usize(v_x_410_);
lean_dec(v_x_410_);
v_res_415_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2(v_00_u03b2_407_, v_x_408_, v_x_2159__boxed_413_, v_x_2160__boxed_414_, v_x_411_, v_x_412_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_416_, lean_object* v_n_417_, lean_object* v_k_418_, lean_object* v_v_419_){
_start:
{
lean_object* v___x_420_; 
v___x_420_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__3___redArg(v_n_417_, v_k_418_, v_v_419_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_421_, size_t v_depth_422_, lean_object* v_keys_423_, lean_object* v_vals_424_, lean_object* v_heq_425_, lean_object* v_i_426_, lean_object* v_entries_427_){
_start:
{
lean_object* v___x_428_; 
v___x_428_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_422_, v_keys_423_, v_vals_424_, v_i_426_, v_entries_427_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03b2_429_, lean_object* v_depth_430_, lean_object* v_keys_431_, lean_object* v_vals_432_, lean_object* v_heq_433_, lean_object* v_i_434_, lean_object* v_entries_435_){
_start:
{
size_t v_depth_boxed_436_; lean_object* v_res_437_; 
v_depth_boxed_436_ = lean_unbox_usize(v_depth_430_);
lean_dec(v_depth_430_);
v_res_437_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__4(v_00_u03b2_429_, v_depth_boxed_436_, v_keys_431_, v_vals_432_, v_heq_433_, v_i_434_, v_entries_435_);
lean_dec_ref(v_vals_432_);
lean_dec_ref(v_keys_431_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_438_, lean_object* v_x_439_, lean_object* v_x_440_, lean_object* v_x_441_, lean_object* v_x_442_){
_start:
{
lean_object* v___x_443_; 
v___x_443_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v_x_439_, v_x_440_, v_x_441_, v_x_442_);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_replaceTargetDefEq_spec__0___redArg(lean_object* v_e_444_, lean_object* v___y_445_){
_start:
{
uint8_t v___x_447_; 
v___x_447_ = l_Lean_Expr_hasMVar(v_e_444_);
if (v___x_447_ == 0)
{
lean_object* v___x_448_; 
v___x_448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_448_, 0, v_e_444_);
return v___x_448_;
}
else
{
lean_object* v___x_449_; lean_object* v_mctx_450_; lean_object* v___x_451_; lean_object* v_fst_452_; lean_object* v_snd_453_; lean_object* v___x_454_; lean_object* v_cache_455_; lean_object* v_zetaDeltaFVarIds_456_; lean_object* v_postponed_457_; lean_object* v_diag_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_467_; 
v___x_449_ = lean_st_ref_get(v___y_445_);
v_mctx_450_ = lean_ctor_get(v___x_449_, 0);
lean_inc_ref(v_mctx_450_);
lean_dec(v___x_449_);
v___x_451_ = l_Lean_instantiateMVarsCore(v_mctx_450_, v_e_444_);
v_fst_452_ = lean_ctor_get(v___x_451_, 0);
lean_inc(v_fst_452_);
v_snd_453_ = lean_ctor_get(v___x_451_, 1);
lean_inc(v_snd_453_);
lean_dec_ref(v___x_451_);
v___x_454_ = lean_st_ref_take(v___y_445_);
v_cache_455_ = lean_ctor_get(v___x_454_, 1);
v_zetaDeltaFVarIds_456_ = lean_ctor_get(v___x_454_, 2);
v_postponed_457_ = lean_ctor_get(v___x_454_, 3);
v_diag_458_ = lean_ctor_get(v___x_454_, 4);
v_isSharedCheck_467_ = !lean_is_exclusive(v___x_454_);
if (v_isSharedCheck_467_ == 0)
{
lean_object* v_unused_468_; 
v_unused_468_ = lean_ctor_get(v___x_454_, 0);
lean_dec(v_unused_468_);
v___x_460_ = v___x_454_;
v_isShared_461_ = v_isSharedCheck_467_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_diag_458_);
lean_inc(v_postponed_457_);
lean_inc(v_zetaDeltaFVarIds_456_);
lean_inc(v_cache_455_);
lean_dec(v___x_454_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_467_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v___x_463_; 
if (v_isShared_461_ == 0)
{
lean_ctor_set(v___x_460_, 0, v_snd_453_);
v___x_463_ = v___x_460_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v_snd_453_);
lean_ctor_set(v_reuseFailAlloc_466_, 1, v_cache_455_);
lean_ctor_set(v_reuseFailAlloc_466_, 2, v_zetaDeltaFVarIds_456_);
lean_ctor_set(v_reuseFailAlloc_466_, 3, v_postponed_457_);
lean_ctor_set(v_reuseFailAlloc_466_, 4, v_diag_458_);
v___x_463_ = v_reuseFailAlloc_466_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_464_ = lean_st_ref_set(v___y_445_, v___x_463_);
v___x_465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_465_, 0, v_fst_452_);
return v___x_465_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_replaceTargetDefEq_spec__0___redArg___boxed(lean_object* v_e_469_, lean_object* v___y_470_, lean_object* v___y_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l_Lean_instantiateMVars___at___00Lean_MVarId_replaceTargetDefEq_spec__0___redArg(v_e_469_, v___y_470_);
lean_dec(v___y_470_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_replaceTargetDefEq_spec__0(lean_object* v_e_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_){
_start:
{
lean_object* v___x_479_; 
v___x_479_ = l_Lean_instantiateMVars___at___00Lean_MVarId_replaceTargetDefEq_spec__0___redArg(v_e_473_, v___y_475_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_replaceTargetDefEq_spec__0___boxed(lean_object* v_e_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l_Lean_instantiateMVars___at___00Lean_MVarId_replaceTargetDefEq_spec__0(v_e_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_);
lean_dec(v___y_484_);
lean_dec_ref(v___y_483_);
lean_dec(v___y_482_);
lean_dec_ref(v___y_481_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetDefEq___lam__0(lean_object* v_mvarId_487_, lean_object* v___x_488_, lean_object* v_targetNew_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_){
_start:
{
lean_object* v___x_495_; 
lean_inc(v_mvarId_487_);
v___x_495_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_487_, v___x_488_, v___y_490_, v___y_491_, v___y_492_, v___y_493_);
if (lean_obj_tag(v___x_495_) == 0)
{
lean_object* v___x_496_; 
lean_dec_ref(v___x_495_);
lean_inc(v_mvarId_487_);
v___x_496_ = l_Lean_MVarId_getType(v_mvarId_487_, v___y_490_, v___y_491_, v___y_492_, v___y_493_);
if (lean_obj_tag(v___x_496_) == 0)
{
lean_object* v_a_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_567_; 
v_a_497_ = lean_ctor_get(v___x_496_, 0);
v_isSharedCheck_567_ = !lean_is_exclusive(v___x_496_);
if (v_isSharedCheck_567_ == 0)
{
v___x_499_ = v___x_496_;
v_isShared_500_ = v_isSharedCheck_567_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_a_497_);
lean_dec(v___x_496_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_567_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
uint8_t v___x_501_; 
v___x_501_ = lean_expr_equal(v_a_497_, v_targetNew_489_);
if (v___x_501_ == 0)
{
lean_object* v___x_502_; lean_object* v_a_503_; lean_object* v___x_504_; lean_object* v_a_505_; uint8_t v___x_506_; 
lean_del_object(v___x_499_);
v___x_502_ = l_Lean_instantiateMVars___at___00Lean_MVarId_replaceTargetDefEq_spec__0___redArg(v_a_497_, v___y_491_);
v_a_503_ = lean_ctor_get(v___x_502_, 0);
lean_inc(v_a_503_);
lean_dec_ref(v___x_502_);
v___x_504_ = l_Lean_instantiateMVars___at___00Lean_MVarId_replaceTargetDefEq_spec__0___redArg(v_targetNew_489_, v___y_491_);
v_a_505_ = lean_ctor_get(v___x_504_, 0);
lean_inc(v_a_505_);
lean_dec_ref(v___x_504_);
v___x_506_ = lean_expr_equal(v_a_503_, v_a_505_);
if (v___x_506_ == 0)
{
lean_object* v___x_507_; 
lean_inc(v_mvarId_487_);
v___x_507_ = l_Lean_MVarId_getTag(v_mvarId_487_, v___y_490_, v___y_491_, v___y_492_, v___y_493_);
if (lean_obj_tag(v___x_507_) == 0)
{
lean_object* v_a_508_; lean_object* v___x_509_; 
v_a_508_ = lean_ctor_get(v___x_507_, 0);
lean_inc(v_a_508_);
lean_dec_ref(v___x_507_);
v___x_509_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_505_, v_a_508_, v___y_490_, v___y_491_, v___y_492_, v___y_493_);
if (lean_obj_tag(v___x_509_) == 0)
{
lean_object* v_a_510_; lean_object* v___x_511_; 
v_a_510_ = lean_ctor_get(v___x_509_, 0);
lean_inc_n(v_a_510_, 2);
lean_dec_ref(v___x_509_);
v___x_511_ = l_Lean_Meta_mkExpectedTypeHint(v_a_510_, v_a_503_, v___y_490_, v___y_491_, v___y_492_, v___y_493_);
if (lean_obj_tag(v___x_511_) == 0)
{
lean_object* v_a_512_; lean_object* v___x_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_521_; 
v_a_512_ = lean_ctor_get(v___x_511_, 0);
lean_inc(v_a_512_);
lean_dec_ref(v___x_511_);
v___x_513_ = l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0___redArg(v_mvarId_487_, v_a_512_, v___y_491_);
v_isSharedCheck_521_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_521_ == 0)
{
lean_object* v_unused_522_; 
v_unused_522_ = lean_ctor_get(v___x_513_, 0);
lean_dec(v_unused_522_);
v___x_515_ = v___x_513_;
v_isShared_516_ = v_isSharedCheck_521_;
goto v_resetjp_514_;
}
else
{
lean_dec(v___x_513_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_521_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
lean_object* v___x_517_; lean_object* v___x_519_; 
v___x_517_ = l_Lean_Expr_mvarId_x21(v_a_510_);
lean_dec(v_a_510_);
if (v_isShared_516_ == 0)
{
lean_ctor_set(v___x_515_, 0, v___x_517_);
v___x_519_ = v___x_515_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v___x_517_);
v___x_519_ = v_reuseFailAlloc_520_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
return v___x_519_;
}
}
}
else
{
lean_object* v_a_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_530_; 
lean_dec(v_a_510_);
lean_dec(v_mvarId_487_);
v_a_523_ = lean_ctor_get(v___x_511_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v___x_511_);
if (v_isSharedCheck_530_ == 0)
{
v___x_525_ = v___x_511_;
v_isShared_526_ = v_isSharedCheck_530_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_a_523_);
lean_dec(v___x_511_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_530_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___x_528_; 
if (v_isShared_526_ == 0)
{
v___x_528_ = v___x_525_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v_a_523_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
return v___x_528_;
}
}
}
}
else
{
lean_object* v_a_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_538_; 
lean_dec(v_a_503_);
lean_dec(v_mvarId_487_);
v_a_531_ = lean_ctor_get(v___x_509_, 0);
v_isSharedCheck_538_ = !lean_is_exclusive(v___x_509_);
if (v_isSharedCheck_538_ == 0)
{
v___x_533_ = v___x_509_;
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_a_531_);
lean_dec(v___x_509_);
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
lean_object* v_a_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_546_; 
lean_dec(v_a_505_);
lean_dec(v_a_503_);
lean_dec(v_mvarId_487_);
v_a_539_ = lean_ctor_get(v___x_507_, 0);
v_isSharedCheck_546_ = !lean_is_exclusive(v___x_507_);
if (v_isSharedCheck_546_ == 0)
{
v___x_541_ = v___x_507_;
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_a_539_);
lean_dec(v___x_507_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_544_; 
if (v_isShared_542_ == 0)
{
v___x_544_ = v___x_541_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_a_539_);
v___x_544_ = v_reuseFailAlloc_545_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
return v___x_544_;
}
}
}
}
else
{
lean_object* v___x_547_; 
lean_dec(v_a_505_);
lean_inc(v_mvarId_487_);
v___x_547_ = l_Lean_MVarId_setType___redArg(v_mvarId_487_, v_a_503_, v___y_491_);
if (lean_obj_tag(v___x_547_) == 0)
{
lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_554_; 
v_isSharedCheck_554_ = !lean_is_exclusive(v___x_547_);
if (v_isSharedCheck_554_ == 0)
{
lean_object* v_unused_555_; 
v_unused_555_ = lean_ctor_get(v___x_547_, 0);
lean_dec(v_unused_555_);
v___x_549_ = v___x_547_;
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
else
{
lean_dec(v___x_547_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_552_; 
if (v_isShared_550_ == 0)
{
lean_ctor_set(v___x_549_, 0, v_mvarId_487_);
v___x_552_ = v___x_549_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_mvarId_487_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
}
else
{
lean_object* v_a_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_563_; 
lean_dec(v_mvarId_487_);
v_a_556_ = lean_ctor_get(v___x_547_, 0);
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_547_);
if (v_isSharedCheck_563_ == 0)
{
v___x_558_ = v___x_547_;
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_a_556_);
lean_dec(v___x_547_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___x_561_; 
if (v_isShared_559_ == 0)
{
v___x_561_ = v___x_558_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v_a_556_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
return v___x_561_;
}
}
}
}
}
else
{
lean_object* v___x_565_; 
lean_dec(v_a_497_);
lean_dec_ref(v_targetNew_489_);
if (v_isShared_500_ == 0)
{
lean_ctor_set(v___x_499_, 0, v_mvarId_487_);
v___x_565_ = v___x_499_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_mvarId_487_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
return v___x_565_;
}
}
}
}
else
{
lean_object* v_a_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_575_; 
lean_dec_ref(v_targetNew_489_);
lean_dec(v_mvarId_487_);
v_a_568_ = lean_ctor_get(v___x_496_, 0);
v_isSharedCheck_575_ = !lean_is_exclusive(v___x_496_);
if (v_isSharedCheck_575_ == 0)
{
v___x_570_ = v___x_496_;
v_isShared_571_ = v_isSharedCheck_575_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_a_568_);
lean_dec(v___x_496_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_575_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___x_573_; 
if (v_isShared_571_ == 0)
{
v___x_573_ = v___x_570_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v_a_568_);
v___x_573_ = v_reuseFailAlloc_574_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
return v___x_573_;
}
}
}
}
else
{
lean_object* v_a_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_583_; 
lean_dec_ref(v_targetNew_489_);
lean_dec(v_mvarId_487_);
v_a_576_ = lean_ctor_get(v___x_495_, 0);
v_isSharedCheck_583_ = !lean_is_exclusive(v___x_495_);
if (v_isSharedCheck_583_ == 0)
{
v___x_578_ = v___x_495_;
v_isShared_579_ = v_isSharedCheck_583_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_a_576_);
lean_dec(v___x_495_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_583_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
lean_object* v___x_581_; 
if (v_isShared_579_ == 0)
{
v___x_581_ = v___x_578_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v_a_576_);
v___x_581_ = v_reuseFailAlloc_582_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
return v___x_581_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetDefEq___lam__0___boxed(lean_object* v_mvarId_584_, lean_object* v___x_585_, lean_object* v_targetNew_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_){
_start:
{
lean_object* v_res_592_; 
v_res_592_ = l_Lean_MVarId_replaceTargetDefEq___lam__0(v_mvarId_584_, v___x_585_, v_targetNew_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_);
lean_dec(v___y_590_);
lean_dec_ref(v___y_589_);
lean_dec(v___y_588_);
lean_dec_ref(v___y_587_);
return v_res_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetDefEq(lean_object* v_mvarId_596_, lean_object* v_targetNew_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_){
_start:
{
lean_object* v___x_603_; lean_object* v___f_604_; lean_object* v___x_605_; 
v___x_603_ = ((lean_object*)(l_Lean_MVarId_replaceTargetDefEq___closed__1));
lean_inc(v_mvarId_596_);
v___f_604_ = lean_alloc_closure((void*)(l_Lean_MVarId_replaceTargetDefEq___lam__0___boxed), 8, 3);
lean_closure_set(v___f_604_, 0, v_mvarId_596_);
lean_closure_set(v___f_604_, 1, v___x_603_);
lean_closure_set(v___f_604_, 2, v_targetNew_597_);
v___x_605_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(v_mvarId_596_, v___f_604_, v_a_598_, v_a_599_, v_a_600_, v_a_601_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetDefEq___boxed(lean_object* v_mvarId_606_, lean_object* v_targetNew_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v_a_611_, lean_object* v_a_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_606_, v_targetNew_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_);
lean_dec(v_a_611_);
lean_dec_ref(v_a_610_);
lean_dec(v_a_609_);
lean_dec_ref(v_a_608_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replace___lam__0(lean_object* v_mvarId_614_, lean_object* v_fvarId_615_, lean_object* v_val_616_, lean_object* v_userName_x3f_617_, lean_object* v_type_x3f_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_){
_start:
{
lean_object* v___y_625_; lean_object* v_a_626_; lean_object* v_a_657_; 
if (lean_obj_tag(v_type_x3f_618_) == 0)
{
lean_object* v___x_670_; 
lean_inc(v___y_622_);
lean_inc_ref(v___y_621_);
lean_inc(v___y_620_);
lean_inc_ref(v___y_619_);
lean_inc_ref(v_val_616_);
v___x_670_ = lean_infer_type(v_val_616_, v___y_619_, v___y_620_, v___y_621_, v___y_622_);
if (lean_obj_tag(v___x_670_) == 0)
{
lean_object* v_a_671_; 
v_a_671_ = lean_ctor_get(v___x_670_, 0);
lean_inc(v_a_671_);
lean_dec_ref(v___x_670_);
v_a_657_ = v_a_671_;
goto v___jp_656_;
}
else
{
lean_object* v_a_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_679_; 
lean_dec(v___y_622_);
lean_dec_ref(v___y_621_);
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
lean_dec(v_userName_x3f_617_);
lean_dec_ref(v_val_616_);
lean_dec(v_fvarId_615_);
lean_dec(v_mvarId_614_);
v_a_672_ = lean_ctor_get(v___x_670_, 0);
v_isSharedCheck_679_ = !lean_is_exclusive(v___x_670_);
if (v_isSharedCheck_679_ == 0)
{
v___x_674_ = v___x_670_;
v_isShared_675_ = v_isSharedCheck_679_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_a_672_);
lean_dec(v___x_670_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_679_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v___x_677_; 
if (v_isShared_675_ == 0)
{
v___x_677_ = v___x_674_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v_a_672_);
v___x_677_ = v_reuseFailAlloc_678_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
return v___x_677_;
}
}
}
}
else
{
lean_object* v_val_680_; 
v_val_680_ = lean_ctor_get(v_type_x3f_618_, 0);
lean_inc(v_val_680_);
lean_dec_ref(v_type_x3f_618_);
v_a_657_ = v_val_680_;
goto v___jp_656_;
}
v___jp_624_:
{
lean_object* v___x_627_; 
lean_inc(v_fvarId_615_);
v___x_627_ = l_Lean_MVarId_assertAfter_x27(v_mvarId_614_, v_fvarId_615_, v_a_626_, v___y_625_, v_val_616_, v___y_619_, v___y_620_, v___y_621_, v___y_622_);
if (lean_obj_tag(v___x_627_) == 0)
{
lean_object* v_a_628_; lean_object* v_fvarId_629_; lean_object* v_mvarId_630_; lean_object* v_subst_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_655_; 
v_a_628_ = lean_ctor_get(v___x_627_, 0);
lean_inc(v_a_628_);
lean_dec_ref(v___x_627_);
v_fvarId_629_ = lean_ctor_get(v_a_628_, 0);
v_mvarId_630_ = lean_ctor_get(v_a_628_, 1);
v_subst_631_ = lean_ctor_get(v_a_628_, 2);
v_isSharedCheck_655_ = !lean_is_exclusive(v_a_628_);
if (v_isSharedCheck_655_ == 0)
{
v___x_633_ = v_a_628_;
v_isShared_634_ = v_isSharedCheck_655_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_subst_631_);
lean_inc(v_mvarId_630_);
lean_inc(v_fvarId_629_);
lean_dec(v_a_628_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_655_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
lean_object* v___x_635_; 
v___x_635_ = l_Lean_MVarId_tryClear(v_mvarId_630_, v_fvarId_615_, v___y_619_, v___y_620_, v___y_621_, v___y_622_);
lean_dec(v___y_622_);
lean_dec_ref(v___y_621_);
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
if (lean_obj_tag(v___x_635_) == 0)
{
lean_object* v_a_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_646_; 
v_a_636_ = lean_ctor_get(v___x_635_, 0);
v_isSharedCheck_646_ = !lean_is_exclusive(v___x_635_);
if (v_isSharedCheck_646_ == 0)
{
v___x_638_ = v___x_635_;
v_isShared_639_ = v_isSharedCheck_646_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_a_636_);
lean_dec(v___x_635_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_646_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
lean_object* v___x_641_; 
if (v_isShared_634_ == 0)
{
lean_ctor_set(v___x_633_, 1, v_a_636_);
v___x_641_ = v___x_633_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v_fvarId_629_);
lean_ctor_set(v_reuseFailAlloc_645_, 1, v_a_636_);
lean_ctor_set(v_reuseFailAlloc_645_, 2, v_subst_631_);
v___x_641_ = v_reuseFailAlloc_645_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
lean_object* v___x_643_; 
if (v_isShared_639_ == 0)
{
lean_ctor_set(v___x_638_, 0, v___x_641_);
v___x_643_ = v___x_638_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v___x_641_);
v___x_643_ = v_reuseFailAlloc_644_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
return v___x_643_;
}
}
}
}
else
{
lean_object* v_a_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_654_; 
lean_del_object(v___x_633_);
lean_dec(v_subst_631_);
lean_dec(v_fvarId_629_);
v_a_647_ = lean_ctor_get(v___x_635_, 0);
v_isSharedCheck_654_ = !lean_is_exclusive(v___x_635_);
if (v_isSharedCheck_654_ == 0)
{
v___x_649_ = v___x_635_;
v_isShared_650_ = v_isSharedCheck_654_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_a_647_);
lean_dec(v___x_635_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_654_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v___x_652_; 
if (v_isShared_650_ == 0)
{
v___x_652_ = v___x_649_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_a_647_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
return v___x_652_;
}
}
}
}
}
else
{
lean_dec(v___y_622_);
lean_dec_ref(v___y_621_);
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
lean_dec(v_fvarId_615_);
return v___x_627_;
}
}
v___jp_656_:
{
if (lean_obj_tag(v_userName_x3f_617_) == 0)
{
lean_object* v___x_658_; 
lean_inc(v_fvarId_615_);
v___x_658_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_615_, v___y_619_, v___y_621_, v___y_622_);
if (lean_obj_tag(v___x_658_) == 0)
{
lean_object* v_a_659_; lean_object* v___x_660_; 
v_a_659_ = lean_ctor_get(v___x_658_, 0);
lean_inc(v_a_659_);
lean_dec_ref(v___x_658_);
v___x_660_ = l_Lean_LocalDecl_userName(v_a_659_);
lean_dec(v_a_659_);
v___y_625_ = v_a_657_;
v_a_626_ = v___x_660_;
goto v___jp_624_;
}
else
{
lean_object* v_a_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_668_; 
lean_dec_ref(v_a_657_);
lean_dec(v___y_622_);
lean_dec_ref(v___y_621_);
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
lean_dec_ref(v_val_616_);
lean_dec(v_fvarId_615_);
lean_dec(v_mvarId_614_);
v_a_661_ = lean_ctor_get(v___x_658_, 0);
v_isSharedCheck_668_ = !lean_is_exclusive(v___x_658_);
if (v_isSharedCheck_668_ == 0)
{
v___x_663_ = v___x_658_;
v_isShared_664_ = v_isSharedCheck_668_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_a_661_);
lean_dec(v___x_658_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_668_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___x_666_; 
if (v_isShared_664_ == 0)
{
v___x_666_ = v___x_663_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v_a_661_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
}
}
}
}
else
{
lean_object* v_val_669_; 
v_val_669_ = lean_ctor_get(v_userName_x3f_617_, 0);
lean_inc(v_val_669_);
lean_dec_ref(v_userName_x3f_617_);
v___y_625_ = v_a_657_;
v_a_626_ = v_val_669_;
goto v___jp_624_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replace___lam__0___boxed(lean_object* v_mvarId_681_, lean_object* v_fvarId_682_, lean_object* v_val_683_, lean_object* v_userName_x3f_684_, lean_object* v_type_x3f_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l_Lean_MVarId_replace___lam__0(v_mvarId_681_, v_fvarId_682_, v_val_683_, v_userName_x3f_684_, v_type_x3f_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replace(lean_object* v_mvarId_692_, lean_object* v_fvarId_693_, lean_object* v_val_694_, lean_object* v_type_x3f_695_, lean_object* v_userName_x3f_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_){
_start:
{
lean_object* v___f_702_; lean_object* v___x_703_; 
lean_inc(v_mvarId_692_);
v___f_702_ = lean_alloc_closure((void*)(l_Lean_MVarId_replace___lam__0___boxed), 10, 5);
lean_closure_set(v___f_702_, 0, v_mvarId_692_);
lean_closure_set(v___f_702_, 1, v_fvarId_693_);
lean_closure_set(v___f_702_, 2, v_val_694_);
lean_closure_set(v___f_702_, 3, v_userName_x3f_696_);
lean_closure_set(v___f_702_, 4, v_type_x3f_695_);
v___x_703_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(v_mvarId_692_, v___f_702_, v_a_697_, v_a_698_, v_a_699_, v_a_700_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replace___boxed(lean_object* v_mvarId_704_, lean_object* v_fvarId_705_, lean_object* v_val_706_, lean_object* v_type_x3f_707_, lean_object* v_userName_x3f_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_){
_start:
{
lean_object* v_res_714_; 
v_res_714_ = l_Lean_MVarId_replace(v_mvarId_704_, v_fvarId_705_, v_val_706_, v_type_x3f_707_, v_userName_x3f_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_);
lean_dec(v_a_712_);
lean_dec_ref(v_a_711_);
lean_dec(v_a_710_);
lean_dec_ref(v_a_709_);
return v_res_714_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceLocalDecl___lam__0(lean_object* v_eqProof_715_, lean_object* v___x_716_, lean_object* v_typeNew_717_, lean_object* v_mvarId_718_, lean_object* v_fvarId_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_){
_start:
{
lean_object* v___x_725_; 
v___x_725_ = l_Lean_Meta_mkEqMP(v_eqProof_715_, v___x_716_, v___y_720_, v___y_721_, v___y_722_, v___y_723_);
if (lean_obj_tag(v___x_725_) == 0)
{
lean_object* v_a_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v_a_726_ = lean_ctor_get(v___x_725_, 0);
lean_inc(v_a_726_);
lean_dec_ref(v___x_725_);
v___x_727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_727_, 0, v_typeNew_717_);
v___x_728_ = lean_box(0);
v___x_729_ = l_Lean_MVarId_replace(v_mvarId_718_, v_fvarId_719_, v_a_726_, v___x_727_, v___x_728_, v___y_720_, v___y_721_, v___y_722_, v___y_723_);
return v___x_729_;
}
else
{
lean_object* v_a_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_737_; 
lean_dec(v_fvarId_719_);
lean_dec(v_mvarId_718_);
lean_dec_ref(v_typeNew_717_);
v_a_730_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_737_ == 0)
{
v___x_732_ = v___x_725_;
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_a_730_);
lean_dec(v___x_725_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___x_735_; 
if (v_isShared_733_ == 0)
{
v___x_735_ = v___x_732_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v_a_730_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceLocalDecl___lam__0___boxed(lean_object* v_eqProof_738_, lean_object* v___x_739_, lean_object* v_typeNew_740_, lean_object* v_mvarId_741_, lean_object* v_fvarId_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_){
_start:
{
lean_object* v_res_748_; 
v_res_748_ = l_Lean_MVarId_replaceLocalDecl___lam__0(v_eqProof_738_, v___x_739_, v_typeNew_740_, v_mvarId_741_, v_fvarId_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_);
lean_dec(v___y_746_);
lean_dec_ref(v___y_745_);
lean_dec(v___y_744_);
lean_dec_ref(v___y_743_);
return v_res_748_;
}
}
static lean_object* _init_l_Lean_MVarId_replaceLocalDecl___closed__0(void){
_start:
{
lean_object* v___x_749_; 
v___x_749_ = l_instMonadEIO(lean_box(0));
return v___x_749_;
}
}
static lean_object* _init_l_Lean_MVarId_replaceLocalDecl___closed__1(void){
_start:
{
lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_750_ = lean_obj_once(&l_Lean_MVarId_replaceLocalDecl___closed__0, &l_Lean_MVarId_replaceLocalDecl___closed__0_once, _init_l_Lean_MVarId_replaceLocalDecl___closed__0);
v___x_751_ = l_StateRefT_x27_instMonad___redArg(v___x_750_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceLocalDecl(lean_object* v_mvarId_756_, lean_object* v_fvarId_757_, lean_object* v_typeNew_758_, lean_object* v_eqProof_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_){
_start:
{
lean_object* v___x_765_; lean_object* v_toApplicative_766_; lean_object* v_toFunctor_767_; lean_object* v_toSeq_768_; lean_object* v_toSeqLeft_769_; lean_object* v_toSeqRight_770_; lean_object* v___f_771_; lean_object* v___f_772_; lean_object* v___f_773_; lean_object* v___f_774_; lean_object* v___x_775_; lean_object* v___f_776_; lean_object* v___f_777_; lean_object* v___f_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v_toApplicative_784_; lean_object* v_toFunctor_785_; lean_object* v_toSeq_786_; lean_object* v_toSeqLeft_787_; lean_object* v_toSeqRight_788_; lean_object* v___f_789_; lean_object* v___f_790_; lean_object* v___x_791_; lean_object* v___f_792_; lean_object* v___f_793_; lean_object* v___f_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v_toApplicative_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_829_; 
v___x_765_ = lean_obj_once(&l_Lean_MVarId_replaceLocalDecl___closed__1, &l_Lean_MVarId_replaceLocalDecl___closed__1_once, _init_l_Lean_MVarId_replaceLocalDecl___closed__1);
v_toApplicative_766_ = lean_ctor_get(v___x_765_, 0);
v_toFunctor_767_ = lean_ctor_get(v_toApplicative_766_, 0);
v_toSeq_768_ = lean_ctor_get(v_toApplicative_766_, 2);
v_toSeqLeft_769_ = lean_ctor_get(v_toApplicative_766_, 3);
v_toSeqRight_770_ = lean_ctor_get(v_toApplicative_766_, 4);
v___f_771_ = ((lean_object*)(l_Lean_MVarId_replaceLocalDecl___closed__2));
v___f_772_ = ((lean_object*)(l_Lean_MVarId_replaceLocalDecl___closed__3));
lean_inc_ref_n(v_toFunctor_767_, 2);
v___f_773_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_773_, 0, v_toFunctor_767_);
v___f_774_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_774_, 0, v_toFunctor_767_);
v___x_775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_775_, 0, v___f_773_);
lean_ctor_set(v___x_775_, 1, v___f_774_);
lean_inc(v_toSeqRight_770_);
v___f_776_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_776_, 0, v_toSeqRight_770_);
lean_inc(v_toSeqLeft_769_);
v___f_777_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_777_, 0, v_toSeqLeft_769_);
lean_inc(v_toSeq_768_);
v___f_778_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_778_, 0, v_toSeq_768_);
v___x_779_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_779_, 0, v___x_775_);
lean_ctor_set(v___x_779_, 1, v___f_771_);
lean_ctor_set(v___x_779_, 2, v___f_778_);
lean_ctor_set(v___x_779_, 3, v___f_777_);
lean_ctor_set(v___x_779_, 4, v___f_776_);
v___x_780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_780_, 0, v___x_779_);
lean_ctor_set(v___x_780_, 1, v___f_772_);
v___x_781_ = l_StateRefT_x27_instMonad___redArg(v___x_780_);
v___x_782_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(v___x_782_, 0, lean_box(0));
lean_closure_set(v___x_782_, 1, lean_box(0));
lean_closure_set(v___x_782_, 2, v___x_781_);
v___x_783_ = l_instMonadControlTOfPure___redArg(v___x_782_);
v_toApplicative_784_ = lean_ctor_get(v___x_765_, 0);
v_toFunctor_785_ = lean_ctor_get(v_toApplicative_784_, 0);
v_toSeq_786_ = lean_ctor_get(v_toApplicative_784_, 2);
v_toSeqLeft_787_ = lean_ctor_get(v_toApplicative_784_, 3);
v_toSeqRight_788_ = lean_ctor_get(v_toApplicative_784_, 4);
lean_inc_ref_n(v_toFunctor_785_, 2);
v___f_789_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_789_, 0, v_toFunctor_785_);
v___f_790_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_790_, 0, v_toFunctor_785_);
v___x_791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_791_, 0, v___f_789_);
lean_ctor_set(v___x_791_, 1, v___f_790_);
lean_inc(v_toSeqRight_788_);
v___f_792_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_792_, 0, v_toSeqRight_788_);
lean_inc(v_toSeqLeft_787_);
v___f_793_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_793_, 0, v_toSeqLeft_787_);
lean_inc(v_toSeq_786_);
v___f_794_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_794_, 0, v_toSeq_786_);
v___x_795_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_795_, 0, v___x_791_);
lean_ctor_set(v___x_795_, 1, v___f_771_);
lean_ctor_set(v___x_795_, 2, v___f_794_);
lean_ctor_set(v___x_795_, 3, v___f_793_);
lean_ctor_set(v___x_795_, 4, v___f_792_);
v___x_796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_796_, 0, v___x_795_);
lean_ctor_set(v___x_796_, 1, v___f_772_);
v___x_797_ = l_StateRefT_x27_instMonad___redArg(v___x_796_);
v_toApplicative_798_ = lean_ctor_get(v___x_797_, 0);
v_isSharedCheck_829_ = !lean_is_exclusive(v___x_797_);
if (v_isSharedCheck_829_ == 0)
{
lean_object* v_unused_830_; 
v_unused_830_ = lean_ctor_get(v___x_797_, 1);
lean_dec(v_unused_830_);
v___x_800_ = v___x_797_;
v_isShared_801_ = v_isSharedCheck_829_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_toApplicative_798_);
lean_dec(v___x_797_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_829_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v_toFunctor_802_; lean_object* v_toSeq_803_; lean_object* v_toSeqLeft_804_; lean_object* v_toSeqRight_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_827_; 
v_toFunctor_802_ = lean_ctor_get(v_toApplicative_798_, 0);
v_toSeq_803_ = lean_ctor_get(v_toApplicative_798_, 2);
v_toSeqLeft_804_ = lean_ctor_get(v_toApplicative_798_, 3);
v_toSeqRight_805_ = lean_ctor_get(v_toApplicative_798_, 4);
v_isSharedCheck_827_ = !lean_is_exclusive(v_toApplicative_798_);
if (v_isSharedCheck_827_ == 0)
{
lean_object* v_unused_828_; 
v_unused_828_ = lean_ctor_get(v_toApplicative_798_, 1);
lean_dec(v_unused_828_);
v___x_807_ = v_toApplicative_798_;
v_isShared_808_ = v_isSharedCheck_827_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_toSeqRight_805_);
lean_inc(v_toSeqLeft_804_);
lean_inc(v_toSeq_803_);
lean_inc(v_toFunctor_802_);
lean_dec(v_toApplicative_798_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_827_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___f_809_; lean_object* v___f_810_; lean_object* v___f_811_; lean_object* v___f_812_; lean_object* v___x_813_; lean_object* v___f_814_; lean_object* v___f_815_; lean_object* v___f_816_; lean_object* v___x_818_; 
v___f_809_ = ((lean_object*)(l_Lean_MVarId_replaceLocalDecl___closed__4));
v___f_810_ = ((lean_object*)(l_Lean_MVarId_replaceLocalDecl___closed__5));
lean_inc_ref(v_toFunctor_802_);
v___f_811_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_811_, 0, v_toFunctor_802_);
v___f_812_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_812_, 0, v_toFunctor_802_);
v___x_813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_813_, 0, v___f_811_);
lean_ctor_set(v___x_813_, 1, v___f_812_);
v___f_814_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_814_, 0, v_toSeqRight_805_);
v___f_815_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_815_, 0, v_toSeqLeft_804_);
v___f_816_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_816_, 0, v_toSeq_803_);
if (v_isShared_808_ == 0)
{
lean_ctor_set(v___x_807_, 4, v___f_814_);
lean_ctor_set(v___x_807_, 3, v___f_815_);
lean_ctor_set(v___x_807_, 2, v___f_816_);
lean_ctor_set(v___x_807_, 1, v___f_809_);
lean_ctor_set(v___x_807_, 0, v___x_813_);
v___x_818_ = v___x_807_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v___x_813_);
lean_ctor_set(v_reuseFailAlloc_826_, 1, v___f_809_);
lean_ctor_set(v_reuseFailAlloc_826_, 2, v___f_816_);
lean_ctor_set(v_reuseFailAlloc_826_, 3, v___f_815_);
lean_ctor_set(v_reuseFailAlloc_826_, 4, v___f_814_);
v___x_818_ = v_reuseFailAlloc_826_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
lean_object* v___x_820_; 
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 1, v___f_810_);
lean_ctor_set(v___x_800_, 0, v___x_818_);
v___x_820_ = v___x_800_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v___x_818_);
lean_ctor_set(v_reuseFailAlloc_825_, 1, v___f_810_);
v___x_820_ = v_reuseFailAlloc_825_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
lean_object* v___x_821_; lean_object* v___f_822_; lean_object* v___x_17__overap_823_; lean_object* v___x_824_; 
lean_inc(v_fvarId_757_);
v___x_821_ = l_Lean_mkFVar(v_fvarId_757_);
lean_inc(v_mvarId_756_);
v___f_822_ = lean_alloc_closure((void*)(l_Lean_MVarId_replaceLocalDecl___lam__0___boxed), 10, 5);
lean_closure_set(v___f_822_, 0, v_eqProof_759_);
lean_closure_set(v___f_822_, 1, v___x_821_);
lean_closure_set(v___f_822_, 2, v_typeNew_758_);
lean_closure_set(v___f_822_, 3, v_mvarId_756_);
lean_closure_set(v___f_822_, 4, v_fvarId_757_);
v___x_17__overap_823_ = l_Lean_MVarId_withContext___redArg(v___x_783_, v___x_820_, v_mvarId_756_, v___f_822_);
lean_inc(v_a_763_);
lean_inc_ref(v_a_762_);
lean_inc(v_a_761_);
lean_inc_ref(v_a_760_);
v___x_824_ = lean_apply_5(v___x_17__overap_823_, v_a_760_, v_a_761_, v_a_762_, v_a_763_, lean_box(0));
return v___x_824_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceLocalDecl___boxed(lean_object* v_mvarId_831_, lean_object* v_fvarId_832_, lean_object* v_typeNew_833_, lean_object* v_eqProof_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l_Lean_MVarId_replaceLocalDecl(v_mvarId_831_, v_fvarId_832_, v_typeNew_833_, v_eqProof_834_, v_a_835_, v_a_836_, v_a_837_, v_a_838_);
lean_dec(v_a_838_);
lean_dec_ref(v_a_837_);
lean_dec(v_a_836_);
lean_dec_ref(v_a_835_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalInstances___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__0___redArg(lean_object* v_decls_841_, lean_object* v_x_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_){
_start:
{
lean_object* v___x_848_; 
v___x_848_ = l_Lean_Meta_withLocalInstancesImp___redArg(v_decls_841_, v_x_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_);
if (lean_obj_tag(v___x_848_) == 0)
{
lean_object* v_a_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_856_; 
v_a_849_ = lean_ctor_get(v___x_848_, 0);
v_isSharedCheck_856_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_856_ == 0)
{
v___x_851_ = v___x_848_;
v_isShared_852_ = v_isSharedCheck_856_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_a_849_);
lean_dec(v___x_848_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_856_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___x_854_; 
if (v_isShared_852_ == 0)
{
v___x_854_ = v___x_851_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v_a_849_);
v___x_854_ = v_reuseFailAlloc_855_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
return v___x_854_;
}
}
}
else
{
lean_object* v_a_857_; lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_864_; 
v_a_857_ = lean_ctor_get(v___x_848_, 0);
v_isSharedCheck_864_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_864_ == 0)
{
v___x_859_ = v___x_848_;
v_isShared_860_ = v_isSharedCheck_864_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_a_857_);
lean_dec(v___x_848_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_864_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
lean_object* v___x_862_; 
if (v_isShared_860_ == 0)
{
v___x_862_ = v___x_859_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v_a_857_);
v___x_862_ = v_reuseFailAlloc_863_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
return v___x_862_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalInstances___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__0___redArg___boxed(lean_object* v_decls_865_, lean_object* v_x_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_){
_start:
{
lean_object* v_res_872_; 
v_res_872_ = l_Lean_Meta_withLocalInstances___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__0___redArg(v_decls_865_, v_x_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_);
lean_dec(v___y_870_);
lean_dec_ref(v___y_869_);
lean_dec(v___y_868_);
lean_dec_ref(v___y_867_);
lean_dec(v_decls_865_);
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalInstances___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__0(lean_object* v_00_u03b1_873_, lean_object* v_decls_874_, lean_object* v_x_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_){
_start:
{
lean_object* v___x_881_; 
v___x_881_ = l_Lean_Meta_withLocalInstances___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__0___redArg(v_decls_874_, v_x_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalInstances___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__0___boxed(lean_object* v_00_u03b1_882_, lean_object* v_decls_883_, lean_object* v_x_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_){
_start:
{
lean_object* v_res_890_; 
v_res_890_ = l_Lean_Meta_withLocalInstances___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__0(v_00_u03b1_882_, v_decls_883_, v_x_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_);
lean_dec(v___y_888_);
lean_dec_ref(v___y_887_);
lean_dec(v___y_886_);
lean_dec_ref(v___y_885_);
lean_dec(v_decls_883_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__1___redArg(lean_object* v_lctx_891_, lean_object* v_x_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_){
_start:
{
lean_object* v_keyedConfig_898_; uint8_t v_trackZetaDelta_899_; lean_object* v_zetaDeltaSet_900_; lean_object* v_localInstances_901_; lean_object* v_defEqCtx_x3f_902_; lean_object* v_synthPendingDepth_903_; lean_object* v_canUnfold_x3f_904_; uint8_t v_univApprox_905_; uint8_t v_inTypeClassResolution_906_; uint8_t v_cacheInferType_907_; lean_object* v___x_908_; lean_object* v___x_909_; 
v_keyedConfig_898_ = lean_ctor_get(v___y_893_, 0);
v_trackZetaDelta_899_ = lean_ctor_get_uint8(v___y_893_, sizeof(void*)*7);
v_zetaDeltaSet_900_ = lean_ctor_get(v___y_893_, 1);
v_localInstances_901_ = lean_ctor_get(v___y_893_, 3);
v_defEqCtx_x3f_902_ = lean_ctor_get(v___y_893_, 4);
v_synthPendingDepth_903_ = lean_ctor_get(v___y_893_, 5);
v_canUnfold_x3f_904_ = lean_ctor_get(v___y_893_, 6);
v_univApprox_905_ = lean_ctor_get_uint8(v___y_893_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_906_ = lean_ctor_get_uint8(v___y_893_, sizeof(void*)*7 + 2);
v_cacheInferType_907_ = lean_ctor_get_uint8(v___y_893_, sizeof(void*)*7 + 3);
lean_inc(v_canUnfold_x3f_904_);
lean_inc(v_synthPendingDepth_903_);
lean_inc(v_defEqCtx_x3f_902_);
lean_inc_ref(v_localInstances_901_);
lean_inc(v_zetaDeltaSet_900_);
lean_inc_ref(v_keyedConfig_898_);
v___x_908_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_908_, 0, v_keyedConfig_898_);
lean_ctor_set(v___x_908_, 1, v_zetaDeltaSet_900_);
lean_ctor_set(v___x_908_, 2, v_lctx_891_);
lean_ctor_set(v___x_908_, 3, v_localInstances_901_);
lean_ctor_set(v___x_908_, 4, v_defEqCtx_x3f_902_);
lean_ctor_set(v___x_908_, 5, v_synthPendingDepth_903_);
lean_ctor_set(v___x_908_, 6, v_canUnfold_x3f_904_);
lean_ctor_set_uint8(v___x_908_, sizeof(void*)*7, v_trackZetaDelta_899_);
lean_ctor_set_uint8(v___x_908_, sizeof(void*)*7 + 1, v_univApprox_905_);
lean_ctor_set_uint8(v___x_908_, sizeof(void*)*7 + 2, v_inTypeClassResolution_906_);
lean_ctor_set_uint8(v___x_908_, sizeof(void*)*7 + 3, v_cacheInferType_907_);
lean_inc(v___y_896_);
lean_inc_ref(v___y_895_);
lean_inc(v___y_894_);
v___x_909_ = lean_apply_5(v_x_892_, v___x_908_, v___y_894_, v___y_895_, v___y_896_, lean_box(0));
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__1___redArg___boxed(lean_object* v_lctx_910_, lean_object* v_x_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_){
_start:
{
lean_object* v_res_917_; 
v_res_917_ = l_Lean_Meta_withLCtx_x27___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__1___redArg(v_lctx_910_, v_x_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_);
lean_dec(v___y_915_);
lean_dec_ref(v___y_914_);
lean_dec(v___y_913_);
lean_dec_ref(v___y_912_);
return v_res_917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__1(lean_object* v_00_u03b1_918_, lean_object* v_lctx_919_, lean_object* v_x_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_){
_start:
{
lean_object* v___x_926_; 
v___x_926_ = l_Lean_Meta_withLCtx_x27___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__1___redArg(v_lctx_919_, v_x_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
return v___x_926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__1___boxed(lean_object* v_00_u03b1_927_, lean_object* v_lctx_928_, lean_object* v_x_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_){
_start:
{
lean_object* v_res_935_; 
v_res_935_ = l_Lean_Meta_withLCtx_x27___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__1(v_00_u03b1_927_, v_lctx_928_, v_x_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
lean_dec(v___y_931_);
lean_dec_ref(v___y_930_);
return v_res_935_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_setFVarType___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2___redArg(lean_object* v_mvarId_936_, lean_object* v_fvarId_937_, lean_object* v_type_938_, lean_object* v___y_939_){
_start:
{
lean_object* v___x_941_; lean_object* v_mctx_942_; lean_object* v_cache_943_; lean_object* v_zetaDeltaFVarIds_944_; lean_object* v_postponed_945_; lean_object* v_diag_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_957_; 
v___x_941_ = lean_st_ref_take(v___y_939_);
v_mctx_942_ = lean_ctor_get(v___x_941_, 0);
v_cache_943_ = lean_ctor_get(v___x_941_, 1);
v_zetaDeltaFVarIds_944_ = lean_ctor_get(v___x_941_, 2);
v_postponed_945_ = lean_ctor_get(v___x_941_, 3);
v_diag_946_ = lean_ctor_get(v___x_941_, 4);
v_isSharedCheck_957_ = !lean_is_exclusive(v___x_941_);
if (v_isSharedCheck_957_ == 0)
{
v___x_948_ = v___x_941_;
v_isShared_949_ = v_isSharedCheck_957_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_diag_946_);
lean_inc(v_postponed_945_);
lean_inc(v_zetaDeltaFVarIds_944_);
lean_inc(v_cache_943_);
lean_inc(v_mctx_942_);
lean_dec(v___x_941_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_957_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v___x_950_; lean_object* v___x_952_; 
v___x_950_ = l_Lean_MetavarContext_setFVarType(v_mctx_942_, v_mvarId_936_, v_fvarId_937_, v_type_938_);
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 0, v___x_950_);
v___x_952_ = v___x_948_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v___x_950_);
lean_ctor_set(v_reuseFailAlloc_956_, 1, v_cache_943_);
lean_ctor_set(v_reuseFailAlloc_956_, 2, v_zetaDeltaFVarIds_944_);
lean_ctor_set(v_reuseFailAlloc_956_, 3, v_postponed_945_);
lean_ctor_set(v_reuseFailAlloc_956_, 4, v_diag_946_);
v___x_952_ = v_reuseFailAlloc_956_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_953_ = lean_st_ref_set(v___y_939_, v___x_952_);
v___x_954_ = lean_box(0);
v___x_955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_955_, 0, v___x_954_);
return v___x_955_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_setFVarType___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2___redArg___boxed(lean_object* v_mvarId_958_, lean_object* v_fvarId_959_, lean_object* v_type_960_, lean_object* v___y_961_, lean_object* v___y_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l_Lean_MVarId_setFVarType___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2___redArg(v_mvarId_958_, v_fvarId_959_, v_type_960_, v___y_961_);
lean_dec(v___y_961_);
return v_res_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_setFVarType___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2(lean_object* v_mvarId_964_, lean_object* v_fvarId_965_, lean_object* v_type_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_){
_start:
{
lean_object* v___x_972_; 
v___x_972_ = l_Lean_MVarId_setFVarType___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2___redArg(v_mvarId_964_, v_fvarId_965_, v_type_966_, v___y_968_);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_setFVarType___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2___boxed(lean_object* v_mvarId_973_, lean_object* v_fvarId_974_, lean_object* v_type_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_){
_start:
{
lean_object* v_res_981_; 
v_res_981_ = l_Lean_MVarId_setFVarType___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2(v_mvarId_973_, v_fvarId_974_, v_type_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_);
lean_dec(v___y_979_);
lean_dec_ref(v___y_978_);
lean_dec(v___y_977_);
lean_dec_ref(v___y_976_);
return v_res_981_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceLocalDeclDefEq___lam__0(lean_object* v_mvarId_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_){
_start:
{
lean_object* v___x_988_; 
lean_inc(v_mvarId_982_);
v___x_988_ = l_Lean_MVarId_getDecl(v_mvarId_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_);
if (lean_obj_tag(v___x_988_) == 0)
{
lean_object* v_a_989_; lean_object* v_userName_990_; lean_object* v_type_991_; uint8_t v_kind_992_; lean_object* v___x_993_; lean_object* v___x_994_; 
v_a_989_ = lean_ctor_get(v___x_988_, 0);
lean_inc(v_a_989_);
lean_dec_ref(v___x_988_);
v_userName_990_ = lean_ctor_get(v_a_989_, 0);
lean_inc(v_userName_990_);
v_type_991_ = lean_ctor_get(v_a_989_, 2);
lean_inc_ref(v_type_991_);
v_kind_992_ = lean_ctor_get_uint8(v_a_989_, sizeof(void*)*7);
lean_dec(v_a_989_);
v___x_993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_993_, 0, v_type_991_);
v___x_994_ = l_Lean_Meta_mkFreshExprMVar(v___x_993_, v_kind_992_, v_userName_990_, v___y_983_, v___y_984_, v___y_985_, v___y_986_);
if (lean_obj_tag(v___x_994_) == 0)
{
lean_object* v_a_995_; lean_object* v___x_996_; lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1004_; 
v_a_995_ = lean_ctor_get(v___x_994_, 0);
lean_inc_n(v_a_995_, 2);
lean_dec_ref(v___x_994_);
v___x_996_ = l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0___redArg(v_mvarId_982_, v_a_995_, v___y_984_);
v_isSharedCheck_1004_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1004_ == 0)
{
lean_object* v_unused_1005_; 
v_unused_1005_ = lean_ctor_get(v___x_996_, 0);
lean_dec(v_unused_1005_);
v___x_998_ = v___x_996_;
v_isShared_999_ = v_isSharedCheck_1004_;
goto v_resetjp_997_;
}
else
{
lean_dec(v___x_996_);
v___x_998_ = lean_box(0);
v_isShared_999_ = v_isSharedCheck_1004_;
goto v_resetjp_997_;
}
v_resetjp_997_:
{
lean_object* v___x_1000_; lean_object* v___x_1002_; 
v___x_1000_ = l_Lean_Expr_mvarId_x21(v_a_995_);
lean_dec(v_a_995_);
if (v_isShared_999_ == 0)
{
lean_ctor_set(v___x_998_, 0, v___x_1000_);
v___x_1002_ = v___x_998_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v___x_1000_);
v___x_1002_ = v_reuseFailAlloc_1003_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
return v___x_1002_;
}
}
}
else
{
lean_object* v_a_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1013_; 
lean_dec(v_mvarId_982_);
v_a_1006_ = lean_ctor_get(v___x_994_, 0);
v_isSharedCheck_1013_ = !lean_is_exclusive(v___x_994_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_1008_ = v___x_994_;
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_a_1006_);
lean_dec(v___x_994_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v___x_1011_; 
if (v_isShared_1009_ == 0)
{
v___x_1011_ = v___x_1008_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v_a_1006_);
v___x_1011_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
return v___x_1011_;
}
}
}
}
else
{
lean_object* v_a_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1021_; 
lean_dec(v_mvarId_982_);
v_a_1014_ = lean_ctor_get(v___x_988_, 0);
v_isSharedCheck_1021_ = !lean_is_exclusive(v___x_988_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_1016_ = v___x_988_;
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_a_1014_);
lean_dec(v___x_988_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1019_; 
if (v_isShared_1017_ == 0)
{
v___x_1019_ = v___x_1016_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v_a_1014_);
v___x_1019_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
return v___x_1019_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceLocalDeclDefEq___lam__0___boxed(lean_object* v_mvarId_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_){
_start:
{
lean_object* v_res_1028_; 
v_res_1028_ = l_Lean_MVarId_replaceLocalDeclDefEq___lam__0(v_mvarId_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_);
lean_dec(v___y_1026_);
lean_dec_ref(v___y_1025_);
lean_dec(v___y_1024_);
lean_dec_ref(v___y_1023_);
return v_res_1028_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceLocalDeclDefEq___lam__1(lean_object* v_fvarId_1029_, lean_object* v_typeNew_1030_, lean_object* v___f_1031_, lean_object* v_mvarId_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_){
_start:
{
lean_object* v___x_1038_; 
lean_inc(v_fvarId_1029_);
v___x_1038_ = l_Lean_FVarId_getType___redArg(v_fvarId_1029_, v___y_1033_, v___y_1035_, v___y_1036_);
if (lean_obj_tag(v___x_1038_) == 0)
{
lean_object* v_a_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1068_; 
v_a_1039_ = lean_ctor_get(v___x_1038_, 0);
v_isSharedCheck_1068_ = !lean_is_exclusive(v___x_1038_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_1041_ = v___x_1038_;
v_isShared_1042_ = v_isSharedCheck_1068_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_a_1039_);
lean_dec(v___x_1038_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1068_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
uint8_t v___x_1043_; 
v___x_1043_ = lean_expr_equal(v_a_1039_, v_typeNew_1030_);
if (v___x_1043_ == 0)
{
lean_object* v___x_1044_; lean_object* v_a_1045_; lean_object* v___x_1046_; lean_object* v_a_1047_; uint8_t v___x_1048_; 
lean_del_object(v___x_1041_);
v___x_1044_ = l_Lean_instantiateMVars___at___00Lean_MVarId_replaceTargetDefEq_spec__0___redArg(v_a_1039_, v___y_1034_);
v_a_1045_ = lean_ctor_get(v___x_1044_, 0);
lean_inc(v_a_1045_);
lean_dec_ref(v___x_1044_);
v___x_1046_ = l_Lean_instantiateMVars___at___00Lean_MVarId_replaceTargetDefEq_spec__0___redArg(v_typeNew_1030_, v___y_1034_);
v_a_1047_ = lean_ctor_get(v___x_1046_, 0);
lean_inc(v_a_1047_);
lean_dec_ref(v___x_1046_);
v___x_1048_ = lean_expr_equal(v_a_1045_, v_a_1047_);
if (v___x_1048_ == 0)
{
lean_object* v_lctx_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; 
lean_dec(v_a_1045_);
lean_dec(v_mvarId_1032_);
v_lctx_1049_ = lean_ctor_get(v___y_1033_, 2);
lean_inc(v_fvarId_1029_);
lean_inc_ref(v_lctx_1049_);
v___x_1050_ = l_Lean_LocalContext_setType(v_lctx_1049_, v_fvarId_1029_, v_a_1047_);
lean_inc_ref(v___x_1050_);
v___x_1051_ = l_Lean_LocalContext_get_x21(v___x_1050_, v_fvarId_1029_);
v___x_1052_ = lean_box(0);
v___x_1053_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1051_);
lean_ctor_set(v___x_1053_, 1, v___x_1052_);
v___x_1054_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalInstances___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__0___boxed), 8, 3);
lean_closure_set(v___x_1054_, 0, lean_box(0));
lean_closure_set(v___x_1054_, 1, v___x_1053_);
lean_closure_set(v___x_1054_, 2, v___f_1031_);
v___x_1055_ = l_Lean_Meta_withLCtx_x27___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__1___redArg(v___x_1050_, v___x_1054_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_);
lean_dec_ref(v___y_1033_);
return v___x_1055_;
}
else
{
lean_object* v___x_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1063_; 
lean_dec(v_a_1047_);
lean_dec_ref(v___y_1033_);
lean_dec_ref(v___f_1031_);
lean_inc(v_mvarId_1032_);
v___x_1056_ = l_Lean_MVarId_setFVarType___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2___redArg(v_mvarId_1032_, v_fvarId_1029_, v_a_1045_, v___y_1034_);
v_isSharedCheck_1063_ = !lean_is_exclusive(v___x_1056_);
if (v_isSharedCheck_1063_ == 0)
{
lean_object* v_unused_1064_; 
v_unused_1064_ = lean_ctor_get(v___x_1056_, 0);
lean_dec(v_unused_1064_);
v___x_1058_ = v___x_1056_;
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
else
{
lean_dec(v___x_1056_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1061_; 
if (v_isShared_1059_ == 0)
{
lean_ctor_set(v___x_1058_, 0, v_mvarId_1032_);
v___x_1061_ = v___x_1058_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_mvarId_1032_);
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
lean_object* v___x_1066_; 
lean_dec(v_a_1039_);
lean_dec_ref(v___y_1033_);
lean_dec_ref(v___f_1031_);
lean_dec_ref(v_typeNew_1030_);
lean_dec(v_fvarId_1029_);
if (v_isShared_1042_ == 0)
{
lean_ctor_set(v___x_1041_, 0, v_mvarId_1032_);
v___x_1066_ = v___x_1041_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v_mvarId_1032_);
v___x_1066_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
return v___x_1066_;
}
}
}
}
else
{
lean_object* v_a_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1076_; 
lean_dec_ref(v___y_1033_);
lean_dec(v_mvarId_1032_);
lean_dec_ref(v___f_1031_);
lean_dec_ref(v_typeNew_1030_);
lean_dec(v_fvarId_1029_);
v_a_1069_ = lean_ctor_get(v___x_1038_, 0);
v_isSharedCheck_1076_ = !lean_is_exclusive(v___x_1038_);
if (v_isSharedCheck_1076_ == 0)
{
v___x_1071_ = v___x_1038_;
v_isShared_1072_ = v_isSharedCheck_1076_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_a_1069_);
lean_dec(v___x_1038_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1076_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v___x_1074_; 
if (v_isShared_1072_ == 0)
{
v___x_1074_ = v___x_1071_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v_a_1069_);
v___x_1074_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
return v___x_1074_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceLocalDeclDefEq___lam__1___boxed(lean_object* v_fvarId_1077_, lean_object* v_typeNew_1078_, lean_object* v___f_1079_, lean_object* v_mvarId_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_){
_start:
{
lean_object* v_res_1086_; 
v_res_1086_ = l_Lean_MVarId_replaceLocalDeclDefEq___lam__1(v_fvarId_1077_, v_typeNew_1078_, v___f_1079_, v_mvarId_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_);
lean_dec(v___y_1084_);
lean_dec_ref(v___y_1083_);
lean_dec(v___y_1082_);
return v_res_1086_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceLocalDeclDefEq(lean_object* v_mvarId_1087_, lean_object* v_fvarId_1088_, lean_object* v_typeNew_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_){
_start:
{
lean_object* v___f_1095_; lean_object* v___f_1096_; lean_object* v___x_1097_; 
lean_inc_n(v_mvarId_1087_, 2);
v___f_1095_ = lean_alloc_closure((void*)(l_Lean_MVarId_replaceLocalDeclDefEq___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1095_, 0, v_mvarId_1087_);
v___f_1096_ = lean_alloc_closure((void*)(l_Lean_MVarId_replaceLocalDeclDefEq___lam__1___boxed), 9, 4);
lean_closure_set(v___f_1096_, 0, v_fvarId_1088_);
lean_closure_set(v___f_1096_, 1, v_typeNew_1089_);
lean_closure_set(v___f_1096_, 2, v___f_1095_);
lean_closure_set(v___f_1096_, 3, v_mvarId_1087_);
v___x_1097_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(v_mvarId_1087_, v___f_1096_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_);
return v___x_1097_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceLocalDeclDefEq___boxed(lean_object* v_mvarId_1098_, lean_object* v_fvarId_1099_, lean_object* v_typeNew_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_){
_start:
{
lean_object* v_res_1106_; 
v_res_1106_ = l_Lean_MVarId_replaceLocalDeclDefEq(v_mvarId_1098_, v_fvarId_1099_, v_typeNew_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_);
lean_dec(v_a_1104_);
lean_dec_ref(v_a_1103_);
lean_dec(v_a_1102_);
lean_dec_ref(v_a_1101_);
return v_res_1106_;
}
}
static lean_object* _init_l_Lean_MVarId_change___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; 
v___x_1108_ = ((lean_object*)(l_Lean_MVarId_change___lam__0___closed__0));
v___x_1109_ = l_Lean_stringToMessageData(v___x_1108_);
return v___x_1109_;
}
}
static lean_object* _init_l_Lean_MVarId_change___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1111_ = ((lean_object*)(l_Lean_MVarId_change___lam__0___closed__2));
v___x_1112_ = l_Lean_stringToMessageData(v___x_1111_);
return v___x_1112_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_change___lam__0(lean_object* v_mvarId_1113_, uint8_t v_checkDefEq_1114_, lean_object* v_targetNew_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_){
_start:
{
lean_object* v___x_1121_; 
lean_inc(v_mvarId_1113_);
v___x_1121_ = l_Lean_MVarId_getType(v_mvarId_1113_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_);
if (lean_obj_tag(v___x_1121_) == 0)
{
if (v_checkDefEq_1114_ == 0)
{
lean_object* v___x_1122_; 
lean_dec_ref(v___x_1121_);
v___x_1122_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_1113_, v_targetNew_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_);
return v___x_1122_;
}
else
{
lean_object* v_a_1123_; lean_object* v___x_1124_; 
v_a_1123_ = lean_ctor_get(v___x_1121_, 0);
lean_inc_n(v_a_1123_, 2);
lean_dec_ref(v___x_1121_);
lean_inc_ref(v_targetNew_1115_);
v___x_1124_ = l_Lean_Meta_isExprDefEq(v_a_1123_, v_targetNew_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_);
if (lean_obj_tag(v___x_1124_) == 0)
{
lean_object* v_a_1125_; uint8_t v___x_1126_; 
v_a_1125_ = lean_ctor_get(v___x_1124_, 0);
lean_inc(v_a_1125_);
lean_dec_ref(v___x_1124_);
v___x_1126_ = lean_unbox(v_a_1125_);
lean_dec(v_a_1125_);
if (v___x_1126_ == 0)
{
lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1127_ = ((lean_object*)(l_Lean_MVarId_replaceTargetDefEq___closed__1));
v___x_1128_ = lean_obj_once(&l_Lean_MVarId_change___lam__0___closed__1, &l_Lean_MVarId_change___lam__0___closed__1_once, _init_l_Lean_MVarId_change___lam__0___closed__1);
lean_inc_ref(v_targetNew_1115_);
v___x_1129_ = l_Lean_indentExpr(v_targetNew_1115_);
v___x_1130_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1130_, 0, v___x_1128_);
lean_ctor_set(v___x_1130_, 1, v___x_1129_);
v___x_1131_ = lean_obj_once(&l_Lean_MVarId_change___lam__0___closed__3, &l_Lean_MVarId_change___lam__0___closed__3_once, _init_l_Lean_MVarId_change___lam__0___closed__3);
v___x_1132_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1132_, 0, v___x_1130_);
lean_ctor_set(v___x_1132_, 1, v___x_1131_);
v___x_1133_ = l_Lean_indentExpr(v_a_1123_);
v___x_1134_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1134_, 0, v___x_1132_);
lean_ctor_set(v___x_1134_, 1, v___x_1133_);
v___x_1135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1135_, 0, v___x_1134_);
lean_inc(v_mvarId_1113_);
v___x_1136_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1127_, v_mvarId_1113_, v___x_1135_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_);
if (lean_obj_tag(v___x_1136_) == 0)
{
lean_object* v___x_1137_; 
lean_dec_ref(v___x_1136_);
v___x_1137_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_1113_, v_targetNew_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_);
return v___x_1137_;
}
else
{
lean_object* v_a_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1145_; 
lean_dec_ref(v_targetNew_1115_);
lean_dec(v_mvarId_1113_);
v_a_1138_ = lean_ctor_get(v___x_1136_, 0);
v_isSharedCheck_1145_ = !lean_is_exclusive(v___x_1136_);
if (v_isSharedCheck_1145_ == 0)
{
v___x_1140_ = v___x_1136_;
v_isShared_1141_ = v_isSharedCheck_1145_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_a_1138_);
lean_dec(v___x_1136_);
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
else
{
lean_object* v___x_1146_; 
lean_dec(v_a_1123_);
v___x_1146_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_1113_, v_targetNew_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_);
return v___x_1146_;
}
}
else
{
lean_object* v_a_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1154_; 
lean_dec(v_a_1123_);
lean_dec_ref(v_targetNew_1115_);
lean_dec(v_mvarId_1113_);
v_a_1147_ = lean_ctor_get(v___x_1124_, 0);
v_isSharedCheck_1154_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1149_ = v___x_1124_;
v_isShared_1150_ = v_isSharedCheck_1154_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_a_1147_);
lean_dec(v___x_1124_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1154_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
lean_object* v___x_1152_; 
if (v_isShared_1150_ == 0)
{
v___x_1152_ = v___x_1149_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v_a_1147_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
return v___x_1152_;
}
}
}
}
}
else
{
lean_object* v_a_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1162_; 
lean_dec_ref(v_targetNew_1115_);
lean_dec(v_mvarId_1113_);
v_a_1155_ = lean_ctor_get(v___x_1121_, 0);
v_isSharedCheck_1162_ = !lean_is_exclusive(v___x_1121_);
if (v_isSharedCheck_1162_ == 0)
{
v___x_1157_ = v___x_1121_;
v_isShared_1158_ = v_isSharedCheck_1162_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_a_1155_);
lean_dec(v___x_1121_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1162_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v___x_1160_; 
if (v_isShared_1158_ == 0)
{
v___x_1160_ = v___x_1157_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v_a_1155_);
v___x_1160_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
return v___x_1160_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_change___lam__0___boxed(lean_object* v_mvarId_1163_, lean_object* v_checkDefEq_1164_, lean_object* v_targetNew_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_){
_start:
{
uint8_t v_checkDefEq_boxed_1171_; lean_object* v_res_1172_; 
v_checkDefEq_boxed_1171_ = lean_unbox(v_checkDefEq_1164_);
v_res_1172_ = l_Lean_MVarId_change___lam__0(v_mvarId_1163_, v_checkDefEq_boxed_1171_, v_targetNew_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_);
lean_dec(v___y_1169_);
lean_dec_ref(v___y_1168_);
lean_dec(v___y_1167_);
lean_dec_ref(v___y_1166_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_change(lean_object* v_mvarId_1173_, lean_object* v_targetNew_1174_, uint8_t v_checkDefEq_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_){
_start:
{
lean_object* v___x_1181_; lean_object* v___f_1182_; lean_object* v___x_1183_; 
v___x_1181_ = lean_box(v_checkDefEq_1175_);
lean_inc(v_mvarId_1173_);
v___f_1182_ = lean_alloc_closure((void*)(l_Lean_MVarId_change___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1182_, 0, v_mvarId_1173_);
lean_closure_set(v___f_1182_, 1, v___x_1181_);
lean_closure_set(v___f_1182_, 2, v_targetNew_1174_);
v___x_1183_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(v_mvarId_1173_, v___f_1182_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_);
return v___x_1183_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_change___boxed(lean_object* v_mvarId_1184_, lean_object* v_targetNew_1185_, lean_object* v_checkDefEq_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_){
_start:
{
uint8_t v_checkDefEq_boxed_1192_; lean_object* v_res_1193_; 
v_checkDefEq_boxed_1192_ = lean_unbox(v_checkDefEq_1186_);
v_res_1193_ = l_Lean_MVarId_change(v_mvarId_1184_, v_targetNew_1185_, v_checkDefEq_boxed_1192_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_);
lean_dec(v_a_1190_);
lean_dec_ref(v_a_1189_);
lean_dec(v_a_1188_);
lean_dec_ref(v_a_1187_);
return v_res_1193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0_spec__0___redArg(lean_object* v_t_1194_, lean_object* v___y_1195_){
_start:
{
lean_object* v___x_1197_; lean_object* v_infoState_1198_; uint8_t v_enabled_1199_; 
v___x_1197_ = lean_st_ref_get(v___y_1195_);
v_infoState_1198_ = lean_ctor_get(v___x_1197_, 7);
lean_inc_ref(v_infoState_1198_);
lean_dec(v___x_1197_);
v_enabled_1199_ = lean_ctor_get_uint8(v_infoState_1198_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1198_);
if (v_enabled_1199_ == 0)
{
lean_object* v___x_1200_; lean_object* v___x_1201_; 
lean_dec_ref(v_t_1194_);
v___x_1200_ = lean_box(0);
v___x_1201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1201_, 0, v___x_1200_);
return v___x_1201_;
}
else
{
lean_object* v___x_1202_; lean_object* v_infoState_1203_; lean_object* v_env_1204_; lean_object* v_nextMacroScope_1205_; lean_object* v_ngen_1206_; lean_object* v_auxDeclNGen_1207_; lean_object* v_traceState_1208_; lean_object* v_cache_1209_; lean_object* v_messages_1210_; lean_object* v_snapshotTasks_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1233_; 
v___x_1202_ = lean_st_ref_take(v___y_1195_);
v_infoState_1203_ = lean_ctor_get(v___x_1202_, 7);
v_env_1204_ = lean_ctor_get(v___x_1202_, 0);
v_nextMacroScope_1205_ = lean_ctor_get(v___x_1202_, 1);
v_ngen_1206_ = lean_ctor_get(v___x_1202_, 2);
v_auxDeclNGen_1207_ = lean_ctor_get(v___x_1202_, 3);
v_traceState_1208_ = lean_ctor_get(v___x_1202_, 4);
v_cache_1209_ = lean_ctor_get(v___x_1202_, 5);
v_messages_1210_ = lean_ctor_get(v___x_1202_, 6);
v_snapshotTasks_1211_ = lean_ctor_get(v___x_1202_, 8);
v_isSharedCheck_1233_ = !lean_is_exclusive(v___x_1202_);
if (v_isSharedCheck_1233_ == 0)
{
v___x_1213_ = v___x_1202_;
v_isShared_1214_ = v_isSharedCheck_1233_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_snapshotTasks_1211_);
lean_inc(v_infoState_1203_);
lean_inc(v_messages_1210_);
lean_inc(v_cache_1209_);
lean_inc(v_traceState_1208_);
lean_inc(v_auxDeclNGen_1207_);
lean_inc(v_ngen_1206_);
lean_inc(v_nextMacroScope_1205_);
lean_inc(v_env_1204_);
lean_dec(v___x_1202_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1233_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
uint8_t v_enabled_1215_; lean_object* v_assignment_1216_; lean_object* v_lazyAssignment_1217_; lean_object* v_trees_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1232_; 
v_enabled_1215_ = lean_ctor_get_uint8(v_infoState_1203_, sizeof(void*)*3);
v_assignment_1216_ = lean_ctor_get(v_infoState_1203_, 0);
v_lazyAssignment_1217_ = lean_ctor_get(v_infoState_1203_, 1);
v_trees_1218_ = lean_ctor_get(v_infoState_1203_, 2);
v_isSharedCheck_1232_ = !lean_is_exclusive(v_infoState_1203_);
if (v_isSharedCheck_1232_ == 0)
{
v___x_1220_ = v_infoState_1203_;
v_isShared_1221_ = v_isSharedCheck_1232_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_trees_1218_);
lean_inc(v_lazyAssignment_1217_);
lean_inc(v_assignment_1216_);
lean_dec(v_infoState_1203_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1232_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v___x_1222_; lean_object* v___x_1224_; 
v___x_1222_ = l_Lean_PersistentArray_push___redArg(v_trees_1218_, v_t_1194_);
if (v_isShared_1221_ == 0)
{
lean_ctor_set(v___x_1220_, 2, v___x_1222_);
v___x_1224_ = v___x_1220_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v_assignment_1216_);
lean_ctor_set(v_reuseFailAlloc_1231_, 1, v_lazyAssignment_1217_);
lean_ctor_set(v_reuseFailAlloc_1231_, 2, v___x_1222_);
lean_ctor_set_uint8(v_reuseFailAlloc_1231_, sizeof(void*)*3, v_enabled_1215_);
v___x_1224_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
lean_object* v___x_1226_; 
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 7, v___x_1224_);
v___x_1226_ = v___x_1213_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v_env_1204_);
lean_ctor_set(v_reuseFailAlloc_1230_, 1, v_nextMacroScope_1205_);
lean_ctor_set(v_reuseFailAlloc_1230_, 2, v_ngen_1206_);
lean_ctor_set(v_reuseFailAlloc_1230_, 3, v_auxDeclNGen_1207_);
lean_ctor_set(v_reuseFailAlloc_1230_, 4, v_traceState_1208_);
lean_ctor_set(v_reuseFailAlloc_1230_, 5, v_cache_1209_);
lean_ctor_set(v_reuseFailAlloc_1230_, 6, v_messages_1210_);
lean_ctor_set(v_reuseFailAlloc_1230_, 7, v___x_1224_);
lean_ctor_set(v_reuseFailAlloc_1230_, 8, v_snapshotTasks_1211_);
v___x_1226_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; 
v___x_1227_ = lean_st_ref_set(v___y_1195_, v___x_1226_);
v___x_1228_ = lean_box(0);
v___x_1229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1229_, 0, v___x_1228_);
return v___x_1229_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0_spec__0___redArg___boxed(lean_object* v_t_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_){
_start:
{
lean_object* v_res_1237_; 
v_res_1237_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0_spec__0___redArg(v_t_1234_, v___y_1235_);
lean_dec(v___y_1235_);
return v_res_1237_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; 
v___x_1238_ = lean_unsigned_to_nat(32u);
v___x_1239_ = lean_mk_empty_array_with_capacity(v___x_1238_);
v___x_1240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1240_, 0, v___x_1239_);
return v___x_1240_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0___closed__1(void){
_start:
{
size_t v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; 
v___x_1241_ = ((size_t)5ULL);
v___x_1242_ = lean_unsigned_to_nat(0u);
v___x_1243_ = lean_unsigned_to_nat(32u);
v___x_1244_ = lean_mk_empty_array_with_capacity(v___x_1243_);
v___x_1245_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0___closed__0);
v___x_1246_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1246_, 0, v___x_1245_);
lean_ctor_set(v___x_1246_, 1, v___x_1244_);
lean_ctor_set(v___x_1246_, 2, v___x_1242_);
lean_ctor_set(v___x_1246_, 3, v___x_1242_);
lean_ctor_set_usize(v___x_1246_, 4, v___x_1241_);
return v___x_1246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0(lean_object* v_t_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_){
_start:
{
lean_object* v___x_1253_; lean_object* v_infoState_1254_; uint8_t v_enabled_1255_; 
v___x_1253_ = lean_st_ref_get(v___y_1251_);
v_infoState_1254_ = lean_ctor_get(v___x_1253_, 7);
lean_inc_ref(v_infoState_1254_);
lean_dec(v___x_1253_);
v_enabled_1255_ = lean_ctor_get_uint8(v_infoState_1254_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1254_);
if (v_enabled_1255_ == 0)
{
lean_object* v___x_1256_; lean_object* v___x_1257_; 
lean_dec_ref(v_t_1247_);
v___x_1256_ = lean_box(0);
v___x_1257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1257_, 0, v___x_1256_);
return v___x_1257_;
}
else
{
lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; 
v___x_1258_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0___closed__1);
v___x_1259_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1259_, 0, v_t_1247_);
lean_ctor_set(v___x_1259_, 1, v___x_1258_);
v___x_1260_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0_spec__0___redArg(v___x_1259_, v___y_1251_);
return v___x_1260_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0___boxed(lean_object* v_t_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_){
_start:
{
lean_object* v_res_1267_; 
v_res_1267_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0(v_t_1261_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_);
lean_dec(v___y_1265_);
lean_dec_ref(v___y_1264_);
lean_dec(v___y_1263_);
lean_dec_ref(v___y_1262_);
return v_res_1267_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_withReverted_spec__1(lean_object* v_as_1268_, size_t v_sz_1269_, size_t v_i_1270_, lean_object* v_b_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_){
_start:
{
lean_object* v_a_1278_; uint8_t v___x_1282_; 
v___x_1282_ = lean_usize_dec_lt(v_i_1270_, v_sz_1269_);
if (v___x_1282_ == 0)
{
lean_object* v___x_1283_; 
v___x_1283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1283_, 0, v_b_1271_);
return v___x_1283_;
}
else
{
lean_object* v_array_1284_; lean_object* v_start_1285_; lean_object* v_stop_1286_; uint8_t v___x_1287_; 
v_array_1284_ = lean_ctor_get(v_b_1271_, 0);
v_start_1285_ = lean_ctor_get(v_b_1271_, 1);
v_stop_1286_ = lean_ctor_get(v_b_1271_, 2);
v___x_1287_ = lean_nat_dec_lt(v_start_1285_, v_stop_1286_);
if (v___x_1287_ == 0)
{
lean_object* v___x_1288_; 
v___x_1288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1288_, 0, v_b_1271_);
return v___x_1288_;
}
else
{
lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1327_; 
lean_inc(v_stop_1286_);
lean_inc(v_start_1285_);
lean_inc_ref(v_array_1284_);
v_isSharedCheck_1327_ = !lean_is_exclusive(v_b_1271_);
if (v_isSharedCheck_1327_ == 0)
{
lean_object* v_unused_1328_; lean_object* v_unused_1329_; lean_object* v_unused_1330_; 
v_unused_1328_ = lean_ctor_get(v_b_1271_, 2);
lean_dec(v_unused_1328_);
v_unused_1329_ = lean_ctor_get(v_b_1271_, 1);
lean_dec(v_unused_1329_);
v_unused_1330_ = lean_ctor_get(v_b_1271_, 0);
lean_dec(v_unused_1330_);
v___x_1290_ = v_b_1271_;
v_isShared_1291_ = v_isSharedCheck_1327_;
goto v_resetjp_1289_;
}
else
{
lean_dec(v_b_1271_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1327_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v_a_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1297_; 
v_a_1292_ = lean_array_uget(v_as_1268_, v_i_1270_);
v___x_1293_ = lean_array_fget(v_array_1284_, v_start_1285_);
v___x_1294_ = lean_unsigned_to_nat(1u);
v___x_1295_ = lean_nat_add(v_start_1285_, v___x_1294_);
lean_dec(v_start_1285_);
if (v_isShared_1291_ == 0)
{
lean_ctor_set(v___x_1290_, 1, v___x_1295_);
v___x_1297_ = v___x_1290_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v_array_1284_);
lean_ctor_set(v_reuseFailAlloc_1326_, 1, v___x_1295_);
lean_ctor_set(v_reuseFailAlloc_1326_, 2, v_stop_1286_);
v___x_1297_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
if (lean_obj_tag(v_a_1292_) == 1)
{
lean_object* v_val_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1325_; 
v_val_1298_ = lean_ctor_get(v_a_1292_, 0);
v_isSharedCheck_1325_ = !lean_is_exclusive(v_a_1292_);
if (v_isSharedCheck_1325_ == 0)
{
v___x_1300_ = v_a_1292_;
v_isShared_1301_ = v_isSharedCheck_1325_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_val_1298_);
lean_dec(v_a_1292_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1325_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
lean_object* v___x_1302_; 
lean_inc(v___x_1293_);
v___x_1302_ = l_Lean_FVarId_getUserName___redArg(v___x_1293_, v___y_1272_, v___y_1274_, v___y_1275_);
if (lean_obj_tag(v___x_1302_) == 0)
{
lean_object* v_a_1303_; lean_object* v___x_1304_; lean_object* v___x_1306_; 
v_a_1303_ = lean_ctor_get(v___x_1302_, 0);
lean_inc(v_a_1303_);
lean_dec_ref(v___x_1302_);
v___x_1304_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1304_, 0, v_a_1303_);
lean_ctor_set(v___x_1304_, 1, v___x_1293_);
lean_ctor_set(v___x_1304_, 2, v_val_1298_);
if (v_isShared_1301_ == 0)
{
lean_ctor_set_tag(v___x_1300_, 11);
lean_ctor_set(v___x_1300_, 0, v___x_1304_);
v___x_1306_ = v___x_1300_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v___x_1304_);
v___x_1306_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
lean_object* v___x_1307_; 
v___x_1307_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0(v___x_1306_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_);
if (lean_obj_tag(v___x_1307_) == 0)
{
lean_dec_ref(v___x_1307_);
v_a_1278_ = v___x_1297_;
goto v___jp_1277_;
}
else
{
lean_object* v_a_1308_; lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1315_; 
lean_dec_ref(v___x_1297_);
v_a_1308_ = lean_ctor_get(v___x_1307_, 0);
v_isSharedCheck_1315_ = !lean_is_exclusive(v___x_1307_);
if (v_isSharedCheck_1315_ == 0)
{
v___x_1310_ = v___x_1307_;
v_isShared_1311_ = v_isSharedCheck_1315_;
goto v_resetjp_1309_;
}
else
{
lean_inc(v_a_1308_);
lean_dec(v___x_1307_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1315_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
lean_object* v___x_1313_; 
if (v_isShared_1311_ == 0)
{
v___x_1313_ = v___x_1310_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1314_; 
v_reuseFailAlloc_1314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1314_, 0, v_a_1308_);
v___x_1313_ = v_reuseFailAlloc_1314_;
goto v_reusejp_1312_;
}
v_reusejp_1312_:
{
return v___x_1313_;
}
}
}
}
}
else
{
lean_object* v_a_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1324_; 
lean_del_object(v___x_1300_);
lean_dec(v_val_1298_);
lean_dec_ref(v___x_1297_);
lean_dec(v___x_1293_);
v_a_1317_ = lean_ctor_get(v___x_1302_, 0);
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1302_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1319_ = v___x_1302_;
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_a_1317_);
lean_dec(v___x_1302_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v___x_1322_; 
if (v_isShared_1320_ == 0)
{
v___x_1322_ = v___x_1319_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v_a_1317_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
return v___x_1322_;
}
}
}
}
}
else
{
lean_dec(v___x_1293_);
lean_dec(v_a_1292_);
v_a_1278_ = v___x_1297_;
goto v___jp_1277_;
}
}
}
}
}
v___jp_1277_:
{
size_t v___x_1279_; size_t v___x_1280_; 
v___x_1279_ = ((size_t)1ULL);
v___x_1280_ = lean_usize_add(v_i_1270_, v___x_1279_);
v_i_1270_ = v___x_1280_;
v_b_1271_ = v_a_1278_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_withReverted_spec__1___boxed(lean_object* v_as_1331_, lean_object* v_sz_1332_, lean_object* v_i_1333_, lean_object* v_b_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_){
_start:
{
size_t v_sz_boxed_1340_; size_t v_i_boxed_1341_; lean_object* v_res_1342_; 
v_sz_boxed_1340_ = lean_unbox_usize(v_sz_1332_);
lean_dec(v_sz_1332_);
v_i_boxed_1341_ = lean_unbox_usize(v_i_1333_);
lean_dec(v_i_1333_);
v_res_1342_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_withReverted_spec__1(v_as_1331_, v_sz_boxed_1340_, v_i_boxed_1341_, v_b_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_);
lean_dec(v___y_1338_);
lean_dec_ref(v___y_1337_);
lean_dec(v___y_1336_);
lean_dec_ref(v___y_1335_);
lean_dec_ref(v_as_1331_);
return v_res_1342_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withReverted___redArg___lam__0(lean_object* v_fst_1343_, size_t v_sz_1344_, size_t v___x_1345_, lean_object* v___x_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_){
_start:
{
lean_object* v___x_1352_; 
v___x_1352_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_withReverted_spec__1(v_fst_1343_, v_sz_1344_, v___x_1345_, v___x_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_);
if (lean_obj_tag(v___x_1352_) == 0)
{
lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1360_; 
v_isSharedCheck_1360_ = !lean_is_exclusive(v___x_1352_);
if (v_isSharedCheck_1360_ == 0)
{
lean_object* v_unused_1361_; 
v_unused_1361_ = lean_ctor_get(v___x_1352_, 0);
lean_dec(v_unused_1361_);
v___x_1354_ = v___x_1352_;
v_isShared_1355_ = v_isSharedCheck_1360_;
goto v_resetjp_1353_;
}
else
{
lean_dec(v___x_1352_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1360_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v___x_1356_; lean_object* v___x_1358_; 
v___x_1356_ = lean_box(0);
if (v_isShared_1355_ == 0)
{
lean_ctor_set(v___x_1354_, 0, v___x_1356_);
v___x_1358_ = v___x_1354_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v___x_1356_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
return v___x_1358_;
}
}
}
else
{
lean_object* v_a_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1369_; 
v_a_1362_ = lean_ctor_get(v___x_1352_, 0);
v_isSharedCheck_1369_ = !lean_is_exclusive(v___x_1352_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1364_ = v___x_1352_;
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_a_1362_);
lean_dec(v___x_1352_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v___x_1367_; 
if (v_isShared_1365_ == 0)
{
v___x_1367_ = v___x_1364_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v_a_1362_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withReverted___redArg___lam__0___boxed(lean_object* v_fst_1370_, lean_object* v_sz_1371_, lean_object* v___x_1372_, lean_object* v___x_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_){
_start:
{
size_t v_sz_boxed_1379_; size_t v___x_3386__boxed_1380_; lean_object* v_res_1381_; 
v_sz_boxed_1379_ = lean_unbox_usize(v_sz_1371_);
lean_dec(v_sz_1371_);
v___x_3386__boxed_1380_ = lean_unbox_usize(v___x_1372_);
lean_dec(v___x_1372_);
v_res_1381_ = l_Lean_MVarId_withReverted___redArg___lam__0(v_fst_1370_, v_sz_boxed_1379_, v___x_3386__boxed_1380_, v___x_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_);
lean_dec(v___y_1377_);
lean_dec_ref(v___y_1376_);
lean_dec(v___y_1375_);
lean_dec_ref(v___y_1374_);
lean_dec_ref(v_fst_1370_);
return v_res_1381_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withReverted___redArg(lean_object* v_mvarId_1384_, lean_object* v_fvarIds_1385_, lean_object* v_k_1386_, uint8_t v_clearAuxDeclsInsteadOfRevert_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_){
_start:
{
uint8_t v___x_1393_; lean_object* v___x_1394_; 
v___x_1393_ = 1;
v___x_1394_ = l_Lean_MVarId_revert(v_mvarId_1384_, v_fvarIds_1385_, v___x_1393_, v_clearAuxDeclsInsteadOfRevert_1387_, v_a_1388_, v_a_1389_, v_a_1390_, v_a_1391_);
if (lean_obj_tag(v___x_1394_) == 0)
{
lean_object* v_a_1395_; lean_object* v_fst_1396_; lean_object* v_snd_1397_; lean_object* v___x_1398_; 
v_a_1395_ = lean_ctor_get(v___x_1394_, 0);
lean_inc(v_a_1395_);
lean_dec_ref(v___x_1394_);
v_fst_1396_ = lean_ctor_get(v_a_1395_, 0);
lean_inc(v_fst_1396_);
v_snd_1397_ = lean_ctor_get(v_a_1395_, 1);
lean_inc(v_snd_1397_);
lean_dec(v_a_1395_);
lean_inc(v_a_1391_);
lean_inc_ref(v_a_1390_);
lean_inc(v_a_1389_);
lean_inc_ref(v_a_1388_);
v___x_1398_ = lean_apply_7(v_k_1386_, v_snd_1397_, v_fst_1396_, v_a_1388_, v_a_1389_, v_a_1390_, v_a_1391_, lean_box(0));
if (lean_obj_tag(v___x_1398_) == 0)
{
lean_object* v_a_1399_; lean_object* v_snd_1400_; lean_object* v_fst_1401_; lean_object* v_fst_1402_; lean_object* v_snd_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; uint8_t v___x_1406_; lean_object* v___x_1407_; 
v_a_1399_ = lean_ctor_get(v___x_1398_, 0);
lean_inc(v_a_1399_);
lean_dec_ref(v___x_1398_);
v_snd_1400_ = lean_ctor_get(v_a_1399_, 1);
lean_inc(v_snd_1400_);
v_fst_1401_ = lean_ctor_get(v_a_1399_, 0);
lean_inc(v_fst_1401_);
lean_dec(v_a_1399_);
v_fst_1402_ = lean_ctor_get(v_snd_1400_, 0);
lean_inc(v_fst_1402_);
v_snd_1403_ = lean_ctor_get(v_snd_1400_, 1);
lean_inc(v_snd_1403_);
lean_dec(v_snd_1400_);
v___x_1404_ = lean_array_get_size(v_fst_1402_);
v___x_1405_ = lean_box(0);
v___x_1406_ = 0;
v___x_1407_ = l_Lean_Meta_introNCore(v_snd_1403_, v___x_1404_, v___x_1405_, v___x_1406_, v___x_1393_, v_a_1388_, v_a_1389_, v_a_1390_, v_a_1391_);
if (lean_obj_tag(v___x_1407_) == 0)
{
lean_object* v_a_1408_; lean_object* v_fst_1409_; lean_object* v_snd_1410_; lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1441_; 
v_a_1408_ = lean_ctor_get(v___x_1407_, 0);
lean_inc(v_a_1408_);
lean_dec_ref(v___x_1407_);
v_fst_1409_ = lean_ctor_get(v_a_1408_, 0);
v_snd_1410_ = lean_ctor_get(v_a_1408_, 1);
v_isSharedCheck_1441_ = !lean_is_exclusive(v_a_1408_);
if (v_isSharedCheck_1441_ == 0)
{
v___x_1412_ = v_a_1408_;
v_isShared_1413_ = v_isSharedCheck_1441_;
goto v_resetjp_1411_;
}
else
{
lean_inc(v_snd_1410_);
lean_inc(v_fst_1409_);
lean_dec(v_a_1408_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1441_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; size_t v_sz_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___f_1420_; lean_object* v___x_1421_; 
v___x_1414_ = lean_unsigned_to_nat(0u);
v___x_1415_ = lean_array_get_size(v_fst_1409_);
v___x_1416_ = l_Array_toSubarray___redArg(v_fst_1409_, v___x_1414_, v___x_1415_);
v_sz_1417_ = lean_array_size(v_fst_1402_);
v___x_1418_ = lean_box_usize(v_sz_1417_);
v___x_1419_ = ((lean_object*)(l_Lean_MVarId_withReverted___redArg___boxed__const__1));
v___f_1420_ = lean_alloc_closure((void*)(l_Lean_MVarId_withReverted___redArg___lam__0___boxed), 9, 4);
lean_closure_set(v___f_1420_, 0, v_fst_1402_);
lean_closure_set(v___f_1420_, 1, v___x_1418_);
lean_closure_set(v___f_1420_, 2, v___x_1419_);
lean_closure_set(v___f_1420_, 3, v___x_1416_);
lean_inc(v_snd_1410_);
v___x_1421_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(v_snd_1410_, v___f_1420_, v_a_1388_, v_a_1389_, v_a_1390_, v_a_1391_);
if (lean_obj_tag(v___x_1421_) == 0)
{
lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1431_; 
v_isSharedCheck_1431_ = !lean_is_exclusive(v___x_1421_);
if (v_isSharedCheck_1431_ == 0)
{
lean_object* v_unused_1432_; 
v_unused_1432_ = lean_ctor_get(v___x_1421_, 0);
lean_dec(v_unused_1432_);
v___x_1423_ = v___x_1421_;
v_isShared_1424_ = v_isSharedCheck_1431_;
goto v_resetjp_1422_;
}
else
{
lean_dec(v___x_1421_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1431_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v___x_1426_; 
if (v_isShared_1413_ == 0)
{
lean_ctor_set(v___x_1412_, 0, v_fst_1401_);
v___x_1426_ = v___x_1412_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v_fst_1401_);
lean_ctor_set(v_reuseFailAlloc_1430_, 1, v_snd_1410_);
v___x_1426_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
lean_object* v___x_1428_; 
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 0, v___x_1426_);
v___x_1428_ = v___x_1423_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v___x_1426_);
v___x_1428_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
return v___x_1428_;
}
}
}
}
else
{
lean_object* v_a_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1440_; 
lean_del_object(v___x_1412_);
lean_dec(v_snd_1410_);
lean_dec(v_fst_1401_);
v_a_1433_ = lean_ctor_get(v___x_1421_, 0);
v_isSharedCheck_1440_ = !lean_is_exclusive(v___x_1421_);
if (v_isSharedCheck_1440_ == 0)
{
v___x_1435_ = v___x_1421_;
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_a_1433_);
lean_dec(v___x_1421_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v___x_1438_; 
if (v_isShared_1436_ == 0)
{
v___x_1438_ = v___x_1435_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v_a_1433_);
v___x_1438_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
return v___x_1438_;
}
}
}
}
}
else
{
lean_object* v_a_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1449_; 
lean_dec(v_fst_1402_);
lean_dec(v_fst_1401_);
v_a_1442_ = lean_ctor_get(v___x_1407_, 0);
v_isSharedCheck_1449_ = !lean_is_exclusive(v___x_1407_);
if (v_isSharedCheck_1449_ == 0)
{
v___x_1444_ = v___x_1407_;
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_a_1442_);
lean_dec(v___x_1407_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___x_1447_; 
if (v_isShared_1445_ == 0)
{
v___x_1447_ = v___x_1444_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v_a_1442_);
v___x_1447_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
return v___x_1447_;
}
}
}
}
else
{
lean_object* v_a_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1457_; 
v_a_1450_ = lean_ctor_get(v___x_1398_, 0);
v_isSharedCheck_1457_ = !lean_is_exclusive(v___x_1398_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1452_ = v___x_1398_;
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_a_1450_);
lean_dec(v___x_1398_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v___x_1455_; 
if (v_isShared_1453_ == 0)
{
v___x_1455_ = v___x_1452_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v_a_1450_);
v___x_1455_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
return v___x_1455_;
}
}
}
}
else
{
lean_object* v_a_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1465_; 
lean_dec_ref(v_k_1386_);
v_a_1458_ = lean_ctor_get(v___x_1394_, 0);
v_isSharedCheck_1465_ = !lean_is_exclusive(v___x_1394_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1460_ = v___x_1394_;
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_a_1458_);
lean_dec(v___x_1394_);
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
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withReverted___redArg___boxed(lean_object* v_mvarId_1466_, lean_object* v_fvarIds_1467_, lean_object* v_k_1468_, lean_object* v_clearAuxDeclsInsteadOfRevert_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_){
_start:
{
uint8_t v_clearAuxDeclsInsteadOfRevert_boxed_1475_; lean_object* v_res_1476_; 
v_clearAuxDeclsInsteadOfRevert_boxed_1475_ = lean_unbox(v_clearAuxDeclsInsteadOfRevert_1469_);
v_res_1476_ = l_Lean_MVarId_withReverted___redArg(v_mvarId_1466_, v_fvarIds_1467_, v_k_1468_, v_clearAuxDeclsInsteadOfRevert_boxed_1475_, v_a_1470_, v_a_1471_, v_a_1472_, v_a_1473_);
lean_dec(v_a_1473_);
lean_dec_ref(v_a_1472_);
lean_dec(v_a_1471_);
lean_dec_ref(v_a_1470_);
return v_res_1476_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withReverted(lean_object* v_00_u03b1_1477_, lean_object* v_mvarId_1478_, lean_object* v_fvarIds_1479_, lean_object* v_k_1480_, uint8_t v_clearAuxDeclsInsteadOfRevert_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_){
_start:
{
lean_object* v___x_1487_; 
v___x_1487_ = l_Lean_MVarId_withReverted___redArg(v_mvarId_1478_, v_fvarIds_1479_, v_k_1480_, v_clearAuxDeclsInsteadOfRevert_1481_, v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_);
return v___x_1487_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withReverted___boxed(lean_object* v_00_u03b1_1488_, lean_object* v_mvarId_1489_, lean_object* v_fvarIds_1490_, lean_object* v_k_1491_, lean_object* v_clearAuxDeclsInsteadOfRevert_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_){
_start:
{
uint8_t v_clearAuxDeclsInsteadOfRevert_boxed_1498_; lean_object* v_res_1499_; 
v_clearAuxDeclsInsteadOfRevert_boxed_1498_ = lean_unbox(v_clearAuxDeclsInsteadOfRevert_1492_);
v_res_1499_ = l_Lean_MVarId_withReverted(v_00_u03b1_1488_, v_mvarId_1489_, v_fvarIds_1490_, v_k_1491_, v_clearAuxDeclsInsteadOfRevert_boxed_1498_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_);
lean_dec(v_a_1496_);
lean_dec_ref(v_a_1495_);
lean_dec(v_a_1494_);
lean_dec_ref(v_a_1493_);
return v_res_1499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0_spec__0(lean_object* v_t_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_){
_start:
{
lean_object* v___x_1506_; 
v___x_1506_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0_spec__0___redArg(v_t_1500_, v___y_1504_);
return v___x_1506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0_spec__0___boxed(lean_object* v_t_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_){
_start:
{
lean_object* v_res_1513_; 
v_res_1513_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0_spec__0(v_t_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_);
lean_dec(v___y_1511_);
lean_dec_ref(v___y_1510_);
lean_dec(v___y_1509_);
lean_dec_ref(v___y_1508_);
return v_res_1513_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withRevertedFrom___redArg(lean_object* v_mvarId_1514_, lean_object* v_fvarId_1515_, lean_object* v_k_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_){
_start:
{
lean_object* v___x_1522_; 
v___x_1522_ = l_Lean_MVarId_revertFrom(v_mvarId_1514_, v_fvarId_1515_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_);
if (lean_obj_tag(v___x_1522_) == 0)
{
lean_object* v_a_1523_; lean_object* v_fst_1524_; lean_object* v_snd_1525_; lean_object* v___x_1526_; 
v_a_1523_ = lean_ctor_get(v___x_1522_, 0);
lean_inc(v_a_1523_);
lean_dec_ref(v___x_1522_);
v_fst_1524_ = lean_ctor_get(v_a_1523_, 0);
lean_inc(v_fst_1524_);
v_snd_1525_ = lean_ctor_get(v_a_1523_, 1);
lean_inc(v_snd_1525_);
lean_dec(v_a_1523_);
lean_inc(v_a_1520_);
lean_inc_ref(v_a_1519_);
lean_inc(v_a_1518_);
lean_inc_ref(v_a_1517_);
v___x_1526_ = lean_apply_7(v_k_1516_, v_snd_1525_, v_fst_1524_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_, lean_box(0));
if (lean_obj_tag(v___x_1526_) == 0)
{
lean_object* v_a_1527_; lean_object* v_snd_1528_; lean_object* v_fst_1529_; lean_object* v_fst_1530_; lean_object* v_snd_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; uint8_t v___x_1534_; uint8_t v___x_1535_; lean_object* v___x_1536_; 
v_a_1527_ = lean_ctor_get(v___x_1526_, 0);
lean_inc(v_a_1527_);
lean_dec_ref(v___x_1526_);
v_snd_1528_ = lean_ctor_get(v_a_1527_, 1);
lean_inc(v_snd_1528_);
v_fst_1529_ = lean_ctor_get(v_a_1527_, 0);
lean_inc(v_fst_1529_);
lean_dec(v_a_1527_);
v_fst_1530_ = lean_ctor_get(v_snd_1528_, 0);
lean_inc(v_fst_1530_);
v_snd_1531_ = lean_ctor_get(v_snd_1528_, 1);
lean_inc(v_snd_1531_);
lean_dec(v_snd_1528_);
v___x_1532_ = lean_array_get_size(v_fst_1530_);
v___x_1533_ = lean_box(0);
v___x_1534_ = 0;
v___x_1535_ = 1;
v___x_1536_ = l_Lean_Meta_introNCore(v_snd_1531_, v___x_1532_, v___x_1533_, v___x_1534_, v___x_1535_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_);
if (lean_obj_tag(v___x_1536_) == 0)
{
lean_object* v_a_1537_; lean_object* v_fst_1538_; lean_object* v_snd_1539_; lean_object* v___x_1541_; uint8_t v_isShared_1542_; uint8_t v_isSharedCheck_1570_; 
v_a_1537_ = lean_ctor_get(v___x_1536_, 0);
lean_inc(v_a_1537_);
lean_dec_ref(v___x_1536_);
v_fst_1538_ = lean_ctor_get(v_a_1537_, 0);
v_snd_1539_ = lean_ctor_get(v_a_1537_, 1);
v_isSharedCheck_1570_ = !lean_is_exclusive(v_a_1537_);
if (v_isSharedCheck_1570_ == 0)
{
v___x_1541_ = v_a_1537_;
v_isShared_1542_ = v_isSharedCheck_1570_;
goto v_resetjp_1540_;
}
else
{
lean_inc(v_snd_1539_);
lean_inc(v_fst_1538_);
lean_dec(v_a_1537_);
v___x_1541_ = lean_box(0);
v_isShared_1542_ = v_isSharedCheck_1570_;
goto v_resetjp_1540_;
}
v_resetjp_1540_:
{
lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; size_t v_sz_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___f_1549_; lean_object* v___x_1550_; 
v___x_1543_ = lean_unsigned_to_nat(0u);
v___x_1544_ = lean_array_get_size(v_fst_1538_);
v___x_1545_ = l_Array_toSubarray___redArg(v_fst_1538_, v___x_1543_, v___x_1544_);
v_sz_1546_ = lean_array_size(v_fst_1530_);
v___x_1547_ = lean_box_usize(v_sz_1546_);
v___x_1548_ = ((lean_object*)(l_Lean_MVarId_withReverted___redArg___boxed__const__1));
v___f_1549_ = lean_alloc_closure((void*)(l_Lean_MVarId_withReverted___redArg___lam__0___boxed), 9, 4);
lean_closure_set(v___f_1549_, 0, v_fst_1530_);
lean_closure_set(v___f_1549_, 1, v___x_1547_);
lean_closure_set(v___f_1549_, 2, v___x_1548_);
lean_closure_set(v___f_1549_, 3, v___x_1545_);
lean_inc(v_snd_1539_);
v___x_1550_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(v_snd_1539_, v___f_1549_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_);
if (lean_obj_tag(v___x_1550_) == 0)
{
lean_object* v___x_1552_; uint8_t v_isShared_1553_; uint8_t v_isSharedCheck_1560_; 
v_isSharedCheck_1560_ = !lean_is_exclusive(v___x_1550_);
if (v_isSharedCheck_1560_ == 0)
{
lean_object* v_unused_1561_; 
v_unused_1561_ = lean_ctor_get(v___x_1550_, 0);
lean_dec(v_unused_1561_);
v___x_1552_ = v___x_1550_;
v_isShared_1553_ = v_isSharedCheck_1560_;
goto v_resetjp_1551_;
}
else
{
lean_dec(v___x_1550_);
v___x_1552_ = lean_box(0);
v_isShared_1553_ = v_isSharedCheck_1560_;
goto v_resetjp_1551_;
}
v_resetjp_1551_:
{
lean_object* v___x_1555_; 
if (v_isShared_1542_ == 0)
{
lean_ctor_set(v___x_1541_, 0, v_fst_1529_);
v___x_1555_ = v___x_1541_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v_fst_1529_);
lean_ctor_set(v_reuseFailAlloc_1559_, 1, v_snd_1539_);
v___x_1555_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
lean_object* v___x_1557_; 
if (v_isShared_1553_ == 0)
{
lean_ctor_set(v___x_1552_, 0, v___x_1555_);
v___x_1557_ = v___x_1552_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v___x_1555_);
v___x_1557_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
return v___x_1557_;
}
}
}
}
else
{
lean_object* v_a_1562_; lean_object* v___x_1564_; uint8_t v_isShared_1565_; uint8_t v_isSharedCheck_1569_; 
lean_del_object(v___x_1541_);
lean_dec(v_snd_1539_);
lean_dec(v_fst_1529_);
v_a_1562_ = lean_ctor_get(v___x_1550_, 0);
v_isSharedCheck_1569_ = !lean_is_exclusive(v___x_1550_);
if (v_isSharedCheck_1569_ == 0)
{
v___x_1564_ = v___x_1550_;
v_isShared_1565_ = v_isSharedCheck_1569_;
goto v_resetjp_1563_;
}
else
{
lean_inc(v_a_1562_);
lean_dec(v___x_1550_);
v___x_1564_ = lean_box(0);
v_isShared_1565_ = v_isSharedCheck_1569_;
goto v_resetjp_1563_;
}
v_resetjp_1563_:
{
lean_object* v___x_1567_; 
if (v_isShared_1565_ == 0)
{
v___x_1567_ = v___x_1564_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1568_; 
v_reuseFailAlloc_1568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1568_, 0, v_a_1562_);
v___x_1567_ = v_reuseFailAlloc_1568_;
goto v_reusejp_1566_;
}
v_reusejp_1566_:
{
return v___x_1567_;
}
}
}
}
}
else
{
lean_object* v_a_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1578_; 
lean_dec(v_fst_1530_);
lean_dec(v_fst_1529_);
v_a_1571_ = lean_ctor_get(v___x_1536_, 0);
v_isSharedCheck_1578_ = !lean_is_exclusive(v___x_1536_);
if (v_isSharedCheck_1578_ == 0)
{
v___x_1573_ = v___x_1536_;
v_isShared_1574_ = v_isSharedCheck_1578_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_a_1571_);
lean_dec(v___x_1536_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1578_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
lean_object* v___x_1576_; 
if (v_isShared_1574_ == 0)
{
v___x_1576_ = v___x_1573_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v_a_1571_);
v___x_1576_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
return v___x_1576_;
}
}
}
}
else
{
lean_object* v_a_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1586_; 
v_a_1579_ = lean_ctor_get(v___x_1526_, 0);
v_isSharedCheck_1586_ = !lean_is_exclusive(v___x_1526_);
if (v_isSharedCheck_1586_ == 0)
{
v___x_1581_ = v___x_1526_;
v_isShared_1582_ = v_isSharedCheck_1586_;
goto v_resetjp_1580_;
}
else
{
lean_inc(v_a_1579_);
lean_dec(v___x_1526_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1586_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
lean_object* v___x_1584_; 
if (v_isShared_1582_ == 0)
{
v___x_1584_ = v___x_1581_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v_a_1579_);
v___x_1584_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
return v___x_1584_;
}
}
}
}
else
{
lean_object* v_a_1587_; lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1594_; 
lean_dec_ref(v_k_1516_);
v_a_1587_ = lean_ctor_get(v___x_1522_, 0);
v_isSharedCheck_1594_ = !lean_is_exclusive(v___x_1522_);
if (v_isSharedCheck_1594_ == 0)
{
v___x_1589_ = v___x_1522_;
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
else
{
lean_inc(v_a_1587_);
lean_dec(v___x_1522_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
lean_object* v___x_1592_; 
if (v_isShared_1590_ == 0)
{
v___x_1592_ = v___x_1589_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v_a_1587_);
v___x_1592_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
return v___x_1592_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withRevertedFrom___redArg___boxed(lean_object* v_mvarId_1595_, lean_object* v_fvarId_1596_, lean_object* v_k_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_){
_start:
{
lean_object* v_res_1603_; 
v_res_1603_ = l_Lean_MVarId_withRevertedFrom___redArg(v_mvarId_1595_, v_fvarId_1596_, v_k_1597_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_);
lean_dec(v_a_1601_);
lean_dec_ref(v_a_1600_);
lean_dec(v_a_1599_);
lean_dec_ref(v_a_1598_);
return v_res_1603_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withRevertedFrom(lean_object* v_00_u03b1_1604_, lean_object* v_mvarId_1605_, lean_object* v_fvarId_1606_, lean_object* v_k_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_){
_start:
{
lean_object* v___x_1613_; 
v___x_1613_ = l_Lean_MVarId_withRevertedFrom___redArg(v_mvarId_1605_, v_fvarId_1606_, v_k_1607_, v_a_1608_, v_a_1609_, v_a_1610_, v_a_1611_);
return v___x_1613_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withRevertedFrom___boxed(lean_object* v_00_u03b1_1614_, lean_object* v_mvarId_1615_, lean_object* v_fvarId_1616_, lean_object* v_k_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_){
_start:
{
lean_object* v_res_1623_; 
v_res_1623_ = l_Lean_MVarId_withRevertedFrom(v_00_u03b1_1614_, v_mvarId_1615_, v_fvarId_1616_, v_k_1617_, v_a_1618_, v_a_1619_, v_a_1620_, v_a_1621_);
lean_dec(v_a_1621_);
lean_dec_ref(v_a_1620_);
lean_dec(v_a_1619_);
lean_dec_ref(v_a_1618_);
return v_res_1623_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_changeLocalDecl___lam__0(uint8_t v_checkDefEq_1624_, lean_object* v_typeNew_1625_, lean_object* v___x_1626_, lean_object* v_mvarId_1627_, lean_object* v_typeOld_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_){
_start:
{
if (v_checkDefEq_1624_ == 0)
{
lean_object* v___x_1634_; lean_object* v___x_1635_; 
lean_dec_ref(v_typeOld_1628_);
lean_dec(v_mvarId_1627_);
lean_dec(v___x_1626_);
lean_dec_ref(v_typeNew_1625_);
v___x_1634_ = lean_box(0);
v___x_1635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1635_, 0, v___x_1634_);
return v___x_1635_;
}
else
{
lean_object* v___x_1636_; 
lean_inc_ref(v_typeOld_1628_);
lean_inc_ref(v_typeNew_1625_);
v___x_1636_ = l_Lean_Meta_isExprDefEq(v_typeNew_1625_, v_typeOld_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_);
if (lean_obj_tag(v___x_1636_) == 0)
{
lean_object* v_a_1637_; lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1655_; 
v_a_1637_ = lean_ctor_get(v___x_1636_, 0);
v_isSharedCheck_1655_ = !lean_is_exclusive(v___x_1636_);
if (v_isSharedCheck_1655_ == 0)
{
v___x_1639_ = v___x_1636_;
v_isShared_1640_ = v_isSharedCheck_1655_;
goto v_resetjp_1638_;
}
else
{
lean_inc(v_a_1637_);
lean_dec(v___x_1636_);
v___x_1639_ = lean_box(0);
v_isShared_1640_ = v_isSharedCheck_1655_;
goto v_resetjp_1638_;
}
v_resetjp_1638_:
{
uint8_t v___x_1641_; 
v___x_1641_ = lean_unbox(v_a_1637_);
lean_dec(v_a_1637_);
if (v___x_1641_ == 0)
{
lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; 
lean_del_object(v___x_1639_);
v___x_1642_ = lean_obj_once(&l_Lean_MVarId_change___lam__0___closed__1, &l_Lean_MVarId_change___lam__0___closed__1_once, _init_l_Lean_MVarId_change___lam__0___closed__1);
v___x_1643_ = l_Lean_indentExpr(v_typeNew_1625_);
v___x_1644_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1644_, 0, v___x_1642_);
lean_ctor_set(v___x_1644_, 1, v___x_1643_);
v___x_1645_ = lean_obj_once(&l_Lean_MVarId_change___lam__0___closed__3, &l_Lean_MVarId_change___lam__0___closed__3_once, _init_l_Lean_MVarId_change___lam__0___closed__3);
v___x_1646_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1646_, 0, v___x_1644_);
lean_ctor_set(v___x_1646_, 1, v___x_1645_);
v___x_1647_ = l_Lean_indentExpr(v_typeOld_1628_);
v___x_1648_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1648_, 0, v___x_1646_);
lean_ctor_set(v___x_1648_, 1, v___x_1647_);
v___x_1649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1649_, 0, v___x_1648_);
v___x_1650_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1626_, v_mvarId_1627_, v___x_1649_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_);
return v___x_1650_;
}
else
{
lean_object* v___x_1651_; lean_object* v___x_1653_; 
lean_dec_ref(v_typeOld_1628_);
lean_dec(v_mvarId_1627_);
lean_dec(v___x_1626_);
lean_dec_ref(v_typeNew_1625_);
v___x_1651_ = lean_box(0);
if (v_isShared_1640_ == 0)
{
lean_ctor_set(v___x_1639_, 0, v___x_1651_);
v___x_1653_ = v___x_1639_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v___x_1651_);
v___x_1653_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
return v___x_1653_;
}
}
}
}
else
{
lean_object* v_a_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1663_; 
lean_dec_ref(v_typeOld_1628_);
lean_dec(v_mvarId_1627_);
lean_dec(v___x_1626_);
lean_dec_ref(v_typeNew_1625_);
v_a_1656_ = lean_ctor_get(v___x_1636_, 0);
v_isSharedCheck_1663_ = !lean_is_exclusive(v___x_1636_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1658_ = v___x_1636_;
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_a_1656_);
lean_dec(v___x_1636_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
lean_object* v___x_1661_; 
if (v_isShared_1659_ == 0)
{
v___x_1661_ = v___x_1658_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v_a_1656_);
v___x_1661_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
return v___x_1661_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_changeLocalDecl___lam__0___boxed(lean_object* v_checkDefEq_1664_, lean_object* v_typeNew_1665_, lean_object* v___x_1666_, lean_object* v_mvarId_1667_, lean_object* v_typeOld_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_){
_start:
{
uint8_t v_checkDefEq_boxed_1674_; lean_object* v_res_1675_; 
v_checkDefEq_boxed_1674_ = lean_unbox(v_checkDefEq_1664_);
v_res_1675_ = l_Lean_MVarId_changeLocalDecl___lam__0(v_checkDefEq_boxed_1674_, v_typeNew_1665_, v___x_1666_, v_mvarId_1667_, v_typeOld_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_);
lean_dec(v___y_1672_);
lean_dec_ref(v___y_1671_);
lean_dec(v___y_1670_);
lean_dec_ref(v___y_1669_);
return v_res_1675_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_changeLocalDecl_spec__0(size_t v_sz_1676_, size_t v_i_1677_, lean_object* v_bs_1678_){
_start:
{
uint8_t v___x_1679_; 
v___x_1679_ = lean_usize_dec_lt(v_i_1677_, v_sz_1676_);
if (v___x_1679_ == 0)
{
return v_bs_1678_;
}
else
{
lean_object* v_v_1680_; lean_object* v___x_1681_; lean_object* v_bs_x27_1682_; lean_object* v___x_1683_; size_t v___x_1684_; size_t v___x_1685_; lean_object* v___x_1686_; 
v_v_1680_ = lean_array_uget(v_bs_1678_, v_i_1677_);
v___x_1681_ = lean_unsigned_to_nat(0u);
v_bs_x27_1682_ = lean_array_uset(v_bs_1678_, v_i_1677_, v___x_1681_);
v___x_1683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1683_, 0, v_v_1680_);
v___x_1684_ = ((size_t)1ULL);
v___x_1685_ = lean_usize_add(v_i_1677_, v___x_1684_);
v___x_1686_ = lean_array_uset(v_bs_x27_1682_, v_i_1677_, v___x_1683_);
v_i_1677_ = v___x_1685_;
v_bs_1678_ = v___x_1686_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_changeLocalDecl_spec__0___boxed(lean_object* v_sz_1688_, lean_object* v_i_1689_, lean_object* v_bs_1690_){
_start:
{
size_t v_sz_boxed_1691_; size_t v_i_boxed_1692_; lean_object* v_res_1693_; 
v_sz_boxed_1691_ = lean_unbox_usize(v_sz_1688_);
lean_dec(v_sz_1688_);
v_i_boxed_1692_ = lean_unbox_usize(v_i_1689_);
lean_dec(v_i_1689_);
v_res_1693_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_changeLocalDecl_spec__0(v_sz_boxed_1691_, v_i_boxed_1692_, v_bs_1690_);
return v_res_1693_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_changeLocalDecl___lam__1(lean_object* v_mvarId_1694_, lean_object* v_fvars_1695_, lean_object* v_targetNew_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_){
_start:
{
lean_object* v___x_1702_; 
v___x_1702_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_1694_, v_targetNew_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_);
if (lean_obj_tag(v___x_1702_) == 0)
{
lean_object* v_a_1703_; lean_object* v___x_1705_; uint8_t v_isShared_1706_; uint8_t v_isSharedCheck_1716_; 
v_a_1703_ = lean_ctor_get(v___x_1702_, 0);
v_isSharedCheck_1716_ = !lean_is_exclusive(v___x_1702_);
if (v_isSharedCheck_1716_ == 0)
{
v___x_1705_ = v___x_1702_;
v_isShared_1706_ = v_isSharedCheck_1716_;
goto v_resetjp_1704_;
}
else
{
lean_inc(v_a_1703_);
lean_dec(v___x_1702_);
v___x_1705_ = lean_box(0);
v_isShared_1706_ = v_isSharedCheck_1716_;
goto v_resetjp_1704_;
}
v_resetjp_1704_:
{
lean_object* v___x_1707_; size_t v_sz_1708_; size_t v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1714_; 
v___x_1707_ = lean_box(0);
v_sz_1708_ = lean_array_size(v_fvars_1695_);
v___x_1709_ = ((size_t)0ULL);
v___x_1710_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_changeLocalDecl_spec__0(v_sz_1708_, v___x_1709_, v_fvars_1695_);
v___x_1711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1711_, 0, v___x_1710_);
lean_ctor_set(v___x_1711_, 1, v_a_1703_);
v___x_1712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1712_, 0, v___x_1707_);
lean_ctor_set(v___x_1712_, 1, v___x_1711_);
if (v_isShared_1706_ == 0)
{
lean_ctor_set(v___x_1705_, 0, v___x_1712_);
v___x_1714_ = v___x_1705_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1715_; 
v_reuseFailAlloc_1715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1715_, 0, v___x_1712_);
v___x_1714_ = v_reuseFailAlloc_1715_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
return v___x_1714_;
}
}
}
else
{
lean_object* v_a_1717_; lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1724_; 
lean_dec_ref(v_fvars_1695_);
v_a_1717_ = lean_ctor_get(v___x_1702_, 0);
v_isSharedCheck_1724_ = !lean_is_exclusive(v___x_1702_);
if (v_isSharedCheck_1724_ == 0)
{
v___x_1719_ = v___x_1702_;
v_isShared_1720_ = v_isSharedCheck_1724_;
goto v_resetjp_1718_;
}
else
{
lean_inc(v_a_1717_);
lean_dec(v___x_1702_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1724_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
lean_object* v___x_1722_; 
if (v_isShared_1720_ == 0)
{
v___x_1722_ = v___x_1719_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v_a_1717_);
v___x_1722_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
return v___x_1722_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_changeLocalDecl___lam__1___boxed(lean_object* v_mvarId_1725_, lean_object* v_fvars_1726_, lean_object* v_targetNew_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_){
_start:
{
lean_object* v_res_1733_; 
v_res_1733_ = l_Lean_MVarId_changeLocalDecl___lam__1(v_mvarId_1725_, v_fvars_1726_, v_targetNew_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_);
lean_dec(v___y_1731_);
lean_dec_ref(v___y_1730_);
lean_dec(v___y_1729_);
lean_dec_ref(v___y_1728_);
return v_res_1733_;
}
}
static lean_object* _init_l_Lean_MVarId_changeLocalDecl___lam__2___closed__2(void){
_start:
{
lean_object* v___x_1737_; lean_object* v___x_1738_; 
v___x_1737_ = ((lean_object*)(l_Lean_MVarId_changeLocalDecl___lam__2___closed__1));
v___x_1738_ = l_Lean_MessageData_ofFormat(v___x_1737_);
return v___x_1738_;
}
}
static lean_object* _init_l_Lean_MVarId_changeLocalDecl___lam__2___closed__3(void){
_start:
{
lean_object* v___x_1739_; lean_object* v___x_1740_; 
v___x_1739_ = lean_obj_once(&l_Lean_MVarId_changeLocalDecl___lam__2___closed__2, &l_Lean_MVarId_changeLocalDecl___lam__2___closed__2_once, _init_l_Lean_MVarId_changeLocalDecl___lam__2___closed__2);
v___x_1740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1740_, 0, v___x_1739_);
return v___x_1740_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_changeLocalDecl___lam__2(lean_object* v_mvarId_1741_, lean_object* v___f_1742_, lean_object* v_typeNew_1743_, lean_object* v___f_1744_, lean_object* v___x_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_){
_start:
{
lean_object* v___x_1751_; 
lean_inc(v_mvarId_1741_);
v___x_1751_ = l_Lean_MVarId_getType(v_mvarId_1741_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_);
if (lean_obj_tag(v___x_1751_) == 0)
{
lean_object* v_a_1752_; 
v_a_1752_ = lean_ctor_get(v___x_1751_, 0);
lean_inc(v_a_1752_);
lean_dec_ref(v___x_1751_);
switch(lean_obj_tag(v_a_1752_))
{
case 7:
{
lean_object* v_binderName_1753_; lean_object* v_binderType_1754_; lean_object* v_body_1755_; uint8_t v_binderInfo_1756_; lean_object* v___x_1757_; 
lean_dec(v___x_1745_);
lean_dec(v_mvarId_1741_);
v_binderName_1753_ = lean_ctor_get(v_a_1752_, 0);
lean_inc(v_binderName_1753_);
v_binderType_1754_ = lean_ctor_get(v_a_1752_, 1);
lean_inc_ref(v_binderType_1754_);
v_body_1755_ = lean_ctor_get(v_a_1752_, 2);
lean_inc_ref(v_body_1755_);
v_binderInfo_1756_ = lean_ctor_get_uint8(v_a_1752_, sizeof(void*)*3 + 8);
lean_dec_ref(v_a_1752_);
lean_inc(v___y_1749_);
lean_inc_ref(v___y_1748_);
lean_inc(v___y_1747_);
lean_inc_ref(v___y_1746_);
v___x_1757_ = lean_apply_6(v___f_1742_, v_binderType_1754_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_, lean_box(0));
if (lean_obj_tag(v___x_1757_) == 0)
{
lean_object* v___x_1758_; lean_object* v___x_1759_; 
lean_dec_ref(v___x_1757_);
v___x_1758_ = l_Lean_Expr_forallE___override(v_binderName_1753_, v_typeNew_1743_, v_body_1755_, v_binderInfo_1756_);
v___x_1759_ = lean_apply_6(v___f_1744_, v___x_1758_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_, lean_box(0));
return v___x_1759_;
}
else
{
lean_object* v_a_1760_; lean_object* v___x_1762_; uint8_t v_isShared_1763_; uint8_t v_isSharedCheck_1767_; 
lean_dec_ref(v_body_1755_);
lean_dec(v_binderName_1753_);
lean_dec(v___y_1749_);
lean_dec_ref(v___y_1748_);
lean_dec(v___y_1747_);
lean_dec_ref(v___y_1746_);
lean_dec_ref(v___f_1744_);
lean_dec_ref(v_typeNew_1743_);
v_a_1760_ = lean_ctor_get(v___x_1757_, 0);
v_isSharedCheck_1767_ = !lean_is_exclusive(v___x_1757_);
if (v_isSharedCheck_1767_ == 0)
{
v___x_1762_ = v___x_1757_;
v_isShared_1763_ = v_isSharedCheck_1767_;
goto v_resetjp_1761_;
}
else
{
lean_inc(v_a_1760_);
lean_dec(v___x_1757_);
v___x_1762_ = lean_box(0);
v_isShared_1763_ = v_isSharedCheck_1767_;
goto v_resetjp_1761_;
}
v_resetjp_1761_:
{
lean_object* v___x_1765_; 
if (v_isShared_1763_ == 0)
{
v___x_1765_ = v___x_1762_;
goto v_reusejp_1764_;
}
else
{
lean_object* v_reuseFailAlloc_1766_; 
v_reuseFailAlloc_1766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1766_, 0, v_a_1760_);
v___x_1765_ = v_reuseFailAlloc_1766_;
goto v_reusejp_1764_;
}
v_reusejp_1764_:
{
return v___x_1765_;
}
}
}
}
case 8:
{
lean_object* v_declName_1768_; lean_object* v_type_1769_; lean_object* v_value_1770_; lean_object* v_body_1771_; uint8_t v_nondep_1772_; lean_object* v___x_1773_; 
lean_dec(v___x_1745_);
lean_dec(v_mvarId_1741_);
v_declName_1768_ = lean_ctor_get(v_a_1752_, 0);
lean_inc(v_declName_1768_);
v_type_1769_ = lean_ctor_get(v_a_1752_, 1);
lean_inc_ref(v_type_1769_);
v_value_1770_ = lean_ctor_get(v_a_1752_, 2);
lean_inc_ref(v_value_1770_);
v_body_1771_ = lean_ctor_get(v_a_1752_, 3);
lean_inc_ref(v_body_1771_);
v_nondep_1772_ = lean_ctor_get_uint8(v_a_1752_, sizeof(void*)*4 + 8);
lean_dec_ref(v_a_1752_);
lean_inc(v___y_1749_);
lean_inc_ref(v___y_1748_);
lean_inc(v___y_1747_);
lean_inc_ref(v___y_1746_);
v___x_1773_ = lean_apply_6(v___f_1742_, v_type_1769_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_, lean_box(0));
if (lean_obj_tag(v___x_1773_) == 0)
{
lean_object* v___x_1774_; lean_object* v___x_1775_; 
lean_dec_ref(v___x_1773_);
v___x_1774_ = l_Lean_Expr_letE___override(v_declName_1768_, v_typeNew_1743_, v_value_1770_, v_body_1771_, v_nondep_1772_);
v___x_1775_ = lean_apply_6(v___f_1744_, v___x_1774_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_, lean_box(0));
return v___x_1775_;
}
else
{
lean_object* v_a_1776_; lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1783_; 
lean_dec_ref(v_body_1771_);
lean_dec_ref(v_value_1770_);
lean_dec(v_declName_1768_);
lean_dec(v___y_1749_);
lean_dec_ref(v___y_1748_);
lean_dec(v___y_1747_);
lean_dec_ref(v___y_1746_);
lean_dec_ref(v___f_1744_);
lean_dec_ref(v_typeNew_1743_);
v_a_1776_ = lean_ctor_get(v___x_1773_, 0);
v_isSharedCheck_1783_ = !lean_is_exclusive(v___x_1773_);
if (v_isSharedCheck_1783_ == 0)
{
v___x_1778_ = v___x_1773_;
v_isShared_1779_ = v_isSharedCheck_1783_;
goto v_resetjp_1777_;
}
else
{
lean_inc(v_a_1776_);
lean_dec(v___x_1773_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1783_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
lean_object* v___x_1781_; 
if (v_isShared_1779_ == 0)
{
v___x_1781_ = v___x_1778_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v_a_1776_);
v___x_1781_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
return v___x_1781_;
}
}
}
}
default: 
{
lean_object* v___x_1784_; lean_object* v___x_1785_; 
lean_dec(v_a_1752_);
lean_dec_ref(v___f_1744_);
lean_dec_ref(v_typeNew_1743_);
lean_dec_ref(v___f_1742_);
v___x_1784_ = lean_obj_once(&l_Lean_MVarId_changeLocalDecl___lam__2___closed__3, &l_Lean_MVarId_changeLocalDecl___lam__2___closed__3_once, _init_l_Lean_MVarId_changeLocalDecl___lam__2___closed__3);
v___x_1785_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1745_, v_mvarId_1741_, v___x_1784_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_);
lean_dec(v___y_1749_);
lean_dec_ref(v___y_1748_);
lean_dec(v___y_1747_);
lean_dec_ref(v___y_1746_);
return v___x_1785_;
}
}
}
else
{
lean_object* v_a_1786_; lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1793_; 
lean_dec(v___y_1749_);
lean_dec_ref(v___y_1748_);
lean_dec(v___y_1747_);
lean_dec_ref(v___y_1746_);
lean_dec(v___x_1745_);
lean_dec_ref(v___f_1744_);
lean_dec_ref(v_typeNew_1743_);
lean_dec_ref(v___f_1742_);
lean_dec(v_mvarId_1741_);
v_a_1786_ = lean_ctor_get(v___x_1751_, 0);
v_isSharedCheck_1793_ = !lean_is_exclusive(v___x_1751_);
if (v_isSharedCheck_1793_ == 0)
{
v___x_1788_ = v___x_1751_;
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
else
{
lean_inc(v_a_1786_);
lean_dec(v___x_1751_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
lean_object* v___x_1791_; 
if (v_isShared_1789_ == 0)
{
v___x_1791_ = v___x_1788_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v_a_1786_);
v___x_1791_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1790_;
}
v_reusejp_1790_:
{
return v___x_1791_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_changeLocalDecl___lam__2___boxed(lean_object* v_mvarId_1794_, lean_object* v___f_1795_, lean_object* v_typeNew_1796_, lean_object* v___f_1797_, lean_object* v___x_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_){
_start:
{
lean_object* v_res_1804_; 
v_res_1804_ = l_Lean_MVarId_changeLocalDecl___lam__2(v_mvarId_1794_, v___f_1795_, v_typeNew_1796_, v___f_1797_, v___x_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_);
return v_res_1804_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_changeLocalDecl___lam__3(uint8_t v_checkDefEq_1805_, lean_object* v_typeNew_1806_, lean_object* v___x_1807_, lean_object* v_mvarId_1808_, lean_object* v_fvars_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_){
_start:
{
lean_object* v___x_1815_; lean_object* v___f_1816_; lean_object* v___f_1817_; lean_object* v___f_1818_; lean_object* v___x_1819_; 
v___x_1815_ = lean_box(v_checkDefEq_1805_);
lean_inc_n(v_mvarId_1808_, 3);
lean_inc(v___x_1807_);
lean_inc_ref(v_typeNew_1806_);
v___f_1816_ = lean_alloc_closure((void*)(l_Lean_MVarId_changeLocalDecl___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1816_, 0, v___x_1815_);
lean_closure_set(v___f_1816_, 1, v_typeNew_1806_);
lean_closure_set(v___f_1816_, 2, v___x_1807_);
lean_closure_set(v___f_1816_, 3, v_mvarId_1808_);
v___f_1817_ = lean_alloc_closure((void*)(l_Lean_MVarId_changeLocalDecl___lam__1___boxed), 8, 2);
lean_closure_set(v___f_1817_, 0, v_mvarId_1808_);
lean_closure_set(v___f_1817_, 1, v_fvars_1809_);
v___f_1818_ = lean_alloc_closure((void*)(l_Lean_MVarId_changeLocalDecl___lam__2___boxed), 10, 5);
lean_closure_set(v___f_1818_, 0, v_mvarId_1808_);
lean_closure_set(v___f_1818_, 1, v___f_1816_);
lean_closure_set(v___f_1818_, 2, v_typeNew_1806_);
lean_closure_set(v___f_1818_, 3, v___f_1817_);
lean_closure_set(v___f_1818_, 4, v___x_1807_);
v___x_1819_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(v_mvarId_1808_, v___f_1818_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_);
return v___x_1819_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_changeLocalDecl___lam__3___boxed(lean_object* v_checkDefEq_1820_, lean_object* v_typeNew_1821_, lean_object* v___x_1822_, lean_object* v_mvarId_1823_, lean_object* v_fvars_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_){
_start:
{
uint8_t v_checkDefEq_boxed_1830_; lean_object* v_res_1831_; 
v_checkDefEq_boxed_1830_ = lean_unbox(v_checkDefEq_1820_);
v_res_1831_ = l_Lean_MVarId_changeLocalDecl___lam__3(v_checkDefEq_boxed_1830_, v_typeNew_1821_, v___x_1822_, v_mvarId_1823_, v_fvars_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_);
lean_dec(v___y_1828_);
lean_dec_ref(v___y_1827_);
lean_dec(v___y_1826_);
lean_dec_ref(v___y_1825_);
return v_res_1831_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_changeLocalDecl(lean_object* v_mvarId_1835_, lean_object* v_fvarId_1836_, lean_object* v_typeNew_1837_, uint8_t v_checkDefEq_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_){
_start:
{
lean_object* v___x_1844_; lean_object* v___x_1845_; 
v___x_1844_ = ((lean_object*)(l_Lean_MVarId_changeLocalDecl___closed__1));
lean_inc(v_mvarId_1835_);
v___x_1845_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_1835_, v___x_1844_, v_a_1839_, v_a_1840_, v_a_1841_, v_a_1842_);
if (lean_obj_tag(v___x_1845_) == 0)
{
lean_object* v___x_1846_; lean_object* v___f_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; uint8_t v___x_1851_; lean_object* v___x_1852_; 
lean_dec_ref(v___x_1845_);
v___x_1846_ = lean_box(v_checkDefEq_1838_);
v___f_1847_ = lean_alloc_closure((void*)(l_Lean_MVarId_changeLocalDecl___lam__3___boxed), 10, 3);
lean_closure_set(v___f_1847_, 0, v___x_1846_);
lean_closure_set(v___f_1847_, 1, v_typeNew_1837_);
lean_closure_set(v___f_1847_, 2, v___x_1844_);
v___x_1848_ = lean_unsigned_to_nat(1u);
v___x_1849_ = lean_mk_empty_array_with_capacity(v___x_1848_);
v___x_1850_ = lean_array_push(v___x_1849_, v_fvarId_1836_);
v___x_1851_ = 0;
v___x_1852_ = l_Lean_MVarId_withReverted___redArg(v_mvarId_1835_, v___x_1850_, v___f_1847_, v___x_1851_, v_a_1839_, v_a_1840_, v_a_1841_, v_a_1842_);
if (lean_obj_tag(v___x_1852_) == 0)
{
lean_object* v_a_1853_; lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_1861_; 
v_a_1853_ = lean_ctor_get(v___x_1852_, 0);
v_isSharedCheck_1861_ = !lean_is_exclusive(v___x_1852_);
if (v_isSharedCheck_1861_ == 0)
{
v___x_1855_ = v___x_1852_;
v_isShared_1856_ = v_isSharedCheck_1861_;
goto v_resetjp_1854_;
}
else
{
lean_inc(v_a_1853_);
lean_dec(v___x_1852_);
v___x_1855_ = lean_box(0);
v_isShared_1856_ = v_isSharedCheck_1861_;
goto v_resetjp_1854_;
}
v_resetjp_1854_:
{
lean_object* v_snd_1857_; lean_object* v___x_1859_; 
v_snd_1857_ = lean_ctor_get(v_a_1853_, 1);
lean_inc(v_snd_1857_);
lean_dec(v_a_1853_);
if (v_isShared_1856_ == 0)
{
lean_ctor_set(v___x_1855_, 0, v_snd_1857_);
v___x_1859_ = v___x_1855_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v_snd_1857_);
v___x_1859_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
return v___x_1859_;
}
}
}
else
{
lean_object* v_a_1862_; lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1869_; 
v_a_1862_ = lean_ctor_get(v___x_1852_, 0);
v_isSharedCheck_1869_ = !lean_is_exclusive(v___x_1852_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1864_ = v___x_1852_;
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
else
{
lean_inc(v_a_1862_);
lean_dec(v___x_1852_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
lean_object* v___x_1867_; 
if (v_isShared_1865_ == 0)
{
v___x_1867_ = v___x_1864_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v_a_1862_);
v___x_1867_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
return v___x_1867_;
}
}
}
}
else
{
lean_object* v_a_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1877_; 
lean_dec_ref(v_typeNew_1837_);
lean_dec(v_fvarId_1836_);
lean_dec(v_mvarId_1835_);
v_a_1870_ = lean_ctor_get(v___x_1845_, 0);
v_isSharedCheck_1877_ = !lean_is_exclusive(v___x_1845_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1872_ = v___x_1845_;
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_a_1870_);
lean_dec(v___x_1845_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v___x_1875_; 
if (v_isShared_1873_ == 0)
{
v___x_1875_ = v___x_1872_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v_a_1870_);
v___x_1875_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
return v___x_1875_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_changeLocalDecl___boxed(lean_object* v_mvarId_1878_, lean_object* v_fvarId_1879_, lean_object* v_typeNew_1880_, lean_object* v_checkDefEq_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_){
_start:
{
uint8_t v_checkDefEq_boxed_1887_; lean_object* v_res_1888_; 
v_checkDefEq_boxed_1887_ = lean_unbox(v_checkDefEq_1881_);
v_res_1888_ = l_Lean_MVarId_changeLocalDecl(v_mvarId_1878_, v_fvarId_1879_, v_typeNew_1880_, v_checkDefEq_boxed_1887_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_);
lean_dec(v_a_1885_);
lean_dec_ref(v_a_1884_);
lean_dec(v_a_1883_);
lean_dec_ref(v_a_1882_);
return v_res_1888_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyTarget___lam__0(lean_object* v_mvarId_1889_, lean_object* v___x_1890_, lean_object* v_f_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_){
_start:
{
lean_object* v___x_1897_; 
lean_inc(v_mvarId_1889_);
v___x_1897_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_1889_, v___x_1890_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_);
if (lean_obj_tag(v___x_1897_) == 0)
{
lean_object* v___x_1898_; 
lean_dec_ref(v___x_1897_);
lean_inc(v_mvarId_1889_);
v___x_1898_ = l_Lean_MVarId_getType(v_mvarId_1889_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_);
if (lean_obj_tag(v___x_1898_) == 0)
{
lean_object* v_a_1899_; lean_object* v___x_1900_; 
v_a_1899_ = lean_ctor_get(v___x_1898_, 0);
lean_inc(v_a_1899_);
lean_dec_ref(v___x_1898_);
lean_inc(v___y_1895_);
lean_inc_ref(v___y_1894_);
lean_inc(v___y_1893_);
lean_inc_ref(v___y_1892_);
v___x_1900_ = lean_apply_6(v_f_1891_, v_a_1899_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, lean_box(0));
if (lean_obj_tag(v___x_1900_) == 0)
{
lean_object* v_a_1901_; uint8_t v___x_1902_; lean_object* v___x_1903_; 
v_a_1901_ = lean_ctor_get(v___x_1900_, 0);
lean_inc(v_a_1901_);
lean_dec_ref(v___x_1900_);
v___x_1902_ = 0;
v___x_1903_ = l_Lean_MVarId_change(v_mvarId_1889_, v_a_1901_, v___x_1902_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_);
lean_dec(v___y_1895_);
lean_dec_ref(v___y_1894_);
lean_dec(v___y_1893_);
lean_dec_ref(v___y_1892_);
return v___x_1903_;
}
else
{
lean_object* v_a_1904_; lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1911_; 
lean_dec(v___y_1895_);
lean_dec_ref(v___y_1894_);
lean_dec(v___y_1893_);
lean_dec_ref(v___y_1892_);
lean_dec(v_mvarId_1889_);
v_a_1904_ = lean_ctor_get(v___x_1900_, 0);
v_isSharedCheck_1911_ = !lean_is_exclusive(v___x_1900_);
if (v_isSharedCheck_1911_ == 0)
{
v___x_1906_ = v___x_1900_;
v_isShared_1907_ = v_isSharedCheck_1911_;
goto v_resetjp_1905_;
}
else
{
lean_inc(v_a_1904_);
lean_dec(v___x_1900_);
v___x_1906_ = lean_box(0);
v_isShared_1907_ = v_isSharedCheck_1911_;
goto v_resetjp_1905_;
}
v_resetjp_1905_:
{
lean_object* v___x_1909_; 
if (v_isShared_1907_ == 0)
{
v___x_1909_ = v___x_1906_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v_a_1904_);
v___x_1909_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
return v___x_1909_;
}
}
}
}
else
{
lean_object* v_a_1912_; lean_object* v___x_1914_; uint8_t v_isShared_1915_; uint8_t v_isSharedCheck_1919_; 
lean_dec(v___y_1895_);
lean_dec_ref(v___y_1894_);
lean_dec(v___y_1893_);
lean_dec_ref(v___y_1892_);
lean_dec_ref(v_f_1891_);
lean_dec(v_mvarId_1889_);
v_a_1912_ = lean_ctor_get(v___x_1898_, 0);
v_isSharedCheck_1919_ = !lean_is_exclusive(v___x_1898_);
if (v_isSharedCheck_1919_ == 0)
{
v___x_1914_ = v___x_1898_;
v_isShared_1915_ = v_isSharedCheck_1919_;
goto v_resetjp_1913_;
}
else
{
lean_inc(v_a_1912_);
lean_dec(v___x_1898_);
v___x_1914_ = lean_box(0);
v_isShared_1915_ = v_isSharedCheck_1919_;
goto v_resetjp_1913_;
}
v_resetjp_1913_:
{
lean_object* v___x_1917_; 
if (v_isShared_1915_ == 0)
{
v___x_1917_ = v___x_1914_;
goto v_reusejp_1916_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v_a_1912_);
v___x_1917_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1916_;
}
v_reusejp_1916_:
{
return v___x_1917_;
}
}
}
}
else
{
lean_object* v_a_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1927_; 
lean_dec(v___y_1895_);
lean_dec_ref(v___y_1894_);
lean_dec(v___y_1893_);
lean_dec_ref(v___y_1892_);
lean_dec_ref(v_f_1891_);
lean_dec(v_mvarId_1889_);
v_a_1920_ = lean_ctor_get(v___x_1897_, 0);
v_isSharedCheck_1927_ = !lean_is_exclusive(v___x_1897_);
if (v_isSharedCheck_1927_ == 0)
{
v___x_1922_ = v___x_1897_;
v_isShared_1923_ = v_isSharedCheck_1927_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_a_1920_);
lean_dec(v___x_1897_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1927_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v___x_1925_; 
if (v_isShared_1923_ == 0)
{
v___x_1925_ = v___x_1922_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v_a_1920_);
v___x_1925_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
return v___x_1925_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyTarget___lam__0___boxed(lean_object* v_mvarId_1928_, lean_object* v___x_1929_, lean_object* v_f_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_){
_start:
{
lean_object* v_res_1936_; 
v_res_1936_ = l_Lean_MVarId_modifyTarget___lam__0(v_mvarId_1928_, v___x_1929_, v_f_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_);
return v_res_1936_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyTarget(lean_object* v_mvarId_1940_, lean_object* v_f_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_){
_start:
{
lean_object* v___x_1947_; lean_object* v___f_1948_; lean_object* v___x_1949_; 
v___x_1947_ = ((lean_object*)(l_Lean_MVarId_modifyTarget___closed__1));
lean_inc(v_mvarId_1940_);
v___f_1948_ = lean_alloc_closure((void*)(l_Lean_MVarId_modifyTarget___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1948_, 0, v_mvarId_1940_);
lean_closure_set(v___f_1948_, 1, v___x_1947_);
lean_closure_set(v___f_1948_, 2, v_f_1941_);
v___x_1949_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(v_mvarId_1940_, v___f_1948_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_);
return v___x_1949_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyTarget___boxed(lean_object* v_mvarId_1950_, lean_object* v_f_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_){
_start:
{
lean_object* v_res_1957_; 
v_res_1957_ = l_Lean_MVarId_modifyTarget(v_mvarId_1950_, v_f_1951_, v_a_1952_, v_a_1953_, v_a_1954_, v_a_1955_);
lean_dec(v_a_1955_);
lean_dec_ref(v_a_1954_);
lean_dec(v_a_1953_);
lean_dec_ref(v_a_1952_);
return v_res_1957_;
}
}
static lean_object* _init_l_Lean_MVarId_modifyTargetEqLHS___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1962_; lean_object* v___x_1963_; 
v___x_1962_ = ((lean_object*)(l_Lean_MVarId_modifyTargetEqLHS___lam__0___closed__2));
v___x_1963_ = l_Lean_stringToMessageData(v___x_1962_);
return v___x_1963_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyTargetEqLHS___lam__0(lean_object* v_f_1964_, lean_object* v_mvarId_1965_, lean_object* v_target_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_){
_start:
{
lean_object* v___x_1972_; 
lean_inc_ref(v_target_1966_);
v___x_1972_ = l_Lean_Meta_matchEq_x3f(v_target_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_);
if (lean_obj_tag(v___x_1972_) == 0)
{
lean_object* v_a_1973_; 
v_a_1973_ = lean_ctor_get(v___x_1972_, 0);
lean_inc(v_a_1973_);
lean_dec_ref(v___x_1972_);
if (lean_obj_tag(v_a_1973_) == 1)
{
lean_object* v_val_1974_; lean_object* v_snd_1975_; lean_object* v_fst_1976_; lean_object* v_snd_1977_; lean_object* v___x_1978_; 
lean_dec_ref(v_target_1966_);
lean_dec(v_mvarId_1965_);
v_val_1974_ = lean_ctor_get(v_a_1973_, 0);
lean_inc(v_val_1974_);
lean_dec_ref(v_a_1973_);
v_snd_1975_ = lean_ctor_get(v_val_1974_, 1);
lean_inc(v_snd_1975_);
lean_dec(v_val_1974_);
v_fst_1976_ = lean_ctor_get(v_snd_1975_, 0);
lean_inc(v_fst_1976_);
v_snd_1977_ = lean_ctor_get(v_snd_1975_, 1);
lean_inc(v_snd_1977_);
lean_dec(v_snd_1975_);
lean_inc(v___y_1970_);
lean_inc_ref(v___y_1969_);
lean_inc(v___y_1968_);
lean_inc_ref(v___y_1967_);
v___x_1978_ = lean_apply_6(v_f_1964_, v_fst_1976_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_, lean_box(0));
if (lean_obj_tag(v___x_1978_) == 0)
{
lean_object* v_a_1979_; lean_object* v___x_1980_; 
v_a_1979_ = lean_ctor_get(v___x_1978_, 0);
lean_inc(v_a_1979_);
lean_dec_ref(v___x_1978_);
v___x_1980_ = l_Lean_Meta_mkEq(v_a_1979_, v_snd_1977_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_);
return v___x_1980_;
}
else
{
lean_dec(v_snd_1977_);
return v___x_1978_;
}
}
else
{
lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; 
lean_dec(v_a_1973_);
lean_dec_ref(v_f_1964_);
v___x_1981_ = ((lean_object*)(l_Lean_MVarId_modifyTargetEqLHS___lam__0___closed__1));
v___x_1982_ = lean_obj_once(&l_Lean_MVarId_modifyTargetEqLHS___lam__0___closed__3, &l_Lean_MVarId_modifyTargetEqLHS___lam__0___closed__3_once, _init_l_Lean_MVarId_modifyTargetEqLHS___lam__0___closed__3);
v___x_1983_ = l_Lean_indentExpr(v_target_1966_);
v___x_1984_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1984_, 0, v___x_1982_);
lean_ctor_set(v___x_1984_, 1, v___x_1983_);
v___x_1985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1985_, 0, v___x_1984_);
v___x_1986_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1981_, v_mvarId_1965_, v___x_1985_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_);
return v___x_1986_;
}
}
else
{
lean_object* v_a_1987_; lean_object* v___x_1989_; uint8_t v_isShared_1990_; uint8_t v_isSharedCheck_1994_; 
lean_dec_ref(v_target_1966_);
lean_dec(v_mvarId_1965_);
lean_dec_ref(v_f_1964_);
v_a_1987_ = lean_ctor_get(v___x_1972_, 0);
v_isSharedCheck_1994_ = !lean_is_exclusive(v___x_1972_);
if (v_isSharedCheck_1994_ == 0)
{
v___x_1989_ = v___x_1972_;
v_isShared_1990_ = v_isSharedCheck_1994_;
goto v_resetjp_1988_;
}
else
{
lean_inc(v_a_1987_);
lean_dec(v___x_1972_);
v___x_1989_ = lean_box(0);
v_isShared_1990_ = v_isSharedCheck_1994_;
goto v_resetjp_1988_;
}
v_resetjp_1988_:
{
lean_object* v___x_1992_; 
if (v_isShared_1990_ == 0)
{
v___x_1992_ = v___x_1989_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v_a_1987_);
v___x_1992_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
return v___x_1992_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyTargetEqLHS___lam__0___boxed(lean_object* v_f_1995_, lean_object* v_mvarId_1996_, lean_object* v_target_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_){
_start:
{
lean_object* v_res_2003_; 
v_res_2003_ = l_Lean_MVarId_modifyTargetEqLHS___lam__0(v_f_1995_, v_mvarId_1996_, v_target_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_);
lean_dec(v___y_2001_);
lean_dec_ref(v___y_2000_);
lean_dec(v___y_1999_);
lean_dec_ref(v___y_1998_);
return v_res_2003_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyTargetEqLHS(lean_object* v_mvarId_2004_, lean_object* v_f_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_){
_start:
{
lean_object* v___f_2011_; lean_object* v___x_2012_; 
lean_inc(v_mvarId_2004_);
v___f_2011_ = lean_alloc_closure((void*)(l_Lean_MVarId_modifyTargetEqLHS___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2011_, 0, v_f_2005_);
lean_closure_set(v___f_2011_, 1, v_mvarId_2004_);
v___x_2012_ = l_Lean_MVarId_modifyTarget(v_mvarId_2004_, v___f_2011_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_);
return v___x_2012_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyTargetEqLHS___boxed(lean_object* v_mvarId_2013_, lean_object* v_f_2014_, lean_object* v_a_2015_, lean_object* v_a_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_){
_start:
{
lean_object* v_res_2020_; 
v_res_2020_ = l_Lean_MVarId_modifyTargetEqLHS(v_mvarId_2013_, v_f_2014_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_);
lean_dec(v_a_2018_);
lean_dec_ref(v_a_2017_);
lean_dec(v_a_2016_);
lean_dec_ref(v_a_2015_);
return v_res_2020_;
}
}
static lean_object* _init_l_Lean_MVarId_clearValue___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2022_; lean_object* v___x_2023_; 
v___x_2022_ = ((lean_object*)(l_Lean_MVarId_clearValue___lam__0___closed__0));
v___x_2023_ = l_Lean_stringToMessageData(v___x_2022_);
return v___x_2023_;
}
}
static lean_object* _init_l_Lean_MVarId_clearValue___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2025_; lean_object* v___x_2026_; 
v___x_2025_ = ((lean_object*)(l_Lean_MVarId_clearValue___lam__0___closed__2));
v___x_2026_ = l_Lean_stringToMessageData(v___x_2025_);
return v___x_2026_;
}
}
static lean_object* _init_l_Lean_MVarId_clearValue___lam__0___closed__5(void){
_start:
{
lean_object* v___x_2028_; lean_object* v___x_2029_; 
v___x_2028_ = ((lean_object*)(l_Lean_MVarId_clearValue___lam__0___closed__4));
v___x_2029_ = l_Lean_stringToMessageData(v___x_2028_);
return v___x_2029_;
}
}
static lean_object* _init_l_Lean_MVarId_clearValue___lam__0___closed__7(void){
_start:
{
lean_object* v___x_2031_; lean_object* v___x_2032_; 
v___x_2031_ = ((lean_object*)(l_Lean_MVarId_clearValue___lam__0___closed__6));
v___x_2032_ = l_Lean_stringToMessageData(v___x_2031_);
return v___x_2032_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clearValue___lam__0(lean_object* v_mvarId_x27_2033_, lean_object* v_a_2034_, lean_object* v_fvars_2035_, lean_object* v_fvarId_2036_, lean_object* v___x_2037_, lean_object* v_mvarId_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_){
_start:
{
lean_object* v___x_2044_; 
lean_inc(v_mvarId_x27_2033_);
v___x_2044_ = l_Lean_MVarId_getType(v_mvarId_x27_2033_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_);
if (lean_obj_tag(v___x_2044_) == 0)
{
lean_object* v_a_2045_; lean_object* v___y_2047_; lean_object* v___y_2048_; lean_object* v___y_2049_; lean_object* v___y_2050_; lean_object* v___y_2051_; lean_object* v___y_2081_; lean_object* v___y_2082_; lean_object* v___y_2083_; lean_object* v___y_2084_; uint8_t v___x_2126_; 
v_a_2045_ = lean_ctor_get(v___x_2044_, 0);
lean_inc(v_a_2045_);
lean_dec_ref(v___x_2044_);
v___x_2126_ = l_Lean_Expr_isLet(v_a_2045_);
if (v___x_2126_ == 0)
{
lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; 
v___x_2127_ = lean_obj_once(&l_Lean_MVarId_clearValue___lam__0___closed__5, &l_Lean_MVarId_clearValue___lam__0___closed__5_once, _init_l_Lean_MVarId_clearValue___lam__0___closed__5);
lean_inc(v_fvarId_2036_);
v___x_2128_ = l_Lean_Expr_fvar___override(v_fvarId_2036_);
v___x_2129_ = l_Lean_MessageData_ofExpr(v___x_2128_);
v___x_2130_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2130_, 0, v___x_2127_);
lean_ctor_set(v___x_2130_, 1, v___x_2129_);
v___x_2131_ = lean_obj_once(&l_Lean_MVarId_clearValue___lam__0___closed__7, &l_Lean_MVarId_clearValue___lam__0___closed__7_once, _init_l_Lean_MVarId_clearValue___lam__0___closed__7);
v___x_2132_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2132_, 0, v___x_2130_);
lean_ctor_set(v___x_2132_, 1, v___x_2131_);
v___x_2133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2133_, 0, v___x_2132_);
lean_inc_n(v_mvarId_2038_, 2);
lean_inc(v___x_2037_);
v___x_2134_ = lean_alloc_closure((void*)(l_Lean_Meta_throwTacticEx___boxed), 9, 4);
lean_closure_set(v___x_2134_, 0, lean_box(0));
lean_closure_set(v___x_2134_, 1, v___x_2037_);
lean_closure_set(v___x_2134_, 2, v_mvarId_2038_);
lean_closure_set(v___x_2134_, 3, v___x_2133_);
v___x_2135_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(v_mvarId_2038_, v___x_2134_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_);
if (lean_obj_tag(v___x_2135_) == 0)
{
lean_dec_ref(v___x_2135_);
v___y_2081_ = v___y_2039_;
v___y_2082_ = v___y_2040_;
v___y_2083_ = v___y_2041_;
v___y_2084_ = v___y_2042_;
goto v___jp_2080_;
}
else
{
lean_object* v_a_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2143_; 
lean_dec(v_a_2045_);
lean_dec(v_mvarId_2038_);
lean_dec(v___x_2037_);
lean_dec(v_fvarId_2036_);
lean_dec_ref(v_fvars_2035_);
lean_dec(v_a_2034_);
lean_dec(v_mvarId_x27_2033_);
v_a_2136_ = lean_ctor_get(v___x_2135_, 0);
v_isSharedCheck_2143_ = !lean_is_exclusive(v___x_2135_);
if (v_isSharedCheck_2143_ == 0)
{
v___x_2138_ = v___x_2135_;
v_isShared_2139_ = v_isSharedCheck_2143_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_a_2136_);
lean_dec(v___x_2135_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2143_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v___x_2141_; 
if (v_isShared_2139_ == 0)
{
v___x_2141_ = v___x_2138_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v_a_2136_);
v___x_2141_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
return v___x_2141_;
}
}
}
}
else
{
v___y_2081_ = v___y_2039_;
v___y_2082_ = v___y_2040_;
v___y_2083_ = v___y_2041_;
v___y_2084_ = v___y_2042_;
goto v___jp_2080_;
}
v___jp_2046_:
{
lean_object* v___x_2052_; 
v___x_2052_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___y_2047_, v_a_2034_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_);
if (lean_obj_tag(v___x_2052_) == 0)
{
lean_object* v_a_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2070_; 
v_a_2053_ = lean_ctor_get(v___x_2052_, 0);
lean_inc_n(v_a_2053_, 2);
lean_dec_ref(v___x_2052_);
v___x_2054_ = l_Lean_Expr_letValue_x21(v_a_2045_);
lean_dec(v_a_2045_);
v___x_2055_ = l_Lean_Expr_app___override(v_a_2053_, v___x_2054_);
v___x_2056_ = l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0___redArg(v_mvarId_x27_2033_, v___x_2055_, v___y_2049_);
v_isSharedCheck_2070_ = !lean_is_exclusive(v___x_2056_);
if (v_isSharedCheck_2070_ == 0)
{
lean_object* v_unused_2071_; 
v_unused_2071_ = lean_ctor_get(v___x_2056_, 0);
lean_dec(v_unused_2071_);
v___x_2058_ = v___x_2056_;
v_isShared_2059_ = v_isSharedCheck_2070_;
goto v_resetjp_2057_;
}
else
{
lean_dec(v___x_2056_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2070_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
lean_object* v___x_2060_; size_t v_sz_2061_; size_t v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2068_; 
v___x_2060_ = lean_box(0);
v_sz_2061_ = lean_array_size(v_fvars_2035_);
v___x_2062_ = ((size_t)0ULL);
v___x_2063_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_changeLocalDecl_spec__0(v_sz_2061_, v___x_2062_, v_fvars_2035_);
v___x_2064_ = l_Lean_Expr_mvarId_x21(v_a_2053_);
lean_dec(v_a_2053_);
v___x_2065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2065_, 0, v___x_2063_);
lean_ctor_set(v___x_2065_, 1, v___x_2064_);
v___x_2066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2066_, 0, v___x_2060_);
lean_ctor_set(v___x_2066_, 1, v___x_2065_);
if (v_isShared_2059_ == 0)
{
lean_ctor_set(v___x_2058_, 0, v___x_2066_);
v___x_2068_ = v___x_2058_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v___x_2066_);
v___x_2068_ = v_reuseFailAlloc_2069_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
return v___x_2068_;
}
}
}
else
{
lean_object* v_a_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2079_; 
lean_dec(v_a_2045_);
lean_dec_ref(v_fvars_2035_);
lean_dec(v_mvarId_x27_2033_);
v_a_2072_ = lean_ctor_get(v___x_2052_, 0);
v_isSharedCheck_2079_ = !lean_is_exclusive(v___x_2052_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2074_ = v___x_2052_;
v_isShared_2075_ = v_isSharedCheck_2079_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_a_2072_);
lean_dec(v___x_2052_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2079_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
lean_object* v___x_2077_; 
if (v_isShared_2075_ == 0)
{
v___x_2077_ = v___x_2074_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v_a_2072_);
v___x_2077_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
return v___x_2077_;
}
}
}
}
v___jp_2080_:
{
lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; uint8_t v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v_a_2091_; lean_object* v___x_2093_; uint8_t v_isShared_2094_; uint8_t v_isSharedCheck_2125_; 
v___x_2085_ = l_Lean_Expr_letName_x21(v_a_2045_);
v___x_2086_ = l_Lean_Expr_letType_x21(v_a_2045_);
v___x_2087_ = l_Lean_Expr_letBody_x21(v_a_2045_);
v___x_2088_ = 0;
v___x_2089_ = l_Lean_Expr_forallE___override(v___x_2085_, v___x_2086_, v___x_2087_, v___x_2088_);
v___x_2090_ = l_Lean_instantiateMVars___at___00Lean_MVarId_replaceTargetDefEq_spec__0___redArg(v___x_2089_, v___y_2082_);
v_a_2091_ = lean_ctor_get(v___x_2090_, 0);
v_isSharedCheck_2125_ = !lean_is_exclusive(v___x_2090_);
if (v_isSharedCheck_2125_ == 0)
{
v___x_2093_ = v___x_2090_;
v_isShared_2094_ = v_isSharedCheck_2125_;
goto v_resetjp_2092_;
}
else
{
lean_inc(v_a_2091_);
lean_dec(v___x_2090_);
v___x_2093_ = lean_box(0);
v_isShared_2094_ = v_isSharedCheck_2125_;
goto v_resetjp_2092_;
}
v_resetjp_2092_:
{
lean_object* v___x_2095_; 
lean_inc(v_a_2091_);
v___x_2095_ = l_Lean_Meta_isTypeCorrect(v_a_2091_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_);
if (lean_obj_tag(v___x_2095_) == 0)
{
lean_object* v_a_2096_; uint8_t v___x_2097_; 
v_a_2096_ = lean_ctor_get(v___x_2095_, 0);
lean_inc(v_a_2096_);
lean_dec_ref(v___x_2095_);
v___x_2097_ = lean_unbox(v_a_2096_);
lean_dec(v_a_2096_);
if (v___x_2097_ == 0)
{
lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2105_; 
v___x_2098_ = lean_obj_once(&l_Lean_MVarId_clearValue___lam__0___closed__1, &l_Lean_MVarId_clearValue___lam__0___closed__1_once, _init_l_Lean_MVarId_clearValue___lam__0___closed__1);
v___x_2099_ = l_Lean_Expr_fvar___override(v_fvarId_2036_);
v___x_2100_ = l_Lean_MessageData_ofExpr(v___x_2099_);
v___x_2101_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2101_, 0, v___x_2098_);
lean_ctor_set(v___x_2101_, 1, v___x_2100_);
v___x_2102_ = lean_obj_once(&l_Lean_MVarId_clearValue___lam__0___closed__3, &l_Lean_MVarId_clearValue___lam__0___closed__3_once, _init_l_Lean_MVarId_clearValue___lam__0___closed__3);
v___x_2103_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2103_, 0, v___x_2101_);
lean_ctor_set(v___x_2103_, 1, v___x_2102_);
if (v_isShared_2094_ == 0)
{
lean_ctor_set_tag(v___x_2093_, 1);
lean_ctor_set(v___x_2093_, 0, v___x_2103_);
v___x_2105_ = v___x_2093_;
goto v_reusejp_2104_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v___x_2103_);
v___x_2105_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2104_;
}
v_reusejp_2104_:
{
lean_object* v___x_2106_; lean_object* v___x_2107_; 
lean_inc(v_mvarId_2038_);
v___x_2106_ = lean_alloc_closure((void*)(l_Lean_Meta_throwTacticEx___boxed), 9, 4);
lean_closure_set(v___x_2106_, 0, lean_box(0));
lean_closure_set(v___x_2106_, 1, v___x_2037_);
lean_closure_set(v___x_2106_, 2, v_mvarId_2038_);
lean_closure_set(v___x_2106_, 3, v___x_2105_);
v___x_2107_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(v_mvarId_2038_, v___x_2106_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_);
if (lean_obj_tag(v___x_2107_) == 0)
{
lean_dec_ref(v___x_2107_);
v___y_2047_ = v_a_2091_;
v___y_2048_ = v___y_2081_;
v___y_2049_ = v___y_2082_;
v___y_2050_ = v___y_2083_;
v___y_2051_ = v___y_2084_;
goto v___jp_2046_;
}
else
{
lean_object* v_a_2108_; lean_object* v___x_2110_; uint8_t v_isShared_2111_; uint8_t v_isSharedCheck_2115_; 
lean_dec(v_a_2091_);
lean_dec(v_a_2045_);
lean_dec_ref(v_fvars_2035_);
lean_dec(v_a_2034_);
lean_dec(v_mvarId_x27_2033_);
v_a_2108_ = lean_ctor_get(v___x_2107_, 0);
v_isSharedCheck_2115_ = !lean_is_exclusive(v___x_2107_);
if (v_isSharedCheck_2115_ == 0)
{
v___x_2110_ = v___x_2107_;
v_isShared_2111_ = v_isSharedCheck_2115_;
goto v_resetjp_2109_;
}
else
{
lean_inc(v_a_2108_);
lean_dec(v___x_2107_);
v___x_2110_ = lean_box(0);
v_isShared_2111_ = v_isSharedCheck_2115_;
goto v_resetjp_2109_;
}
v_resetjp_2109_:
{
lean_object* v___x_2113_; 
if (v_isShared_2111_ == 0)
{
v___x_2113_ = v___x_2110_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2114_; 
v_reuseFailAlloc_2114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2114_, 0, v_a_2108_);
v___x_2113_ = v_reuseFailAlloc_2114_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
return v___x_2113_;
}
}
}
}
}
else
{
lean_del_object(v___x_2093_);
lean_dec(v_mvarId_2038_);
lean_dec(v___x_2037_);
lean_dec(v_fvarId_2036_);
v___y_2047_ = v_a_2091_;
v___y_2048_ = v___y_2081_;
v___y_2049_ = v___y_2082_;
v___y_2050_ = v___y_2083_;
v___y_2051_ = v___y_2084_;
goto v___jp_2046_;
}
}
else
{
lean_object* v_a_2117_; lean_object* v___x_2119_; uint8_t v_isShared_2120_; uint8_t v_isSharedCheck_2124_; 
lean_del_object(v___x_2093_);
lean_dec(v_a_2091_);
lean_dec(v_a_2045_);
lean_dec(v_mvarId_2038_);
lean_dec(v___x_2037_);
lean_dec(v_fvarId_2036_);
lean_dec_ref(v_fvars_2035_);
lean_dec(v_a_2034_);
lean_dec(v_mvarId_x27_2033_);
v_a_2117_ = lean_ctor_get(v___x_2095_, 0);
v_isSharedCheck_2124_ = !lean_is_exclusive(v___x_2095_);
if (v_isSharedCheck_2124_ == 0)
{
v___x_2119_ = v___x_2095_;
v_isShared_2120_ = v_isSharedCheck_2124_;
goto v_resetjp_2118_;
}
else
{
lean_inc(v_a_2117_);
lean_dec(v___x_2095_);
v___x_2119_ = lean_box(0);
v_isShared_2120_ = v_isSharedCheck_2124_;
goto v_resetjp_2118_;
}
v_resetjp_2118_:
{
lean_object* v___x_2122_; 
if (v_isShared_2120_ == 0)
{
v___x_2122_ = v___x_2119_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2123_; 
v_reuseFailAlloc_2123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2123_, 0, v_a_2117_);
v___x_2122_ = v_reuseFailAlloc_2123_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
return v___x_2122_;
}
}
}
}
}
}
else
{
lean_object* v_a_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2151_; 
lean_dec(v_mvarId_2038_);
lean_dec(v___x_2037_);
lean_dec(v_fvarId_2036_);
lean_dec_ref(v_fvars_2035_);
lean_dec(v_a_2034_);
lean_dec(v_mvarId_x27_2033_);
v_a_2144_ = lean_ctor_get(v___x_2044_, 0);
v_isSharedCheck_2151_ = !lean_is_exclusive(v___x_2044_);
if (v_isSharedCheck_2151_ == 0)
{
v___x_2146_ = v___x_2044_;
v_isShared_2147_ = v_isSharedCheck_2151_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_a_2144_);
lean_dec(v___x_2044_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2151_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
lean_object* v___x_2149_; 
if (v_isShared_2147_ == 0)
{
v___x_2149_ = v___x_2146_;
goto v_reusejp_2148_;
}
else
{
lean_object* v_reuseFailAlloc_2150_; 
v_reuseFailAlloc_2150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2150_, 0, v_a_2144_);
v___x_2149_ = v_reuseFailAlloc_2150_;
goto v_reusejp_2148_;
}
v_reusejp_2148_:
{
return v___x_2149_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clearValue___lam__0___boxed(lean_object* v_mvarId_x27_2152_, lean_object* v_a_2153_, lean_object* v_fvars_2154_, lean_object* v_fvarId_2155_, lean_object* v___x_2156_, lean_object* v_mvarId_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_){
_start:
{
lean_object* v_res_2163_; 
v_res_2163_ = l_Lean_MVarId_clearValue___lam__0(v_mvarId_x27_2152_, v_a_2153_, v_fvars_2154_, v_fvarId_2155_, v___x_2156_, v_mvarId_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_);
lean_dec(v___y_2161_);
lean_dec_ref(v___y_2160_);
lean_dec(v___y_2159_);
lean_dec_ref(v___y_2158_);
return v_res_2163_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clearValue___lam__1(lean_object* v_a_2164_, lean_object* v_fvarId_2165_, lean_object* v___x_2166_, lean_object* v_mvarId_2167_, lean_object* v_mvarId_x27_2168_, lean_object* v_fvars_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_){
_start:
{
lean_object* v___f_2175_; lean_object* v___x_2176_; 
lean_inc(v_mvarId_x27_2168_);
v___f_2175_ = lean_alloc_closure((void*)(l_Lean_MVarId_clearValue___lam__0___boxed), 11, 6);
lean_closure_set(v___f_2175_, 0, v_mvarId_x27_2168_);
lean_closure_set(v___f_2175_, 1, v_a_2164_);
lean_closure_set(v___f_2175_, 2, v_fvars_2169_);
lean_closure_set(v___f_2175_, 3, v_fvarId_2165_);
lean_closure_set(v___f_2175_, 4, v___x_2166_);
lean_closure_set(v___f_2175_, 5, v_mvarId_2167_);
v___x_2176_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(v_mvarId_x27_2168_, v___f_2175_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_);
return v___x_2176_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clearValue___lam__1___boxed(lean_object* v_a_2177_, lean_object* v_fvarId_2178_, lean_object* v___x_2179_, lean_object* v_mvarId_2180_, lean_object* v_mvarId_x27_2181_, lean_object* v_fvars_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_){
_start:
{
lean_object* v_res_2188_; 
v_res_2188_ = l_Lean_MVarId_clearValue___lam__1(v_a_2177_, v_fvarId_2178_, v___x_2179_, v_mvarId_2180_, v_mvarId_x27_2181_, v_fvars_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_);
lean_dec(v___y_2186_);
lean_dec_ref(v___y_2185_);
lean_dec(v___y_2184_);
lean_dec_ref(v___y_2183_);
return v_res_2188_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clearValue(lean_object* v_mvarId_2192_, lean_object* v_fvarId_2193_, lean_object* v_a_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_){
_start:
{
lean_object* v___x_2199_; lean_object* v___x_2200_; 
v___x_2199_ = ((lean_object*)(l_Lean_MVarId_clearValue___closed__1));
lean_inc(v_mvarId_2192_);
v___x_2200_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_2192_, v___x_2199_, v_a_2194_, v_a_2195_, v_a_2196_, v_a_2197_);
if (lean_obj_tag(v___x_2200_) == 0)
{
lean_object* v___x_2201_; 
lean_dec_ref(v___x_2200_);
lean_inc(v_mvarId_2192_);
v___x_2201_ = l_Lean_MVarId_getTag(v_mvarId_2192_, v_a_2194_, v_a_2195_, v_a_2196_, v_a_2197_);
if (lean_obj_tag(v___x_2201_) == 0)
{
lean_object* v_a_2202_; lean_object* v___f_2203_; lean_object* v___x_2204_; 
v_a_2202_ = lean_ctor_get(v___x_2201_, 0);
lean_inc(v_a_2202_);
lean_dec_ref(v___x_2201_);
lean_inc(v_mvarId_2192_);
lean_inc(v_fvarId_2193_);
v___f_2203_ = lean_alloc_closure((void*)(l_Lean_MVarId_clearValue___lam__1___boxed), 11, 4);
lean_closure_set(v___f_2203_, 0, v_a_2202_);
lean_closure_set(v___f_2203_, 1, v_fvarId_2193_);
lean_closure_set(v___f_2203_, 2, v___x_2199_);
lean_closure_set(v___f_2203_, 3, v_mvarId_2192_);
v___x_2204_ = l_Lean_MVarId_withRevertedFrom___redArg(v_mvarId_2192_, v_fvarId_2193_, v___f_2203_, v_a_2194_, v_a_2195_, v_a_2196_, v_a_2197_);
if (lean_obj_tag(v___x_2204_) == 0)
{
lean_object* v_a_2205_; lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2213_; 
v_a_2205_ = lean_ctor_get(v___x_2204_, 0);
v_isSharedCheck_2213_ = !lean_is_exclusive(v___x_2204_);
if (v_isSharedCheck_2213_ == 0)
{
v___x_2207_ = v___x_2204_;
v_isShared_2208_ = v_isSharedCheck_2213_;
goto v_resetjp_2206_;
}
else
{
lean_inc(v_a_2205_);
lean_dec(v___x_2204_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2213_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
lean_object* v_snd_2209_; lean_object* v___x_2211_; 
v_snd_2209_ = lean_ctor_get(v_a_2205_, 1);
lean_inc(v_snd_2209_);
lean_dec(v_a_2205_);
if (v_isShared_2208_ == 0)
{
lean_ctor_set(v___x_2207_, 0, v_snd_2209_);
v___x_2211_ = v___x_2207_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2212_; 
v_reuseFailAlloc_2212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2212_, 0, v_snd_2209_);
v___x_2211_ = v_reuseFailAlloc_2212_;
goto v_reusejp_2210_;
}
v_reusejp_2210_:
{
return v___x_2211_;
}
}
}
else
{
lean_object* v_a_2214_; lean_object* v___x_2216_; uint8_t v_isShared_2217_; uint8_t v_isSharedCheck_2221_; 
v_a_2214_ = lean_ctor_get(v___x_2204_, 0);
v_isSharedCheck_2221_ = !lean_is_exclusive(v___x_2204_);
if (v_isSharedCheck_2221_ == 0)
{
v___x_2216_ = v___x_2204_;
v_isShared_2217_ = v_isSharedCheck_2221_;
goto v_resetjp_2215_;
}
else
{
lean_inc(v_a_2214_);
lean_dec(v___x_2204_);
v___x_2216_ = lean_box(0);
v_isShared_2217_ = v_isSharedCheck_2221_;
goto v_resetjp_2215_;
}
v_resetjp_2215_:
{
lean_object* v___x_2219_; 
if (v_isShared_2217_ == 0)
{
v___x_2219_ = v___x_2216_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v_a_2214_);
v___x_2219_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2218_;
}
v_reusejp_2218_:
{
return v___x_2219_;
}
}
}
}
else
{
lean_object* v_a_2222_; lean_object* v___x_2224_; uint8_t v_isShared_2225_; uint8_t v_isSharedCheck_2229_; 
lean_dec(v_fvarId_2193_);
lean_dec(v_mvarId_2192_);
v_a_2222_ = lean_ctor_get(v___x_2201_, 0);
v_isSharedCheck_2229_ = !lean_is_exclusive(v___x_2201_);
if (v_isSharedCheck_2229_ == 0)
{
v___x_2224_ = v___x_2201_;
v_isShared_2225_ = v_isSharedCheck_2229_;
goto v_resetjp_2223_;
}
else
{
lean_inc(v_a_2222_);
lean_dec(v___x_2201_);
v___x_2224_ = lean_box(0);
v_isShared_2225_ = v_isSharedCheck_2229_;
goto v_resetjp_2223_;
}
v_resetjp_2223_:
{
lean_object* v___x_2227_; 
if (v_isShared_2225_ == 0)
{
v___x_2227_ = v___x_2224_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v_a_2222_);
v___x_2227_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
return v___x_2227_;
}
}
}
}
else
{
lean_object* v_a_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2237_; 
lean_dec(v_fvarId_2193_);
lean_dec(v_mvarId_2192_);
v_a_2230_ = lean_ctor_get(v___x_2200_, 0);
v_isSharedCheck_2237_ = !lean_is_exclusive(v___x_2200_);
if (v_isSharedCheck_2237_ == 0)
{
v___x_2232_ = v___x_2200_;
v_isShared_2233_ = v_isSharedCheck_2237_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_a_2230_);
lean_dec(v___x_2200_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2237_;
goto v_resetjp_2231_;
}
v_resetjp_2231_:
{
lean_object* v___x_2235_; 
if (v_isShared_2233_ == 0)
{
v___x_2235_ = v___x_2232_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v_a_2230_);
v___x_2235_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
return v___x_2235_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clearValue___boxed(lean_object* v_mvarId_2238_, lean_object* v_fvarId_2239_, lean_object* v_a_2240_, lean_object* v_a_2241_, lean_object* v_a_2242_, lean_object* v_a_2243_, lean_object* v_a_2244_){
_start:
{
lean_object* v_res_2245_; 
v_res_2245_ = l_Lean_MVarId_clearValue(v_mvarId_2238_, v_fvarId_2239_, v_a_2240_, v_a_2241_, v_a_2242_, v_a_2243_);
lean_dec(v_a_2243_);
lean_dec_ref(v_a_2242_);
lean_dec(v_a_2241_);
lean_dec_ref(v_a_2240_);
return v_res_2245_;
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
