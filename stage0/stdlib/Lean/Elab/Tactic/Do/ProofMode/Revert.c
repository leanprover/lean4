// Lean compiler output
// Module: Lean.Elab.Tactic.Do.ProofMode.Revert
// Imports: public import Lean.Elab.Tactic.Do.ProofMode.Focus public import Lean.Elab.Tactic.Do.ProofMode.Basic
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
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEST(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_mkApp8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l_Lean_mkAppRev(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_mkAndN(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_zip___redArg(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Meta_mkAndIntroN___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDeclsDND___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Array_mapFinIdxM_map___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_consumeMData(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Elab_Term_instMonadTermElabM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instMonadTermElabM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_instMonadTacticM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_instMonadTacticM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_Pi_instInhabited___redArg___lam__0(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAndIntroN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkCons(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instMonadExceptOfExceptionCoreM;
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadQuotationCoreM;
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadFunctor___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadLift___lam__0___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instAddMessageContextMetaM;
lean_object* l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getNat(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Revert"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__0___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "revert"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "SPred"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "imp"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(254, 180, 127, 119, 35, 232, 80, 131)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "s"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__6___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__6___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__6___closed__0_value),LEAN_SCALAR_PTR_LITERAL(203, 235, 49, 11, 232, 138, 137, 74)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__6___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__6___closed__1_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__5___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__6___closed__1_value)} };
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__6___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__6___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__12___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "and_pure_intro_r"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__12___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__12___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__12___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__12___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__12___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__12___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__12___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__12___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__12___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(167, 48, 44, 122, 88, 53, 63, 251)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__12___closed__1_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__12___closed__1_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(71, 102, 82, 181, 251, 135, 109, 75)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__12___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__12___closed__1_value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__12___closed__0_value),LEAN_SCALAR_PTR_LITERAL(191, 18, 141, 40, 4, 84, 240, 126)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__12___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__12___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__0_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__1_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__2_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__3_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__4_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__5_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__0_value),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__1_value)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__7_value),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__2_value),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__3_value),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__4_value),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__5_value)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__8_value),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__6_value)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__16(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__17___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_mkEqRefl___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__17___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__17___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__17___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__19___boxed(lean_object**);
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__0;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__1;
static const lean_closure_object l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__2_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__3_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__4_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__5_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_inferType___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__21(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__2, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__0_value;
static const lean_array_object l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__2;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__3;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__4;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__5;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__6;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__7;
static const lean_closure_object l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadFunctor___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__8_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__9_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__10_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__11;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__12;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "mrevert: expected "};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__13 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__13_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__14;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = " excess arguments in "};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__15 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__15_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__16;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = ", got "};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__17 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__17_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__18;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mRevert___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__4___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mRevert___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__4___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__4___closed__0_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mRevert___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__4___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__4___closed__0_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mRevert___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__4___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__4___closed__0_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(167, 48, 44, 122, 88, 53, 63, 251)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mRevert___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__4___closed__0_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__4___closed__0_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(71, 102, 82, 181, 251, 135, 109, 75)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mRevert___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__4___closed__0_value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(184, 151, 230, 187, 161, 145, 194, 84)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevert___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__4___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__4___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevert___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevert___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15_spec__20_spec__22___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15_spec__20___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15_spec__21___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15_spec__21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__7(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__6(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__3(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__13(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__13___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19_spec__21___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19_spec__21___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19_spec__21___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19_spec__21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_instMonadTermElabM___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___redArg___closed__0_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_instMonadTermElabM___lam__1___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___redArg___closed__1_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_instMonadTacticM___lam__0___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___redArg___closed__2_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_instMonadTacticM___lam__1___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___redArg___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___redArg___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__2___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "mrevert"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__2_value),LEAN_SCALAR_PTR_LITERAL(82, 105, 168, 208, 87, 76, 255, 172)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "mrevertPat_"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__4_value),LEAN_SCALAR_PTR_LITERAL(237, 56, 253, 143, 81, 27, 28, 109)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 12, .m_data = "mrevertPat∀_"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__7_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__7_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__6_value),LEAN_SCALAR_PTR_LITERAL(191, 101, 4, 189, 225, 175, 44, 14)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__7_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__8_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__9_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Not in proof mode"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__10_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__11;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__2(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15_spec__20(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15_spec__21(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19_spec__21(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15_spec__20_spec__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "ProofMode"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "elabMRevert"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(101, 141, 64, 183, 187, 157, 254, 157)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__3_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__3_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(255, 74, 68, 148, 0, 14, 81, 75)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__3_value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(44, 153, 154, 234, 0, 151, 169, 237)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__0(lean_object* v___x_4_, lean_object* v___x_5_, lean_object* v___x_6_, lean_object* v___x_7_, lean_object* v_00_u03c3s_8_, lean_object* v_hyps_9_, lean_object* v_restHyps_10_, lean_object* v_focusHyp_11_, lean_object* v_target_12_, lean_object* v_proof_13_, lean_object* v_toPure_14_, lean_object* v_prf_15_){
_start:
{
lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v_prf_21_; lean_object* v___x_22_; 
v___x_16_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__0___closed__0));
v___x_17_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__0___closed__1));
v___x_18_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__0___closed__2));
v___x_19_ = l_Lean_Name_mkStr6(v___x_4_, v___x_5_, v___x_6_, v___x_16_, v___x_17_, v___x_18_);
v___x_20_ = l_Lean_mkConst(v___x_19_, v___x_7_);
v_prf_21_ = l_Lean_mkApp7(v___x_20_, v_00_u03c3s_8_, v_hyps_9_, v_restHyps_10_, v_focusHyp_11_, v_target_12_, v_proof_13_, v_prf_15_);
v___x_22_ = lean_apply_2(v_toPure_14_, lean_box(0), v_prf_21_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1(lean_object* v_goal_32_, lean_object* v_toPure_33_, lean_object* v_k_34_, lean_object* v_toBind_35_, lean_object* v_res_36_){
_start:
{
lean_object* v_u_37_; lean_object* v_00_u03c3s_38_; lean_object* v_hyps_39_; lean_object* v_target_40_; lean_object* v___x_42_; uint8_t v_isShared_43_; uint8_t v_isSharedCheck_61_; 
v_u_37_ = lean_ctor_get(v_goal_32_, 0);
v_00_u03c3s_38_ = lean_ctor_get(v_goal_32_, 1);
v_hyps_39_ = lean_ctor_get(v_goal_32_, 2);
v_target_40_ = lean_ctor_get(v_goal_32_, 3);
v_isSharedCheck_61_ = !lean_is_exclusive(v_goal_32_);
if (v_isSharedCheck_61_ == 0)
{
v___x_42_ = v_goal_32_;
v_isShared_43_ = v_isSharedCheck_61_;
goto v_resetjp_41_;
}
else
{
lean_inc(v_target_40_);
lean_inc(v_hyps_39_);
lean_inc(v_00_u03c3s_38_);
lean_inc(v_u_37_);
lean_dec(v_goal_32_);
v___x_42_ = lean_box(0);
v_isShared_43_ = v_isSharedCheck_61_;
goto v_resetjp_41_;
}
v_resetjp_41_:
{
lean_object* v_focusHyp_44_; lean_object* v_restHyps_45_; lean_object* v_proof_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___f_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_57_; 
v_focusHyp_44_ = lean_ctor_get(v_res_36_, 0);
lean_inc_ref(v_focusHyp_44_);
v_restHyps_45_ = lean_ctor_get(v_res_36_, 1);
lean_inc_ref(v_restHyps_45_);
v_proof_46_ = lean_ctor_get(v_res_36_, 2);
lean_inc_ref(v_proof_46_);
lean_dec_ref(v_res_36_);
v___x_47_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__0));
v___x_48_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__1));
v___x_49_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__2));
v___x_50_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__4));
v___x_51_ = lean_box(0);
lean_inc(v_u_37_);
v___x_52_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_52_, 0, v_u_37_);
lean_ctor_set(v___x_52_, 1, v___x_51_);
lean_inc_ref(v_target_40_);
lean_inc_ref(v_focusHyp_44_);
lean_inc_ref(v_restHyps_45_);
lean_inc_ref(v_00_u03c3s_38_);
lean_inc_ref(v___x_52_);
v___f_53_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__0), 12, 11);
lean_closure_set(v___f_53_, 0, v___x_47_);
lean_closure_set(v___f_53_, 1, v___x_48_);
lean_closure_set(v___f_53_, 2, v___x_49_);
lean_closure_set(v___f_53_, 3, v___x_52_);
lean_closure_set(v___f_53_, 4, v_00_u03c3s_38_);
lean_closure_set(v___f_53_, 5, v_hyps_39_);
lean_closure_set(v___f_53_, 6, v_restHyps_45_);
lean_closure_set(v___f_53_, 7, v_focusHyp_44_);
lean_closure_set(v___f_53_, 8, v_target_40_);
lean_closure_set(v___f_53_, 9, v_proof_46_);
lean_closure_set(v___f_53_, 10, v_toPure_33_);
v___x_54_ = l_Lean_mkConst(v___x_50_, v___x_52_);
lean_inc_ref(v_00_u03c3s_38_);
v___x_55_ = l_Lean_mkApp3(v___x_54_, v_00_u03c3s_38_, v_focusHyp_44_, v_target_40_);
if (v_isShared_43_ == 0)
{
lean_ctor_set(v___x_42_, 3, v___x_55_);
lean_ctor_set(v___x_42_, 2, v_restHyps_45_);
v___x_57_ = v___x_42_;
goto v_reusejp_56_;
}
else
{
lean_object* v_reuseFailAlloc_60_; 
v_reuseFailAlloc_60_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_60_, 0, v_u_37_);
lean_ctor_set(v_reuseFailAlloc_60_, 1, v_00_u03c3s_38_);
lean_ctor_set(v_reuseFailAlloc_60_, 2, v_restHyps_45_);
lean_ctor_set(v_reuseFailAlloc_60_, 3, v___x_55_);
v___x_57_ = v_reuseFailAlloc_60_;
goto v_reusejp_56_;
}
v_reusejp_56_:
{
lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_58_ = lean_apply_1(v_k_34_, v___x_57_);
v___x_59_ = lean_apply_4(v_toBind_35_, lean_box(0), lean_box(0), v___x_58_, v___f_53_);
return v___x_59_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg(lean_object* v_inst_62_, lean_object* v_inst_63_, lean_object* v_goal_64_, lean_object* v_ref_65_, lean_object* v_k_66_){
_start:
{
lean_object* v_toApplicative_67_; lean_object* v_toBind_68_; lean_object* v_toPure_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___f_72_; lean_object* v___x_73_; 
v_toApplicative_67_ = lean_ctor_get(v_inst_62_, 0);
lean_inc_ref(v_toApplicative_67_);
v_toBind_68_ = lean_ctor_get(v_inst_62_, 1);
lean_inc(v_toBind_68_);
lean_dec_ref(v_inst_62_);
v_toPure_69_ = lean_ctor_get(v_toApplicative_67_, 1);
lean_inc(v_toPure_69_);
lean_dec_ref(v_toApplicative_67_);
lean_inc_ref(v_goal_64_);
v___x_70_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___boxed), 7, 2);
lean_closure_set(v___x_70_, 0, v_goal_64_);
lean_closure_set(v___x_70_, 1, v_ref_65_);
v___x_71_ = lean_apply_2(v_inst_63_, lean_box(0), v___x_70_);
lean_inc(v_toBind_68_);
v___f_72_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1), 5, 4);
lean_closure_set(v___f_72_, 0, v_goal_64_);
lean_closure_set(v___f_72_, 1, v_toPure_69_);
lean_closure_set(v___f_72_, 2, v_k_66_);
lean_closure_set(v___f_72_, 3, v_toBind_68_);
v___x_73_ = lean_apply_4(v_toBind_68_, lean_box(0), lean_box(0), v___x_71_, v___f_72_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevert(lean_object* v_m_74_, lean_object* v_inst_75_, lean_object* v_inst_76_, lean_object* v_goal_77_, lean_object* v_ref_78_, lean_object* v_k_79_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg(v_inst_75_, v_inst_76_, v_goal_77_, v_ref_78_, v_k_79_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__0(lean_object* v_inst_81_, lean_object* v_x_82_){
_start:
{
lean_object* v_fst_83_; lean_object* v_snd_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v_fst_83_ = lean_ctor_get(v_x_82_, 0);
lean_inc(v_fst_83_);
v_snd_84_ = lean_ctor_get(v_x_82_, 1);
lean_inc(v_snd_84_);
lean_dec_ref(v_x_82_);
v___x_85_ = lean_alloc_closure((void*)(l_Lean_Meta_mkEq___boxed), 7, 2);
lean_closure_set(v___x_85_, 0, v_snd_84_);
lean_closure_set(v___x_85_, 1, v_fst_83_);
v___x_86_ = lean_apply_2(v_inst_81_, lean_box(0), v___x_85_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__1(lean_object* v_hypName_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_){
_start:
{
lean_object* v___x_93_; 
v___x_93_ = l_Lean_Core_mkFreshUserName(v_hypName_87_, v___y_90_, v___y_91_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__1___boxed(lean_object* v_hypName_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__1(v_hypName_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_);
lean_dec(v___y_96_);
lean_dec_ref(v___y_95_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__2(lean_object* v_it_101_, lean_object* v_acc_102_, lean_object* v_recur_103_){
_start:
{
lean_object* v_array_104_; lean_object* v_start_105_; lean_object* v_stop_106_; lean_object* v___x_108_; uint8_t v_isShared_109_; uint8_t v_isSharedCheck_119_; 
v_array_104_ = lean_ctor_get(v_it_101_, 0);
v_start_105_ = lean_ctor_get(v_it_101_, 1);
v_stop_106_ = lean_ctor_get(v_it_101_, 2);
v_isSharedCheck_119_ = !lean_is_exclusive(v_it_101_);
if (v_isSharedCheck_119_ == 0)
{
v___x_108_ = v_it_101_;
v_isShared_109_ = v_isSharedCheck_119_;
goto v_resetjp_107_;
}
else
{
lean_inc(v_stop_106_);
lean_inc(v_start_105_);
lean_inc(v_array_104_);
lean_dec(v_it_101_);
v___x_108_ = lean_box(0);
v_isShared_109_ = v_isSharedCheck_119_;
goto v_resetjp_107_;
}
v_resetjp_107_:
{
uint8_t v___x_110_; 
v___x_110_ = lean_nat_dec_lt(v_start_105_, v_stop_106_);
if (v___x_110_ == 0)
{
lean_del_object(v___x_108_);
lean_dec(v_stop_106_);
lean_dec(v_start_105_);
lean_dec_ref(v_array_104_);
lean_dec_ref(v_recur_103_);
return v_acc_102_;
}
else
{
lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_114_; 
v___x_111_ = lean_unsigned_to_nat(1u);
v___x_112_ = lean_nat_add(v_start_105_, v___x_111_);
lean_inc_ref(v_array_104_);
if (v_isShared_109_ == 0)
{
lean_ctor_set(v___x_108_, 1, v___x_112_);
v___x_114_ = v___x_108_;
goto v_reusejp_113_;
}
else
{
lean_object* v_reuseFailAlloc_118_; 
v_reuseFailAlloc_118_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_118_, 0, v_array_104_);
lean_ctor_set(v_reuseFailAlloc_118_, 1, v___x_112_);
lean_ctor_set(v_reuseFailAlloc_118_, 2, v_stop_106_);
v___x_114_ = v_reuseFailAlloc_118_;
goto v_reusejp_113_;
}
v_reusejp_113_:
{
lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_115_ = lean_array_fget(v_array_104_, v_start_105_);
lean_dec(v_start_105_);
lean_dec_ref(v_array_104_);
v___x_116_ = lean_array_push(v_acc_102_, v___x_115_);
v___x_117_ = lean_apply_3(v_recur_103_, v___x_114_, v___x_116_, lean_box(0));
return v___x_117_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__3(lean_object* v_u_120_, lean_object* v_x1_121_, lean_object* v_x2_122_){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkCons(v_u_120_, v_x1_121_, v_x2_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__4(lean_object* v_toApplicative_124_, lean_object* v_i_125_, lean_object* v_a_126_, lean_object* v_____do__lift_127_){
_start:
{
lean_object* v_toPure_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
v_toPure_128_ = lean_ctor_get(v_toApplicative_124_, 1);
lean_inc(v_toPure_128_);
lean_dec_ref(v_toApplicative_124_);
v___x_129_ = lean_unsigned_to_nat(1u);
v___x_130_ = lean_nat_add(v_i_125_, v___x_129_);
v___x_131_ = lean_name_append_index_after(v_____do__lift_127_, v___x_130_);
v___x_132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_132_, 0, v___x_131_);
lean_ctor_set(v___x_132_, 1, v_a_126_);
v___x_133_ = lean_apply_2(v_toPure_128_, lean_box(0), v___x_132_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__4___boxed(lean_object* v_toApplicative_134_, lean_object* v_i_135_, lean_object* v_a_136_, lean_object* v_____do__lift_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__4(v_toApplicative_134_, v_i_135_, v_a_136_, v_____do__lift_137_);
lean_dec(v_i_135_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__5(lean_object* v___x_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_){
_start:
{
lean_object* v___x_145_; 
v___x_145_ = l_Lean_Core_mkFreshUserName(v___x_139_, v___y_142_, v___y_143_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__5___boxed(lean_object* v___x_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__5(v___x_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_);
lean_dec(v___y_148_);
lean_dec_ref(v___y_147_);
return v_res_152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__6(lean_object* v_toApplicative_158_, lean_object* v_inst_159_, lean_object* v_toBind_160_, lean_object* v_i_161_, lean_object* v_a_162_, lean_object* v_x_163_){
_start:
{
lean_object* v___f_164_; lean_object* v___f_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v___f_164_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__4___boxed), 4, 3);
lean_closure_set(v___f_164_, 0, v_toApplicative_158_);
lean_closure_set(v___f_164_, 1, v_i_161_);
lean_closure_set(v___f_164_, 2, v_a_162_);
v___f_165_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__6___closed__2));
v___x_166_ = lean_apply_2(v_inst_159_, lean_box(0), v___f_165_);
v___x_167_ = lean_apply_4(v_toBind_160_, lean_box(0), lean_box(0), v___x_166_, v___f_164_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__7(lean_object* v_toApplicative_168_, lean_object* v_00_u03c6_169_, lean_object* v_____do__lift_170_){
_start:
{
lean_object* v_toPure_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v_toPure_171_ = lean_ctor_get(v_toApplicative_168_, 1);
lean_inc(v_toPure_171_);
lean_dec_ref(v_toApplicative_168_);
v___x_172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_172_, 0, v_____do__lift_170_);
lean_ctor_set(v___x_172_, 1, v_00_u03c6_169_);
v___x_173_ = lean_apply_2(v_toPure_171_, lean_box(0), v___x_172_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__8(lean_object* v_hypName_174_, lean_object* v_uniq_175_, lean_object* v_toApplicative_176_, lean_object* v_ss_177_, lean_object* v_hyps_178_, uint8_t v___x_179_, uint8_t v___x_180_, uint8_t v___x_181_, lean_object* v_inst_182_, lean_object* v_toBind_183_, lean_object* v_____do__lift_184_){
_start:
{
lean_object* v___x_185_; lean_object* v_00_u03c6_186_; lean_object* v___f_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_185_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_185_, 0, v_hypName_174_);
lean_ctor_set(v___x_185_, 1, v_uniq_175_);
lean_ctor_set(v___x_185_, 2, v_____do__lift_184_);
v_00_u03c6_186_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_185_);
v___f_187_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__7), 3, 2);
lean_closure_set(v___f_187_, 0, v_toApplicative_176_);
lean_closure_set(v___f_187_, 1, v_00_u03c6_186_);
v___x_188_ = lean_box(v___x_179_);
v___x_189_ = lean_box(v___x_180_);
v___x_190_ = lean_box(v___x_179_);
v___x_191_ = lean_box(v___x_180_);
v___x_192_ = lean_box(v___x_181_);
v___x_193_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(v___x_193_, 0, v_ss_177_);
lean_closure_set(v___x_193_, 1, v_hyps_178_);
lean_closure_set(v___x_193_, 2, v___x_188_);
lean_closure_set(v___x_193_, 3, v___x_189_);
lean_closure_set(v___x_193_, 4, v___x_190_);
lean_closure_set(v___x_193_, 5, v___x_191_);
lean_closure_set(v___x_193_, 6, v___x_192_);
v___x_194_ = lean_apply_2(v_inst_182_, lean_box(0), v___x_193_);
v___x_195_ = lean_apply_4(v_toBind_183_, lean_box(0), lean_box(0), v___x_194_, v___f_187_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__8___boxed(lean_object* v_hypName_196_, lean_object* v_uniq_197_, lean_object* v_toApplicative_198_, lean_object* v_ss_199_, lean_object* v_hyps_200_, lean_object* v___x_201_, lean_object* v___x_202_, lean_object* v___x_203_, lean_object* v_inst_204_, lean_object* v_toBind_205_, lean_object* v_____do__lift_206_){
_start:
{
uint8_t v___x_1116__boxed_207_; uint8_t v___x_1117__boxed_208_; uint8_t v___x_1118__boxed_209_; lean_object* v_res_210_; 
v___x_1116__boxed_207_ = lean_unbox(v___x_201_);
v___x_1117__boxed_208_ = lean_unbox(v___x_202_);
v___x_1118__boxed_209_ = lean_unbox(v___x_203_);
v_res_210_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__8(v_hypName_196_, v_uniq_197_, v_toApplicative_198_, v_ss_199_, v_hyps_200_, v___x_1116__boxed_207_, v___x_1117__boxed_208_, v___x_1118__boxed_209_, v_inst_204_, v_toBind_205_, v_____do__lift_206_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__9(lean_object* v_hypName_211_, lean_object* v_toApplicative_212_, lean_object* v_ss_213_, lean_object* v_hyps_214_, uint8_t v___x_215_, lean_object* v_inst_216_, lean_object* v_toBind_217_, lean_object* v_00_u03c6_218_, lean_object* v_uniq_219_){
_start:
{
uint8_t v___x_220_; uint8_t v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___f_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_220_ = 1;
v___x_221_ = 1;
v___x_222_ = lean_box(v___x_215_);
v___x_223_ = lean_box(v___x_220_);
v___x_224_ = lean_box(v___x_221_);
lean_inc(v_toBind_217_);
lean_inc(v_inst_216_);
lean_inc_ref(v_ss_213_);
v___f_225_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__8___boxed), 11, 10);
lean_closure_set(v___f_225_, 0, v_hypName_211_);
lean_closure_set(v___f_225_, 1, v_uniq_219_);
lean_closure_set(v___f_225_, 2, v_toApplicative_212_);
lean_closure_set(v___f_225_, 3, v_ss_213_);
lean_closure_set(v___f_225_, 4, v_hyps_214_);
lean_closure_set(v___f_225_, 5, v___x_222_);
lean_closure_set(v___f_225_, 6, v___x_223_);
lean_closure_set(v___f_225_, 7, v___x_224_);
lean_closure_set(v___f_225_, 8, v_inst_216_);
lean_closure_set(v___f_225_, 9, v_toBind_217_);
v___x_226_ = lean_box(v___x_215_);
v___x_227_ = lean_box(v___x_220_);
v___x_228_ = lean_box(v___x_215_);
v___x_229_ = lean_box(v___x_220_);
v___x_230_ = lean_box(v___x_221_);
v___x_231_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(v___x_231_, 0, v_ss_213_);
lean_closure_set(v___x_231_, 1, v_00_u03c6_218_);
lean_closure_set(v___x_231_, 2, v___x_226_);
lean_closure_set(v___x_231_, 3, v___x_227_);
lean_closure_set(v___x_231_, 4, v___x_228_);
lean_closure_set(v___x_231_, 5, v___x_229_);
lean_closure_set(v___x_231_, 6, v___x_230_);
v___x_232_ = lean_apply_2(v_inst_216_, lean_box(0), v___x_231_);
v___x_233_ = lean_apply_4(v_toBind_217_, lean_box(0), lean_box(0), v___x_232_, v___f_225_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__9___boxed(lean_object* v_hypName_234_, lean_object* v_toApplicative_235_, lean_object* v_ss_236_, lean_object* v_hyps_237_, lean_object* v___x_238_, lean_object* v_inst_239_, lean_object* v_toBind_240_, lean_object* v_00_u03c6_241_, lean_object* v_uniq_242_){
_start:
{
uint8_t v___x_1151__boxed_243_; lean_object* v_res_244_; 
v___x_1151__boxed_243_ = lean_unbox(v___x_238_);
v_res_244_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__9(v_hypName_234_, v_toApplicative_235_, v_ss_236_, v_hyps_237_, v___x_1151__boxed_243_, v_inst_239_, v_toBind_240_, v_00_u03c6_241_, v_uniq_242_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__10(lean_object* v_u_245_, lean_object* v_00_u03c3s_246_, lean_object* v_hypName_247_, lean_object* v_toApplicative_248_, lean_object* v_ss_249_, lean_object* v_hyps_250_, uint8_t v___x_251_, lean_object* v_inst_252_, lean_object* v_toBind_253_, lean_object* v___f_254_, lean_object* v_eqs_255_){
_start:
{
lean_object* v_eqs_256_; lean_object* v_00_u03c6_257_; lean_object* v_00_u03c6_258_; lean_object* v___x_259_; lean_object* v___f_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v_eqs_256_ = lean_array_to_list(v_eqs_255_);
v_00_u03c6_257_ = l_Lean_mkAndN(v_eqs_256_);
v_00_u03c6_258_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure(v_u_245_, v_00_u03c3s_246_, v_00_u03c6_257_);
v___x_259_ = lean_box(v___x_251_);
lean_inc(v_toBind_253_);
lean_inc(v_inst_252_);
v___f_260_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__9___boxed), 9, 8);
lean_closure_set(v___f_260_, 0, v_hypName_247_);
lean_closure_set(v___f_260_, 1, v_toApplicative_248_);
lean_closure_set(v___f_260_, 2, v_ss_249_);
lean_closure_set(v___f_260_, 3, v_hyps_250_);
lean_closure_set(v___f_260_, 4, v___x_259_);
lean_closure_set(v___f_260_, 5, v_inst_252_);
lean_closure_set(v___f_260_, 6, v_toBind_253_);
lean_closure_set(v___f_260_, 7, v_00_u03c6_258_);
v___x_261_ = lean_apply_2(v_inst_252_, lean_box(0), v___f_254_);
v___x_262_ = lean_apply_4(v_toBind_253_, lean_box(0), lean_box(0), v___x_261_, v___f_260_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__10___boxed(lean_object* v_u_263_, lean_object* v_00_u03c3s_264_, lean_object* v_hypName_265_, lean_object* v_toApplicative_266_, lean_object* v_ss_267_, lean_object* v_hyps_268_, lean_object* v___x_269_, lean_object* v_inst_270_, lean_object* v_toBind_271_, lean_object* v___f_272_, lean_object* v_eqs_273_){
_start:
{
uint8_t v___x_1185__boxed_274_; lean_object* v_res_275_; 
v___x_1185__boxed_274_ = lean_unbox(v___x_269_);
v_res_275_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__10(v_u_263_, v_00_u03c3s_264_, v_hypName_265_, v_toApplicative_266_, v_ss_267_, v_hyps_268_, v___x_1185__boxed_274_, v_inst_270_, v_toBind_271_, v___f_272_, v_eqs_273_);
return v_res_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__11(lean_object* v_u_276_, lean_object* v_00_u03c3s_277_, lean_object* v_hypName_278_, lean_object* v_toApplicative_279_, lean_object* v_hyps_280_, uint8_t v___x_281_, lean_object* v_inst_282_, lean_object* v_toBind_283_, lean_object* v___f_284_, lean_object* v_revertArgs_285_, lean_object* v_inst_286_, lean_object* v___f_287_, lean_object* v_ss_288_){
_start:
{
lean_object* v___x_289_; lean_object* v___f_290_; lean_object* v___x_291_; size_t v_sz_292_; size_t v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_289_ = lean_box(v___x_281_);
lean_inc(v_toBind_283_);
lean_inc_ref(v_ss_288_);
v___f_290_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__10___boxed), 11, 10);
lean_closure_set(v___f_290_, 0, v_u_276_);
lean_closure_set(v___f_290_, 1, v_00_u03c3s_277_);
lean_closure_set(v___f_290_, 2, v_hypName_278_);
lean_closure_set(v___f_290_, 3, v_toApplicative_279_);
lean_closure_set(v___f_290_, 4, v_ss_288_);
lean_closure_set(v___f_290_, 5, v_hyps_280_);
lean_closure_set(v___f_290_, 6, v___x_289_);
lean_closure_set(v___f_290_, 7, v_inst_282_);
lean_closure_set(v___f_290_, 8, v_toBind_283_);
lean_closure_set(v___f_290_, 9, v___f_284_);
v___x_291_ = l_Array_zip___redArg(v_revertArgs_285_, v_ss_288_);
lean_dec_ref(v_ss_288_);
v_sz_292_ = lean_array_size(v___x_291_);
v___x_293_ = ((size_t)0ULL);
v___x_294_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_286_, v___f_287_, v_sz_292_, v___x_293_, v___x_291_);
v___x_295_ = lean_apply_4(v_toBind_283_, lean_box(0), lean_box(0), v___x_294_, v___f_290_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__11___boxed(lean_object* v_u_296_, lean_object* v_00_u03c3s_297_, lean_object* v_hypName_298_, lean_object* v_toApplicative_299_, lean_object* v_hyps_300_, lean_object* v___x_301_, lean_object* v_inst_302_, lean_object* v_toBind_303_, lean_object* v___f_304_, lean_object* v_revertArgs_305_, lean_object* v_inst_306_, lean_object* v___f_307_, lean_object* v_ss_308_){
_start:
{
uint8_t v___x_1202__boxed_309_; lean_object* v_res_310_; 
v___x_1202__boxed_309_ = lean_unbox(v___x_301_);
v_res_310_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__11(v_u_296_, v_00_u03c3s_297_, v_hypName_298_, v_toApplicative_299_, v_hyps_300_, v___x_1202__boxed_309_, v_inst_302_, v_toBind_303_, v___f_304_, v_revertArgs_305_, v_inst_306_, v___f_307_, v_ss_308_);
lean_dec_ref(v_revertArgs_305_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__12(lean_object* v_toApplicative_319_, lean_object* v_u_320_, lean_object* v_fst_321_, lean_object* v_revertArgs_322_, lean_object* v_snd_323_, lean_object* v_prf_324_, lean_object* v_00_u03c3s_325_, lean_object* v_hyps_326_, lean_object* v_target_327_, lean_object* v_h_328_, lean_object* v_____do__lift_329_){
_start:
{
lean_object* v_toPure_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v_prf_338_; lean_object* v___x_339_; 
v_toPure_330_ = lean_ctor_get(v_toApplicative_319_, 1);
lean_inc(v_toPure_330_);
lean_dec_ref(v_toApplicative_319_);
v___x_331_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__12___closed__1));
v___x_332_ = lean_box(0);
v___x_333_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_333_, 0, v_u_320_);
lean_ctor_set(v___x_333_, 1, v___x_332_);
v___x_334_ = l_Lean_mkConst(v___x_331_, v___x_333_);
v___x_335_ = l_Lean_mkAppN(v_fst_321_, v_revertArgs_322_);
v___x_336_ = l_Lean_mkAppN(v_snd_323_, v_revertArgs_322_);
v___x_337_ = l_Lean_mkAppN(v_prf_324_, v_revertArgs_322_);
v_prf_338_ = l_Lean_mkApp8(v___x_334_, v_00_u03c3s_325_, v_____do__lift_329_, v_hyps_326_, v___x_335_, v_target_327_, v_h_328_, v___x_336_, v___x_337_);
v___x_339_ = lean_apply_2(v_toPure_330_, lean_box(0), v_prf_338_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__12___boxed(lean_object* v_toApplicative_340_, lean_object* v_u_341_, lean_object* v_fst_342_, lean_object* v_revertArgs_343_, lean_object* v_snd_344_, lean_object* v_prf_345_, lean_object* v_00_u03c3s_346_, lean_object* v_hyps_347_, lean_object* v_target_348_, lean_object* v_h_349_, lean_object* v_____do__lift_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__12(v_toApplicative_340_, v_u_341_, v_fst_342_, v_revertArgs_343_, v_snd_344_, v_prf_345_, v_00_u03c3s_346_, v_hyps_347_, v_target_348_, v_h_349_, v_____do__lift_350_);
lean_dec_ref(v_revertArgs_343_);
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__13(lean_object* v_toApplicative_352_, lean_object* v_u_353_, lean_object* v_fst_354_, lean_object* v_revertArgs_355_, lean_object* v_snd_356_, lean_object* v_00_u03c3s_357_, lean_object* v_hyps_358_, lean_object* v_target_359_, lean_object* v_h_360_, lean_object* v_inst_361_, lean_object* v_toBind_362_, lean_object* v_prf_363_){
_start:
{
lean_object* v___f_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
lean_inc_ref(v_h_360_);
v___f_364_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__12___boxed), 11, 10);
lean_closure_set(v___f_364_, 0, v_toApplicative_352_);
lean_closure_set(v___f_364_, 1, v_u_353_);
lean_closure_set(v___f_364_, 2, v_fst_354_);
lean_closure_set(v___f_364_, 3, v_revertArgs_355_);
lean_closure_set(v___f_364_, 4, v_snd_356_);
lean_closure_set(v___f_364_, 5, v_prf_363_);
lean_closure_set(v___f_364_, 6, v_00_u03c3s_357_);
lean_closure_set(v___f_364_, 7, v_hyps_358_);
lean_closure_set(v___f_364_, 8, v_target_359_);
lean_closure_set(v___f_364_, 9, v_h_360_);
v___x_365_ = lean_alloc_closure((void*)(l_Lean_Meta_inferType___boxed), 6, 1);
lean_closure_set(v___x_365_, 0, v_h_360_);
v___x_366_ = lean_apply_2(v_inst_361_, lean_box(0), v___x_365_);
v___x_367_ = lean_apply_4(v_toBind_362_, lean_box(0), lean_box(0), v___x_366_, v___f_364_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__14(lean_object* v___y_368_, lean_object* v_u_369_, lean_object* v_snd_370_, lean_object* v_toApplicative_371_, lean_object* v_revertArgs_372_, lean_object* v_00_u03c3s_373_, lean_object* v_hyps_374_, lean_object* v_target_375_, lean_object* v_h_376_, lean_object* v_inst_377_, lean_object* v_toBind_378_, lean_object* v_a_379_, lean_object* v_n_380_, lean_object* v_f_381_, lean_object* v_k_382_, lean_object* v_H_383_){
_start:
{
lean_object* v_H_384_; lean_object* v___x_385_; lean_object* v_fst_386_; lean_object* v_snd_387_; lean_object* v___f_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v_goal_x27_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
lean_inc_ref(v___y_368_);
v_H_384_ = l_Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps(v___y_368_, v_H_383_);
lean_inc_ref(v___y_368_);
lean_inc(v_u_369_);
v___x_385_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd(v_u_369_, v___y_368_, v_H_384_, v_snd_370_);
v_fst_386_ = lean_ctor_get(v___x_385_, 0);
lean_inc(v_fst_386_);
v_snd_387_ = lean_ctor_get(v___x_385_, 1);
lean_inc(v_snd_387_);
lean_dec_ref(v___x_385_);
lean_inc(v_toBind_378_);
lean_inc(v_fst_386_);
lean_inc(v_u_369_);
v___f_388_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__13), 12, 11);
lean_closure_set(v___f_388_, 0, v_toApplicative_371_);
lean_closure_set(v___f_388_, 1, v_u_369_);
lean_closure_set(v___f_388_, 2, v_fst_386_);
lean_closure_set(v___f_388_, 3, v_revertArgs_372_);
lean_closure_set(v___f_388_, 4, v_snd_387_);
lean_closure_set(v___f_388_, 5, v_00_u03c3s_373_);
lean_closure_set(v___f_388_, 6, v_hyps_374_);
lean_closure_set(v___f_388_, 7, v_target_375_);
lean_closure_set(v___f_388_, 8, v_h_376_);
lean_closure_set(v___f_388_, 9, v_inst_377_);
lean_closure_set(v___f_388_, 10, v_toBind_378_);
v___x_389_ = lean_array_get_size(v_a_379_);
v___x_390_ = l_Array_toSubarray___redArg(v_a_379_, v_n_380_, v___x_389_);
v___x_391_ = l_Subarray_copy___redArg(v___x_390_);
v___x_392_ = l_Lean_mkAppRev(v_f_381_, v___x_391_);
lean_dec_ref(v___x_391_);
v_goal_x27_393_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_goal_x27_393_, 0, v_u_369_);
lean_ctor_set(v_goal_x27_393_, 1, v___y_368_);
lean_ctor_set(v_goal_x27_393_, 2, v_fst_386_);
lean_ctor_set(v_goal_x27_393_, 3, v___x_392_);
v___x_394_ = lean_apply_1(v_k_382_, v_goal_x27_393_);
v___x_395_ = lean_apply_4(v_toBind_378_, lean_box(0), lean_box(0), v___x_394_, v___f_388_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15(lean_object* v_u_415_, lean_object* v_snd_416_, lean_object* v_toApplicative_417_, lean_object* v_revertArgs_418_, lean_object* v_00_u03c3s_419_, lean_object* v_hyps_420_, lean_object* v_target_421_, lean_object* v_inst_422_, lean_object* v_toBind_423_, lean_object* v_a_424_, lean_object* v_n_425_, lean_object* v_f_426_, lean_object* v_k_427_, lean_object* v_fst_428_, lean_object* v_revertArgsTypes_429_, lean_object* v___x_430_, lean_object* v___f_431_, lean_object* v_h_432_){
_start:
{
lean_object* v___y_434_; lean_object* v___x_439_; lean_object* v___x_440_; uint8_t v___x_441_; 
v___x_439_ = lean_array_get_size(v_revertArgsTypes_429_);
v___x_440_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__9));
v___x_441_ = lean_nat_dec_lt(v___x_430_, v___x_439_);
if (v___x_441_ == 0)
{
lean_dec_ref(v___f_431_);
lean_dec_ref(v_revertArgsTypes_429_);
lean_inc_ref(v_00_u03c3s_419_);
v___y_434_ = v_00_u03c3s_419_;
goto v___jp_433_;
}
else
{
size_t v___x_442_; size_t v___x_443_; lean_object* v___x_444_; 
v___x_442_ = lean_usize_of_nat(v___x_439_);
v___x_443_ = ((size_t)0ULL);
lean_inc_ref(v_00_u03c3s_419_);
v___x_444_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_440_, v___f_431_, v_revertArgsTypes_429_, v___x_442_, v___x_443_, v_00_u03c3s_419_);
v___y_434_ = v___x_444_;
goto v___jp_433_;
}
v___jp_433_:
{
lean_object* v___f_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
lean_inc(v_toBind_423_);
lean_inc(v_inst_422_);
v___f_435_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__14), 16, 15);
lean_closure_set(v___f_435_, 0, v___y_434_);
lean_closure_set(v___f_435_, 1, v_u_415_);
lean_closure_set(v___f_435_, 2, v_snd_416_);
lean_closure_set(v___f_435_, 3, v_toApplicative_417_);
lean_closure_set(v___f_435_, 4, v_revertArgs_418_);
lean_closure_set(v___f_435_, 5, v_00_u03c3s_419_);
lean_closure_set(v___f_435_, 6, v_hyps_420_);
lean_closure_set(v___f_435_, 7, v_target_421_);
lean_closure_set(v___f_435_, 8, v_h_432_);
lean_closure_set(v___f_435_, 9, v_inst_422_);
lean_closure_set(v___f_435_, 10, v_toBind_423_);
lean_closure_set(v___f_435_, 11, v_a_424_);
lean_closure_set(v___f_435_, 12, v_n_425_);
lean_closure_set(v___f_435_, 13, v_f_426_);
lean_closure_set(v___f_435_, 14, v_k_427_);
v___x_436_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateMVarsIfMVarApp___boxed), 6, 1);
lean_closure_set(v___x_436_, 0, v_fst_428_);
v___x_437_ = lean_apply_2(v_inst_422_, lean_box(0), v___x_436_);
v___x_438_ = lean_apply_4(v_toBind_423_, lean_box(0), lean_box(0), v___x_437_, v___f_435_);
return v___x_438_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___boxed(lean_object** _args){
lean_object* v_u_445_ = _args[0];
lean_object* v_snd_446_ = _args[1];
lean_object* v_toApplicative_447_ = _args[2];
lean_object* v_revertArgs_448_ = _args[3];
lean_object* v_00_u03c3s_449_ = _args[4];
lean_object* v_hyps_450_ = _args[5];
lean_object* v_target_451_ = _args[6];
lean_object* v_inst_452_ = _args[7];
lean_object* v_toBind_453_ = _args[8];
lean_object* v_a_454_ = _args[9];
lean_object* v_n_455_ = _args[10];
lean_object* v_f_456_ = _args[11];
lean_object* v_k_457_ = _args[12];
lean_object* v_fst_458_ = _args[13];
lean_object* v_revertArgsTypes_459_ = _args[14];
lean_object* v___x_460_ = _args[15];
lean_object* v___f_461_ = _args[16];
lean_object* v_h_462_ = _args[17];
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15(v_u_445_, v_snd_446_, v_toApplicative_447_, v_revertArgs_448_, v_00_u03c3s_449_, v_hyps_450_, v_target_451_, v_inst_452_, v_toBind_453_, v_a_454_, v_n_455_, v_f_456_, v_k_457_, v_fst_458_, v_revertArgsTypes_459_, v___x_460_, v___f_461_, v_h_462_);
lean_dec(v___x_460_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__16(lean_object* v_inst_464_, lean_object* v_toBind_465_, lean_object* v___f_466_, lean_object* v_prfs_467_){
_start:
{
lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_468_ = lean_array_to_list(v_prfs_467_);
v___x_469_ = lean_alloc_closure((void*)(l_Lean_Meta_mkAndIntroN___boxed), 6, 1);
lean_closure_set(v___x_469_, 0, v___x_468_);
v___x_470_ = lean_apply_2(v_inst_464_, lean_box(0), v___x_469_);
v___x_471_ = lean_apply_4(v_toBind_465_, lean_box(0), lean_box(0), v___x_470_, v___f_466_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__17(lean_object* v_u_473_, lean_object* v_toApplicative_474_, lean_object* v_revertArgs_475_, lean_object* v_00_u03c3s_476_, lean_object* v_hyps_477_, lean_object* v_target_478_, lean_object* v_inst_479_, lean_object* v_toBind_480_, lean_object* v_a_481_, lean_object* v_n_482_, lean_object* v_f_483_, lean_object* v_k_484_, lean_object* v_revertArgsTypes_485_, lean_object* v___x_486_, lean_object* v___f_487_, lean_object* v___x_488_, lean_object* v_____x_489_){
_start:
{
lean_object* v_fst_490_; lean_object* v_snd_491_; lean_object* v___f_492_; lean_object* v___f_493_; lean_object* v___x_494_; size_t v_sz_495_; size_t v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; 
v_fst_490_ = lean_ctor_get(v_____x_489_, 0);
lean_inc(v_fst_490_);
v_snd_491_ = lean_ctor_get(v_____x_489_, 1);
lean_inc(v_snd_491_);
lean_dec_ref(v_____x_489_);
lean_inc(v_toBind_480_);
lean_inc(v_inst_479_);
lean_inc_ref(v_revertArgs_475_);
v___f_492_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___boxed), 18, 17);
lean_closure_set(v___f_492_, 0, v_u_473_);
lean_closure_set(v___f_492_, 1, v_snd_491_);
lean_closure_set(v___f_492_, 2, v_toApplicative_474_);
lean_closure_set(v___f_492_, 3, v_revertArgs_475_);
lean_closure_set(v___f_492_, 4, v_00_u03c3s_476_);
lean_closure_set(v___f_492_, 5, v_hyps_477_);
lean_closure_set(v___f_492_, 6, v_target_478_);
lean_closure_set(v___f_492_, 7, v_inst_479_);
lean_closure_set(v___f_492_, 8, v_toBind_480_);
lean_closure_set(v___f_492_, 9, v_a_481_);
lean_closure_set(v___f_492_, 10, v_n_482_);
lean_closure_set(v___f_492_, 11, v_f_483_);
lean_closure_set(v___f_492_, 12, v_k_484_);
lean_closure_set(v___f_492_, 13, v_fst_490_);
lean_closure_set(v___f_492_, 14, v_revertArgsTypes_485_);
lean_closure_set(v___f_492_, 15, v___x_486_);
lean_closure_set(v___f_492_, 16, v___f_487_);
lean_inc(v_toBind_480_);
lean_inc(v_inst_479_);
v___f_493_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__16), 4, 3);
lean_closure_set(v___f_493_, 0, v_inst_479_);
lean_closure_set(v___f_493_, 1, v_toBind_480_);
lean_closure_set(v___f_493_, 2, v___f_492_);
v___x_494_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__17___closed__0));
v_sz_495_ = lean_array_size(v_revertArgs_475_);
v___x_496_ = ((size_t)0ULL);
v___x_497_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_488_, v___x_494_, v_sz_495_, v___x_496_, v_revertArgs_475_);
v___x_498_ = lean_apply_2(v_inst_479_, lean_box(0), v___x_497_);
v___x_499_ = lean_apply_4(v_toBind_480_, lean_box(0), lean_box(0), v___x_498_, v___f_493_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__17___boxed(lean_object** _args){
lean_object* v_u_500_ = _args[0];
lean_object* v_toApplicative_501_ = _args[1];
lean_object* v_revertArgs_502_ = _args[2];
lean_object* v_00_u03c3s_503_ = _args[3];
lean_object* v_hyps_504_ = _args[4];
lean_object* v_target_505_ = _args[5];
lean_object* v_inst_506_ = _args[6];
lean_object* v_toBind_507_ = _args[7];
lean_object* v_a_508_ = _args[8];
lean_object* v_n_509_ = _args[9];
lean_object* v_f_510_ = _args[10];
lean_object* v_k_511_ = _args[11];
lean_object* v_revertArgsTypes_512_ = _args[12];
lean_object* v___x_513_ = _args[13];
lean_object* v___f_514_ = _args[14];
lean_object* v___x_515_ = _args[15];
lean_object* v_____x_516_ = _args[16];
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__17(v_u_500_, v_toApplicative_501_, v_revertArgs_502_, v_00_u03c3s_503_, v_hyps_504_, v_target_505_, v_inst_506_, v_toBind_507_, v_a_508_, v_n_509_, v_f_510_, v_k_511_, v_revertArgsTypes_512_, v___x_513_, v___f_514_, v___x_515_, v_____x_516_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__18(lean_object* v_inst_518_, lean_object* v_inst_519_, lean_object* v___f_520_, lean_object* v_toBind_521_, lean_object* v___f_522_, lean_object* v_declInfos_523_){
_start:
{
uint8_t v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_524_ = 0;
v___x_525_ = l_Lean_Meta_withLocalDeclsDND___redArg(v_inst_518_, v_inst_519_, v_declInfos_523_, v___f_520_, v___x_524_);
v___x_526_ = lean_apply_4(v_toBind_521_, lean_box(0), lean_box(0), v___x_525_, v___f_522_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__19(lean_object* v_u_527_, lean_object* v_toApplicative_528_, lean_object* v_revertArgs_529_, lean_object* v_00_u03c3s_530_, lean_object* v_hyps_531_, lean_object* v_target_532_, lean_object* v_inst_533_, lean_object* v_toBind_534_, lean_object* v_a_535_, lean_object* v_n_536_, lean_object* v_f_537_, lean_object* v_k_538_, lean_object* v___x_539_, lean_object* v___f_540_, lean_object* v___x_541_, lean_object* v_inst_542_, lean_object* v_inst_543_, lean_object* v___f_544_, lean_object* v___f_545_, lean_object* v_revertArgsTypes_546_){
_start:
{
lean_object* v___f_547_; lean_object* v___f_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
lean_inc(v___x_539_);
lean_inc_ref(v_revertArgsTypes_546_);
lean_inc(v_toBind_534_);
v___f_547_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__17___boxed), 17, 16);
lean_closure_set(v___f_547_, 0, v_u_527_);
lean_closure_set(v___f_547_, 1, v_toApplicative_528_);
lean_closure_set(v___f_547_, 2, v_revertArgs_529_);
lean_closure_set(v___f_547_, 3, v_00_u03c3s_530_);
lean_closure_set(v___f_547_, 4, v_hyps_531_);
lean_closure_set(v___f_547_, 5, v_target_532_);
lean_closure_set(v___f_547_, 6, v_inst_533_);
lean_closure_set(v___f_547_, 7, v_toBind_534_);
lean_closure_set(v___f_547_, 8, v_a_535_);
lean_closure_set(v___f_547_, 9, v_n_536_);
lean_closure_set(v___f_547_, 10, v_f_537_);
lean_closure_set(v___f_547_, 11, v_k_538_);
lean_closure_set(v___f_547_, 12, v_revertArgsTypes_546_);
lean_closure_set(v___f_547_, 13, v___x_539_);
lean_closure_set(v___f_547_, 14, v___f_540_);
lean_closure_set(v___f_547_, 15, v___x_541_);
lean_inc(v_toBind_534_);
lean_inc_ref(v_inst_543_);
v___f_548_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__18), 6, 5);
lean_closure_set(v___f_548_, 0, v_inst_542_);
lean_closure_set(v___f_548_, 1, v_inst_543_);
lean_closure_set(v___f_548_, 2, v___f_544_);
lean_closure_set(v___f_548_, 3, v_toBind_534_);
lean_closure_set(v___f_548_, 4, v___f_547_);
v___x_549_ = lean_array_get_size(v_revertArgsTypes_546_);
v___x_550_ = lean_mk_empty_array_with_capacity(v___x_549_);
v___x_551_ = l_Array_mapFinIdxM_map___redArg(v_inst_543_, v_revertArgsTypes_546_, v___f_545_, v___x_549_, v___x_539_, v___x_550_);
v___x_552_ = lean_apply_4(v_toBind_534_, lean_box(0), lean_box(0), v___x_551_, v___f_548_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__19___boxed(lean_object** _args){
lean_object* v_u_553_ = _args[0];
lean_object* v_toApplicative_554_ = _args[1];
lean_object* v_revertArgs_555_ = _args[2];
lean_object* v_00_u03c3s_556_ = _args[3];
lean_object* v_hyps_557_ = _args[4];
lean_object* v_target_558_ = _args[5];
lean_object* v_inst_559_ = _args[6];
lean_object* v_toBind_560_ = _args[7];
lean_object* v_a_561_ = _args[8];
lean_object* v_n_562_ = _args[9];
lean_object* v_f_563_ = _args[10];
lean_object* v_k_564_ = _args[11];
lean_object* v___x_565_ = _args[12];
lean_object* v___f_566_ = _args[13];
lean_object* v___x_567_ = _args[14];
lean_object* v_inst_568_ = _args[15];
lean_object* v_inst_569_ = _args[16];
lean_object* v___f_570_ = _args[17];
lean_object* v___f_571_ = _args[18];
lean_object* v_revertArgsTypes_572_ = _args[19];
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__19(v_u_553_, v_toApplicative_554_, v_revertArgs_555_, v_00_u03c3s_556_, v_hyps_557_, v_target_558_, v_inst_559_, v_toBind_560_, v_a_561_, v_n_562_, v_f_563_, v_k_564_, v___x_565_, v___f_566_, v___x_567_, v_inst_568_, v_inst_569_, v___f_570_, v___f_571_, v_revertArgsTypes_572_);
return v_res_573_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__0(void){
_start:
{
lean_object* v___x_574_; 
v___x_574_ = l_instMonadEST(lean_box(0), lean_box(0));
return v___x_574_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__1(void){
_start:
{
lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_575_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__0, &l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__0_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__0);
v___x_576_ = l_ReaderT_instMonad___redArg(v___x_575_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20(lean_object* v_inst_582_, lean_object* v_inst_583_, lean_object* v_u_584_, lean_object* v_00_u03c3s_585_, lean_object* v_hypName_586_, lean_object* v_hyps_587_, uint8_t v___x_588_, lean_object* v___f_589_, lean_object* v_revertArgs_590_, lean_object* v___f_591_, lean_object* v_target_592_, lean_object* v_a_593_, lean_object* v_n_594_, lean_object* v_f_595_, lean_object* v_k_596_, lean_object* v___x_597_, lean_object* v___f_598_, lean_object* v_inst_599_, lean_object* v_____r_600_){
_start:
{
lean_object* v_toApplicative_601_; lean_object* v_toBind_602_; lean_object* v___x_603_; lean_object* v_toApplicative_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_671_; 
v_toApplicative_601_ = lean_ctor_get(v_inst_582_, 0);
lean_inc_ref(v_toApplicative_601_);
v_toBind_602_ = lean_ctor_get(v_inst_582_, 1);
lean_inc(v_toBind_602_);
v___x_603_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__1);
v_toApplicative_604_ = lean_ctor_get(v___x_603_, 0);
v_isSharedCheck_671_ = !lean_is_exclusive(v___x_603_);
if (v_isSharedCheck_671_ == 0)
{
lean_object* v_unused_672_; 
v_unused_672_ = lean_ctor_get(v___x_603_, 1);
lean_dec(v_unused_672_);
v___x_606_ = v___x_603_;
v_isShared_607_ = v_isSharedCheck_671_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_toApplicative_604_);
lean_dec(v___x_603_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_671_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v_toFunctor_608_; lean_object* v_toSeq_609_; lean_object* v_toSeqLeft_610_; lean_object* v_toSeqRight_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_669_; 
v_toFunctor_608_ = lean_ctor_get(v_toApplicative_604_, 0);
v_toSeq_609_ = lean_ctor_get(v_toApplicative_604_, 2);
v_toSeqLeft_610_ = lean_ctor_get(v_toApplicative_604_, 3);
v_toSeqRight_611_ = lean_ctor_get(v_toApplicative_604_, 4);
v_isSharedCheck_669_ = !lean_is_exclusive(v_toApplicative_604_);
if (v_isSharedCheck_669_ == 0)
{
lean_object* v_unused_670_; 
v_unused_670_ = lean_ctor_get(v_toApplicative_604_, 1);
lean_dec(v_unused_670_);
v___x_613_ = v_toApplicative_604_;
v_isShared_614_ = v_isSharedCheck_669_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_toSeqRight_611_);
lean_inc(v_toSeqLeft_610_);
lean_inc(v_toSeq_609_);
lean_inc(v_toFunctor_608_);
lean_dec(v_toApplicative_604_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_669_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v___f_615_; lean_object* v___f_616_; lean_object* v___f_617_; lean_object* v___f_618_; lean_object* v___x_619_; lean_object* v___f_620_; lean_object* v___f_621_; lean_object* v___f_622_; lean_object* v___x_624_; 
v___f_615_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__2));
v___f_616_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__3));
lean_inc_ref(v_toFunctor_608_);
v___f_617_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_617_, 0, v_toFunctor_608_);
v___f_618_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_618_, 0, v_toFunctor_608_);
v___x_619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_619_, 0, v___f_617_);
lean_ctor_set(v___x_619_, 1, v___f_618_);
v___f_620_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_620_, 0, v_toSeqRight_611_);
v___f_621_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_621_, 0, v_toSeqLeft_610_);
v___f_622_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_622_, 0, v_toSeq_609_);
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 4, v___f_620_);
lean_ctor_set(v___x_613_, 3, v___f_621_);
lean_ctor_set(v___x_613_, 2, v___f_622_);
lean_ctor_set(v___x_613_, 1, v___f_615_);
lean_ctor_set(v___x_613_, 0, v___x_619_);
v___x_624_ = v___x_613_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v___x_619_);
lean_ctor_set(v_reuseFailAlloc_668_, 1, v___f_615_);
lean_ctor_set(v_reuseFailAlloc_668_, 2, v___f_622_);
lean_ctor_set(v_reuseFailAlloc_668_, 3, v___f_621_);
lean_ctor_set(v_reuseFailAlloc_668_, 4, v___f_620_);
v___x_624_ = v_reuseFailAlloc_668_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
lean_object* v___x_626_; 
if (v_isShared_607_ == 0)
{
lean_ctor_set(v___x_606_, 1, v___f_616_);
lean_ctor_set(v___x_606_, 0, v___x_624_);
v___x_626_ = v___x_606_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v___x_624_);
lean_ctor_set(v_reuseFailAlloc_667_, 1, v___f_616_);
v___x_626_ = v_reuseFailAlloc_667_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
lean_object* v___x_627_; lean_object* v_toApplicative_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_665_; 
v___x_627_ = l_ReaderT_instMonad___redArg(v___x_626_);
v_toApplicative_628_ = lean_ctor_get(v___x_627_, 0);
v_isSharedCheck_665_ = !lean_is_exclusive(v___x_627_);
if (v_isSharedCheck_665_ == 0)
{
lean_object* v_unused_666_; 
v_unused_666_ = lean_ctor_get(v___x_627_, 1);
lean_dec(v_unused_666_);
v___x_630_ = v___x_627_;
v_isShared_631_ = v_isSharedCheck_665_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_toApplicative_628_);
lean_dec(v___x_627_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_665_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
lean_object* v_toFunctor_632_; lean_object* v_toSeq_633_; lean_object* v_toSeqLeft_634_; lean_object* v_toSeqRight_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_663_; 
v_toFunctor_632_ = lean_ctor_get(v_toApplicative_628_, 0);
v_toSeq_633_ = lean_ctor_get(v_toApplicative_628_, 2);
v_toSeqLeft_634_ = lean_ctor_get(v_toApplicative_628_, 3);
v_toSeqRight_635_ = lean_ctor_get(v_toApplicative_628_, 4);
v_isSharedCheck_663_ = !lean_is_exclusive(v_toApplicative_628_);
if (v_isSharedCheck_663_ == 0)
{
lean_object* v_unused_664_; 
v_unused_664_ = lean_ctor_get(v_toApplicative_628_, 1);
lean_dec(v_unused_664_);
v___x_637_ = v_toApplicative_628_;
v_isShared_638_ = v_isSharedCheck_663_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_toSeqRight_635_);
lean_inc(v_toSeqLeft_634_);
lean_inc(v_toSeq_633_);
lean_inc(v_toFunctor_632_);
lean_dec(v_toApplicative_628_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_663_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
lean_object* v___f_639_; lean_object* v___x_640_; lean_object* v___f_641_; lean_object* v___f_642_; lean_object* v___f_643_; lean_object* v___f_644_; lean_object* v___f_645_; lean_object* v___x_646_; lean_object* v___f_647_; lean_object* v___f_648_; lean_object* v___f_649_; lean_object* v___x_651_; 
lean_inc(v_toBind_602_);
lean_inc(v_inst_583_);
lean_inc_ref(v_toApplicative_601_);
v___f_639_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__6), 6, 3);
lean_closure_set(v___f_639_, 0, v_toApplicative_601_);
lean_closure_set(v___f_639_, 1, v_inst_583_);
lean_closure_set(v___f_639_, 2, v_toBind_602_);
v___x_640_ = lean_box(v___x_588_);
lean_inc_ref(v_inst_582_);
lean_inc_ref(v_revertArgs_590_);
lean_inc(v_toBind_602_);
lean_inc(v_inst_583_);
lean_inc_ref(v_hyps_587_);
lean_inc_ref(v_toApplicative_601_);
lean_inc_ref(v_00_u03c3s_585_);
lean_inc(v_u_584_);
v___f_641_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__11___boxed), 13, 12);
lean_closure_set(v___f_641_, 0, v_u_584_);
lean_closure_set(v___f_641_, 1, v_00_u03c3s_585_);
lean_closure_set(v___f_641_, 2, v_hypName_586_);
lean_closure_set(v___f_641_, 3, v_toApplicative_601_);
lean_closure_set(v___f_641_, 4, v_hyps_587_);
lean_closure_set(v___f_641_, 5, v___x_640_);
lean_closure_set(v___f_641_, 6, v_inst_583_);
lean_closure_set(v___f_641_, 7, v_toBind_602_);
lean_closure_set(v___f_641_, 8, v___f_589_);
lean_closure_set(v___f_641_, 9, v_revertArgs_590_);
lean_closure_set(v___f_641_, 10, v_inst_582_);
lean_closure_set(v___f_641_, 11, v___f_591_);
v___f_642_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__4));
v___f_643_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__5));
lean_inc_ref(v_toFunctor_632_);
v___f_644_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_644_, 0, v_toFunctor_632_);
v___f_645_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_645_, 0, v_toFunctor_632_);
v___x_646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_646_, 0, v___f_644_);
lean_ctor_set(v___x_646_, 1, v___f_645_);
v___f_647_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_647_, 0, v_toSeqRight_635_);
v___f_648_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_648_, 0, v_toSeqLeft_634_);
v___f_649_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_649_, 0, v_toSeq_633_);
if (v_isShared_638_ == 0)
{
lean_ctor_set(v___x_637_, 4, v___f_647_);
lean_ctor_set(v___x_637_, 3, v___f_648_);
lean_ctor_set(v___x_637_, 2, v___f_649_);
lean_ctor_set(v___x_637_, 1, v___f_642_);
lean_ctor_set(v___x_637_, 0, v___x_646_);
v___x_651_ = v___x_637_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v___x_646_);
lean_ctor_set(v_reuseFailAlloc_662_, 1, v___f_642_);
lean_ctor_set(v_reuseFailAlloc_662_, 2, v___f_649_);
lean_ctor_set(v_reuseFailAlloc_662_, 3, v___f_648_);
lean_ctor_set(v_reuseFailAlloc_662_, 4, v___f_647_);
v___x_651_ = v_reuseFailAlloc_662_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
lean_object* v___x_653_; 
if (v_isShared_631_ == 0)
{
lean_ctor_set(v___x_630_, 1, v___f_643_);
lean_ctor_set(v___x_630_, 0, v___x_651_);
v___x_653_ = v___x_630_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v___x_651_);
lean_ctor_set(v_reuseFailAlloc_661_, 1, v___f_643_);
v___x_653_ = v_reuseFailAlloc_661_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
lean_object* v___f_654_; lean_object* v___x_655_; size_t v_sz_656_; size_t v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
lean_inc_ref(v___x_653_);
lean_inc(v_toBind_602_);
lean_inc(v_inst_583_);
lean_inc_ref(v_revertArgs_590_);
v___f_654_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__19___boxed), 20, 19);
lean_closure_set(v___f_654_, 0, v_u_584_);
lean_closure_set(v___f_654_, 1, v_toApplicative_601_);
lean_closure_set(v___f_654_, 2, v_revertArgs_590_);
lean_closure_set(v___f_654_, 3, v_00_u03c3s_585_);
lean_closure_set(v___f_654_, 4, v_hyps_587_);
lean_closure_set(v___f_654_, 5, v_target_592_);
lean_closure_set(v___f_654_, 6, v_inst_583_);
lean_closure_set(v___f_654_, 7, v_toBind_602_);
lean_closure_set(v___f_654_, 8, v_a_593_);
lean_closure_set(v___f_654_, 9, v_n_594_);
lean_closure_set(v___f_654_, 10, v_f_595_);
lean_closure_set(v___f_654_, 11, v_k_596_);
lean_closure_set(v___f_654_, 12, v___x_597_);
lean_closure_set(v___f_654_, 13, v___f_598_);
lean_closure_set(v___f_654_, 14, v___x_653_);
lean_closure_set(v___f_654_, 15, v_inst_599_);
lean_closure_set(v___f_654_, 16, v_inst_582_);
lean_closure_set(v___f_654_, 17, v___f_641_);
lean_closure_set(v___f_654_, 18, v___f_639_);
v___x_655_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__6));
v_sz_656_ = lean_array_size(v_revertArgs_590_);
v___x_657_ = ((size_t)0ULL);
v___x_658_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_653_, v___x_655_, v_sz_656_, v___x_657_, v_revertArgs_590_);
v___x_659_ = lean_apply_2(v_inst_583_, lean_box(0), v___x_658_);
v___x_660_ = lean_apply_4(v_toBind_602_, lean_box(0), lean_box(0), v___x_659_, v___f_654_);
return v___x_660_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___boxed(lean_object** _args){
lean_object* v_inst_673_ = _args[0];
lean_object* v_inst_674_ = _args[1];
lean_object* v_u_675_ = _args[2];
lean_object* v_00_u03c3s_676_ = _args[3];
lean_object* v_hypName_677_ = _args[4];
lean_object* v_hyps_678_ = _args[5];
lean_object* v___x_679_ = _args[6];
lean_object* v___f_680_ = _args[7];
lean_object* v_revertArgs_681_ = _args[8];
lean_object* v___f_682_ = _args[9];
lean_object* v_target_683_ = _args[10];
lean_object* v_a_684_ = _args[11];
lean_object* v_n_685_ = _args[12];
lean_object* v_f_686_ = _args[13];
lean_object* v_k_687_ = _args[14];
lean_object* v___x_688_ = _args[15];
lean_object* v___f_689_ = _args[16];
lean_object* v_inst_690_ = _args[17];
lean_object* v_____r_691_ = _args[18];
_start:
{
uint8_t v___x_1546__boxed_692_; lean_object* v_res_693_; 
v___x_1546__boxed_692_ = lean_unbox(v___x_679_);
v_res_693_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20(v_inst_673_, v_inst_674_, v_u_675_, v_00_u03c3s_676_, v_hypName_677_, v_hyps_678_, v___x_1546__boxed_692_, v___f_680_, v_revertArgs_681_, v___f_682_, v_target_683_, v_a_684_, v_n_685_, v_f_686_, v_k_687_, v___x_688_, v___f_689_, v_inst_690_, v_____r_691_);
return v_res_693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__21(lean_object* v___f_694_, lean_object* v_____r_695_){
_start:
{
lean_object* v___x_696_; 
v___x_696_ = lean_apply_1(v___f_694_, v_____r_695_);
return v___x_696_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__2(void){
_start:
{
lean_object* v___x_700_; lean_object* v___f_701_; 
v___x_700_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_701_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_701_, 0, v___x_700_);
return v___f_701_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__3(void){
_start:
{
lean_object* v___x_702_; lean_object* v___f_703_; 
v___x_702_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_703_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_703_, 0, v___x_702_);
return v___f_703_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__4(void){
_start:
{
lean_object* v___f_704_; lean_object* v___f_705_; lean_object* v___x_706_; 
v___f_704_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__3, &l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__3_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__3);
v___f_705_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__2, &l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__2);
v___x_706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_706_, 0, v___f_705_);
lean_ctor_set(v___x_706_, 1, v___f_704_);
return v___x_706_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__5(void){
_start:
{
lean_object* v___x_707_; lean_object* v___f_708_; 
v___x_707_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__4, &l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__4_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__4);
v___f_708_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_708_, 0, v___x_707_);
return v___f_708_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__6(void){
_start:
{
lean_object* v___x_709_; lean_object* v___f_710_; 
v___x_709_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__4, &l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__4_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__4);
v___f_710_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_710_, 0, v___x_709_);
return v___f_710_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__7(void){
_start:
{
lean_object* v___f_711_; lean_object* v___f_712_; lean_object* v___x_713_; 
v___f_711_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__6, &l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__6_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__6);
v___f_712_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__5, &l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__5_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__5);
v___x_713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_713_, 0, v___f_712_);
lean_ctor_set(v___x_713_, 1, v___f_711_);
return v___x_713_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__11(void){
_start:
{
lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___f_719_; lean_object* v___x_720_; 
v___x_717_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_718_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__10));
v___f_719_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__8));
v___x_720_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_719_, v___x_718_, v___x_717_);
return v___x_720_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__12(void){
_start:
{
lean_object* v___x_721_; lean_object* v___f_722_; lean_object* v___f_723_; lean_object* v___x_724_; 
v___x_721_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__11, &l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__11_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__11);
v___f_722_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__9));
v___f_723_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__8));
v___x_724_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_723_, v___f_722_, v___x_721_);
return v___x_724_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__14(void){
_start:
{
lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_726_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__13));
v___x_727_ = l_Lean_stringToMessageData(v___x_726_);
return v___x_727_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__16(void){
_start:
{
lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_729_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__15));
v___x_730_ = l_Lean_stringToMessageData(v___x_729_);
return v___x_730_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__18(void){
_start:
{
lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_732_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__17));
v___x_733_ = l_Lean_stringToMessageData(v___x_732_);
return v___x_733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg(lean_object* v_inst_734_, lean_object* v_inst_735_, lean_object* v_inst_736_, lean_object* v_goal_737_, lean_object* v_n_738_, lean_object* v_hypName_739_, lean_object* v_k_740_){
_start:
{
lean_object* v___x_741_; uint8_t v___x_742_; 
v___x_741_ = lean_unsigned_to_nat(0u);
v___x_742_ = lean_nat_dec_eq(v_n_738_, v___x_741_);
if (v___x_742_ == 0)
{
lean_object* v_u_743_; lean_object* v_00_u03c3s_744_; lean_object* v_hyps_745_; lean_object* v_target_746_; lean_object* v___f_747_; lean_object* v___f_748_; lean_object* v___f_749_; lean_object* v___f_750_; lean_object* v_T_751_; lean_object* v_f_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v_a_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v_revertArgs_759_; lean_object* v___x_760_; lean_object* v___f_761_; lean_object* v___x_762_; uint8_t v___x_763_; 
v_u_743_ = lean_ctor_get(v_goal_737_, 0);
lean_inc(v_u_743_);
v_00_u03c3s_744_ = lean_ctor_get(v_goal_737_, 1);
lean_inc_ref(v_00_u03c3s_744_);
v_hyps_745_ = lean_ctor_get(v_goal_737_, 2);
lean_inc_ref(v_hyps_745_);
v_target_746_ = lean_ctor_get(v_goal_737_, 3);
lean_inc_ref(v_target_746_);
lean_dec_ref(v_goal_737_);
lean_inc(v_inst_736_);
v___f_747_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__0), 2, 1);
lean_closure_set(v___f_747_, 0, v_inst_736_);
lean_inc(v_hypName_739_);
v___f_748_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__1___boxed), 6, 1);
lean_closure_set(v___f_748_, 0, v_hypName_739_);
v___f_749_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__0));
lean_inc(v_u_743_);
v___f_750_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__3), 3, 1);
lean_closure_set(v___f_750_, 0, v_u_743_);
v_T_751_ = l_Lean_Expr_consumeMData(v_target_746_);
v_f_752_ = l_Lean_Expr_getAppFn(v_T_751_);
v___x_753_ = l_Lean_Expr_getAppNumArgs(v_T_751_);
v___x_754_ = lean_mk_empty_array_with_capacity(v___x_753_);
lean_dec(v___x_753_);
lean_inc_ref(v_T_751_);
v_a_755_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_T_751_, v___x_754_);
lean_inc(v_n_738_);
lean_inc_ref(v_a_755_);
v___x_756_ = l_Array_toSubarray___redArg(v_a_755_, v___x_741_, v_n_738_);
v___x_757_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__1));
v___x_758_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_749_, v___x_756_, v___x_757_);
v_revertArgs_759_ = l_Array_reverse___redArg(v___x_758_);
v___x_760_ = lean_box(v___x_742_);
lean_inc_ref(v_inst_735_);
lean_inc_ref(v___f_750_);
lean_inc(v_k_740_);
lean_inc_ref(v_f_752_);
lean_inc(v_n_738_);
lean_inc_ref(v_a_755_);
lean_inc_ref(v_target_746_);
lean_inc_ref(v___f_747_);
lean_inc_ref(v_revertArgs_759_);
lean_inc_ref(v___f_748_);
lean_inc_ref(v_hyps_745_);
lean_inc(v_hypName_739_);
lean_inc_ref(v_00_u03c3s_744_);
lean_inc(v_u_743_);
lean_inc(v_inst_736_);
lean_inc_ref(v_inst_734_);
v___f_761_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___boxed), 19, 18);
lean_closure_set(v___f_761_, 0, v_inst_734_);
lean_closure_set(v___f_761_, 1, v_inst_736_);
lean_closure_set(v___f_761_, 2, v_u_743_);
lean_closure_set(v___f_761_, 3, v_00_u03c3s_744_);
lean_closure_set(v___f_761_, 4, v_hypName_739_);
lean_closure_set(v___f_761_, 5, v_hyps_745_);
lean_closure_set(v___f_761_, 6, v___x_760_);
lean_closure_set(v___f_761_, 7, v___f_748_);
lean_closure_set(v___f_761_, 8, v_revertArgs_759_);
lean_closure_set(v___f_761_, 9, v___f_747_);
lean_closure_set(v___f_761_, 10, v_target_746_);
lean_closure_set(v___f_761_, 11, v_a_755_);
lean_closure_set(v___f_761_, 12, v_n_738_);
lean_closure_set(v___f_761_, 13, v_f_752_);
lean_closure_set(v___f_761_, 14, v_k_740_);
lean_closure_set(v___f_761_, 15, v___x_741_);
lean_closure_set(v___f_761_, 16, v___f_750_);
lean_closure_set(v___f_761_, 17, v_inst_735_);
v___x_762_ = lean_array_get_size(v_revertArgs_759_);
v___x_763_ = lean_nat_dec_eq(v___x_762_, v_n_738_);
if (v___x_763_ == 0)
{
lean_object* v_toBind_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_855_; 
lean_dec_ref(v_revertArgs_759_);
lean_dec_ref(v_a_755_);
lean_dec_ref(v_f_752_);
lean_dec_ref(v___f_750_);
lean_dec_ref(v___f_748_);
lean_dec_ref(v___f_747_);
lean_dec_ref(v_target_746_);
lean_dec_ref(v_hyps_745_);
lean_dec_ref(v_00_u03c3s_744_);
lean_dec(v_u_743_);
lean_dec(v_k_740_);
lean_dec(v_hypName_739_);
lean_dec_ref(v_inst_735_);
v_toBind_764_ = lean_ctor_get(v_inst_734_, 1);
v_isSharedCheck_855_ = !lean_is_exclusive(v_inst_734_);
if (v_isSharedCheck_855_ == 0)
{
lean_object* v_unused_856_; 
v_unused_856_ = lean_ctor_get(v_inst_734_, 0);
lean_dec(v_unused_856_);
v___x_766_ = v_inst_734_;
v_isShared_767_ = v_isSharedCheck_855_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_toBind_764_);
lean_dec(v_inst_734_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_855_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
lean_object* v___x_768_; lean_object* v_toApplicative_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_853_; 
v___x_768_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__1);
v_toApplicative_769_ = lean_ctor_get(v___x_768_, 0);
v_isSharedCheck_853_ = !lean_is_exclusive(v___x_768_);
if (v_isSharedCheck_853_ == 0)
{
lean_object* v_unused_854_; 
v_unused_854_ = lean_ctor_get(v___x_768_, 1);
lean_dec(v_unused_854_);
v___x_771_ = v___x_768_;
v_isShared_772_ = v_isSharedCheck_853_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_toApplicative_769_);
lean_dec(v___x_768_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_853_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v_toFunctor_773_; lean_object* v_toSeq_774_; lean_object* v_toSeqLeft_775_; lean_object* v_toSeqRight_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_851_; 
v_toFunctor_773_ = lean_ctor_get(v_toApplicative_769_, 0);
v_toSeq_774_ = lean_ctor_get(v_toApplicative_769_, 2);
v_toSeqLeft_775_ = lean_ctor_get(v_toApplicative_769_, 3);
v_toSeqRight_776_ = lean_ctor_get(v_toApplicative_769_, 4);
v_isSharedCheck_851_ = !lean_is_exclusive(v_toApplicative_769_);
if (v_isSharedCheck_851_ == 0)
{
lean_object* v_unused_852_; 
v_unused_852_ = lean_ctor_get(v_toApplicative_769_, 1);
lean_dec(v_unused_852_);
v___x_778_ = v_toApplicative_769_;
v_isShared_779_ = v_isSharedCheck_851_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_toSeqRight_776_);
lean_inc(v_toSeqLeft_775_);
lean_inc(v_toSeq_774_);
lean_inc(v_toFunctor_773_);
lean_dec(v_toApplicative_769_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_851_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___f_780_; lean_object* v___f_781_; lean_object* v___f_782_; lean_object* v___f_783_; lean_object* v___x_785_; 
v___f_780_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__2));
v___f_781_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__3));
lean_inc_ref(v_toFunctor_773_);
v___f_782_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_782_, 0, v_toFunctor_773_);
v___f_783_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_783_, 0, v_toFunctor_773_);
if (v_isShared_767_ == 0)
{
lean_ctor_set(v___x_766_, 1, v___f_783_);
lean_ctor_set(v___x_766_, 0, v___f_782_);
v___x_785_ = v___x_766_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v___f_782_);
lean_ctor_set(v_reuseFailAlloc_850_, 1, v___f_783_);
v___x_785_ = v_reuseFailAlloc_850_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
lean_object* v___f_786_; lean_object* v___f_787_; lean_object* v___f_788_; lean_object* v___x_790_; 
v___f_786_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_786_, 0, v_toSeqRight_776_);
v___f_787_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_787_, 0, v_toSeqLeft_775_);
v___f_788_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_788_, 0, v_toSeq_774_);
if (v_isShared_779_ == 0)
{
lean_ctor_set(v___x_778_, 4, v___f_786_);
lean_ctor_set(v___x_778_, 3, v___f_787_);
lean_ctor_set(v___x_778_, 2, v___f_788_);
lean_ctor_set(v___x_778_, 1, v___f_780_);
lean_ctor_set(v___x_778_, 0, v___x_785_);
v___x_790_ = v___x_778_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v___x_785_);
lean_ctor_set(v_reuseFailAlloc_849_, 1, v___f_780_);
lean_ctor_set(v_reuseFailAlloc_849_, 2, v___f_788_);
lean_ctor_set(v_reuseFailAlloc_849_, 3, v___f_787_);
lean_ctor_set(v_reuseFailAlloc_849_, 4, v___f_786_);
v___x_790_ = v_reuseFailAlloc_849_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
lean_object* v___x_792_; 
if (v_isShared_772_ == 0)
{
lean_ctor_set(v___x_771_, 1, v___f_781_);
lean_ctor_set(v___x_771_, 0, v___x_790_);
v___x_792_ = v___x_771_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v___x_790_);
lean_ctor_set(v_reuseFailAlloc_848_, 1, v___f_781_);
v___x_792_ = v_reuseFailAlloc_848_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
lean_object* v___x_793_; lean_object* v_toApplicative_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_846_; 
v___x_793_ = l_ReaderT_instMonad___redArg(v___x_792_);
v_toApplicative_794_ = lean_ctor_get(v___x_793_, 0);
v_isSharedCheck_846_ = !lean_is_exclusive(v___x_793_);
if (v_isSharedCheck_846_ == 0)
{
lean_object* v_unused_847_; 
v_unused_847_ = lean_ctor_get(v___x_793_, 1);
lean_dec(v_unused_847_);
v___x_796_ = v___x_793_;
v_isShared_797_ = v_isSharedCheck_846_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_toApplicative_794_);
lean_dec(v___x_793_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_846_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v_toFunctor_798_; lean_object* v_toSeq_799_; lean_object* v_toSeqLeft_800_; lean_object* v_toSeqRight_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_844_; 
v_toFunctor_798_ = lean_ctor_get(v_toApplicative_794_, 0);
v_toSeq_799_ = lean_ctor_get(v_toApplicative_794_, 2);
v_toSeqLeft_800_ = lean_ctor_get(v_toApplicative_794_, 3);
v_toSeqRight_801_ = lean_ctor_get(v_toApplicative_794_, 4);
v_isSharedCheck_844_ = !lean_is_exclusive(v_toApplicative_794_);
if (v_isSharedCheck_844_ == 0)
{
lean_object* v_unused_845_; 
v_unused_845_ = lean_ctor_get(v_toApplicative_794_, 1);
lean_dec(v_unused_845_);
v___x_803_ = v_toApplicative_794_;
v_isShared_804_ = v_isSharedCheck_844_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_toSeqRight_801_);
lean_inc(v_toSeqLeft_800_);
lean_inc(v_toSeq_799_);
lean_inc(v_toFunctor_798_);
lean_dec(v_toApplicative_794_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_844_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v___f_805_; lean_object* v___f_806_; lean_object* v___f_807_; lean_object* v___f_808_; lean_object* v___x_809_; lean_object* v___f_810_; lean_object* v___f_811_; lean_object* v___f_812_; lean_object* v___x_814_; 
v___f_805_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__4));
v___f_806_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__5));
lean_inc_ref(v_toFunctor_798_);
v___f_807_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_807_, 0, v_toFunctor_798_);
v___f_808_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_808_, 0, v_toFunctor_798_);
v___x_809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_809_, 0, v___f_807_);
lean_ctor_set(v___x_809_, 1, v___f_808_);
v___f_810_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_810_, 0, v_toSeqRight_801_);
v___f_811_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_811_, 0, v_toSeqLeft_800_);
v___f_812_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_812_, 0, v_toSeq_799_);
if (v_isShared_804_ == 0)
{
lean_ctor_set(v___x_803_, 4, v___f_810_);
lean_ctor_set(v___x_803_, 3, v___f_811_);
lean_ctor_set(v___x_803_, 2, v___f_812_);
lean_ctor_set(v___x_803_, 1, v___f_805_);
lean_ctor_set(v___x_803_, 0, v___x_809_);
v___x_814_ = v___x_803_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v___x_809_);
lean_ctor_set(v_reuseFailAlloc_843_, 1, v___f_805_);
lean_ctor_set(v_reuseFailAlloc_843_, 2, v___f_812_);
lean_ctor_set(v_reuseFailAlloc_843_, 3, v___f_811_);
lean_ctor_set(v_reuseFailAlloc_843_, 4, v___f_810_);
v___x_814_ = v_reuseFailAlloc_843_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
lean_object* v___x_816_; 
if (v_isShared_797_ == 0)
{
lean_ctor_set(v___x_796_, 1, v___f_806_);
lean_ctor_set(v___x_796_, 0, v___x_814_);
v___x_816_ = v___x_796_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v___x_814_);
lean_ctor_set(v_reuseFailAlloc_842_, 1, v___f_806_);
v___x_816_ = v_reuseFailAlloc_842_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v_toMonadRef_819_; lean_object* v___f_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; 
v___x_817_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__7, &l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__7_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__7);
v___x_818_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__12, &l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__12_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__12);
v_toMonadRef_819_ = lean_ctor_get(v___x_818_, 0);
lean_inc_ref(v_toMonadRef_819_);
v___f_820_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__21), 2, 1);
lean_closure_set(v___f_820_, 0, v___f_761_);
v___x_821_ = l_Lean_Meta_instAddMessageContextMetaM;
lean_inc_ref(v___x_816_);
v___x_822_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___x_821_, v___x_816_);
v___x_823_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_823_, 0, v___x_817_);
lean_ctor_set(v___x_823_, 1, v_toMonadRef_819_);
lean_ctor_set(v___x_823_, 2, v___x_822_);
v___x_824_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__14, &l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__14_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__14);
v___x_825_ = l_Nat_reprFast(v_n_738_);
v___x_826_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_826_, 0, v___x_825_);
v___x_827_ = l_Lean_MessageData_ofFormat(v___x_826_);
v___x_828_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_828_, 0, v___x_824_);
lean_ctor_set(v___x_828_, 1, v___x_827_);
v___x_829_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__16, &l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__16_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__16);
v___x_830_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_830_, 0, v___x_828_);
lean_ctor_set(v___x_830_, 1, v___x_829_);
v___x_831_ = l_Lean_MessageData_ofExpr(v_T_751_);
v___x_832_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_832_, 0, v___x_830_);
lean_ctor_set(v___x_832_, 1, v___x_831_);
v___x_833_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__18, &l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__18_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__18);
v___x_834_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_834_, 0, v___x_832_);
lean_ctor_set(v___x_834_, 1, v___x_833_);
v___x_835_ = l_Nat_reprFast(v___x_762_);
v___x_836_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_836_, 0, v___x_835_);
v___x_837_ = l_Lean_MessageData_ofFormat(v___x_836_);
v___x_838_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_838_, 0, v___x_834_);
lean_ctor_set(v___x_838_, 1, v___x_837_);
v___x_839_ = l_Lean_throwError___redArg(v___x_816_, v___x_823_, v___x_838_);
v___x_840_ = lean_apply_2(v_inst_736_, lean_box(0), v___x_839_);
v___x_841_ = lean_apply_4(v_toBind_764_, lean_box(0), lean_box(0), v___x_840_, v___f_820_);
return v___x_841_;
}
}
}
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_857_; lean_object* v___x_858_; 
lean_dec_ref(v___f_761_);
lean_dec_ref(v_T_751_);
v___x_857_ = lean_box(0);
v___x_858_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20(v_inst_734_, v_inst_736_, v_u_743_, v_00_u03c3s_744_, v_hypName_739_, v_hyps_745_, v___x_742_, v___f_748_, v_revertArgs_759_, v___f_747_, v_target_746_, v_a_755_, v_n_738_, v_f_752_, v_k_740_, v___x_741_, v___f_750_, v_inst_735_, v___x_857_);
return v___x_858_;
}
}
else
{
lean_object* v___x_859_; 
lean_dec(v_hypName_739_);
lean_dec(v_n_738_);
lean_dec(v_inst_736_);
lean_dec_ref(v_inst_735_);
lean_dec_ref(v_inst_734_);
v___x_859_ = lean_apply_1(v_k_740_, v_goal_737_);
return v___x_859_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN(lean_object* v_m_860_, lean_object* v_inst_861_, lean_object* v_inst_862_, lean_object* v_inst_863_, lean_object* v_goal_864_, lean_object* v_n_865_, lean_object* v_hypName_866_, lean_object* v_k_867_){
_start:
{
lean_object* v___x_868_; 
v___x_868_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg(v_inst_861_, v_inst_862_, v_inst_863_, v_goal_864_, v_n_865_, v_hypName_866_, v_k_867_);
return v___x_868_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_869_ = lean_box(0);
v___x_870_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_871_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_871_, 0, v___x_870_);
lean_ctor_set(v___x_871_, 1, v___x_869_);
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg(){
_start:
{
lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_873_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg___closed__0);
v___x_874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_874_, 0, v___x_873_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg___boxed(lean_object* v___y_875_){
_start:
{
lean_object* v_res_876_; 
v_res_876_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg();
return v_res_876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0(lean_object* v_00_u03b1_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_){
_start:
{
lean_object* v___x_887_; 
v___x_887_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg();
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___boxed(lean_object* v_00_u03b1_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_){
_start:
{
lean_object* v_res_898_; 
v_res_898_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0(v_00_u03b1_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_);
lean_dec(v___y_896_);
lean_dec_ref(v___y_895_);
lean_dec(v___y_894_);
lean_dec_ref(v___y_893_);
lean_dec(v___y_892_);
lean_dec_ref(v___y_891_);
lean_dec(v___y_890_);
lean_dec_ref(v___y_889_);
return v_res_898_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___redArg___lam__0(lean_object* v_x_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_){
_start:
{
lean_object* v___x_909_; 
v___x_909_ = lean_apply_9(v_x_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, lean_box(0));
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___redArg___lam__0___boxed(lean_object* v_x_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_){
_start:
{
lean_object* v_res_920_; 
v_res_920_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___redArg___lam__0(v_x_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_);
return v_res_920_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___redArg(lean_object* v_mvarId_921_, lean_object* v_x_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_){
_start:
{
lean_object* v___f_932_; lean_object* v___x_933_; 
v___f_932_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_932_, 0, v_x_922_);
lean_closure_set(v___f_932_, 1, v___y_923_);
lean_closure_set(v___f_932_, 2, v___y_924_);
lean_closure_set(v___f_932_, 3, v___y_925_);
lean_closure_set(v___f_932_, 4, v___y_926_);
v___x_933_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_921_, v___f_932_, v___y_927_, v___y_928_, v___y_929_, v___y_930_);
if (lean_obj_tag(v___x_933_) == 0)
{
return v___x_933_;
}
else
{
lean_object* v_a_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_941_; 
v_a_934_ = lean_ctor_get(v___x_933_, 0);
v_isSharedCheck_941_ = !lean_is_exclusive(v___x_933_);
if (v_isSharedCheck_941_ == 0)
{
v___x_936_ = v___x_933_;
v_isShared_937_ = v_isSharedCheck_941_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_a_934_);
lean_dec(v___x_933_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_941_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v___x_939_; 
if (v_isShared_937_ == 0)
{
v___x_939_ = v___x_936_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v_a_934_);
v___x_939_ = v_reuseFailAlloc_940_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
return v___x_939_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___redArg___boxed(lean_object* v_mvarId_942_, lean_object* v_x_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___redArg(v_mvarId_942_, v_x_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_);
return v_res_953_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3(lean_object* v_00_u03b1_954_, lean_object* v_mvarId_955_, lean_object* v_x_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_){
_start:
{
lean_object* v___x_966_; 
v___x_966_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___redArg(v_mvarId_955_, v_x_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_);
return v___x_966_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___boxed(lean_object* v_00_u03b1_967_, lean_object* v_mvarId_968_, lean_object* v_x_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3(v_00_u03b1_967_, v_mvarId_968_, v_x_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevert___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__4(lean_object* v_goal_987_, lean_object* v_ref_988_, lean_object* v_k_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_){
_start:
{
lean_object* v___x_999_; 
lean_inc(v___y_997_);
lean_inc_ref(v___y_996_);
lean_inc(v___y_995_);
lean_inc_ref(v___y_994_);
lean_inc_ref(v_goal_987_);
v___x_999_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo(v_goal_987_, v_ref_988_, v___y_994_, v___y_995_, v___y_996_, v___y_997_);
if (lean_obj_tag(v___x_999_) == 0)
{
lean_object* v_a_1000_; lean_object* v_u_1001_; lean_object* v_00_u03c3s_1002_; lean_object* v_hyps_1003_; lean_object* v_target_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1031_; 
v_a_1000_ = lean_ctor_get(v___x_999_, 0);
lean_inc(v_a_1000_);
lean_dec_ref(v___x_999_);
v_u_1001_ = lean_ctor_get(v_goal_987_, 0);
v_00_u03c3s_1002_ = lean_ctor_get(v_goal_987_, 1);
v_hyps_1003_ = lean_ctor_get(v_goal_987_, 2);
v_target_1004_ = lean_ctor_get(v_goal_987_, 3);
v_isSharedCheck_1031_ = !lean_is_exclusive(v_goal_987_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1006_ = v_goal_987_;
v_isShared_1007_ = v_isSharedCheck_1031_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_target_1004_);
lean_inc(v_hyps_1003_);
lean_inc(v_00_u03c3s_1002_);
lean_inc(v_u_1001_);
lean_dec(v_goal_987_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1031_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v_focusHyp_1008_; lean_object* v_restHyps_1009_; lean_object* v_proof_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1017_; 
v_focusHyp_1008_ = lean_ctor_get(v_a_1000_, 0);
lean_inc_ref(v_focusHyp_1008_);
v_restHyps_1009_ = lean_ctor_get(v_a_1000_, 1);
lean_inc_ref(v_restHyps_1009_);
v_proof_1010_ = lean_ctor_get(v_a_1000_, 2);
lean_inc_ref(v_proof_1010_);
lean_dec(v_a_1000_);
v___x_1011_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__4));
v___x_1012_ = lean_box(0);
lean_inc(v_u_1001_);
v___x_1013_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1013_, 0, v_u_1001_);
lean_ctor_set(v___x_1013_, 1, v___x_1012_);
lean_inc_ref(v___x_1013_);
v___x_1014_ = l_Lean_mkConst(v___x_1011_, v___x_1013_);
lean_inc_ref(v_target_1004_);
lean_inc_ref(v_focusHyp_1008_);
lean_inc_ref(v_00_u03c3s_1002_);
v___x_1015_ = l_Lean_mkApp3(v___x_1014_, v_00_u03c3s_1002_, v_focusHyp_1008_, v_target_1004_);
lean_inc_ref(v_restHyps_1009_);
lean_inc_ref(v_00_u03c3s_1002_);
if (v_isShared_1007_ == 0)
{
lean_ctor_set(v___x_1006_, 3, v___x_1015_);
lean_ctor_set(v___x_1006_, 2, v_restHyps_1009_);
v___x_1017_ = v___x_1006_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v_u_1001_);
lean_ctor_set(v_reuseFailAlloc_1030_, 1, v_00_u03c3s_1002_);
lean_ctor_set(v_reuseFailAlloc_1030_, 2, v_restHyps_1009_);
lean_ctor_set(v_reuseFailAlloc_1030_, 3, v___x_1015_);
v___x_1017_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
lean_object* v___x_1018_; 
v___x_1018_ = lean_apply_10(v_k_989_, v___x_1017_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, lean_box(0));
if (lean_obj_tag(v___x_1018_) == 0)
{
lean_object* v_a_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1029_; 
v_a_1019_ = lean_ctor_get(v___x_1018_, 0);
v_isSharedCheck_1029_ = !lean_is_exclusive(v___x_1018_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1021_ = v___x_1018_;
v_isShared_1022_ = v_isSharedCheck_1029_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_a_1019_);
lean_dec(v___x_1018_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1029_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v_prf_1025_; lean_object* v___x_1027_; 
v___x_1023_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__4___closed__0));
v___x_1024_ = l_Lean_mkConst(v___x_1023_, v___x_1013_);
v_prf_1025_ = l_Lean_mkApp7(v___x_1024_, v_00_u03c3s_1002_, v_hyps_1003_, v_restHyps_1009_, v_focusHyp_1008_, v_target_1004_, v_proof_1010_, v_a_1019_);
if (v_isShared_1022_ == 0)
{
lean_ctor_set(v___x_1021_, 0, v_prf_1025_);
v___x_1027_ = v___x_1021_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v_prf_1025_);
v___x_1027_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
return v___x_1027_;
}
}
}
else
{
lean_dec_ref(v___x_1013_);
lean_dec_ref(v_proof_1010_);
lean_dec_ref(v_restHyps_1009_);
lean_dec_ref(v_focusHyp_1008_);
lean_dec_ref(v_target_1004_);
lean_dec_ref(v_hyps_1003_);
lean_dec_ref(v_00_u03c3s_1002_);
return v___x_1018_;
}
}
}
}
else
{
lean_object* v_a_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1039_; 
lean_dec(v___y_997_);
lean_dec_ref(v___y_996_);
lean_dec(v___y_995_);
lean_dec_ref(v___y_994_);
lean_dec(v___y_993_);
lean_dec_ref(v___y_992_);
lean_dec(v___y_991_);
lean_dec_ref(v___y_990_);
lean_dec_ref(v_k_989_);
lean_dec_ref(v_goal_987_);
v_a_1032_ = lean_ctor_get(v___x_999_, 0);
v_isSharedCheck_1039_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1034_ = v___x_999_;
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_a_1032_);
lean_dec(v___x_999_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevert___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__4___boxed(lean_object* v_goal_1040_, lean_object* v_ref_1041_, lean_object* v_k_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_){
_start:
{
lean_object* v_res_1052_; 
v_res_1052_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevert___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__4(v_goal_1040_, v_ref_1041_, v_k_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_);
return v_res_1052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__0(lean_object* v_val_1053_, lean_object* v_newGoal_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_){
_start:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; 
v___x_1064_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v_newGoal_1054_);
v___x_1065_ = lean_box(0);
v___x_1066_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_1064_, v___x_1065_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_);
if (lean_obj_tag(v___x_1066_) == 0)
{
lean_object* v_a_1067_; lean_object* v___x_1069_; uint8_t v_isShared_1070_; uint8_t v_isSharedCheck_1078_; 
v_a_1067_ = lean_ctor_get(v___x_1066_, 0);
v_isSharedCheck_1078_ = !lean_is_exclusive(v___x_1066_);
if (v_isSharedCheck_1078_ == 0)
{
v___x_1069_ = v___x_1066_;
v_isShared_1070_ = v_isSharedCheck_1078_;
goto v_resetjp_1068_;
}
else
{
lean_inc(v_a_1067_);
lean_dec(v___x_1066_);
v___x_1069_ = lean_box(0);
v_isShared_1070_ = v_isSharedCheck_1078_;
goto v_resetjp_1068_;
}
v_resetjp_1068_:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1076_; 
v___x_1071_ = lean_st_ref_take(v_val_1053_);
v___x_1072_ = l_Lean_Expr_mvarId_x21(v_a_1067_);
v___x_1073_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1072_);
lean_ctor_set(v___x_1073_, 1, v___x_1071_);
v___x_1074_ = lean_st_ref_set(v_val_1053_, v___x_1073_);
if (v_isShared_1070_ == 0)
{
v___x_1076_ = v___x_1069_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v_a_1067_);
v___x_1076_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
return v___x_1076_;
}
}
}
else
{
return v___x_1066_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__0___boxed(lean_object* v_val_1079_, lean_object* v_newGoal_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_){
_start:
{
lean_object* v_res_1090_; 
v_res_1090_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__0(v_val_1079_, v_newGoal_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_);
lean_dec(v___y_1088_);
lean_dec_ref(v___y_1087_);
lean_dec(v___y_1086_);
lean_dec(v___y_1084_);
lean_dec_ref(v___y_1083_);
lean_dec(v___y_1082_);
lean_dec_ref(v___y_1081_);
lean_dec(v_val_1079_);
return v_res_1090_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15_spec__20_spec__22___redArg(lean_object* v_x_1091_, lean_object* v_x_1092_, lean_object* v_x_1093_, lean_object* v_x_1094_){
_start:
{
lean_object* v_ks_1095_; lean_object* v_vs_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1120_; 
v_ks_1095_ = lean_ctor_get(v_x_1091_, 0);
v_vs_1096_ = lean_ctor_get(v_x_1091_, 1);
v_isSharedCheck_1120_ = !lean_is_exclusive(v_x_1091_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1098_ = v_x_1091_;
v_isShared_1099_ = v_isSharedCheck_1120_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_vs_1096_);
lean_inc(v_ks_1095_);
lean_dec(v_x_1091_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1120_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v___x_1100_; uint8_t v___x_1101_; 
v___x_1100_ = lean_array_get_size(v_ks_1095_);
v___x_1101_ = lean_nat_dec_lt(v_x_1092_, v___x_1100_);
if (v___x_1101_ == 0)
{
lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1105_; 
lean_dec(v_x_1092_);
v___x_1102_ = lean_array_push(v_ks_1095_, v_x_1093_);
v___x_1103_ = lean_array_push(v_vs_1096_, v_x_1094_);
if (v_isShared_1099_ == 0)
{
lean_ctor_set(v___x_1098_, 1, v___x_1103_);
lean_ctor_set(v___x_1098_, 0, v___x_1102_);
v___x_1105_ = v___x_1098_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v___x_1102_);
lean_ctor_set(v_reuseFailAlloc_1106_, 1, v___x_1103_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
}
}
else
{
lean_object* v_k_x27_1107_; uint8_t v___x_1108_; 
v_k_x27_1107_ = lean_array_fget_borrowed(v_ks_1095_, v_x_1092_);
v___x_1108_ = l_Lean_instBEqMVarId_beq(v_x_1093_, v_k_x27_1107_);
if (v___x_1108_ == 0)
{
lean_object* v___x_1110_; 
if (v_isShared_1099_ == 0)
{
v___x_1110_ = v___x_1098_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v_ks_1095_);
lean_ctor_set(v_reuseFailAlloc_1114_, 1, v_vs_1096_);
v___x_1110_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1111_ = lean_unsigned_to_nat(1u);
v___x_1112_ = lean_nat_add(v_x_1092_, v___x_1111_);
lean_dec(v_x_1092_);
v_x_1091_ = v___x_1110_;
v_x_1092_ = v___x_1112_;
goto _start;
}
}
else
{
lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1118_; 
v___x_1115_ = lean_array_fset(v_ks_1095_, v_x_1092_, v_x_1093_);
v___x_1116_ = lean_array_fset(v_vs_1096_, v_x_1092_, v_x_1094_);
lean_dec(v_x_1092_);
if (v_isShared_1099_ == 0)
{
lean_ctor_set(v___x_1098_, 1, v___x_1116_);
lean_ctor_set(v___x_1098_, 0, v___x_1115_);
v___x_1118_ = v___x_1098_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v___x_1115_);
lean_ctor_set(v_reuseFailAlloc_1119_, 1, v___x_1116_);
v___x_1118_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
return v___x_1118_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15_spec__20___redArg(lean_object* v_n_1121_, lean_object* v_k_1122_, lean_object* v_v_1123_){
_start:
{
lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1124_ = lean_unsigned_to_nat(0u);
v___x_1125_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15_spec__20_spec__22___redArg(v_n_1121_, v___x_1124_, v_k_1122_, v_v_1123_);
return v___x_1125_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15___redArg___closed__0(void){
_start:
{
size_t v___x_1126_; size_t v___x_1127_; size_t v___x_1128_; 
v___x_1126_ = ((size_t)5ULL);
v___x_1127_ = ((size_t)1ULL);
v___x_1128_ = lean_usize_shift_left(v___x_1127_, v___x_1126_);
return v___x_1128_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15___redArg___closed__1(void){
_start:
{
size_t v___x_1129_; size_t v___x_1130_; size_t v___x_1131_; 
v___x_1129_ = ((size_t)1ULL);
v___x_1130_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15___redArg___closed__0);
v___x_1131_ = lean_usize_sub(v___x_1130_, v___x_1129_);
return v___x_1131_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15___redArg___closed__2(void){
_start:
{
lean_object* v___x_1132_; 
v___x_1132_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1132_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15___redArg(lean_object* v_x_1133_, size_t v_x_1134_, size_t v_x_1135_, lean_object* v_x_1136_, lean_object* v_x_1137_){
_start:
{
if (lean_obj_tag(v_x_1133_) == 0)
{
lean_object* v_es_1138_; size_t v___x_1139_; size_t v___x_1140_; size_t v___x_1141_; size_t v___x_1142_; lean_object* v_j_1143_; lean_object* v___x_1144_; uint8_t v___x_1145_; 
v_es_1138_ = lean_ctor_get(v_x_1133_, 0);
v___x_1139_ = ((size_t)5ULL);
v___x_1140_ = ((size_t)1ULL);
v___x_1141_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15___redArg___closed__1);
v___x_1142_ = lean_usize_land(v_x_1134_, v___x_1141_);
v_j_1143_ = lean_usize_to_nat(v___x_1142_);
v___x_1144_ = lean_array_get_size(v_es_1138_);
v___x_1145_ = lean_nat_dec_lt(v_j_1143_, v___x_1144_);
if (v___x_1145_ == 0)
{
lean_dec(v_j_1143_);
lean_dec(v_x_1137_);
lean_dec(v_x_1136_);
return v_x_1133_;
}
else
{
lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1182_; 
lean_inc_ref(v_es_1138_);
v_isSharedCheck_1182_ = !lean_is_exclusive(v_x_1133_);
if (v_isSharedCheck_1182_ == 0)
{
lean_object* v_unused_1183_; 
v_unused_1183_ = lean_ctor_get(v_x_1133_, 0);
lean_dec(v_unused_1183_);
v___x_1147_ = v_x_1133_;
v_isShared_1148_ = v_isSharedCheck_1182_;
goto v_resetjp_1146_;
}
else
{
lean_dec(v_x_1133_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1182_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v_v_1149_; lean_object* v___x_1150_; lean_object* v_xs_x27_1151_; lean_object* v___y_1153_; 
v_v_1149_ = lean_array_fget(v_es_1138_, v_j_1143_);
v___x_1150_ = lean_box(0);
v_xs_x27_1151_ = lean_array_fset(v_es_1138_, v_j_1143_, v___x_1150_);
switch(lean_obj_tag(v_v_1149_))
{
case 0:
{
lean_object* v_key_1158_; lean_object* v_val_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1169_; 
v_key_1158_ = lean_ctor_get(v_v_1149_, 0);
v_val_1159_ = lean_ctor_get(v_v_1149_, 1);
v_isSharedCheck_1169_ = !lean_is_exclusive(v_v_1149_);
if (v_isSharedCheck_1169_ == 0)
{
v___x_1161_ = v_v_1149_;
v_isShared_1162_ = v_isSharedCheck_1169_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_val_1159_);
lean_inc(v_key_1158_);
lean_dec(v_v_1149_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1169_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
uint8_t v___x_1163_; 
v___x_1163_ = l_Lean_instBEqMVarId_beq(v_x_1136_, v_key_1158_);
if (v___x_1163_ == 0)
{
lean_object* v___x_1164_; lean_object* v___x_1165_; 
lean_del_object(v___x_1161_);
v___x_1164_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1158_, v_val_1159_, v_x_1136_, v_x_1137_);
v___x_1165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1165_, 0, v___x_1164_);
v___y_1153_ = v___x_1165_;
goto v___jp_1152_;
}
else
{
lean_object* v___x_1167_; 
lean_dec(v_val_1159_);
lean_dec(v_key_1158_);
if (v_isShared_1162_ == 0)
{
lean_ctor_set(v___x_1161_, 1, v_x_1137_);
lean_ctor_set(v___x_1161_, 0, v_x_1136_);
v___x_1167_ = v___x_1161_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v_x_1136_);
lean_ctor_set(v_reuseFailAlloc_1168_, 1, v_x_1137_);
v___x_1167_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
v___y_1153_ = v___x_1167_;
goto v___jp_1152_;
}
}
}
}
case 1:
{
lean_object* v_node_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1180_; 
v_node_1170_ = lean_ctor_get(v_v_1149_, 0);
v_isSharedCheck_1180_ = !lean_is_exclusive(v_v_1149_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1172_ = v_v_1149_;
v_isShared_1173_ = v_isSharedCheck_1180_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_node_1170_);
lean_dec(v_v_1149_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1180_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
size_t v___x_1174_; size_t v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1178_; 
v___x_1174_ = lean_usize_shift_right(v_x_1134_, v___x_1139_);
v___x_1175_ = lean_usize_add(v_x_1135_, v___x_1140_);
v___x_1176_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15___redArg(v_node_1170_, v___x_1174_, v___x_1175_, v_x_1136_, v_x_1137_);
if (v_isShared_1173_ == 0)
{
lean_ctor_set(v___x_1172_, 0, v___x_1176_);
v___x_1178_ = v___x_1172_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v___x_1176_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
v___y_1153_ = v___x_1178_;
goto v___jp_1152_;
}
}
}
default: 
{
lean_object* v___x_1181_; 
v___x_1181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1181_, 0, v_x_1136_);
lean_ctor_set(v___x_1181_, 1, v_x_1137_);
v___y_1153_ = v___x_1181_;
goto v___jp_1152_;
}
}
v___jp_1152_:
{
lean_object* v___x_1154_; lean_object* v___x_1156_; 
v___x_1154_ = lean_array_fset(v_xs_x27_1151_, v_j_1143_, v___y_1153_);
lean_dec(v_j_1143_);
if (v_isShared_1148_ == 0)
{
lean_ctor_set(v___x_1147_, 0, v___x_1154_);
v___x_1156_ = v___x_1147_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v___x_1154_);
v___x_1156_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
return v___x_1156_;
}
}
}
}
}
else
{
lean_object* v_ks_1184_; lean_object* v_vs_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1205_; 
v_ks_1184_ = lean_ctor_get(v_x_1133_, 0);
v_vs_1185_ = lean_ctor_get(v_x_1133_, 1);
v_isSharedCheck_1205_ = !lean_is_exclusive(v_x_1133_);
if (v_isSharedCheck_1205_ == 0)
{
v___x_1187_ = v_x_1133_;
v_isShared_1188_ = v_isSharedCheck_1205_;
goto v_resetjp_1186_;
}
else
{
lean_inc(v_vs_1185_);
lean_inc(v_ks_1184_);
lean_dec(v_x_1133_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1205_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
lean_object* v___x_1190_; 
if (v_isShared_1188_ == 0)
{
v___x_1190_ = v___x_1187_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v_ks_1184_);
lean_ctor_set(v_reuseFailAlloc_1204_, 1, v_vs_1185_);
v___x_1190_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
lean_object* v_newNode_1191_; uint8_t v___y_1193_; size_t v___x_1199_; uint8_t v___x_1200_; 
v_newNode_1191_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15_spec__20___redArg(v___x_1190_, v_x_1136_, v_x_1137_);
v___x_1199_ = ((size_t)7ULL);
v___x_1200_ = lean_usize_dec_le(v___x_1199_, v_x_1135_);
if (v___x_1200_ == 0)
{
lean_object* v___x_1201_; lean_object* v___x_1202_; uint8_t v___x_1203_; 
v___x_1201_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1191_);
v___x_1202_ = lean_unsigned_to_nat(4u);
v___x_1203_ = lean_nat_dec_lt(v___x_1201_, v___x_1202_);
lean_dec(v___x_1201_);
v___y_1193_ = v___x_1203_;
goto v___jp_1192_;
}
else
{
v___y_1193_ = v___x_1200_;
goto v___jp_1192_;
}
v___jp_1192_:
{
if (v___y_1193_ == 0)
{
lean_object* v_ks_1194_; lean_object* v_vs_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; 
v_ks_1194_ = lean_ctor_get(v_newNode_1191_, 0);
lean_inc_ref(v_ks_1194_);
v_vs_1195_ = lean_ctor_get(v_newNode_1191_, 1);
lean_inc_ref(v_vs_1195_);
lean_dec_ref(v_newNode_1191_);
v___x_1196_ = lean_unsigned_to_nat(0u);
v___x_1197_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15___redArg___closed__2);
v___x_1198_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15_spec__21___redArg(v_x_1135_, v_ks_1194_, v_vs_1195_, v___x_1196_, v___x_1197_);
lean_dec_ref(v_vs_1195_);
lean_dec_ref(v_ks_1194_);
return v___x_1198_;
}
else
{
return v_newNode_1191_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15_spec__21___redArg(size_t v_depth_1206_, lean_object* v_keys_1207_, lean_object* v_vals_1208_, lean_object* v_i_1209_, lean_object* v_entries_1210_){
_start:
{
lean_object* v___x_1211_; uint8_t v___x_1212_; 
v___x_1211_ = lean_array_get_size(v_keys_1207_);
v___x_1212_ = lean_nat_dec_lt(v_i_1209_, v___x_1211_);
if (v___x_1212_ == 0)
{
lean_dec(v_i_1209_);
return v_entries_1210_;
}
else
{
lean_object* v_k_1213_; lean_object* v_v_1214_; uint64_t v___x_1215_; size_t v_h_1216_; size_t v___x_1217_; lean_object* v___x_1218_; size_t v___x_1219_; size_t v___x_1220_; size_t v___x_1221_; size_t v_h_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; 
v_k_1213_ = lean_array_fget_borrowed(v_keys_1207_, v_i_1209_);
v_v_1214_ = lean_array_fget_borrowed(v_vals_1208_, v_i_1209_);
v___x_1215_ = l_Lean_instHashableMVarId_hash(v_k_1213_);
v_h_1216_ = lean_uint64_to_usize(v___x_1215_);
v___x_1217_ = ((size_t)5ULL);
v___x_1218_ = lean_unsigned_to_nat(1u);
v___x_1219_ = ((size_t)1ULL);
v___x_1220_ = lean_usize_sub(v_depth_1206_, v___x_1219_);
v___x_1221_ = lean_usize_mul(v___x_1217_, v___x_1220_);
v_h_1222_ = lean_usize_shift_right(v_h_1216_, v___x_1221_);
v___x_1223_ = lean_nat_add(v_i_1209_, v___x_1218_);
lean_dec(v_i_1209_);
lean_inc(v_v_1214_);
lean_inc(v_k_1213_);
v___x_1224_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15___redArg(v_entries_1210_, v_h_1222_, v_depth_1206_, v_k_1213_, v_v_1214_);
v_i_1209_ = v___x_1223_;
v_entries_1210_ = v___x_1224_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15_spec__21___redArg___boxed(lean_object* v_depth_1226_, lean_object* v_keys_1227_, lean_object* v_vals_1228_, lean_object* v_i_1229_, lean_object* v_entries_1230_){
_start:
{
size_t v_depth_boxed_1231_; lean_object* v_res_1232_; 
v_depth_boxed_1231_ = lean_unbox_usize(v_depth_1226_);
lean_dec(v_depth_1226_);
v_res_1232_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15_spec__21___redArg(v_depth_boxed_1231_, v_keys_1227_, v_vals_1228_, v_i_1229_, v_entries_1230_);
lean_dec_ref(v_vals_1228_);
lean_dec_ref(v_keys_1227_);
return v_res_1232_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15___redArg___boxed(lean_object* v_x_1233_, lean_object* v_x_1234_, lean_object* v_x_1235_, lean_object* v_x_1236_, lean_object* v_x_1237_){
_start:
{
size_t v_x_20505__boxed_1238_; size_t v_x_20506__boxed_1239_; lean_object* v_res_1240_; 
v_x_20505__boxed_1238_ = lean_unbox_usize(v_x_1234_);
lean_dec(v_x_1234_);
v_x_20506__boxed_1239_ = lean_unbox_usize(v_x_1235_);
lean_dec(v_x_1235_);
v_res_1240_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15___redArg(v_x_1233_, v_x_20505__boxed_1238_, v_x_20506__boxed_1239_, v_x_1236_, v_x_1237_);
return v_res_1240_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10___redArg(lean_object* v_x_1241_, lean_object* v_x_1242_, lean_object* v_x_1243_){
_start:
{
uint64_t v___x_1244_; size_t v___x_1245_; size_t v___x_1246_; lean_object* v___x_1247_; 
v___x_1244_ = l_Lean_instHashableMVarId_hash(v_x_1242_);
v___x_1245_ = lean_uint64_to_usize(v___x_1244_);
v___x_1246_ = ((size_t)1ULL);
v___x_1247_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15___redArg(v_x_1241_, v___x_1245_, v___x_1246_, v_x_1242_, v_x_1243_);
return v___x_1247_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2___redArg(lean_object* v_mvarId_1248_, lean_object* v_val_1249_, lean_object* v___y_1250_){
_start:
{
lean_object* v___x_1252_; lean_object* v_mctx_1253_; lean_object* v_cache_1254_; lean_object* v_zetaDeltaFVarIds_1255_; lean_object* v_postponed_1256_; lean_object* v_diag_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1284_; 
v___x_1252_ = lean_st_ref_take(v___y_1250_);
v_mctx_1253_ = lean_ctor_get(v___x_1252_, 0);
v_cache_1254_ = lean_ctor_get(v___x_1252_, 1);
v_zetaDeltaFVarIds_1255_ = lean_ctor_get(v___x_1252_, 2);
v_postponed_1256_ = lean_ctor_get(v___x_1252_, 3);
v_diag_1257_ = lean_ctor_get(v___x_1252_, 4);
v_isSharedCheck_1284_ = !lean_is_exclusive(v___x_1252_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1259_ = v___x_1252_;
v_isShared_1260_ = v_isSharedCheck_1284_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_diag_1257_);
lean_inc(v_postponed_1256_);
lean_inc(v_zetaDeltaFVarIds_1255_);
lean_inc(v_cache_1254_);
lean_inc(v_mctx_1253_);
lean_dec(v___x_1252_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1284_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v_depth_1261_; lean_object* v_levelAssignDepth_1262_; lean_object* v_mvarCounter_1263_; lean_object* v_lDepth_1264_; lean_object* v_decls_1265_; lean_object* v_userNames_1266_; lean_object* v_lAssignment_1267_; lean_object* v_eAssignment_1268_; lean_object* v_dAssignment_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1283_; 
v_depth_1261_ = lean_ctor_get(v_mctx_1253_, 0);
v_levelAssignDepth_1262_ = lean_ctor_get(v_mctx_1253_, 1);
v_mvarCounter_1263_ = lean_ctor_get(v_mctx_1253_, 2);
v_lDepth_1264_ = lean_ctor_get(v_mctx_1253_, 3);
v_decls_1265_ = lean_ctor_get(v_mctx_1253_, 4);
v_userNames_1266_ = lean_ctor_get(v_mctx_1253_, 5);
v_lAssignment_1267_ = lean_ctor_get(v_mctx_1253_, 6);
v_eAssignment_1268_ = lean_ctor_get(v_mctx_1253_, 7);
v_dAssignment_1269_ = lean_ctor_get(v_mctx_1253_, 8);
v_isSharedCheck_1283_ = !lean_is_exclusive(v_mctx_1253_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1271_ = v_mctx_1253_;
v_isShared_1272_ = v_isSharedCheck_1283_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_dAssignment_1269_);
lean_inc(v_eAssignment_1268_);
lean_inc(v_lAssignment_1267_);
lean_inc(v_userNames_1266_);
lean_inc(v_decls_1265_);
lean_inc(v_lDepth_1264_);
lean_inc(v_mvarCounter_1263_);
lean_inc(v_levelAssignDepth_1262_);
lean_inc(v_depth_1261_);
lean_dec(v_mctx_1253_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1283_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
lean_object* v___x_1273_; lean_object* v___x_1275_; 
v___x_1273_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10___redArg(v_eAssignment_1268_, v_mvarId_1248_, v_val_1249_);
if (v_isShared_1272_ == 0)
{
lean_ctor_set(v___x_1271_, 7, v___x_1273_);
v___x_1275_ = v___x_1271_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v_depth_1261_);
lean_ctor_set(v_reuseFailAlloc_1282_, 1, v_levelAssignDepth_1262_);
lean_ctor_set(v_reuseFailAlloc_1282_, 2, v_mvarCounter_1263_);
lean_ctor_set(v_reuseFailAlloc_1282_, 3, v_lDepth_1264_);
lean_ctor_set(v_reuseFailAlloc_1282_, 4, v_decls_1265_);
lean_ctor_set(v_reuseFailAlloc_1282_, 5, v_userNames_1266_);
lean_ctor_set(v_reuseFailAlloc_1282_, 6, v_lAssignment_1267_);
lean_ctor_set(v_reuseFailAlloc_1282_, 7, v___x_1273_);
lean_ctor_set(v_reuseFailAlloc_1282_, 8, v_dAssignment_1269_);
v___x_1275_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
lean_object* v___x_1277_; 
if (v_isShared_1260_ == 0)
{
lean_ctor_set(v___x_1259_, 0, v___x_1275_);
v___x_1277_ = v___x_1259_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v___x_1275_);
lean_ctor_set(v_reuseFailAlloc_1281_, 1, v_cache_1254_);
lean_ctor_set(v_reuseFailAlloc_1281_, 2, v_zetaDeltaFVarIds_1255_);
lean_ctor_set(v_reuseFailAlloc_1281_, 3, v_postponed_1256_);
lean_ctor_set(v_reuseFailAlloc_1281_, 4, v_diag_1257_);
v___x_1277_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; 
v___x_1278_ = lean_st_ref_set(v___y_1250_, v___x_1277_);
v___x_1279_ = lean_box(0);
v___x_1280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1280_, 0, v___x_1279_);
return v___x_1280_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2___redArg___boxed(lean_object* v_mvarId_1285_, lean_object* v_val_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_){
_start:
{
lean_object* v_res_1289_; 
v_res_1289_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2___redArg(v_mvarId_1285_, v_val_1286_, v___y_1287_);
lean_dec(v___y_1287_);
return v_res_1289_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__4___redArg(lean_object* v_as_1290_, lean_object* v_i_1291_, lean_object* v_j_1292_, lean_object* v_bs_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_){
_start:
{
lean_object* v_zero_1297_; uint8_t v_isZero_1298_; 
v_zero_1297_ = lean_unsigned_to_nat(0u);
v_isZero_1298_ = lean_nat_dec_eq(v_i_1291_, v_zero_1297_);
if (v_isZero_1298_ == 1)
{
lean_object* v___x_1299_; 
lean_dec(v___y_1295_);
lean_dec_ref(v___y_1294_);
lean_dec(v_j_1292_);
lean_dec(v_i_1291_);
v___x_1299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1299_, 0, v_bs_1293_);
return v___x_1299_;
}
else
{
lean_object* v___x_1300_; lean_object* v___x_1301_; 
v___x_1300_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__6___closed__1));
lean_inc(v___y_1295_);
lean_inc_ref(v___y_1294_);
v___x_1301_ = l_Lean_Core_mkFreshUserName(v___x_1300_, v___y_1294_, v___y_1295_);
if (lean_obj_tag(v___x_1301_) == 0)
{
lean_object* v_a_1302_; lean_object* v_one_1303_; lean_object* v_n_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; 
v_a_1302_ = lean_ctor_get(v___x_1301_, 0);
lean_inc(v_a_1302_);
lean_dec_ref(v___x_1301_);
v_one_1303_ = lean_unsigned_to_nat(1u);
v_n_1304_ = lean_nat_sub(v_i_1291_, v_one_1303_);
lean_dec(v_i_1291_);
v___x_1305_ = lean_array_fget_borrowed(v_as_1290_, v_j_1292_);
v___x_1306_ = lean_nat_add(v_j_1292_, v_one_1303_);
lean_dec(v_j_1292_);
lean_inc(v___x_1306_);
v___x_1307_ = lean_name_append_index_after(v_a_1302_, v___x_1306_);
lean_inc(v___x_1305_);
v___x_1308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1308_, 0, v___x_1307_);
lean_ctor_set(v___x_1308_, 1, v___x_1305_);
v___x_1309_ = lean_array_push(v_bs_1293_, v___x_1308_);
v_i_1291_ = v_n_1304_;
v_j_1292_ = v___x_1306_;
v_bs_1293_ = v___x_1309_;
goto _start;
}
else
{
lean_object* v_a_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1318_; 
lean_dec(v___y_1295_);
lean_dec_ref(v___y_1294_);
lean_dec_ref(v_bs_1293_);
lean_dec(v_j_1292_);
lean_dec(v_i_1291_);
v_a_1311_ = lean_ctor_get(v___x_1301_, 0);
v_isSharedCheck_1318_ = !lean_is_exclusive(v___x_1301_);
if (v_isSharedCheck_1318_ == 0)
{
v___x_1313_ = v___x_1301_;
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_a_1311_);
lean_dec(v___x_1301_);
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
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__4___redArg___boxed(lean_object* v_as_1319_, lean_object* v_i_1320_, lean_object* v_j_1321_, lean_object* v_bs_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_){
_start:
{
lean_object* v_res_1326_; 
v_res_1326_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__4___redArg(v_as_1319_, v_i_1320_, v_j_1321_, v_bs_1322_, v___y_1323_, v___y_1324_);
lean_dec_ref(v_as_1319_);
return v_res_1326_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5_spec__14(lean_object* v_msgData_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_){
_start:
{
lean_object* v___x_1333_; lean_object* v_env_1334_; lean_object* v___x_1335_; lean_object* v_mctx_1336_; lean_object* v_lctx_1337_; lean_object* v_options_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; 
v___x_1333_ = lean_st_ref_get(v___y_1331_);
v_env_1334_ = lean_ctor_get(v___x_1333_, 0);
lean_inc_ref(v_env_1334_);
lean_dec(v___x_1333_);
v___x_1335_ = lean_st_ref_get(v___y_1329_);
v_mctx_1336_ = lean_ctor_get(v___x_1335_, 0);
lean_inc_ref(v_mctx_1336_);
lean_dec(v___x_1335_);
v_lctx_1337_ = lean_ctor_get(v___y_1328_, 2);
v_options_1338_ = lean_ctor_get(v___y_1330_, 2);
lean_inc_ref(v_options_1338_);
lean_inc_ref(v_lctx_1337_);
v___x_1339_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1339_, 0, v_env_1334_);
lean_ctor_set(v___x_1339_, 1, v_mctx_1336_);
lean_ctor_set(v___x_1339_, 2, v_lctx_1337_);
lean_ctor_set(v___x_1339_, 3, v_options_1338_);
v___x_1340_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1340_, 0, v___x_1339_);
lean_ctor_set(v___x_1340_, 1, v_msgData_1327_);
v___x_1341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1341_, 0, v___x_1340_);
return v___x_1341_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5_spec__14___boxed(lean_object* v_msgData_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_){
_start:
{
lean_object* v_res_1348_; 
v_res_1348_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5_spec__14(v_msgData_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_);
lean_dec(v___y_1346_);
lean_dec_ref(v___y_1345_);
lean_dec(v___y_1344_);
lean_dec_ref(v___y_1343_);
return v_res_1348_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__8___redArg(lean_object* v_msg_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_){
_start:
{
lean_object* v_ref_1355_; lean_object* v___x_1356_; lean_object* v_a_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1365_; 
v_ref_1355_ = lean_ctor_get(v___y_1352_, 5);
v___x_1356_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5_spec__14(v_msg_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_);
v_a_1357_ = lean_ctor_get(v___x_1356_, 0);
v_isSharedCheck_1365_ = !lean_is_exclusive(v___x_1356_);
if (v_isSharedCheck_1365_ == 0)
{
v___x_1359_ = v___x_1356_;
v_isShared_1360_ = v_isSharedCheck_1365_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_a_1357_);
lean_dec(v___x_1356_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1365_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1361_; lean_object* v___x_1363_; 
lean_inc(v_ref_1355_);
v___x_1361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1361_, 0, v_ref_1355_);
lean_ctor_set(v___x_1361_, 1, v_a_1357_);
if (v_isShared_1360_ == 0)
{
lean_ctor_set_tag(v___x_1359_, 1);
lean_ctor_set(v___x_1359_, 0, v___x_1361_);
v___x_1363_ = v___x_1359_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v___x_1361_);
v___x_1363_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
return v___x_1363_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__8___redArg___boxed(lean_object* v_msg_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_){
_start:
{
lean_object* v_res_1372_; 
v_res_1372_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__8___redArg(v_msg_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_);
lean_dec(v___y_1370_);
lean_dec_ref(v___y_1369_);
lean_dec(v___y_1368_);
lean_dec_ref(v___y_1367_);
return v_res_1372_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__7(lean_object* v_u_1373_, lean_object* v_as_1374_, size_t v_i_1375_, size_t v_stop_1376_, lean_object* v_b_1377_){
_start:
{
uint8_t v___x_1378_; 
v___x_1378_ = lean_usize_dec_eq(v_i_1375_, v_stop_1376_);
if (v___x_1378_ == 0)
{
size_t v___x_1379_; size_t v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; 
v___x_1379_ = ((size_t)1ULL);
v___x_1380_ = lean_usize_sub(v_i_1375_, v___x_1379_);
v___x_1381_ = lean_array_uget_borrowed(v_as_1374_, v___x_1380_);
lean_inc(v___x_1381_);
lean_inc(v_u_1373_);
v___x_1382_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkCons(v_u_1373_, v___x_1381_, v_b_1377_);
v_i_1375_ = v___x_1380_;
v_b_1377_ = v___x_1382_;
goto _start;
}
else
{
lean_dec(v_u_1373_);
return v_b_1377_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__7___boxed(lean_object* v_u_1384_, lean_object* v_as_1385_, lean_object* v_i_1386_, lean_object* v_stop_1387_, lean_object* v_b_1388_){
_start:
{
size_t v_i_boxed_1389_; size_t v_stop_boxed_1390_; lean_object* v_res_1391_; 
v_i_boxed_1389_ = lean_unbox_usize(v_i_1386_);
lean_dec(v_i_1386_);
v_stop_boxed_1390_ = lean_unbox_usize(v_stop_1387_);
lean_dec(v_stop_1387_);
v_res_1391_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__7(v_u_1384_, v_as_1385_, v_i_boxed_1389_, v_stop_boxed_1390_, v_b_1388_);
lean_dec_ref(v_as_1385_);
return v_res_1391_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__6(size_t v_sz_1392_, size_t v_i_1393_, lean_object* v_bs_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_){
_start:
{
uint8_t v___x_1400_; 
v___x_1400_ = lean_usize_dec_lt(v_i_1393_, v_sz_1392_);
if (v___x_1400_ == 0)
{
lean_object* v___x_1401_; 
lean_dec(v___y_1398_);
lean_dec_ref(v___y_1397_);
lean_dec(v___y_1396_);
lean_dec_ref(v___y_1395_);
v___x_1401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1401_, 0, v_bs_1394_);
return v___x_1401_;
}
else
{
lean_object* v_v_1402_; lean_object* v___x_1403_; 
v_v_1402_ = lean_array_uget_borrowed(v_bs_1394_, v_i_1393_);
lean_inc(v___y_1398_);
lean_inc_ref(v___y_1397_);
lean_inc(v___y_1396_);
lean_inc_ref(v___y_1395_);
lean_inc(v_v_1402_);
v___x_1403_ = l_Lean_Meta_mkEqRefl(v_v_1402_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_);
if (lean_obj_tag(v___x_1403_) == 0)
{
lean_object* v_a_1404_; lean_object* v___x_1405_; lean_object* v_bs_x27_1406_; size_t v___x_1407_; size_t v___x_1408_; lean_object* v___x_1409_; 
v_a_1404_ = lean_ctor_get(v___x_1403_, 0);
lean_inc(v_a_1404_);
lean_dec_ref(v___x_1403_);
v___x_1405_ = lean_unsigned_to_nat(0u);
v_bs_x27_1406_ = lean_array_uset(v_bs_1394_, v_i_1393_, v___x_1405_);
v___x_1407_ = ((size_t)1ULL);
v___x_1408_ = lean_usize_add(v_i_1393_, v___x_1407_);
v___x_1409_ = lean_array_uset(v_bs_x27_1406_, v_i_1393_, v_a_1404_);
v_i_1393_ = v___x_1408_;
v_bs_1394_ = v___x_1409_;
goto _start;
}
else
{
lean_object* v_a_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1418_; 
lean_dec(v___y_1398_);
lean_dec_ref(v___y_1397_);
lean_dec(v___y_1396_);
lean_dec_ref(v___y_1395_);
lean_dec_ref(v_bs_1394_);
v_a_1411_ = lean_ctor_get(v___x_1403_, 0);
v_isSharedCheck_1418_ = !lean_is_exclusive(v___x_1403_);
if (v_isSharedCheck_1418_ == 0)
{
v___x_1413_ = v___x_1403_;
v_isShared_1414_ = v_isSharedCheck_1418_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_a_1411_);
lean_dec(v___x_1403_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1418_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
lean_object* v___x_1416_; 
if (v_isShared_1414_ == 0)
{
v___x_1416_ = v___x_1413_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v_a_1411_);
v___x_1416_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
return v___x_1416_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__6___boxed(lean_object* v_sz_1419_, lean_object* v_i_1420_, lean_object* v_bs_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_){
_start:
{
size_t v_sz_boxed_1427_; size_t v_i_boxed_1428_; lean_object* v_res_1429_; 
v_sz_boxed_1427_ = lean_unbox_usize(v_sz_1419_);
lean_dec(v_sz_1419_);
v_i_boxed_1428_ = lean_unbox_usize(v_i_1420_);
lean_dec(v_i_1420_);
v_res_1429_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__6(v_sz_boxed_1427_, v_i_boxed_1428_, v_bs_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_);
return v_res_1429_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__1___redArg(lean_object* v_a_1430_, lean_object* v_b_1431_){
_start:
{
lean_object* v_array_1432_; lean_object* v_start_1433_; lean_object* v_stop_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1447_; 
v_array_1432_ = lean_ctor_get(v_a_1430_, 0);
v_start_1433_ = lean_ctor_get(v_a_1430_, 1);
v_stop_1434_ = lean_ctor_get(v_a_1430_, 2);
v_isSharedCheck_1447_ = !lean_is_exclusive(v_a_1430_);
if (v_isSharedCheck_1447_ == 0)
{
v___x_1436_ = v_a_1430_;
v_isShared_1437_ = v_isSharedCheck_1447_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_stop_1434_);
lean_inc(v_start_1433_);
lean_inc(v_array_1432_);
lean_dec(v_a_1430_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1447_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
uint8_t v___x_1438_; 
v___x_1438_ = lean_nat_dec_lt(v_start_1433_, v_stop_1434_);
if (v___x_1438_ == 0)
{
lean_del_object(v___x_1436_);
lean_dec(v_stop_1434_);
lean_dec(v_start_1433_);
lean_dec_ref(v_array_1432_);
return v_b_1431_;
}
else
{
lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1442_; 
v___x_1439_ = lean_unsigned_to_nat(1u);
v___x_1440_ = lean_nat_add(v_start_1433_, v___x_1439_);
lean_inc_ref(v_array_1432_);
if (v_isShared_1437_ == 0)
{
lean_ctor_set(v___x_1436_, 1, v___x_1440_);
v___x_1442_ = v___x_1436_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v_array_1432_);
lean_ctor_set(v_reuseFailAlloc_1446_, 1, v___x_1440_);
lean_ctor_set(v_reuseFailAlloc_1446_, 2, v_stop_1434_);
v___x_1442_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
lean_object* v___x_1443_; lean_object* v___x_1444_; 
v___x_1443_ = lean_array_fget(v_array_1432_, v_start_1433_);
lean_dec(v_start_1433_);
lean_dec_ref(v_array_1432_);
v___x_1444_ = lean_array_push(v_b_1431_, v___x_1443_);
v_a_1430_ = v___x_1442_;
v_b_1431_ = v___x_1444_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__3(size_t v_sz_1448_, size_t v_i_1449_, lean_object* v_bs_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_){
_start:
{
uint8_t v___x_1456_; 
v___x_1456_ = lean_usize_dec_lt(v_i_1449_, v_sz_1448_);
if (v___x_1456_ == 0)
{
lean_object* v___x_1457_; 
lean_dec(v___y_1454_);
lean_dec_ref(v___y_1453_);
lean_dec(v___y_1452_);
lean_dec_ref(v___y_1451_);
v___x_1457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1457_, 0, v_bs_1450_);
return v___x_1457_;
}
else
{
lean_object* v_v_1458_; lean_object* v___x_1459_; 
v_v_1458_ = lean_array_uget_borrowed(v_bs_1450_, v_i_1449_);
lean_inc(v___y_1454_);
lean_inc_ref(v___y_1453_);
lean_inc(v___y_1452_);
lean_inc_ref(v___y_1451_);
lean_inc(v_v_1458_);
v___x_1459_ = lean_infer_type(v_v_1458_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_);
if (lean_obj_tag(v___x_1459_) == 0)
{
lean_object* v_a_1460_; lean_object* v___x_1461_; lean_object* v_bs_x27_1462_; size_t v___x_1463_; size_t v___x_1464_; lean_object* v___x_1465_; 
v_a_1460_ = lean_ctor_get(v___x_1459_, 0);
lean_inc(v_a_1460_);
lean_dec_ref(v___x_1459_);
v___x_1461_ = lean_unsigned_to_nat(0u);
v_bs_x27_1462_ = lean_array_uset(v_bs_1450_, v_i_1449_, v___x_1461_);
v___x_1463_ = ((size_t)1ULL);
v___x_1464_ = lean_usize_add(v_i_1449_, v___x_1463_);
v___x_1465_ = lean_array_uset(v_bs_x27_1462_, v_i_1449_, v_a_1460_);
v_i_1449_ = v___x_1464_;
v_bs_1450_ = v___x_1465_;
goto _start;
}
else
{
lean_object* v_a_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1474_; 
lean_dec(v___y_1454_);
lean_dec_ref(v___y_1453_);
lean_dec(v___y_1452_);
lean_dec_ref(v___y_1451_);
lean_dec_ref(v_bs_1450_);
v_a_1467_ = lean_ctor_get(v___x_1459_, 0);
v_isSharedCheck_1474_ = !lean_is_exclusive(v___x_1459_);
if (v_isSharedCheck_1474_ == 0)
{
v___x_1469_ = v___x_1459_;
v_isShared_1470_ = v_isSharedCheck_1474_;
goto v_resetjp_1468_;
}
else
{
lean_inc(v_a_1467_);
lean_dec(v___x_1459_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1474_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
lean_object* v___x_1472_; 
if (v_isShared_1470_ == 0)
{
v___x_1472_ = v___x_1469_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v_a_1467_);
v___x_1472_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
return v___x_1472_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__3___boxed(lean_object* v_sz_1475_, lean_object* v_i_1476_, lean_object* v_bs_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_){
_start:
{
size_t v_sz_boxed_1483_; size_t v_i_boxed_1484_; lean_object* v_res_1485_; 
v_sz_boxed_1483_ = lean_unbox_usize(v_sz_1475_);
lean_dec(v_sz_1475_);
v_i_boxed_1484_ = lean_unbox_usize(v_i_1476_);
lean_dec(v_i_1476_);
v_res_1485_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__3(v_sz_boxed_1483_, v_i_boxed_1484_, v_bs_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_);
return v_res_1485_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__13(size_t v_sz_1486_, size_t v_i_1487_, lean_object* v_bs_1488_){
_start:
{
uint8_t v___x_1489_; 
v___x_1489_ = lean_usize_dec_lt(v_i_1487_, v_sz_1486_);
if (v___x_1489_ == 0)
{
return v_bs_1488_;
}
else
{
lean_object* v_v_1490_; lean_object* v_fst_1491_; lean_object* v_snd_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1508_; 
v_v_1490_ = lean_array_uget(v_bs_1488_, v_i_1487_);
v_fst_1491_ = lean_ctor_get(v_v_1490_, 0);
v_snd_1492_ = lean_ctor_get(v_v_1490_, 1);
v_isSharedCheck_1508_ = !lean_is_exclusive(v_v_1490_);
if (v_isSharedCheck_1508_ == 0)
{
v___x_1494_ = v_v_1490_;
v_isShared_1495_ = v_isSharedCheck_1508_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_snd_1492_);
lean_inc(v_fst_1491_);
lean_dec(v_v_1490_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1508_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v___x_1496_; lean_object* v_bs_x27_1497_; uint8_t v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1501_; 
v___x_1496_ = lean_unsigned_to_nat(0u);
v_bs_x27_1497_ = lean_array_uset(v_bs_1488_, v_i_1487_, v___x_1496_);
v___x_1498_ = 0;
v___x_1499_ = lean_box(v___x_1498_);
if (v_isShared_1495_ == 0)
{
lean_ctor_set(v___x_1494_, 0, v___x_1499_);
v___x_1501_ = v___x_1494_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v___x_1499_);
lean_ctor_set(v_reuseFailAlloc_1507_, 1, v_snd_1492_);
v___x_1501_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
lean_object* v___x_1502_; size_t v___x_1503_; size_t v___x_1504_; lean_object* v___x_1505_; 
v___x_1502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1502_, 0, v_fst_1491_);
lean_ctor_set(v___x_1502_, 1, v___x_1501_);
v___x_1503_ = ((size_t)1ULL);
v___x_1504_ = lean_usize_add(v_i_1487_, v___x_1503_);
v___x_1505_ = lean_array_uset(v_bs_x27_1497_, v_i_1487_, v___x_1502_);
v_i_1487_ = v___x_1504_;
v_bs_1488_ = v___x_1505_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__13___boxed(lean_object* v_sz_1509_, lean_object* v_i_1510_, lean_object* v_bs_1511_){
_start:
{
size_t v_sz_boxed_1512_; size_t v_i_boxed_1513_; lean_object* v_res_1514_; 
v_sz_boxed_1512_ = lean_unbox_usize(v_sz_1509_);
lean_dec(v_sz_1509_);
v_i_boxed_1513_ = lean_unbox_usize(v_i_1510_);
lean_dec(v_i_1510_);
v_res_1514_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__13(v_sz_boxed_1512_, v_i_boxed_1513_, v_bs_1511_);
return v_res_1514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19_spec__21___redArg___lam__0(lean_object* v_k_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v_b_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_){
_start:
{
lean_object* v___x_1526_; 
v___x_1526_ = lean_apply_10(v_k_1515_, v_b_1520_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_, lean_box(0));
return v___x_1526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19_spec__21___redArg___lam__0___boxed(lean_object* v_k_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v_b_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_){
_start:
{
lean_object* v_res_1538_; 
v_res_1538_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19_spec__21___redArg___lam__0(v_k_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v_b_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_);
return v_res_1538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19_spec__21___redArg(lean_object* v_name_1539_, uint8_t v_bi_1540_, lean_object* v_type_1541_, lean_object* v_k_1542_, uint8_t v_kind_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_){
_start:
{
lean_object* v___f_1553_; lean_object* v___x_1554_; 
v___f_1553_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19_spec__21___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_1553_, 0, v_k_1542_);
lean_closure_set(v___f_1553_, 1, v___y_1544_);
lean_closure_set(v___f_1553_, 2, v___y_1545_);
lean_closure_set(v___f_1553_, 3, v___y_1546_);
lean_closure_set(v___f_1553_, 4, v___y_1547_);
v___x_1554_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1539_, v_bi_1540_, v_type_1541_, v___f_1553_, v_kind_1543_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_);
if (lean_obj_tag(v___x_1554_) == 0)
{
return v___x_1554_;
}
else
{
lean_object* v_a_1555_; lean_object* v___x_1557_; uint8_t v_isShared_1558_; uint8_t v_isSharedCheck_1562_; 
v_a_1555_ = lean_ctor_get(v___x_1554_, 0);
v_isSharedCheck_1562_ = !lean_is_exclusive(v___x_1554_);
if (v_isSharedCheck_1562_ == 0)
{
v___x_1557_ = v___x_1554_;
v_isShared_1558_ = v_isSharedCheck_1562_;
goto v_resetjp_1556_;
}
else
{
lean_inc(v_a_1555_);
lean_dec(v___x_1554_);
v___x_1557_ = lean_box(0);
v_isShared_1558_ = v_isSharedCheck_1562_;
goto v_resetjp_1556_;
}
v_resetjp_1556_:
{
lean_object* v___x_1560_; 
if (v_isShared_1558_ == 0)
{
v___x_1560_ = v___x_1557_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v_a_1555_);
v___x_1560_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
return v___x_1560_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19_spec__21___redArg___boxed(lean_object* v_name_1563_, lean_object* v_bi_1564_, lean_object* v_type_1565_, lean_object* v_k_1566_, lean_object* v_kind_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_){
_start:
{
uint8_t v_bi_boxed_1577_; uint8_t v_kind_boxed_1578_; lean_object* v_res_1579_; 
v_bi_boxed_1577_ = lean_unbox(v_bi_1564_);
v_kind_boxed_1578_ = lean_unbox(v_kind_1567_);
v_res_1579_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19_spec__21___redArg(v_name_1563_, v_bi_boxed_1577_, v_type_1565_, v_k_1566_, v_kind_boxed_1578_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_);
return v_res_1579_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___redArg___lam__0(lean_object* v___x_1580_, lean_object* v_a_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_){
_start:
{
lean_object* v___x_1591_; lean_object* v___x_20065__overap_1592_; lean_object* v___x_1593_; 
v___x_1591_ = l_Lean_instInhabitedExpr;
v___x_20065__overap_1592_ = l_instInhabitedOfMonad___redArg(v___x_1580_, v___x_1591_);
v___x_1593_ = lean_apply_9(v___x_20065__overap_1592_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_, lean_box(0));
return v___x_1593_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___redArg___lam__0___boxed(lean_object* v___x_1594_, lean_object* v_a_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_){
_start:
{
lean_object* v_res_1605_; 
v_res_1605_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___redArg___lam__0(v___x_1594_, v_a_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_);
lean_dec_ref(v_a_1595_);
return v_res_1605_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___redArg___lam__1___boxed(lean_object* v_acc_1610_, lean_object* v_declInfos_1611_, lean_object* v_k_1612_, lean_object* v_kind_1613_, lean_object* v_x_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_){
_start:
{
uint8_t v_kind_boxed_1624_; lean_object* v_res_1625_; 
v_kind_boxed_1624_ = lean_unbox(v_kind_1613_);
v_res_1625_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___redArg___lam__1(v_acc_1610_, v_declInfos_1611_, v_k_1612_, v_kind_boxed_1624_, v_x_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_);
return v_res_1625_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___redArg(lean_object* v_declInfos_1626_, lean_object* v_k_1627_, uint8_t v_kind_1628_, lean_object* v_acc_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_){
_start:
{
lean_object* v___x_1639_; lean_object* v_toApplicative_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1787_; 
v___x_1639_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__1);
v_toApplicative_1640_ = lean_ctor_get(v___x_1639_, 0);
v_isSharedCheck_1787_ = !lean_is_exclusive(v___x_1639_);
if (v_isSharedCheck_1787_ == 0)
{
lean_object* v_unused_1788_; 
v_unused_1788_ = lean_ctor_get(v___x_1639_, 1);
lean_dec(v_unused_1788_);
v___x_1642_ = v___x_1639_;
v_isShared_1643_ = v_isSharedCheck_1787_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_toApplicative_1640_);
lean_dec(v___x_1639_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1787_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
lean_object* v_toFunctor_1644_; lean_object* v_toSeq_1645_; lean_object* v_toSeqLeft_1646_; lean_object* v_toSeqRight_1647_; lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1785_; 
v_toFunctor_1644_ = lean_ctor_get(v_toApplicative_1640_, 0);
v_toSeq_1645_ = lean_ctor_get(v_toApplicative_1640_, 2);
v_toSeqLeft_1646_ = lean_ctor_get(v_toApplicative_1640_, 3);
v_toSeqRight_1647_ = lean_ctor_get(v_toApplicative_1640_, 4);
v_isSharedCheck_1785_ = !lean_is_exclusive(v_toApplicative_1640_);
if (v_isSharedCheck_1785_ == 0)
{
lean_object* v_unused_1786_; 
v_unused_1786_ = lean_ctor_get(v_toApplicative_1640_, 1);
lean_dec(v_unused_1786_);
v___x_1649_ = v_toApplicative_1640_;
v_isShared_1650_ = v_isSharedCheck_1785_;
goto v_resetjp_1648_;
}
else
{
lean_inc(v_toSeqRight_1647_);
lean_inc(v_toSeqLeft_1646_);
lean_inc(v_toSeq_1645_);
lean_inc(v_toFunctor_1644_);
lean_dec(v_toApplicative_1640_);
v___x_1649_ = lean_box(0);
v_isShared_1650_ = v_isSharedCheck_1785_;
goto v_resetjp_1648_;
}
v_resetjp_1648_:
{
lean_object* v___f_1651_; lean_object* v___f_1652_; lean_object* v___f_1653_; lean_object* v___f_1654_; lean_object* v___x_1655_; lean_object* v___f_1656_; lean_object* v___f_1657_; lean_object* v___f_1658_; lean_object* v___x_1660_; 
v___f_1651_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__2));
v___f_1652_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__3));
lean_inc_ref(v_toFunctor_1644_);
v___f_1653_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1653_, 0, v_toFunctor_1644_);
v___f_1654_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1654_, 0, v_toFunctor_1644_);
v___x_1655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1655_, 0, v___f_1653_);
lean_ctor_set(v___x_1655_, 1, v___f_1654_);
v___f_1656_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1656_, 0, v_toSeqRight_1647_);
v___f_1657_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1657_, 0, v_toSeqLeft_1646_);
v___f_1658_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1658_, 0, v_toSeq_1645_);
if (v_isShared_1650_ == 0)
{
lean_ctor_set(v___x_1649_, 4, v___f_1656_);
lean_ctor_set(v___x_1649_, 3, v___f_1657_);
lean_ctor_set(v___x_1649_, 2, v___f_1658_);
lean_ctor_set(v___x_1649_, 1, v___f_1651_);
lean_ctor_set(v___x_1649_, 0, v___x_1655_);
v___x_1660_ = v___x_1649_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v___x_1655_);
lean_ctor_set(v_reuseFailAlloc_1784_, 1, v___f_1651_);
lean_ctor_set(v_reuseFailAlloc_1784_, 2, v___f_1658_);
lean_ctor_set(v_reuseFailAlloc_1784_, 3, v___f_1657_);
lean_ctor_set(v_reuseFailAlloc_1784_, 4, v___f_1656_);
v___x_1660_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1659_;
}
v_reusejp_1659_:
{
lean_object* v___x_1662_; 
if (v_isShared_1643_ == 0)
{
lean_ctor_set(v___x_1642_, 1, v___f_1652_);
lean_ctor_set(v___x_1642_, 0, v___x_1660_);
v___x_1662_ = v___x_1642_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1783_; 
v_reuseFailAlloc_1783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1783_, 0, v___x_1660_);
lean_ctor_set(v_reuseFailAlloc_1783_, 1, v___f_1652_);
v___x_1662_ = v_reuseFailAlloc_1783_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
lean_object* v___x_1663_; lean_object* v_toApplicative_1664_; lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1781_; 
v___x_1663_ = l_ReaderT_instMonad___redArg(v___x_1662_);
v_toApplicative_1664_ = lean_ctor_get(v___x_1663_, 0);
v_isSharedCheck_1781_ = !lean_is_exclusive(v___x_1663_);
if (v_isSharedCheck_1781_ == 0)
{
lean_object* v_unused_1782_; 
v_unused_1782_ = lean_ctor_get(v___x_1663_, 1);
lean_dec(v_unused_1782_);
v___x_1666_ = v___x_1663_;
v_isShared_1667_ = v_isSharedCheck_1781_;
goto v_resetjp_1665_;
}
else
{
lean_inc(v_toApplicative_1664_);
lean_dec(v___x_1663_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1781_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
lean_object* v_toFunctor_1668_; lean_object* v_toSeq_1669_; lean_object* v_toSeqLeft_1670_; lean_object* v_toSeqRight_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1779_; 
v_toFunctor_1668_ = lean_ctor_get(v_toApplicative_1664_, 0);
v_toSeq_1669_ = lean_ctor_get(v_toApplicative_1664_, 2);
v_toSeqLeft_1670_ = lean_ctor_get(v_toApplicative_1664_, 3);
v_toSeqRight_1671_ = lean_ctor_get(v_toApplicative_1664_, 4);
v_isSharedCheck_1779_ = !lean_is_exclusive(v_toApplicative_1664_);
if (v_isSharedCheck_1779_ == 0)
{
lean_object* v_unused_1780_; 
v_unused_1780_ = lean_ctor_get(v_toApplicative_1664_, 1);
lean_dec(v_unused_1780_);
v___x_1673_ = v_toApplicative_1664_;
v_isShared_1674_ = v_isSharedCheck_1779_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_toSeqRight_1671_);
lean_inc(v_toSeqLeft_1670_);
lean_inc(v_toSeq_1669_);
lean_inc(v_toFunctor_1668_);
lean_dec(v_toApplicative_1664_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1779_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
lean_object* v___f_1675_; lean_object* v___f_1676_; lean_object* v___f_1677_; lean_object* v___f_1678_; lean_object* v___x_1679_; lean_object* v___f_1680_; lean_object* v___f_1681_; lean_object* v___f_1682_; lean_object* v___x_1684_; 
v___f_1675_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__4));
v___f_1676_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__5));
lean_inc_ref(v_toFunctor_1668_);
v___f_1677_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1677_, 0, v_toFunctor_1668_);
v___f_1678_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1678_, 0, v_toFunctor_1668_);
v___x_1679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1679_, 0, v___f_1677_);
lean_ctor_set(v___x_1679_, 1, v___f_1678_);
v___f_1680_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1680_, 0, v_toSeqRight_1671_);
v___f_1681_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1681_, 0, v_toSeqLeft_1670_);
v___f_1682_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1682_, 0, v_toSeq_1669_);
if (v_isShared_1674_ == 0)
{
lean_ctor_set(v___x_1673_, 4, v___f_1680_);
lean_ctor_set(v___x_1673_, 3, v___f_1681_);
lean_ctor_set(v___x_1673_, 2, v___f_1682_);
lean_ctor_set(v___x_1673_, 1, v___f_1675_);
lean_ctor_set(v___x_1673_, 0, v___x_1679_);
v___x_1684_ = v___x_1673_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v___x_1679_);
lean_ctor_set(v_reuseFailAlloc_1778_, 1, v___f_1675_);
lean_ctor_set(v_reuseFailAlloc_1778_, 2, v___f_1682_);
lean_ctor_set(v_reuseFailAlloc_1778_, 3, v___f_1681_);
lean_ctor_set(v_reuseFailAlloc_1778_, 4, v___f_1680_);
v___x_1684_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1683_;
}
v_reusejp_1683_:
{
lean_object* v___x_1686_; 
if (v_isShared_1667_ == 0)
{
lean_ctor_set(v___x_1666_, 1, v___f_1676_);
lean_ctor_set(v___x_1666_, 0, v___x_1684_);
v___x_1686_ = v___x_1666_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v___x_1684_);
lean_ctor_set(v_reuseFailAlloc_1777_, 1, v___f_1676_);
v___x_1686_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
lean_object* v___x_1687_; lean_object* v_toApplicative_1688_; lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1775_; 
v___x_1687_ = l_ReaderT_instMonad___redArg(v___x_1686_);
v_toApplicative_1688_ = lean_ctor_get(v___x_1687_, 0);
v_isSharedCheck_1775_ = !lean_is_exclusive(v___x_1687_);
if (v_isSharedCheck_1775_ == 0)
{
lean_object* v_unused_1776_; 
v_unused_1776_ = lean_ctor_get(v___x_1687_, 1);
lean_dec(v_unused_1776_);
v___x_1690_ = v___x_1687_;
v_isShared_1691_ = v_isSharedCheck_1775_;
goto v_resetjp_1689_;
}
else
{
lean_inc(v_toApplicative_1688_);
lean_dec(v___x_1687_);
v___x_1690_ = lean_box(0);
v_isShared_1691_ = v_isSharedCheck_1775_;
goto v_resetjp_1689_;
}
v_resetjp_1689_:
{
lean_object* v_toFunctor_1692_; lean_object* v_toSeq_1693_; lean_object* v_toSeqLeft_1694_; lean_object* v_toSeqRight_1695_; lean_object* v___x_1697_; uint8_t v_isShared_1698_; uint8_t v_isSharedCheck_1773_; 
v_toFunctor_1692_ = lean_ctor_get(v_toApplicative_1688_, 0);
v_toSeq_1693_ = lean_ctor_get(v_toApplicative_1688_, 2);
v_toSeqLeft_1694_ = lean_ctor_get(v_toApplicative_1688_, 3);
v_toSeqRight_1695_ = lean_ctor_get(v_toApplicative_1688_, 4);
v_isSharedCheck_1773_ = !lean_is_exclusive(v_toApplicative_1688_);
if (v_isSharedCheck_1773_ == 0)
{
lean_object* v_unused_1774_; 
v_unused_1774_ = lean_ctor_get(v_toApplicative_1688_, 1);
lean_dec(v_unused_1774_);
v___x_1697_ = v_toApplicative_1688_;
v_isShared_1698_ = v_isSharedCheck_1773_;
goto v_resetjp_1696_;
}
else
{
lean_inc(v_toSeqRight_1695_);
lean_inc(v_toSeqLeft_1694_);
lean_inc(v_toSeq_1693_);
lean_inc(v_toFunctor_1692_);
lean_dec(v_toApplicative_1688_);
v___x_1697_ = lean_box(0);
v_isShared_1698_ = v_isSharedCheck_1773_;
goto v_resetjp_1696_;
}
v_resetjp_1696_:
{
lean_object* v___f_1699_; lean_object* v___f_1700_; lean_object* v___f_1701_; lean_object* v___f_1702_; lean_object* v___x_1703_; lean_object* v___f_1704_; lean_object* v___f_1705_; lean_object* v___f_1706_; lean_object* v___x_1708_; 
v___f_1699_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___redArg___closed__0));
v___f_1700_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___redArg___closed__1));
lean_inc_ref(v_toFunctor_1692_);
v___f_1701_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1701_, 0, v_toFunctor_1692_);
v___f_1702_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1702_, 0, v_toFunctor_1692_);
v___x_1703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1703_, 0, v___f_1701_);
lean_ctor_set(v___x_1703_, 1, v___f_1702_);
v___f_1704_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1704_, 0, v_toSeqRight_1695_);
v___f_1705_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1705_, 0, v_toSeqLeft_1694_);
v___f_1706_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1706_, 0, v_toSeq_1693_);
if (v_isShared_1698_ == 0)
{
lean_ctor_set(v___x_1697_, 4, v___f_1704_);
lean_ctor_set(v___x_1697_, 3, v___f_1705_);
lean_ctor_set(v___x_1697_, 2, v___f_1706_);
lean_ctor_set(v___x_1697_, 1, v___f_1699_);
lean_ctor_set(v___x_1697_, 0, v___x_1703_);
v___x_1708_ = v___x_1697_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1772_; 
v_reuseFailAlloc_1772_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1772_, 0, v___x_1703_);
lean_ctor_set(v_reuseFailAlloc_1772_, 1, v___f_1699_);
lean_ctor_set(v_reuseFailAlloc_1772_, 2, v___f_1706_);
lean_ctor_set(v_reuseFailAlloc_1772_, 3, v___f_1705_);
lean_ctor_set(v_reuseFailAlloc_1772_, 4, v___f_1704_);
v___x_1708_ = v_reuseFailAlloc_1772_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
lean_object* v___x_1710_; 
if (v_isShared_1691_ == 0)
{
lean_ctor_set(v___x_1690_, 1, v___f_1700_);
lean_ctor_set(v___x_1690_, 0, v___x_1708_);
v___x_1710_ = v___x_1690_;
goto v_reusejp_1709_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v___x_1708_);
lean_ctor_set(v_reuseFailAlloc_1771_, 1, v___f_1700_);
v___x_1710_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1709_;
}
v_reusejp_1709_:
{
lean_object* v___x_1711_; lean_object* v_toApplicative_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1769_; 
v___x_1711_ = l_ReaderT_instMonad___redArg(v___x_1710_);
v_toApplicative_1712_ = lean_ctor_get(v___x_1711_, 0);
v_isSharedCheck_1769_ = !lean_is_exclusive(v___x_1711_);
if (v_isSharedCheck_1769_ == 0)
{
lean_object* v_unused_1770_; 
v_unused_1770_ = lean_ctor_get(v___x_1711_, 1);
lean_dec(v_unused_1770_);
v___x_1714_ = v___x_1711_;
v_isShared_1715_ = v_isSharedCheck_1769_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_toApplicative_1712_);
lean_dec(v___x_1711_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1769_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
lean_object* v_toFunctor_1716_; lean_object* v_toSeq_1717_; lean_object* v_toSeqLeft_1718_; lean_object* v_toSeqRight_1719_; lean_object* v___x_1721_; uint8_t v_isShared_1722_; uint8_t v_isSharedCheck_1767_; 
v_toFunctor_1716_ = lean_ctor_get(v_toApplicative_1712_, 0);
v_toSeq_1717_ = lean_ctor_get(v_toApplicative_1712_, 2);
v_toSeqLeft_1718_ = lean_ctor_get(v_toApplicative_1712_, 3);
v_toSeqRight_1719_ = lean_ctor_get(v_toApplicative_1712_, 4);
v_isSharedCheck_1767_ = !lean_is_exclusive(v_toApplicative_1712_);
if (v_isSharedCheck_1767_ == 0)
{
lean_object* v_unused_1768_; 
v_unused_1768_ = lean_ctor_get(v_toApplicative_1712_, 1);
lean_dec(v_unused_1768_);
v___x_1721_ = v_toApplicative_1712_;
v_isShared_1722_ = v_isSharedCheck_1767_;
goto v_resetjp_1720_;
}
else
{
lean_inc(v_toSeqRight_1719_);
lean_inc(v_toSeqLeft_1718_);
lean_inc(v_toSeq_1717_);
lean_inc(v_toFunctor_1716_);
lean_dec(v_toApplicative_1712_);
v___x_1721_ = lean_box(0);
v_isShared_1722_ = v_isSharedCheck_1767_;
goto v_resetjp_1720_;
}
v_resetjp_1720_:
{
lean_object* v___f_1723_; lean_object* v___f_1724_; lean_object* v___f_1725_; lean_object* v___f_1726_; lean_object* v___x_1727_; lean_object* v___f_1728_; lean_object* v___f_1729_; lean_object* v___f_1730_; lean_object* v___x_1732_; 
v___f_1723_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___redArg___closed__2));
v___f_1724_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___redArg___closed__3));
lean_inc_ref(v_toFunctor_1716_);
v___f_1725_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1725_, 0, v_toFunctor_1716_);
v___f_1726_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1726_, 0, v_toFunctor_1716_);
v___x_1727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1727_, 0, v___f_1725_);
lean_ctor_set(v___x_1727_, 1, v___f_1726_);
v___f_1728_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1728_, 0, v_toSeqRight_1719_);
v___f_1729_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1729_, 0, v_toSeqLeft_1718_);
v___f_1730_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1730_, 0, v_toSeq_1717_);
if (v_isShared_1722_ == 0)
{
lean_ctor_set(v___x_1721_, 4, v___f_1728_);
lean_ctor_set(v___x_1721_, 3, v___f_1729_);
lean_ctor_set(v___x_1721_, 2, v___f_1730_);
lean_ctor_set(v___x_1721_, 1, v___f_1723_);
lean_ctor_set(v___x_1721_, 0, v___x_1727_);
v___x_1732_ = v___x_1721_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1766_; 
v_reuseFailAlloc_1766_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1766_, 0, v___x_1727_);
lean_ctor_set(v_reuseFailAlloc_1766_, 1, v___f_1723_);
lean_ctor_set(v_reuseFailAlloc_1766_, 2, v___f_1730_);
lean_ctor_set(v_reuseFailAlloc_1766_, 3, v___f_1729_);
lean_ctor_set(v_reuseFailAlloc_1766_, 4, v___f_1728_);
v___x_1732_ = v_reuseFailAlloc_1766_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
lean_object* v___x_1734_; 
if (v_isShared_1715_ == 0)
{
lean_ctor_set(v___x_1714_, 1, v___f_1724_);
lean_ctor_set(v___x_1714_, 0, v___x_1732_);
v___x_1734_ = v___x_1714_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v___x_1732_);
lean_ctor_set(v_reuseFailAlloc_1765_, 1, v___f_1724_);
v___x_1734_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1733_;
}
v_reusejp_1733_:
{
lean_object* v___x_1735_; lean_object* v___x_1736_; uint8_t v___x_1737_; 
v___x_1735_ = lean_array_get_size(v_acc_1629_);
v___x_1736_ = lean_array_get_size(v_declInfos_1626_);
v___x_1737_ = lean_nat_dec_lt(v___x_1735_, v___x_1736_);
if (v___x_1737_ == 0)
{
lean_object* v___x_1738_; 
lean_dec_ref(v___x_1734_);
lean_dec_ref(v_declInfos_1626_);
v___x_1738_ = lean_apply_10(v_k_1627_, v_acc_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, lean_box(0));
return v___x_1738_;
}
else
{
lean_object* v___f_1739_; lean_object* v___x_1740_; uint8_t v___x_1741_; lean_object* v___f_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v_snd_1747_; lean_object* v_fst_1748_; lean_object* v_fst_1749_; lean_object* v_snd_1750_; lean_object* v___x_1751_; 
v___f_1739_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___redArg___lam__0___boxed), 11, 1);
lean_closure_set(v___f_1739_, 0, v___x_1734_);
v___x_1740_ = lean_box(0);
v___x_1741_ = 0;
v___f_1742_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1742_, 0, v___f_1739_);
v___x_1743_ = lean_box(v___x_1741_);
v___x_1744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1744_, 0, v___x_1743_);
lean_ctor_set(v___x_1744_, 1, v___f_1742_);
v___x_1745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1745_, 0, v___x_1740_);
lean_ctor_set(v___x_1745_, 1, v___x_1744_);
v___x_1746_ = lean_array_get_borrowed(v___x_1745_, v_declInfos_1626_, v___x_1735_);
v_snd_1747_ = lean_ctor_get(v___x_1746_, 1);
v_fst_1748_ = lean_ctor_get(v___x_1746_, 0);
lean_inc(v_fst_1748_);
v_fst_1749_ = lean_ctor_get(v_snd_1747_, 0);
lean_inc(v_fst_1749_);
v_snd_1750_ = lean_ctor_get(v_snd_1747_, 1);
lean_inc(v_snd_1750_);
lean_inc(v___y_1637_);
lean_inc_ref(v___y_1636_);
lean_inc(v___y_1635_);
lean_inc_ref(v___y_1634_);
lean_inc(v___y_1633_);
lean_inc_ref(v___y_1632_);
lean_inc(v___y_1631_);
lean_inc_ref(v___y_1630_);
lean_inc_ref(v_acc_1629_);
v___x_1751_ = lean_apply_10(v_snd_1750_, v_acc_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, lean_box(0));
if (lean_obj_tag(v___x_1751_) == 0)
{
lean_object* v_a_1752_; lean_object* v___x_1753_; lean_object* v___f_1754_; uint8_t v___x_1755_; lean_object* v___x_1756_; 
v_a_1752_ = lean_ctor_get(v___x_1751_, 0);
lean_inc(v_a_1752_);
lean_dec_ref(v___x_1751_);
v___x_1753_ = lean_box(v_kind_1628_);
v___f_1754_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___redArg___lam__1___boxed), 14, 4);
lean_closure_set(v___f_1754_, 0, v_acc_1629_);
lean_closure_set(v___f_1754_, 1, v_declInfos_1626_);
lean_closure_set(v___f_1754_, 2, v_k_1627_);
lean_closure_set(v___f_1754_, 3, v___x_1753_);
v___x_1755_ = lean_unbox(v_fst_1749_);
lean_dec(v_fst_1749_);
v___x_1756_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19_spec__21___redArg(v_fst_1748_, v___x_1755_, v_a_1752_, v___f_1754_, v_kind_1628_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_);
return v___x_1756_;
}
else
{
lean_object* v_a_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1764_; 
lean_dec(v_fst_1749_);
lean_dec(v_fst_1748_);
lean_dec(v___y_1637_);
lean_dec_ref(v___y_1636_);
lean_dec(v___y_1635_);
lean_dec_ref(v___y_1634_);
lean_dec(v___y_1633_);
lean_dec_ref(v___y_1632_);
lean_dec(v___y_1631_);
lean_dec_ref(v___y_1630_);
lean_dec_ref(v_acc_1629_);
lean_dec_ref(v_k_1627_);
lean_dec_ref(v_declInfos_1626_);
v_a_1757_ = lean_ctor_get(v___x_1751_, 0);
v_isSharedCheck_1764_ = !lean_is_exclusive(v___x_1751_);
if (v_isSharedCheck_1764_ == 0)
{
v___x_1759_ = v___x_1751_;
v_isShared_1760_ = v_isSharedCheck_1764_;
goto v_resetjp_1758_;
}
else
{
lean_inc(v_a_1757_);
lean_dec(v___x_1751_);
v___x_1759_ = lean_box(0);
v_isShared_1760_ = v_isSharedCheck_1764_;
goto v_resetjp_1758_;
}
v_resetjp_1758_:
{
lean_object* v___x_1762_; 
if (v_isShared_1760_ == 0)
{
v___x_1762_ = v___x_1759_;
goto v_reusejp_1761_;
}
else
{
lean_object* v_reuseFailAlloc_1763_; 
v_reuseFailAlloc_1763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1763_, 0, v_a_1757_);
v___x_1762_ = v_reuseFailAlloc_1763_;
goto v_reusejp_1761_;
}
v_reusejp_1761_:
{
return v___x_1762_;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___redArg___lam__1(lean_object* v_acc_1789_, lean_object* v_declInfos_1790_, lean_object* v_k_1791_, uint8_t v_kind_1792_, lean_object* v_x_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_){
_start:
{
lean_object* v___x_1803_; lean_object* v___x_1804_; 
v___x_1803_ = lean_array_push(v_acc_1789_, v_x_1793_);
v___x_1804_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___redArg(v_declInfos_1790_, v_k_1791_, v_kind_1792_, v___x_1803_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_);
return v___x_1804_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___redArg___boxed(lean_object* v_declInfos_1805_, lean_object* v_k_1806_, lean_object* v_kind_1807_, lean_object* v_acc_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_){
_start:
{
uint8_t v_kind_boxed_1818_; lean_object* v_res_1819_; 
v_kind_boxed_1818_ = lean_unbox(v_kind_1807_);
v_res_1819_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___redArg(v_declInfos_1805_, v_k_1806_, v_kind_boxed_1818_, v_acc_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_);
return v_res_1819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14___redArg(lean_object* v_inst_1820_, lean_object* v_declInfos_1821_, lean_object* v_k_1822_, uint8_t v_kind_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_){
_start:
{
lean_object* v___x_1833_; lean_object* v___x_1834_; 
v___x_1833_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__1));
v___x_1834_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___redArg(v_declInfos_1821_, v_k_1822_, v_kind_1823_, v___x_1833_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_);
return v___x_1834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14___redArg___boxed(lean_object* v_inst_1835_, lean_object* v_declInfos_1836_, lean_object* v_k_1837_, lean_object* v_kind_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_){
_start:
{
uint8_t v_kind_boxed_1848_; lean_object* v_res_1849_; 
v_kind_boxed_1848_ = lean_unbox(v_kind_1838_);
v_res_1849_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14___redArg(v_inst_1835_, v_declInfos_1836_, v_k_1837_, v_kind_boxed_1848_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_);
lean_dec(v_inst_1835_);
return v_res_1849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9___redArg(lean_object* v_inst_1850_, lean_object* v_declInfos_1851_, lean_object* v_k_1852_, uint8_t v_kind_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_){
_start:
{
size_t v_sz_1863_; size_t v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; 
v_sz_1863_ = lean_array_size(v_declInfos_1851_);
v___x_1864_ = ((size_t)0ULL);
v___x_1865_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__13(v_sz_1863_, v___x_1864_, v_declInfos_1851_);
v___x_1866_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14___redArg(v_inst_1850_, v___x_1865_, v_k_1852_, v_kind_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_);
return v___x_1866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9___redArg___boxed(lean_object* v_inst_1867_, lean_object* v_declInfos_1868_, lean_object* v_k_1869_, lean_object* v_kind_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_){
_start:
{
uint8_t v_kind_boxed_1880_; lean_object* v_res_1881_; 
v_kind_boxed_1880_ = lean_unbox(v_kind_1870_);
v_res_1881_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9___redArg(v_inst_1867_, v_declInfos_1868_, v_k_1869_, v_kind_boxed_1880_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_);
lean_dec(v_inst_1867_);
return v_res_1881_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8___lam__0(lean_object* v_snd_1882_, lean_object* v_x_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_){
_start:
{
lean_object* v___x_1893_; 
v___x_1893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1893_, 0, v_snd_1882_);
return v___x_1893_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8___lam__0___boxed(lean_object* v_snd_1894_, lean_object* v_x_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_){
_start:
{
lean_object* v_res_1905_; 
v_res_1905_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8___lam__0(v_snd_1894_, v_x_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_);
lean_dec(v___y_1903_);
lean_dec_ref(v___y_1902_);
lean_dec(v___y_1901_);
lean_dec_ref(v___y_1900_);
lean_dec(v___y_1899_);
lean_dec_ref(v___y_1898_);
lean_dec(v___y_1897_);
lean_dec_ref(v___y_1896_);
lean_dec_ref(v_x_1895_);
return v_res_1905_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8(size_t v_sz_1906_, size_t v_i_1907_, lean_object* v_bs_1908_){
_start:
{
uint8_t v___x_1909_; 
v___x_1909_ = lean_usize_dec_lt(v_i_1907_, v_sz_1906_);
if (v___x_1909_ == 0)
{
return v_bs_1908_;
}
else
{
lean_object* v_v_1910_; lean_object* v_fst_1911_; lean_object* v_snd_1912_; lean_object* v___x_1914_; uint8_t v_isShared_1915_; uint8_t v_isSharedCheck_1926_; 
v_v_1910_ = lean_array_uget(v_bs_1908_, v_i_1907_);
v_fst_1911_ = lean_ctor_get(v_v_1910_, 0);
v_snd_1912_ = lean_ctor_get(v_v_1910_, 1);
v_isSharedCheck_1926_ = !lean_is_exclusive(v_v_1910_);
if (v_isSharedCheck_1926_ == 0)
{
v___x_1914_ = v_v_1910_;
v_isShared_1915_ = v_isSharedCheck_1926_;
goto v_resetjp_1913_;
}
else
{
lean_inc(v_snd_1912_);
lean_inc(v_fst_1911_);
lean_dec(v_v_1910_);
v___x_1914_ = lean_box(0);
v_isShared_1915_ = v_isSharedCheck_1926_;
goto v_resetjp_1913_;
}
v_resetjp_1913_:
{
lean_object* v___x_1916_; lean_object* v_bs_x27_1917_; lean_object* v___f_1918_; lean_object* v___x_1920_; 
v___x_1916_ = lean_unsigned_to_nat(0u);
v_bs_x27_1917_ = lean_array_uset(v_bs_1908_, v_i_1907_, v___x_1916_);
v___f_1918_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8___lam__0___boxed), 11, 1);
lean_closure_set(v___f_1918_, 0, v_snd_1912_);
if (v_isShared_1915_ == 0)
{
lean_ctor_set(v___x_1914_, 1, v___f_1918_);
v___x_1920_ = v___x_1914_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v_fst_1911_);
lean_ctor_set(v_reuseFailAlloc_1925_, 1, v___f_1918_);
v___x_1920_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
size_t v___x_1921_; size_t v___x_1922_; lean_object* v___x_1923_; 
v___x_1921_ = ((size_t)1ULL);
v___x_1922_ = lean_usize_add(v_i_1907_, v___x_1921_);
v___x_1923_ = lean_array_uset(v_bs_x27_1917_, v_i_1907_, v___x_1920_);
v_i_1907_ = v___x_1922_;
v_bs_1908_ = v___x_1923_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8___boxed(lean_object* v_sz_1927_, lean_object* v_i_1928_, lean_object* v_bs_1929_){
_start:
{
size_t v_sz_boxed_1930_; size_t v_i_boxed_1931_; lean_object* v_res_1932_; 
v_sz_boxed_1930_ = lean_unbox_usize(v_sz_1927_);
lean_dec(v_sz_1927_);
v_i_boxed_1931_ = lean_unbox_usize(v_i_1928_);
lean_dec(v_i_1928_);
v_res_1932_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8(v_sz_boxed_1930_, v_i_boxed_1931_, v_bs_1929_);
return v_res_1932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5___redArg(lean_object* v_inst_1933_, lean_object* v_declInfos_1934_, lean_object* v_k_1935_, uint8_t v_kind_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_){
_start:
{
size_t v_sz_1946_; size_t v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; 
v_sz_1946_ = lean_array_size(v_declInfos_1934_);
v___x_1947_ = ((size_t)0ULL);
v___x_1948_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8(v_sz_1946_, v___x_1947_, v_declInfos_1934_);
v___x_1949_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9___redArg(v_inst_1933_, v___x_1948_, v_k_1935_, v_kind_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_);
return v___x_1949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5___redArg___boxed(lean_object* v_inst_1950_, lean_object* v_declInfos_1951_, lean_object* v_k_1952_, lean_object* v_kind_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_){
_start:
{
uint8_t v_kind_boxed_1963_; lean_object* v_res_1964_; 
v_kind_boxed_1963_ = lean_unbox(v_kind_1953_);
v_res_1964_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5___redArg(v_inst_1950_, v_declInfos_1951_, v_k_1952_, v_kind_boxed_1963_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_);
lean_dec(v_inst_1950_);
return v_res_1964_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__2___redArg(size_t v_sz_1965_, size_t v_i_1966_, lean_object* v_bs_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_){
_start:
{
uint8_t v___x_1973_; 
v___x_1973_ = lean_usize_dec_lt(v_i_1966_, v_sz_1965_);
if (v___x_1973_ == 0)
{
lean_object* v___x_1974_; 
lean_dec(v___y_1971_);
lean_dec_ref(v___y_1970_);
lean_dec(v___y_1969_);
lean_dec_ref(v___y_1968_);
v___x_1974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1974_, 0, v_bs_1967_);
return v___x_1974_;
}
else
{
lean_object* v_v_1975_; lean_object* v_fst_1976_; lean_object* v_snd_1977_; lean_object* v___x_1978_; 
v_v_1975_ = lean_array_uget_borrowed(v_bs_1967_, v_i_1966_);
v_fst_1976_ = lean_ctor_get(v_v_1975_, 0);
v_snd_1977_ = lean_ctor_get(v_v_1975_, 1);
lean_inc(v___y_1971_);
lean_inc_ref(v___y_1970_);
lean_inc(v___y_1969_);
lean_inc_ref(v___y_1968_);
lean_inc(v_fst_1976_);
lean_inc(v_snd_1977_);
v___x_1978_ = l_Lean_Meta_mkEq(v_snd_1977_, v_fst_1976_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_);
if (lean_obj_tag(v___x_1978_) == 0)
{
lean_object* v_a_1979_; lean_object* v___x_1980_; lean_object* v_bs_x27_1981_; size_t v___x_1982_; size_t v___x_1983_; lean_object* v___x_1984_; 
v_a_1979_ = lean_ctor_get(v___x_1978_, 0);
lean_inc(v_a_1979_);
lean_dec_ref(v___x_1978_);
v___x_1980_ = lean_unsigned_to_nat(0u);
v_bs_x27_1981_ = lean_array_uset(v_bs_1967_, v_i_1966_, v___x_1980_);
v___x_1982_ = ((size_t)1ULL);
v___x_1983_ = lean_usize_add(v_i_1966_, v___x_1982_);
v___x_1984_ = lean_array_uset(v_bs_x27_1981_, v_i_1966_, v_a_1979_);
v_i_1966_ = v___x_1983_;
v_bs_1967_ = v___x_1984_;
goto _start;
}
else
{
lean_object* v_a_1986_; lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_1993_; 
lean_dec(v___y_1971_);
lean_dec_ref(v___y_1970_);
lean_dec(v___y_1969_);
lean_dec_ref(v___y_1968_);
lean_dec_ref(v_bs_1967_);
v_a_1986_ = lean_ctor_get(v___x_1978_, 0);
v_isSharedCheck_1993_ = !lean_is_exclusive(v___x_1978_);
if (v_isSharedCheck_1993_ == 0)
{
v___x_1988_ = v___x_1978_;
v_isShared_1989_ = v_isSharedCheck_1993_;
goto v_resetjp_1987_;
}
else
{
lean_inc(v_a_1986_);
lean_dec(v___x_1978_);
v___x_1988_ = lean_box(0);
v_isShared_1989_ = v_isSharedCheck_1993_;
goto v_resetjp_1987_;
}
v_resetjp_1987_:
{
lean_object* v___x_1991_; 
if (v_isShared_1989_ == 0)
{
v___x_1991_ = v___x_1988_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v_a_1986_);
v___x_1991_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
return v___x_1991_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__2___redArg___boxed(lean_object* v_sz_1994_, lean_object* v_i_1995_, lean_object* v_bs_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_){
_start:
{
size_t v_sz_boxed_2002_; size_t v_i_boxed_2003_; lean_object* v_res_2004_; 
v_sz_boxed_2002_ = lean_unbox_usize(v_sz_1994_);
lean_dec(v_sz_1994_);
v_i_boxed_2003_ = lean_unbox_usize(v_i_1995_);
lean_dec(v_i_1995_);
v_res_2004_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__2___redArg(v_sz_boxed_2002_, v_i_boxed_2003_, v_bs_1996_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_);
return v_res_2004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1___lam__0(lean_object* v_revertArgs_2005_, lean_object* v_hypName_2006_, lean_object* v_u_2007_, lean_object* v_00_u03c3s_2008_, uint8_t v___x_2009_, lean_object* v_hyps_2010_, lean_object* v_ss_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_){
_start:
{
lean_object* v___x_2021_; size_t v_sz_2022_; size_t v___x_2023_; lean_object* v___x_2024_; 
v___x_2021_ = l_Array_zip___redArg(v_revertArgs_2005_, v_ss_2011_);
v_sz_2022_ = lean_array_size(v___x_2021_);
v___x_2023_ = ((size_t)0ULL);
lean_inc(v___y_2019_);
lean_inc_ref(v___y_2018_);
lean_inc(v___y_2017_);
lean_inc_ref(v___y_2016_);
v___x_2024_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__2___redArg(v_sz_2022_, v___x_2023_, v___x_2021_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_);
if (lean_obj_tag(v___x_2024_) == 0)
{
lean_object* v_a_2025_; lean_object* v___x_2026_; 
v_a_2025_ = lean_ctor_get(v___x_2024_, 0);
lean_inc(v_a_2025_);
lean_dec_ref(v___x_2024_);
lean_inc(v___y_2019_);
lean_inc_ref(v___y_2018_);
lean_inc(v_hypName_2006_);
v___x_2026_ = l_Lean_Core_mkFreshUserName(v_hypName_2006_, v___y_2018_, v___y_2019_);
if (lean_obj_tag(v___x_2026_) == 0)
{
lean_object* v_a_2027_; lean_object* v_eqs_2028_; lean_object* v_00_u03c6_2029_; lean_object* v_00_u03c6_2030_; uint8_t v___x_2031_; uint8_t v___x_2032_; lean_object* v___x_2033_; 
v_a_2027_ = lean_ctor_get(v___x_2026_, 0);
lean_inc(v_a_2027_);
lean_dec_ref(v___x_2026_);
v_eqs_2028_ = lean_array_to_list(v_a_2025_);
v_00_u03c6_2029_ = l_Lean_mkAndN(v_eqs_2028_);
v_00_u03c6_2030_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure(v_u_2007_, v_00_u03c3s_2008_, v_00_u03c6_2029_);
v___x_2031_ = 1;
v___x_2032_ = 1;
v___x_2033_ = l_Lean_Meta_mkLambdaFVars(v_ss_2011_, v_00_u03c6_2030_, v___x_2009_, v___x_2031_, v___x_2009_, v___x_2031_, v___x_2032_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_);
if (lean_obj_tag(v___x_2033_) == 0)
{
lean_object* v_a_2034_; lean_object* v___x_2035_; 
v_a_2034_ = lean_ctor_get(v___x_2033_, 0);
lean_inc(v_a_2034_);
lean_dec_ref(v___x_2033_);
v___x_2035_ = l_Lean_Meta_mkLambdaFVars(v_ss_2011_, v_hyps_2010_, v___x_2009_, v___x_2031_, v___x_2009_, v___x_2031_, v___x_2032_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_);
lean_dec(v___y_2019_);
lean_dec_ref(v___y_2018_);
lean_dec(v___y_2017_);
lean_dec_ref(v___y_2016_);
if (lean_obj_tag(v___x_2035_) == 0)
{
lean_object* v_a_2036_; lean_object* v___x_2038_; uint8_t v_isShared_2039_; uint8_t v_isSharedCheck_2046_; 
v_a_2036_ = lean_ctor_get(v___x_2035_, 0);
v_isSharedCheck_2046_ = !lean_is_exclusive(v___x_2035_);
if (v_isSharedCheck_2046_ == 0)
{
v___x_2038_ = v___x_2035_;
v_isShared_2039_ = v_isSharedCheck_2046_;
goto v_resetjp_2037_;
}
else
{
lean_inc(v_a_2036_);
lean_dec(v___x_2035_);
v___x_2038_ = lean_box(0);
v_isShared_2039_ = v_isSharedCheck_2046_;
goto v_resetjp_2037_;
}
v_resetjp_2037_:
{
lean_object* v___x_2040_; lean_object* v_00_u03c6_2041_; lean_object* v___x_2042_; lean_object* v___x_2044_; 
v___x_2040_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2040_, 0, v_hypName_2006_);
lean_ctor_set(v___x_2040_, 1, v_a_2027_);
lean_ctor_set(v___x_2040_, 2, v_a_2034_);
v_00_u03c6_2041_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_2040_);
v___x_2042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2042_, 0, v_a_2036_);
lean_ctor_set(v___x_2042_, 1, v_00_u03c6_2041_);
if (v_isShared_2039_ == 0)
{
lean_ctor_set(v___x_2038_, 0, v___x_2042_);
v___x_2044_ = v___x_2038_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v___x_2042_);
v___x_2044_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
return v___x_2044_;
}
}
}
else
{
lean_object* v_a_2047_; lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2054_; 
lean_dec(v_a_2034_);
lean_dec(v_a_2027_);
lean_dec(v_hypName_2006_);
v_a_2047_ = lean_ctor_get(v___x_2035_, 0);
v_isSharedCheck_2054_ = !lean_is_exclusive(v___x_2035_);
if (v_isSharedCheck_2054_ == 0)
{
v___x_2049_ = v___x_2035_;
v_isShared_2050_ = v_isSharedCheck_2054_;
goto v_resetjp_2048_;
}
else
{
lean_inc(v_a_2047_);
lean_dec(v___x_2035_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2054_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
lean_object* v___x_2052_; 
if (v_isShared_2050_ == 0)
{
v___x_2052_ = v___x_2049_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v_a_2047_);
v___x_2052_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
return v___x_2052_;
}
}
}
}
else
{
lean_object* v_a_2055_; lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2062_; 
lean_dec(v_a_2027_);
lean_dec(v___y_2019_);
lean_dec_ref(v___y_2018_);
lean_dec(v___y_2017_);
lean_dec_ref(v___y_2016_);
lean_dec_ref(v_hyps_2010_);
lean_dec(v_hypName_2006_);
v_a_2055_ = lean_ctor_get(v___x_2033_, 0);
v_isSharedCheck_2062_ = !lean_is_exclusive(v___x_2033_);
if (v_isSharedCheck_2062_ == 0)
{
v___x_2057_ = v___x_2033_;
v_isShared_2058_ = v_isSharedCheck_2062_;
goto v_resetjp_2056_;
}
else
{
lean_inc(v_a_2055_);
lean_dec(v___x_2033_);
v___x_2057_ = lean_box(0);
v_isShared_2058_ = v_isSharedCheck_2062_;
goto v_resetjp_2056_;
}
v_resetjp_2056_:
{
lean_object* v___x_2060_; 
if (v_isShared_2058_ == 0)
{
v___x_2060_ = v___x_2057_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v_a_2055_);
v___x_2060_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
return v___x_2060_;
}
}
}
}
else
{
lean_object* v_a_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2070_; 
lean_dec(v_a_2025_);
lean_dec(v___y_2019_);
lean_dec_ref(v___y_2018_);
lean_dec(v___y_2017_);
lean_dec_ref(v___y_2016_);
lean_dec_ref(v_hyps_2010_);
lean_dec_ref(v_00_u03c3s_2008_);
lean_dec(v_u_2007_);
lean_dec(v_hypName_2006_);
v_a_2063_ = lean_ctor_get(v___x_2026_, 0);
v_isSharedCheck_2070_ = !lean_is_exclusive(v___x_2026_);
if (v_isSharedCheck_2070_ == 0)
{
v___x_2065_ = v___x_2026_;
v_isShared_2066_ = v_isSharedCheck_2070_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_a_2063_);
lean_dec(v___x_2026_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2070_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
lean_object* v___x_2068_; 
if (v_isShared_2066_ == 0)
{
v___x_2068_ = v___x_2065_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v_a_2063_);
v___x_2068_ = v_reuseFailAlloc_2069_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
return v___x_2068_;
}
}
}
}
else
{
lean_object* v_a_2071_; lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2078_; 
lean_dec(v___y_2019_);
lean_dec_ref(v___y_2018_);
lean_dec(v___y_2017_);
lean_dec_ref(v___y_2016_);
lean_dec_ref(v_hyps_2010_);
lean_dec_ref(v_00_u03c3s_2008_);
lean_dec(v_u_2007_);
lean_dec(v_hypName_2006_);
v_a_2071_ = lean_ctor_get(v___x_2024_, 0);
v_isSharedCheck_2078_ = !lean_is_exclusive(v___x_2024_);
if (v_isSharedCheck_2078_ == 0)
{
v___x_2073_ = v___x_2024_;
v_isShared_2074_ = v_isSharedCheck_2078_;
goto v_resetjp_2072_;
}
else
{
lean_inc(v_a_2071_);
lean_dec(v___x_2024_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2078_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
lean_object* v___x_2076_; 
if (v_isShared_2074_ == 0)
{
v___x_2076_ = v___x_2073_;
goto v_reusejp_2075_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v_a_2071_);
v___x_2076_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2075_;
}
v_reusejp_2075_:
{
return v___x_2076_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1___lam__0___boxed(lean_object* v_revertArgs_2079_, lean_object* v_hypName_2080_, lean_object* v_u_2081_, lean_object* v_00_u03c3s_2082_, lean_object* v___x_2083_, lean_object* v_hyps_2084_, lean_object* v_ss_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_){
_start:
{
uint8_t v___x_21685__boxed_2095_; lean_object* v_res_2096_; 
v___x_21685__boxed_2095_ = lean_unbox(v___x_2083_);
v_res_2096_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1___lam__0(v_revertArgs_2079_, v_hypName_2080_, v_u_2081_, v_00_u03c3s_2082_, v___x_21685__boxed_2095_, v_hyps_2084_, v_ss_2085_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_);
lean_dec(v___y_2089_);
lean_dec_ref(v___y_2088_);
lean_dec(v___y_2087_);
lean_dec_ref(v___y_2086_);
lean_dec_ref(v_ss_2085_);
lean_dec_ref(v_revertArgs_2079_);
return v_res_2096_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2097_; lean_object* v___x_2098_; 
v___x_2097_ = l_Lean_instInhabitedExpr;
v___x_2098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2098_, 0, v___x_2097_);
lean_ctor_set(v___x_2098_, 1, v___x_2097_);
return v___x_2098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1(lean_object* v_goal_2099_, lean_object* v_n_2100_, lean_object* v_hypName_2101_, lean_object* v_k_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_){
_start:
{
lean_object* v___x_2112_; uint8_t v___x_2113_; 
v___x_2112_ = lean_unsigned_to_nat(0u);
v___x_2113_ = lean_nat_dec_eq(v_n_2100_, v___x_2112_);
if (v___x_2113_ == 0)
{
lean_object* v_u_2114_; lean_object* v_00_u03c3s_2115_; lean_object* v_hyps_2116_; lean_object* v_target_2117_; lean_object* v___x_2119_; uint8_t v_isShared_2120_; uint8_t v_isSharedCheck_2272_; 
v_u_2114_ = lean_ctor_get(v_goal_2099_, 0);
v_00_u03c3s_2115_ = lean_ctor_get(v_goal_2099_, 1);
v_hyps_2116_ = lean_ctor_get(v_goal_2099_, 2);
v_target_2117_ = lean_ctor_get(v_goal_2099_, 3);
v_isSharedCheck_2272_ = !lean_is_exclusive(v_goal_2099_);
if (v_isSharedCheck_2272_ == 0)
{
v___x_2119_ = v_goal_2099_;
v_isShared_2120_ = v_isSharedCheck_2272_;
goto v_resetjp_2118_;
}
else
{
lean_inc(v_target_2117_);
lean_inc(v_hyps_2116_);
lean_inc(v_00_u03c3s_2115_);
lean_inc(v_u_2114_);
lean_dec(v_goal_2099_);
v___x_2119_ = lean_box(0);
v_isShared_2120_ = v_isSharedCheck_2272_;
goto v_resetjp_2118_;
}
v_resetjp_2118_:
{
lean_object* v_T_2121_; lean_object* v_f_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v_a_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v_revertArgs_2129_; lean_object* v___y_2131_; lean_object* v___y_2132_; lean_object* v___y_2133_; lean_object* v___y_2134_; lean_object* v___y_2135_; lean_object* v___y_2136_; lean_object* v___y_2137_; lean_object* v___y_2138_; lean_object* v___y_2139_; lean_object* v___y_2140_; lean_object* v___y_2141_; lean_object* v___y_2142_; lean_object* v___x_2181_; lean_object* v___f_2182_; lean_object* v___y_2184_; lean_object* v___y_2185_; lean_object* v___y_2186_; lean_object* v___y_2187_; lean_object* v___y_2188_; lean_object* v___y_2189_; lean_object* v___y_2190_; lean_object* v___y_2191_; lean_object* v___x_2246_; uint8_t v___x_2247_; 
v_T_2121_ = l_Lean_Expr_consumeMData(v_target_2117_);
v_f_2122_ = l_Lean_Expr_getAppFn(v_T_2121_);
v___x_2123_ = l_Lean_Expr_getAppNumArgs(v_T_2121_);
v___x_2124_ = lean_mk_empty_array_with_capacity(v___x_2123_);
lean_dec(v___x_2123_);
lean_inc_ref(v_T_2121_);
v_a_2125_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_T_2121_, v___x_2124_);
lean_inc(v_n_2100_);
lean_inc_ref(v_a_2125_);
v___x_2126_ = l_Array_toSubarray___redArg(v_a_2125_, v___x_2112_, v_n_2100_);
v___x_2127_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__1));
v___x_2128_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__1___redArg(v___x_2126_, v___x_2127_);
v_revertArgs_2129_ = l_Array_reverse___redArg(v___x_2128_);
v___x_2181_ = lean_box(v___x_2113_);
lean_inc_ref(v_hyps_2116_);
lean_inc_ref(v_00_u03c3s_2115_);
lean_inc(v_u_2114_);
lean_inc_ref(v_revertArgs_2129_);
v___f_2182_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1___lam__0___boxed), 16, 6);
lean_closure_set(v___f_2182_, 0, v_revertArgs_2129_);
lean_closure_set(v___f_2182_, 1, v_hypName_2101_);
lean_closure_set(v___f_2182_, 2, v_u_2114_);
lean_closure_set(v___f_2182_, 3, v_00_u03c3s_2115_);
lean_closure_set(v___f_2182_, 4, v___x_2181_);
lean_closure_set(v___f_2182_, 5, v_hyps_2116_);
v___x_2246_ = lean_array_get_size(v_revertArgs_2129_);
v___x_2247_ = lean_nat_dec_eq(v___x_2246_, v_n_2100_);
if (v___x_2247_ == 0)
{
lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v_a_2264_; lean_object* v___x_2266_; uint8_t v_isShared_2267_; uint8_t v_isSharedCheck_2271_; 
lean_dec_ref(v___f_2182_);
lean_dec_ref(v_revertArgs_2129_);
lean_dec_ref(v_a_2125_);
lean_dec_ref(v_f_2122_);
lean_del_object(v___x_2119_);
lean_dec_ref(v_target_2117_);
lean_dec_ref(v_hyps_2116_);
lean_dec_ref(v_00_u03c3s_2115_);
lean_dec(v_u_2114_);
lean_dec(v___y_2106_);
lean_dec_ref(v___y_2105_);
lean_dec(v___y_2104_);
lean_dec_ref(v___y_2103_);
lean_dec_ref(v_k_2102_);
v___x_2248_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__14, &l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__14_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__14);
v___x_2249_ = l_Nat_reprFast(v_n_2100_);
v___x_2250_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2250_, 0, v___x_2249_);
v___x_2251_ = l_Lean_MessageData_ofFormat(v___x_2250_);
v___x_2252_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2252_, 0, v___x_2248_);
lean_ctor_set(v___x_2252_, 1, v___x_2251_);
v___x_2253_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__16, &l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__16_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__16);
v___x_2254_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2254_, 0, v___x_2252_);
lean_ctor_set(v___x_2254_, 1, v___x_2253_);
v___x_2255_ = l_Lean_MessageData_ofExpr(v_T_2121_);
v___x_2256_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2256_, 0, v___x_2254_);
lean_ctor_set(v___x_2256_, 1, v___x_2255_);
v___x_2257_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__18, &l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__18_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__18);
v___x_2258_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2258_, 0, v___x_2256_);
lean_ctor_set(v___x_2258_, 1, v___x_2257_);
v___x_2259_ = l_Nat_reprFast(v___x_2246_);
v___x_2260_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2260_, 0, v___x_2259_);
v___x_2261_ = l_Lean_MessageData_ofFormat(v___x_2260_);
v___x_2262_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2262_, 0, v___x_2258_);
lean_ctor_set(v___x_2262_, 1, v___x_2261_);
v___x_2263_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__8___redArg(v___x_2262_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_);
lean_dec(v___y_2110_);
lean_dec_ref(v___y_2109_);
lean_dec(v___y_2108_);
lean_dec_ref(v___y_2107_);
v_a_2264_ = lean_ctor_get(v___x_2263_, 0);
v_isSharedCheck_2271_ = !lean_is_exclusive(v___x_2263_);
if (v_isSharedCheck_2271_ == 0)
{
v___x_2266_ = v___x_2263_;
v_isShared_2267_ = v_isSharedCheck_2271_;
goto v_resetjp_2265_;
}
else
{
lean_inc(v_a_2264_);
lean_dec(v___x_2263_);
v___x_2266_ = lean_box(0);
v_isShared_2267_ = v_isSharedCheck_2271_;
goto v_resetjp_2265_;
}
v_resetjp_2265_:
{
lean_object* v___x_2269_; 
if (v_isShared_2267_ == 0)
{
v___x_2269_ = v___x_2266_;
goto v_reusejp_2268_;
}
else
{
lean_object* v_reuseFailAlloc_2270_; 
v_reuseFailAlloc_2270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2270_, 0, v_a_2264_);
v___x_2269_ = v_reuseFailAlloc_2270_;
goto v_reusejp_2268_;
}
v_reusejp_2268_:
{
return v___x_2269_;
}
}
}
else
{
lean_dec_ref(v_T_2121_);
v___y_2184_ = v___y_2103_;
v___y_2185_ = v___y_2104_;
v___y_2186_ = v___y_2105_;
v___y_2187_ = v___y_2106_;
v___y_2188_ = v___y_2107_;
v___y_2189_ = v___y_2108_;
v___y_2190_ = v___y_2109_;
v___y_2191_ = v___y_2110_;
goto v___jp_2183_;
}
v___jp_2130_:
{
lean_object* v___x_2143_; 
v___x_2143_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v___y_2134_, v___y_2131_);
if (lean_obj_tag(v___x_2143_) == 0)
{
lean_object* v_a_2144_; lean_object* v_H_2145_; lean_object* v___x_2146_; lean_object* v_fst_2147_; lean_object* v_snd_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2180_; 
v_a_2144_ = lean_ctor_get(v___x_2143_, 0);
lean_inc(v_a_2144_);
lean_dec_ref(v___x_2143_);
lean_inc_ref(v___y_2142_);
v_H_2145_ = l_Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps(v___y_2142_, v_a_2144_);
lean_inc_ref(v___y_2142_);
lean_inc(v_u_2114_);
v___x_2146_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd(v_u_2114_, v___y_2142_, v_H_2145_, v___y_2137_);
v_fst_2147_ = lean_ctor_get(v___x_2146_, 0);
v_snd_2148_ = lean_ctor_get(v___x_2146_, 1);
v_isSharedCheck_2180_ = !lean_is_exclusive(v___x_2146_);
if (v_isSharedCheck_2180_ == 0)
{
v___x_2150_ = v___x_2146_;
v_isShared_2151_ = v_isSharedCheck_2180_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_snd_2148_);
lean_inc(v_fst_2147_);
lean_dec(v___x_2146_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2180_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v_goal_x27_2157_; 
v___x_2152_ = lean_array_get_size(v_a_2125_);
v___x_2153_ = l_Array_toSubarray___redArg(v_a_2125_, v_n_2100_, v___x_2152_);
v___x_2154_ = l_Subarray_copy___redArg(v___x_2153_);
v___x_2155_ = l_Lean_mkAppRev(v_f_2122_, v___x_2154_);
lean_dec_ref(v___x_2154_);
lean_inc(v_fst_2147_);
lean_inc(v_u_2114_);
if (v_isShared_2120_ == 0)
{
lean_ctor_set(v___x_2119_, 3, v___x_2155_);
lean_ctor_set(v___x_2119_, 2, v_fst_2147_);
lean_ctor_set(v___x_2119_, 1, v___y_2142_);
v_goal_x27_2157_ = v___x_2119_;
goto v_reusejp_2156_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v_u_2114_);
lean_ctor_set(v_reuseFailAlloc_2179_, 1, v___y_2142_);
lean_ctor_set(v_reuseFailAlloc_2179_, 2, v_fst_2147_);
lean_ctor_set(v_reuseFailAlloc_2179_, 3, v___x_2155_);
v_goal_x27_2157_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2156_;
}
v_reusejp_2156_:
{
lean_object* v___x_2158_; 
lean_inc(v___y_2136_);
lean_inc_ref(v___y_2139_);
lean_inc(v___y_2131_);
lean_inc_ref(v___y_2140_);
v___x_2158_ = lean_apply_10(v_k_2102_, v_goal_x27_2157_, v___y_2132_, v___y_2135_, v___y_2141_, v___y_2138_, v___y_2140_, v___y_2131_, v___y_2139_, v___y_2136_, lean_box(0));
if (lean_obj_tag(v___x_2158_) == 0)
{
lean_object* v_a_2159_; lean_object* v___x_2160_; 
v_a_2159_ = lean_ctor_get(v___x_2158_, 0);
lean_inc(v_a_2159_);
lean_dec_ref(v___x_2158_);
lean_inc_ref(v___y_2133_);
v___x_2160_ = lean_infer_type(v___y_2133_, v___y_2140_, v___y_2131_, v___y_2139_, v___y_2136_);
if (lean_obj_tag(v___x_2160_) == 0)
{
lean_object* v_a_2161_; lean_object* v___x_2163_; uint8_t v_isShared_2164_; uint8_t v_isSharedCheck_2178_; 
v_a_2161_ = lean_ctor_get(v___x_2160_, 0);
v_isSharedCheck_2178_ = !lean_is_exclusive(v___x_2160_);
if (v_isSharedCheck_2178_ == 0)
{
v___x_2163_ = v___x_2160_;
v_isShared_2164_ = v_isSharedCheck_2178_;
goto v_resetjp_2162_;
}
else
{
lean_inc(v_a_2161_);
lean_dec(v___x_2160_);
v___x_2163_ = lean_box(0);
v_isShared_2164_ = v_isSharedCheck_2178_;
goto v_resetjp_2162_;
}
v_resetjp_2162_:
{
lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2168_; 
v___x_2165_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__12___closed__1));
v___x_2166_ = lean_box(0);
if (v_isShared_2151_ == 0)
{
lean_ctor_set_tag(v___x_2150_, 1);
lean_ctor_set(v___x_2150_, 1, v___x_2166_);
lean_ctor_set(v___x_2150_, 0, v_u_2114_);
v___x_2168_ = v___x_2150_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v_u_2114_);
lean_ctor_set(v_reuseFailAlloc_2177_, 1, v___x_2166_);
v___x_2168_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v_prf_2173_; lean_object* v___x_2175_; 
v___x_2169_ = l_Lean_mkConst(v___x_2165_, v___x_2168_);
v___x_2170_ = l_Lean_mkAppN(v_fst_2147_, v_revertArgs_2129_);
v___x_2171_ = l_Lean_mkAppN(v_snd_2148_, v_revertArgs_2129_);
v___x_2172_ = l_Lean_mkAppN(v_a_2159_, v_revertArgs_2129_);
lean_dec_ref(v_revertArgs_2129_);
v_prf_2173_ = l_Lean_mkApp8(v___x_2169_, v_00_u03c3s_2115_, v_a_2161_, v_hyps_2116_, v___x_2170_, v_target_2117_, v___y_2133_, v___x_2171_, v___x_2172_);
if (v_isShared_2164_ == 0)
{
lean_ctor_set(v___x_2163_, 0, v_prf_2173_);
v___x_2175_ = v___x_2163_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v_prf_2173_);
v___x_2175_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
return v___x_2175_;
}
}
}
}
else
{
lean_dec(v_a_2159_);
lean_del_object(v___x_2150_);
lean_dec(v_snd_2148_);
lean_dec(v_fst_2147_);
lean_dec_ref(v___y_2133_);
lean_dec_ref(v_revertArgs_2129_);
lean_dec_ref(v_target_2117_);
lean_dec_ref(v_hyps_2116_);
lean_dec_ref(v_00_u03c3s_2115_);
lean_dec(v_u_2114_);
return v___x_2160_;
}
}
else
{
lean_del_object(v___x_2150_);
lean_dec(v_snd_2148_);
lean_dec(v_fst_2147_);
lean_dec_ref(v___y_2140_);
lean_dec_ref(v___y_2139_);
lean_dec(v___y_2136_);
lean_dec_ref(v___y_2133_);
lean_dec(v___y_2131_);
lean_dec_ref(v_revertArgs_2129_);
lean_dec_ref(v_target_2117_);
lean_dec_ref(v_hyps_2116_);
lean_dec_ref(v_00_u03c3s_2115_);
lean_dec(v_u_2114_);
return v___x_2158_;
}
}
}
}
else
{
lean_dec_ref(v___y_2142_);
lean_dec_ref(v___y_2141_);
lean_dec_ref(v___y_2140_);
lean_dec_ref(v___y_2139_);
lean_dec(v___y_2138_);
lean_dec_ref(v___y_2137_);
lean_dec(v___y_2136_);
lean_dec(v___y_2135_);
lean_dec_ref(v___y_2133_);
lean_dec_ref(v___y_2132_);
lean_dec(v___y_2131_);
lean_dec_ref(v_revertArgs_2129_);
lean_dec_ref(v_a_2125_);
lean_dec_ref(v_f_2122_);
lean_del_object(v___x_2119_);
lean_dec_ref(v_target_2117_);
lean_dec_ref(v_hyps_2116_);
lean_dec_ref(v_00_u03c3s_2115_);
lean_dec(v_u_2114_);
lean_dec_ref(v_k_2102_);
lean_dec(v_n_2100_);
return v___x_2143_;
}
}
v___jp_2183_:
{
size_t v_sz_2192_; size_t v___x_2193_; lean_object* v___x_2194_; 
v_sz_2192_ = lean_array_size(v_revertArgs_2129_);
v___x_2193_ = ((size_t)0ULL);
lean_inc(v___y_2191_);
lean_inc_ref(v___y_2190_);
lean_inc(v___y_2189_);
lean_inc_ref(v___y_2188_);
lean_inc_ref(v_revertArgs_2129_);
v___x_2194_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__3(v_sz_2192_, v___x_2193_, v_revertArgs_2129_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_);
if (lean_obj_tag(v___x_2194_) == 0)
{
lean_object* v_a_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; 
v_a_2195_ = lean_ctor_get(v___x_2194_, 0);
lean_inc(v_a_2195_);
lean_dec_ref(v___x_2194_);
v___x_2196_ = lean_array_get_size(v_a_2195_);
v___x_2197_ = lean_mk_empty_array_with_capacity(v___x_2196_);
lean_inc(v___y_2191_);
lean_inc_ref(v___y_2190_);
v___x_2198_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__4___redArg(v_a_2195_, v___x_2196_, v___x_2112_, v___x_2197_, v___y_2190_, v___y_2191_);
if (lean_obj_tag(v___x_2198_) == 0)
{
lean_object* v_a_2199_; lean_object* v___x_2200_; uint8_t v___x_2201_; lean_object* v___x_2202_; 
v_a_2199_ = lean_ctor_get(v___x_2198_, 0);
lean_inc(v_a_2199_);
lean_dec_ref(v___x_2198_);
v___x_2200_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1___closed__0, &l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1___closed__0_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1___closed__0);
v___x_2201_ = 0;
lean_inc(v___y_2191_);
lean_inc_ref(v___y_2190_);
lean_inc(v___y_2189_);
lean_inc_ref(v___y_2188_);
lean_inc(v___y_2187_);
lean_inc_ref(v___y_2186_);
lean_inc(v___y_2185_);
lean_inc_ref(v___y_2184_);
v___x_2202_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5___redArg(v___x_2200_, v_a_2199_, v___f_2182_, v___x_2201_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_);
if (lean_obj_tag(v___x_2202_) == 0)
{
lean_object* v_a_2203_; lean_object* v_fst_2204_; lean_object* v_snd_2205_; lean_object* v___x_2206_; 
v_a_2203_ = lean_ctor_get(v___x_2202_, 0);
lean_inc(v_a_2203_);
lean_dec_ref(v___x_2202_);
v_fst_2204_ = lean_ctor_get(v_a_2203_, 0);
lean_inc(v_fst_2204_);
v_snd_2205_ = lean_ctor_get(v_a_2203_, 1);
lean_inc(v_snd_2205_);
lean_dec(v_a_2203_);
lean_inc(v___y_2191_);
lean_inc_ref(v___y_2190_);
lean_inc(v___y_2189_);
lean_inc_ref(v___y_2188_);
lean_inc_ref(v_revertArgs_2129_);
v___x_2206_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__6(v_sz_2192_, v___x_2193_, v_revertArgs_2129_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_);
if (lean_obj_tag(v___x_2206_) == 0)
{
lean_object* v_a_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; 
v_a_2207_ = lean_ctor_get(v___x_2206_, 0);
lean_inc(v_a_2207_);
lean_dec_ref(v___x_2206_);
v___x_2208_ = lean_array_to_list(v_a_2207_);
lean_inc(v___y_2191_);
lean_inc_ref(v___y_2190_);
lean_inc(v___y_2189_);
lean_inc_ref(v___y_2188_);
v___x_2209_ = l_Lean_Meta_mkAndIntroN(v___x_2208_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_);
if (lean_obj_tag(v___x_2209_) == 0)
{
lean_object* v_a_2210_; uint8_t v___x_2211_; 
v_a_2210_ = lean_ctor_get(v___x_2209_, 0);
lean_inc(v_a_2210_);
lean_dec_ref(v___x_2209_);
v___x_2211_ = lean_nat_dec_lt(v___x_2112_, v___x_2196_);
if (v___x_2211_ == 0)
{
lean_dec(v_a_2195_);
lean_inc_ref(v_00_u03c3s_2115_);
v___y_2131_ = v___y_2189_;
v___y_2132_ = v___y_2184_;
v___y_2133_ = v_a_2210_;
v___y_2134_ = v_fst_2204_;
v___y_2135_ = v___y_2185_;
v___y_2136_ = v___y_2191_;
v___y_2137_ = v_snd_2205_;
v___y_2138_ = v___y_2187_;
v___y_2139_ = v___y_2190_;
v___y_2140_ = v___y_2188_;
v___y_2141_ = v___y_2186_;
v___y_2142_ = v_00_u03c3s_2115_;
goto v___jp_2130_;
}
else
{
size_t v___x_2212_; lean_object* v___x_2213_; 
v___x_2212_ = lean_usize_of_nat(v___x_2196_);
lean_inc_ref(v_00_u03c3s_2115_);
lean_inc(v_u_2114_);
v___x_2213_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__7(v_u_2114_, v_a_2195_, v___x_2212_, v___x_2193_, v_00_u03c3s_2115_);
lean_dec(v_a_2195_);
v___y_2131_ = v___y_2189_;
v___y_2132_ = v___y_2184_;
v___y_2133_ = v_a_2210_;
v___y_2134_ = v_fst_2204_;
v___y_2135_ = v___y_2185_;
v___y_2136_ = v___y_2191_;
v___y_2137_ = v_snd_2205_;
v___y_2138_ = v___y_2187_;
v___y_2139_ = v___y_2190_;
v___y_2140_ = v___y_2188_;
v___y_2141_ = v___y_2186_;
v___y_2142_ = v___x_2213_;
goto v___jp_2130_;
}
}
else
{
lean_dec(v_snd_2205_);
lean_dec(v_fst_2204_);
lean_dec(v_a_2195_);
lean_dec(v___y_2191_);
lean_dec_ref(v___y_2190_);
lean_dec(v___y_2189_);
lean_dec_ref(v___y_2188_);
lean_dec(v___y_2187_);
lean_dec_ref(v___y_2186_);
lean_dec(v___y_2185_);
lean_dec_ref(v___y_2184_);
lean_dec_ref(v_revertArgs_2129_);
lean_dec_ref(v_a_2125_);
lean_dec_ref(v_f_2122_);
lean_del_object(v___x_2119_);
lean_dec_ref(v_target_2117_);
lean_dec_ref(v_hyps_2116_);
lean_dec_ref(v_00_u03c3s_2115_);
lean_dec(v_u_2114_);
lean_dec_ref(v_k_2102_);
lean_dec(v_n_2100_);
return v___x_2209_;
}
}
else
{
lean_object* v_a_2214_; lean_object* v___x_2216_; uint8_t v_isShared_2217_; uint8_t v_isSharedCheck_2221_; 
lean_dec(v_snd_2205_);
lean_dec(v_fst_2204_);
lean_dec(v_a_2195_);
lean_dec(v___y_2191_);
lean_dec_ref(v___y_2190_);
lean_dec(v___y_2189_);
lean_dec_ref(v___y_2188_);
lean_dec(v___y_2187_);
lean_dec_ref(v___y_2186_);
lean_dec(v___y_2185_);
lean_dec_ref(v___y_2184_);
lean_dec_ref(v_revertArgs_2129_);
lean_dec_ref(v_a_2125_);
lean_dec_ref(v_f_2122_);
lean_del_object(v___x_2119_);
lean_dec_ref(v_target_2117_);
lean_dec_ref(v_hyps_2116_);
lean_dec_ref(v_00_u03c3s_2115_);
lean_dec(v_u_2114_);
lean_dec_ref(v_k_2102_);
lean_dec(v_n_2100_);
v_a_2214_ = lean_ctor_get(v___x_2206_, 0);
v_isSharedCheck_2221_ = !lean_is_exclusive(v___x_2206_);
if (v_isSharedCheck_2221_ == 0)
{
v___x_2216_ = v___x_2206_;
v_isShared_2217_ = v_isSharedCheck_2221_;
goto v_resetjp_2215_;
}
else
{
lean_inc(v_a_2214_);
lean_dec(v___x_2206_);
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
lean_dec(v_a_2195_);
lean_dec(v___y_2191_);
lean_dec_ref(v___y_2190_);
lean_dec(v___y_2189_);
lean_dec_ref(v___y_2188_);
lean_dec(v___y_2187_);
lean_dec_ref(v___y_2186_);
lean_dec(v___y_2185_);
lean_dec_ref(v___y_2184_);
lean_dec_ref(v_revertArgs_2129_);
lean_dec_ref(v_a_2125_);
lean_dec_ref(v_f_2122_);
lean_del_object(v___x_2119_);
lean_dec_ref(v_target_2117_);
lean_dec_ref(v_hyps_2116_);
lean_dec_ref(v_00_u03c3s_2115_);
lean_dec(v_u_2114_);
lean_dec_ref(v_k_2102_);
lean_dec(v_n_2100_);
v_a_2222_ = lean_ctor_get(v___x_2202_, 0);
v_isSharedCheck_2229_ = !lean_is_exclusive(v___x_2202_);
if (v_isSharedCheck_2229_ == 0)
{
v___x_2224_ = v___x_2202_;
v_isShared_2225_ = v_isSharedCheck_2229_;
goto v_resetjp_2223_;
}
else
{
lean_inc(v_a_2222_);
lean_dec(v___x_2202_);
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
lean_dec(v_a_2195_);
lean_dec(v___y_2191_);
lean_dec_ref(v___y_2190_);
lean_dec(v___y_2189_);
lean_dec_ref(v___y_2188_);
lean_dec(v___y_2187_);
lean_dec_ref(v___y_2186_);
lean_dec(v___y_2185_);
lean_dec_ref(v___y_2184_);
lean_dec_ref(v___f_2182_);
lean_dec_ref(v_revertArgs_2129_);
lean_dec_ref(v_a_2125_);
lean_dec_ref(v_f_2122_);
lean_del_object(v___x_2119_);
lean_dec_ref(v_target_2117_);
lean_dec_ref(v_hyps_2116_);
lean_dec_ref(v_00_u03c3s_2115_);
lean_dec(v_u_2114_);
lean_dec_ref(v_k_2102_);
lean_dec(v_n_2100_);
v_a_2230_ = lean_ctor_get(v___x_2198_, 0);
v_isSharedCheck_2237_ = !lean_is_exclusive(v___x_2198_);
if (v_isSharedCheck_2237_ == 0)
{
v___x_2232_ = v___x_2198_;
v_isShared_2233_ = v_isSharedCheck_2237_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_a_2230_);
lean_dec(v___x_2198_);
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
else
{
lean_object* v_a_2238_; lean_object* v___x_2240_; uint8_t v_isShared_2241_; uint8_t v_isSharedCheck_2245_; 
lean_dec(v___y_2191_);
lean_dec_ref(v___y_2190_);
lean_dec(v___y_2189_);
lean_dec_ref(v___y_2188_);
lean_dec(v___y_2187_);
lean_dec_ref(v___y_2186_);
lean_dec(v___y_2185_);
lean_dec_ref(v___y_2184_);
lean_dec_ref(v___f_2182_);
lean_dec_ref(v_revertArgs_2129_);
lean_dec_ref(v_a_2125_);
lean_dec_ref(v_f_2122_);
lean_del_object(v___x_2119_);
lean_dec_ref(v_target_2117_);
lean_dec_ref(v_hyps_2116_);
lean_dec_ref(v_00_u03c3s_2115_);
lean_dec(v_u_2114_);
lean_dec_ref(v_k_2102_);
lean_dec(v_n_2100_);
v_a_2238_ = lean_ctor_get(v___x_2194_, 0);
v_isSharedCheck_2245_ = !lean_is_exclusive(v___x_2194_);
if (v_isSharedCheck_2245_ == 0)
{
v___x_2240_ = v___x_2194_;
v_isShared_2241_ = v_isSharedCheck_2245_;
goto v_resetjp_2239_;
}
else
{
lean_inc(v_a_2238_);
lean_dec(v___x_2194_);
v___x_2240_ = lean_box(0);
v_isShared_2241_ = v_isSharedCheck_2245_;
goto v_resetjp_2239_;
}
v_resetjp_2239_:
{
lean_object* v___x_2243_; 
if (v_isShared_2241_ == 0)
{
v___x_2243_ = v___x_2240_;
goto v_reusejp_2242_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v_a_2238_);
v___x_2243_ = v_reuseFailAlloc_2244_;
goto v_reusejp_2242_;
}
v_reusejp_2242_:
{
return v___x_2243_;
}
}
}
}
}
}
else
{
lean_object* v___x_2273_; 
lean_dec(v_hypName_2101_);
lean_dec(v_n_2100_);
v___x_2273_ = lean_apply_10(v_k_2102_, v_goal_2099_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_, lean_box(0));
return v___x_2273_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1___boxed(lean_object* v_goal_2274_, lean_object* v_n_2275_, lean_object* v_hypName_2276_, lean_object* v_k_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_){
_start:
{
lean_object* v_res_2287_; 
v_res_2287_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1(v_goal_2274_, v_n_2275_, v_hypName_2276_, v_k_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_);
return v_res_2287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__1(lean_object* v___x_2291_, lean_object* v_snd_2292_, lean_object* v___y_2293_, lean_object* v_fst_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_){
_start:
{
lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; 
v___x_2304_ = lean_st_mk_ref(v___x_2291_);
v___x_2305_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__1___closed__1));
lean_inc(v___y_2302_);
lean_inc_ref(v___y_2301_);
v___x_2306_ = l_Lean_Core_mkFreshUserName(v___x_2305_, v___y_2301_, v___y_2302_);
if (lean_obj_tag(v___x_2306_) == 0)
{
lean_object* v_a_2307_; lean_object* v___f_2308_; lean_object* v___x_2309_; 
v_a_2307_ = lean_ctor_get(v___x_2306_, 0);
lean_inc(v_a_2307_);
lean_dec_ref(v___x_2306_);
lean_inc(v___x_2304_);
v___f_2308_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__0___boxed), 11, 1);
lean_closure_set(v___f_2308_, 0, v___x_2304_);
lean_inc(v___y_2302_);
lean_inc_ref(v___y_2301_);
lean_inc(v___y_2300_);
lean_inc_ref(v___y_2299_);
lean_inc(v___y_2296_);
v___x_2309_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1(v_snd_2292_, v___y_2293_, v_a_2307_, v___f_2308_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_);
if (lean_obj_tag(v___x_2309_) == 0)
{
lean_object* v_a_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; 
v_a_2310_ = lean_ctor_get(v___x_2309_, 0);
lean_inc(v_a_2310_);
lean_dec_ref(v___x_2309_);
v___x_2311_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2___redArg(v_fst_2294_, v_a_2310_, v___y_2300_);
lean_dec_ref(v___x_2311_);
v___x_2312_ = lean_st_ref_get(v___x_2304_);
lean_dec(v___x_2304_);
v___x_2313_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2312_, v___y_2296_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_);
lean_dec(v___y_2302_);
lean_dec_ref(v___y_2301_);
lean_dec(v___y_2300_);
lean_dec_ref(v___y_2299_);
lean_dec(v___y_2296_);
return v___x_2313_;
}
else
{
lean_object* v_a_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2321_; 
lean_dec(v___x_2304_);
lean_dec(v___y_2302_);
lean_dec_ref(v___y_2301_);
lean_dec(v___y_2300_);
lean_dec_ref(v___y_2299_);
lean_dec(v___y_2296_);
lean_dec(v_fst_2294_);
v_a_2314_ = lean_ctor_get(v___x_2309_, 0);
v_isSharedCheck_2321_ = !lean_is_exclusive(v___x_2309_);
if (v_isSharedCheck_2321_ == 0)
{
v___x_2316_ = v___x_2309_;
v_isShared_2317_ = v_isSharedCheck_2321_;
goto v_resetjp_2315_;
}
else
{
lean_inc(v_a_2314_);
lean_dec(v___x_2309_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2321_;
goto v_resetjp_2315_;
}
v_resetjp_2315_:
{
lean_object* v___x_2319_; 
if (v_isShared_2317_ == 0)
{
v___x_2319_ = v___x_2316_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v_a_2314_);
v___x_2319_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
return v___x_2319_;
}
}
}
}
else
{
lean_object* v_a_2322_; lean_object* v___x_2324_; uint8_t v_isShared_2325_; uint8_t v_isSharedCheck_2329_; 
lean_dec(v___x_2304_);
lean_dec(v___y_2302_);
lean_dec_ref(v___y_2301_);
lean_dec(v___y_2300_);
lean_dec_ref(v___y_2299_);
lean_dec(v___y_2298_);
lean_dec_ref(v___y_2297_);
lean_dec(v___y_2296_);
lean_dec_ref(v___y_2295_);
lean_dec(v_fst_2294_);
lean_dec(v___y_2293_);
lean_dec_ref(v_snd_2292_);
v_a_2322_ = lean_ctor_get(v___x_2306_, 0);
v_isSharedCheck_2329_ = !lean_is_exclusive(v___x_2306_);
if (v_isSharedCheck_2329_ == 0)
{
v___x_2324_ = v___x_2306_;
v_isShared_2325_ = v_isSharedCheck_2329_;
goto v_resetjp_2323_;
}
else
{
lean_inc(v_a_2322_);
lean_dec(v___x_2306_);
v___x_2324_ = lean_box(0);
v_isShared_2325_ = v_isSharedCheck_2329_;
goto v_resetjp_2323_;
}
v_resetjp_2323_:
{
lean_object* v___x_2327_; 
if (v_isShared_2325_ == 0)
{
v___x_2327_ = v___x_2324_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2328_; 
v_reuseFailAlloc_2328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2328_, 0, v_a_2322_);
v___x_2327_ = v_reuseFailAlloc_2328_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
return v___x_2327_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__1___boxed(lean_object* v___x_2330_, lean_object* v_snd_2331_, lean_object* v___y_2332_, lean_object* v_fst_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_){
_start:
{
lean_object* v_res_2343_; 
v_res_2343_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__1(v___x_2330_, v_snd_2331_, v___y_2332_, v_fst_2333_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_);
return v_res_2343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__3(lean_object* v___x_2344_, lean_object* v_val_2345_, lean_object* v_h_2346_, lean_object* v_a_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_){
_start:
{
lean_object* v___x_2357_; lean_object* v___f_2358_; lean_object* v___x_2359_; 
v___x_2357_ = lean_st_mk_ref(v___x_2344_);
lean_inc(v___x_2357_);
v___f_2358_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__0___boxed), 11, 1);
lean_closure_set(v___f_2358_, 0, v___x_2357_);
lean_inc(v___y_2355_);
lean_inc_ref(v___y_2354_);
lean_inc(v___y_2353_);
lean_inc_ref(v___y_2352_);
lean_inc(v___y_2349_);
v___x_2359_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevert___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__4(v_val_2345_, v_h_2346_, v___f_2358_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_, v___y_2354_, v___y_2355_);
if (lean_obj_tag(v___x_2359_) == 0)
{
lean_object* v_a_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; 
v_a_2360_ = lean_ctor_get(v___x_2359_, 0);
lean_inc(v_a_2360_);
lean_dec_ref(v___x_2359_);
v___x_2361_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2___redArg(v_a_2347_, v_a_2360_, v___y_2353_);
lean_dec_ref(v___x_2361_);
v___x_2362_ = lean_st_ref_get(v___x_2357_);
lean_dec(v___x_2357_);
v___x_2363_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2362_, v___y_2349_, v___y_2352_, v___y_2353_, v___y_2354_, v___y_2355_);
lean_dec(v___y_2355_);
lean_dec_ref(v___y_2354_);
lean_dec(v___y_2353_);
lean_dec_ref(v___y_2352_);
lean_dec(v___y_2349_);
return v___x_2363_;
}
else
{
lean_object* v_a_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2371_; 
lean_dec(v___x_2357_);
lean_dec(v___y_2355_);
lean_dec_ref(v___y_2354_);
lean_dec(v___y_2353_);
lean_dec_ref(v___y_2352_);
lean_dec(v___y_2349_);
lean_dec(v_a_2347_);
v_a_2364_ = lean_ctor_get(v___x_2359_, 0);
v_isSharedCheck_2371_ = !lean_is_exclusive(v___x_2359_);
if (v_isSharedCheck_2371_ == 0)
{
v___x_2366_ = v___x_2359_;
v_isShared_2367_ = v_isSharedCheck_2371_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_a_2364_);
lean_dec(v___x_2359_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2371_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
lean_object* v___x_2369_; 
if (v_isShared_2367_ == 0)
{
v___x_2369_ = v___x_2366_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v_a_2364_);
v___x_2369_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
return v___x_2369_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__3___boxed(lean_object* v___x_2372_, lean_object* v_val_2373_, lean_object* v_h_2374_, lean_object* v_a_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_){
_start:
{
lean_object* v_res_2385_; 
v_res_2385_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__3(v___x_2372_, v_val_2373_, v_h_2374_, v_a_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_);
return v_res_2385_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5___redArg(lean_object* v_msg_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_){
_start:
{
lean_object* v_ref_2392_; lean_object* v___x_2393_; lean_object* v_a_2394_; lean_object* v___x_2396_; uint8_t v_isShared_2397_; uint8_t v_isSharedCheck_2402_; 
v_ref_2392_ = lean_ctor_get(v___y_2389_, 5);
v___x_2393_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5_spec__14(v_msg_2386_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_);
v_a_2394_ = lean_ctor_get(v___x_2393_, 0);
v_isSharedCheck_2402_ = !lean_is_exclusive(v___x_2393_);
if (v_isSharedCheck_2402_ == 0)
{
v___x_2396_ = v___x_2393_;
v_isShared_2397_ = v_isSharedCheck_2402_;
goto v_resetjp_2395_;
}
else
{
lean_inc(v_a_2394_);
lean_dec(v___x_2393_);
v___x_2396_ = lean_box(0);
v_isShared_2397_ = v_isSharedCheck_2402_;
goto v_resetjp_2395_;
}
v_resetjp_2395_:
{
lean_object* v___x_2398_; lean_object* v___x_2400_; 
lean_inc(v_ref_2392_);
v___x_2398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2398_, 0, v_ref_2392_);
lean_ctor_set(v___x_2398_, 1, v_a_2394_);
if (v_isShared_2397_ == 0)
{
lean_ctor_set_tag(v___x_2396_, 1);
lean_ctor_set(v___x_2396_, 0, v___x_2398_);
v___x_2400_ = v___x_2396_;
goto v_reusejp_2399_;
}
else
{
lean_object* v_reuseFailAlloc_2401_; 
v_reuseFailAlloc_2401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2401_, 0, v___x_2398_);
v___x_2400_ = v_reuseFailAlloc_2401_;
goto v_reusejp_2399_;
}
v_reusejp_2399_:
{
return v___x_2400_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5___redArg___boxed(lean_object* v_msg_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_){
_start:
{
lean_object* v_res_2409_; 
v_res_2409_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5___redArg(v_msg_2403_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_);
lean_dec(v___y_2407_);
lean_dec_ref(v___y_2406_);
lean_dec(v___y_2405_);
lean_dec_ref(v___y_2404_);
return v_res_2409_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__11(void){
_start:
{
lean_object* v___x_2434_; lean_object* v___x_2435_; 
v___x_2434_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__10));
v___x_2435_ = l_Lean_stringToMessageData(v___x_2434_);
return v___x_2435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert(lean_object* v_x_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_){
_start:
{
lean_object* v___y_2447_; lean_object* v___y_2448_; lean_object* v___y_2449_; lean_object* v___y_2450_; lean_object* v___y_2451_; lean_object* v___y_2452_; lean_object* v___y_2453_; lean_object* v___y_2454_; lean_object* v___y_2455_; lean_object* v___y_2456_; lean_object* v___y_2457_; lean_object* v___x_2461_; uint8_t v___x_2462_; 
v___x_2461_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__3));
lean_inc(v_x_2436_);
v___x_2462_ = l_Lean_Syntax_isOfKind(v_x_2436_, v___x_2461_);
if (v___x_2462_ == 0)
{
lean_object* v___x_2463_; 
lean_dec(v_a_2444_);
lean_dec_ref(v_a_2443_);
lean_dec(v_a_2442_);
lean_dec_ref(v_a_2441_);
lean_dec(v_a_2440_);
lean_dec_ref(v_a_2439_);
lean_dec(v_a_2438_);
lean_dec_ref(v_a_2437_);
lean_dec(v_x_2436_);
v___x_2463_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg();
return v___x_2463_;
}
else
{
lean_object* v___x_2464_; lean_object* v_n_2466_; lean_object* v___y_2467_; lean_object* v___y_2468_; lean_object* v___y_2469_; lean_object* v___y_2470_; lean_object* v___y_2471_; lean_object* v___y_2472_; lean_object* v___y_2473_; lean_object* v___y_2474_; lean_object* v___x_2491_; uint8_t v___x_2492_; 
v___x_2464_ = lean_unsigned_to_nat(1u);
v___x_2491_ = l_Lean_Syntax_getArg(v_x_2436_, v___x_2464_);
lean_dec(v_x_2436_);
lean_inc(v___x_2491_);
v___x_2492_ = l_Lean_Syntax_matchesNull(v___x_2491_, v___x_2464_);
if (v___x_2492_ == 0)
{
lean_object* v___x_2493_; 
lean_dec(v___x_2491_);
lean_dec(v_a_2444_);
lean_dec_ref(v_a_2443_);
lean_dec(v_a_2442_);
lean_dec_ref(v_a_2441_);
lean_dec(v_a_2440_);
lean_dec_ref(v_a_2439_);
lean_dec(v_a_2438_);
lean_dec_ref(v_a_2437_);
v___x_2493_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg();
return v___x_2493_;
}
else
{
lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; uint8_t v___x_2497_; 
v___x_2494_ = lean_unsigned_to_nat(0u);
v___x_2495_ = l_Lean_Syntax_getArg(v___x_2491_, v___x_2494_);
lean_dec(v___x_2491_);
v___x_2496_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__5));
lean_inc(v___x_2495_);
v___x_2497_ = l_Lean_Syntax_isOfKind(v___x_2495_, v___x_2496_);
if (v___x_2497_ == 0)
{
lean_object* v___x_2498_; uint8_t v___x_2499_; 
v___x_2498_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__7));
lean_inc(v___x_2495_);
v___x_2499_ = l_Lean_Syntax_isOfKind(v___x_2495_, v___x_2498_);
if (v___x_2499_ == 0)
{
lean_object* v___x_2500_; 
lean_dec(v___x_2495_);
lean_dec(v_a_2444_);
lean_dec_ref(v_a_2443_);
lean_dec(v_a_2442_);
lean_dec_ref(v_a_2441_);
lean_dec(v_a_2440_);
lean_dec_ref(v_a_2439_);
lean_dec(v_a_2438_);
lean_dec_ref(v_a_2437_);
v___x_2500_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg();
return v___x_2500_;
}
else
{
lean_object* v___x_2501_; uint8_t v___x_2502_; 
v___x_2501_ = l_Lean_Syntax_getArg(v___x_2495_, v___x_2464_);
lean_dec(v___x_2495_);
v___x_2502_ = l_Lean_Syntax_isNone(v___x_2501_);
if (v___x_2502_ == 0)
{
uint8_t v___x_2503_; 
lean_inc(v___x_2501_);
v___x_2503_ = l_Lean_Syntax_matchesNull(v___x_2501_, v___x_2464_);
if (v___x_2503_ == 0)
{
lean_object* v___x_2504_; 
lean_dec(v___x_2501_);
lean_dec(v_a_2444_);
lean_dec_ref(v_a_2443_);
lean_dec(v_a_2442_);
lean_dec_ref(v_a_2441_);
lean_dec(v_a_2440_);
lean_dec_ref(v_a_2439_);
lean_dec(v_a_2438_);
lean_dec_ref(v_a_2437_);
v___x_2504_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg();
return v___x_2504_;
}
else
{
lean_object* v_n_2505_; lean_object* v___x_2506_; 
v_n_2505_ = l_Lean_Syntax_getArg(v___x_2501_, v___x_2494_);
lean_dec(v___x_2501_);
v___x_2506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2506_, 0, v_n_2505_);
v_n_2466_ = v___x_2506_;
v___y_2467_ = v_a_2437_;
v___y_2468_ = v_a_2438_;
v___y_2469_ = v_a_2439_;
v___y_2470_ = v_a_2440_;
v___y_2471_ = v_a_2441_;
v___y_2472_ = v_a_2442_;
v___y_2473_ = v_a_2443_;
v___y_2474_ = v_a_2444_;
goto v___jp_2465_;
}
}
else
{
lean_object* v___x_2507_; 
lean_dec(v___x_2501_);
v___x_2507_ = lean_box(0);
v_n_2466_ = v___x_2507_;
v___y_2467_ = v_a_2437_;
v___y_2468_ = v_a_2438_;
v___y_2469_ = v_a_2439_;
v___y_2470_ = v_a_2440_;
v___y_2471_ = v_a_2441_;
v___y_2472_ = v_a_2442_;
v___y_2473_ = v_a_2443_;
v___y_2474_ = v_a_2444_;
goto v___jp_2465_;
}
}
}
else
{
lean_object* v_h_2508_; lean_object* v___x_2509_; uint8_t v___x_2510_; 
v_h_2508_ = l_Lean_Syntax_getArg(v___x_2495_, v___x_2494_);
lean_dec(v___x_2495_);
v___x_2509_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__9));
lean_inc(v_h_2508_);
v___x_2510_ = l_Lean_Syntax_isOfKind(v_h_2508_, v___x_2509_);
if (v___x_2510_ == 0)
{
lean_object* v___x_2511_; 
lean_dec(v_h_2508_);
lean_dec(v_a_2444_);
lean_dec_ref(v_a_2443_);
lean_dec(v_a_2442_);
lean_dec_ref(v_a_2441_);
lean_dec(v_a_2440_);
lean_dec_ref(v_a_2439_);
lean_dec(v_a_2438_);
lean_dec_ref(v_a_2437_);
v___x_2511_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg();
return v___x_2511_;
}
else
{
lean_object* v___x_2512_; 
v___x_2512_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_2438_, v_a_2441_, v_a_2442_, v_a_2443_, v_a_2444_);
if (lean_obj_tag(v___x_2512_) == 0)
{
lean_object* v_a_2513_; lean_object* v___x_2514_; 
v_a_2513_ = lean_ctor_get(v___x_2512_, 0);
lean_inc(v_a_2513_);
lean_dec_ref(v___x_2512_);
lean_inc(v_a_2513_);
v___x_2514_ = l_Lean_MVarId_getType(v_a_2513_, v_a_2441_, v_a_2442_, v_a_2443_, v_a_2444_);
if (lean_obj_tag(v___x_2514_) == 0)
{
lean_object* v_a_2515_; lean_object* v___x_2516_; 
v_a_2515_ = lean_ctor_get(v___x_2514_, 0);
lean_inc(v_a_2515_);
lean_dec_ref(v___x_2514_);
v___x_2516_ = l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f(v_a_2515_);
lean_dec(v_a_2515_);
if (lean_obj_tag(v___x_2516_) == 1)
{
lean_object* v_val_2517_; lean_object* v___x_2518_; lean_object* v___f_2519_; lean_object* v___x_2520_; 
v_val_2517_ = lean_ctor_get(v___x_2516_, 0);
lean_inc(v_val_2517_);
lean_dec_ref(v___x_2516_);
v___x_2518_ = lean_box(0);
lean_inc(v_a_2513_);
v___f_2519_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__3___boxed), 13, 4);
lean_closure_set(v___f_2519_, 0, v___x_2518_);
lean_closure_set(v___f_2519_, 1, v_val_2517_);
lean_closure_set(v___f_2519_, 2, v_h_2508_);
lean_closure_set(v___f_2519_, 3, v_a_2513_);
v___x_2520_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___redArg(v_a_2513_, v___f_2519_, v_a_2437_, v_a_2438_, v_a_2439_, v_a_2440_, v_a_2441_, v_a_2442_, v_a_2443_, v_a_2444_);
return v___x_2520_;
}
else
{
lean_object* v___x_2521_; lean_object* v___x_2522_; 
lean_dec(v___x_2516_);
lean_dec(v_a_2513_);
lean_dec(v_h_2508_);
lean_dec(v_a_2440_);
lean_dec_ref(v_a_2439_);
lean_dec(v_a_2438_);
lean_dec_ref(v_a_2437_);
v___x_2521_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__11, &l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__11_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__11);
v___x_2522_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5___redArg(v___x_2521_, v_a_2441_, v_a_2442_, v_a_2443_, v_a_2444_);
lean_dec(v_a_2444_);
lean_dec_ref(v_a_2443_);
lean_dec(v_a_2442_);
lean_dec_ref(v_a_2441_);
return v___x_2522_;
}
}
else
{
lean_object* v_a_2523_; lean_object* v___x_2525_; uint8_t v_isShared_2526_; uint8_t v_isSharedCheck_2530_; 
lean_dec(v_a_2513_);
lean_dec(v_h_2508_);
lean_dec(v_a_2444_);
lean_dec_ref(v_a_2443_);
lean_dec(v_a_2442_);
lean_dec_ref(v_a_2441_);
lean_dec(v_a_2440_);
lean_dec_ref(v_a_2439_);
lean_dec(v_a_2438_);
lean_dec_ref(v_a_2437_);
v_a_2523_ = lean_ctor_get(v___x_2514_, 0);
v_isSharedCheck_2530_ = !lean_is_exclusive(v___x_2514_);
if (v_isSharedCheck_2530_ == 0)
{
v___x_2525_ = v___x_2514_;
v_isShared_2526_ = v_isSharedCheck_2530_;
goto v_resetjp_2524_;
}
else
{
lean_inc(v_a_2523_);
lean_dec(v___x_2514_);
v___x_2525_ = lean_box(0);
v_isShared_2526_ = v_isSharedCheck_2530_;
goto v_resetjp_2524_;
}
v_resetjp_2524_:
{
lean_object* v___x_2528_; 
if (v_isShared_2526_ == 0)
{
v___x_2528_ = v___x_2525_;
goto v_reusejp_2527_;
}
else
{
lean_object* v_reuseFailAlloc_2529_; 
v_reuseFailAlloc_2529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2529_, 0, v_a_2523_);
v___x_2528_ = v_reuseFailAlloc_2529_;
goto v_reusejp_2527_;
}
v_reusejp_2527_:
{
return v___x_2528_;
}
}
}
}
else
{
lean_object* v_a_2531_; lean_object* v___x_2533_; uint8_t v_isShared_2534_; uint8_t v_isSharedCheck_2538_; 
lean_dec(v_h_2508_);
lean_dec(v_a_2444_);
lean_dec_ref(v_a_2443_);
lean_dec(v_a_2442_);
lean_dec_ref(v_a_2441_);
lean_dec(v_a_2440_);
lean_dec_ref(v_a_2439_);
lean_dec(v_a_2438_);
lean_dec_ref(v_a_2437_);
v_a_2531_ = lean_ctor_get(v___x_2512_, 0);
v_isSharedCheck_2538_ = !lean_is_exclusive(v___x_2512_);
if (v_isSharedCheck_2538_ == 0)
{
v___x_2533_ = v___x_2512_;
v_isShared_2534_ = v_isSharedCheck_2538_;
goto v_resetjp_2532_;
}
else
{
lean_inc(v_a_2531_);
lean_dec(v___x_2512_);
v___x_2533_ = lean_box(0);
v_isShared_2534_ = v_isSharedCheck_2538_;
goto v_resetjp_2532_;
}
v_resetjp_2532_:
{
lean_object* v___x_2536_; 
if (v_isShared_2534_ == 0)
{
v___x_2536_ = v___x_2533_;
goto v_reusejp_2535_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v_a_2531_);
v___x_2536_ = v_reuseFailAlloc_2537_;
goto v_reusejp_2535_;
}
v_reusejp_2535_:
{
return v___x_2536_;
}
}
}
}
}
}
v___jp_2465_:
{
lean_object* v___x_2475_; 
lean_inc(v___y_2474_);
lean_inc_ref(v___y_2473_);
lean_inc(v___y_2472_);
lean_inc_ref(v___y_2471_);
v___x_2475_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg(v___y_2468_, v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_);
if (lean_obj_tag(v___x_2475_) == 0)
{
lean_object* v_a_2476_; 
v_a_2476_ = lean_ctor_get(v___x_2475_, 0);
lean_inc(v_a_2476_);
lean_dec_ref(v___x_2475_);
if (lean_obj_tag(v_n_2466_) == 0)
{
lean_object* v_fst_2477_; lean_object* v_snd_2478_; 
v_fst_2477_ = lean_ctor_get(v_a_2476_, 0);
lean_inc(v_fst_2477_);
v_snd_2478_ = lean_ctor_get(v_a_2476_, 1);
lean_inc(v_snd_2478_);
lean_dec(v_a_2476_);
v___y_2447_ = v_snd_2478_;
v___y_2448_ = v_fst_2477_;
v___y_2449_ = v___y_2471_;
v___y_2450_ = v___y_2467_;
v___y_2451_ = v___y_2474_;
v___y_2452_ = v___y_2473_;
v___y_2453_ = v___y_2469_;
v___y_2454_ = v___y_2468_;
v___y_2455_ = v___y_2470_;
v___y_2456_ = v___y_2472_;
v___y_2457_ = v___x_2464_;
goto v___jp_2446_;
}
else
{
lean_object* v_fst_2479_; lean_object* v_snd_2480_; lean_object* v_val_2481_; lean_object* v___x_2482_; 
v_fst_2479_ = lean_ctor_get(v_a_2476_, 0);
lean_inc(v_fst_2479_);
v_snd_2480_ = lean_ctor_get(v_a_2476_, 1);
lean_inc(v_snd_2480_);
lean_dec(v_a_2476_);
v_val_2481_ = lean_ctor_get(v_n_2466_, 0);
lean_inc(v_val_2481_);
lean_dec_ref(v_n_2466_);
v___x_2482_ = l_Lean_TSyntax_getNat(v_val_2481_);
lean_dec(v_val_2481_);
v___y_2447_ = v_snd_2480_;
v___y_2448_ = v_fst_2479_;
v___y_2449_ = v___y_2471_;
v___y_2450_ = v___y_2467_;
v___y_2451_ = v___y_2474_;
v___y_2452_ = v___y_2473_;
v___y_2453_ = v___y_2469_;
v___y_2454_ = v___y_2468_;
v___y_2455_ = v___y_2470_;
v___y_2456_ = v___y_2472_;
v___y_2457_ = v___x_2482_;
goto v___jp_2446_;
}
}
else
{
lean_object* v_a_2483_; lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_2490_; 
lean_dec(v___y_2474_);
lean_dec_ref(v___y_2473_);
lean_dec(v___y_2472_);
lean_dec_ref(v___y_2471_);
lean_dec(v___y_2470_);
lean_dec_ref(v___y_2469_);
lean_dec(v___y_2468_);
lean_dec_ref(v___y_2467_);
lean_dec(v_n_2466_);
v_a_2483_ = lean_ctor_get(v___x_2475_, 0);
v_isSharedCheck_2490_ = !lean_is_exclusive(v___x_2475_);
if (v_isSharedCheck_2490_ == 0)
{
v___x_2485_ = v___x_2475_;
v_isShared_2486_ = v_isSharedCheck_2490_;
goto v_resetjp_2484_;
}
else
{
lean_inc(v_a_2483_);
lean_dec(v___x_2475_);
v___x_2485_ = lean_box(0);
v_isShared_2486_ = v_isSharedCheck_2490_;
goto v_resetjp_2484_;
}
v_resetjp_2484_:
{
lean_object* v___x_2488_; 
if (v_isShared_2486_ == 0)
{
v___x_2488_ = v___x_2485_;
goto v_reusejp_2487_;
}
else
{
lean_object* v_reuseFailAlloc_2489_; 
v_reuseFailAlloc_2489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v_a_2483_);
v___x_2488_ = v_reuseFailAlloc_2489_;
goto v_reusejp_2487_;
}
v_reusejp_2487_:
{
return v___x_2488_;
}
}
}
}
}
v___jp_2446_:
{
lean_object* v___x_2458_; lean_object* v___f_2459_; lean_object* v___x_2460_; 
v___x_2458_ = lean_box(0);
lean_inc(v___y_2448_);
v___f_2459_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__1___boxed), 13, 4);
lean_closure_set(v___f_2459_, 0, v___x_2458_);
lean_closure_set(v___f_2459_, 1, v___y_2447_);
lean_closure_set(v___f_2459_, 2, v___y_2457_);
lean_closure_set(v___f_2459_, 3, v___y_2448_);
v___x_2460_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___redArg(v___y_2448_, v___f_2459_, v___y_2450_, v___y_2454_, v___y_2453_, v___y_2455_, v___y_2449_, v___y_2456_, v___y_2452_, v___y_2451_);
return v___x_2460_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___boxed(lean_object* v_x_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_){
_start:
{
lean_object* v_res_2549_; 
v_res_2549_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert(v_x_2539_, v_a_2540_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_);
return v_res_2549_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2(lean_object* v_mvarId_2550_, lean_object* v_val_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_){
_start:
{
lean_object* v___x_2561_; 
v___x_2561_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2___redArg(v_mvarId_2550_, v_val_2551_, v___y_2557_);
return v___x_2561_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2___boxed(lean_object* v_mvarId_2562_, lean_object* v_val_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_){
_start:
{
lean_object* v_res_2573_; 
v_res_2573_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2(v_mvarId_2562_, v_val_2563_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_);
lean_dec(v___y_2571_);
lean_dec_ref(v___y_2570_);
lean_dec(v___y_2569_);
lean_dec_ref(v___y_2568_);
lean_dec(v___y_2567_);
lean_dec_ref(v___y_2566_);
lean_dec(v___y_2565_);
lean_dec_ref(v___y_2564_);
return v_res_2573_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5(lean_object* v_00_u03b1_2574_, lean_object* v_msg_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_){
_start:
{
lean_object* v___x_2585_; 
v___x_2585_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5___redArg(v_msg_2575_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_);
return v___x_2585_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5___boxed(lean_object* v_00_u03b1_2586_, lean_object* v_msg_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_){
_start:
{
lean_object* v_res_2597_; 
v_res_2597_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5(v_00_u03b1_2586_, v_msg_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_);
lean_dec(v___y_2595_);
lean_dec_ref(v___y_2594_);
lean_dec(v___y_2593_);
lean_dec_ref(v___y_2592_);
lean_dec(v___y_2591_);
lean_dec_ref(v___y_2590_);
lean_dec(v___y_2589_);
lean_dec_ref(v___y_2588_);
return v_res_2597_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__1(lean_object* v_inst_2598_, lean_object* v_R_2599_, lean_object* v_a_2600_, lean_object* v_b_2601_){
_start:
{
lean_object* v___x_2602_; 
v___x_2602_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__1___redArg(v_a_2600_, v_b_2601_);
return v___x_2602_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__2(size_t v_sz_2603_, size_t v_i_2604_, lean_object* v_bs_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_){
_start:
{
lean_object* v___x_2615_; 
v___x_2615_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__2___redArg(v_sz_2603_, v_i_2604_, v_bs_2605_, v___y_2610_, v___y_2611_, v___y_2612_, v___y_2613_);
return v___x_2615_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__2___boxed(lean_object* v_sz_2616_, lean_object* v_i_2617_, lean_object* v_bs_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_){
_start:
{
size_t v_sz_boxed_2628_; size_t v_i_boxed_2629_; lean_object* v_res_2630_; 
v_sz_boxed_2628_ = lean_unbox_usize(v_sz_2616_);
lean_dec(v_sz_2616_);
v_i_boxed_2629_ = lean_unbox_usize(v_i_2617_);
lean_dec(v_i_2617_);
v_res_2630_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__2(v_sz_boxed_2628_, v_i_boxed_2629_, v_bs_2618_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_);
lean_dec(v___y_2622_);
lean_dec_ref(v___y_2621_);
lean_dec(v___y_2620_);
lean_dec_ref(v___y_2619_);
return v_res_2630_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__4(lean_object* v_as_2631_, lean_object* v_i_2632_, lean_object* v_j_2633_, lean_object* v_inv_2634_, lean_object* v_bs_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_){
_start:
{
lean_object* v___x_2645_; 
v___x_2645_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__4___redArg(v_as_2631_, v_i_2632_, v_j_2633_, v_bs_2635_, v___y_2642_, v___y_2643_);
return v___x_2645_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__4___boxed(lean_object* v_as_2646_, lean_object* v_i_2647_, lean_object* v_j_2648_, lean_object* v_inv_2649_, lean_object* v_bs_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_){
_start:
{
lean_object* v_res_2660_; 
v_res_2660_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__4(v_as_2646_, v_i_2647_, v_j_2648_, v_inv_2649_, v_bs_2650_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_, v___y_2658_);
lean_dec(v___y_2656_);
lean_dec_ref(v___y_2655_);
lean_dec(v___y_2654_);
lean_dec_ref(v___y_2653_);
lean_dec(v___y_2652_);
lean_dec_ref(v___y_2651_);
lean_dec_ref(v_as_2646_);
return v_res_2660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5(lean_object* v_00_u03b1_2661_, lean_object* v_inst_2662_, lean_object* v_declInfos_2663_, lean_object* v_k_2664_, uint8_t v_kind_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_){
_start:
{
lean_object* v___x_2675_; 
v___x_2675_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5___redArg(v_inst_2662_, v_declInfos_2663_, v_k_2664_, v_kind_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_, v___y_2673_);
return v___x_2675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5___boxed(lean_object* v_00_u03b1_2676_, lean_object* v_inst_2677_, lean_object* v_declInfos_2678_, lean_object* v_k_2679_, lean_object* v_kind_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_){
_start:
{
uint8_t v_kind_boxed_2690_; lean_object* v_res_2691_; 
v_kind_boxed_2690_ = lean_unbox(v_kind_2680_);
v_res_2691_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5(v_00_u03b1_2676_, v_inst_2677_, v_declInfos_2678_, v_k_2679_, v_kind_boxed_2690_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_);
lean_dec(v_inst_2677_);
return v_res_2691_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__8(lean_object* v_00_u03b1_2692_, lean_object* v_msg_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_){
_start:
{
lean_object* v___x_2699_; 
v___x_2699_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__8___redArg(v_msg_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_);
return v___x_2699_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__8___boxed(lean_object* v_00_u03b1_2700_, lean_object* v_msg_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_){
_start:
{
lean_object* v_res_2707_; 
v_res_2707_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__8(v_00_u03b1_2700_, v_msg_2701_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_);
lean_dec(v___y_2705_);
lean_dec_ref(v___y_2704_);
lean_dec(v___y_2703_);
lean_dec_ref(v___y_2702_);
return v_res_2707_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10(lean_object* v_00_u03b2_2708_, lean_object* v_x_2709_, lean_object* v_x_2710_, lean_object* v_x_2711_){
_start:
{
lean_object* v___x_2712_; 
v___x_2712_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10___redArg(v_x_2709_, v_x_2710_, v_x_2711_);
return v___x_2712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9(lean_object* v_00_u03b1_2713_, lean_object* v_inst_2714_, lean_object* v_declInfos_2715_, lean_object* v_k_2716_, uint8_t v_kind_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_){
_start:
{
lean_object* v___x_2727_; 
v___x_2727_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9___redArg(v_inst_2714_, v_declInfos_2715_, v_k_2716_, v_kind_2717_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_);
return v___x_2727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9___boxed(lean_object* v_00_u03b1_2728_, lean_object* v_inst_2729_, lean_object* v_declInfos_2730_, lean_object* v_k_2731_, lean_object* v_kind_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_){
_start:
{
uint8_t v_kind_boxed_2742_; lean_object* v_res_2743_; 
v_kind_boxed_2742_ = lean_unbox(v_kind_2732_);
v_res_2743_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9(v_00_u03b1_2728_, v_inst_2729_, v_declInfos_2730_, v_k_2731_, v_kind_boxed_2742_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_);
lean_dec(v_inst_2729_);
return v_res_2743_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15(lean_object* v_00_u03b2_2744_, lean_object* v_x_2745_, size_t v_x_2746_, size_t v_x_2747_, lean_object* v_x_2748_, lean_object* v_x_2749_){
_start:
{
lean_object* v___x_2750_; 
v___x_2750_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15___redArg(v_x_2745_, v_x_2746_, v_x_2747_, v_x_2748_, v_x_2749_);
return v___x_2750_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15___boxed(lean_object* v_00_u03b2_2751_, lean_object* v_x_2752_, lean_object* v_x_2753_, lean_object* v_x_2754_, lean_object* v_x_2755_, lean_object* v_x_2756_){
_start:
{
size_t v_x_22894__boxed_2757_; size_t v_x_22895__boxed_2758_; lean_object* v_res_2759_; 
v_x_22894__boxed_2757_ = lean_unbox_usize(v_x_2753_);
lean_dec(v_x_2753_);
v_x_22895__boxed_2758_ = lean_unbox_usize(v_x_2754_);
lean_dec(v_x_2754_);
v_res_2759_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15(v_00_u03b2_2751_, v_x_2752_, v_x_22894__boxed_2757_, v_x_22895__boxed_2758_, v_x_2755_, v_x_2756_);
return v_res_2759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14(lean_object* v_00_u03b1_2760_, lean_object* v_inst_2761_, lean_object* v_declInfos_2762_, lean_object* v_k_2763_, uint8_t v_kind_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_){
_start:
{
lean_object* v___x_2774_; 
v___x_2774_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14___redArg(v_inst_2761_, v_declInfos_2762_, v_k_2763_, v_kind_2764_, v___y_2765_, v___y_2766_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_);
return v___x_2774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14___boxed(lean_object* v_00_u03b1_2775_, lean_object* v_inst_2776_, lean_object* v_declInfos_2777_, lean_object* v_k_2778_, lean_object* v_kind_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_){
_start:
{
uint8_t v_kind_boxed_2789_; lean_object* v_res_2790_; 
v_kind_boxed_2789_ = lean_unbox(v_kind_2779_);
v_res_2790_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14(v_00_u03b1_2775_, v_inst_2776_, v_declInfos_2777_, v_k_2778_, v_kind_boxed_2789_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_);
lean_dec(v_inst_2776_);
return v_res_2790_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15_spec__20(lean_object* v_00_u03b2_2791_, lean_object* v_n_2792_, lean_object* v_k_2793_, lean_object* v_v_2794_){
_start:
{
lean_object* v___x_2795_; 
v___x_2795_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15_spec__20___redArg(v_n_2792_, v_k_2793_, v_v_2794_);
return v___x_2795_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15_spec__21(lean_object* v_00_u03b2_2796_, size_t v_depth_2797_, lean_object* v_keys_2798_, lean_object* v_vals_2799_, lean_object* v_heq_2800_, lean_object* v_i_2801_, lean_object* v_entries_2802_){
_start:
{
lean_object* v___x_2803_; 
v___x_2803_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15_spec__21___redArg(v_depth_2797_, v_keys_2798_, v_vals_2799_, v_i_2801_, v_entries_2802_);
return v___x_2803_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15_spec__21___boxed(lean_object* v_00_u03b2_2804_, lean_object* v_depth_2805_, lean_object* v_keys_2806_, lean_object* v_vals_2807_, lean_object* v_heq_2808_, lean_object* v_i_2809_, lean_object* v_entries_2810_){
_start:
{
size_t v_depth_boxed_2811_; lean_object* v_res_2812_; 
v_depth_boxed_2811_ = lean_unbox_usize(v_depth_2805_);
lean_dec(v_depth_2805_);
v_res_2812_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15_spec__21(v_00_u03b2_2804_, v_depth_boxed_2811_, v_keys_2806_, v_vals_2807_, v_heq_2808_, v_i_2809_, v_entries_2810_);
lean_dec_ref(v_vals_2807_);
lean_dec_ref(v_keys_2806_);
return v_res_2812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19_spec__21(lean_object* v_00_u03b1_2813_, lean_object* v_name_2814_, uint8_t v_bi_2815_, lean_object* v_type_2816_, lean_object* v_k_2817_, uint8_t v_kind_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_){
_start:
{
lean_object* v___x_2828_; 
v___x_2828_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19_spec__21___redArg(v_name_2814_, v_bi_2815_, v_type_2816_, v_k_2817_, v_kind_2818_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_);
return v___x_2828_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19_spec__21___boxed(lean_object* v_00_u03b1_2829_, lean_object* v_name_2830_, lean_object* v_bi_2831_, lean_object* v_type_2832_, lean_object* v_k_2833_, lean_object* v_kind_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_){
_start:
{
uint8_t v_bi_boxed_2844_; uint8_t v_kind_boxed_2845_; lean_object* v_res_2846_; 
v_bi_boxed_2844_ = lean_unbox(v_bi_2831_);
v_kind_boxed_2845_ = lean_unbox(v_kind_2834_);
v_res_2846_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19_spec__21(v_00_u03b1_2829_, v_name_2830_, v_bi_boxed_2844_, v_type_2832_, v_k_2833_, v_kind_boxed_2845_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_);
return v_res_2846_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19(lean_object* v_00_u03b1_2847_, lean_object* v_declInfos_2848_, lean_object* v_k_2849_, uint8_t v_kind_2850_, lean_object* v_inst_2851_, lean_object* v_acc_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_){
_start:
{
lean_object* v___x_2862_; 
v___x_2862_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___redArg(v_declInfos_2848_, v_k_2849_, v_kind_2850_, v_acc_2852_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_);
return v___x_2862_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___boxed(lean_object* v_00_u03b1_2863_, lean_object* v_declInfos_2864_, lean_object* v_k_2865_, lean_object* v_kind_2866_, lean_object* v_inst_2867_, lean_object* v_acc_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_){
_start:
{
uint8_t v_kind_boxed_2878_; lean_object* v_res_2879_; 
v_kind_boxed_2878_ = lean_unbox(v_kind_2866_);
v_res_2879_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19(v_00_u03b1_2863_, v_declInfos_2864_, v_k_2865_, v_kind_boxed_2878_, v_inst_2867_, v_acc_2868_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_);
lean_dec(v_inst_2867_);
return v_res_2879_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15_spec__20_spec__22(lean_object* v_00_u03b2_2880_, lean_object* v_x_2881_, lean_object* v_x_2882_, lean_object* v_x_2883_, lean_object* v_x_2884_){
_start:
{
lean_object* v___x_2885_; 
v___x_2885_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15_spec__20_spec__22___redArg(v_x_2881_, v_x_2882_, v_x_2883_, v_x_2884_);
return v___x_2885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1(){
_start:
{
lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; 
v___x_2897_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2898_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__3));
v___x_2899_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__3));
v___x_2900_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___boxed), 10, 0);
v___x_2901_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2897_, v___x_2898_, v___x_2899_, v___x_2900_);
return v___x_2901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___boxed(lean_object* v_a_2902_){
_start:
{
lean_object* v_res_2903_; 
v_res_2903_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1();
return v_res_2903_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Revert(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Do_ProofMode_Revert(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Do_ProofMode_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Do_ProofMode_Revert(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Do_ProofMode_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Revert(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Do_ProofMode_Revert(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Do_ProofMode_Revert(builtin);
}
#ifdef __cplusplus
}
#endif
