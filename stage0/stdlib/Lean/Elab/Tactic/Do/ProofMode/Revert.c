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
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_mkApp8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l_Lean_mkAppRev(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_mkAndN(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instMonadExceptOfExceptionCoreM;
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_consumeMData(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_zip___redArg(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
lean_object* l_instMonadEIO___redArg();
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instMonadTermElabM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instMonadTermElabM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_instMonadTacticM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_instMonadTacticM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_Pi_instInhabited___redArg___lam__0(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAndIntroN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkCons(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadFunctor___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Meta_withLocalDeclsDND___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Core_instMonadQuotationCoreM;
lean_object* l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadLift___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadFunctor___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instAddMessageContextMetaM;
lean_object* l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(lean_object*, lean_object*);
lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAndIntroN___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
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
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "impossible; res.focusHyp not a hypothesis"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__5_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__0;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__1;
static const lean_closure_object l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__2_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__3_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__4_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__5_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__6;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__7;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__8;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__9;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__10;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__11;
static const lean_closure_object l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadFunctor___redArg___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__12 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__12_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__13 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__13_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_instMonadFunctor___aux__1___boxed, .m_arity = 7, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__14 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__14_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__15 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__15_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__16;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__17;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "s"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__5___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__5___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(203, 235, 49, 11, 232, 138, 137, 74)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__5___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__5___closed__1_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__4___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__5___closed__1_value)} };
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__5___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__5___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__6(lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_inferType___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__21(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__0_value;
static const lean_array_object l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "mrevert: expected "};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__3;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = " excess arguments in "};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__5;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = ", got "};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__6_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__7;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14_spec__20_spec__22___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14_spec__20___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14_spec__21___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14_spec__21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__7(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__6(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__4___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19_spec__21___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19_spec__21___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19_spec__21___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19_spec__21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_instMonadTermElabM___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___closed__0 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___closed__0_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_instMonadTermElabM___lam__1___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___closed__1 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___closed__1_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_instMonadTacticM___lam__0___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___closed__2 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___closed__2_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_instMonadTacticM___lam__1___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___closed__3 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__13(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__13___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__7___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__7___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__7(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__3(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__2___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mRevert___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__4___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mRevert___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__4___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__4___closed__0_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mRevert___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__4___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__4___closed__0_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mRevert___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__4___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__4___closed__0_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(167, 48, 44, 122, 88, 53, 63, 251)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mRevert___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__4___closed__0_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__4___closed__0_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(71, 102, 82, 181, 251, 135, 109, 75)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mRevert___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__4___closed__0_value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(184, 151, 230, 187, 161, 145, 194, 84)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevert___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__4___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__4___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevert___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevert___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14_spec__20(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14_spec__21(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19_spec__21(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14_spec__20_spec__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Revert_0__Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Revert_0__Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Revert_0__Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Revert_0__Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "ProofMode"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Revert_0__Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Revert_0__Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Revert_0__Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "elabMRevert"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Revert_0__Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Revert_0__Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Revert_0__Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Revert_0__Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Revert_0__Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Revert_0__Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Revert_0__Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Revert_0__Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Revert_0__Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Revert_0__Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(101, 141, 64, 183, 187, 157, 254, 157)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Revert_0__Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__3_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Revert_0__Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__3_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Revert_0__Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(255, 74, 68, 148, 0, 14, 81, 75)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Revert_0__Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Revert_0__Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__3_value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Revert_0__Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(44, 153, 154, 234, 0, 151, 169, 237)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Revert_0__Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Revert_0__Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Revert_0__Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Revert_0__Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___boxed(lean_object*);
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
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__6(void){
_start:
{
lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_33_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__5));
v___x_34_ = l_Lean_stringToMessageData(v___x_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1(lean_object* v_goal_35_, lean_object* v_toPure_36_, lean_object* v_k_37_, lean_object* v_toBind_38_, lean_object* v___x_39_, lean_object* v___x_40_, lean_object* v_inst_41_, lean_object* v_res_42_){
_start:
{
lean_object* v_focusHyp_43_; lean_object* v_restHyps_44_; lean_object* v_proof_45_; lean_object* v___x_46_; 
v_focusHyp_43_ = lean_ctor_get(v_res_42_, 0);
lean_inc_ref_n(v_focusHyp_43_, 2);
v_restHyps_44_ = lean_ctor_get(v_res_42_, 1);
lean_inc_ref(v_restHyps_44_);
v_proof_45_ = lean_ctor_get(v_res_42_, 2);
lean_inc_ref(v_proof_45_);
lean_dec_ref(v_res_42_);
v___x_46_ = l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(v_focusHyp_43_);
if (lean_obj_tag(v___x_46_) == 1)
{
lean_object* v_val_47_; lean_object* v_u_48_; lean_object* v_00_u03c3s_49_; lean_object* v_hyps_50_; lean_object* v_target_51_; lean_object* v___x_53_; uint8_t v_isShared_54_; uint8_t v_isSharedCheck_70_; 
lean_dec(v_inst_41_);
lean_dec_ref(v___x_40_);
lean_dec_ref(v___x_39_);
v_val_47_ = lean_ctor_get(v___x_46_, 0);
lean_inc(v_val_47_);
lean_dec_ref_known(v___x_46_, 1);
v_u_48_ = lean_ctor_get(v_goal_35_, 0);
v_00_u03c3s_49_ = lean_ctor_get(v_goal_35_, 1);
v_hyps_50_ = lean_ctor_get(v_goal_35_, 2);
v_target_51_ = lean_ctor_get(v_goal_35_, 3);
v_isSharedCheck_70_ = !lean_is_exclusive(v_goal_35_);
if (v_isSharedCheck_70_ == 0)
{
v___x_53_ = v_goal_35_;
v_isShared_54_ = v_isSharedCheck_70_;
goto v_resetjp_52_;
}
else
{
lean_inc(v_target_51_);
lean_inc(v_hyps_50_);
lean_inc(v_00_u03c3s_49_);
lean_inc(v_u_48_);
lean_dec(v_goal_35_);
v___x_53_ = lean_box(0);
v_isShared_54_ = v_isSharedCheck_70_;
goto v_resetjp_52_;
}
v_resetjp_52_:
{
lean_object* v_p_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___f_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_66_; 
v_p_55_ = lean_ctor_get(v_val_47_, 2);
lean_inc_ref(v_p_55_);
lean_dec(v_val_47_);
v___x_56_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__0));
v___x_57_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__1));
v___x_58_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__2));
v___x_59_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__4));
v___x_60_ = lean_box(0);
lean_inc(v_u_48_);
v___x_61_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_61_, 0, v_u_48_);
lean_ctor_set(v___x_61_, 1, v___x_60_);
lean_inc_ref(v_target_51_);
lean_inc_ref(v_restHyps_44_);
lean_inc_ref_n(v_00_u03c3s_49_, 2);
lean_inc_ref(v___x_61_);
v___f_62_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__0), 12, 11);
lean_closure_set(v___f_62_, 0, v___x_56_);
lean_closure_set(v___f_62_, 1, v___x_57_);
lean_closure_set(v___f_62_, 2, v___x_58_);
lean_closure_set(v___f_62_, 3, v___x_61_);
lean_closure_set(v___f_62_, 4, v_00_u03c3s_49_);
lean_closure_set(v___f_62_, 5, v_hyps_50_);
lean_closure_set(v___f_62_, 6, v_restHyps_44_);
lean_closure_set(v___f_62_, 7, v_focusHyp_43_);
lean_closure_set(v___f_62_, 8, v_target_51_);
lean_closure_set(v___f_62_, 9, v_proof_45_);
lean_closure_set(v___f_62_, 10, v_toPure_36_);
v___x_63_ = l_Lean_mkConst(v___x_59_, v___x_61_);
v___x_64_ = l_Lean_mkApp3(v___x_63_, v_00_u03c3s_49_, v_p_55_, v_target_51_);
if (v_isShared_54_ == 0)
{
lean_ctor_set(v___x_53_, 3, v___x_64_);
lean_ctor_set(v___x_53_, 2, v_restHyps_44_);
v___x_66_ = v___x_53_;
goto v_reusejp_65_;
}
else
{
lean_object* v_reuseFailAlloc_69_; 
v_reuseFailAlloc_69_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_69_, 0, v_u_48_);
lean_ctor_set(v_reuseFailAlloc_69_, 1, v_00_u03c3s_49_);
lean_ctor_set(v_reuseFailAlloc_69_, 2, v_restHyps_44_);
lean_ctor_set(v_reuseFailAlloc_69_, 3, v___x_64_);
v___x_66_ = v_reuseFailAlloc_69_;
goto v_reusejp_65_;
}
v_reusejp_65_:
{
lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_67_ = lean_apply_1(v_k_37_, v___x_66_);
v___x_68_ = lean_apply_4(v_toBind_38_, lean_box(0), lean_box(0), v___x_67_, v___f_62_);
return v___x_68_;
}
}
}
else
{
lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
lean_dec(v___x_46_);
lean_dec_ref(v_proof_45_);
lean_dec_ref(v_restHyps_44_);
lean_dec_ref(v_focusHyp_43_);
lean_dec(v_toBind_38_);
lean_dec(v_k_37_);
lean_dec(v_toPure_36_);
lean_dec_ref(v_goal_35_);
v___x_71_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__6, &l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__6_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__6);
v___x_72_ = l_Lean_throwError___redArg(v___x_39_, v___x_40_, v___x_71_);
v___x_73_ = lean_apply_2(v_inst_41_, lean_box(0), v___x_72_);
return v___x_73_;
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__0(void){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = l_instMonadEIO___redArg();
return v___x_74_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__1(void){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_75_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__0, &l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__0_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__0);
v___x_76_ = l_StateRefT_x27_instMonad___redArg(v___x_75_);
return v___x_76_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__6(void){
_start:
{
lean_object* v___x_81_; lean_object* v___f_82_; 
v___x_81_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_82_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_82_, 0, v___x_81_);
return v___f_82_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__7(void){
_start:
{
lean_object* v___x_83_; lean_object* v___f_84_; 
v___x_83_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_84_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_84_, 0, v___x_83_);
return v___f_84_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__8(void){
_start:
{
lean_object* v___f_85_; lean_object* v___f_86_; lean_object* v___x_87_; 
v___f_85_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__7, &l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__7_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__7);
v___f_86_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__6, &l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__6_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__6);
v___x_87_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_87_, 0, v___f_86_);
lean_ctor_set(v___x_87_, 1, v___f_85_);
return v___x_87_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__9(void){
_start:
{
lean_object* v___x_88_; lean_object* v___f_89_; 
v___x_88_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__8, &l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__8_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__8);
v___f_89_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_89_, 0, v___x_88_);
return v___f_89_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__10(void){
_start:
{
lean_object* v___x_90_; lean_object* v___f_91_; 
v___x_90_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__8, &l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__8_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__8);
v___f_91_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_91_, 0, v___x_90_);
return v___f_91_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__11(void){
_start:
{
lean_object* v___f_92_; lean_object* v___f_93_; lean_object* v___x_94_; 
v___f_92_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__10, &l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__10_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__10);
v___f_93_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__9, &l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__9_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__9);
v___x_94_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_94_, 0, v___f_93_);
lean_ctor_set(v___x_94_, 1, v___f_92_);
return v___x_94_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__16(void){
_start:
{
lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_99_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_100_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__15));
v___x_101_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__14));
v___x_102_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_101_, v___x_100_, v___x_99_);
return v___x_102_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__17(void){
_start:
{
lean_object* v___x_103_; lean_object* v___f_104_; lean_object* v___f_105_; lean_object* v___x_106_; 
v___x_103_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__16, &l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__16_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__16);
v___f_104_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__13));
v___f_105_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__12));
v___x_106_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_105_, v___f_104_, v___x_103_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg(lean_object* v_inst_107_, lean_object* v_inst_108_, lean_object* v_goal_109_, lean_object* v_ref_110_, lean_object* v_k_111_){
_start:
{
lean_object* v___x_112_; lean_object* v_toApplicative_113_; lean_object* v_toFunctor_114_; lean_object* v_toSeq_115_; lean_object* v_toSeqLeft_116_; lean_object* v_toSeqRight_117_; lean_object* v___f_118_; lean_object* v___f_119_; lean_object* v___f_120_; lean_object* v___f_121_; lean_object* v___x_122_; lean_object* v___f_123_; lean_object* v___f_124_; lean_object* v___f_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v_toApplicative_129_; lean_object* v___x_131_; uint8_t v_isShared_132_; uint8_t v_isSharedCheck_169_; 
v___x_112_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__1);
v_toApplicative_113_ = lean_ctor_get(v___x_112_, 0);
v_toFunctor_114_ = lean_ctor_get(v_toApplicative_113_, 0);
v_toSeq_115_ = lean_ctor_get(v_toApplicative_113_, 2);
v_toSeqLeft_116_ = lean_ctor_get(v_toApplicative_113_, 3);
v_toSeqRight_117_ = lean_ctor_get(v_toApplicative_113_, 4);
v___f_118_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__2));
v___f_119_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_114_, 2);
v___f_120_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_120_, 0, v_toFunctor_114_);
v___f_121_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_121_, 0, v_toFunctor_114_);
v___x_122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_122_, 0, v___f_120_);
lean_ctor_set(v___x_122_, 1, v___f_121_);
lean_inc(v_toSeqRight_117_);
v___f_123_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_123_, 0, v_toSeqRight_117_);
lean_inc(v_toSeqLeft_116_);
v___f_124_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_124_, 0, v_toSeqLeft_116_);
lean_inc(v_toSeq_115_);
v___f_125_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_125_, 0, v_toSeq_115_);
v___x_126_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_126_, 0, v___x_122_);
lean_ctor_set(v___x_126_, 1, v___f_118_);
lean_ctor_set(v___x_126_, 2, v___f_125_);
lean_ctor_set(v___x_126_, 3, v___f_124_);
lean_ctor_set(v___x_126_, 4, v___f_123_);
v___x_127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_127_, 0, v___x_126_);
lean_ctor_set(v___x_127_, 1, v___f_119_);
v___x_128_ = l_StateRefT_x27_instMonad___redArg(v___x_127_);
v_toApplicative_129_ = lean_ctor_get(v___x_128_, 0);
v_isSharedCheck_169_ = !lean_is_exclusive(v___x_128_);
if (v_isSharedCheck_169_ == 0)
{
lean_object* v_unused_170_; 
v_unused_170_ = lean_ctor_get(v___x_128_, 1);
lean_dec(v_unused_170_);
v___x_131_ = v___x_128_;
v_isShared_132_ = v_isSharedCheck_169_;
goto v_resetjp_130_;
}
else
{
lean_inc(v_toApplicative_129_);
lean_dec(v___x_128_);
v___x_131_ = lean_box(0);
v_isShared_132_ = v_isSharedCheck_169_;
goto v_resetjp_130_;
}
v_resetjp_130_:
{
lean_object* v_toFunctor_133_; lean_object* v_toSeq_134_; lean_object* v_toSeqLeft_135_; lean_object* v_toSeqRight_136_; lean_object* v___x_138_; uint8_t v_isShared_139_; uint8_t v_isSharedCheck_167_; 
v_toFunctor_133_ = lean_ctor_get(v_toApplicative_129_, 0);
v_toSeq_134_ = lean_ctor_get(v_toApplicative_129_, 2);
v_toSeqLeft_135_ = lean_ctor_get(v_toApplicative_129_, 3);
v_toSeqRight_136_ = lean_ctor_get(v_toApplicative_129_, 4);
v_isSharedCheck_167_ = !lean_is_exclusive(v_toApplicative_129_);
if (v_isSharedCheck_167_ == 0)
{
lean_object* v_unused_168_; 
v_unused_168_ = lean_ctor_get(v_toApplicative_129_, 1);
lean_dec(v_unused_168_);
v___x_138_ = v_toApplicative_129_;
v_isShared_139_ = v_isSharedCheck_167_;
goto v_resetjp_137_;
}
else
{
lean_inc(v_toSeqRight_136_);
lean_inc(v_toSeqLeft_135_);
lean_inc(v_toSeq_134_);
lean_inc(v_toFunctor_133_);
lean_dec(v_toApplicative_129_);
v___x_138_ = lean_box(0);
v_isShared_139_ = v_isSharedCheck_167_;
goto v_resetjp_137_;
}
v_resetjp_137_:
{
lean_object* v___f_140_; lean_object* v___f_141_; lean_object* v___f_142_; lean_object* v___f_143_; lean_object* v___x_144_; lean_object* v___f_145_; lean_object* v___f_146_; lean_object* v___f_147_; lean_object* v___x_149_; 
v___f_140_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__4));
v___f_141_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__5));
lean_inc_ref(v_toFunctor_133_);
v___f_142_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_142_, 0, v_toFunctor_133_);
v___f_143_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_143_, 0, v_toFunctor_133_);
v___x_144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_144_, 0, v___f_142_);
lean_ctor_set(v___x_144_, 1, v___f_143_);
v___f_145_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_145_, 0, v_toSeqRight_136_);
v___f_146_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_146_, 0, v_toSeqLeft_135_);
v___f_147_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_147_, 0, v_toSeq_134_);
if (v_isShared_139_ == 0)
{
lean_ctor_set(v___x_138_, 4, v___f_145_);
lean_ctor_set(v___x_138_, 3, v___f_146_);
lean_ctor_set(v___x_138_, 2, v___f_147_);
lean_ctor_set(v___x_138_, 1, v___f_140_);
lean_ctor_set(v___x_138_, 0, v___x_144_);
v___x_149_ = v___x_138_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v___x_144_);
lean_ctor_set(v_reuseFailAlloc_166_, 1, v___f_140_);
lean_ctor_set(v_reuseFailAlloc_166_, 2, v___f_147_);
lean_ctor_set(v_reuseFailAlloc_166_, 3, v___f_146_);
lean_ctor_set(v_reuseFailAlloc_166_, 4, v___f_145_);
v___x_149_ = v_reuseFailAlloc_166_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
lean_object* v___x_151_; 
if (v_isShared_132_ == 0)
{
lean_ctor_set(v___x_131_, 1, v___f_141_);
lean_ctor_set(v___x_131_, 0, v___x_149_);
v___x_151_ = v___x_131_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v___x_149_);
lean_ctor_set(v_reuseFailAlloc_165_, 1, v___f_141_);
v___x_151_ = v_reuseFailAlloc_165_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v_toMonadRef_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v_toApplicative_158_; lean_object* v_toBind_159_; lean_object* v_toPure_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___f_163_; lean_object* v___x_164_; 
v___x_152_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__11, &l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__11_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__11);
v___x_153_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__17, &l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__17_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__17);
v_toMonadRef_154_ = lean_ctor_get(v___x_153_, 0);
v___x_155_ = l_Lean_Meta_instAddMessageContextMetaM;
lean_inc_ref(v___x_151_);
v___x_156_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___x_155_, v___x_151_);
lean_inc_ref(v_toMonadRef_154_);
v___x_157_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_157_, 0, v___x_152_);
lean_ctor_set(v___x_157_, 1, v_toMonadRef_154_);
lean_ctor_set(v___x_157_, 2, v___x_156_);
v_toApplicative_158_ = lean_ctor_get(v_inst_107_, 0);
lean_inc_ref(v_toApplicative_158_);
v_toBind_159_ = lean_ctor_get(v_inst_107_, 1);
lean_inc_n(v_toBind_159_, 2);
lean_dec_ref(v_inst_107_);
v_toPure_160_ = lean_ctor_get(v_toApplicative_158_, 1);
lean_inc(v_toPure_160_);
lean_dec_ref(v_toApplicative_158_);
lean_inc_ref(v_goal_109_);
v___x_161_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___boxed), 7, 2);
lean_closure_set(v___x_161_, 0, v_goal_109_);
lean_closure_set(v___x_161_, 1, v_ref_110_);
lean_inc(v_inst_108_);
v___x_162_ = lean_apply_2(v_inst_108_, lean_box(0), v___x_161_);
v___f_163_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1), 8, 7);
lean_closure_set(v___f_163_, 0, v_goal_109_);
lean_closure_set(v___f_163_, 1, v_toPure_160_);
lean_closure_set(v___f_163_, 2, v_k_111_);
lean_closure_set(v___f_163_, 3, v_toBind_159_);
lean_closure_set(v___f_163_, 4, v___x_151_);
lean_closure_set(v___f_163_, 5, v___x_157_);
lean_closure_set(v___f_163_, 6, v_inst_108_);
v___x_164_ = lean_apply_4(v_toBind_159_, lean_box(0), lean_box(0), v___x_162_, v___f_163_);
return v___x_164_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevert(lean_object* v_m_171_, lean_object* v_inst_172_, lean_object* v_inst_173_, lean_object* v_goal_174_, lean_object* v_ref_175_, lean_object* v_k_176_){
_start:
{
lean_object* v___x_177_; 
v___x_177_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg(v_inst_172_, v_inst_173_, v_goal_174_, v_ref_175_, v_k_176_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__0(lean_object* v_it_178_, lean_object* v_acc_179_, lean_object* v_recur_180_){
_start:
{
lean_object* v_array_181_; lean_object* v_start_182_; lean_object* v_stop_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_196_; 
v_array_181_ = lean_ctor_get(v_it_178_, 0);
v_start_182_ = lean_ctor_get(v_it_178_, 1);
v_stop_183_ = lean_ctor_get(v_it_178_, 2);
v_isSharedCheck_196_ = !lean_is_exclusive(v_it_178_);
if (v_isSharedCheck_196_ == 0)
{
v___x_185_ = v_it_178_;
v_isShared_186_ = v_isSharedCheck_196_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_stop_183_);
lean_inc(v_start_182_);
lean_inc(v_array_181_);
lean_dec(v_it_178_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_196_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
uint8_t v___x_187_; 
v___x_187_ = lean_nat_dec_lt(v_start_182_, v_stop_183_);
if (v___x_187_ == 0)
{
lean_del_object(v___x_185_);
lean_dec(v_stop_183_);
lean_dec(v_start_182_);
lean_dec_ref(v_array_181_);
lean_dec_ref(v_recur_180_);
return v_acc_179_;
}
else
{
lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_191_; 
v___x_188_ = lean_unsigned_to_nat(1u);
v___x_189_ = lean_nat_add(v_start_182_, v___x_188_);
lean_inc_ref(v_array_181_);
if (v_isShared_186_ == 0)
{
lean_ctor_set(v___x_185_, 1, v___x_189_);
v___x_191_ = v___x_185_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v_array_181_);
lean_ctor_set(v_reuseFailAlloc_195_, 1, v___x_189_);
lean_ctor_set(v_reuseFailAlloc_195_, 2, v_stop_183_);
v___x_191_ = v_reuseFailAlloc_195_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_192_ = lean_array_fget(v_array_181_, v_start_182_);
lean_dec(v_start_182_);
lean_dec_ref(v_array_181_);
v___x_193_ = lean_array_push(v_acc_179_, v___x_192_);
v___x_194_ = lean_apply_3(v_recur_180_, v___x_191_, v___x_193_, lean_box(0));
return v___x_194_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__1(lean_object* v_inst_197_, lean_object* v_x_198_){
_start:
{
lean_object* v_fst_199_; lean_object* v_snd_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v_fst_199_ = lean_ctor_get(v_x_198_, 0);
lean_inc(v_fst_199_);
v_snd_200_ = lean_ctor_get(v_x_198_, 1);
lean_inc(v_snd_200_);
lean_dec_ref(v_x_198_);
v___x_201_ = lean_alloc_closure((void*)(l_Lean_Meta_mkEq___boxed), 7, 2);
lean_closure_set(v___x_201_, 0, v_snd_200_);
lean_closure_set(v___x_201_, 1, v_fst_199_);
v___x_202_ = lean_apply_2(v_inst_197_, lean_box(0), v___x_201_);
return v___x_202_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__2(lean_object* v_hypName_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = l_Lean_Core_mkFreshUserName(v_hypName_203_, v___y_206_, v___y_207_);
return v___x_209_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_hypName_203_ = stack[0].m_obj;
lean_object* v___y_204_ = stack[1].m_obj;
lean_object* v___y_205_ = stack[2].m_obj;
lean_object* v___y_206_ = stack[3].m_obj;
lean_object* v___y_207_ = stack[4].m_obj;
lean_object* v_res_210_;
v_res_210_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__2(v_hypName_203_, v___y_204_, v___y_205_, v___y_206_, v___y_207_);
stack->m_obj
 = v_res_210_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__2___boxed(lean_object* v_hypName_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__2(v_hypName_211_, v___y_212_, v___y_213_, v___y_214_, v___y_215_);
lean_dec(v___y_215_);
lean_dec_ref(v___y_214_);
lean_dec(v___y_213_);
lean_dec_ref(v___y_212_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__3(lean_object* v_i_218_, lean_object* v_a_219_, lean_object* v_toPure_220_, lean_object* v_____do__lift_221_){
_start:
{
lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_222_ = lean_unsigned_to_nat(1u);
v___x_223_ = lean_nat_add(v_i_218_, v___x_222_);
v___x_224_ = lean_name_append_index_after(v_____do__lift_221_, v___x_223_);
v___x_225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_225_, 0, v___x_224_);
lean_ctor_set(v___x_225_, 1, v_a_219_);
v___x_226_ = lean_apply_2(v_toPure_220_, lean_box(0), v___x_225_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__3___boxed(lean_object* v_i_227_, lean_object* v_a_228_, lean_object* v_toPure_229_, lean_object* v_____do__lift_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__3(v_i_227_, v_a_228_, v_toPure_229_, v_____do__lift_230_);
lean_dec(v_i_227_);
return v_res_231_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__4(lean_object* v___x_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_){
_start:
{
lean_object* v___x_238_; 
v___x_238_ = l_Lean_Core_mkFreshUserName(v___x_232_, v___y_235_, v___y_236_);
return v___x_238_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_232_ = stack[0].m_obj;
lean_object* v___y_233_ = stack[1].m_obj;
lean_object* v___y_234_ = stack[2].m_obj;
lean_object* v___y_235_ = stack[3].m_obj;
lean_object* v___y_236_ = stack[4].m_obj;
lean_object* v_res_239_;
v_res_239_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__4(v___x_232_, v___y_233_, v___y_234_, v___y_235_, v___y_236_);
stack->m_obj
 = v_res_239_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__4___boxed(lean_object* v___x_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__4(v___x_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_);
lean_dec(v___y_244_);
lean_dec_ref(v___y_243_);
lean_dec(v___y_242_);
lean_dec_ref(v___y_241_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__5(lean_object* v_toPure_252_, lean_object* v_inst_253_, lean_object* v_toBind_254_, lean_object* v_i_255_, lean_object* v_a_256_, lean_object* v_x_257_){
_start:
{
lean_object* v___f_258_; lean_object* v___f_259_; lean_object* v___x_260_; lean_object* v___x_261_; 
v___f_258_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__3___boxed), 4, 3);
lean_closure_set(v___f_258_, 0, v_i_255_);
lean_closure_set(v___f_258_, 1, v_a_256_);
lean_closure_set(v___f_258_, 2, v_toPure_252_);
v___f_259_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__5___closed__2));
v___x_260_ = lean_apply_2(v_inst_253_, lean_box(0), v___f_259_);
v___x_261_ = lean_apply_4(v_toBind_254_, lean_box(0), lean_box(0), v___x_260_, v___f_258_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__6(lean_object* v_u_262_, lean_object* v_x1_263_, lean_object* v_x2_264_){
_start:
{
lean_object* v___x_265_; 
v___x_265_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkCons(v_u_262_, v_x1_263_, v_x2_264_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__7(lean_object* v_00_u03c6_266_, lean_object* v_toPure_267_, lean_object* v_____do__lift_268_){
_start:
{
lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_269_, 0, v_____do__lift_268_);
lean_ctor_set(v___x_269_, 1, v_00_u03c6_266_);
v___x_270_ = lean_apply_2(v_toPure_267_, lean_box(0), v___x_269_);
return v___x_270_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__8(lean_object* v_hypName_271_, lean_object* v_uniq_272_, lean_object* v_toPure_273_, lean_object* v_ss_274_, lean_object* v_hyps_275_, uint8_t v___x_276_, uint8_t v___x_277_, uint8_t v___x_278_, lean_object* v_inst_279_, lean_object* v_toBind_280_, lean_object* v_____do__lift_281_){
_start:
{
lean_object* v___x_282_; lean_object* v_00_u03c6_283_; lean_object* v___f_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_282_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_282_, 0, v_hypName_271_);
lean_ctor_set(v___x_282_, 1, v_uniq_272_);
lean_ctor_set(v___x_282_, 2, v_____do__lift_281_);
v_00_u03c6_283_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_282_);
v___f_284_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__7), 3, 2);
lean_closure_set(v___f_284_, 0, v_00_u03c6_283_);
lean_closure_set(v___f_284_, 1, v_toPure_273_);
v___x_285_ = lean_box(v___x_276_);
v___x_286_ = lean_box(v___x_277_);
v___x_287_ = lean_box(v___x_276_);
v___x_288_ = lean_box(v___x_277_);
v___x_289_ = lean_box(v___x_278_);
v___x_290_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(v___x_290_, 0, v_ss_274_);
lean_closure_set(v___x_290_, 1, v_hyps_275_);
lean_closure_set(v___x_290_, 2, v___x_285_);
lean_closure_set(v___x_290_, 3, v___x_286_);
lean_closure_set(v___x_290_, 4, v___x_287_);
lean_closure_set(v___x_290_, 5, v___x_288_);
lean_closure_set(v___x_290_, 6, v___x_289_);
v___x_291_ = lean_apply_2(v_inst_279_, lean_box(0), v___x_290_);
v___x_292_ = lean_apply_4(v_toBind_280_, lean_box(0), lean_box(0), v___x_291_, v___f_284_);
return v___x_292_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_hypName_271_ = stack[0].m_obj;
lean_object* v_uniq_272_ = stack[1].m_obj;
lean_object* v_toPure_273_ = stack[2].m_obj;
lean_object* v_ss_274_ = stack[3].m_obj;
lean_object* v_hyps_275_ = stack[4].m_obj;
uint8_t v___x_276_ = stack[5].m_num;
uint8_t v___x_277_ = stack[6].m_num;
uint8_t v___x_278_ = stack[7].m_num;
lean_object* v_inst_279_ = stack[8].m_obj;
lean_object* v_toBind_280_ = stack[9].m_obj;
lean_object* v_____do__lift_281_ = stack[10].m_obj;
lean_object* v_res_293_;
v_res_293_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__8(v_hypName_271_, v_uniq_272_, v_toPure_273_, v_ss_274_, v_hyps_275_, v___x_276_, v___x_277_, v___x_278_, v_inst_279_, v_toBind_280_, v_____do__lift_281_);
stack->m_obj
 = v_res_293_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__8___boxed(lean_object* v_hypName_294_, lean_object* v_uniq_295_, lean_object* v_toPure_296_, lean_object* v_ss_297_, lean_object* v_hyps_298_, lean_object* v___x_299_, lean_object* v___x_300_, lean_object* v___x_301_, lean_object* v_inst_302_, lean_object* v_toBind_303_, lean_object* v_____do__lift_304_){
_start:
{
uint8_t v___x_1143__boxed_305_; uint8_t v___x_1144__boxed_306_; uint8_t v___x_1145__boxed_307_; lean_object* v_res_308_; 
v___x_1143__boxed_305_ = lean_unbox(v___x_299_);
v___x_1144__boxed_306_ = lean_unbox(v___x_300_);
v___x_1145__boxed_307_ = lean_unbox(v___x_301_);
v_res_308_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__8(v_hypName_294_, v_uniq_295_, v_toPure_296_, v_ss_297_, v_hyps_298_, v___x_1143__boxed_305_, v___x_1144__boxed_306_, v___x_1145__boxed_307_, v_inst_302_, v_toBind_303_, v_____do__lift_304_);
return v_res_308_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__9(lean_object* v_hypName_309_, lean_object* v_toPure_310_, lean_object* v_ss_311_, lean_object* v_hyps_312_, uint8_t v___x_313_, lean_object* v_inst_314_, lean_object* v_toBind_315_, lean_object* v_00_u03c6_316_, lean_object* v_uniq_317_){
_start:
{
uint8_t v___x_318_; uint8_t v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___f_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_318_ = 1;
v___x_319_ = 1;
v___x_320_ = lean_box(v___x_313_);
v___x_321_ = lean_box(v___x_318_);
v___x_322_ = lean_box(v___x_319_);
lean_inc(v_toBind_315_);
lean_inc(v_inst_314_);
lean_inc_ref(v_ss_311_);
v___f_323_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__8___boxed), 11, 10);
lean_closure_set(v___f_323_, 0, v_hypName_309_);
lean_closure_set(v___f_323_, 1, v_uniq_317_);
lean_closure_set(v___f_323_, 2, v_toPure_310_);
lean_closure_set(v___f_323_, 3, v_ss_311_);
lean_closure_set(v___f_323_, 4, v_hyps_312_);
lean_closure_set(v___f_323_, 5, v___x_320_);
lean_closure_set(v___f_323_, 6, v___x_321_);
lean_closure_set(v___f_323_, 7, v___x_322_);
lean_closure_set(v___f_323_, 8, v_inst_314_);
lean_closure_set(v___f_323_, 9, v_toBind_315_);
v___x_324_ = lean_box(v___x_313_);
v___x_325_ = lean_box(v___x_318_);
v___x_326_ = lean_box(v___x_313_);
v___x_327_ = lean_box(v___x_318_);
v___x_328_ = lean_box(v___x_319_);
v___x_329_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(v___x_329_, 0, v_ss_311_);
lean_closure_set(v___x_329_, 1, v_00_u03c6_316_);
lean_closure_set(v___x_329_, 2, v___x_324_);
lean_closure_set(v___x_329_, 3, v___x_325_);
lean_closure_set(v___x_329_, 4, v___x_326_);
lean_closure_set(v___x_329_, 5, v___x_327_);
lean_closure_set(v___x_329_, 6, v___x_328_);
v___x_330_ = lean_apply_2(v_inst_314_, lean_box(0), v___x_329_);
v___x_331_ = lean_apply_4(v_toBind_315_, lean_box(0), lean_box(0), v___x_330_, v___f_323_);
return v___x_331_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_hypName_309_ = stack[0].m_obj;
lean_object* v_toPure_310_ = stack[1].m_obj;
lean_object* v_ss_311_ = stack[2].m_obj;
lean_object* v_hyps_312_ = stack[3].m_obj;
uint8_t v___x_313_ = stack[4].m_num;
lean_object* v_inst_314_ = stack[5].m_obj;
lean_object* v_toBind_315_ = stack[6].m_obj;
lean_object* v_00_u03c6_316_ = stack[7].m_obj;
lean_object* v_uniq_317_ = stack[8].m_obj;
lean_object* v_res_332_;
v_res_332_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__9(v_hypName_309_, v_toPure_310_, v_ss_311_, v_hyps_312_, v___x_313_, v_inst_314_, v_toBind_315_, v_00_u03c6_316_, v_uniq_317_);
stack->m_obj
 = v_res_332_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__9___boxed(lean_object* v_hypName_333_, lean_object* v_toPure_334_, lean_object* v_ss_335_, lean_object* v_hyps_336_, lean_object* v___x_337_, lean_object* v_inst_338_, lean_object* v_toBind_339_, lean_object* v_00_u03c6_340_, lean_object* v_uniq_341_){
_start:
{
uint8_t v___x_1198__boxed_342_; lean_object* v_res_343_; 
v___x_1198__boxed_342_ = lean_unbox(v___x_337_);
v_res_343_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__9(v_hypName_333_, v_toPure_334_, v_ss_335_, v_hyps_336_, v___x_1198__boxed_342_, v_inst_338_, v_toBind_339_, v_00_u03c6_340_, v_uniq_341_);
return v_res_343_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__10(lean_object* v_u_344_, lean_object* v_00_u03c3s_345_, lean_object* v_hypName_346_, lean_object* v_toPure_347_, lean_object* v_ss_348_, lean_object* v_hyps_349_, uint8_t v___x_350_, lean_object* v_inst_351_, lean_object* v_toBind_352_, lean_object* v___f_353_, lean_object* v_eqs_354_){
_start:
{
lean_object* v_eqs_355_; lean_object* v_00_u03c6_356_; lean_object* v_00_u03c6_357_; lean_object* v___x_358_; lean_object* v___f_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v_eqs_355_ = lean_array_to_list(v_eqs_354_);
v_00_u03c6_356_ = l_Lean_mkAndN(v_eqs_355_);
v_00_u03c6_357_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure(v_u_344_, v_00_u03c3s_345_, v_00_u03c6_356_);
v___x_358_ = lean_box(v___x_350_);
lean_inc(v_toBind_352_);
lean_inc(v_inst_351_);
v___f_359_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__9___boxed), 9, 8);
lean_closure_set(v___f_359_, 0, v_hypName_346_);
lean_closure_set(v___f_359_, 1, v_toPure_347_);
lean_closure_set(v___f_359_, 2, v_ss_348_);
lean_closure_set(v___f_359_, 3, v_hyps_349_);
lean_closure_set(v___f_359_, 4, v___x_358_);
lean_closure_set(v___f_359_, 5, v_inst_351_);
lean_closure_set(v___f_359_, 6, v_toBind_352_);
lean_closure_set(v___f_359_, 7, v_00_u03c6_357_);
v___x_360_ = lean_apply_2(v_inst_351_, lean_box(0), v___f_353_);
v___x_361_ = lean_apply_4(v_toBind_352_, lean_box(0), lean_box(0), v___x_360_, v___f_359_);
return v___x_361_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_344_ = stack[0].m_obj;
lean_object* v_00_u03c3s_345_ = stack[1].m_obj;
lean_object* v_hypName_346_ = stack[2].m_obj;
lean_object* v_toPure_347_ = stack[3].m_obj;
lean_object* v_ss_348_ = stack[4].m_obj;
lean_object* v_hyps_349_ = stack[5].m_obj;
uint8_t v___x_350_ = stack[6].m_num;
lean_object* v_inst_351_ = stack[7].m_obj;
lean_object* v_toBind_352_ = stack[8].m_obj;
lean_object* v___f_353_ = stack[9].m_obj;
lean_object* v_eqs_354_ = stack[10].m_obj;
lean_object* v_res_362_;
v_res_362_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__10(v_u_344_, v_00_u03c3s_345_, v_hypName_346_, v_toPure_347_, v_ss_348_, v_hyps_349_, v___x_350_, v_inst_351_, v_toBind_352_, v___f_353_, v_eqs_354_);
stack->m_obj
 = v_res_362_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__10___boxed(lean_object* v_u_363_, lean_object* v_00_u03c3s_364_, lean_object* v_hypName_365_, lean_object* v_toPure_366_, lean_object* v_ss_367_, lean_object* v_hyps_368_, lean_object* v___x_369_, lean_object* v_inst_370_, lean_object* v_toBind_371_, lean_object* v___f_372_, lean_object* v_eqs_373_){
_start:
{
uint8_t v___x_1250__boxed_374_; lean_object* v_res_375_; 
v___x_1250__boxed_374_ = lean_unbox(v___x_369_);
v_res_375_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__10(v_u_363_, v_00_u03c3s_364_, v_hypName_365_, v_toPure_366_, v_ss_367_, v_hyps_368_, v___x_1250__boxed_374_, v_inst_370_, v_toBind_371_, v___f_372_, v_eqs_373_);
return v_res_375_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__11(lean_object* v_u_376_, lean_object* v_00_u03c3s_377_, lean_object* v_hypName_378_, lean_object* v_toPure_379_, lean_object* v_hyps_380_, uint8_t v___x_381_, lean_object* v_inst_382_, lean_object* v_toBind_383_, lean_object* v___f_384_, lean_object* v_revertArgs_385_, lean_object* v_inst_386_, lean_object* v___f_387_, lean_object* v_ss_388_){
_start:
{
lean_object* v___x_389_; lean_object* v___f_390_; lean_object* v___x_391_; size_t v_sz_392_; size_t v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_389_ = lean_box(v___x_381_);
lean_inc(v_toBind_383_);
lean_inc_ref(v_ss_388_);
v___f_390_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__10___boxed), 11, 10);
lean_closure_set(v___f_390_, 0, v_u_376_);
lean_closure_set(v___f_390_, 1, v_00_u03c3s_377_);
lean_closure_set(v___f_390_, 2, v_hypName_378_);
lean_closure_set(v___f_390_, 3, v_toPure_379_);
lean_closure_set(v___f_390_, 4, v_ss_388_);
lean_closure_set(v___f_390_, 5, v_hyps_380_);
lean_closure_set(v___f_390_, 6, v___x_389_);
lean_closure_set(v___f_390_, 7, v_inst_382_);
lean_closure_set(v___f_390_, 8, v_toBind_383_);
lean_closure_set(v___f_390_, 9, v___f_384_);
v___x_391_ = l_Array_zip___redArg(v_revertArgs_385_, v_ss_388_);
lean_dec_ref(v_ss_388_);
v_sz_392_ = lean_array_size(v___x_391_);
v___x_393_ = ((size_t)0ULL);
v___x_394_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_386_, v___f_387_, v_sz_392_, v___x_393_, v___x_391_);
v___x_395_ = lean_apply_4(v_toBind_383_, lean_box(0), lean_box(0), v___x_394_, v___f_390_);
return v___x_395_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_376_ = stack[0].m_obj;
lean_object* v_00_u03c3s_377_ = stack[1].m_obj;
lean_object* v_hypName_378_ = stack[2].m_obj;
lean_object* v_toPure_379_ = stack[3].m_obj;
lean_object* v_hyps_380_ = stack[4].m_obj;
uint8_t v___x_381_ = stack[5].m_num;
lean_object* v_inst_382_ = stack[6].m_obj;
lean_object* v_toBind_383_ = stack[7].m_obj;
lean_object* v___f_384_ = stack[8].m_obj;
lean_object* v_revertArgs_385_ = stack[9].m_obj;
lean_object* v_inst_386_ = stack[10].m_obj;
lean_object* v___f_387_ = stack[11].m_obj;
lean_object* v_ss_388_ = stack[12].m_obj;
lean_object* v_res_396_;
v_res_396_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__11(v_u_376_, v_00_u03c3s_377_, v_hypName_378_, v_toPure_379_, v_hyps_380_, v___x_381_, v_inst_382_, v_toBind_383_, v___f_384_, v_revertArgs_385_, v_inst_386_, v___f_387_, v_ss_388_);
stack->m_obj
 = v_res_396_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__11___boxed(lean_object* v_u_397_, lean_object* v_00_u03c3s_398_, lean_object* v_hypName_399_, lean_object* v_toPure_400_, lean_object* v_hyps_401_, lean_object* v___x_402_, lean_object* v_inst_403_, lean_object* v_toBind_404_, lean_object* v___f_405_, lean_object* v_revertArgs_406_, lean_object* v_inst_407_, lean_object* v___f_408_, lean_object* v_ss_409_){
_start:
{
uint8_t v___x_1277__boxed_410_; lean_object* v_res_411_; 
v___x_1277__boxed_410_ = lean_unbox(v___x_402_);
v_res_411_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__11(v_u_397_, v_00_u03c3s_398_, v_hypName_399_, v_toPure_400_, v_hyps_401_, v___x_1277__boxed_410_, v_inst_403_, v_toBind_404_, v___f_405_, v_revertArgs_406_, v_inst_407_, v___f_408_, v_ss_409_);
lean_dec_ref(v_revertArgs_406_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__12(lean_object* v_u_420_, lean_object* v_fst_421_, lean_object* v_revertArgs_422_, lean_object* v_snd_423_, lean_object* v_prf_424_, lean_object* v_00_u03c3s_425_, lean_object* v_hyps_426_, lean_object* v_target_427_, lean_object* v_h_428_, lean_object* v_toPure_429_, lean_object* v_____do__lift_430_){
_start:
{
lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v_prf_438_; lean_object* v___x_439_; 
v___x_431_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__12___closed__1));
v___x_432_ = lean_box(0);
v___x_433_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_433_, 0, v_u_420_);
lean_ctor_set(v___x_433_, 1, v___x_432_);
v___x_434_ = l_Lean_mkConst(v___x_431_, v___x_433_);
v___x_435_ = l_Lean_mkAppN(v_fst_421_, v_revertArgs_422_);
v___x_436_ = l_Lean_mkAppN(v_snd_423_, v_revertArgs_422_);
v___x_437_ = l_Lean_mkAppN(v_prf_424_, v_revertArgs_422_);
v_prf_438_ = l_Lean_mkApp8(v___x_434_, v_00_u03c3s_425_, v_____do__lift_430_, v_hyps_426_, v___x_435_, v_target_427_, v_h_428_, v___x_436_, v___x_437_);
v___x_439_ = lean_apply_2(v_toPure_429_, lean_box(0), v_prf_438_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__12___boxed(lean_object* v_u_440_, lean_object* v_fst_441_, lean_object* v_revertArgs_442_, lean_object* v_snd_443_, lean_object* v_prf_444_, lean_object* v_00_u03c3s_445_, lean_object* v_hyps_446_, lean_object* v_target_447_, lean_object* v_h_448_, lean_object* v_toPure_449_, lean_object* v_____do__lift_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__12(v_u_440_, v_fst_441_, v_revertArgs_442_, v_snd_443_, v_prf_444_, v_00_u03c3s_445_, v_hyps_446_, v_target_447_, v_h_448_, v_toPure_449_, v_____do__lift_450_);
lean_dec_ref(v_revertArgs_442_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__13(lean_object* v_u_452_, lean_object* v_fst_453_, lean_object* v_revertArgs_454_, lean_object* v_snd_455_, lean_object* v_00_u03c3s_456_, lean_object* v_hyps_457_, lean_object* v_target_458_, lean_object* v_h_459_, lean_object* v_toPure_460_, lean_object* v_inst_461_, lean_object* v_toBind_462_, lean_object* v_prf_463_){
_start:
{
lean_object* v___f_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
lean_inc_ref(v_h_459_);
v___f_464_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__12___boxed), 11, 10);
lean_closure_set(v___f_464_, 0, v_u_452_);
lean_closure_set(v___f_464_, 1, v_fst_453_);
lean_closure_set(v___f_464_, 2, v_revertArgs_454_);
lean_closure_set(v___f_464_, 3, v_snd_455_);
lean_closure_set(v___f_464_, 4, v_prf_463_);
lean_closure_set(v___f_464_, 5, v_00_u03c3s_456_);
lean_closure_set(v___f_464_, 6, v_hyps_457_);
lean_closure_set(v___f_464_, 7, v_target_458_);
lean_closure_set(v___f_464_, 8, v_h_459_);
lean_closure_set(v___f_464_, 9, v_toPure_460_);
v___x_465_ = lean_alloc_closure((void*)(l_Lean_Meta_inferType___boxed), 6, 1);
lean_closure_set(v___x_465_, 0, v_h_459_);
v___x_466_ = lean_apply_2(v_inst_461_, lean_box(0), v___x_465_);
v___x_467_ = lean_apply_4(v_toBind_462_, lean_box(0), lean_box(0), v___x_466_, v___f_464_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__14(lean_object* v___y_468_, lean_object* v_u_469_, lean_object* v_snd_470_, lean_object* v_revertArgs_471_, lean_object* v_00_u03c3s_472_, lean_object* v_hyps_473_, lean_object* v_target_474_, lean_object* v_h_475_, lean_object* v_toPure_476_, lean_object* v_inst_477_, lean_object* v_toBind_478_, lean_object* v_a_479_, lean_object* v_n_480_, lean_object* v_f_481_, lean_object* v_k_482_, lean_object* v_H_483_){
_start:
{
lean_object* v_H_484_; lean_object* v___x_485_; lean_object* v_fst_486_; lean_object* v_snd_487_; lean_object* v___f_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v_goal_x27_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
lean_inc_ref_n(v___y_468_, 2);
v_H_484_ = l_Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps(v___y_468_, v_H_483_);
lean_inc_n(v_u_469_, 2);
v___x_485_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd(v_u_469_, v___y_468_, v_H_484_, v_snd_470_);
v_fst_486_ = lean_ctor_get(v___x_485_, 0);
lean_inc_n(v_fst_486_, 2);
v_snd_487_ = lean_ctor_get(v___x_485_, 1);
lean_inc(v_snd_487_);
lean_dec_ref(v___x_485_);
lean_inc(v_toBind_478_);
v___f_488_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__13), 12, 11);
lean_closure_set(v___f_488_, 0, v_u_469_);
lean_closure_set(v___f_488_, 1, v_fst_486_);
lean_closure_set(v___f_488_, 2, v_revertArgs_471_);
lean_closure_set(v___f_488_, 3, v_snd_487_);
lean_closure_set(v___f_488_, 4, v_00_u03c3s_472_);
lean_closure_set(v___f_488_, 5, v_hyps_473_);
lean_closure_set(v___f_488_, 6, v_target_474_);
lean_closure_set(v___f_488_, 7, v_h_475_);
lean_closure_set(v___f_488_, 8, v_toPure_476_);
lean_closure_set(v___f_488_, 9, v_inst_477_);
lean_closure_set(v___f_488_, 10, v_toBind_478_);
v___x_489_ = lean_array_get_size(v_a_479_);
v___x_490_ = l_Array_toSubarray___redArg(v_a_479_, v_n_480_, v___x_489_);
v___x_491_ = l_Subarray_copy___redArg(v___x_490_);
v___x_492_ = l_Lean_mkAppRev(v_f_481_, v___x_491_);
lean_dec_ref(v___x_491_);
v_goal_x27_493_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_goal_x27_493_, 0, v_u_469_);
lean_ctor_set(v_goal_x27_493_, 1, v___y_468_);
lean_ctor_set(v_goal_x27_493_, 2, v_fst_486_);
lean_ctor_set(v_goal_x27_493_, 3, v___x_492_);
v___x_494_ = lean_apply_1(v_k_482_, v_goal_x27_493_);
v___x_495_ = lean_apply_4(v_toBind_478_, lean_box(0), lean_box(0), v___x_494_, v___f_488_);
return v___x_495_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15(lean_object* v_u_515_, lean_object* v_snd_516_, lean_object* v_revertArgs_517_, lean_object* v_00_u03c3s_518_, lean_object* v_hyps_519_, lean_object* v_target_520_, lean_object* v_toPure_521_, lean_object* v_inst_522_, lean_object* v_toBind_523_, lean_object* v_a_524_, lean_object* v_n_525_, lean_object* v_f_526_, lean_object* v_k_527_, lean_object* v_fst_528_, lean_object* v_revertArgsTypes_529_, lean_object* v___x_530_, lean_object* v___f_531_, lean_object* v_h_532_){
_start:
{
lean_object* v___y_534_; lean_object* v___x_539_; lean_object* v___x_540_; uint8_t v___x_541_; 
v___x_539_ = lean_array_get_size(v_revertArgsTypes_529_);
v___x_540_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__9));
v___x_541_ = lean_nat_dec_lt(v___x_530_, v___x_539_);
if (v___x_541_ == 0)
{
lean_dec_ref(v___f_531_);
lean_dec_ref(v_revertArgsTypes_529_);
lean_inc_ref(v_00_u03c3s_518_);
v___y_534_ = v_00_u03c3s_518_;
goto v___jp_533_;
}
else
{
size_t v___x_542_; size_t v___x_543_; lean_object* v___x_544_; 
v___x_542_ = lean_usize_of_nat(v___x_539_);
v___x_543_ = ((size_t)0ULL);
lean_inc_ref(v_00_u03c3s_518_);
v___x_544_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_540_, v___f_531_, v_revertArgsTypes_529_, v___x_542_, v___x_543_, v_00_u03c3s_518_);
v___y_534_ = v___x_544_;
goto v___jp_533_;
}
v___jp_533_:
{
lean_object* v___f_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
lean_inc(v_toBind_523_);
lean_inc(v_inst_522_);
v___f_535_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__14), 16, 15);
lean_closure_set(v___f_535_, 0, v___y_534_);
lean_closure_set(v___f_535_, 1, v_u_515_);
lean_closure_set(v___f_535_, 2, v_snd_516_);
lean_closure_set(v___f_535_, 3, v_revertArgs_517_);
lean_closure_set(v___f_535_, 4, v_00_u03c3s_518_);
lean_closure_set(v___f_535_, 5, v_hyps_519_);
lean_closure_set(v___f_535_, 6, v_target_520_);
lean_closure_set(v___f_535_, 7, v_h_532_);
lean_closure_set(v___f_535_, 8, v_toPure_521_);
lean_closure_set(v___f_535_, 9, v_inst_522_);
lean_closure_set(v___f_535_, 10, v_toBind_523_);
lean_closure_set(v___f_535_, 11, v_a_524_);
lean_closure_set(v___f_535_, 12, v_n_525_);
lean_closure_set(v___f_535_, 13, v_f_526_);
lean_closure_set(v___f_535_, 14, v_k_527_);
v___x_536_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateMVarsIfMVarApp___boxed), 6, 1);
lean_closure_set(v___x_536_, 0, v_fst_528_);
v___x_537_ = lean_apply_2(v_inst_522_, lean_box(0), v___x_536_);
v___x_538_ = lean_apply_4(v_toBind_523_, lean_box(0), lean_box(0), v___x_537_, v___f_535_);
return v___x_538_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_515_ = stack[0].m_obj;
lean_object* v_snd_516_ = stack[1].m_obj;
lean_object* v_revertArgs_517_ = stack[2].m_obj;
lean_object* v_00_u03c3s_518_ = stack[3].m_obj;
lean_object* v_hyps_519_ = stack[4].m_obj;
lean_object* v_target_520_ = stack[5].m_obj;
lean_object* v_toPure_521_ = stack[6].m_obj;
lean_object* v_inst_522_ = stack[7].m_obj;
lean_object* v_toBind_523_ = stack[8].m_obj;
lean_object* v_a_524_ = stack[9].m_obj;
lean_object* v_n_525_ = stack[10].m_obj;
lean_object* v_f_526_ = stack[11].m_obj;
lean_object* v_k_527_ = stack[12].m_obj;
lean_object* v_fst_528_ = stack[13].m_obj;
lean_object* v_revertArgsTypes_529_ = stack[14].m_obj;
lean_object* v___x_530_ = stack[15].m_obj;
lean_object* v___f_531_ = stack[16].m_obj;
lean_object* v_h_532_ = stack[17].m_obj;
lean_object* v_res_545_;
v_res_545_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15(v_u_515_, v_snd_516_, v_revertArgs_517_, v_00_u03c3s_518_, v_hyps_519_, v_target_520_, v_toPure_521_, v_inst_522_, v_toBind_523_, v_a_524_, v_n_525_, v_f_526_, v_k_527_, v_fst_528_, v_revertArgsTypes_529_, v___x_530_, v___f_531_, v_h_532_);
stack->m_obj
 = v_res_545_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___boxed(lean_object** _args){
lean_object* v_u_546_ = _args[0];
lean_object* v_snd_547_ = _args[1];
lean_object* v_revertArgs_548_ = _args[2];
lean_object* v_00_u03c3s_549_ = _args[3];
lean_object* v_hyps_550_ = _args[4];
lean_object* v_target_551_ = _args[5];
lean_object* v_toPure_552_ = _args[6];
lean_object* v_inst_553_ = _args[7];
lean_object* v_toBind_554_ = _args[8];
lean_object* v_a_555_ = _args[9];
lean_object* v_n_556_ = _args[10];
lean_object* v_f_557_ = _args[11];
lean_object* v_k_558_ = _args[12];
lean_object* v_fst_559_ = _args[13];
lean_object* v_revertArgsTypes_560_ = _args[14];
lean_object* v___x_561_ = _args[15];
lean_object* v___f_562_ = _args[16];
lean_object* v_h_563_ = _args[17];
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15(v_u_546_, v_snd_547_, v_revertArgs_548_, v_00_u03c3s_549_, v_hyps_550_, v_target_551_, v_toPure_552_, v_inst_553_, v_toBind_554_, v_a_555_, v_n_556_, v_f_557_, v_k_558_, v_fst_559_, v_revertArgsTypes_560_, v___x_561_, v___f_562_, v_h_563_);
lean_dec(v___x_561_);
return v_res_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__16(lean_object* v_inst_565_, lean_object* v_toBind_566_, lean_object* v___f_567_, lean_object* v_prfs_568_){
_start:
{
lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_569_ = lean_array_to_list(v_prfs_568_);
v___x_570_ = lean_alloc_closure((void*)(l_Lean_Meta_mkAndIntroN___boxed), 6, 1);
lean_closure_set(v___x_570_, 0, v___x_569_);
v___x_571_ = lean_apply_2(v_inst_565_, lean_box(0), v___x_570_);
v___x_572_ = lean_apply_4(v_toBind_566_, lean_box(0), lean_box(0), v___x_571_, v___f_567_);
return v___x_572_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__17(lean_object* v_u_574_, lean_object* v_revertArgs_575_, lean_object* v_00_u03c3s_576_, lean_object* v_hyps_577_, lean_object* v_target_578_, lean_object* v_toPure_579_, lean_object* v_inst_580_, lean_object* v_toBind_581_, lean_object* v_a_582_, lean_object* v_n_583_, lean_object* v_f_584_, lean_object* v_k_585_, lean_object* v_revertArgsTypes_586_, lean_object* v___x_587_, lean_object* v___f_588_, lean_object* v___x_589_, lean_object* v_____x_590_){
_start:
{
lean_object* v_fst_591_; lean_object* v_snd_592_; lean_object* v___f_593_; lean_object* v___f_594_; lean_object* v___x_595_; size_t v_sz_596_; size_t v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; 
v_fst_591_ = lean_ctor_get(v_____x_590_, 0);
lean_inc(v_fst_591_);
v_snd_592_ = lean_ctor_get(v_____x_590_, 1);
lean_inc(v_snd_592_);
lean_dec_ref(v_____x_590_);
lean_inc_n(v_toBind_581_, 2);
lean_inc_n(v_inst_580_, 2);
lean_inc_ref(v_revertArgs_575_);
v___f_593_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___boxed), 18, 17);
lean_closure_set(v___f_593_, 0, v_u_574_);
lean_closure_set(v___f_593_, 1, v_snd_592_);
lean_closure_set(v___f_593_, 2, v_revertArgs_575_);
lean_closure_set(v___f_593_, 3, v_00_u03c3s_576_);
lean_closure_set(v___f_593_, 4, v_hyps_577_);
lean_closure_set(v___f_593_, 5, v_target_578_);
lean_closure_set(v___f_593_, 6, v_toPure_579_);
lean_closure_set(v___f_593_, 7, v_inst_580_);
lean_closure_set(v___f_593_, 8, v_toBind_581_);
lean_closure_set(v___f_593_, 9, v_a_582_);
lean_closure_set(v___f_593_, 10, v_n_583_);
lean_closure_set(v___f_593_, 11, v_f_584_);
lean_closure_set(v___f_593_, 12, v_k_585_);
lean_closure_set(v___f_593_, 13, v_fst_591_);
lean_closure_set(v___f_593_, 14, v_revertArgsTypes_586_);
lean_closure_set(v___f_593_, 15, v___x_587_);
lean_closure_set(v___f_593_, 16, v___f_588_);
v___f_594_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__16), 4, 3);
lean_closure_set(v___f_594_, 0, v_inst_580_);
lean_closure_set(v___f_594_, 1, v_toBind_581_);
lean_closure_set(v___f_594_, 2, v___f_593_);
v___x_595_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__17___closed__0));
v_sz_596_ = lean_array_size(v_revertArgs_575_);
v___x_597_ = ((size_t)0ULL);
v___x_598_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_589_, v___x_595_, v_sz_596_, v___x_597_, v_revertArgs_575_);
v___x_599_ = lean_apply_2(v_inst_580_, lean_box(0), v___x_598_);
v___x_600_ = lean_apply_4(v_toBind_581_, lean_box(0), lean_box(0), v___x_599_, v___f_594_);
return v___x_600_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__17_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_574_ = stack[0].m_obj;
lean_object* v_revertArgs_575_ = stack[1].m_obj;
lean_object* v_00_u03c3s_576_ = stack[2].m_obj;
lean_object* v_hyps_577_ = stack[3].m_obj;
lean_object* v_target_578_ = stack[4].m_obj;
lean_object* v_toPure_579_ = stack[5].m_obj;
lean_object* v_inst_580_ = stack[6].m_obj;
lean_object* v_toBind_581_ = stack[7].m_obj;
lean_object* v_a_582_ = stack[8].m_obj;
lean_object* v_n_583_ = stack[9].m_obj;
lean_object* v_f_584_ = stack[10].m_obj;
lean_object* v_k_585_ = stack[11].m_obj;
lean_object* v_revertArgsTypes_586_ = stack[12].m_obj;
lean_object* v___x_587_ = stack[13].m_obj;
lean_object* v___f_588_ = stack[14].m_obj;
lean_object* v___x_589_ = stack[15].m_obj;
lean_object* v_____x_590_ = stack[16].m_obj;
lean_object* v_res_601_;
v_res_601_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__17(v_u_574_, v_revertArgs_575_, v_00_u03c3s_576_, v_hyps_577_, v_target_578_, v_toPure_579_, v_inst_580_, v_toBind_581_, v_a_582_, v_n_583_, v_f_584_, v_k_585_, v_revertArgsTypes_586_, v___x_587_, v___f_588_, v___x_589_, v_____x_590_);
stack->m_obj
 = v_res_601_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__17___boxed(lean_object** _args){
lean_object* v_u_602_ = _args[0];
lean_object* v_revertArgs_603_ = _args[1];
lean_object* v_00_u03c3s_604_ = _args[2];
lean_object* v_hyps_605_ = _args[3];
lean_object* v_target_606_ = _args[4];
lean_object* v_toPure_607_ = _args[5];
lean_object* v_inst_608_ = _args[6];
lean_object* v_toBind_609_ = _args[7];
lean_object* v_a_610_ = _args[8];
lean_object* v_n_611_ = _args[9];
lean_object* v_f_612_ = _args[10];
lean_object* v_k_613_ = _args[11];
lean_object* v_revertArgsTypes_614_ = _args[12];
lean_object* v___x_615_ = _args[13];
lean_object* v___f_616_ = _args[14];
lean_object* v___x_617_ = _args[15];
lean_object* v_____x_618_ = _args[16];
_start:
{
lean_object* v_res_619_; 
v_res_619_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__17(v_u_602_, v_revertArgs_603_, v_00_u03c3s_604_, v_hyps_605_, v_target_606_, v_toPure_607_, v_inst_608_, v_toBind_609_, v_a_610_, v_n_611_, v_f_612_, v_k_613_, v_revertArgsTypes_614_, v___x_615_, v___f_616_, v___x_617_, v_____x_618_);
return v_res_619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__18(lean_object* v_inst_620_, lean_object* v_inst_621_, lean_object* v___f_622_, lean_object* v_toBind_623_, lean_object* v___f_624_, lean_object* v_declInfos_625_){
_start:
{
uint8_t v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_626_ = 0;
v___x_627_ = l_Lean_Meta_withLocalDeclsDND___redArg(v_inst_620_, v_inst_621_, v_declInfos_625_, v___f_622_, v___x_626_);
v___x_628_ = lean_apply_4(v_toBind_623_, lean_box(0), lean_box(0), v___x_627_, v___f_624_);
return v___x_628_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__19(lean_object* v_u_629_, lean_object* v_revertArgs_630_, lean_object* v_00_u03c3s_631_, lean_object* v_hyps_632_, lean_object* v_target_633_, lean_object* v_toPure_634_, lean_object* v_inst_635_, lean_object* v_toBind_636_, lean_object* v_a_637_, lean_object* v_n_638_, lean_object* v_f_639_, lean_object* v_k_640_, lean_object* v___x_641_, lean_object* v___f_642_, lean_object* v___x_643_, lean_object* v_inst_644_, lean_object* v_inst_645_, lean_object* v___f_646_, lean_object* v___f_647_, lean_object* v_revertArgsTypes_648_){
_start:
{
lean_object* v___f_649_; lean_object* v___f_650_; size_t v_sz_651_; size_t v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
lean_inc_ref_n(v_revertArgsTypes_648_, 2);
lean_inc_n(v_toBind_636_, 2);
v___f_649_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__17___boxed), 17, 16);
lean_closure_set(v___f_649_, 0, v_u_629_);
lean_closure_set(v___f_649_, 1, v_revertArgs_630_);
lean_closure_set(v___f_649_, 2, v_00_u03c3s_631_);
lean_closure_set(v___f_649_, 3, v_hyps_632_);
lean_closure_set(v___f_649_, 4, v_target_633_);
lean_closure_set(v___f_649_, 5, v_toPure_634_);
lean_closure_set(v___f_649_, 6, v_inst_635_);
lean_closure_set(v___f_649_, 7, v_toBind_636_);
lean_closure_set(v___f_649_, 8, v_a_637_);
lean_closure_set(v___f_649_, 9, v_n_638_);
lean_closure_set(v___f_649_, 10, v_f_639_);
lean_closure_set(v___f_649_, 11, v_k_640_);
lean_closure_set(v___f_649_, 12, v_revertArgsTypes_648_);
lean_closure_set(v___f_649_, 13, v___x_641_);
lean_closure_set(v___f_649_, 14, v___f_642_);
lean_closure_set(v___f_649_, 15, v___x_643_);
lean_inc_ref(v_inst_645_);
v___f_650_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__18), 6, 5);
lean_closure_set(v___f_650_, 0, v_inst_644_);
lean_closure_set(v___f_650_, 1, v_inst_645_);
lean_closure_set(v___f_650_, 2, v___f_646_);
lean_closure_set(v___f_650_, 3, v_toBind_636_);
lean_closure_set(v___f_650_, 4, v___f_649_);
v_sz_651_ = lean_array_size(v_revertArgsTypes_648_);
v___x_652_ = ((size_t)0ULL);
v___x_653_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_645_, v_revertArgsTypes_648_, v___f_647_, v_sz_651_, v___x_652_, v_revertArgsTypes_648_);
lean_dec_ref(v_revertArgsTypes_648_);
v___x_654_ = lean_apply_4(v_toBind_636_, lean_box(0), lean_box(0), v___x_653_, v___f_650_);
return v___x_654_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__19_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_629_ = stack[0].m_obj;
lean_object* v_revertArgs_630_ = stack[1].m_obj;
lean_object* v_00_u03c3s_631_ = stack[2].m_obj;
lean_object* v_hyps_632_ = stack[3].m_obj;
lean_object* v_target_633_ = stack[4].m_obj;
lean_object* v_toPure_634_ = stack[5].m_obj;
lean_object* v_inst_635_ = stack[6].m_obj;
lean_object* v_toBind_636_ = stack[7].m_obj;
lean_object* v_a_637_ = stack[8].m_obj;
lean_object* v_n_638_ = stack[9].m_obj;
lean_object* v_f_639_ = stack[10].m_obj;
lean_object* v_k_640_ = stack[11].m_obj;
lean_object* v___x_641_ = stack[12].m_obj;
lean_object* v___f_642_ = stack[13].m_obj;
lean_object* v___x_643_ = stack[14].m_obj;
lean_object* v_inst_644_ = stack[15].m_obj;
lean_object* v_inst_645_ = stack[16].m_obj;
lean_object* v___f_646_ = stack[17].m_obj;
lean_object* v___f_647_ = stack[18].m_obj;
lean_object* v_revertArgsTypes_648_ = stack[19].m_obj;
lean_object* v_res_655_;
v_res_655_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__19(v_u_629_, v_revertArgs_630_, v_00_u03c3s_631_, v_hyps_632_, v_target_633_, v_toPure_634_, v_inst_635_, v_toBind_636_, v_a_637_, v_n_638_, v_f_639_, v_k_640_, v___x_641_, v___f_642_, v___x_643_, v_inst_644_, v_inst_645_, v___f_646_, v___f_647_, v_revertArgsTypes_648_);
stack->m_obj
 = v_res_655_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__19___boxed(lean_object** _args){
lean_object* v_u_656_ = _args[0];
lean_object* v_revertArgs_657_ = _args[1];
lean_object* v_00_u03c3s_658_ = _args[2];
lean_object* v_hyps_659_ = _args[3];
lean_object* v_target_660_ = _args[4];
lean_object* v_toPure_661_ = _args[5];
lean_object* v_inst_662_ = _args[6];
lean_object* v_toBind_663_ = _args[7];
lean_object* v_a_664_ = _args[8];
lean_object* v_n_665_ = _args[9];
lean_object* v_f_666_ = _args[10];
lean_object* v_k_667_ = _args[11];
lean_object* v___x_668_ = _args[12];
lean_object* v___f_669_ = _args[13];
lean_object* v___x_670_ = _args[14];
lean_object* v_inst_671_ = _args[15];
lean_object* v_inst_672_ = _args[16];
lean_object* v___f_673_ = _args[17];
lean_object* v___f_674_ = _args[18];
lean_object* v_revertArgsTypes_675_ = _args[19];
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__19(v_u_656_, v_revertArgs_657_, v_00_u03c3s_658_, v_hyps_659_, v_target_660_, v_toPure_661_, v_inst_662_, v_toBind_663_, v_a_664_, v_n_665_, v_f_666_, v_k_667_, v___x_668_, v___f_669_, v___x_670_, v_inst_671_, v_inst_672_, v___f_673_, v___f_674_, v_revertArgsTypes_675_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20(lean_object* v_revertArgs_678_, lean_object* v___x_679_, lean_object* v_inst_680_, lean_object* v_toBind_681_, lean_object* v___f_682_, lean_object* v_____r_683_){
_start:
{
lean_object* v___x_684_; size_t v_sz_685_; size_t v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_684_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__0));
v_sz_685_ = lean_array_size(v_revertArgs_678_);
v___x_686_ = ((size_t)0ULL);
v___x_687_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_679_, v___x_684_, v_sz_685_, v___x_686_, v_revertArgs_678_);
v___x_688_ = lean_apply_2(v_inst_680_, lean_box(0), v___x_687_);
v___x_689_ = lean_apply_4(v_toBind_681_, lean_box(0), lean_box(0), v___x_688_, v___f_682_);
return v___x_689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__21(lean_object* v___f_690_, lean_object* v_____r_691_){
_start:
{
lean_object* v___x_692_; 
v___x_692_ = lean_apply_1(v___f_690_, v_____r_691_);
return v___x_692_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__3(void){
_start:
{
lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_697_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__2));
v___x_698_ = l_Lean_stringToMessageData(v___x_697_);
return v___x_698_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__5(void){
_start:
{
lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_700_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__4));
v___x_701_ = l_Lean_stringToMessageData(v___x_700_);
return v___x_701_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__7(void){
_start:
{
lean_object* v___x_703_; lean_object* v___x_704_; 
v___x_703_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__6));
v___x_704_ = l_Lean_stringToMessageData(v___x_703_);
return v___x_704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg(lean_object* v_inst_705_, lean_object* v_inst_706_, lean_object* v_inst_707_, lean_object* v_goal_708_, lean_object* v_n_709_, lean_object* v_hypName_710_, lean_object* v_k_711_){
_start:
{
lean_object* v___x_712_; lean_object* v_toApplicative_713_; lean_object* v_toFunctor_714_; lean_object* v_toSeq_715_; lean_object* v_toSeqLeft_716_; lean_object* v_toSeqRight_717_; lean_object* v___f_718_; lean_object* v___f_719_; lean_object* v___f_720_; lean_object* v___f_721_; lean_object* v___x_722_; lean_object* v___f_723_; lean_object* v___f_724_; lean_object* v___f_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v_toApplicative_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_813_; 
v___x_712_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__1);
v_toApplicative_713_ = lean_ctor_get(v___x_712_, 0);
v_toFunctor_714_ = lean_ctor_get(v_toApplicative_713_, 0);
v_toSeq_715_ = lean_ctor_get(v_toApplicative_713_, 2);
v_toSeqLeft_716_ = lean_ctor_get(v_toApplicative_713_, 3);
v_toSeqRight_717_ = lean_ctor_get(v_toApplicative_713_, 4);
v___f_718_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__2));
v___f_719_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_714_, 2);
v___f_720_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_720_, 0, v_toFunctor_714_);
v___f_721_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_721_, 0, v_toFunctor_714_);
v___x_722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_722_, 0, v___f_720_);
lean_ctor_set(v___x_722_, 1, v___f_721_);
lean_inc(v_toSeqRight_717_);
v___f_723_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_723_, 0, v_toSeqRight_717_);
lean_inc(v_toSeqLeft_716_);
v___f_724_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_724_, 0, v_toSeqLeft_716_);
lean_inc(v_toSeq_715_);
v___f_725_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_725_, 0, v_toSeq_715_);
v___x_726_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_726_, 0, v___x_722_);
lean_ctor_set(v___x_726_, 1, v___f_718_);
lean_ctor_set(v___x_726_, 2, v___f_725_);
lean_ctor_set(v___x_726_, 3, v___f_724_);
lean_ctor_set(v___x_726_, 4, v___f_723_);
v___x_727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_727_, 0, v___x_726_);
lean_ctor_set(v___x_727_, 1, v___f_719_);
v___x_728_ = l_StateRefT_x27_instMonad___redArg(v___x_727_);
v_toApplicative_729_ = lean_ctor_get(v___x_728_, 0);
v_isSharedCheck_813_ = !lean_is_exclusive(v___x_728_);
if (v_isSharedCheck_813_ == 0)
{
lean_object* v_unused_814_; 
v_unused_814_ = lean_ctor_get(v___x_728_, 1);
lean_dec(v_unused_814_);
v___x_731_ = v___x_728_;
v_isShared_732_ = v_isSharedCheck_813_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_toApplicative_729_);
lean_dec(v___x_728_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_813_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
lean_object* v_toFunctor_733_; lean_object* v_toSeq_734_; lean_object* v_toSeqLeft_735_; lean_object* v_toSeqRight_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_811_; 
v_toFunctor_733_ = lean_ctor_get(v_toApplicative_729_, 0);
v_toSeq_734_ = lean_ctor_get(v_toApplicative_729_, 2);
v_toSeqLeft_735_ = lean_ctor_get(v_toApplicative_729_, 3);
v_toSeqRight_736_ = lean_ctor_get(v_toApplicative_729_, 4);
v_isSharedCheck_811_ = !lean_is_exclusive(v_toApplicative_729_);
if (v_isSharedCheck_811_ == 0)
{
lean_object* v_unused_812_; 
v_unused_812_ = lean_ctor_get(v_toApplicative_729_, 1);
lean_dec(v_unused_812_);
v___x_738_ = v_toApplicative_729_;
v_isShared_739_ = v_isSharedCheck_811_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_toSeqRight_736_);
lean_inc(v_toSeqLeft_735_);
lean_inc(v_toSeq_734_);
lean_inc(v_toFunctor_733_);
lean_dec(v_toApplicative_729_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_811_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___f_740_; lean_object* v___f_741_; lean_object* v___f_742_; lean_object* v___f_743_; lean_object* v___x_744_; lean_object* v___f_745_; lean_object* v___f_746_; lean_object* v___f_747_; lean_object* v___x_749_; 
v___f_740_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__4));
v___f_741_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__5));
lean_inc_ref(v_toFunctor_733_);
v___f_742_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_742_, 0, v_toFunctor_733_);
v___f_743_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_743_, 0, v_toFunctor_733_);
v___x_744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_744_, 0, v___f_742_);
lean_ctor_set(v___x_744_, 1, v___f_743_);
v___f_745_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_745_, 0, v_toSeqRight_736_);
v___f_746_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_746_, 0, v_toSeqLeft_735_);
v___f_747_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_747_, 0, v_toSeq_734_);
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 4, v___f_745_);
lean_ctor_set(v___x_738_, 3, v___f_746_);
lean_ctor_set(v___x_738_, 2, v___f_747_);
lean_ctor_set(v___x_738_, 1, v___f_740_);
lean_ctor_set(v___x_738_, 0, v___x_744_);
v___x_749_ = v___x_738_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v___x_744_);
lean_ctor_set(v_reuseFailAlloc_810_, 1, v___f_740_);
lean_ctor_set(v_reuseFailAlloc_810_, 2, v___f_747_);
lean_ctor_set(v_reuseFailAlloc_810_, 3, v___f_746_);
lean_ctor_set(v_reuseFailAlloc_810_, 4, v___f_745_);
v___x_749_ = v_reuseFailAlloc_810_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
lean_object* v___x_751_; 
if (v_isShared_732_ == 0)
{
lean_ctor_set(v___x_731_, 1, v___f_741_);
lean_ctor_set(v___x_731_, 0, v___x_749_);
v___x_751_ = v___x_731_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v___x_749_);
lean_ctor_set(v_reuseFailAlloc_809_, 1, v___f_741_);
v___x_751_ = v_reuseFailAlloc_809_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v_toMonadRef_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v_toApplicative_758_; lean_object* v_toBind_759_; lean_object* v_toPure_760_; lean_object* v___x_761_; uint8_t v___x_762_; 
v___x_752_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__11, &l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__11_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__11);
v___x_753_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__17, &l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__17_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__17);
v_toMonadRef_754_ = lean_ctor_get(v___x_753_, 0);
v___x_755_ = l_Lean_Meta_instAddMessageContextMetaM;
lean_inc_ref(v___x_751_);
v___x_756_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___x_755_, v___x_751_);
lean_inc_ref(v_toMonadRef_754_);
v___x_757_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_757_, 0, v___x_752_);
lean_ctor_set(v___x_757_, 1, v_toMonadRef_754_);
lean_ctor_set(v___x_757_, 2, v___x_756_);
v_toApplicative_758_ = lean_ctor_get(v_inst_705_, 0);
v_toBind_759_ = lean_ctor_get(v_inst_705_, 1);
lean_inc(v_toBind_759_);
v_toPure_760_ = lean_ctor_get(v_toApplicative_758_, 1);
lean_inc(v_toPure_760_);
v___x_761_ = lean_unsigned_to_nat(0u);
v___x_762_ = lean_nat_dec_eq(v_n_709_, v___x_761_);
if (v___x_762_ == 0)
{
lean_object* v_u_763_; lean_object* v_00_u03c3s_764_; lean_object* v_hyps_765_; lean_object* v_target_766_; lean_object* v___f_767_; lean_object* v___f_768_; lean_object* v___f_769_; lean_object* v___f_770_; lean_object* v___f_771_; lean_object* v_T_772_; lean_object* v_f_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v_a_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v_revertArgs_780_; lean_object* v___x_781_; lean_object* v___f_782_; lean_object* v___f_783_; lean_object* v___f_784_; lean_object* v___x_785_; uint8_t v___x_786_; 
v_u_763_ = lean_ctor_get(v_goal_708_, 0);
lean_inc_n(v_u_763_, 3);
v_00_u03c3s_764_ = lean_ctor_get(v_goal_708_, 1);
lean_inc_ref_n(v_00_u03c3s_764_, 2);
v_hyps_765_ = lean_ctor_get(v_goal_708_, 2);
lean_inc_ref_n(v_hyps_765_, 2);
v_target_766_ = lean_ctor_get(v_goal_708_, 3);
lean_inc_ref(v_target_766_);
lean_dec_ref(v_goal_708_);
v___f_767_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__0));
lean_inc_n(v_inst_707_, 5);
v___f_768_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__1), 2, 1);
lean_closure_set(v___f_768_, 0, v_inst_707_);
lean_inc(v_hypName_710_);
v___f_769_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_769_, 0, v_hypName_710_);
lean_inc_n(v_toBind_759_, 4);
lean_inc_n(v_toPure_760_, 2);
v___f_770_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__5), 6, 3);
lean_closure_set(v___f_770_, 0, v_toPure_760_);
lean_closure_set(v___f_770_, 1, v_inst_707_);
lean_closure_set(v___f_770_, 2, v_toBind_759_);
v___f_771_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__6), 3, 1);
lean_closure_set(v___f_771_, 0, v_u_763_);
v_T_772_ = l_Lean_Expr_consumeMData(v_target_766_);
v_f_773_ = l_Lean_Expr_getAppFn(v_T_772_);
v___x_774_ = l_Lean_Expr_getAppNumArgs(v_T_772_);
v___x_775_ = lean_mk_empty_array_with_capacity(v___x_774_);
lean_dec(v___x_774_);
lean_inc_ref(v_T_772_);
v_a_776_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_T_772_, v___x_775_);
lean_inc_n(v_n_709_, 2);
lean_inc_ref(v_a_776_);
v___x_777_ = l_Array_toSubarray___redArg(v_a_776_, v___x_761_, v_n_709_);
v___x_778_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__1));
v___x_779_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_767_, v___x_777_, v___x_778_);
v_revertArgs_780_ = l_Array_reverse___redArg(v___x_779_);
v___x_781_ = lean_box(v___x_762_);
lean_inc_ref(v_inst_705_);
lean_inc_ref_n(v_revertArgs_780_, 3);
v___f_782_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__11___boxed), 13, 12);
lean_closure_set(v___f_782_, 0, v_u_763_);
lean_closure_set(v___f_782_, 1, v_00_u03c3s_764_);
lean_closure_set(v___f_782_, 2, v_hypName_710_);
lean_closure_set(v___f_782_, 3, v_toPure_760_);
lean_closure_set(v___f_782_, 4, v_hyps_765_);
lean_closure_set(v___f_782_, 5, v___x_781_);
lean_closure_set(v___f_782_, 6, v_inst_707_);
lean_closure_set(v___f_782_, 7, v_toBind_759_);
lean_closure_set(v___f_782_, 8, v___f_769_);
lean_closure_set(v___f_782_, 9, v_revertArgs_780_);
lean_closure_set(v___f_782_, 10, v_inst_705_);
lean_closure_set(v___f_782_, 11, v___f_768_);
lean_inc_ref_n(v___x_751_, 2);
v___f_783_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__19___boxed), 20, 19);
lean_closure_set(v___f_783_, 0, v_u_763_);
lean_closure_set(v___f_783_, 1, v_revertArgs_780_);
lean_closure_set(v___f_783_, 2, v_00_u03c3s_764_);
lean_closure_set(v___f_783_, 3, v_hyps_765_);
lean_closure_set(v___f_783_, 4, v_target_766_);
lean_closure_set(v___f_783_, 5, v_toPure_760_);
lean_closure_set(v___f_783_, 6, v_inst_707_);
lean_closure_set(v___f_783_, 7, v_toBind_759_);
lean_closure_set(v___f_783_, 8, v_a_776_);
lean_closure_set(v___f_783_, 9, v_n_709_);
lean_closure_set(v___f_783_, 10, v_f_773_);
lean_closure_set(v___f_783_, 11, v_k_711_);
lean_closure_set(v___f_783_, 12, v___x_761_);
lean_closure_set(v___f_783_, 13, v___f_771_);
lean_closure_set(v___f_783_, 14, v___x_751_);
lean_closure_set(v___f_783_, 15, v_inst_706_);
lean_closure_set(v___f_783_, 16, v_inst_705_);
lean_closure_set(v___f_783_, 17, v___f_782_);
lean_closure_set(v___f_783_, 18, v___f_770_);
lean_inc_ref(v___f_783_);
v___f_784_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20), 6, 5);
lean_closure_set(v___f_784_, 0, v_revertArgs_780_);
lean_closure_set(v___f_784_, 1, v___x_751_);
lean_closure_set(v___f_784_, 2, v_inst_707_);
lean_closure_set(v___f_784_, 3, v_toBind_759_);
lean_closure_set(v___f_784_, 4, v___f_783_);
v___x_785_ = lean_array_get_size(v_revertArgs_780_);
v___x_786_ = lean_nat_dec_eq(v___x_785_, v_n_709_);
if (v___x_786_ == 0)
{
lean_object* v___f_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; 
lean_dec_ref(v___f_783_);
lean_dec_ref(v_revertArgs_780_);
v___f_787_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__21), 2, 1);
lean_closure_set(v___f_787_, 0, v___f_784_);
v___x_788_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__3, &l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__3_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__3);
v___x_789_ = l_Nat_reprFast(v_n_709_);
v___x_790_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_790_, 0, v___x_789_);
v___x_791_ = l_Lean_MessageData_ofFormat(v___x_790_);
v___x_792_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_792_, 0, v___x_788_);
lean_ctor_set(v___x_792_, 1, v___x_791_);
v___x_793_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__5, &l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__5_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__5);
v___x_794_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_794_, 0, v___x_792_);
lean_ctor_set(v___x_794_, 1, v___x_793_);
v___x_795_ = l_Lean_MessageData_ofExpr(v_T_772_);
v___x_796_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_796_, 0, v___x_794_);
lean_ctor_set(v___x_796_, 1, v___x_795_);
v___x_797_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__7, &l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__7_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__7);
v___x_798_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_798_, 0, v___x_796_);
lean_ctor_set(v___x_798_, 1, v___x_797_);
v___x_799_ = l_Nat_reprFast(v___x_785_);
v___x_800_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_800_, 0, v___x_799_);
v___x_801_ = l_Lean_MessageData_ofFormat(v___x_800_);
v___x_802_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_802_, 0, v___x_798_);
lean_ctor_set(v___x_802_, 1, v___x_801_);
v___x_803_ = l_Lean_throwError___redArg(v___x_751_, v___x_757_, v___x_802_);
v___x_804_ = lean_apply_2(v_inst_707_, lean_box(0), v___x_803_);
v___x_805_ = lean_apply_4(v_toBind_759_, lean_box(0), lean_box(0), v___x_804_, v___f_787_);
return v___x_805_;
}
else
{
lean_object* v___x_806_; lean_object* v___x_807_; 
lean_dec_ref(v___f_784_);
lean_dec_ref(v_T_772_);
lean_dec_ref_known(v___x_757_, 3);
lean_dec(v_n_709_);
v___x_806_ = lean_box(0);
v___x_807_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20(v_revertArgs_780_, v___x_751_, v_inst_707_, v_toBind_759_, v___f_783_, v___x_806_);
return v___x_807_;
}
}
else
{
lean_object* v___x_808_; 
lean_dec(v_toPure_760_);
lean_dec(v_toBind_759_);
lean_dec_ref_known(v___x_757_, 3);
lean_dec_ref(v___x_751_);
lean_dec(v_hypName_710_);
lean_dec(v_n_709_);
lean_dec(v_inst_707_);
lean_dec_ref(v_inst_706_);
lean_dec_ref(v_inst_705_);
v___x_808_ = lean_apply_1(v_k_711_, v_goal_708_);
return v___x_808_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN(lean_object* v_m_815_, lean_object* v_inst_816_, lean_object* v_inst_817_, lean_object* v_inst_818_, lean_object* v_goal_819_, lean_object* v_n_820_, lean_object* v_hypName_821_, lean_object* v_k_822_){
_start:
{
lean_object* v___x_823_; 
v___x_823_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg(v_inst_816_, v_inst_817_, v_inst_818_, v_goal_819_, v_n_820_, v_hypName_821_, v_k_822_);
return v___x_823_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; 
v___x_824_ = lean_box(0);
v___x_825_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_826_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_826_, 0, v___x_825_);
lean_ctor_set(v___x_826_, 1, v___x_824_);
return v___x_826_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg(){
_start:
{
lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_828_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg___closed__0);
v___x_829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_829_, 0, v___x_828_);
return v___x_829_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_830_;
v_res_830_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg();
stack->m_obj
 = v_res_830_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg___boxed(lean_object* v___y_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg();
return v_res_832_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0(lean_object* v_00_u03b1_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_){
_start:
{
lean_object* v___x_843_; 
v___x_843_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg();
return v___x_843_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_834_ = stack[1].m_obj;
lean_object* v___y_835_ = stack[2].m_obj;
lean_object* v___y_836_ = stack[3].m_obj;
lean_object* v___y_837_ = stack[4].m_obj;
lean_object* v___y_838_ = stack[5].m_obj;
lean_object* v___y_839_ = stack[6].m_obj;
lean_object* v___y_840_ = stack[7].m_obj;
lean_object* v___y_841_ = stack[8].m_obj;
lean_object* v_res_844_;
v_res_844_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0(lean_box(0), v___y_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_);
stack->m_obj
 = v_res_844_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___boxed(lean_object* v_00_u03b1_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0(v_00_u03b1_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_, v___y_853_);
lean_dec(v___y_853_);
lean_dec_ref(v___y_852_);
lean_dec(v___y_851_);
lean_dec_ref(v___y_850_);
lean_dec(v___y_849_);
lean_dec_ref(v___y_848_);
lean_dec(v___y_847_);
lean_dec_ref(v___y_846_);
return v_res_855_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___redArg___lam__0(lean_object* v_x_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_){
_start:
{
lean_object* v___x_866_; 
lean_inc(v___y_860_);
lean_inc_ref(v___y_859_);
lean_inc(v___y_858_);
lean_inc_ref(v___y_857_);
v___x_866_ = lean_apply_9(v_x_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_, lean_box(0));
return v___x_866_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_856_ = stack[0].m_obj;
lean_object* v___y_857_ = stack[1].m_obj;
lean_object* v___y_858_ = stack[2].m_obj;
lean_object* v___y_859_ = stack[3].m_obj;
lean_object* v___y_860_ = stack[4].m_obj;
lean_object* v___y_861_ = stack[5].m_obj;
lean_object* v___y_862_ = stack[6].m_obj;
lean_object* v___y_863_ = stack[7].m_obj;
lean_object* v___y_864_ = stack[8].m_obj;
lean_object* v_res_867_;
v_res_867_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___redArg___lam__0(v_x_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_);
stack->m_obj
 = v_res_867_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___redArg___lam__0___boxed(lean_object* v_x_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_){
_start:
{
lean_object* v_res_878_; 
v_res_878_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___redArg___lam__0(v_x_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_, v___y_876_);
lean_dec(v___y_872_);
lean_dec_ref(v___y_871_);
lean_dec(v___y_870_);
lean_dec_ref(v___y_869_);
return v_res_878_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___redArg(lean_object* v_mvarId_879_, lean_object* v_x_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_){
_start:
{
lean_object* v___f_890_; lean_object* v___x_891_; 
lean_inc(v___y_884_);
lean_inc_ref(v___y_883_);
lean_inc(v___y_882_);
lean_inc_ref(v___y_881_);
v___f_890_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_890_, 0, v_x_880_);
lean_closure_set(v___f_890_, 1, v___y_881_);
lean_closure_set(v___f_890_, 2, v___y_882_);
lean_closure_set(v___f_890_, 3, v___y_883_);
lean_closure_set(v___f_890_, 4, v___y_884_);
v___x_891_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_879_, v___f_890_, v___y_885_, v___y_886_, v___y_887_, v___y_888_);
if (lean_obj_tag(v___x_891_) == 0)
{
return v___x_891_;
}
else
{
lean_object* v_a_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_899_; 
v_a_892_ = lean_ctor_get(v___x_891_, 0);
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_891_);
if (v_isSharedCheck_899_ == 0)
{
v___x_894_ = v___x_891_;
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_a_892_);
lean_dec(v___x_891_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v___x_897_; 
if (v_isShared_895_ == 0)
{
v___x_897_ = v___x_894_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_a_892_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
return v___x_897_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_879_ = stack[0].m_obj;
lean_object* v_x_880_ = stack[1].m_obj;
lean_object* v___y_881_ = stack[2].m_obj;
lean_object* v___y_882_ = stack[3].m_obj;
lean_object* v___y_883_ = stack[4].m_obj;
lean_object* v___y_884_ = stack[5].m_obj;
lean_object* v___y_885_ = stack[6].m_obj;
lean_object* v___y_886_ = stack[7].m_obj;
lean_object* v___y_887_ = stack[8].m_obj;
lean_object* v___y_888_ = stack[9].m_obj;
lean_object* v_res_900_;
v_res_900_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___redArg(v_mvarId_879_, v_x_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_);
stack->m_obj
 = v_res_900_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___redArg___boxed(lean_object* v_mvarId_901_, lean_object* v_x_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_){
_start:
{
lean_object* v_res_912_; 
v_res_912_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___redArg(v_mvarId_901_, v_x_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_);
lean_dec(v___y_910_);
lean_dec_ref(v___y_909_);
lean_dec(v___y_908_);
lean_dec_ref(v___y_907_);
lean_dec(v___y_906_);
lean_dec_ref(v___y_905_);
lean_dec(v___y_904_);
lean_dec_ref(v___y_903_);
return v_res_912_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3(lean_object* v_00_u03b1_913_, lean_object* v_mvarId_914_, lean_object* v_x_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_){
_start:
{
lean_object* v___x_925_; 
v___x_925_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___redArg(v_mvarId_914_, v_x_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_);
return v___x_925_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_914_ = stack[1].m_obj;
lean_object* v_x_915_ = stack[2].m_obj;
lean_object* v___y_916_ = stack[3].m_obj;
lean_object* v___y_917_ = stack[4].m_obj;
lean_object* v___y_918_ = stack[5].m_obj;
lean_object* v___y_919_ = stack[6].m_obj;
lean_object* v___y_920_ = stack[7].m_obj;
lean_object* v___y_921_ = stack[8].m_obj;
lean_object* v___y_922_ = stack[9].m_obj;
lean_object* v___y_923_ = stack[10].m_obj;
lean_object* v_res_926_;
v_res_926_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3(lean_box(0), v_mvarId_914_, v_x_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_);
stack->m_obj
 = v_res_926_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___boxed(lean_object* v_00_u03b1_927_, lean_object* v_mvarId_928_, lean_object* v_x_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_){
_start:
{
lean_object* v_res_939_; 
v_res_939_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3(v_00_u03b1_927_, v_mvarId_928_, v_x_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
lean_dec(v___y_937_);
lean_dec_ref(v___y_936_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
lean_dec(v___y_931_);
lean_dec_ref(v___y_930_);
return v_res_939_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__0(lean_object* v_val_940_, lean_object* v_newGoal_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_){
_start:
{
lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_951_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v_newGoal_941_);
v___x_952_ = lean_box(0);
v___x_953_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_951_, v___x_952_, v___y_946_, v___y_947_, v___y_948_, v___y_949_);
if (lean_obj_tag(v___x_953_) == 0)
{
lean_object* v_a_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_965_; 
v_a_954_ = lean_ctor_get(v___x_953_, 0);
v_isSharedCheck_965_ = !lean_is_exclusive(v___x_953_);
if (v_isSharedCheck_965_ == 0)
{
v___x_956_ = v___x_953_;
v_isShared_957_ = v_isSharedCheck_965_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_a_954_);
lean_dec(v___x_953_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_965_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_963_; 
v___x_958_ = lean_st_ref_take(v_val_940_);
v___x_959_ = l_Lean_Expr_mvarId_x21(v_a_954_);
v___x_960_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_960_, 0, v___x_959_);
lean_ctor_set(v___x_960_, 1, v___x_958_);
v___x_961_ = lean_st_ref_put(v_val_940_, v___x_960_);
if (v_isShared_957_ == 0)
{
v___x_963_ = v___x_956_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v_a_954_);
v___x_963_ = v_reuseFailAlloc_964_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
return v___x_963_;
}
}
}
else
{
return v___x_953_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_940_ = stack[0].m_obj;
lean_object* v_newGoal_941_ = stack[1].m_obj;
lean_object* v___y_942_ = stack[2].m_obj;
lean_object* v___y_943_ = stack[3].m_obj;
lean_object* v___y_944_ = stack[4].m_obj;
lean_object* v___y_945_ = stack[5].m_obj;
lean_object* v___y_946_ = stack[6].m_obj;
lean_object* v___y_947_ = stack[7].m_obj;
lean_object* v___y_948_ = stack[8].m_obj;
lean_object* v___y_949_ = stack[9].m_obj;
lean_object* v_res_966_;
v_res_966_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__0(v_val_940_, v_newGoal_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_);
stack->m_obj
 = v_res_966_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__0___boxed(lean_object* v_val_967_, lean_object* v_newGoal_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_){
_start:
{
lean_object* v_res_978_; 
v_res_978_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__0(v_val_967_, v_newGoal_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_);
lean_dec(v___y_976_);
lean_dec_ref(v___y_975_);
lean_dec(v___y_974_);
lean_dec_ref(v___y_973_);
lean_dec(v___y_972_);
lean_dec_ref(v___y_971_);
lean_dec(v___y_970_);
lean_dec_ref(v___y_969_);
lean_dec(v_val_967_);
return v_res_978_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14_spec__20_spec__22___redArg(lean_object* v_x_979_, lean_object* v_x_980_, lean_object* v_x_981_, lean_object* v_x_982_){
_start:
{
lean_object* v_ks_983_; lean_object* v_vs_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_1008_; 
v_ks_983_ = lean_ctor_get(v_x_979_, 0);
v_vs_984_ = lean_ctor_get(v_x_979_, 1);
v_isSharedCheck_1008_ = !lean_is_exclusive(v_x_979_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_986_ = v_x_979_;
v_isShared_987_ = v_isSharedCheck_1008_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_vs_984_);
lean_inc(v_ks_983_);
lean_dec(v_x_979_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_1008_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v___x_988_; uint8_t v___x_989_; 
v___x_988_ = lean_array_get_size(v_ks_983_);
v___x_989_ = lean_nat_dec_lt(v_x_980_, v___x_988_);
if (v___x_989_ == 0)
{
lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_993_; 
lean_dec(v_x_980_);
v___x_990_ = lean_array_push(v_ks_983_, v_x_981_);
v___x_991_ = lean_array_push(v_vs_984_, v_x_982_);
if (v_isShared_987_ == 0)
{
lean_ctor_set(v___x_986_, 1, v___x_991_);
lean_ctor_set(v___x_986_, 0, v___x_990_);
v___x_993_ = v___x_986_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v___x_990_);
lean_ctor_set(v_reuseFailAlloc_994_, 1, v___x_991_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
else
{
lean_object* v_k_x27_995_; uint8_t v___x_996_; 
v_k_x27_995_ = lean_array_fget_borrowed(v_ks_983_, v_x_980_);
v___x_996_ = l_Lean_instBEqMVarId_beq(v_x_981_, v_k_x27_995_);
if (v___x_996_ == 0)
{
lean_object* v___x_998_; 
if (v_isShared_987_ == 0)
{
v___x_998_ = v___x_986_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v_ks_983_);
lean_ctor_set(v_reuseFailAlloc_1002_, 1, v_vs_984_);
v___x_998_ = v_reuseFailAlloc_1002_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
lean_object* v___x_999_; lean_object* v___x_1000_; 
v___x_999_ = lean_unsigned_to_nat(1u);
v___x_1000_ = lean_nat_add(v_x_980_, v___x_999_);
lean_dec(v_x_980_);
v_x_979_ = v___x_998_;
v_x_980_ = v___x_1000_;
goto _start;
}
}
else
{
lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1006_; 
v___x_1003_ = lean_array_fset(v_ks_983_, v_x_980_, v_x_981_);
v___x_1004_ = lean_array_fset(v_vs_984_, v_x_980_, v_x_982_);
lean_dec(v_x_980_);
if (v_isShared_987_ == 0)
{
lean_ctor_set(v___x_986_, 1, v___x_1004_);
lean_ctor_set(v___x_986_, 0, v___x_1003_);
v___x_1006_ = v___x_986_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v___x_1003_);
lean_ctor_set(v_reuseFailAlloc_1007_, 1, v___x_1004_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14_spec__20___redArg(lean_object* v_n_1009_, lean_object* v_k_1010_, lean_object* v_v_1011_){
_start:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1012_ = lean_unsigned_to_nat(0u);
v___x_1013_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14_spec__20_spec__22___redArg(v_n_1009_, v___x_1012_, v_k_1010_, v_v_1011_);
return v___x_1013_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14___redArg___closed__0(void){
_start:
{
lean_object* v___x_1014_; 
v___x_1014_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1014_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14___redArg(lean_object* v_x_1015_, size_t v_x_1016_, size_t v_x_1017_, lean_object* v_x_1018_, lean_object* v_x_1019_){
_start:
{
if (lean_obj_tag(v_x_1015_) == 0)
{
lean_object* v_es_1020_; size_t v___x_1021_; size_t v___x_1022_; lean_object* v_j_1023_; lean_object* v___x_1024_; uint8_t v___x_1025_; 
v_es_1020_ = lean_ctor_get(v_x_1015_, 0);
v___x_1021_ = ((size_t)31ULL);
v___x_1022_ = lean_usize_land(v_x_1016_, v___x_1021_);
v_j_1023_ = lean_usize_to_nat(v___x_1022_);
v___x_1024_ = lean_array_get_size(v_es_1020_);
v___x_1025_ = lean_nat_dec_lt(v_j_1023_, v___x_1024_);
if (v___x_1025_ == 0)
{
lean_dec(v_j_1023_);
lean_dec(v_x_1019_);
lean_dec(v_x_1018_);
return v_x_1015_;
}
else
{
lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1064_; 
lean_inc_ref(v_es_1020_);
v_isSharedCheck_1064_ = !lean_is_exclusive(v_x_1015_);
if (v_isSharedCheck_1064_ == 0)
{
lean_object* v_unused_1065_; 
v_unused_1065_ = lean_ctor_get(v_x_1015_, 0);
lean_dec(v_unused_1065_);
v___x_1027_ = v_x_1015_;
v_isShared_1028_ = v_isSharedCheck_1064_;
goto v_resetjp_1026_;
}
else
{
lean_dec(v_x_1015_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1064_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v_v_1029_; lean_object* v___x_1030_; lean_object* v_xs_x27_1031_; lean_object* v___y_1033_; 
v_v_1029_ = lean_array_fget(v_es_1020_, v_j_1023_);
v___x_1030_ = lean_box(0);
v_xs_x27_1031_ = lean_array_fset(v_es_1020_, v_j_1023_, v___x_1030_);
switch(lean_obj_tag(v_v_1029_))
{
case 0:
{
lean_object* v_key_1038_; lean_object* v_val_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1049_; 
v_key_1038_ = lean_ctor_get(v_v_1029_, 0);
v_val_1039_ = lean_ctor_get(v_v_1029_, 1);
v_isSharedCheck_1049_ = !lean_is_exclusive(v_v_1029_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1041_ = v_v_1029_;
v_isShared_1042_ = v_isSharedCheck_1049_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_val_1039_);
lean_inc(v_key_1038_);
lean_dec(v_v_1029_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1049_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
uint8_t v___x_1043_; 
v___x_1043_ = l_Lean_instBEqMVarId_beq(v_x_1018_, v_key_1038_);
if (v___x_1043_ == 0)
{
lean_object* v___x_1044_; lean_object* v___x_1045_; 
lean_del_object(v___x_1041_);
v___x_1044_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1038_, v_val_1039_, v_x_1018_, v_x_1019_);
v___x_1045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1044_);
v___y_1033_ = v___x_1045_;
goto v___jp_1032_;
}
else
{
lean_object* v___x_1047_; 
lean_dec(v_val_1039_);
lean_dec(v_key_1038_);
if (v_isShared_1042_ == 0)
{
lean_ctor_set(v___x_1041_, 1, v_x_1019_);
lean_ctor_set(v___x_1041_, 0, v_x_1018_);
v___x_1047_ = v___x_1041_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v_x_1018_);
lean_ctor_set(v_reuseFailAlloc_1048_, 1, v_x_1019_);
v___x_1047_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
v___y_1033_ = v___x_1047_;
goto v___jp_1032_;
}
}
}
}
case 1:
{
lean_object* v_node_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1062_; 
v_node_1050_ = lean_ctor_get(v_v_1029_, 0);
v_isSharedCheck_1062_ = !lean_is_exclusive(v_v_1029_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_1052_ = v_v_1029_;
v_isShared_1053_ = v_isSharedCheck_1062_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_node_1050_);
lean_dec(v_v_1029_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1062_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
size_t v___x_1054_; size_t v___x_1055_; size_t v___x_1056_; size_t v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1060_; 
v___x_1054_ = ((size_t)5ULL);
v___x_1055_ = lean_usize_shift_right(v_x_1016_, v___x_1054_);
v___x_1056_ = ((size_t)1ULL);
v___x_1057_ = lean_usize_add(v_x_1017_, v___x_1056_);
v___x_1058_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14___redArg(v_node_1050_, v___x_1055_, v___x_1057_, v_x_1018_, v_x_1019_);
if (v_isShared_1053_ == 0)
{
lean_ctor_set(v___x_1052_, 0, v___x_1058_);
v___x_1060_ = v___x_1052_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v___x_1058_);
v___x_1060_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
v___y_1033_ = v___x_1060_;
goto v___jp_1032_;
}
}
}
default: 
{
lean_object* v___x_1063_; 
v___x_1063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1063_, 0, v_x_1018_);
lean_ctor_set(v___x_1063_, 1, v_x_1019_);
v___y_1033_ = v___x_1063_;
goto v___jp_1032_;
}
}
v___jp_1032_:
{
lean_object* v___x_1034_; lean_object* v___x_1036_; 
v___x_1034_ = lean_array_fset(v_xs_x27_1031_, v_j_1023_, v___y_1033_);
lean_dec(v_j_1023_);
if (v_isShared_1028_ == 0)
{
lean_ctor_set(v___x_1027_, 0, v___x_1034_);
v___x_1036_ = v___x_1027_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v___x_1034_);
v___x_1036_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
return v___x_1036_;
}
}
}
}
}
else
{
lean_object* v_ks_1066_; lean_object* v_vs_1067_; lean_object* v___x_1069_; uint8_t v_isShared_1070_; uint8_t v_isSharedCheck_1085_; 
v_ks_1066_ = lean_ctor_get(v_x_1015_, 0);
v_vs_1067_ = lean_ctor_get(v_x_1015_, 1);
v_isSharedCheck_1085_ = !lean_is_exclusive(v_x_1015_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1069_ = v_x_1015_;
v_isShared_1070_ = v_isSharedCheck_1085_;
goto v_resetjp_1068_;
}
else
{
lean_inc(v_vs_1067_);
lean_inc(v_ks_1066_);
lean_dec(v_x_1015_);
v___x_1069_ = lean_box(0);
v_isShared_1070_ = v_isSharedCheck_1085_;
goto v_resetjp_1068_;
}
v_resetjp_1068_:
{
lean_object* v___x_1072_; 
if (v_isShared_1070_ == 0)
{
v___x_1072_ = v___x_1069_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v_ks_1066_);
lean_ctor_set(v_reuseFailAlloc_1084_, 1, v_vs_1067_);
v___x_1072_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
lean_object* v_newNode_1073_; size_t v___x_1074_; uint8_t v___x_1075_; 
v_newNode_1073_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14_spec__20___redArg(v___x_1072_, v_x_1018_, v_x_1019_);
v___x_1074_ = ((size_t)7ULL);
v___x_1075_ = lean_usize_dec_le(v___x_1074_, v_x_1017_);
if (v___x_1075_ == 0)
{
lean_object* v___x_1076_; lean_object* v___x_1077_; uint8_t v___x_1078_; 
v___x_1076_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1073_);
v___x_1077_ = lean_unsigned_to_nat(4u);
v___x_1078_ = lean_nat_dec_lt(v___x_1076_, v___x_1077_);
lean_dec(v___x_1076_);
if (v___x_1078_ == 0)
{
lean_object* v_ks_1079_; lean_object* v_vs_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; 
v_ks_1079_ = lean_ctor_get(v_newNode_1073_, 0);
lean_inc_ref(v_ks_1079_);
v_vs_1080_ = lean_ctor_get(v_newNode_1073_, 1);
lean_inc_ref(v_vs_1080_);
lean_dec_ref(v_newNode_1073_);
v___x_1081_ = lean_unsigned_to_nat(0u);
v___x_1082_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14___redArg___closed__0);
v___x_1083_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14_spec__21___redArg(v_x_1017_, v_ks_1079_, v_vs_1080_, v___x_1081_, v___x_1082_);
lean_dec_ref(v_vs_1080_);
lean_dec_ref(v_ks_1079_);
return v___x_1083_;
}
else
{
return v_newNode_1073_;
}
}
else
{
return v_newNode_1073_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1015_ = stack[0].m_obj;
size_t v_x_1016_ = stack[1].m_num;
size_t v_x_1017_ = stack[2].m_num;
lean_object* v_x_1018_ = stack[3].m_obj;
lean_object* v_x_1019_ = stack[4].m_obj;
lean_object* v_res_1086_;
v_res_1086_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14___redArg(v_x_1015_, v_x_1016_, v_x_1017_, v_x_1018_, v_x_1019_);
stack->m_obj
 = v_res_1086_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14_spec__21___redArg(size_t v_depth_1087_, lean_object* v_keys_1088_, lean_object* v_vals_1089_, lean_object* v_i_1090_, lean_object* v_entries_1091_){
_start:
{
lean_object* v___x_1092_; uint8_t v___x_1093_; 
v___x_1092_ = lean_array_get_size(v_keys_1088_);
v___x_1093_ = lean_nat_dec_lt(v_i_1090_, v___x_1092_);
if (v___x_1093_ == 0)
{
lean_dec(v_i_1090_);
return v_entries_1091_;
}
else
{
lean_object* v_k_1094_; lean_object* v_v_1095_; uint64_t v___x_1096_; size_t v_h_1097_; size_t v___x_1098_; lean_object* v___x_1099_; size_t v___x_1100_; size_t v___x_1101_; size_t v___x_1102_; size_t v_h_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; 
v_k_1094_ = lean_array_fget_borrowed(v_keys_1088_, v_i_1090_);
v_v_1095_ = lean_array_fget_borrowed(v_vals_1089_, v_i_1090_);
v___x_1096_ = l_Lean_instHashableMVarId_hash(v_k_1094_);
v_h_1097_ = lean_uint64_to_usize(v___x_1096_);
v___x_1098_ = ((size_t)5ULL);
v___x_1099_ = lean_unsigned_to_nat(1u);
v___x_1100_ = ((size_t)1ULL);
v___x_1101_ = lean_usize_sub(v_depth_1087_, v___x_1100_);
v___x_1102_ = lean_usize_mul(v___x_1098_, v___x_1101_);
v_h_1103_ = lean_usize_shift_right(v_h_1097_, v___x_1102_);
v___x_1104_ = lean_nat_add(v_i_1090_, v___x_1099_);
lean_dec(v_i_1090_);
lean_inc(v_v_1095_);
lean_inc(v_k_1094_);
v___x_1105_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14___redArg(v_entries_1091_, v_h_1103_, v_depth_1087_, v_k_1094_, v_v_1095_);
v_i_1090_ = v___x_1104_;
v_entries_1091_ = v___x_1105_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14_spec__21___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_1087_ = stack[0].m_num;
lean_object* v_keys_1088_ = stack[1].m_obj;
lean_object* v_vals_1089_ = stack[2].m_obj;
lean_object* v_i_1090_ = stack[3].m_obj;
lean_object* v_entries_1091_ = stack[4].m_obj;
lean_object* v_res_1107_;
v_res_1107_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14_spec__21___redArg(v_depth_1087_, v_keys_1088_, v_vals_1089_, v_i_1090_, v_entries_1091_);
stack->m_obj
 = v_res_1107_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14_spec__21___redArg___boxed(lean_object* v_depth_1108_, lean_object* v_keys_1109_, lean_object* v_vals_1110_, lean_object* v_i_1111_, lean_object* v_entries_1112_){
_start:
{
size_t v_depth_boxed_1113_; lean_object* v_res_1114_; 
v_depth_boxed_1113_ = lean_unbox_usize(v_depth_1108_);
lean_dec(v_depth_1108_);
v_res_1114_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14_spec__21___redArg(v_depth_boxed_1113_, v_keys_1109_, v_vals_1110_, v_i_1111_, v_entries_1112_);
lean_dec_ref(v_vals_1110_);
lean_dec_ref(v_keys_1109_);
return v_res_1114_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14___redArg___boxed(lean_object* v_x_1115_, lean_object* v_x_1116_, lean_object* v_x_1117_, lean_object* v_x_1118_, lean_object* v_x_1119_){
_start:
{
size_t v_x_17149__boxed_1120_; size_t v_x_17150__boxed_1121_; lean_object* v_res_1122_; 
v_x_17149__boxed_1120_ = lean_unbox_usize(v_x_1116_);
lean_dec(v_x_1116_);
v_x_17150__boxed_1121_ = lean_unbox_usize(v_x_1117_);
lean_dec(v_x_1117_);
v_res_1122_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14___redArg(v_x_1115_, v_x_17149__boxed_1120_, v_x_17150__boxed_1121_, v_x_1118_, v_x_1119_);
return v_res_1122_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10___redArg(lean_object* v_x_1123_, lean_object* v_x_1124_, lean_object* v_x_1125_){
_start:
{
uint64_t v___x_1126_; size_t v___x_1127_; size_t v___x_1128_; lean_object* v___x_1129_; 
v___x_1126_ = l_Lean_instHashableMVarId_hash(v_x_1124_);
v___x_1127_ = lean_uint64_to_usize(v___x_1126_);
v___x_1128_ = ((size_t)1ULL);
v___x_1129_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14___redArg(v_x_1123_, v___x_1127_, v___x_1128_, v_x_1124_, v_x_1125_);
return v___x_1129_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2___redArg(lean_object* v_mvarId_1130_, lean_object* v_val_1131_, lean_object* v___y_1132_){
_start:
{
lean_object* v___x_1134_; lean_object* v_mctx_1135_; lean_object* v_cache_1136_; lean_object* v_zetaDeltaFVarIds_1137_; lean_object* v_postponed_1138_; lean_object* v_diag_1139_; lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1169_; 
v___x_1134_ = lean_st_ref_take(v___y_1132_);
v_mctx_1135_ = lean_ctor_get(v___x_1134_, 0);
v_cache_1136_ = lean_ctor_get(v___x_1134_, 1);
v_zetaDeltaFVarIds_1137_ = lean_ctor_get(v___x_1134_, 2);
v_postponed_1138_ = lean_ctor_get(v___x_1134_, 3);
v_diag_1139_ = lean_ctor_get(v___x_1134_, 4);
v_isSharedCheck_1169_ = !lean_is_exclusive(v___x_1134_);
if (v_isSharedCheck_1169_ == 0)
{
v___x_1141_ = v___x_1134_;
v_isShared_1142_ = v_isSharedCheck_1169_;
goto v_resetjp_1140_;
}
else
{
lean_inc(v_diag_1139_);
lean_inc(v_postponed_1138_);
lean_inc(v_zetaDeltaFVarIds_1137_);
lean_inc(v_cache_1136_);
lean_inc(v_mctx_1135_);
lean_dec(v___x_1134_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1169_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v_depth_1143_; lean_object* v_levelAssignDepth_1144_; lean_object* v_lmvarCounter_1145_; lean_object* v_mvarCounter_1146_; lean_object* v_lDecls_1147_; lean_object* v_decls_1148_; lean_object* v_userNames_1149_; lean_object* v_lAssignment_1150_; lean_object* v_eAssignment_1151_; lean_object* v_dAssignment_1152_; lean_object* v_instanceTypedMVars_1153_; lean_object* v_synthNormMemo_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1168_; 
v_depth_1143_ = lean_ctor_get(v_mctx_1135_, 0);
v_levelAssignDepth_1144_ = lean_ctor_get(v_mctx_1135_, 1);
v_lmvarCounter_1145_ = lean_ctor_get(v_mctx_1135_, 2);
v_mvarCounter_1146_ = lean_ctor_get(v_mctx_1135_, 3);
v_lDecls_1147_ = lean_ctor_get(v_mctx_1135_, 4);
v_decls_1148_ = lean_ctor_get(v_mctx_1135_, 5);
v_userNames_1149_ = lean_ctor_get(v_mctx_1135_, 6);
v_lAssignment_1150_ = lean_ctor_get(v_mctx_1135_, 7);
v_eAssignment_1151_ = lean_ctor_get(v_mctx_1135_, 8);
v_dAssignment_1152_ = lean_ctor_get(v_mctx_1135_, 9);
v_instanceTypedMVars_1153_ = lean_ctor_get(v_mctx_1135_, 10);
v_synthNormMemo_1154_ = lean_ctor_get(v_mctx_1135_, 11);
v_isSharedCheck_1168_ = !lean_is_exclusive(v_mctx_1135_);
if (v_isSharedCheck_1168_ == 0)
{
v___x_1156_ = v_mctx_1135_;
v_isShared_1157_ = v_isSharedCheck_1168_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_synthNormMemo_1154_);
lean_inc(v_instanceTypedMVars_1153_);
lean_inc(v_dAssignment_1152_);
lean_inc(v_eAssignment_1151_);
lean_inc(v_lAssignment_1150_);
lean_inc(v_userNames_1149_);
lean_inc(v_decls_1148_);
lean_inc(v_lDecls_1147_);
lean_inc(v_mvarCounter_1146_);
lean_inc(v_lmvarCounter_1145_);
lean_inc(v_levelAssignDepth_1144_);
lean_inc(v_depth_1143_);
lean_dec(v_mctx_1135_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1168_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1161_; 
v___x_1158_ = lean_box(0);
v___x_1159_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10___redArg(v_eAssignment_1151_, v_mvarId_1130_, v_val_1131_);
if (v_isShared_1157_ == 0)
{
lean_ctor_set(v___x_1156_, 8, v___x_1159_);
v___x_1161_ = v___x_1156_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v_depth_1143_);
lean_ctor_set(v_reuseFailAlloc_1167_, 1, v_levelAssignDepth_1144_);
lean_ctor_set(v_reuseFailAlloc_1167_, 2, v_lmvarCounter_1145_);
lean_ctor_set(v_reuseFailAlloc_1167_, 3, v_mvarCounter_1146_);
lean_ctor_set(v_reuseFailAlloc_1167_, 4, v_lDecls_1147_);
lean_ctor_set(v_reuseFailAlloc_1167_, 5, v_decls_1148_);
lean_ctor_set(v_reuseFailAlloc_1167_, 6, v_userNames_1149_);
lean_ctor_set(v_reuseFailAlloc_1167_, 7, v_lAssignment_1150_);
lean_ctor_set(v_reuseFailAlloc_1167_, 8, v___x_1159_);
lean_ctor_set(v_reuseFailAlloc_1167_, 9, v_dAssignment_1152_);
lean_ctor_set(v_reuseFailAlloc_1167_, 10, v_instanceTypedMVars_1153_);
lean_ctor_set(v_reuseFailAlloc_1167_, 11, v_synthNormMemo_1154_);
v___x_1161_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
lean_object* v___x_1163_; 
if (v_isShared_1142_ == 0)
{
lean_ctor_set(v___x_1141_, 0, v___x_1161_);
v___x_1163_ = v___x_1141_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v___x_1161_);
lean_ctor_set(v_reuseFailAlloc_1166_, 1, v_cache_1136_);
lean_ctor_set(v_reuseFailAlloc_1166_, 2, v_zetaDeltaFVarIds_1137_);
lean_ctor_set(v_reuseFailAlloc_1166_, 3, v_postponed_1138_);
lean_ctor_set(v_reuseFailAlloc_1166_, 4, v_diag_1139_);
v___x_1163_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; 
v___x_1164_ = lean_st_ref_put(v___y_1132_, v___x_1163_);
v___x_1165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1165_, 0, v___x_1158_);
return v___x_1165_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1130_ = stack[0].m_obj;
lean_object* v_val_1131_ = stack[1].m_obj;
lean_object* v___y_1132_ = stack[2].m_obj;
lean_object* v_res_1170_;
v_res_1170_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2___redArg(v_mvarId_1130_, v_val_1131_, v___y_1132_);
stack->m_obj
 = v_res_1170_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2___redArg___boxed(lean_object* v_mvarId_1171_, lean_object* v_val_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_){
_start:
{
lean_object* v_res_1175_; 
v_res_1175_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2___redArg(v_mvarId_1171_, v_val_1172_, v___y_1173_);
lean_dec(v___y_1173_);
return v_res_1175_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5_spec__14(lean_object* v_msgData_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_){
_start:
{
lean_object* v___x_1182_; lean_object* v_env_1183_; uint8_t v___x_1184_; lean_object* v_env_1185_; lean_object* v___x_1186_; lean_object* v_toCold_1187_; lean_object* v_mctx_1188_; lean_object* v_lctx_1189_; lean_object* v_options_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; 
v___x_1182_ = lean_st_ref_get(v___y_1180_);
v_env_1183_ = lean_ctor_get(v___x_1182_, 0);
lean_inc_ref(v_env_1183_);
lean_dec(v___x_1182_);
v___x_1184_ = 0;
v_env_1185_ = l_Lean_Environment_setRecordingDeps(v_env_1183_, v___x_1184_);
v___x_1186_ = lean_st_ref_get(v___y_1178_);
v_toCold_1187_ = lean_ctor_get(v___y_1179_, 0);
v_mctx_1188_ = lean_ctor_get(v___x_1186_, 0);
lean_inc_ref(v_mctx_1188_);
lean_dec(v___x_1186_);
v_lctx_1189_ = lean_ctor_get(v___y_1177_, 2);
v_options_1190_ = lean_ctor_get(v_toCold_1187_, 2);
lean_inc_ref(v_options_1190_);
lean_inc_ref(v_lctx_1189_);
v___x_1191_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1191_, 0, v_env_1185_);
lean_ctor_set(v___x_1191_, 1, v_mctx_1188_);
lean_ctor_set(v___x_1191_, 2, v_lctx_1189_);
lean_ctor_set(v___x_1191_, 3, v_options_1190_);
v___x_1192_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1192_, 0, v___x_1191_);
lean_ctor_set(v___x_1192_, 1, v_msgData_1176_);
v___x_1193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1193_, 0, v___x_1192_);
return v___x_1193_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5_spec__14_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1176_ = stack[0].m_obj;
lean_object* v___y_1177_ = stack[1].m_obj;
lean_object* v___y_1178_ = stack[2].m_obj;
lean_object* v___y_1179_ = stack[3].m_obj;
lean_object* v___y_1180_ = stack[4].m_obj;
lean_object* v_res_1194_;
v_res_1194_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5_spec__14(v_msgData_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_);
stack->m_obj
 = v_res_1194_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5_spec__14___boxed(lean_object* v_msgData_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_){
_start:
{
lean_object* v_res_1201_; 
v_res_1201_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5_spec__14(v_msgData_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_);
lean_dec(v___y_1199_);
lean_dec_ref(v___y_1198_);
lean_dec(v___y_1197_);
lean_dec_ref(v___y_1196_);
return v_res_1201_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__8___redArg(lean_object* v_msg_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_){
_start:
{
lean_object* v_ref_1208_; lean_object* v___x_1209_; lean_object* v_a_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1218_; 
v_ref_1208_ = lean_ctor_get(v___y_1205_, 2);
v___x_1209_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5_spec__14(v_msg_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_);
v_a_1210_ = lean_ctor_get(v___x_1209_, 0);
v_isSharedCheck_1218_ = !lean_is_exclusive(v___x_1209_);
if (v_isSharedCheck_1218_ == 0)
{
v___x_1212_ = v___x_1209_;
v_isShared_1213_ = v_isSharedCheck_1218_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_a_1210_);
lean_dec(v___x_1209_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1218_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v___x_1214_; lean_object* v___x_1216_; 
lean_inc(v_ref_1208_);
v___x_1214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1214_, 0, v_ref_1208_);
lean_ctor_set(v___x_1214_, 1, v_a_1210_);
if (v_isShared_1213_ == 0)
{
lean_ctor_set_tag(v___x_1212_, 1);
lean_ctor_set(v___x_1212_, 0, v___x_1214_);
v___x_1216_ = v___x_1212_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v___x_1214_);
v___x_1216_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
return v___x_1216_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1202_ = stack[0].m_obj;
lean_object* v___y_1203_ = stack[1].m_obj;
lean_object* v___y_1204_ = stack[2].m_obj;
lean_object* v___y_1205_ = stack[3].m_obj;
lean_object* v___y_1206_ = stack[4].m_obj;
lean_object* v_res_1219_;
v_res_1219_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__8___redArg(v_msg_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_);
stack->m_obj
 = v_res_1219_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__8___redArg___boxed(lean_object* v_msg_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_){
_start:
{
lean_object* v_res_1226_; 
v_res_1226_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__8___redArg(v_msg_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_);
lean_dec(v___y_1224_);
lean_dec_ref(v___y_1223_);
lean_dec(v___y_1222_);
lean_dec_ref(v___y_1221_);
return v_res_1226_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__7(lean_object* v_u_1227_, lean_object* v_as_1228_, size_t v_i_1229_, size_t v_stop_1230_, lean_object* v_b_1231_){
_start:
{
uint8_t v___x_1232_; 
v___x_1232_ = lean_usize_dec_eq(v_i_1229_, v_stop_1230_);
if (v___x_1232_ == 0)
{
size_t v___x_1233_; size_t v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; 
v___x_1233_ = ((size_t)1ULL);
v___x_1234_ = lean_usize_sub(v_i_1229_, v___x_1233_);
v___x_1235_ = lean_array_uget_borrowed(v_as_1228_, v___x_1234_);
lean_inc(v___x_1235_);
lean_inc(v_u_1227_);
v___x_1236_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkCons(v_u_1227_, v___x_1235_, v_b_1231_);
v_i_1229_ = v___x_1234_;
v_b_1231_ = v___x_1236_;
goto _start;
}
else
{
lean_dec(v_u_1227_);
return v_b_1231_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_1227_ = stack[0].m_obj;
lean_object* v_as_1228_ = stack[1].m_obj;
size_t v_i_1229_ = stack[2].m_num;
size_t v_stop_1230_ = stack[3].m_num;
lean_object* v_b_1231_ = stack[4].m_obj;
lean_object* v_res_1238_;
v_res_1238_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__7(v_u_1227_, v_as_1228_, v_i_1229_, v_stop_1230_, v_b_1231_);
stack->m_obj
 = v_res_1238_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__7___boxed(lean_object* v_u_1239_, lean_object* v_as_1240_, lean_object* v_i_1241_, lean_object* v_stop_1242_, lean_object* v_b_1243_){
_start:
{
size_t v_i_boxed_1244_; size_t v_stop_boxed_1245_; lean_object* v_res_1246_; 
v_i_boxed_1244_ = lean_unbox_usize(v_i_1241_);
lean_dec(v_i_1241_);
v_stop_boxed_1245_ = lean_unbox_usize(v_stop_1242_);
lean_dec(v_stop_1242_);
v_res_1246_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__7(v_u_1239_, v_as_1240_, v_i_boxed_1244_, v_stop_boxed_1245_, v_b_1243_);
lean_dec_ref(v_as_1240_);
return v_res_1246_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__6(size_t v_sz_1247_, size_t v_i_1248_, lean_object* v_bs_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_){
_start:
{
uint8_t v___x_1255_; 
v___x_1255_ = lean_usize_dec_lt(v_i_1248_, v_sz_1247_);
if (v___x_1255_ == 0)
{
lean_object* v___x_1256_; 
v___x_1256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1256_, 0, v_bs_1249_);
return v___x_1256_;
}
else
{
lean_object* v_v_1257_; lean_object* v___x_1258_; lean_object* v_bs_x27_1259_; lean_object* v___x_1260_; 
v_v_1257_ = lean_array_uget(v_bs_1249_, v_i_1248_);
v___x_1258_ = lean_unsigned_to_nat(0u);
v_bs_x27_1259_ = lean_array_uset(v_bs_1249_, v_i_1248_, v___x_1258_);
v___x_1260_ = l_Lean_Meta_mkEqRefl(v_v_1257_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_);
if (lean_obj_tag(v___x_1260_) == 0)
{
lean_object* v_a_1261_; size_t v___x_1262_; size_t v___x_1263_; lean_object* v___x_1264_; 
v_a_1261_ = lean_ctor_get(v___x_1260_, 0);
lean_inc(v_a_1261_);
lean_dec_ref_known(v___x_1260_, 1);
v___x_1262_ = ((size_t)1ULL);
v___x_1263_ = lean_usize_add(v_i_1248_, v___x_1262_);
v___x_1264_ = lean_array_uset(v_bs_x27_1259_, v_i_1248_, v_a_1261_);
v_i_1248_ = v___x_1263_;
v_bs_1249_ = v___x_1264_;
goto _start;
}
else
{
lean_object* v_a_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1273_; 
lean_dec_ref(v_bs_x27_1259_);
v_a_1266_ = lean_ctor_get(v___x_1260_, 0);
v_isSharedCheck_1273_ = !lean_is_exclusive(v___x_1260_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1268_ = v___x_1260_;
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_a_1266_);
lean_dec(v___x_1260_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1271_; 
if (v_isShared_1269_ == 0)
{
v___x_1271_ = v___x_1268_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_a_1266_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__6_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1247_ = stack[0].m_num;
size_t v_i_1248_ = stack[1].m_num;
lean_object* v_bs_1249_ = stack[2].m_obj;
lean_object* v___y_1250_ = stack[3].m_obj;
lean_object* v___y_1251_ = stack[4].m_obj;
lean_object* v___y_1252_ = stack[5].m_obj;
lean_object* v___y_1253_ = stack[6].m_obj;
lean_object* v_res_1274_;
v_res_1274_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__6(v_sz_1247_, v_i_1248_, v_bs_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_);
stack->m_obj
 = v_res_1274_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__6___boxed(lean_object* v_sz_1275_, lean_object* v_i_1276_, lean_object* v_bs_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_){
_start:
{
size_t v_sz_boxed_1283_; size_t v_i_boxed_1284_; lean_object* v_res_1285_; 
v_sz_boxed_1283_ = lean_unbox_usize(v_sz_1275_);
lean_dec(v_sz_1275_);
v_i_boxed_1284_ = lean_unbox_usize(v_i_1276_);
lean_dec(v_i_1276_);
v_res_1285_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__6(v_sz_boxed_1283_, v_i_boxed_1284_, v_bs_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_);
lean_dec(v___y_1281_);
lean_dec_ref(v___y_1280_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1278_);
return v_res_1285_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__4___redArg(size_t v_sz_1286_, size_t v_i_1287_, lean_object* v_bs_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_){
_start:
{
uint8_t v___x_1292_; 
v___x_1292_ = lean_usize_dec_lt(v_i_1287_, v_sz_1286_);
if (v___x_1292_ == 0)
{
lean_object* v___x_1293_; 
v___x_1293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1293_, 0, v_bs_1288_);
return v___x_1293_;
}
else
{
lean_object* v_v_1294_; lean_object* v___x_1295_; lean_object* v_bs_x27_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; 
v_v_1294_ = lean_array_uget(v_bs_1288_, v_i_1287_);
v___x_1295_ = lean_unsigned_to_nat(0u);
v_bs_x27_1296_ = lean_array_uset(v_bs_1288_, v_i_1287_, v___x_1295_);
v___x_1297_ = lean_usize_to_nat(v_i_1287_);
v___x_1298_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__5___closed__1));
v___x_1299_ = l_Lean_Core_mkFreshUserName(v___x_1298_, v___y_1289_, v___y_1290_);
if (lean_obj_tag(v___x_1299_) == 0)
{
lean_object* v_a_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; size_t v___x_1305_; size_t v___x_1306_; lean_object* v___x_1307_; 
v_a_1300_ = lean_ctor_get(v___x_1299_, 0);
lean_inc(v_a_1300_);
lean_dec_ref_known(v___x_1299_, 1);
v___x_1301_ = lean_unsigned_to_nat(1u);
v___x_1302_ = lean_nat_add(v___x_1297_, v___x_1301_);
lean_dec(v___x_1297_);
v___x_1303_ = lean_name_append_index_after(v_a_1300_, v___x_1302_);
v___x_1304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1304_, 0, v___x_1303_);
lean_ctor_set(v___x_1304_, 1, v_v_1294_);
v___x_1305_ = ((size_t)1ULL);
v___x_1306_ = lean_usize_add(v_i_1287_, v___x_1305_);
v___x_1307_ = lean_array_uset(v_bs_x27_1296_, v_i_1287_, v___x_1304_);
v_i_1287_ = v___x_1306_;
v_bs_1288_ = v___x_1307_;
goto _start;
}
else
{
lean_object* v_a_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1316_; 
lean_dec(v___x_1297_);
lean_dec_ref(v_bs_x27_1296_);
lean_dec(v_v_1294_);
v_a_1309_ = lean_ctor_get(v___x_1299_, 0);
v_isSharedCheck_1316_ = !lean_is_exclusive(v___x_1299_);
if (v_isSharedCheck_1316_ == 0)
{
v___x_1311_ = v___x_1299_;
v_isShared_1312_ = v_isSharedCheck_1316_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_a_1309_);
lean_dec(v___x_1299_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1316_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v___x_1314_; 
if (v_isShared_1312_ == 0)
{
v___x_1314_ = v___x_1311_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v_a_1309_);
v___x_1314_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
return v___x_1314_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1286_ = stack[0].m_num;
size_t v_i_1287_ = stack[1].m_num;
lean_object* v_bs_1288_ = stack[2].m_obj;
lean_object* v___y_1289_ = stack[3].m_obj;
lean_object* v___y_1290_ = stack[4].m_obj;
lean_object* v_res_1317_;
v_res_1317_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__4___redArg(v_sz_1286_, v_i_1287_, v_bs_1288_, v___y_1289_, v___y_1290_);
stack->m_obj
 = v_res_1317_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__4___redArg___boxed(lean_object* v_sz_1318_, lean_object* v_i_1319_, lean_object* v_bs_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_){
_start:
{
size_t v_sz_boxed_1324_; size_t v_i_boxed_1325_; lean_object* v_res_1326_; 
v_sz_boxed_1324_ = lean_unbox_usize(v_sz_1318_);
lean_dec(v_sz_1318_);
v_i_boxed_1325_ = lean_unbox_usize(v_i_1319_);
lean_dec(v_i_1319_);
v_res_1326_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__4___redArg(v_sz_boxed_1324_, v_i_boxed_1325_, v_bs_1320_, v___y_1321_, v___y_1322_);
lean_dec(v___y_1322_);
lean_dec_ref(v___y_1321_);
return v_res_1326_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__1___redArg(lean_object* v_a_1327_, lean_object* v_b_1328_){
_start:
{
lean_object* v_array_1329_; lean_object* v_start_1330_; lean_object* v_stop_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1344_; 
v_array_1329_ = lean_ctor_get(v_a_1327_, 0);
v_start_1330_ = lean_ctor_get(v_a_1327_, 1);
v_stop_1331_ = lean_ctor_get(v_a_1327_, 2);
v_isSharedCheck_1344_ = !lean_is_exclusive(v_a_1327_);
if (v_isSharedCheck_1344_ == 0)
{
v___x_1333_ = v_a_1327_;
v_isShared_1334_ = v_isSharedCheck_1344_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_stop_1331_);
lean_inc(v_start_1330_);
lean_inc(v_array_1329_);
lean_dec(v_a_1327_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1344_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
uint8_t v___x_1335_; 
v___x_1335_ = lean_nat_dec_lt(v_start_1330_, v_stop_1331_);
if (v___x_1335_ == 0)
{
lean_del_object(v___x_1333_);
lean_dec(v_stop_1331_);
lean_dec(v_start_1330_);
lean_dec_ref(v_array_1329_);
return v_b_1328_;
}
else
{
lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1339_; 
v___x_1336_ = lean_unsigned_to_nat(1u);
v___x_1337_ = lean_nat_add(v_start_1330_, v___x_1336_);
lean_inc_ref(v_array_1329_);
if (v_isShared_1334_ == 0)
{
lean_ctor_set(v___x_1333_, 1, v___x_1337_);
v___x_1339_ = v___x_1333_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v_array_1329_);
lean_ctor_set(v_reuseFailAlloc_1343_, 1, v___x_1337_);
lean_ctor_set(v_reuseFailAlloc_1343_, 2, v_stop_1331_);
v___x_1339_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
lean_object* v___x_1340_; lean_object* v___x_1341_; 
v___x_1340_ = lean_array_fget(v_array_1329_, v_start_1330_);
lean_dec(v_start_1330_);
lean_dec_ref(v_array_1329_);
v___x_1341_ = lean_array_push(v_b_1328_, v___x_1340_);
v_a_1327_ = v___x_1339_;
v_b_1328_ = v___x_1341_;
goto _start;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___lam__0(lean_object* v___x_1345_, lean_object* v___x_1346_, lean_object* v_a_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_){
_start:
{
lean_object* v___x_16690__overap_1357_; lean_object* v___x_1358_; 
v___x_16690__overap_1357_ = l_instInhabitedOfMonad___redArg(v___x_1345_, v___x_1346_);
lean_inc(v___y_1355_);
lean_inc_ref(v___y_1354_);
lean_inc(v___y_1353_);
lean_inc_ref(v___y_1352_);
lean_inc(v___y_1351_);
lean_inc_ref(v___y_1350_);
lean_inc(v___y_1349_);
lean_inc_ref(v___y_1348_);
v___x_1358_ = lean_apply_9(v___x_16690__overap_1357_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, lean_box(0));
return v___x_1358_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1345_ = stack[0].m_obj;
lean_object* v___x_1346_ = stack[1].m_obj;
lean_object* v_a_1347_ = stack[2].m_obj;
lean_object* v___y_1348_ = stack[3].m_obj;
lean_object* v___y_1349_ = stack[4].m_obj;
lean_object* v___y_1350_ = stack[5].m_obj;
lean_object* v___y_1351_ = stack[6].m_obj;
lean_object* v___y_1352_ = stack[7].m_obj;
lean_object* v___y_1353_ = stack[8].m_obj;
lean_object* v___y_1354_ = stack[9].m_obj;
lean_object* v___y_1355_ = stack[10].m_obj;
lean_object* v_res_1359_;
v_res_1359_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___lam__0(v___x_1345_, v___x_1346_, v_a_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
stack->m_obj
 = v_res_1359_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___lam__0___boxed(lean_object* v___x_1360_, lean_object* v___x_1361_, lean_object* v_a_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_){
_start:
{
lean_object* v_res_1372_; 
v_res_1372_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___lam__0(v___x_1360_, v___x_1361_, v_a_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_);
lean_dec(v___y_1370_);
lean_dec_ref(v___y_1369_);
lean_dec(v___y_1368_);
lean_dec_ref(v___y_1367_);
lean_dec(v___y_1366_);
lean_dec_ref(v___y_1365_);
lean_dec(v___y_1364_);
lean_dec_ref(v___y_1363_);
lean_dec_ref(v_a_1362_);
return v_res_1372_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19_spec__21___redArg___lam__0(lean_object* v_k_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v_b_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_){
_start:
{
lean_object* v___x_1384_; 
lean_inc(v___y_1382_);
lean_inc_ref(v___y_1381_);
lean_inc(v___y_1380_);
lean_inc_ref(v___y_1379_);
lean_inc(v___y_1377_);
lean_inc_ref(v___y_1376_);
lean_inc(v___y_1375_);
lean_inc_ref(v___y_1374_);
v___x_1384_ = lean_apply_10(v_k_1373_, v_b_1378_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, lean_box(0));
return v___x_1384_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19_spec__21___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1373_ = stack[0].m_obj;
lean_object* v___y_1374_ = stack[1].m_obj;
lean_object* v___y_1375_ = stack[2].m_obj;
lean_object* v___y_1376_ = stack[3].m_obj;
lean_object* v___y_1377_ = stack[4].m_obj;
lean_object* v_b_1378_ = stack[5].m_obj;
lean_object* v___y_1379_ = stack[6].m_obj;
lean_object* v___y_1380_ = stack[7].m_obj;
lean_object* v___y_1381_ = stack[8].m_obj;
lean_object* v___y_1382_ = stack[9].m_obj;
lean_object* v_res_1385_;
v_res_1385_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19_spec__21___redArg___lam__0(v_k_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v_b_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_);
stack->m_obj
 = v_res_1385_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19_spec__21___redArg___lam__0___boxed(lean_object* v_k_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v_b_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_){
_start:
{
lean_object* v_res_1397_; 
v_res_1397_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19_spec__21___redArg___lam__0(v_k_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v_b_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_);
lean_dec(v___y_1395_);
lean_dec_ref(v___y_1394_);
lean_dec(v___y_1393_);
lean_dec_ref(v___y_1392_);
lean_dec(v___y_1390_);
lean_dec_ref(v___y_1389_);
lean_dec(v___y_1388_);
lean_dec_ref(v___y_1387_);
return v_res_1397_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19_spec__21___redArg(lean_object* v_name_1398_, uint8_t v_bi_1399_, lean_object* v_type_1400_, lean_object* v_k_1401_, uint8_t v_kind_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_){
_start:
{
lean_object* v___f_1412_; lean_object* v___x_1413_; 
lean_inc(v___y_1406_);
lean_inc_ref(v___y_1405_);
lean_inc(v___y_1404_);
lean_inc_ref(v___y_1403_);
v___f_1412_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19_spec__21___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_1412_, 0, v_k_1401_);
lean_closure_set(v___f_1412_, 1, v___y_1403_);
lean_closure_set(v___f_1412_, 2, v___y_1404_);
lean_closure_set(v___f_1412_, 3, v___y_1405_);
lean_closure_set(v___f_1412_, 4, v___y_1406_);
v___x_1413_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1398_, v_bi_1399_, v_type_1400_, v___f_1412_, v_kind_1402_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_);
if (lean_obj_tag(v___x_1413_) == 0)
{
return v___x_1413_;
}
else
{
lean_object* v_a_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1421_; 
v_a_1414_ = lean_ctor_get(v___x_1413_, 0);
v_isSharedCheck_1421_ = !lean_is_exclusive(v___x_1413_);
if (v_isSharedCheck_1421_ == 0)
{
v___x_1416_ = v___x_1413_;
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_a_1414_);
lean_dec(v___x_1413_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v___x_1419_; 
if (v_isShared_1417_ == 0)
{
v___x_1419_ = v___x_1416_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v_a_1414_);
v___x_1419_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
return v___x_1419_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19_spec__21___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1398_ = stack[0].m_obj;
uint8_t v_bi_1399_ = stack[1].m_num;
lean_object* v_type_1400_ = stack[2].m_obj;
lean_object* v_k_1401_ = stack[3].m_obj;
uint8_t v_kind_1402_ = stack[4].m_num;
lean_object* v___y_1403_ = stack[5].m_obj;
lean_object* v___y_1404_ = stack[6].m_obj;
lean_object* v___y_1405_ = stack[7].m_obj;
lean_object* v___y_1406_ = stack[8].m_obj;
lean_object* v___y_1407_ = stack[9].m_obj;
lean_object* v___y_1408_ = stack[10].m_obj;
lean_object* v___y_1409_ = stack[11].m_obj;
lean_object* v___y_1410_ = stack[12].m_obj;
lean_object* v_res_1422_;
v_res_1422_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19_spec__21___redArg(v_name_1398_, v_bi_1399_, v_type_1400_, v_k_1401_, v_kind_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_);
stack->m_obj
 = v_res_1422_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19_spec__21___redArg___boxed(lean_object* v_name_1423_, lean_object* v_bi_1424_, lean_object* v_type_1425_, lean_object* v_k_1426_, lean_object* v_kind_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_){
_start:
{
uint8_t v_bi_boxed_1437_; uint8_t v_kind_boxed_1438_; lean_object* v_res_1439_; 
v_bi_boxed_1437_ = lean_unbox(v_bi_1424_);
v_kind_boxed_1438_ = lean_unbox(v_kind_1427_);
v_res_1439_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19_spec__21___redArg(v_name_1423_, v_bi_boxed_1437_, v_type_1425_, v_k_1426_, v_kind_boxed_1438_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_);
lean_dec(v___y_1435_);
lean_dec_ref(v___y_1434_);
lean_dec(v___y_1433_);
lean_dec_ref(v___y_1432_);
lean_dec(v___y_1431_);
lean_dec_ref(v___y_1430_);
lean_dec(v___y_1429_);
lean_dec_ref(v___y_1428_);
return v_res_1439_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___lam__1___boxed(lean_object* v_acc_1444_, lean_object* v_declInfos_1445_, lean_object* v_k_1446_, lean_object* v_kind_1447_, lean_object* v_x_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_){
_start:
{
uint8_t v_kind_boxed_1458_; lean_object* v_res_1459_; 
v_kind_boxed_1458_ = lean_unbox(v_kind_1447_);
v_res_1459_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___lam__1(v_acc_1444_, v_declInfos_1445_, v_k_1446_, v_kind_boxed_1458_, v_x_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_);
lean_dec(v___y_1456_);
lean_dec_ref(v___y_1455_);
lean_dec(v___y_1454_);
lean_dec_ref(v___y_1453_);
lean_dec(v___y_1452_);
lean_dec_ref(v___y_1451_);
lean_dec(v___y_1450_);
lean_dec_ref(v___y_1449_);
return v_res_1459_;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19(lean_object* v_declInfos_1460_, lean_object* v_k_1461_, uint8_t v_kind_1462_, lean_object* v_acc_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_){
_start:
{
lean_object* v___x_1473_; lean_object* v_toApplicative_1474_; lean_object* v_toFunctor_1475_; lean_object* v_toSeq_1476_; lean_object* v_toSeqLeft_1477_; lean_object* v_toSeqRight_1478_; lean_object* v___f_1479_; lean_object* v___f_1480_; lean_object* v___f_1481_; lean_object* v___f_1482_; lean_object* v___x_1483_; lean_object* v___f_1484_; lean_object* v___f_1485_; lean_object* v___f_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v_toApplicative_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1608_; 
v___x_1473_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__1);
v_toApplicative_1474_ = lean_ctor_get(v___x_1473_, 0);
v_toFunctor_1475_ = lean_ctor_get(v_toApplicative_1474_, 0);
v_toSeq_1476_ = lean_ctor_get(v_toApplicative_1474_, 2);
v_toSeqLeft_1477_ = lean_ctor_get(v_toApplicative_1474_, 3);
v_toSeqRight_1478_ = lean_ctor_get(v_toApplicative_1474_, 4);
v___f_1479_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__2));
v___f_1480_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_1475_, 2);
v___f_1481_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1481_, 0, v_toFunctor_1475_);
v___f_1482_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1482_, 0, v_toFunctor_1475_);
v___x_1483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1483_, 0, v___f_1481_);
lean_ctor_set(v___x_1483_, 1, v___f_1482_);
lean_inc(v_toSeqRight_1478_);
v___f_1484_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1484_, 0, v_toSeqRight_1478_);
lean_inc(v_toSeqLeft_1477_);
v___f_1485_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1485_, 0, v_toSeqLeft_1477_);
lean_inc(v_toSeq_1476_);
v___f_1486_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1486_, 0, v_toSeq_1476_);
v___x_1487_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1487_, 0, v___x_1483_);
lean_ctor_set(v___x_1487_, 1, v___f_1479_);
lean_ctor_set(v___x_1487_, 2, v___f_1486_);
lean_ctor_set(v___x_1487_, 3, v___f_1485_);
lean_ctor_set(v___x_1487_, 4, v___f_1484_);
v___x_1488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1488_, 0, v___x_1487_);
lean_ctor_set(v___x_1488_, 1, v___f_1480_);
v___x_1489_ = l_StateRefT_x27_instMonad___redArg(v___x_1488_);
v_toApplicative_1490_ = lean_ctor_get(v___x_1489_, 0);
v_isSharedCheck_1608_ = !lean_is_exclusive(v___x_1489_);
if (v_isSharedCheck_1608_ == 0)
{
lean_object* v_unused_1609_; 
v_unused_1609_ = lean_ctor_get(v___x_1489_, 1);
lean_dec(v_unused_1609_);
v___x_1492_ = v___x_1489_;
v_isShared_1493_ = v_isSharedCheck_1608_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_toApplicative_1490_);
lean_dec(v___x_1489_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1608_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
lean_object* v_toFunctor_1494_; lean_object* v_toSeq_1495_; lean_object* v_toSeqLeft_1496_; lean_object* v_toSeqRight_1497_; lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1606_; 
v_toFunctor_1494_ = lean_ctor_get(v_toApplicative_1490_, 0);
v_toSeq_1495_ = lean_ctor_get(v_toApplicative_1490_, 2);
v_toSeqLeft_1496_ = lean_ctor_get(v_toApplicative_1490_, 3);
v_toSeqRight_1497_ = lean_ctor_get(v_toApplicative_1490_, 4);
v_isSharedCheck_1606_ = !lean_is_exclusive(v_toApplicative_1490_);
if (v_isSharedCheck_1606_ == 0)
{
lean_object* v_unused_1607_; 
v_unused_1607_ = lean_ctor_get(v_toApplicative_1490_, 1);
lean_dec(v_unused_1607_);
v___x_1499_ = v_toApplicative_1490_;
v_isShared_1500_ = v_isSharedCheck_1606_;
goto v_resetjp_1498_;
}
else
{
lean_inc(v_toSeqRight_1497_);
lean_inc(v_toSeqLeft_1496_);
lean_inc(v_toSeq_1495_);
lean_inc(v_toFunctor_1494_);
lean_dec(v_toApplicative_1490_);
v___x_1499_ = lean_box(0);
v_isShared_1500_ = v_isSharedCheck_1606_;
goto v_resetjp_1498_;
}
v_resetjp_1498_:
{
lean_object* v___f_1501_; lean_object* v___f_1502_; lean_object* v___f_1503_; lean_object* v___f_1504_; lean_object* v___x_1505_; lean_object* v___f_1506_; lean_object* v___f_1507_; lean_object* v___f_1508_; lean_object* v___x_1510_; 
v___f_1501_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__4));
v___f_1502_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__5));
lean_inc_ref(v_toFunctor_1494_);
v___f_1503_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1503_, 0, v_toFunctor_1494_);
v___f_1504_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1504_, 0, v_toFunctor_1494_);
v___x_1505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1505_, 0, v___f_1503_);
lean_ctor_set(v___x_1505_, 1, v___f_1504_);
v___f_1506_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1506_, 0, v_toSeqRight_1497_);
v___f_1507_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1507_, 0, v_toSeqLeft_1496_);
v___f_1508_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1508_, 0, v_toSeq_1495_);
if (v_isShared_1500_ == 0)
{
lean_ctor_set(v___x_1499_, 4, v___f_1506_);
lean_ctor_set(v___x_1499_, 3, v___f_1507_);
lean_ctor_set(v___x_1499_, 2, v___f_1508_);
lean_ctor_set(v___x_1499_, 1, v___f_1501_);
lean_ctor_set(v___x_1499_, 0, v___x_1505_);
v___x_1510_ = v___x_1499_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v___x_1505_);
lean_ctor_set(v_reuseFailAlloc_1605_, 1, v___f_1501_);
lean_ctor_set(v_reuseFailAlloc_1605_, 2, v___f_1508_);
lean_ctor_set(v_reuseFailAlloc_1605_, 3, v___f_1507_);
lean_ctor_set(v_reuseFailAlloc_1605_, 4, v___f_1506_);
v___x_1510_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
lean_object* v___x_1512_; 
if (v_isShared_1493_ == 0)
{
lean_ctor_set(v___x_1492_, 1, v___f_1502_);
lean_ctor_set(v___x_1492_, 0, v___x_1510_);
v___x_1512_ = v___x_1492_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v___x_1510_);
lean_ctor_set(v_reuseFailAlloc_1604_, 1, v___f_1502_);
v___x_1512_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
lean_object* v___x_1513_; lean_object* v_toApplicative_1514_; lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1602_; 
v___x_1513_ = l_StateRefT_x27_instMonad___redArg(v___x_1512_);
v_toApplicative_1514_ = lean_ctor_get(v___x_1513_, 0);
v_isSharedCheck_1602_ = !lean_is_exclusive(v___x_1513_);
if (v_isSharedCheck_1602_ == 0)
{
lean_object* v_unused_1603_; 
v_unused_1603_ = lean_ctor_get(v___x_1513_, 1);
lean_dec(v_unused_1603_);
v___x_1516_ = v___x_1513_;
v_isShared_1517_ = v_isSharedCheck_1602_;
goto v_resetjp_1515_;
}
else
{
lean_inc(v_toApplicative_1514_);
lean_dec(v___x_1513_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1602_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
lean_object* v_toFunctor_1518_; lean_object* v_toSeq_1519_; lean_object* v_toSeqLeft_1520_; lean_object* v_toSeqRight_1521_; lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1600_; 
v_toFunctor_1518_ = lean_ctor_get(v_toApplicative_1514_, 0);
v_toSeq_1519_ = lean_ctor_get(v_toApplicative_1514_, 2);
v_toSeqLeft_1520_ = lean_ctor_get(v_toApplicative_1514_, 3);
v_toSeqRight_1521_ = lean_ctor_get(v_toApplicative_1514_, 4);
v_isSharedCheck_1600_ = !lean_is_exclusive(v_toApplicative_1514_);
if (v_isSharedCheck_1600_ == 0)
{
lean_object* v_unused_1601_; 
v_unused_1601_ = lean_ctor_get(v_toApplicative_1514_, 1);
lean_dec(v_unused_1601_);
v___x_1523_ = v_toApplicative_1514_;
v_isShared_1524_ = v_isSharedCheck_1600_;
goto v_resetjp_1522_;
}
else
{
lean_inc(v_toSeqRight_1521_);
lean_inc(v_toSeqLeft_1520_);
lean_inc(v_toSeq_1519_);
lean_inc(v_toFunctor_1518_);
lean_dec(v_toApplicative_1514_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1600_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
lean_object* v___f_1525_; lean_object* v___f_1526_; lean_object* v___f_1527_; lean_object* v___f_1528_; lean_object* v___x_1529_; lean_object* v___f_1530_; lean_object* v___f_1531_; lean_object* v___f_1532_; lean_object* v___x_1534_; 
v___f_1525_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___closed__0));
v___f_1526_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___closed__1));
lean_inc_ref(v_toFunctor_1518_);
v___f_1527_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1527_, 0, v_toFunctor_1518_);
v___f_1528_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1528_, 0, v_toFunctor_1518_);
v___x_1529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1529_, 0, v___f_1527_);
lean_ctor_set(v___x_1529_, 1, v___f_1528_);
v___f_1530_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1530_, 0, v_toSeqRight_1521_);
v___f_1531_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1531_, 0, v_toSeqLeft_1520_);
v___f_1532_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1532_, 0, v_toSeq_1519_);
if (v_isShared_1524_ == 0)
{
lean_ctor_set(v___x_1523_, 4, v___f_1530_);
lean_ctor_set(v___x_1523_, 3, v___f_1531_);
lean_ctor_set(v___x_1523_, 2, v___f_1532_);
lean_ctor_set(v___x_1523_, 1, v___f_1525_);
lean_ctor_set(v___x_1523_, 0, v___x_1529_);
v___x_1534_ = v___x_1523_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v___x_1529_);
lean_ctor_set(v_reuseFailAlloc_1599_, 1, v___f_1525_);
lean_ctor_set(v_reuseFailAlloc_1599_, 2, v___f_1532_);
lean_ctor_set(v_reuseFailAlloc_1599_, 3, v___f_1531_);
lean_ctor_set(v_reuseFailAlloc_1599_, 4, v___f_1530_);
v___x_1534_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
lean_object* v___x_1536_; 
if (v_isShared_1517_ == 0)
{
lean_ctor_set(v___x_1516_, 1, v___f_1526_);
lean_ctor_set(v___x_1516_, 0, v___x_1534_);
v___x_1536_ = v___x_1516_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v___x_1534_);
lean_ctor_set(v_reuseFailAlloc_1598_, 1, v___f_1526_);
v___x_1536_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
lean_object* v___x_1537_; lean_object* v_toApplicative_1538_; lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1596_; 
v___x_1537_ = l_StateRefT_x27_instMonad___redArg(v___x_1536_);
v_toApplicative_1538_ = lean_ctor_get(v___x_1537_, 0);
v_isSharedCheck_1596_ = !lean_is_exclusive(v___x_1537_);
if (v_isSharedCheck_1596_ == 0)
{
lean_object* v_unused_1597_; 
v_unused_1597_ = lean_ctor_get(v___x_1537_, 1);
lean_dec(v_unused_1597_);
v___x_1540_ = v___x_1537_;
v_isShared_1541_ = v_isSharedCheck_1596_;
goto v_resetjp_1539_;
}
else
{
lean_inc(v_toApplicative_1538_);
lean_dec(v___x_1537_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1596_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
lean_object* v_toFunctor_1542_; lean_object* v_toSeq_1543_; lean_object* v_toSeqLeft_1544_; lean_object* v_toSeqRight_1545_; lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1594_; 
v_toFunctor_1542_ = lean_ctor_get(v_toApplicative_1538_, 0);
v_toSeq_1543_ = lean_ctor_get(v_toApplicative_1538_, 2);
v_toSeqLeft_1544_ = lean_ctor_get(v_toApplicative_1538_, 3);
v_toSeqRight_1545_ = lean_ctor_get(v_toApplicative_1538_, 4);
v_isSharedCheck_1594_ = !lean_is_exclusive(v_toApplicative_1538_);
if (v_isSharedCheck_1594_ == 0)
{
lean_object* v_unused_1595_; 
v_unused_1595_ = lean_ctor_get(v_toApplicative_1538_, 1);
lean_dec(v_unused_1595_);
v___x_1547_ = v_toApplicative_1538_;
v_isShared_1548_ = v_isSharedCheck_1594_;
goto v_resetjp_1546_;
}
else
{
lean_inc(v_toSeqRight_1545_);
lean_inc(v_toSeqLeft_1544_);
lean_inc(v_toSeq_1543_);
lean_inc(v_toFunctor_1542_);
lean_dec(v_toApplicative_1538_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1594_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
lean_object* v___f_1549_; lean_object* v___f_1550_; lean_object* v___f_1551_; lean_object* v___f_1552_; lean_object* v___x_1553_; lean_object* v___f_1554_; lean_object* v___f_1555_; lean_object* v___f_1556_; lean_object* v___x_1558_; 
v___f_1549_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___closed__2));
v___f_1550_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___closed__3));
lean_inc_ref(v_toFunctor_1542_);
v___f_1551_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1551_, 0, v_toFunctor_1542_);
v___f_1552_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1552_, 0, v_toFunctor_1542_);
v___x_1553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1553_, 0, v___f_1551_);
lean_ctor_set(v___x_1553_, 1, v___f_1552_);
v___f_1554_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1554_, 0, v_toSeqRight_1545_);
v___f_1555_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1555_, 0, v_toSeqLeft_1544_);
v___f_1556_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1556_, 0, v_toSeq_1543_);
if (v_isShared_1548_ == 0)
{
lean_ctor_set(v___x_1547_, 4, v___f_1554_);
lean_ctor_set(v___x_1547_, 3, v___f_1555_);
lean_ctor_set(v___x_1547_, 2, v___f_1556_);
lean_ctor_set(v___x_1547_, 1, v___f_1549_);
lean_ctor_set(v___x_1547_, 0, v___x_1553_);
v___x_1558_ = v___x_1547_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v___x_1553_);
lean_ctor_set(v_reuseFailAlloc_1593_, 1, v___f_1549_);
lean_ctor_set(v_reuseFailAlloc_1593_, 2, v___f_1556_);
lean_ctor_set(v_reuseFailAlloc_1593_, 3, v___f_1555_);
lean_ctor_set(v_reuseFailAlloc_1593_, 4, v___f_1554_);
v___x_1558_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
lean_object* v___x_1560_; 
if (v_isShared_1541_ == 0)
{
lean_ctor_set(v___x_1540_, 1, v___f_1550_);
lean_ctor_set(v___x_1540_, 0, v___x_1558_);
v___x_1560_ = v___x_1540_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v___x_1558_);
lean_ctor_set(v_reuseFailAlloc_1592_, 1, v___f_1550_);
v___x_1560_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
lean_object* v___x_1561_; lean_object* v___x_1562_; uint8_t v___x_1563_; 
v___x_1561_ = lean_array_get_size(v_acc_1463_);
v___x_1562_ = lean_array_get_size(v_declInfos_1460_);
v___x_1563_ = lean_nat_dec_lt(v___x_1561_, v___x_1562_);
if (v___x_1563_ == 0)
{
lean_object* v___x_1564_; 
lean_dec_ref(v___x_1560_);
lean_dec_ref(v_declInfos_1460_);
lean_inc(v___y_1471_);
lean_inc_ref(v___y_1470_);
lean_inc(v___y_1469_);
lean_inc_ref(v___y_1468_);
lean_inc(v___y_1467_);
lean_inc_ref(v___y_1466_);
lean_inc(v___y_1465_);
lean_inc_ref(v___y_1464_);
v___x_1564_ = lean_apply_10(v_k_1461_, v_acc_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_, lean_box(0));
return v___x_1564_;
}
else
{
lean_object* v___x_1565_; uint8_t v___x_1566_; lean_object* v___x_1567_; lean_object* v___f_1568_; lean_object* v___f_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v_snd_1574_; lean_object* v_fst_1575_; lean_object* v_fst_1576_; lean_object* v_snd_1577_; lean_object* v___x_1578_; lean_object* v___f_1579_; lean_object* v___x_1580_; 
v___x_1565_ = lean_box(0);
v___x_1566_ = 0;
v___x_1567_ = l_Lean_instInhabitedExpr;
v___f_1568_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___lam__0___boxed), 12, 2);
lean_closure_set(v___f_1568_, 0, v___x_1560_);
lean_closure_set(v___f_1568_, 1, v___x_1567_);
v___f_1569_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1569_, 0, v___f_1568_);
v___x_1570_ = lean_box(v___x_1566_);
v___x_1571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1571_, 0, v___x_1570_);
lean_ctor_set(v___x_1571_, 1, v___f_1569_);
v___x_1572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1572_, 0, v___x_1565_);
lean_ctor_set(v___x_1572_, 1, v___x_1571_);
v___x_1573_ = lean_array_get(v___x_1572_, v_declInfos_1460_, v___x_1561_);
lean_dec_ref_known(v___x_1572_, 2);
v_snd_1574_ = lean_ctor_get(v___x_1573_, 1);
lean_inc(v_snd_1574_);
v_fst_1575_ = lean_ctor_get(v___x_1573_, 0);
lean_inc(v_fst_1575_);
lean_dec(v___x_1573_);
v_fst_1576_ = lean_ctor_get(v_snd_1574_, 0);
lean_inc(v_fst_1576_);
v_snd_1577_ = lean_ctor_get(v_snd_1574_, 1);
lean_inc(v_snd_1577_);
lean_dec(v_snd_1574_);
v___x_1578_ = lean_box(v_kind_1462_);
lean_inc_ref(v_acc_1463_);
v___f_1579_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___lam__1___boxed), 14, 4);
lean_closure_set(v___f_1579_, 0, v_acc_1463_);
lean_closure_set(v___f_1579_, 1, v_declInfos_1460_);
lean_closure_set(v___f_1579_, 2, v_k_1461_);
lean_closure_set(v___f_1579_, 3, v___x_1578_);
lean_inc(v___y_1471_);
lean_inc_ref(v___y_1470_);
lean_inc(v___y_1469_);
lean_inc_ref(v___y_1468_);
lean_inc(v___y_1467_);
lean_inc_ref(v___y_1466_);
lean_inc(v___y_1465_);
lean_inc_ref(v___y_1464_);
v___x_1580_ = lean_apply_10(v_snd_1577_, v_acc_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_, lean_box(0));
if (lean_obj_tag(v___x_1580_) == 0)
{
lean_object* v_a_1581_; uint8_t v___x_1582_; lean_object* v___x_1583_; 
v_a_1581_ = lean_ctor_get(v___x_1580_, 0);
lean_inc(v_a_1581_);
lean_dec_ref_known(v___x_1580_, 1);
v___x_1582_ = lean_unbox(v_fst_1576_);
lean_dec(v_fst_1576_);
v___x_1583_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19_spec__21___redArg(v_fst_1575_, v___x_1582_, v_a_1581_, v___f_1579_, v_kind_1462_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_);
return v___x_1583_;
}
else
{
lean_object* v_a_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1591_; 
lean_dec_ref(v___f_1579_);
lean_dec(v_fst_1576_);
lean_dec(v_fst_1575_);
v_a_1584_ = lean_ctor_get(v___x_1580_, 0);
v_isSharedCheck_1591_ = !lean_is_exclusive(v___x_1580_);
if (v_isSharedCheck_1591_ == 0)
{
v___x_1586_ = v___x_1580_;
v_isShared_1587_ = v_isSharedCheck_1591_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_a_1584_);
lean_dec(v___x_1580_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1591_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v___x_1589_; 
if (v_isShared_1587_ == 0)
{
v___x_1589_ = v___x_1586_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v_a_1584_);
v___x_1589_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
return v___x_1589_;
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
LEAN_EXPORT void l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19_0interp(lean_interpreter_value* stack)
{
lean_object* v_declInfos_1460_ = stack[0].m_obj;
lean_object* v_k_1461_ = stack[1].m_obj;
uint8_t v_kind_1462_ = stack[2].m_num;
lean_object* v_acc_1463_ = stack[3].m_obj;
lean_object* v___y_1464_ = stack[4].m_obj;
lean_object* v___y_1465_ = stack[5].m_obj;
lean_object* v___y_1466_ = stack[6].m_obj;
lean_object* v___y_1467_ = stack[7].m_obj;
lean_object* v___y_1468_ = stack[8].m_obj;
lean_object* v___y_1469_ = stack[9].m_obj;
lean_object* v___y_1470_ = stack[10].m_obj;
lean_object* v___y_1471_ = stack[11].m_obj;
lean_object* v_res_1610_;
v_res_1610_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19(v_declInfos_1460_, v_k_1461_, v_kind_1462_, v_acc_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_);
stack->m_obj
 = v_res_1610_;
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___lam__1(lean_object* v_acc_1611_, lean_object* v_declInfos_1612_, lean_object* v_k_1613_, uint8_t v_kind_1614_, lean_object* v_x_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_){
_start:
{
lean_object* v___x_1625_; lean_object* v___x_1626_; 
v___x_1625_ = lean_array_push(v_acc_1611_, v_x_1615_);
v___x_1626_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19(v_declInfos_1612_, v_k_1613_, v_kind_1614_, v___x_1625_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_);
return v___x_1626_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_acc_1611_ = stack[0].m_obj;
lean_object* v_declInfos_1612_ = stack[1].m_obj;
lean_object* v_k_1613_ = stack[2].m_obj;
uint8_t v_kind_1614_ = stack[3].m_num;
lean_object* v_x_1615_ = stack[4].m_obj;
lean_object* v___y_1616_ = stack[5].m_obj;
lean_object* v___y_1617_ = stack[6].m_obj;
lean_object* v___y_1618_ = stack[7].m_obj;
lean_object* v___y_1619_ = stack[8].m_obj;
lean_object* v___y_1620_ = stack[9].m_obj;
lean_object* v___y_1621_ = stack[10].m_obj;
lean_object* v___y_1622_ = stack[11].m_obj;
lean_object* v___y_1623_ = stack[12].m_obj;
lean_object* v_res_1627_;
v_res_1627_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___lam__1(v_acc_1611_, v_declInfos_1612_, v_k_1613_, v_kind_1614_, v_x_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_);
stack->m_obj
 = v_res_1627_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___boxed(lean_object* v_declInfos_1628_, lean_object* v_k_1629_, lean_object* v_kind_1630_, lean_object* v_acc_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_){
_start:
{
uint8_t v_kind_boxed_1641_; lean_object* v_res_1642_; 
v_kind_boxed_1641_ = lean_unbox(v_kind_1630_);
v_res_1642_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19(v_declInfos_1628_, v_k_1629_, v_kind_boxed_1641_, v_acc_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_);
lean_dec(v___y_1639_);
lean_dec_ref(v___y_1638_);
lean_dec(v___y_1637_);
lean_dec_ref(v___y_1636_);
lean_dec(v___y_1635_);
lean_dec_ref(v___y_1634_);
lean_dec(v___y_1633_);
lean_dec_ref(v___y_1632_);
return v_res_1642_;
}
}
lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14(lean_object* v_declInfos_1643_, lean_object* v_k_1644_, uint8_t v_kind_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_){
_start:
{
lean_object* v___x_1655_; lean_object* v___x_1656_; 
v___x_1655_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__1));
v___x_1656_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19(v_declInfos_1643_, v_k_1644_, v_kind_1645_, v___x_1655_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_);
return v___x_1656_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_0interp(lean_interpreter_value* stack)
{
lean_object* v_declInfos_1643_ = stack[0].m_obj;
lean_object* v_k_1644_ = stack[1].m_obj;
uint8_t v_kind_1645_ = stack[2].m_num;
lean_object* v___y_1646_ = stack[3].m_obj;
lean_object* v___y_1647_ = stack[4].m_obj;
lean_object* v___y_1648_ = stack[5].m_obj;
lean_object* v___y_1649_ = stack[6].m_obj;
lean_object* v___y_1650_ = stack[7].m_obj;
lean_object* v___y_1651_ = stack[8].m_obj;
lean_object* v___y_1652_ = stack[9].m_obj;
lean_object* v___y_1653_ = stack[10].m_obj;
lean_object* v_res_1657_;
v_res_1657_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14(v_declInfos_1643_, v_k_1644_, v_kind_1645_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_);
stack->m_obj
 = v_res_1657_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14___boxed(lean_object* v_declInfos_1658_, lean_object* v_k_1659_, lean_object* v_kind_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_){
_start:
{
uint8_t v_kind_boxed_1670_; lean_object* v_res_1671_; 
v_kind_boxed_1670_ = lean_unbox(v_kind_1660_);
v_res_1671_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14(v_declInfos_1658_, v_k_1659_, v_kind_boxed_1670_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_);
lean_dec(v___y_1668_);
lean_dec_ref(v___y_1667_);
lean_dec(v___y_1666_);
lean_dec_ref(v___y_1665_);
lean_dec(v___y_1664_);
lean_dec_ref(v___y_1663_);
lean_dec(v___y_1662_);
lean_dec_ref(v___y_1661_);
return v_res_1671_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__13(size_t v_sz_1672_, size_t v_i_1673_, lean_object* v_bs_1674_){
_start:
{
uint8_t v___x_1675_; 
v___x_1675_ = lean_usize_dec_lt(v_i_1673_, v_sz_1672_);
if (v___x_1675_ == 0)
{
return v_bs_1674_;
}
else
{
lean_object* v_v_1676_; lean_object* v_fst_1677_; lean_object* v_snd_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1694_; 
v_v_1676_ = lean_array_uget(v_bs_1674_, v_i_1673_);
v_fst_1677_ = lean_ctor_get(v_v_1676_, 0);
v_snd_1678_ = lean_ctor_get(v_v_1676_, 1);
v_isSharedCheck_1694_ = !lean_is_exclusive(v_v_1676_);
if (v_isSharedCheck_1694_ == 0)
{
v___x_1680_ = v_v_1676_;
v_isShared_1681_ = v_isSharedCheck_1694_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_snd_1678_);
lean_inc(v_fst_1677_);
lean_dec(v_v_1676_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1694_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
lean_object* v___x_1682_; lean_object* v_bs_x27_1683_; uint8_t v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1687_; 
v___x_1682_ = lean_unsigned_to_nat(0u);
v_bs_x27_1683_ = lean_array_uset(v_bs_1674_, v_i_1673_, v___x_1682_);
v___x_1684_ = 0;
v___x_1685_ = lean_box(v___x_1684_);
if (v_isShared_1681_ == 0)
{
lean_ctor_set(v___x_1680_, 0, v___x_1685_);
v___x_1687_ = v___x_1680_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v___x_1685_);
lean_ctor_set(v_reuseFailAlloc_1693_, 1, v_snd_1678_);
v___x_1687_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
lean_object* v___x_1688_; size_t v___x_1689_; size_t v___x_1690_; lean_object* v___x_1691_; 
v___x_1688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1688_, 0, v_fst_1677_);
lean_ctor_set(v___x_1688_, 1, v___x_1687_);
v___x_1689_ = ((size_t)1ULL);
v___x_1690_ = lean_usize_add(v_i_1673_, v___x_1689_);
v___x_1691_ = lean_array_uset(v_bs_x27_1683_, v_i_1673_, v___x_1688_);
v_i_1673_ = v___x_1690_;
v_bs_1674_ = v___x_1691_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__13_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1672_ = stack[0].m_num;
size_t v_i_1673_ = stack[1].m_num;
lean_object* v_bs_1674_ = stack[2].m_obj;
lean_object* v_res_1695_;
v_res_1695_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__13(v_sz_1672_, v_i_1673_, v_bs_1674_);
stack->m_obj
 = v_res_1695_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__13___boxed(lean_object* v_sz_1696_, lean_object* v_i_1697_, lean_object* v_bs_1698_){
_start:
{
size_t v_sz_boxed_1699_; size_t v_i_boxed_1700_; lean_object* v_res_1701_; 
v_sz_boxed_1699_ = lean_unbox_usize(v_sz_1696_);
lean_dec(v_sz_1696_);
v_i_boxed_1700_ = lean_unbox_usize(v_i_1697_);
lean_dec(v_i_1697_);
v_res_1701_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__13(v_sz_boxed_1699_, v_i_boxed_1700_, v_bs_1698_);
return v_res_1701_;
}
}
lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8(lean_object* v_declInfos_1702_, lean_object* v_k_1703_, uint8_t v_kind_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_){
_start:
{
size_t v_sz_1714_; size_t v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; 
v_sz_1714_ = lean_array_size(v_declInfos_1702_);
v___x_1715_ = ((size_t)0ULL);
v___x_1716_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__13(v_sz_1714_, v___x_1715_, v_declInfos_1702_);
v___x_1717_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14(v___x_1716_, v_k_1703_, v_kind_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_);
return v___x_1717_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_declInfos_1702_ = stack[0].m_obj;
lean_object* v_k_1703_ = stack[1].m_obj;
uint8_t v_kind_1704_ = stack[2].m_num;
lean_object* v___y_1705_ = stack[3].m_obj;
lean_object* v___y_1706_ = stack[4].m_obj;
lean_object* v___y_1707_ = stack[5].m_obj;
lean_object* v___y_1708_ = stack[6].m_obj;
lean_object* v___y_1709_ = stack[7].m_obj;
lean_object* v___y_1710_ = stack[8].m_obj;
lean_object* v___y_1711_ = stack[9].m_obj;
lean_object* v___y_1712_ = stack[10].m_obj;
lean_object* v_res_1718_;
v_res_1718_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8(v_declInfos_1702_, v_k_1703_, v_kind_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_);
stack->m_obj
 = v_res_1718_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8___boxed(lean_object* v_declInfos_1719_, lean_object* v_k_1720_, lean_object* v_kind_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_){
_start:
{
uint8_t v_kind_boxed_1731_; lean_object* v_res_1732_; 
v_kind_boxed_1731_ = lean_unbox(v_kind_1721_);
v_res_1732_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8(v_declInfos_1719_, v_k_1720_, v_kind_boxed_1731_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_);
lean_dec(v___y_1729_);
lean_dec_ref(v___y_1728_);
lean_dec(v___y_1727_);
lean_dec_ref(v___y_1726_);
lean_dec(v___y_1725_);
lean_dec_ref(v___y_1724_);
lean_dec(v___y_1723_);
lean_dec_ref(v___y_1722_);
return v_res_1732_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__7___lam__0(lean_object* v_snd_1733_, lean_object* v_x_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_){
_start:
{
lean_object* v___x_1744_; 
v___x_1744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1744_, 0, v_snd_1733_);
return v___x_1744_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__7___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_snd_1733_ = stack[0].m_obj;
lean_object* v_x_1734_ = stack[1].m_obj;
lean_object* v___y_1735_ = stack[2].m_obj;
lean_object* v___y_1736_ = stack[3].m_obj;
lean_object* v___y_1737_ = stack[4].m_obj;
lean_object* v___y_1738_ = stack[5].m_obj;
lean_object* v___y_1739_ = stack[6].m_obj;
lean_object* v___y_1740_ = stack[7].m_obj;
lean_object* v___y_1741_ = stack[8].m_obj;
lean_object* v___y_1742_ = stack[9].m_obj;
lean_object* v_res_1745_;
v_res_1745_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__7___lam__0(v_snd_1733_, v_x_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_);
stack->m_obj
 = v_res_1745_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__7___lam__0___boxed(lean_object* v_snd_1746_, lean_object* v_x_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_){
_start:
{
lean_object* v_res_1757_; 
v_res_1757_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__7___lam__0(v_snd_1746_, v_x_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_);
lean_dec(v___y_1755_);
lean_dec_ref(v___y_1754_);
lean_dec(v___y_1753_);
lean_dec_ref(v___y_1752_);
lean_dec(v___y_1751_);
lean_dec_ref(v___y_1750_);
lean_dec(v___y_1749_);
lean_dec_ref(v___y_1748_);
lean_dec_ref(v_x_1747_);
return v_res_1757_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__7(size_t v_sz_1758_, size_t v_i_1759_, lean_object* v_bs_1760_){
_start:
{
uint8_t v___x_1761_; 
v___x_1761_ = lean_usize_dec_lt(v_i_1759_, v_sz_1758_);
if (v___x_1761_ == 0)
{
return v_bs_1760_;
}
else
{
lean_object* v_v_1762_; lean_object* v_fst_1763_; lean_object* v_snd_1764_; lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1778_; 
v_v_1762_ = lean_array_uget(v_bs_1760_, v_i_1759_);
v_fst_1763_ = lean_ctor_get(v_v_1762_, 0);
v_snd_1764_ = lean_ctor_get(v_v_1762_, 1);
v_isSharedCheck_1778_ = !lean_is_exclusive(v_v_1762_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1766_ = v_v_1762_;
v_isShared_1767_ = v_isSharedCheck_1778_;
goto v_resetjp_1765_;
}
else
{
lean_inc(v_snd_1764_);
lean_inc(v_fst_1763_);
lean_dec(v_v_1762_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1778_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
lean_object* v___x_1768_; lean_object* v_bs_x27_1769_; lean_object* v___f_1770_; lean_object* v___x_1772_; 
v___x_1768_ = lean_unsigned_to_nat(0u);
v_bs_x27_1769_ = lean_array_uset(v_bs_1760_, v_i_1759_, v___x_1768_);
v___f_1770_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__7___lam__0___boxed), 11, 1);
lean_closure_set(v___f_1770_, 0, v_snd_1764_);
if (v_isShared_1767_ == 0)
{
lean_ctor_set(v___x_1766_, 1, v___f_1770_);
v___x_1772_ = v___x_1766_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_fst_1763_);
lean_ctor_set(v_reuseFailAlloc_1777_, 1, v___f_1770_);
v___x_1772_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
size_t v___x_1773_; size_t v___x_1774_; lean_object* v___x_1775_; 
v___x_1773_ = ((size_t)1ULL);
v___x_1774_ = lean_usize_add(v_i_1759_, v___x_1773_);
v___x_1775_ = lean_array_uset(v_bs_x27_1769_, v_i_1759_, v___x_1772_);
v_i_1759_ = v___x_1774_;
v_bs_1760_ = v___x_1775_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__7_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1758_ = stack[0].m_num;
size_t v_i_1759_ = stack[1].m_num;
lean_object* v_bs_1760_ = stack[2].m_obj;
lean_object* v_res_1779_;
v_res_1779_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__7(v_sz_1758_, v_i_1759_, v_bs_1760_);
stack->m_obj
 = v_res_1779_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__7___boxed(lean_object* v_sz_1780_, lean_object* v_i_1781_, lean_object* v_bs_1782_){
_start:
{
size_t v_sz_boxed_1783_; size_t v_i_boxed_1784_; lean_object* v_res_1785_; 
v_sz_boxed_1783_ = lean_unbox_usize(v_sz_1780_);
lean_dec(v_sz_1780_);
v_i_boxed_1784_ = lean_unbox_usize(v_i_1781_);
lean_dec(v_i_1781_);
v_res_1785_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__7(v_sz_boxed_1783_, v_i_boxed_1784_, v_bs_1782_);
return v_res_1785_;
}
}
lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5(lean_object* v_declInfos_1786_, lean_object* v_k_1787_, uint8_t v_kind_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_){
_start:
{
size_t v_sz_1798_; size_t v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; 
v_sz_1798_ = lean_array_size(v_declInfos_1786_);
v___x_1799_ = ((size_t)0ULL);
v___x_1800_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__7(v_sz_1798_, v___x_1799_, v_declInfos_1786_);
v___x_1801_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8(v___x_1800_, v_k_1787_, v_kind_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_);
return v___x_1801_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_declInfos_1786_ = stack[0].m_obj;
lean_object* v_k_1787_ = stack[1].m_obj;
uint8_t v_kind_1788_ = stack[2].m_num;
lean_object* v___y_1789_ = stack[3].m_obj;
lean_object* v___y_1790_ = stack[4].m_obj;
lean_object* v___y_1791_ = stack[5].m_obj;
lean_object* v___y_1792_ = stack[6].m_obj;
lean_object* v___y_1793_ = stack[7].m_obj;
lean_object* v___y_1794_ = stack[8].m_obj;
lean_object* v___y_1795_ = stack[9].m_obj;
lean_object* v___y_1796_ = stack[10].m_obj;
lean_object* v_res_1802_;
v_res_1802_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5(v_declInfos_1786_, v_k_1787_, v_kind_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_);
stack->m_obj
 = v_res_1802_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5___boxed(lean_object* v_declInfos_1803_, lean_object* v_k_1804_, lean_object* v_kind_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_){
_start:
{
uint8_t v_kind_boxed_1815_; lean_object* v_res_1816_; 
v_kind_boxed_1815_ = lean_unbox(v_kind_1805_);
v_res_1816_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5(v_declInfos_1803_, v_k_1804_, v_kind_boxed_1815_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_);
lean_dec(v___y_1813_);
lean_dec_ref(v___y_1812_);
lean_dec(v___y_1811_);
lean_dec_ref(v___y_1810_);
lean_dec(v___y_1809_);
lean_dec_ref(v___y_1808_);
lean_dec(v___y_1807_);
lean_dec_ref(v___y_1806_);
return v_res_1816_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__3(size_t v_sz_1817_, size_t v_i_1818_, lean_object* v_bs_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_){
_start:
{
uint8_t v___x_1825_; 
v___x_1825_ = lean_usize_dec_lt(v_i_1818_, v_sz_1817_);
if (v___x_1825_ == 0)
{
lean_object* v___x_1826_; 
v___x_1826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1826_, 0, v_bs_1819_);
return v___x_1826_;
}
else
{
lean_object* v_v_1827_; lean_object* v___x_1828_; lean_object* v_bs_x27_1829_; lean_object* v___x_1830_; 
v_v_1827_ = lean_array_uget(v_bs_1819_, v_i_1818_);
v___x_1828_ = lean_unsigned_to_nat(0u);
v_bs_x27_1829_ = lean_array_uset(v_bs_1819_, v_i_1818_, v___x_1828_);
lean_inc(v___y_1823_);
lean_inc_ref(v___y_1822_);
lean_inc(v___y_1821_);
lean_inc_ref(v___y_1820_);
v___x_1830_ = lean_infer_type(v_v_1827_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_);
if (lean_obj_tag(v___x_1830_) == 0)
{
lean_object* v_a_1831_; size_t v___x_1832_; size_t v___x_1833_; lean_object* v___x_1834_; 
v_a_1831_ = lean_ctor_get(v___x_1830_, 0);
lean_inc(v_a_1831_);
lean_dec_ref_known(v___x_1830_, 1);
v___x_1832_ = ((size_t)1ULL);
v___x_1833_ = lean_usize_add(v_i_1818_, v___x_1832_);
v___x_1834_ = lean_array_uset(v_bs_x27_1829_, v_i_1818_, v_a_1831_);
v_i_1818_ = v___x_1833_;
v_bs_1819_ = v___x_1834_;
goto _start;
}
else
{
lean_object* v_a_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1843_; 
lean_dec_ref(v_bs_x27_1829_);
v_a_1836_ = lean_ctor_get(v___x_1830_, 0);
v_isSharedCheck_1843_ = !lean_is_exclusive(v___x_1830_);
if (v_isSharedCheck_1843_ == 0)
{
v___x_1838_ = v___x_1830_;
v_isShared_1839_ = v_isSharedCheck_1843_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_a_1836_);
lean_dec(v___x_1830_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1843_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
lean_object* v___x_1841_; 
if (v_isShared_1839_ == 0)
{
v___x_1841_ = v___x_1838_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v_a_1836_);
v___x_1841_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
return v___x_1841_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1817_ = stack[0].m_num;
size_t v_i_1818_ = stack[1].m_num;
lean_object* v_bs_1819_ = stack[2].m_obj;
lean_object* v___y_1820_ = stack[3].m_obj;
lean_object* v___y_1821_ = stack[4].m_obj;
lean_object* v___y_1822_ = stack[5].m_obj;
lean_object* v___y_1823_ = stack[6].m_obj;
lean_object* v_res_1844_;
v_res_1844_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__3(v_sz_1817_, v_i_1818_, v_bs_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_);
stack->m_obj
 = v_res_1844_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__3___boxed(lean_object* v_sz_1845_, lean_object* v_i_1846_, lean_object* v_bs_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_){
_start:
{
size_t v_sz_boxed_1853_; size_t v_i_boxed_1854_; lean_object* v_res_1855_; 
v_sz_boxed_1853_ = lean_unbox_usize(v_sz_1845_);
lean_dec(v_sz_1845_);
v_i_boxed_1854_ = lean_unbox_usize(v_i_1846_);
lean_dec(v_i_1846_);
v_res_1855_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__3(v_sz_boxed_1853_, v_i_boxed_1854_, v_bs_1847_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_);
lean_dec(v___y_1851_);
lean_dec_ref(v___y_1850_);
lean_dec(v___y_1849_);
lean_dec_ref(v___y_1848_);
return v_res_1855_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__2___redArg(size_t v_sz_1856_, size_t v_i_1857_, lean_object* v_bs_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_){
_start:
{
uint8_t v___x_1864_; 
v___x_1864_ = lean_usize_dec_lt(v_i_1857_, v_sz_1856_);
if (v___x_1864_ == 0)
{
lean_object* v___x_1865_; 
v___x_1865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1865_, 0, v_bs_1858_);
return v___x_1865_;
}
else
{
lean_object* v_v_1866_; lean_object* v_fst_1867_; lean_object* v_snd_1868_; lean_object* v___x_1869_; lean_object* v_bs_x27_1870_; lean_object* v___x_1871_; 
v_v_1866_ = lean_array_uget_borrowed(v_bs_1858_, v_i_1857_);
v_fst_1867_ = lean_ctor_get(v_v_1866_, 0);
lean_inc(v_fst_1867_);
v_snd_1868_ = lean_ctor_get(v_v_1866_, 1);
lean_inc(v_snd_1868_);
v___x_1869_ = lean_unsigned_to_nat(0u);
v_bs_x27_1870_ = lean_array_uset(v_bs_1858_, v_i_1857_, v___x_1869_);
v___x_1871_ = l_Lean_Meta_mkEq(v_snd_1868_, v_fst_1867_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_);
if (lean_obj_tag(v___x_1871_) == 0)
{
lean_object* v_a_1872_; size_t v___x_1873_; size_t v___x_1874_; lean_object* v___x_1875_; 
v_a_1872_ = lean_ctor_get(v___x_1871_, 0);
lean_inc(v_a_1872_);
lean_dec_ref_known(v___x_1871_, 1);
v___x_1873_ = ((size_t)1ULL);
v___x_1874_ = lean_usize_add(v_i_1857_, v___x_1873_);
v___x_1875_ = lean_array_uset(v_bs_x27_1870_, v_i_1857_, v_a_1872_);
v_i_1857_ = v___x_1874_;
v_bs_1858_ = v___x_1875_;
goto _start;
}
else
{
lean_object* v_a_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1884_; 
lean_dec_ref(v_bs_x27_1870_);
v_a_1877_ = lean_ctor_get(v___x_1871_, 0);
v_isSharedCheck_1884_ = !lean_is_exclusive(v___x_1871_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1879_ = v___x_1871_;
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_a_1877_);
lean_dec(v___x_1871_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v___x_1882_; 
if (v_isShared_1880_ == 0)
{
v___x_1882_ = v___x_1879_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v_a_1877_);
v___x_1882_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
return v___x_1882_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1856_ = stack[0].m_num;
size_t v_i_1857_ = stack[1].m_num;
lean_object* v_bs_1858_ = stack[2].m_obj;
lean_object* v___y_1859_ = stack[3].m_obj;
lean_object* v___y_1860_ = stack[4].m_obj;
lean_object* v___y_1861_ = stack[5].m_obj;
lean_object* v___y_1862_ = stack[6].m_obj;
lean_object* v_res_1885_;
v_res_1885_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__2___redArg(v_sz_1856_, v_i_1857_, v_bs_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_);
stack->m_obj
 = v_res_1885_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__2___redArg___boxed(lean_object* v_sz_1886_, lean_object* v_i_1887_, lean_object* v_bs_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_){
_start:
{
size_t v_sz_boxed_1894_; size_t v_i_boxed_1895_; lean_object* v_res_1896_; 
v_sz_boxed_1894_ = lean_unbox_usize(v_sz_1886_);
lean_dec(v_sz_1886_);
v_i_boxed_1895_ = lean_unbox_usize(v_i_1887_);
lean_dec(v_i_1887_);
v_res_1896_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__2___redArg(v_sz_boxed_1894_, v_i_boxed_1895_, v_bs_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_);
lean_dec(v___y_1892_);
lean_dec_ref(v___y_1891_);
lean_dec(v___y_1890_);
lean_dec_ref(v___y_1889_);
return v_res_1896_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1___lam__0(lean_object* v_revertArgs_1897_, lean_object* v_u_1898_, lean_object* v_00_u03c3s_1899_, lean_object* v_hypName_1900_, uint8_t v___x_1901_, lean_object* v_hyps_1902_, lean_object* v_ss_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_){
_start:
{
lean_object* v___x_1913_; size_t v_sz_1914_; size_t v___x_1915_; lean_object* v___x_1916_; 
v___x_1913_ = l_Array_zip___redArg(v_revertArgs_1897_, v_ss_1903_);
v_sz_1914_ = lean_array_size(v___x_1913_);
v___x_1915_ = ((size_t)0ULL);
v___x_1916_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__2___redArg(v_sz_1914_, v___x_1915_, v___x_1913_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_);
if (lean_obj_tag(v___x_1916_) == 0)
{
lean_object* v_a_1917_; lean_object* v_eqs_1918_; lean_object* v_00_u03c6_1919_; lean_object* v_00_u03c6_1920_; lean_object* v___x_1921_; 
v_a_1917_ = lean_ctor_get(v___x_1916_, 0);
lean_inc(v_a_1917_);
lean_dec_ref_known(v___x_1916_, 1);
v_eqs_1918_ = lean_array_to_list(v_a_1917_);
v_00_u03c6_1919_ = l_Lean_mkAndN(v_eqs_1918_);
v_00_u03c6_1920_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure(v_u_1898_, v_00_u03c3s_1899_, v_00_u03c6_1919_);
lean_inc(v_hypName_1900_);
v___x_1921_ = l_Lean_Core_mkFreshUserName(v_hypName_1900_, v___y_1910_, v___y_1911_);
if (lean_obj_tag(v___x_1921_) == 0)
{
lean_object* v_a_1922_; uint8_t v___x_1923_; uint8_t v___x_1924_; lean_object* v___x_1925_; 
v_a_1922_ = lean_ctor_get(v___x_1921_, 0);
lean_inc(v_a_1922_);
lean_dec_ref_known(v___x_1921_, 1);
v___x_1923_ = 1;
v___x_1924_ = 1;
v___x_1925_ = l_Lean_Meta_mkLambdaFVars(v_ss_1903_, v_00_u03c6_1920_, v___x_1901_, v___x_1923_, v___x_1901_, v___x_1923_, v___x_1924_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_);
if (lean_obj_tag(v___x_1925_) == 0)
{
lean_object* v_a_1926_; lean_object* v___x_1927_; lean_object* v_00_u03c6_1928_; lean_object* v___x_1929_; 
v_a_1926_ = lean_ctor_get(v___x_1925_, 0);
lean_inc(v_a_1926_);
lean_dec_ref_known(v___x_1925_, 1);
v___x_1927_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1927_, 0, v_hypName_1900_);
lean_ctor_set(v___x_1927_, 1, v_a_1922_);
lean_ctor_set(v___x_1927_, 2, v_a_1926_);
v_00_u03c6_1928_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_1927_);
v___x_1929_ = l_Lean_Meta_mkLambdaFVars(v_ss_1903_, v_hyps_1902_, v___x_1901_, v___x_1923_, v___x_1901_, v___x_1923_, v___x_1924_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_);
if (lean_obj_tag(v___x_1929_) == 0)
{
lean_object* v_a_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1938_; 
v_a_1930_ = lean_ctor_get(v___x_1929_, 0);
v_isSharedCheck_1938_ = !lean_is_exclusive(v___x_1929_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1932_ = v___x_1929_;
v_isShared_1933_ = v_isSharedCheck_1938_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_a_1930_);
lean_dec(v___x_1929_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_1938_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
lean_object* v___x_1934_; lean_object* v___x_1936_; 
v___x_1934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1934_, 0, v_a_1930_);
lean_ctor_set(v___x_1934_, 1, v_00_u03c6_1928_);
if (v_isShared_1933_ == 0)
{
lean_ctor_set(v___x_1932_, 0, v___x_1934_);
v___x_1936_ = v___x_1932_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v___x_1934_);
v___x_1936_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
return v___x_1936_;
}
}
}
else
{
lean_object* v_a_1939_; lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_1946_; 
lean_dec_ref(v_00_u03c6_1928_);
v_a_1939_ = lean_ctor_get(v___x_1929_, 0);
v_isSharedCheck_1946_ = !lean_is_exclusive(v___x_1929_);
if (v_isSharedCheck_1946_ == 0)
{
v___x_1941_ = v___x_1929_;
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
else
{
lean_inc(v_a_1939_);
lean_dec(v___x_1929_);
v___x_1941_ = lean_box(0);
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
v_resetjp_1940_:
{
lean_object* v___x_1944_; 
if (v_isShared_1942_ == 0)
{
v___x_1944_ = v___x_1941_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v_a_1939_);
v___x_1944_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
return v___x_1944_;
}
}
}
}
else
{
lean_object* v_a_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_1954_; 
lean_dec(v_a_1922_);
lean_dec_ref(v_hyps_1902_);
lean_dec(v_hypName_1900_);
v_a_1947_ = lean_ctor_get(v___x_1925_, 0);
v_isSharedCheck_1954_ = !lean_is_exclusive(v___x_1925_);
if (v_isSharedCheck_1954_ == 0)
{
v___x_1949_ = v___x_1925_;
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_a_1947_);
lean_dec(v___x_1925_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
lean_object* v___x_1952_; 
if (v_isShared_1950_ == 0)
{
v___x_1952_ = v___x_1949_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v_a_1947_);
v___x_1952_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
return v___x_1952_;
}
}
}
}
else
{
lean_object* v_a_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1962_; 
lean_dec_ref(v_00_u03c6_1920_);
lean_dec_ref(v_hyps_1902_);
lean_dec(v_hypName_1900_);
v_a_1955_ = lean_ctor_get(v___x_1921_, 0);
v_isSharedCheck_1962_ = !lean_is_exclusive(v___x_1921_);
if (v_isSharedCheck_1962_ == 0)
{
v___x_1957_ = v___x_1921_;
v_isShared_1958_ = v_isSharedCheck_1962_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_a_1955_);
lean_dec(v___x_1921_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_1962_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v___x_1960_; 
if (v_isShared_1958_ == 0)
{
v___x_1960_ = v___x_1957_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v_a_1955_);
v___x_1960_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
return v___x_1960_;
}
}
}
}
else
{
lean_object* v_a_1963_; lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_1970_; 
lean_dec_ref(v_hyps_1902_);
lean_dec(v_hypName_1900_);
lean_dec_ref(v_00_u03c3s_1899_);
lean_dec(v_u_1898_);
v_a_1963_ = lean_ctor_get(v___x_1916_, 0);
v_isSharedCheck_1970_ = !lean_is_exclusive(v___x_1916_);
if (v_isSharedCheck_1970_ == 0)
{
v___x_1965_ = v___x_1916_;
v_isShared_1966_ = v_isSharedCheck_1970_;
goto v_resetjp_1964_;
}
else
{
lean_inc(v_a_1963_);
lean_dec(v___x_1916_);
v___x_1965_ = lean_box(0);
v_isShared_1966_ = v_isSharedCheck_1970_;
goto v_resetjp_1964_;
}
v_resetjp_1964_:
{
lean_object* v___x_1968_; 
if (v_isShared_1966_ == 0)
{
v___x_1968_ = v___x_1965_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v_a_1963_);
v___x_1968_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
return v___x_1968_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_revertArgs_1897_ = stack[0].m_obj;
lean_object* v_u_1898_ = stack[1].m_obj;
lean_object* v_00_u03c3s_1899_ = stack[2].m_obj;
lean_object* v_hypName_1900_ = stack[3].m_obj;
uint8_t v___x_1901_ = stack[4].m_num;
lean_object* v_hyps_1902_ = stack[5].m_obj;
lean_object* v_ss_1903_ = stack[6].m_obj;
lean_object* v___y_1904_ = stack[7].m_obj;
lean_object* v___y_1905_ = stack[8].m_obj;
lean_object* v___y_1906_ = stack[9].m_obj;
lean_object* v___y_1907_ = stack[10].m_obj;
lean_object* v___y_1908_ = stack[11].m_obj;
lean_object* v___y_1909_ = stack[12].m_obj;
lean_object* v___y_1910_ = stack[13].m_obj;
lean_object* v___y_1911_ = stack[14].m_obj;
lean_object* v_res_1971_;
v_res_1971_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1___lam__0(v_revertArgs_1897_, v_u_1898_, v_00_u03c3s_1899_, v_hypName_1900_, v___x_1901_, v_hyps_1902_, v_ss_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_);
stack->m_obj
 = v_res_1971_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1___lam__0___boxed(lean_object* v_revertArgs_1972_, lean_object* v_u_1973_, lean_object* v_00_u03c3s_1974_, lean_object* v_hypName_1975_, lean_object* v___x_1976_, lean_object* v_hyps_1977_, lean_object* v_ss_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_){
_start:
{
uint8_t v___x_18924__boxed_1988_; lean_object* v_res_1989_; 
v___x_18924__boxed_1988_ = lean_unbox(v___x_1976_);
v_res_1989_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1___lam__0(v_revertArgs_1972_, v_u_1973_, v_00_u03c3s_1974_, v_hypName_1975_, v___x_18924__boxed_1988_, v_hyps_1977_, v_ss_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_);
lean_dec(v___y_1986_);
lean_dec_ref(v___y_1985_);
lean_dec(v___y_1984_);
lean_dec_ref(v___y_1983_);
lean_dec(v___y_1982_);
lean_dec_ref(v___y_1981_);
lean_dec(v___y_1980_);
lean_dec_ref(v___y_1979_);
lean_dec_ref(v_ss_1978_);
lean_dec_ref(v_revertArgs_1972_);
return v_res_1989_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1(lean_object* v_goal_1990_, lean_object* v_n_1991_, lean_object* v_hypName_1992_, lean_object* v_k_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_){
_start:
{
lean_object* v___x_2003_; uint8_t v___x_2004_; 
v___x_2003_ = lean_unsigned_to_nat(0u);
v___x_2004_ = lean_nat_dec_eq(v_n_1991_, v___x_2003_);
if (v___x_2004_ == 0)
{
lean_object* v_u_2005_; lean_object* v_00_u03c3s_2006_; lean_object* v_hyps_2007_; lean_object* v_target_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2162_; 
v_u_2005_ = lean_ctor_get(v_goal_1990_, 0);
v_00_u03c3s_2006_ = lean_ctor_get(v_goal_1990_, 1);
v_hyps_2007_ = lean_ctor_get(v_goal_1990_, 2);
v_target_2008_ = lean_ctor_get(v_goal_1990_, 3);
v_isSharedCheck_2162_ = !lean_is_exclusive(v_goal_1990_);
if (v_isSharedCheck_2162_ == 0)
{
v___x_2010_ = v_goal_1990_;
v_isShared_2011_ = v_isSharedCheck_2162_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_target_2008_);
lean_inc(v_hyps_2007_);
lean_inc(v_00_u03c3s_2006_);
lean_inc(v_u_2005_);
lean_dec(v_goal_1990_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2162_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v_T_2012_; lean_object* v_f_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v_a_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v_revertArgs_2020_; lean_object* v___y_2022_; lean_object* v___y_2023_; lean_object* v___y_2024_; lean_object* v___y_2025_; lean_object* v___y_2026_; lean_object* v___y_2027_; lean_object* v___y_2028_; lean_object* v___y_2029_; lean_object* v___y_2030_; lean_object* v___y_2031_; lean_object* v___y_2032_; lean_object* v___y_2033_; lean_object* v___x_2072_; lean_object* v___f_2073_; lean_object* v___y_2075_; lean_object* v___y_2076_; lean_object* v___y_2077_; lean_object* v___y_2078_; lean_object* v___y_2079_; lean_object* v___y_2080_; lean_object* v___y_2081_; lean_object* v___y_2082_; lean_object* v___x_2136_; uint8_t v___x_2137_; 
v_T_2012_ = l_Lean_Expr_consumeMData(v_target_2008_);
v_f_2013_ = l_Lean_Expr_getAppFn(v_T_2012_);
v___x_2014_ = l_Lean_Expr_getAppNumArgs(v_T_2012_);
v___x_2015_ = lean_mk_empty_array_with_capacity(v___x_2014_);
lean_dec(v___x_2014_);
lean_inc_ref(v_T_2012_);
v_a_2016_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_T_2012_, v___x_2015_);
lean_inc(v_n_1991_);
lean_inc_ref(v_a_2016_);
v___x_2017_ = l_Array_toSubarray___redArg(v_a_2016_, v___x_2003_, v_n_1991_);
v___x_2018_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__1));
v___x_2019_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__1___redArg(v___x_2017_, v___x_2018_);
v_revertArgs_2020_ = l_Array_reverse___redArg(v___x_2019_);
v___x_2072_ = lean_box(v___x_2004_);
lean_inc_ref(v_hyps_2007_);
lean_inc_ref(v_00_u03c3s_2006_);
lean_inc(v_u_2005_);
lean_inc_ref(v_revertArgs_2020_);
v___f_2073_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1___lam__0___boxed), 16, 6);
lean_closure_set(v___f_2073_, 0, v_revertArgs_2020_);
lean_closure_set(v___f_2073_, 1, v_u_2005_);
lean_closure_set(v___f_2073_, 2, v_00_u03c3s_2006_);
lean_closure_set(v___f_2073_, 3, v_hypName_1992_);
lean_closure_set(v___f_2073_, 4, v___x_2072_);
lean_closure_set(v___f_2073_, 5, v_hyps_2007_);
v___x_2136_ = lean_array_get_size(v_revertArgs_2020_);
v___x_2137_ = lean_nat_dec_eq(v___x_2136_, v_n_1991_);
if (v___x_2137_ == 0)
{
lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v_a_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2161_; 
lean_dec_ref(v___f_2073_);
lean_dec_ref(v_revertArgs_2020_);
lean_dec_ref(v_a_2016_);
lean_dec_ref(v_f_2013_);
lean_del_object(v___x_2010_);
lean_dec_ref(v_target_2008_);
lean_dec_ref(v_hyps_2007_);
lean_dec_ref(v_00_u03c3s_2006_);
lean_dec(v_u_2005_);
lean_dec_ref(v_k_1993_);
v___x_2138_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__3, &l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__3_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__3);
v___x_2139_ = l_Nat_reprFast(v_n_1991_);
v___x_2140_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2140_, 0, v___x_2139_);
v___x_2141_ = l_Lean_MessageData_ofFormat(v___x_2140_);
v___x_2142_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2142_, 0, v___x_2138_);
lean_ctor_set(v___x_2142_, 1, v___x_2141_);
v___x_2143_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__5, &l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__5_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__5);
v___x_2144_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2144_, 0, v___x_2142_);
lean_ctor_set(v___x_2144_, 1, v___x_2143_);
v___x_2145_ = l_Lean_MessageData_ofExpr(v_T_2012_);
v___x_2146_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2146_, 0, v___x_2144_);
lean_ctor_set(v___x_2146_, 1, v___x_2145_);
v___x_2147_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__7, &l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__7_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__7);
v___x_2148_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2148_, 0, v___x_2146_);
lean_ctor_set(v___x_2148_, 1, v___x_2147_);
v___x_2149_ = l_Nat_reprFast(v___x_2136_);
v___x_2150_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2150_, 0, v___x_2149_);
v___x_2151_ = l_Lean_MessageData_ofFormat(v___x_2150_);
v___x_2152_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2152_, 0, v___x_2148_);
lean_ctor_set(v___x_2152_, 1, v___x_2151_);
v___x_2153_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__8___redArg(v___x_2152_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_);
v_a_2154_ = lean_ctor_get(v___x_2153_, 0);
v_isSharedCheck_2161_ = !lean_is_exclusive(v___x_2153_);
if (v_isSharedCheck_2161_ == 0)
{
v___x_2156_ = v___x_2153_;
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_a_2154_);
lean_dec(v___x_2153_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
lean_object* v___x_2159_; 
if (v_isShared_2157_ == 0)
{
v___x_2159_ = v___x_2156_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v_a_2154_);
v___x_2159_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
return v___x_2159_;
}
}
}
else
{
lean_dec_ref(v_T_2012_);
v___y_2075_ = v___y_1994_;
v___y_2076_ = v___y_1995_;
v___y_2077_ = v___y_1996_;
v___y_2078_ = v___y_1997_;
v___y_2079_ = v___y_1998_;
v___y_2080_ = v___y_1999_;
v___y_2081_ = v___y_2000_;
v___y_2082_ = v___y_2001_;
goto v___jp_2074_;
}
v___jp_2021_:
{
lean_object* v___x_2034_; 
v___x_2034_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v___y_2026_, v___y_2025_);
if (lean_obj_tag(v___x_2034_) == 0)
{
lean_object* v_a_2035_; lean_object* v_H_2036_; lean_object* v___x_2037_; lean_object* v_fst_2038_; lean_object* v_snd_2039_; lean_object* v___x_2041_; uint8_t v_isShared_2042_; uint8_t v_isSharedCheck_2071_; 
v_a_2035_ = lean_ctor_get(v___x_2034_, 0);
lean_inc(v_a_2035_);
lean_dec_ref_known(v___x_2034_, 1);
lean_inc_ref_n(v___y_2033_, 2);
v_H_2036_ = l_Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps(v___y_2033_, v_a_2035_);
lean_inc(v_u_2005_);
v___x_2037_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd(v_u_2005_, v___y_2033_, v_H_2036_, v___y_2022_);
v_fst_2038_ = lean_ctor_get(v___x_2037_, 0);
v_snd_2039_ = lean_ctor_get(v___x_2037_, 1);
v_isSharedCheck_2071_ = !lean_is_exclusive(v___x_2037_);
if (v_isSharedCheck_2071_ == 0)
{
v___x_2041_ = v___x_2037_;
v_isShared_2042_ = v_isSharedCheck_2071_;
goto v_resetjp_2040_;
}
else
{
lean_inc(v_snd_2039_);
lean_inc(v_fst_2038_);
lean_dec(v___x_2037_);
v___x_2041_ = lean_box(0);
v_isShared_2042_ = v_isSharedCheck_2071_;
goto v_resetjp_2040_;
}
v_resetjp_2040_:
{
lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v_goal_x27_2048_; 
v___x_2043_ = lean_array_get_size(v_a_2016_);
v___x_2044_ = l_Array_toSubarray___redArg(v_a_2016_, v_n_1991_, v___x_2043_);
v___x_2045_ = l_Subarray_copy___redArg(v___x_2044_);
v___x_2046_ = l_Lean_mkAppRev(v_f_2013_, v___x_2045_);
lean_dec_ref(v___x_2045_);
lean_inc(v_fst_2038_);
lean_inc(v_u_2005_);
if (v_isShared_2011_ == 0)
{
lean_ctor_set(v___x_2010_, 3, v___x_2046_);
lean_ctor_set(v___x_2010_, 2, v_fst_2038_);
lean_ctor_set(v___x_2010_, 1, v___y_2033_);
v_goal_x27_2048_ = v___x_2010_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v_u_2005_);
lean_ctor_set(v_reuseFailAlloc_2070_, 1, v___y_2033_);
lean_ctor_set(v_reuseFailAlloc_2070_, 2, v_fst_2038_);
lean_ctor_set(v_reuseFailAlloc_2070_, 3, v___x_2046_);
v_goal_x27_2048_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
lean_object* v___x_2049_; 
lean_inc(v___y_2023_);
lean_inc_ref(v___y_2028_);
lean_inc(v___y_2025_);
lean_inc_ref(v___y_2031_);
lean_inc(v___y_2024_);
lean_inc_ref(v___y_2029_);
lean_inc(v___y_2027_);
lean_inc_ref(v___y_2032_);
v___x_2049_ = lean_apply_10(v_k_1993_, v_goal_x27_2048_, v___y_2032_, v___y_2027_, v___y_2029_, v___y_2024_, v___y_2031_, v___y_2025_, v___y_2028_, v___y_2023_, lean_box(0));
if (lean_obj_tag(v___x_2049_) == 0)
{
lean_object* v_a_2050_; lean_object* v___x_2051_; 
v_a_2050_ = lean_ctor_get(v___x_2049_, 0);
lean_inc(v_a_2050_);
lean_dec_ref_known(v___x_2049_, 1);
lean_inc(v___y_2023_);
lean_inc_ref(v___y_2028_);
lean_inc(v___y_2025_);
lean_inc_ref(v___y_2031_);
lean_inc_ref(v___y_2030_);
v___x_2051_ = lean_infer_type(v___y_2030_, v___y_2031_, v___y_2025_, v___y_2028_, v___y_2023_);
if (lean_obj_tag(v___x_2051_) == 0)
{
lean_object* v_a_2052_; lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2069_; 
v_a_2052_ = lean_ctor_get(v___x_2051_, 0);
v_isSharedCheck_2069_ = !lean_is_exclusive(v___x_2051_);
if (v_isSharedCheck_2069_ == 0)
{
v___x_2054_ = v___x_2051_;
v_isShared_2055_ = v_isSharedCheck_2069_;
goto v_resetjp_2053_;
}
else
{
lean_inc(v_a_2052_);
lean_dec(v___x_2051_);
v___x_2054_ = lean_box(0);
v_isShared_2055_ = v_isSharedCheck_2069_;
goto v_resetjp_2053_;
}
v_resetjp_2053_:
{
lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2059_; 
v___x_2056_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__12___closed__1));
v___x_2057_ = lean_box(0);
if (v_isShared_2042_ == 0)
{
lean_ctor_set_tag(v___x_2041_, 1);
lean_ctor_set(v___x_2041_, 1, v___x_2057_);
lean_ctor_set(v___x_2041_, 0, v_u_2005_);
v___x_2059_ = v___x_2041_;
goto v_reusejp_2058_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v_u_2005_);
lean_ctor_set(v_reuseFailAlloc_2068_, 1, v___x_2057_);
v___x_2059_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2058_;
}
v_reusejp_2058_:
{
lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v_prf_2064_; lean_object* v___x_2066_; 
v___x_2060_ = l_Lean_mkConst(v___x_2056_, v___x_2059_);
v___x_2061_ = l_Lean_mkAppN(v_fst_2038_, v_revertArgs_2020_);
v___x_2062_ = l_Lean_mkAppN(v_snd_2039_, v_revertArgs_2020_);
v___x_2063_ = l_Lean_mkAppN(v_a_2050_, v_revertArgs_2020_);
lean_dec_ref(v_revertArgs_2020_);
v_prf_2064_ = l_Lean_mkApp8(v___x_2060_, v_00_u03c3s_2006_, v_a_2052_, v_hyps_2007_, v___x_2061_, v_target_2008_, v___y_2030_, v___x_2062_, v___x_2063_);
if (v_isShared_2055_ == 0)
{
lean_ctor_set(v___x_2054_, 0, v_prf_2064_);
v___x_2066_ = v___x_2054_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v_prf_2064_);
v___x_2066_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
return v___x_2066_;
}
}
}
}
else
{
lean_dec(v_a_2050_);
lean_del_object(v___x_2041_);
lean_dec(v_snd_2039_);
lean_dec(v_fst_2038_);
lean_dec_ref(v___y_2030_);
lean_dec_ref(v_revertArgs_2020_);
lean_dec_ref(v_target_2008_);
lean_dec_ref(v_hyps_2007_);
lean_dec_ref(v_00_u03c3s_2006_);
lean_dec(v_u_2005_);
return v___x_2051_;
}
}
else
{
lean_del_object(v___x_2041_);
lean_dec(v_snd_2039_);
lean_dec(v_fst_2038_);
lean_dec_ref(v___y_2030_);
lean_dec_ref(v_revertArgs_2020_);
lean_dec_ref(v_target_2008_);
lean_dec_ref(v_hyps_2007_);
lean_dec_ref(v_00_u03c3s_2006_);
lean_dec(v_u_2005_);
return v___x_2049_;
}
}
}
}
else
{
lean_dec_ref(v___y_2033_);
lean_dec_ref(v___y_2030_);
lean_dec_ref(v___y_2022_);
lean_dec_ref(v_revertArgs_2020_);
lean_dec_ref(v_a_2016_);
lean_dec_ref(v_f_2013_);
lean_del_object(v___x_2010_);
lean_dec_ref(v_target_2008_);
lean_dec_ref(v_hyps_2007_);
lean_dec_ref(v_00_u03c3s_2006_);
lean_dec(v_u_2005_);
lean_dec_ref(v_k_1993_);
lean_dec(v_n_1991_);
return v___x_2034_;
}
}
v___jp_2074_:
{
size_t v_sz_2083_; size_t v___x_2084_; lean_object* v___x_2085_; 
v_sz_2083_ = lean_array_size(v_revertArgs_2020_);
v___x_2084_ = ((size_t)0ULL);
lean_inc_ref(v_revertArgs_2020_);
v___x_2085_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__3(v_sz_2083_, v___x_2084_, v_revertArgs_2020_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_);
if (lean_obj_tag(v___x_2085_) == 0)
{
lean_object* v_a_2086_; size_t v_sz_2087_; lean_object* v___x_2088_; 
v_a_2086_ = lean_ctor_get(v___x_2085_, 0);
lean_inc_n(v_a_2086_, 2);
lean_dec_ref_known(v___x_2085_, 1);
v_sz_2087_ = lean_array_size(v_a_2086_);
v___x_2088_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__4___redArg(v_sz_2087_, v___x_2084_, v_a_2086_, v___y_2081_, v___y_2082_);
if (lean_obj_tag(v___x_2088_) == 0)
{
lean_object* v_a_2089_; uint8_t v___x_2090_; lean_object* v___x_2091_; 
v_a_2089_ = lean_ctor_get(v___x_2088_, 0);
lean_inc(v_a_2089_);
lean_dec_ref_known(v___x_2088_, 1);
v___x_2090_ = 0;
v___x_2091_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5(v_a_2089_, v___f_2073_, v___x_2090_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_);
if (lean_obj_tag(v___x_2091_) == 0)
{
lean_object* v_a_2092_; lean_object* v_fst_2093_; lean_object* v_snd_2094_; lean_object* v___x_2095_; 
v_a_2092_ = lean_ctor_get(v___x_2091_, 0);
lean_inc(v_a_2092_);
lean_dec_ref_known(v___x_2091_, 1);
v_fst_2093_ = lean_ctor_get(v_a_2092_, 0);
lean_inc(v_fst_2093_);
v_snd_2094_ = lean_ctor_get(v_a_2092_, 1);
lean_inc(v_snd_2094_);
lean_dec(v_a_2092_);
lean_inc_ref(v_revertArgs_2020_);
v___x_2095_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__6(v_sz_2083_, v___x_2084_, v_revertArgs_2020_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_);
if (lean_obj_tag(v___x_2095_) == 0)
{
lean_object* v_a_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; 
v_a_2096_ = lean_ctor_get(v___x_2095_, 0);
lean_inc(v_a_2096_);
lean_dec_ref_known(v___x_2095_, 1);
v___x_2097_ = lean_array_to_list(v_a_2096_);
v___x_2098_ = l_Lean_Meta_mkAndIntroN(v___x_2097_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_);
if (lean_obj_tag(v___x_2098_) == 0)
{
lean_object* v_a_2099_; lean_object* v___x_2100_; uint8_t v___x_2101_; 
v_a_2099_ = lean_ctor_get(v___x_2098_, 0);
lean_inc(v_a_2099_);
lean_dec_ref_known(v___x_2098_, 1);
v___x_2100_ = lean_array_get_size(v_a_2086_);
v___x_2101_ = lean_nat_dec_lt(v___x_2003_, v___x_2100_);
if (v___x_2101_ == 0)
{
lean_dec(v_a_2086_);
lean_inc_ref(v_00_u03c3s_2006_);
v___y_2022_ = v_snd_2094_;
v___y_2023_ = v___y_2082_;
v___y_2024_ = v___y_2078_;
v___y_2025_ = v___y_2080_;
v___y_2026_ = v_fst_2093_;
v___y_2027_ = v___y_2076_;
v___y_2028_ = v___y_2081_;
v___y_2029_ = v___y_2077_;
v___y_2030_ = v_a_2099_;
v___y_2031_ = v___y_2079_;
v___y_2032_ = v___y_2075_;
v___y_2033_ = v_00_u03c3s_2006_;
goto v___jp_2021_;
}
else
{
size_t v___x_2102_; lean_object* v___x_2103_; 
v___x_2102_ = lean_usize_of_nat(v___x_2100_);
lean_inc_ref(v_00_u03c3s_2006_);
lean_inc(v_u_2005_);
v___x_2103_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__7(v_u_2005_, v_a_2086_, v___x_2102_, v___x_2084_, v_00_u03c3s_2006_);
lean_dec(v_a_2086_);
v___y_2022_ = v_snd_2094_;
v___y_2023_ = v___y_2082_;
v___y_2024_ = v___y_2078_;
v___y_2025_ = v___y_2080_;
v___y_2026_ = v_fst_2093_;
v___y_2027_ = v___y_2076_;
v___y_2028_ = v___y_2081_;
v___y_2029_ = v___y_2077_;
v___y_2030_ = v_a_2099_;
v___y_2031_ = v___y_2079_;
v___y_2032_ = v___y_2075_;
v___y_2033_ = v___x_2103_;
goto v___jp_2021_;
}
}
else
{
lean_dec(v_snd_2094_);
lean_dec(v_fst_2093_);
lean_dec(v_a_2086_);
lean_dec_ref(v_revertArgs_2020_);
lean_dec_ref(v_a_2016_);
lean_dec_ref(v_f_2013_);
lean_del_object(v___x_2010_);
lean_dec_ref(v_target_2008_);
lean_dec_ref(v_hyps_2007_);
lean_dec_ref(v_00_u03c3s_2006_);
lean_dec(v_u_2005_);
lean_dec_ref(v_k_1993_);
lean_dec(v_n_1991_);
return v___x_2098_;
}
}
else
{
lean_object* v_a_2104_; lean_object* v___x_2106_; uint8_t v_isShared_2107_; uint8_t v_isSharedCheck_2111_; 
lean_dec(v_snd_2094_);
lean_dec(v_fst_2093_);
lean_dec(v_a_2086_);
lean_dec_ref(v_revertArgs_2020_);
lean_dec_ref(v_a_2016_);
lean_dec_ref(v_f_2013_);
lean_del_object(v___x_2010_);
lean_dec_ref(v_target_2008_);
lean_dec_ref(v_hyps_2007_);
lean_dec_ref(v_00_u03c3s_2006_);
lean_dec(v_u_2005_);
lean_dec_ref(v_k_1993_);
lean_dec(v_n_1991_);
v_a_2104_ = lean_ctor_get(v___x_2095_, 0);
v_isSharedCheck_2111_ = !lean_is_exclusive(v___x_2095_);
if (v_isSharedCheck_2111_ == 0)
{
v___x_2106_ = v___x_2095_;
v_isShared_2107_ = v_isSharedCheck_2111_;
goto v_resetjp_2105_;
}
else
{
lean_inc(v_a_2104_);
lean_dec(v___x_2095_);
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
else
{
lean_object* v_a_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2119_; 
lean_dec(v_a_2086_);
lean_dec_ref(v_revertArgs_2020_);
lean_dec_ref(v_a_2016_);
lean_dec_ref(v_f_2013_);
lean_del_object(v___x_2010_);
lean_dec_ref(v_target_2008_);
lean_dec_ref(v_hyps_2007_);
lean_dec_ref(v_00_u03c3s_2006_);
lean_dec(v_u_2005_);
lean_dec_ref(v_k_1993_);
lean_dec(v_n_1991_);
v_a_2112_ = lean_ctor_get(v___x_2091_, 0);
v_isSharedCheck_2119_ = !lean_is_exclusive(v___x_2091_);
if (v_isSharedCheck_2119_ == 0)
{
v___x_2114_ = v___x_2091_;
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_a_2112_);
lean_dec(v___x_2091_);
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
else
{
lean_object* v_a_2120_; lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2127_; 
lean_dec(v_a_2086_);
lean_dec_ref(v___f_2073_);
lean_dec_ref(v_revertArgs_2020_);
lean_dec_ref(v_a_2016_);
lean_dec_ref(v_f_2013_);
lean_del_object(v___x_2010_);
lean_dec_ref(v_target_2008_);
lean_dec_ref(v_hyps_2007_);
lean_dec_ref(v_00_u03c3s_2006_);
lean_dec(v_u_2005_);
lean_dec_ref(v_k_1993_);
lean_dec(v_n_1991_);
v_a_2120_ = lean_ctor_get(v___x_2088_, 0);
v_isSharedCheck_2127_ = !lean_is_exclusive(v___x_2088_);
if (v_isSharedCheck_2127_ == 0)
{
v___x_2122_ = v___x_2088_;
v_isShared_2123_ = v_isSharedCheck_2127_;
goto v_resetjp_2121_;
}
else
{
lean_inc(v_a_2120_);
lean_dec(v___x_2088_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2127_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
lean_object* v___x_2125_; 
if (v_isShared_2123_ == 0)
{
v___x_2125_ = v___x_2122_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v_a_2120_);
v___x_2125_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
return v___x_2125_;
}
}
}
}
else
{
lean_object* v_a_2128_; lean_object* v___x_2130_; uint8_t v_isShared_2131_; uint8_t v_isSharedCheck_2135_; 
lean_dec_ref(v___f_2073_);
lean_dec_ref(v_revertArgs_2020_);
lean_dec_ref(v_a_2016_);
lean_dec_ref(v_f_2013_);
lean_del_object(v___x_2010_);
lean_dec_ref(v_target_2008_);
lean_dec_ref(v_hyps_2007_);
lean_dec_ref(v_00_u03c3s_2006_);
lean_dec(v_u_2005_);
lean_dec_ref(v_k_1993_);
lean_dec(v_n_1991_);
v_a_2128_ = lean_ctor_get(v___x_2085_, 0);
v_isSharedCheck_2135_ = !lean_is_exclusive(v___x_2085_);
if (v_isSharedCheck_2135_ == 0)
{
v___x_2130_ = v___x_2085_;
v_isShared_2131_ = v_isSharedCheck_2135_;
goto v_resetjp_2129_;
}
else
{
lean_inc(v_a_2128_);
lean_dec(v___x_2085_);
v___x_2130_ = lean_box(0);
v_isShared_2131_ = v_isSharedCheck_2135_;
goto v_resetjp_2129_;
}
v_resetjp_2129_:
{
lean_object* v___x_2133_; 
if (v_isShared_2131_ == 0)
{
v___x_2133_ = v___x_2130_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v_a_2128_);
v___x_2133_ = v_reuseFailAlloc_2134_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
return v___x_2133_;
}
}
}
}
}
}
else
{
lean_object* v___x_2163_; 
lean_dec(v_hypName_1992_);
lean_dec(v_n_1991_);
lean_inc(v___y_2001_);
lean_inc_ref(v___y_2000_);
lean_inc(v___y_1999_);
lean_inc_ref(v___y_1998_);
lean_inc(v___y_1997_);
lean_inc_ref(v___y_1996_);
lean_inc(v___y_1995_);
lean_inc_ref(v___y_1994_);
v___x_2163_ = lean_apply_10(v_k_1993_, v_goal_1990_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_, lean_box(0));
return v___x_2163_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_1990_ = stack[0].m_obj;
lean_object* v_n_1991_ = stack[1].m_obj;
lean_object* v_hypName_1992_ = stack[2].m_obj;
lean_object* v_k_1993_ = stack[3].m_obj;
lean_object* v___y_1994_ = stack[4].m_obj;
lean_object* v___y_1995_ = stack[5].m_obj;
lean_object* v___y_1996_ = stack[6].m_obj;
lean_object* v___y_1997_ = stack[7].m_obj;
lean_object* v___y_1998_ = stack[8].m_obj;
lean_object* v___y_1999_ = stack[9].m_obj;
lean_object* v___y_2000_ = stack[10].m_obj;
lean_object* v___y_2001_ = stack[11].m_obj;
lean_object* v_res_2164_;
v_res_2164_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1(v_goal_1990_, v_n_1991_, v_hypName_1992_, v_k_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_);
stack->m_obj
 = v_res_2164_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1___boxed(lean_object* v_goal_2165_, lean_object* v_n_2166_, lean_object* v_hypName_2167_, lean_object* v_k_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_){
_start:
{
lean_object* v_res_2178_; 
v_res_2178_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1(v_goal_2165_, v_n_2166_, v_hypName_2167_, v_k_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_);
lean_dec(v___y_2176_);
lean_dec_ref(v___y_2175_);
lean_dec(v___y_2174_);
lean_dec_ref(v___y_2173_);
lean_dec(v___y_2172_);
lean_dec_ref(v___y_2171_);
lean_dec(v___y_2170_);
lean_dec_ref(v___y_2169_);
return v_res_2178_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__1(lean_object* v___x_2182_, lean_object* v_snd_2183_, lean_object* v___y_2184_, lean_object* v_fst_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_){
_start:
{
lean_object* v___x_2195_; lean_object* v___f_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; 
v___x_2195_ = lean_st_mk_ref(v___x_2182_);
lean_inc(v___x_2195_);
v___f_2196_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__0___boxed), 11, 1);
lean_closure_set(v___f_2196_, 0, v___x_2195_);
v___x_2197_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__1___closed__1));
v___x_2198_ = l_Lean_Core_mkFreshUserName(v___x_2197_, v___y_2192_, v___y_2193_);
if (lean_obj_tag(v___x_2198_) == 0)
{
lean_object* v_a_2199_; lean_object* v___x_2200_; 
v_a_2199_ = lean_ctor_get(v___x_2198_, 0);
lean_inc(v_a_2199_);
lean_dec_ref_known(v___x_2198_, 1);
v___x_2200_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1(v_snd_2183_, v___y_2184_, v_a_2199_, v___f_2196_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_);
if (lean_obj_tag(v___x_2200_) == 0)
{
lean_object* v_a_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; 
v_a_2201_ = lean_ctor_get(v___x_2200_, 0);
lean_inc(v_a_2201_);
lean_dec_ref_known(v___x_2200_, 1);
v___x_2202_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2___redArg(v_fst_2185_, v_a_2201_, v___y_2191_);
lean_dec_ref(v___x_2202_);
v___x_2203_ = lean_st_ref_get(v___x_2195_);
lean_dec(v___x_2195_);
v___x_2204_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2203_, v___y_2187_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_);
return v___x_2204_;
}
else
{
lean_object* v_a_2205_; lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2212_; 
lean_dec(v___x_2195_);
lean_dec(v_fst_2185_);
v_a_2205_ = lean_ctor_get(v___x_2200_, 0);
v_isSharedCheck_2212_ = !lean_is_exclusive(v___x_2200_);
if (v_isSharedCheck_2212_ == 0)
{
v___x_2207_ = v___x_2200_;
v_isShared_2208_ = v_isSharedCheck_2212_;
goto v_resetjp_2206_;
}
else
{
lean_inc(v_a_2205_);
lean_dec(v___x_2200_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2212_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
lean_object* v___x_2210_; 
if (v_isShared_2208_ == 0)
{
v___x_2210_ = v___x_2207_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v_a_2205_);
v___x_2210_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
return v___x_2210_;
}
}
}
}
else
{
lean_object* v_a_2213_; lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2220_; 
lean_dec_ref(v___f_2196_);
lean_dec(v___x_2195_);
lean_dec(v_fst_2185_);
lean_dec(v___y_2184_);
lean_dec_ref(v_snd_2183_);
v_a_2213_ = lean_ctor_get(v___x_2198_, 0);
v_isSharedCheck_2220_ = !lean_is_exclusive(v___x_2198_);
if (v_isSharedCheck_2220_ == 0)
{
v___x_2215_ = v___x_2198_;
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
else
{
lean_inc(v_a_2213_);
lean_dec(v___x_2198_);
v___x_2215_ = lean_box(0);
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
v_resetjp_2214_:
{
lean_object* v___x_2218_; 
if (v_isShared_2216_ == 0)
{
v___x_2218_ = v___x_2215_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v_a_2213_);
v___x_2218_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
return v___x_2218_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2182_ = stack[0].m_obj;
lean_object* v_snd_2183_ = stack[1].m_obj;
lean_object* v___y_2184_ = stack[2].m_obj;
lean_object* v_fst_2185_ = stack[3].m_obj;
lean_object* v___y_2186_ = stack[4].m_obj;
lean_object* v___y_2187_ = stack[5].m_obj;
lean_object* v___y_2188_ = stack[6].m_obj;
lean_object* v___y_2189_ = stack[7].m_obj;
lean_object* v___y_2190_ = stack[8].m_obj;
lean_object* v___y_2191_ = stack[9].m_obj;
lean_object* v___y_2192_ = stack[10].m_obj;
lean_object* v___y_2193_ = stack[11].m_obj;
lean_object* v_res_2221_;
v_res_2221_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__1(v___x_2182_, v_snd_2183_, v___y_2184_, v_fst_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_);
stack->m_obj
 = v_res_2221_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__1___boxed(lean_object* v___x_2222_, lean_object* v_snd_2223_, lean_object* v___y_2224_, lean_object* v_fst_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_){
_start:
{
lean_object* v_res_2235_; 
v_res_2235_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__1(v___x_2222_, v_snd_2223_, v___y_2224_, v_fst_2225_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_);
lean_dec(v___y_2233_);
lean_dec_ref(v___y_2232_);
lean_dec(v___y_2231_);
lean_dec_ref(v___y_2230_);
lean_dec(v___y_2229_);
lean_dec_ref(v___y_2228_);
lean_dec(v___y_2227_);
lean_dec_ref(v___y_2226_);
return v_res_2235_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevert___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__4(lean_object* v_goal_2243_, lean_object* v_ref_2244_, lean_object* v_k_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_){
_start:
{
lean_object* v___x_2255_; 
lean_inc_ref(v_goal_2243_);
v___x_2255_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo(v_goal_2243_, v_ref_2244_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_);
if (lean_obj_tag(v___x_2255_) == 0)
{
lean_object* v_a_2256_; lean_object* v_focusHyp_2257_; lean_object* v_restHyps_2258_; lean_object* v_proof_2259_; lean_object* v___x_2260_; 
v_a_2256_ = lean_ctor_get(v___x_2255_, 0);
lean_inc(v_a_2256_);
lean_dec_ref_known(v___x_2255_, 1);
v_focusHyp_2257_ = lean_ctor_get(v_a_2256_, 0);
lean_inc_ref_n(v_focusHyp_2257_, 2);
v_restHyps_2258_ = lean_ctor_get(v_a_2256_, 1);
lean_inc_ref(v_restHyps_2258_);
v_proof_2259_ = lean_ctor_get(v_a_2256_, 2);
lean_inc_ref(v_proof_2259_);
lean_dec(v_a_2256_);
v___x_2260_ = l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(v_focusHyp_2257_);
if (lean_obj_tag(v___x_2260_) == 1)
{
lean_object* v_val_2261_; lean_object* v_u_2262_; lean_object* v_00_u03c3s_2263_; lean_object* v_hyps_2264_; lean_object* v_target_2265_; lean_object* v___x_2267_; uint8_t v_isShared_2268_; uint8_t v_isSharedCheck_2290_; 
v_val_2261_ = lean_ctor_get(v___x_2260_, 0);
lean_inc(v_val_2261_);
lean_dec_ref_known(v___x_2260_, 1);
v_u_2262_ = lean_ctor_get(v_goal_2243_, 0);
v_00_u03c3s_2263_ = lean_ctor_get(v_goal_2243_, 1);
v_hyps_2264_ = lean_ctor_get(v_goal_2243_, 2);
v_target_2265_ = lean_ctor_get(v_goal_2243_, 3);
v_isSharedCheck_2290_ = !lean_is_exclusive(v_goal_2243_);
if (v_isSharedCheck_2290_ == 0)
{
v___x_2267_ = v_goal_2243_;
v_isShared_2268_ = v_isSharedCheck_2290_;
goto v_resetjp_2266_;
}
else
{
lean_inc(v_target_2265_);
lean_inc(v_hyps_2264_);
lean_inc(v_00_u03c3s_2263_);
lean_inc(v_u_2262_);
lean_dec(v_goal_2243_);
v___x_2267_ = lean_box(0);
v_isShared_2268_ = v_isSharedCheck_2290_;
goto v_resetjp_2266_;
}
v_resetjp_2266_:
{
lean_object* v_p_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2276_; 
v_p_2269_ = lean_ctor_get(v_val_2261_, 2);
lean_inc_ref(v_p_2269_);
lean_dec(v_val_2261_);
v___x_2270_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__4));
v___x_2271_ = lean_box(0);
lean_inc(v_u_2262_);
v___x_2272_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2272_, 0, v_u_2262_);
lean_ctor_set(v___x_2272_, 1, v___x_2271_);
lean_inc_ref(v___x_2272_);
v___x_2273_ = l_Lean_mkConst(v___x_2270_, v___x_2272_);
lean_inc_ref(v_target_2265_);
lean_inc_ref_n(v_00_u03c3s_2263_, 2);
v___x_2274_ = l_Lean_mkApp3(v___x_2273_, v_00_u03c3s_2263_, v_p_2269_, v_target_2265_);
lean_inc_ref(v_restHyps_2258_);
if (v_isShared_2268_ == 0)
{
lean_ctor_set(v___x_2267_, 3, v___x_2274_);
lean_ctor_set(v___x_2267_, 2, v_restHyps_2258_);
v___x_2276_ = v___x_2267_;
goto v_reusejp_2275_;
}
else
{
lean_object* v_reuseFailAlloc_2289_; 
v_reuseFailAlloc_2289_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2289_, 0, v_u_2262_);
lean_ctor_set(v_reuseFailAlloc_2289_, 1, v_00_u03c3s_2263_);
lean_ctor_set(v_reuseFailAlloc_2289_, 2, v_restHyps_2258_);
lean_ctor_set(v_reuseFailAlloc_2289_, 3, v___x_2274_);
v___x_2276_ = v_reuseFailAlloc_2289_;
goto v_reusejp_2275_;
}
v_reusejp_2275_:
{
lean_object* v___x_2277_; 
lean_inc(v___y_2253_);
lean_inc_ref(v___y_2252_);
lean_inc(v___y_2251_);
lean_inc_ref(v___y_2250_);
lean_inc(v___y_2249_);
lean_inc_ref(v___y_2248_);
lean_inc(v___y_2247_);
lean_inc_ref(v___y_2246_);
v___x_2277_ = lean_apply_10(v_k_2245_, v___x_2276_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, lean_box(0));
if (lean_obj_tag(v___x_2277_) == 0)
{
lean_object* v_a_2278_; lean_object* v___x_2280_; uint8_t v_isShared_2281_; uint8_t v_isSharedCheck_2288_; 
v_a_2278_ = lean_ctor_get(v___x_2277_, 0);
v_isSharedCheck_2288_ = !lean_is_exclusive(v___x_2277_);
if (v_isSharedCheck_2288_ == 0)
{
v___x_2280_ = v___x_2277_;
v_isShared_2281_ = v_isSharedCheck_2288_;
goto v_resetjp_2279_;
}
else
{
lean_inc(v_a_2278_);
lean_dec(v___x_2277_);
v___x_2280_ = lean_box(0);
v_isShared_2281_ = v_isSharedCheck_2288_;
goto v_resetjp_2279_;
}
v_resetjp_2279_:
{
lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v_prf_2284_; lean_object* v___x_2286_; 
v___x_2282_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__4___closed__0));
v___x_2283_ = l_Lean_mkConst(v___x_2282_, v___x_2272_);
v_prf_2284_ = l_Lean_mkApp7(v___x_2283_, v_00_u03c3s_2263_, v_hyps_2264_, v_restHyps_2258_, v_focusHyp_2257_, v_target_2265_, v_proof_2259_, v_a_2278_);
if (v_isShared_2281_ == 0)
{
lean_ctor_set(v___x_2280_, 0, v_prf_2284_);
v___x_2286_ = v___x_2280_;
goto v_reusejp_2285_;
}
else
{
lean_object* v_reuseFailAlloc_2287_; 
v_reuseFailAlloc_2287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2287_, 0, v_prf_2284_);
v___x_2286_ = v_reuseFailAlloc_2287_;
goto v_reusejp_2285_;
}
v_reusejp_2285_:
{
return v___x_2286_;
}
}
}
else
{
lean_dec_ref_known(v___x_2272_, 2);
lean_dec_ref(v_target_2265_);
lean_dec_ref(v_hyps_2264_);
lean_dec_ref(v_00_u03c3s_2263_);
lean_dec_ref(v_proof_2259_);
lean_dec_ref(v_restHyps_2258_);
lean_dec_ref(v_focusHyp_2257_);
return v___x_2277_;
}
}
}
}
else
{
lean_object* v___x_2291_; lean_object* v___x_2292_; 
lean_dec(v___x_2260_);
lean_dec_ref(v_proof_2259_);
lean_dec_ref(v_restHyps_2258_);
lean_dec_ref(v_focusHyp_2257_);
lean_dec_ref(v_k_2245_);
lean_dec_ref(v_goal_2243_);
v___x_2291_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__6, &l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__6_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__6);
v___x_2292_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__8___redArg(v___x_2291_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_);
return v___x_2292_;
}
}
else
{
lean_object* v_a_2293_; lean_object* v___x_2295_; uint8_t v_isShared_2296_; uint8_t v_isSharedCheck_2300_; 
lean_dec_ref(v_k_2245_);
lean_dec_ref(v_goal_2243_);
v_a_2293_ = lean_ctor_get(v___x_2255_, 0);
v_isSharedCheck_2300_ = !lean_is_exclusive(v___x_2255_);
if (v_isSharedCheck_2300_ == 0)
{
v___x_2295_ = v___x_2255_;
v_isShared_2296_ = v_isSharedCheck_2300_;
goto v_resetjp_2294_;
}
else
{
lean_inc(v_a_2293_);
lean_dec(v___x_2255_);
v___x_2295_ = lean_box(0);
v_isShared_2296_ = v_isSharedCheck_2300_;
goto v_resetjp_2294_;
}
v_resetjp_2294_:
{
lean_object* v___x_2298_; 
if (v_isShared_2296_ == 0)
{
v___x_2298_ = v___x_2295_;
goto v_reusejp_2297_;
}
else
{
lean_object* v_reuseFailAlloc_2299_; 
v_reuseFailAlloc_2299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2299_, 0, v_a_2293_);
v___x_2298_ = v_reuseFailAlloc_2299_;
goto v_reusejp_2297_;
}
v_reusejp_2297_:
{
return v___x_2298_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_mRevert___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_2243_ = stack[0].m_obj;
lean_object* v_ref_2244_ = stack[1].m_obj;
lean_object* v_k_2245_ = stack[2].m_obj;
lean_object* v___y_2246_ = stack[3].m_obj;
lean_object* v___y_2247_ = stack[4].m_obj;
lean_object* v___y_2248_ = stack[5].m_obj;
lean_object* v___y_2249_ = stack[6].m_obj;
lean_object* v___y_2250_ = stack[7].m_obj;
lean_object* v___y_2251_ = stack[8].m_obj;
lean_object* v___y_2252_ = stack[9].m_obj;
lean_object* v___y_2253_ = stack[10].m_obj;
lean_object* v_res_2301_;
v_res_2301_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevert___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__4(v_goal_2243_, v_ref_2244_, v_k_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_);
stack->m_obj
 = v_res_2301_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevert___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__4___boxed(lean_object* v_goal_2302_, lean_object* v_ref_2303_, lean_object* v_k_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_){
_start:
{
lean_object* v_res_2314_; 
v_res_2314_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevert___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__4(v_goal_2302_, v_ref_2303_, v_k_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_);
lean_dec(v___y_2312_);
lean_dec_ref(v___y_2311_);
lean_dec(v___y_2310_);
lean_dec_ref(v___y_2309_);
lean_dec(v___y_2308_);
lean_dec_ref(v___y_2307_);
lean_dec(v___y_2306_);
lean_dec_ref(v___y_2305_);
return v_res_2314_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__3(lean_object* v___x_2315_, lean_object* v_val_2316_, lean_object* v_h_2317_, lean_object* v_a_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_){
_start:
{
lean_object* v___x_2328_; lean_object* v___f_2329_; lean_object* v___x_2330_; 
v___x_2328_ = lean_st_mk_ref(v___x_2315_);
lean_inc(v___x_2328_);
v___f_2329_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__0___boxed), 11, 1);
lean_closure_set(v___f_2329_, 0, v___x_2328_);
v___x_2330_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevert___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__4(v_val_2316_, v_h_2317_, v___f_2329_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_);
if (lean_obj_tag(v___x_2330_) == 0)
{
lean_object* v_a_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; 
v_a_2331_ = lean_ctor_get(v___x_2330_, 0);
lean_inc(v_a_2331_);
lean_dec_ref_known(v___x_2330_, 1);
v___x_2332_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2___redArg(v_a_2318_, v_a_2331_, v___y_2324_);
lean_dec_ref(v___x_2332_);
v___x_2333_ = lean_st_ref_get(v___x_2328_);
lean_dec(v___x_2328_);
v___x_2334_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2333_, v___y_2320_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_);
return v___x_2334_;
}
else
{
lean_object* v_a_2335_; lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2342_; 
lean_dec(v___x_2328_);
lean_dec(v_a_2318_);
v_a_2335_ = lean_ctor_get(v___x_2330_, 0);
v_isSharedCheck_2342_ = !lean_is_exclusive(v___x_2330_);
if (v_isSharedCheck_2342_ == 0)
{
v___x_2337_ = v___x_2330_;
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
else
{
lean_inc(v_a_2335_);
lean_dec(v___x_2330_);
v___x_2337_ = lean_box(0);
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
v_resetjp_2336_:
{
lean_object* v___x_2340_; 
if (v_isShared_2338_ == 0)
{
v___x_2340_ = v___x_2337_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v_a_2335_);
v___x_2340_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
return v___x_2340_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2315_ = stack[0].m_obj;
lean_object* v_val_2316_ = stack[1].m_obj;
lean_object* v_h_2317_ = stack[2].m_obj;
lean_object* v_a_2318_ = stack[3].m_obj;
lean_object* v___y_2319_ = stack[4].m_obj;
lean_object* v___y_2320_ = stack[5].m_obj;
lean_object* v___y_2321_ = stack[6].m_obj;
lean_object* v___y_2322_ = stack[7].m_obj;
lean_object* v___y_2323_ = stack[8].m_obj;
lean_object* v___y_2324_ = stack[9].m_obj;
lean_object* v___y_2325_ = stack[10].m_obj;
lean_object* v___y_2326_ = stack[11].m_obj;
lean_object* v_res_2343_;
v_res_2343_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__3(v___x_2315_, v_val_2316_, v_h_2317_, v_a_2318_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_);
stack->m_obj
 = v_res_2343_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__3___boxed(lean_object* v___x_2344_, lean_object* v_val_2345_, lean_object* v_h_2346_, lean_object* v_a_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_){
_start:
{
lean_object* v_res_2357_; 
v_res_2357_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__3(v___x_2344_, v_val_2345_, v_h_2346_, v_a_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_, v___y_2354_, v___y_2355_);
lean_dec(v___y_2355_);
lean_dec_ref(v___y_2354_);
lean_dec(v___y_2353_);
lean_dec_ref(v___y_2352_);
lean_dec(v___y_2351_);
lean_dec_ref(v___y_2350_);
lean_dec(v___y_2349_);
lean_dec_ref(v___y_2348_);
return v_res_2357_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5___redArg(lean_object* v_msg_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_){
_start:
{
lean_object* v_ref_2364_; lean_object* v___x_2365_; lean_object* v_a_2366_; lean_object* v___x_2368_; uint8_t v_isShared_2369_; uint8_t v_isSharedCheck_2374_; 
v_ref_2364_ = lean_ctor_get(v___y_2361_, 2);
v___x_2365_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5_spec__14(v_msg_2358_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_);
v_a_2366_ = lean_ctor_get(v___x_2365_, 0);
v_isSharedCheck_2374_ = !lean_is_exclusive(v___x_2365_);
if (v_isSharedCheck_2374_ == 0)
{
v___x_2368_ = v___x_2365_;
v_isShared_2369_ = v_isSharedCheck_2374_;
goto v_resetjp_2367_;
}
else
{
lean_inc(v_a_2366_);
lean_dec(v___x_2365_);
v___x_2368_ = lean_box(0);
v_isShared_2369_ = v_isSharedCheck_2374_;
goto v_resetjp_2367_;
}
v_resetjp_2367_:
{
lean_object* v___x_2370_; lean_object* v___x_2372_; 
lean_inc(v_ref_2364_);
v___x_2370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2370_, 0, v_ref_2364_);
lean_ctor_set(v___x_2370_, 1, v_a_2366_);
if (v_isShared_2369_ == 0)
{
lean_ctor_set_tag(v___x_2368_, 1);
lean_ctor_set(v___x_2368_, 0, v___x_2370_);
v___x_2372_ = v___x_2368_;
goto v_reusejp_2371_;
}
else
{
lean_object* v_reuseFailAlloc_2373_; 
v_reuseFailAlloc_2373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2373_, 0, v___x_2370_);
v___x_2372_ = v_reuseFailAlloc_2373_;
goto v_reusejp_2371_;
}
v_reusejp_2371_:
{
return v___x_2372_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2358_ = stack[0].m_obj;
lean_object* v___y_2359_ = stack[1].m_obj;
lean_object* v___y_2360_ = stack[2].m_obj;
lean_object* v___y_2361_ = stack[3].m_obj;
lean_object* v___y_2362_ = stack[4].m_obj;
lean_object* v_res_2375_;
v_res_2375_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5___redArg(v_msg_2358_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_);
stack->m_obj
 = v_res_2375_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5___redArg___boxed(lean_object* v_msg_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_){
_start:
{
lean_object* v_res_2382_; 
v_res_2382_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5___redArg(v_msg_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_);
lean_dec(v___y_2380_);
lean_dec_ref(v___y_2379_);
lean_dec(v___y_2378_);
lean_dec_ref(v___y_2377_);
return v_res_2382_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__11(void){
_start:
{
lean_object* v___x_2407_; lean_object* v___x_2408_; 
v___x_2407_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__10));
v___x_2408_ = l_Lean_stringToMessageData(v___x_2407_);
return v___x_2408_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert(lean_object* v_x_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_){
_start:
{
lean_object* v___y_2420_; lean_object* v___y_2421_; lean_object* v___y_2422_; lean_object* v___y_2423_; lean_object* v___y_2424_; lean_object* v___y_2425_; lean_object* v___y_2426_; lean_object* v___y_2427_; lean_object* v___y_2428_; lean_object* v___y_2429_; lean_object* v___y_2430_; lean_object* v___x_2434_; uint8_t v___x_2435_; 
v___x_2434_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__3));
lean_inc(v_x_2409_);
v___x_2435_ = l_Lean_Syntax_isOfKind(v_x_2409_, v___x_2434_);
if (v___x_2435_ == 0)
{
lean_object* v___x_2436_; 
lean_dec(v_x_2409_);
v___x_2436_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg();
return v___x_2436_;
}
else
{
lean_object* v___x_2437_; lean_object* v_n_2439_; lean_object* v___y_2440_; lean_object* v___y_2441_; lean_object* v___y_2442_; lean_object* v___y_2443_; lean_object* v___y_2444_; lean_object* v___y_2445_; lean_object* v___y_2446_; lean_object* v___y_2447_; lean_object* v___x_2464_; uint8_t v___x_2465_; 
v___x_2437_ = lean_unsigned_to_nat(1u);
v___x_2464_ = l_Lean_Syntax_getArg(v_x_2409_, v___x_2437_);
lean_dec(v_x_2409_);
lean_inc(v___x_2464_);
v___x_2465_ = l_Lean_Syntax_matchesNull(v___x_2464_, v___x_2437_);
if (v___x_2465_ == 0)
{
lean_object* v___x_2466_; 
lean_dec(v___x_2464_);
v___x_2466_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg();
return v___x_2466_;
}
else
{
lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; uint8_t v___x_2470_; 
v___x_2467_ = lean_unsigned_to_nat(0u);
v___x_2468_ = l_Lean_Syntax_getArg(v___x_2464_, v___x_2467_);
lean_dec(v___x_2464_);
v___x_2469_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__5));
lean_inc(v___x_2468_);
v___x_2470_ = l_Lean_Syntax_isOfKind(v___x_2468_, v___x_2469_);
if (v___x_2470_ == 0)
{
lean_object* v___x_2471_; uint8_t v___x_2472_; 
v___x_2471_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__7));
lean_inc(v___x_2468_);
v___x_2472_ = l_Lean_Syntax_isOfKind(v___x_2468_, v___x_2471_);
if (v___x_2472_ == 0)
{
lean_object* v___x_2473_; 
lean_dec(v___x_2468_);
v___x_2473_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg();
return v___x_2473_;
}
else
{
lean_object* v___x_2474_; uint8_t v___x_2475_; 
v___x_2474_ = l_Lean_Syntax_getArg(v___x_2468_, v___x_2437_);
lean_dec(v___x_2468_);
v___x_2475_ = l_Lean_Syntax_isNone(v___x_2474_);
if (v___x_2475_ == 0)
{
uint8_t v___x_2476_; 
lean_inc(v___x_2474_);
v___x_2476_ = l_Lean_Syntax_matchesNull(v___x_2474_, v___x_2437_);
if (v___x_2476_ == 0)
{
lean_object* v___x_2477_; 
lean_dec(v___x_2474_);
v___x_2477_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg();
return v___x_2477_;
}
else
{
lean_object* v_n_2478_; lean_object* v___x_2479_; 
v_n_2478_ = l_Lean_Syntax_getArg(v___x_2474_, v___x_2467_);
lean_dec(v___x_2474_);
v___x_2479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2479_, 0, v_n_2478_);
v_n_2439_ = v___x_2479_;
v___y_2440_ = v_a_2410_;
v___y_2441_ = v_a_2411_;
v___y_2442_ = v_a_2412_;
v___y_2443_ = v_a_2413_;
v___y_2444_ = v_a_2414_;
v___y_2445_ = v_a_2415_;
v___y_2446_ = v_a_2416_;
v___y_2447_ = v_a_2417_;
goto v___jp_2438_;
}
}
else
{
lean_object* v___x_2480_; 
lean_dec(v___x_2474_);
v___x_2480_ = lean_box(0);
v_n_2439_ = v___x_2480_;
v___y_2440_ = v_a_2410_;
v___y_2441_ = v_a_2411_;
v___y_2442_ = v_a_2412_;
v___y_2443_ = v_a_2413_;
v___y_2444_ = v_a_2414_;
v___y_2445_ = v_a_2415_;
v___y_2446_ = v_a_2416_;
v___y_2447_ = v_a_2417_;
goto v___jp_2438_;
}
}
}
else
{
lean_object* v_h_2481_; lean_object* v___x_2482_; uint8_t v___x_2483_; 
v_h_2481_ = l_Lean_Syntax_getArg(v___x_2468_, v___x_2467_);
lean_dec(v___x_2468_);
v___x_2482_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__9));
lean_inc(v_h_2481_);
v___x_2483_ = l_Lean_Syntax_isOfKind(v_h_2481_, v___x_2482_);
if (v___x_2483_ == 0)
{
lean_object* v___x_2484_; 
lean_dec(v_h_2481_);
v___x_2484_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg();
return v___x_2484_;
}
else
{
lean_object* v___x_2485_; 
v___x_2485_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_2411_, v_a_2414_, v_a_2415_, v_a_2416_, v_a_2417_);
if (lean_obj_tag(v___x_2485_) == 0)
{
lean_object* v_a_2486_; lean_object* v___x_2487_; 
v_a_2486_ = lean_ctor_get(v___x_2485_, 0);
lean_inc_n(v_a_2486_, 2);
lean_dec_ref_known(v___x_2485_, 1);
v___x_2487_ = l_Lean_MVarId_getType(v_a_2486_, v_a_2414_, v_a_2415_, v_a_2416_, v_a_2417_);
if (lean_obj_tag(v___x_2487_) == 0)
{
lean_object* v_a_2488_; lean_object* v___x_2489_; 
v_a_2488_ = lean_ctor_get(v___x_2487_, 0);
lean_inc(v_a_2488_);
lean_dec_ref_known(v___x_2487_, 1);
v___x_2489_ = l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f(v_a_2488_);
lean_dec(v_a_2488_);
if (lean_obj_tag(v___x_2489_) == 1)
{
lean_object* v_val_2490_; lean_object* v___x_2491_; lean_object* v___f_2492_; lean_object* v___x_2493_; 
v_val_2490_ = lean_ctor_get(v___x_2489_, 0);
lean_inc(v_val_2490_);
lean_dec_ref_known(v___x_2489_, 1);
v___x_2491_ = lean_box(0);
lean_inc(v_a_2486_);
v___f_2492_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__3___boxed), 13, 4);
lean_closure_set(v___f_2492_, 0, v___x_2491_);
lean_closure_set(v___f_2492_, 1, v_val_2490_);
lean_closure_set(v___f_2492_, 2, v_h_2481_);
lean_closure_set(v___f_2492_, 3, v_a_2486_);
v___x_2493_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___redArg(v_a_2486_, v___f_2492_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_, v_a_2414_, v_a_2415_, v_a_2416_, v_a_2417_);
return v___x_2493_;
}
else
{
lean_object* v___x_2494_; lean_object* v___x_2495_; 
lean_dec(v___x_2489_);
lean_dec(v_a_2486_);
lean_dec(v_h_2481_);
v___x_2494_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__11, &l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__11_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__11);
v___x_2495_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5___redArg(v___x_2494_, v_a_2414_, v_a_2415_, v_a_2416_, v_a_2417_);
return v___x_2495_;
}
}
else
{
lean_object* v_a_2496_; lean_object* v___x_2498_; uint8_t v_isShared_2499_; uint8_t v_isSharedCheck_2503_; 
lean_dec(v_a_2486_);
lean_dec(v_h_2481_);
v_a_2496_ = lean_ctor_get(v___x_2487_, 0);
v_isSharedCheck_2503_ = !lean_is_exclusive(v___x_2487_);
if (v_isSharedCheck_2503_ == 0)
{
v___x_2498_ = v___x_2487_;
v_isShared_2499_ = v_isSharedCheck_2503_;
goto v_resetjp_2497_;
}
else
{
lean_inc(v_a_2496_);
lean_dec(v___x_2487_);
v___x_2498_ = lean_box(0);
v_isShared_2499_ = v_isSharedCheck_2503_;
goto v_resetjp_2497_;
}
v_resetjp_2497_:
{
lean_object* v___x_2501_; 
if (v_isShared_2499_ == 0)
{
v___x_2501_ = v___x_2498_;
goto v_reusejp_2500_;
}
else
{
lean_object* v_reuseFailAlloc_2502_; 
v_reuseFailAlloc_2502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2502_, 0, v_a_2496_);
v___x_2501_ = v_reuseFailAlloc_2502_;
goto v_reusejp_2500_;
}
v_reusejp_2500_:
{
return v___x_2501_;
}
}
}
}
else
{
lean_object* v_a_2504_; lean_object* v___x_2506_; uint8_t v_isShared_2507_; uint8_t v_isSharedCheck_2511_; 
lean_dec(v_h_2481_);
v_a_2504_ = lean_ctor_get(v___x_2485_, 0);
v_isSharedCheck_2511_ = !lean_is_exclusive(v___x_2485_);
if (v_isSharedCheck_2511_ == 0)
{
v___x_2506_ = v___x_2485_;
v_isShared_2507_ = v_isSharedCheck_2511_;
goto v_resetjp_2505_;
}
else
{
lean_inc(v_a_2504_);
lean_dec(v___x_2485_);
v___x_2506_ = lean_box(0);
v_isShared_2507_ = v_isSharedCheck_2511_;
goto v_resetjp_2505_;
}
v_resetjp_2505_:
{
lean_object* v___x_2509_; 
if (v_isShared_2507_ == 0)
{
v___x_2509_ = v___x_2506_;
goto v_reusejp_2508_;
}
else
{
lean_object* v_reuseFailAlloc_2510_; 
v_reuseFailAlloc_2510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2510_, 0, v_a_2504_);
v___x_2509_ = v_reuseFailAlloc_2510_;
goto v_reusejp_2508_;
}
v_reusejp_2508_:
{
return v___x_2509_;
}
}
}
}
}
}
v___jp_2438_:
{
lean_object* v___x_2448_; 
v___x_2448_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg(v___y_2441_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_);
if (lean_obj_tag(v___x_2448_) == 0)
{
lean_object* v_a_2449_; 
v_a_2449_ = lean_ctor_get(v___x_2448_, 0);
lean_inc(v_a_2449_);
lean_dec_ref_known(v___x_2448_, 1);
if (lean_obj_tag(v_n_2439_) == 0)
{
lean_object* v_fst_2450_; lean_object* v_snd_2451_; 
v_fst_2450_ = lean_ctor_get(v_a_2449_, 0);
lean_inc(v_fst_2450_);
v_snd_2451_ = lean_ctor_get(v_a_2449_, 1);
lean_inc(v_snd_2451_);
lean_dec(v_a_2449_);
v___y_2420_ = v_snd_2451_;
v___y_2421_ = v_fst_2450_;
v___y_2422_ = v___y_2444_;
v___y_2423_ = v___y_2447_;
v___y_2424_ = v___y_2441_;
v___y_2425_ = v___y_2446_;
v___y_2426_ = v___y_2445_;
v___y_2427_ = v___y_2442_;
v___y_2428_ = v___y_2440_;
v___y_2429_ = v___y_2443_;
v___y_2430_ = v___x_2437_;
goto v___jp_2419_;
}
else
{
lean_object* v_fst_2452_; lean_object* v_snd_2453_; lean_object* v_val_2454_; lean_object* v___x_2455_; 
v_fst_2452_ = lean_ctor_get(v_a_2449_, 0);
lean_inc(v_fst_2452_);
v_snd_2453_ = lean_ctor_get(v_a_2449_, 1);
lean_inc(v_snd_2453_);
lean_dec(v_a_2449_);
v_val_2454_ = lean_ctor_get(v_n_2439_, 0);
lean_inc(v_val_2454_);
lean_dec_ref_known(v_n_2439_, 1);
v___x_2455_ = l_Lean_TSyntax_getNat(v_val_2454_);
lean_dec(v_val_2454_);
v___y_2420_ = v_snd_2453_;
v___y_2421_ = v_fst_2452_;
v___y_2422_ = v___y_2444_;
v___y_2423_ = v___y_2447_;
v___y_2424_ = v___y_2441_;
v___y_2425_ = v___y_2446_;
v___y_2426_ = v___y_2445_;
v___y_2427_ = v___y_2442_;
v___y_2428_ = v___y_2440_;
v___y_2429_ = v___y_2443_;
v___y_2430_ = v___x_2455_;
goto v___jp_2419_;
}
}
else
{
lean_object* v_a_2456_; lean_object* v___x_2458_; uint8_t v_isShared_2459_; uint8_t v_isSharedCheck_2463_; 
lean_dec(v_n_2439_);
v_a_2456_ = lean_ctor_get(v___x_2448_, 0);
v_isSharedCheck_2463_ = !lean_is_exclusive(v___x_2448_);
if (v_isSharedCheck_2463_ == 0)
{
v___x_2458_ = v___x_2448_;
v_isShared_2459_ = v_isSharedCheck_2463_;
goto v_resetjp_2457_;
}
else
{
lean_inc(v_a_2456_);
lean_dec(v___x_2448_);
v___x_2458_ = lean_box(0);
v_isShared_2459_ = v_isSharedCheck_2463_;
goto v_resetjp_2457_;
}
v_resetjp_2457_:
{
lean_object* v___x_2461_; 
if (v_isShared_2459_ == 0)
{
v___x_2461_ = v___x_2458_;
goto v_reusejp_2460_;
}
else
{
lean_object* v_reuseFailAlloc_2462_; 
v_reuseFailAlloc_2462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2462_, 0, v_a_2456_);
v___x_2461_ = v_reuseFailAlloc_2462_;
goto v_reusejp_2460_;
}
v_reusejp_2460_:
{
return v___x_2461_;
}
}
}
}
}
v___jp_2419_:
{
lean_object* v___x_2431_; lean_object* v___f_2432_; lean_object* v___x_2433_; 
v___x_2431_ = lean_box(0);
lean_inc(v___y_2421_);
v___f_2432_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__1___boxed), 13, 4);
lean_closure_set(v___f_2432_, 0, v___x_2431_);
lean_closure_set(v___f_2432_, 1, v___y_2420_);
lean_closure_set(v___f_2432_, 2, v___y_2430_);
lean_closure_set(v___f_2432_, 3, v___y_2421_);
v___x_2433_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___redArg(v___y_2421_, v___f_2432_, v___y_2428_, v___y_2424_, v___y_2427_, v___y_2429_, v___y_2422_, v___y_2426_, v___y_2425_, v___y_2423_);
return v___x_2433_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2409_ = stack[0].m_obj;
lean_object* v_a_2410_ = stack[1].m_obj;
lean_object* v_a_2411_ = stack[2].m_obj;
lean_object* v_a_2412_ = stack[3].m_obj;
lean_object* v_a_2413_ = stack[4].m_obj;
lean_object* v_a_2414_ = stack[5].m_obj;
lean_object* v_a_2415_ = stack[6].m_obj;
lean_object* v_a_2416_ = stack[7].m_obj;
lean_object* v_a_2417_ = stack[8].m_obj;
lean_object* v_res_2512_;
v_res_2512_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert(v_x_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_, v_a_2414_, v_a_2415_, v_a_2416_, v_a_2417_);
stack->m_obj
 = v_res_2512_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___boxed(lean_object* v_x_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_, lean_object* v_a_2520_, lean_object* v_a_2521_, lean_object* v_a_2522_){
_start:
{
lean_object* v_res_2523_; 
v_res_2523_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert(v_x_2513_, v_a_2514_, v_a_2515_, v_a_2516_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_, v_a_2521_);
lean_dec(v_a_2521_);
lean_dec_ref(v_a_2520_);
lean_dec(v_a_2519_);
lean_dec_ref(v_a_2518_);
lean_dec(v_a_2517_);
lean_dec_ref(v_a_2516_);
lean_dec(v_a_2515_);
lean_dec_ref(v_a_2514_);
return v_res_2523_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2(lean_object* v_mvarId_2524_, lean_object* v_val_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_){
_start:
{
lean_object* v___x_2535_; 
v___x_2535_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2___redArg(v_mvarId_2524_, v_val_2525_, v___y_2531_);
return v___x_2535_;
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_2524_ = stack[0].m_obj;
lean_object* v_val_2525_ = stack[1].m_obj;
lean_object* v___y_2526_ = stack[2].m_obj;
lean_object* v___y_2527_ = stack[3].m_obj;
lean_object* v___y_2528_ = stack[4].m_obj;
lean_object* v___y_2529_ = stack[5].m_obj;
lean_object* v___y_2530_ = stack[6].m_obj;
lean_object* v___y_2531_ = stack[7].m_obj;
lean_object* v___y_2532_ = stack[8].m_obj;
lean_object* v___y_2533_ = stack[9].m_obj;
lean_object* v_res_2536_;
v_res_2536_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2(v_mvarId_2524_, v_val_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_);
stack->m_obj
 = v_res_2536_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2___boxed(lean_object* v_mvarId_2537_, lean_object* v_val_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_){
_start:
{
lean_object* v_res_2548_; 
v_res_2548_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2(v_mvarId_2537_, v_val_2538_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_);
lean_dec(v___y_2546_);
lean_dec_ref(v___y_2545_);
lean_dec(v___y_2544_);
lean_dec_ref(v___y_2543_);
lean_dec(v___y_2542_);
lean_dec_ref(v___y_2541_);
lean_dec(v___y_2540_);
lean_dec_ref(v___y_2539_);
return v_res_2548_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5(lean_object* v_00_u03b1_2549_, lean_object* v_msg_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_){
_start:
{
lean_object* v___x_2560_; 
v___x_2560_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5___redArg(v_msg_2550_, v___y_2555_, v___y_2556_, v___y_2557_, v___y_2558_);
return v___x_2560_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2550_ = stack[1].m_obj;
lean_object* v___y_2551_ = stack[2].m_obj;
lean_object* v___y_2552_ = stack[3].m_obj;
lean_object* v___y_2553_ = stack[4].m_obj;
lean_object* v___y_2554_ = stack[5].m_obj;
lean_object* v___y_2555_ = stack[6].m_obj;
lean_object* v___y_2556_ = stack[7].m_obj;
lean_object* v___y_2557_ = stack[8].m_obj;
lean_object* v___y_2558_ = stack[9].m_obj;
lean_object* v_res_2561_;
v_res_2561_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5(lean_box(0), v_msg_2550_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_, v___y_2558_);
stack->m_obj
 = v_res_2561_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5___boxed(lean_object* v_00_u03b1_2562_, lean_object* v_msg_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_){
_start:
{
lean_object* v_res_2573_; 
v_res_2573_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5(v_00_u03b1_2562_, v_msg_2563_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_);
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
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__1(lean_object* v_inst_2574_, lean_object* v_R_2575_, lean_object* v_a_2576_, lean_object* v_b_2577_){
_start:
{
lean_object* v___x_2578_; 
v___x_2578_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__1___redArg(v_a_2576_, v_b_2577_);
return v___x_2578_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__2(size_t v_sz_2579_, size_t v_i_2580_, lean_object* v_bs_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_){
_start:
{
lean_object* v___x_2591_; 
v___x_2591_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__2___redArg(v_sz_2579_, v_i_2580_, v_bs_2581_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_);
return v___x_2591_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
size_t v_sz_2579_ = stack[0].m_num;
size_t v_i_2580_ = stack[1].m_num;
lean_object* v_bs_2581_ = stack[2].m_obj;
lean_object* v___y_2582_ = stack[3].m_obj;
lean_object* v___y_2583_ = stack[4].m_obj;
lean_object* v___y_2584_ = stack[5].m_obj;
lean_object* v___y_2585_ = stack[6].m_obj;
lean_object* v___y_2586_ = stack[7].m_obj;
lean_object* v___y_2587_ = stack[8].m_obj;
lean_object* v___y_2588_ = stack[9].m_obj;
lean_object* v___y_2589_ = stack[10].m_obj;
lean_object* v_res_2592_;
v_res_2592_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__2(v_sz_2579_, v_i_2580_, v_bs_2581_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_);
stack->m_obj
 = v_res_2592_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__2___boxed(lean_object* v_sz_2593_, lean_object* v_i_2594_, lean_object* v_bs_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_){
_start:
{
size_t v_sz_boxed_2605_; size_t v_i_boxed_2606_; lean_object* v_res_2607_; 
v_sz_boxed_2605_ = lean_unbox_usize(v_sz_2593_);
lean_dec(v_sz_2593_);
v_i_boxed_2606_ = lean_unbox_usize(v_i_2594_);
lean_dec(v_i_2594_);
v_res_2607_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__2(v_sz_boxed_2605_, v_i_boxed_2606_, v_bs_2595_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_);
lean_dec(v___y_2603_);
lean_dec_ref(v___y_2602_);
lean_dec(v___y_2601_);
lean_dec_ref(v___y_2600_);
lean_dec(v___y_2599_);
lean_dec_ref(v___y_2598_);
lean_dec(v___y_2597_);
lean_dec_ref(v___y_2596_);
return v_res_2607_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__4(lean_object* v_as_2608_, size_t v_sz_2609_, size_t v_i_2610_, lean_object* v_bs_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_){
_start:
{
lean_object* v___x_2621_; 
v___x_2621_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__4___redArg(v_sz_2609_, v_i_2610_, v_bs_2611_, v___y_2618_, v___y_2619_);
return v___x_2621_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2608_ = stack[0].m_obj;
size_t v_sz_2609_ = stack[1].m_num;
size_t v_i_2610_ = stack[2].m_num;
lean_object* v_bs_2611_ = stack[3].m_obj;
lean_object* v___y_2612_ = stack[4].m_obj;
lean_object* v___y_2613_ = stack[5].m_obj;
lean_object* v___y_2614_ = stack[6].m_obj;
lean_object* v___y_2615_ = stack[7].m_obj;
lean_object* v___y_2616_ = stack[8].m_obj;
lean_object* v___y_2617_ = stack[9].m_obj;
lean_object* v___y_2618_ = stack[10].m_obj;
lean_object* v___y_2619_ = stack[11].m_obj;
lean_object* v_res_2622_;
v_res_2622_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__4(v_as_2608_, v_sz_2609_, v_i_2610_, v_bs_2611_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_);
stack->m_obj
 = v_res_2622_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__4___boxed(lean_object* v_as_2623_, lean_object* v_sz_2624_, lean_object* v_i_2625_, lean_object* v_bs_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_){
_start:
{
size_t v_sz_boxed_2636_; size_t v_i_boxed_2637_; lean_object* v_res_2638_; 
v_sz_boxed_2636_ = lean_unbox_usize(v_sz_2624_);
lean_dec(v_sz_2624_);
v_i_boxed_2637_ = lean_unbox_usize(v_i_2625_);
lean_dec(v_i_2625_);
v_res_2638_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__4(v_as_2623_, v_sz_boxed_2636_, v_i_boxed_2637_, v_bs_2626_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_);
lean_dec(v___y_2634_);
lean_dec_ref(v___y_2633_);
lean_dec(v___y_2632_);
lean_dec_ref(v___y_2631_);
lean_dec(v___y_2630_);
lean_dec_ref(v___y_2629_);
lean_dec(v___y_2628_);
lean_dec_ref(v___y_2627_);
lean_dec_ref(v_as_2623_);
return v_res_2638_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__8(lean_object* v_00_u03b1_2639_, lean_object* v_msg_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_){
_start:
{
lean_object* v___x_2646_; 
v___x_2646_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__8___redArg(v_msg_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_);
return v___x_2646_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2640_ = stack[1].m_obj;
lean_object* v___y_2641_ = stack[2].m_obj;
lean_object* v___y_2642_ = stack[3].m_obj;
lean_object* v___y_2643_ = stack[4].m_obj;
lean_object* v___y_2644_ = stack[5].m_obj;
lean_object* v_res_2647_;
v_res_2647_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__8(lean_box(0), v_msg_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_);
stack->m_obj
 = v_res_2647_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__8___boxed(lean_object* v_00_u03b1_2648_, lean_object* v_msg_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_){
_start:
{
lean_object* v_res_2655_; 
v_res_2655_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__8(v_00_u03b1_2648_, v_msg_2649_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_);
lean_dec(v___y_2653_);
lean_dec_ref(v___y_2652_);
lean_dec(v___y_2651_);
lean_dec_ref(v___y_2650_);
return v_res_2655_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10(lean_object* v_00_u03b2_2656_, lean_object* v_x_2657_, lean_object* v_x_2658_, lean_object* v_x_2659_){
_start:
{
lean_object* v___x_2660_; 
v___x_2660_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10___redArg(v_x_2657_, v_x_2658_, v_x_2659_);
return v___x_2660_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14(lean_object* v_00_u03b2_2661_, lean_object* v_x_2662_, size_t v_x_2663_, size_t v_x_2664_, lean_object* v_x_2665_, lean_object* v_x_2666_){
_start:
{
lean_object* v___x_2667_; 
v___x_2667_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14___redArg(v_x_2662_, v_x_2663_, v_x_2664_, v_x_2665_, v_x_2666_);
return v___x_2667_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2662_ = stack[1].m_obj;
size_t v_x_2663_ = stack[2].m_num;
size_t v_x_2664_ = stack[3].m_num;
lean_object* v_x_2665_ = stack[4].m_obj;
lean_object* v_x_2666_ = stack[5].m_obj;
lean_object* v_res_2668_;
v_res_2668_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14(lean_box(0), v_x_2662_, v_x_2663_, v_x_2664_, v_x_2665_, v_x_2666_);
stack->m_obj
 = v_res_2668_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14___boxed(lean_object* v_00_u03b2_2669_, lean_object* v_x_2670_, lean_object* v_x_2671_, lean_object* v_x_2672_, lean_object* v_x_2673_, lean_object* v_x_2674_){
_start:
{
size_t v_x_20809__boxed_2675_; size_t v_x_20810__boxed_2676_; lean_object* v_res_2677_; 
v_x_20809__boxed_2675_ = lean_unbox_usize(v_x_2671_);
lean_dec(v_x_2671_);
v_x_20810__boxed_2676_ = lean_unbox_usize(v_x_2672_);
lean_dec(v_x_2672_);
v_res_2677_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14(v_00_u03b2_2669_, v_x_2670_, v_x_20809__boxed_2675_, v_x_20810__boxed_2676_, v_x_2673_, v_x_2674_);
return v_res_2677_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14_spec__20(lean_object* v_00_u03b2_2678_, lean_object* v_n_2679_, lean_object* v_k_2680_, lean_object* v_v_2681_){
_start:
{
lean_object* v___x_2682_; 
v___x_2682_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14_spec__20___redArg(v_n_2679_, v_k_2680_, v_v_2681_);
return v___x_2682_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14_spec__21(lean_object* v_00_u03b2_2683_, size_t v_depth_2684_, lean_object* v_keys_2685_, lean_object* v_vals_2686_, lean_object* v_heq_2687_, lean_object* v_i_2688_, lean_object* v_entries_2689_){
_start:
{
lean_object* v___x_2690_; 
v___x_2690_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14_spec__21___redArg(v_depth_2684_, v_keys_2685_, v_vals_2686_, v_i_2688_, v_entries_2689_);
return v___x_2690_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14_spec__21_0interp(lean_interpreter_value* stack)
{
size_t v_depth_2684_ = stack[1].m_num;
lean_object* v_keys_2685_ = stack[2].m_obj;
lean_object* v_vals_2686_ = stack[3].m_obj;
lean_object* v_i_2688_ = stack[5].m_obj;
lean_object* v_entries_2689_ = stack[6].m_obj;
lean_object* v_res_2691_;
v_res_2691_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14_spec__21(lean_box(0), v_depth_2684_, v_keys_2685_, v_vals_2686_, lean_box(0), v_i_2688_, v_entries_2689_);
stack->m_obj
 = v_res_2691_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14_spec__21___boxed(lean_object* v_00_u03b2_2692_, lean_object* v_depth_2693_, lean_object* v_keys_2694_, lean_object* v_vals_2695_, lean_object* v_heq_2696_, lean_object* v_i_2697_, lean_object* v_entries_2698_){
_start:
{
size_t v_depth_boxed_2699_; lean_object* v_res_2700_; 
v_depth_boxed_2699_ = lean_unbox_usize(v_depth_2693_);
lean_dec(v_depth_2693_);
v_res_2700_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14_spec__21(v_00_u03b2_2692_, v_depth_boxed_2699_, v_keys_2694_, v_vals_2695_, v_heq_2696_, v_i_2697_, v_entries_2698_);
lean_dec_ref(v_vals_2695_);
lean_dec_ref(v_keys_2694_);
return v_res_2700_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19_spec__21(lean_object* v_00_u03b1_2701_, lean_object* v_name_2702_, uint8_t v_bi_2703_, lean_object* v_type_2704_, lean_object* v_k_2705_, uint8_t v_kind_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_){
_start:
{
lean_object* v___x_2716_; 
v___x_2716_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19_spec__21___redArg(v_name_2702_, v_bi_2703_, v_type_2704_, v_k_2705_, v_kind_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_);
return v___x_2716_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19_spec__21_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_2702_ = stack[1].m_obj;
uint8_t v_bi_2703_ = stack[2].m_num;
lean_object* v_type_2704_ = stack[3].m_obj;
lean_object* v_k_2705_ = stack[4].m_obj;
uint8_t v_kind_2706_ = stack[5].m_num;
lean_object* v___y_2707_ = stack[6].m_obj;
lean_object* v___y_2708_ = stack[7].m_obj;
lean_object* v___y_2709_ = stack[8].m_obj;
lean_object* v___y_2710_ = stack[9].m_obj;
lean_object* v___y_2711_ = stack[10].m_obj;
lean_object* v___y_2712_ = stack[11].m_obj;
lean_object* v___y_2713_ = stack[12].m_obj;
lean_object* v___y_2714_ = stack[13].m_obj;
lean_object* v_res_2717_;
v_res_2717_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19_spec__21(lean_box(0), v_name_2702_, v_bi_2703_, v_type_2704_, v_k_2705_, v_kind_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_);
stack->m_obj
 = v_res_2717_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19_spec__21___boxed(lean_object* v_00_u03b1_2718_, lean_object* v_name_2719_, lean_object* v_bi_2720_, lean_object* v_type_2721_, lean_object* v_k_2722_, lean_object* v_kind_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_){
_start:
{
uint8_t v_bi_boxed_2733_; uint8_t v_kind_boxed_2734_; lean_object* v_res_2735_; 
v_bi_boxed_2733_ = lean_unbox(v_bi_2720_);
v_kind_boxed_2734_ = lean_unbox(v_kind_2723_);
v_res_2735_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19_spec__21(v_00_u03b1_2718_, v_name_2719_, v_bi_boxed_2733_, v_type_2721_, v_k_2722_, v_kind_boxed_2734_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_, v___y_2731_);
lean_dec(v___y_2731_);
lean_dec_ref(v___y_2730_);
lean_dec(v___y_2729_);
lean_dec_ref(v___y_2728_);
lean_dec(v___y_2727_);
lean_dec_ref(v___y_2726_);
lean_dec(v___y_2725_);
lean_dec_ref(v___y_2724_);
return v_res_2735_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14_spec__20_spec__22(lean_object* v_00_u03b2_2736_, lean_object* v_x_2737_, lean_object* v_x_2738_, lean_object* v_x_2739_, lean_object* v_x_2740_){
_start:
{
lean_object* v___x_2741_; 
v___x_2741_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14_spec__20_spec__22___redArg(v_x_2737_, v_x_2738_, v_x_2739_, v_x_2740_);
return v___x_2741_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Revert_0__Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1(){
_start:
{
lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; 
v___x_2753_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2754_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__3));
v___x_2755_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Revert_0__Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__3));
v___x_2756_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___boxed), 10, 0);
v___x_2757_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2753_, v___x_2754_, v___x_2755_, v___x_2756_);
return v___x_2757_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Do_ProofMode_Revert_0__Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2758_;
v_res_2758_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Revert_0__Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1();
stack->m_obj
 = v_res_2758_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Revert_0__Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___boxed(lean_object* v_a_2759_){
_start:
{
lean_object* v_res_2760_; 
v_res_2760_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Revert_0__Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1();
return v_res_2760_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Revert(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Do_ProofMode_Revert_0__Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1();
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
