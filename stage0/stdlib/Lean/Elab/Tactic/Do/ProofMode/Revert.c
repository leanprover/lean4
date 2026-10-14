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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__2(lean_object* v_hypName_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = l_Lean_Core_mkFreshUserName(v_hypName_203_, v___y_206_, v___y_207_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__2___boxed(lean_object* v_hypName_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__2(v_hypName_210_, v___y_211_, v___y_212_, v___y_213_, v___y_214_);
lean_dec(v___y_214_);
lean_dec_ref(v___y_213_);
lean_dec(v___y_212_);
lean_dec_ref(v___y_211_);
return v_res_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__3(lean_object* v_i_217_, lean_object* v_a_218_, lean_object* v_toPure_219_, lean_object* v_____do__lift_220_){
_start:
{
lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_221_ = lean_unsigned_to_nat(1u);
v___x_222_ = lean_nat_add(v_i_217_, v___x_221_);
v___x_223_ = lean_name_append_index_after(v_____do__lift_220_, v___x_222_);
v___x_224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_224_, 0, v___x_223_);
lean_ctor_set(v___x_224_, 1, v_a_218_);
v___x_225_ = lean_apply_2(v_toPure_219_, lean_box(0), v___x_224_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__3___boxed(lean_object* v_i_226_, lean_object* v_a_227_, lean_object* v_toPure_228_, lean_object* v_____do__lift_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__3(v_i_226_, v_a_227_, v_toPure_228_, v_____do__lift_229_);
lean_dec(v_i_226_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__4(lean_object* v___x_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_){
_start:
{
lean_object* v___x_237_; 
v___x_237_ = l_Lean_Core_mkFreshUserName(v___x_231_, v___y_234_, v___y_235_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__4___boxed(lean_object* v___x_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__4(v___x_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_);
lean_dec(v___y_242_);
lean_dec_ref(v___y_241_);
lean_dec(v___y_240_);
lean_dec_ref(v___y_239_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__5(lean_object* v_toPure_250_, lean_object* v_inst_251_, lean_object* v_toBind_252_, lean_object* v_i_253_, lean_object* v_a_254_, lean_object* v_x_255_){
_start:
{
lean_object* v___f_256_; lean_object* v___f_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v___f_256_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__3___boxed), 4, 3);
lean_closure_set(v___f_256_, 0, v_i_253_);
lean_closure_set(v___f_256_, 1, v_a_254_);
lean_closure_set(v___f_256_, 2, v_toPure_250_);
v___f_257_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__5___closed__2));
v___x_258_ = lean_apply_2(v_inst_251_, lean_box(0), v___f_257_);
v___x_259_ = lean_apply_4(v_toBind_252_, lean_box(0), lean_box(0), v___x_258_, v___f_256_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__6(lean_object* v_u_260_, lean_object* v_x1_261_, lean_object* v_x2_262_){
_start:
{
lean_object* v___x_263_; 
v___x_263_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkCons(v_u_260_, v_x1_261_, v_x2_262_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__7(lean_object* v_00_u03c6_264_, lean_object* v_toPure_265_, lean_object* v_____do__lift_266_){
_start:
{
lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_267_, 0, v_____do__lift_266_);
lean_ctor_set(v___x_267_, 1, v_00_u03c6_264_);
v___x_268_ = lean_apply_2(v_toPure_265_, lean_box(0), v___x_267_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__8(lean_object* v_hypName_269_, lean_object* v_uniq_270_, lean_object* v_toPure_271_, lean_object* v_ss_272_, lean_object* v_hyps_273_, uint8_t v___x_274_, uint8_t v___x_275_, uint8_t v___x_276_, lean_object* v_inst_277_, lean_object* v_toBind_278_, lean_object* v_____do__lift_279_){
_start:
{
lean_object* v___x_280_; lean_object* v_00_u03c6_281_; lean_object* v___f_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_280_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_280_, 0, v_hypName_269_);
lean_ctor_set(v___x_280_, 1, v_uniq_270_);
lean_ctor_set(v___x_280_, 2, v_____do__lift_279_);
v_00_u03c6_281_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_280_);
v___f_282_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__7), 3, 2);
lean_closure_set(v___f_282_, 0, v_00_u03c6_281_);
lean_closure_set(v___f_282_, 1, v_toPure_271_);
v___x_283_ = lean_box(v___x_274_);
v___x_284_ = lean_box(v___x_275_);
v___x_285_ = lean_box(v___x_274_);
v___x_286_ = lean_box(v___x_275_);
v___x_287_ = lean_box(v___x_276_);
v___x_288_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(v___x_288_, 0, v_ss_272_);
lean_closure_set(v___x_288_, 1, v_hyps_273_);
lean_closure_set(v___x_288_, 2, v___x_283_);
lean_closure_set(v___x_288_, 3, v___x_284_);
lean_closure_set(v___x_288_, 4, v___x_285_);
lean_closure_set(v___x_288_, 5, v___x_286_);
lean_closure_set(v___x_288_, 6, v___x_287_);
v___x_289_ = lean_apply_2(v_inst_277_, lean_box(0), v___x_288_);
v___x_290_ = lean_apply_4(v_toBind_278_, lean_box(0), lean_box(0), v___x_289_, v___f_282_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__8___boxed(lean_object* v_hypName_291_, lean_object* v_uniq_292_, lean_object* v_toPure_293_, lean_object* v_ss_294_, lean_object* v_hyps_295_, lean_object* v___x_296_, lean_object* v___x_297_, lean_object* v___x_298_, lean_object* v_inst_299_, lean_object* v_toBind_300_, lean_object* v_____do__lift_301_){
_start:
{
uint8_t v___x_1076__boxed_302_; uint8_t v___x_1077__boxed_303_; uint8_t v___x_1078__boxed_304_; lean_object* v_res_305_; 
v___x_1076__boxed_302_ = lean_unbox(v___x_296_);
v___x_1077__boxed_303_ = lean_unbox(v___x_297_);
v___x_1078__boxed_304_ = lean_unbox(v___x_298_);
v_res_305_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__8(v_hypName_291_, v_uniq_292_, v_toPure_293_, v_ss_294_, v_hyps_295_, v___x_1076__boxed_302_, v___x_1077__boxed_303_, v___x_1078__boxed_304_, v_inst_299_, v_toBind_300_, v_____do__lift_301_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__9(lean_object* v_hypName_306_, lean_object* v_toPure_307_, lean_object* v_ss_308_, lean_object* v_hyps_309_, uint8_t v___x_310_, lean_object* v_inst_311_, lean_object* v_toBind_312_, lean_object* v_00_u03c6_313_, lean_object* v_uniq_314_){
_start:
{
uint8_t v___x_315_; uint8_t v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___f_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_315_ = 1;
v___x_316_ = 1;
v___x_317_ = lean_box(v___x_310_);
v___x_318_ = lean_box(v___x_315_);
v___x_319_ = lean_box(v___x_316_);
lean_inc(v_toBind_312_);
lean_inc(v_inst_311_);
lean_inc_ref(v_ss_308_);
v___f_320_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__8___boxed), 11, 10);
lean_closure_set(v___f_320_, 0, v_hypName_306_);
lean_closure_set(v___f_320_, 1, v_uniq_314_);
lean_closure_set(v___f_320_, 2, v_toPure_307_);
lean_closure_set(v___f_320_, 3, v_ss_308_);
lean_closure_set(v___f_320_, 4, v_hyps_309_);
lean_closure_set(v___f_320_, 5, v___x_317_);
lean_closure_set(v___f_320_, 6, v___x_318_);
lean_closure_set(v___f_320_, 7, v___x_319_);
lean_closure_set(v___f_320_, 8, v_inst_311_);
lean_closure_set(v___f_320_, 9, v_toBind_312_);
v___x_321_ = lean_box(v___x_310_);
v___x_322_ = lean_box(v___x_315_);
v___x_323_ = lean_box(v___x_310_);
v___x_324_ = lean_box(v___x_315_);
v___x_325_ = lean_box(v___x_316_);
v___x_326_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(v___x_326_, 0, v_ss_308_);
lean_closure_set(v___x_326_, 1, v_00_u03c6_313_);
lean_closure_set(v___x_326_, 2, v___x_321_);
lean_closure_set(v___x_326_, 3, v___x_322_);
lean_closure_set(v___x_326_, 4, v___x_323_);
lean_closure_set(v___x_326_, 5, v___x_324_);
lean_closure_set(v___x_326_, 6, v___x_325_);
v___x_327_ = lean_apply_2(v_inst_311_, lean_box(0), v___x_326_);
v___x_328_ = lean_apply_4(v_toBind_312_, lean_box(0), lean_box(0), v___x_327_, v___f_320_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__9___boxed(lean_object* v_hypName_329_, lean_object* v_toPure_330_, lean_object* v_ss_331_, lean_object* v_hyps_332_, lean_object* v___x_333_, lean_object* v_inst_334_, lean_object* v_toBind_335_, lean_object* v_00_u03c6_336_, lean_object* v_uniq_337_){
_start:
{
uint8_t v___x_1111__boxed_338_; lean_object* v_res_339_; 
v___x_1111__boxed_338_ = lean_unbox(v___x_333_);
v_res_339_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__9(v_hypName_329_, v_toPure_330_, v_ss_331_, v_hyps_332_, v___x_1111__boxed_338_, v_inst_334_, v_toBind_335_, v_00_u03c6_336_, v_uniq_337_);
return v_res_339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__10(lean_object* v_u_340_, lean_object* v_00_u03c3s_341_, lean_object* v_hypName_342_, lean_object* v_toPure_343_, lean_object* v_ss_344_, lean_object* v_hyps_345_, uint8_t v___x_346_, lean_object* v_inst_347_, lean_object* v_toBind_348_, lean_object* v___f_349_, lean_object* v_eqs_350_){
_start:
{
lean_object* v_eqs_351_; lean_object* v_00_u03c6_352_; lean_object* v_00_u03c6_353_; lean_object* v___x_354_; lean_object* v___f_355_; lean_object* v___x_356_; lean_object* v___x_357_; 
v_eqs_351_ = lean_array_to_list(v_eqs_350_);
v_00_u03c6_352_ = l_Lean_mkAndN(v_eqs_351_);
v_00_u03c6_353_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure(v_u_340_, v_00_u03c3s_341_, v_00_u03c6_352_);
v___x_354_ = lean_box(v___x_346_);
lean_inc(v_toBind_348_);
lean_inc(v_inst_347_);
v___f_355_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__9___boxed), 9, 8);
lean_closure_set(v___f_355_, 0, v_hypName_342_);
lean_closure_set(v___f_355_, 1, v_toPure_343_);
lean_closure_set(v___f_355_, 2, v_ss_344_);
lean_closure_set(v___f_355_, 3, v_hyps_345_);
lean_closure_set(v___f_355_, 4, v___x_354_);
lean_closure_set(v___f_355_, 5, v_inst_347_);
lean_closure_set(v___f_355_, 6, v_toBind_348_);
lean_closure_set(v___f_355_, 7, v_00_u03c6_353_);
v___x_356_ = lean_apply_2(v_inst_347_, lean_box(0), v___f_349_);
v___x_357_ = lean_apply_4(v_toBind_348_, lean_box(0), lean_box(0), v___x_356_, v___f_355_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__10___boxed(lean_object* v_u_358_, lean_object* v_00_u03c3s_359_, lean_object* v_hypName_360_, lean_object* v_toPure_361_, lean_object* v_ss_362_, lean_object* v_hyps_363_, lean_object* v___x_364_, lean_object* v_inst_365_, lean_object* v_toBind_366_, lean_object* v___f_367_, lean_object* v_eqs_368_){
_start:
{
uint8_t v___x_1145__boxed_369_; lean_object* v_res_370_; 
v___x_1145__boxed_369_ = lean_unbox(v___x_364_);
v_res_370_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__10(v_u_358_, v_00_u03c3s_359_, v_hypName_360_, v_toPure_361_, v_ss_362_, v_hyps_363_, v___x_1145__boxed_369_, v_inst_365_, v_toBind_366_, v___f_367_, v_eqs_368_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__11(lean_object* v_u_371_, lean_object* v_00_u03c3s_372_, lean_object* v_hypName_373_, lean_object* v_toPure_374_, lean_object* v_hyps_375_, uint8_t v___x_376_, lean_object* v_inst_377_, lean_object* v_toBind_378_, lean_object* v___f_379_, lean_object* v_revertArgs_380_, lean_object* v_inst_381_, lean_object* v___f_382_, lean_object* v_ss_383_){
_start:
{
lean_object* v___x_384_; lean_object* v___f_385_; lean_object* v___x_386_; size_t v_sz_387_; size_t v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_384_ = lean_box(v___x_376_);
lean_inc(v_toBind_378_);
lean_inc_ref(v_ss_383_);
v___f_385_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__10___boxed), 11, 10);
lean_closure_set(v___f_385_, 0, v_u_371_);
lean_closure_set(v___f_385_, 1, v_00_u03c3s_372_);
lean_closure_set(v___f_385_, 2, v_hypName_373_);
lean_closure_set(v___f_385_, 3, v_toPure_374_);
lean_closure_set(v___f_385_, 4, v_ss_383_);
lean_closure_set(v___f_385_, 5, v_hyps_375_);
lean_closure_set(v___f_385_, 6, v___x_384_);
lean_closure_set(v___f_385_, 7, v_inst_377_);
lean_closure_set(v___f_385_, 8, v_toBind_378_);
lean_closure_set(v___f_385_, 9, v___f_379_);
v___x_386_ = l_Array_zip___redArg(v_revertArgs_380_, v_ss_383_);
lean_dec_ref(v_ss_383_);
v_sz_387_ = lean_array_size(v___x_386_);
v___x_388_ = ((size_t)0ULL);
v___x_389_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_381_, v___f_382_, v_sz_387_, v___x_388_, v___x_386_);
v___x_390_ = lean_apply_4(v_toBind_378_, lean_box(0), lean_box(0), v___x_389_, v___f_385_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__11___boxed(lean_object* v_u_391_, lean_object* v_00_u03c3s_392_, lean_object* v_hypName_393_, lean_object* v_toPure_394_, lean_object* v_hyps_395_, lean_object* v___x_396_, lean_object* v_inst_397_, lean_object* v_toBind_398_, lean_object* v___f_399_, lean_object* v_revertArgs_400_, lean_object* v_inst_401_, lean_object* v___f_402_, lean_object* v_ss_403_){
_start:
{
uint8_t v___x_1162__boxed_404_; lean_object* v_res_405_; 
v___x_1162__boxed_404_ = lean_unbox(v___x_396_);
v_res_405_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__11(v_u_391_, v_00_u03c3s_392_, v_hypName_393_, v_toPure_394_, v_hyps_395_, v___x_1162__boxed_404_, v_inst_397_, v_toBind_398_, v___f_399_, v_revertArgs_400_, v_inst_401_, v___f_402_, v_ss_403_);
lean_dec_ref(v_revertArgs_400_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__12(lean_object* v_u_414_, lean_object* v_fst_415_, lean_object* v_revertArgs_416_, lean_object* v_snd_417_, lean_object* v_prf_418_, lean_object* v_00_u03c3s_419_, lean_object* v_hyps_420_, lean_object* v_target_421_, lean_object* v_h_422_, lean_object* v_toPure_423_, lean_object* v_____do__lift_424_){
_start:
{
lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v_prf_432_; lean_object* v___x_433_; 
v___x_425_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__12___closed__1));
v___x_426_ = lean_box(0);
v___x_427_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_427_, 0, v_u_414_);
lean_ctor_set(v___x_427_, 1, v___x_426_);
v___x_428_ = l_Lean_mkConst(v___x_425_, v___x_427_);
v___x_429_ = l_Lean_mkAppN(v_fst_415_, v_revertArgs_416_);
v___x_430_ = l_Lean_mkAppN(v_snd_417_, v_revertArgs_416_);
v___x_431_ = l_Lean_mkAppN(v_prf_418_, v_revertArgs_416_);
v_prf_432_ = l_Lean_mkApp8(v___x_428_, v_00_u03c3s_419_, v_____do__lift_424_, v_hyps_420_, v___x_429_, v_target_421_, v_h_422_, v___x_430_, v___x_431_);
v___x_433_ = lean_apply_2(v_toPure_423_, lean_box(0), v_prf_432_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__12___boxed(lean_object* v_u_434_, lean_object* v_fst_435_, lean_object* v_revertArgs_436_, lean_object* v_snd_437_, lean_object* v_prf_438_, lean_object* v_00_u03c3s_439_, lean_object* v_hyps_440_, lean_object* v_target_441_, lean_object* v_h_442_, lean_object* v_toPure_443_, lean_object* v_____do__lift_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__12(v_u_434_, v_fst_435_, v_revertArgs_436_, v_snd_437_, v_prf_438_, v_00_u03c3s_439_, v_hyps_440_, v_target_441_, v_h_442_, v_toPure_443_, v_____do__lift_444_);
lean_dec_ref(v_revertArgs_436_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__13(lean_object* v_u_446_, lean_object* v_fst_447_, lean_object* v_revertArgs_448_, lean_object* v_snd_449_, lean_object* v_00_u03c3s_450_, lean_object* v_hyps_451_, lean_object* v_target_452_, lean_object* v_h_453_, lean_object* v_toPure_454_, lean_object* v_inst_455_, lean_object* v_toBind_456_, lean_object* v_prf_457_){
_start:
{
lean_object* v___f_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; 
lean_inc_ref(v_h_453_);
v___f_458_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__12___boxed), 11, 10);
lean_closure_set(v___f_458_, 0, v_u_446_);
lean_closure_set(v___f_458_, 1, v_fst_447_);
lean_closure_set(v___f_458_, 2, v_revertArgs_448_);
lean_closure_set(v___f_458_, 3, v_snd_449_);
lean_closure_set(v___f_458_, 4, v_prf_457_);
lean_closure_set(v___f_458_, 5, v_00_u03c3s_450_);
lean_closure_set(v___f_458_, 6, v_hyps_451_);
lean_closure_set(v___f_458_, 7, v_target_452_);
lean_closure_set(v___f_458_, 8, v_h_453_);
lean_closure_set(v___f_458_, 9, v_toPure_454_);
v___x_459_ = lean_alloc_closure((void*)(l_Lean_Meta_inferType___boxed), 6, 1);
lean_closure_set(v___x_459_, 0, v_h_453_);
v___x_460_ = lean_apply_2(v_inst_455_, lean_box(0), v___x_459_);
v___x_461_ = lean_apply_4(v_toBind_456_, lean_box(0), lean_box(0), v___x_460_, v___f_458_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__14(lean_object* v___y_462_, lean_object* v_u_463_, lean_object* v_snd_464_, lean_object* v_revertArgs_465_, lean_object* v_00_u03c3s_466_, lean_object* v_hyps_467_, lean_object* v_target_468_, lean_object* v_h_469_, lean_object* v_toPure_470_, lean_object* v_inst_471_, lean_object* v_toBind_472_, lean_object* v_a_473_, lean_object* v_n_474_, lean_object* v_f_475_, lean_object* v_k_476_, lean_object* v_H_477_){
_start:
{
lean_object* v_H_478_; lean_object* v___x_479_; lean_object* v_fst_480_; lean_object* v_snd_481_; lean_object* v___f_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v_goal_x27_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
lean_inc_ref_n(v___y_462_, 2);
v_H_478_ = l_Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps(v___y_462_, v_H_477_);
lean_inc_n(v_u_463_, 2);
v___x_479_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd(v_u_463_, v___y_462_, v_H_478_, v_snd_464_);
v_fst_480_ = lean_ctor_get(v___x_479_, 0);
lean_inc_n(v_fst_480_, 2);
v_snd_481_ = lean_ctor_get(v___x_479_, 1);
lean_inc(v_snd_481_);
lean_dec_ref(v___x_479_);
lean_inc(v_toBind_472_);
v___f_482_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__13), 12, 11);
lean_closure_set(v___f_482_, 0, v_u_463_);
lean_closure_set(v___f_482_, 1, v_fst_480_);
lean_closure_set(v___f_482_, 2, v_revertArgs_465_);
lean_closure_set(v___f_482_, 3, v_snd_481_);
lean_closure_set(v___f_482_, 4, v_00_u03c3s_466_);
lean_closure_set(v___f_482_, 5, v_hyps_467_);
lean_closure_set(v___f_482_, 6, v_target_468_);
lean_closure_set(v___f_482_, 7, v_h_469_);
lean_closure_set(v___f_482_, 8, v_toPure_470_);
lean_closure_set(v___f_482_, 9, v_inst_471_);
lean_closure_set(v___f_482_, 10, v_toBind_472_);
v___x_483_ = lean_array_get_size(v_a_473_);
v___x_484_ = l_Array_toSubarray___redArg(v_a_473_, v_n_474_, v___x_483_);
v___x_485_ = l_Subarray_copy___redArg(v___x_484_);
v___x_486_ = l_Lean_mkAppRev(v_f_475_, v___x_485_);
lean_dec_ref(v___x_485_);
v_goal_x27_487_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_goal_x27_487_, 0, v_u_463_);
lean_ctor_set(v_goal_x27_487_, 1, v___y_462_);
lean_ctor_set(v_goal_x27_487_, 2, v_fst_480_);
lean_ctor_set(v_goal_x27_487_, 3, v___x_486_);
v___x_488_ = lean_apply_1(v_k_476_, v_goal_x27_487_);
v___x_489_ = lean_apply_4(v_toBind_472_, lean_box(0), lean_box(0), v___x_488_, v___f_482_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15(lean_object* v_u_509_, lean_object* v_snd_510_, lean_object* v_revertArgs_511_, lean_object* v_00_u03c3s_512_, lean_object* v_hyps_513_, lean_object* v_target_514_, lean_object* v_toPure_515_, lean_object* v_inst_516_, lean_object* v_toBind_517_, lean_object* v_a_518_, lean_object* v_n_519_, lean_object* v_f_520_, lean_object* v_k_521_, lean_object* v_fst_522_, lean_object* v_revertArgsTypes_523_, lean_object* v___x_524_, lean_object* v___f_525_, lean_object* v_h_526_){
_start:
{
lean_object* v___y_528_; lean_object* v___x_533_; lean_object* v___x_534_; uint8_t v___x_535_; 
v___x_533_ = lean_array_get_size(v_revertArgsTypes_523_);
v___x_534_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__9));
v___x_535_ = lean_nat_dec_lt(v___x_524_, v___x_533_);
if (v___x_535_ == 0)
{
lean_dec_ref(v___f_525_);
lean_dec_ref(v_revertArgsTypes_523_);
lean_inc_ref(v_00_u03c3s_512_);
v___y_528_ = v_00_u03c3s_512_;
goto v___jp_527_;
}
else
{
size_t v___x_536_; size_t v___x_537_; lean_object* v___x_538_; 
v___x_536_ = lean_usize_of_nat(v___x_533_);
v___x_537_ = ((size_t)0ULL);
lean_inc_ref(v_00_u03c3s_512_);
v___x_538_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_534_, v___f_525_, v_revertArgsTypes_523_, v___x_536_, v___x_537_, v_00_u03c3s_512_);
v___y_528_ = v___x_538_;
goto v___jp_527_;
}
v___jp_527_:
{
lean_object* v___f_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
lean_inc(v_toBind_517_);
lean_inc(v_inst_516_);
v___f_529_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__14), 16, 15);
lean_closure_set(v___f_529_, 0, v___y_528_);
lean_closure_set(v___f_529_, 1, v_u_509_);
lean_closure_set(v___f_529_, 2, v_snd_510_);
lean_closure_set(v___f_529_, 3, v_revertArgs_511_);
lean_closure_set(v___f_529_, 4, v_00_u03c3s_512_);
lean_closure_set(v___f_529_, 5, v_hyps_513_);
lean_closure_set(v___f_529_, 6, v_target_514_);
lean_closure_set(v___f_529_, 7, v_h_526_);
lean_closure_set(v___f_529_, 8, v_toPure_515_);
lean_closure_set(v___f_529_, 9, v_inst_516_);
lean_closure_set(v___f_529_, 10, v_toBind_517_);
lean_closure_set(v___f_529_, 11, v_a_518_);
lean_closure_set(v___f_529_, 12, v_n_519_);
lean_closure_set(v___f_529_, 13, v_f_520_);
lean_closure_set(v___f_529_, 14, v_k_521_);
v___x_530_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateMVarsIfMVarApp___boxed), 6, 1);
lean_closure_set(v___x_530_, 0, v_fst_522_);
v___x_531_ = lean_apply_2(v_inst_516_, lean_box(0), v___x_530_);
v___x_532_ = lean_apply_4(v_toBind_517_, lean_box(0), lean_box(0), v___x_531_, v___f_529_);
return v___x_532_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___boxed(lean_object** _args){
lean_object* v_u_539_ = _args[0];
lean_object* v_snd_540_ = _args[1];
lean_object* v_revertArgs_541_ = _args[2];
lean_object* v_00_u03c3s_542_ = _args[3];
lean_object* v_hyps_543_ = _args[4];
lean_object* v_target_544_ = _args[5];
lean_object* v_toPure_545_ = _args[6];
lean_object* v_inst_546_ = _args[7];
lean_object* v_toBind_547_ = _args[8];
lean_object* v_a_548_ = _args[9];
lean_object* v_n_549_ = _args[10];
lean_object* v_f_550_ = _args[11];
lean_object* v_k_551_ = _args[12];
lean_object* v_fst_552_ = _args[13];
lean_object* v_revertArgsTypes_553_ = _args[14];
lean_object* v___x_554_ = _args[15];
lean_object* v___f_555_ = _args[16];
lean_object* v_h_556_ = _args[17];
_start:
{
lean_object* v_res_557_; 
v_res_557_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15(v_u_539_, v_snd_540_, v_revertArgs_541_, v_00_u03c3s_542_, v_hyps_543_, v_target_544_, v_toPure_545_, v_inst_546_, v_toBind_547_, v_a_548_, v_n_549_, v_f_550_, v_k_551_, v_fst_552_, v_revertArgsTypes_553_, v___x_554_, v___f_555_, v_h_556_);
lean_dec(v___x_554_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__16(lean_object* v_inst_558_, lean_object* v_toBind_559_, lean_object* v___f_560_, lean_object* v_prfs_561_){
_start:
{
lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_562_ = lean_array_to_list(v_prfs_561_);
v___x_563_ = lean_alloc_closure((void*)(l_Lean_Meta_mkAndIntroN___boxed), 6, 1);
lean_closure_set(v___x_563_, 0, v___x_562_);
v___x_564_ = lean_apply_2(v_inst_558_, lean_box(0), v___x_563_);
v___x_565_ = lean_apply_4(v_toBind_559_, lean_box(0), lean_box(0), v___x_564_, v___f_560_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__17(lean_object* v_u_567_, lean_object* v_revertArgs_568_, lean_object* v_00_u03c3s_569_, lean_object* v_hyps_570_, lean_object* v_target_571_, lean_object* v_toPure_572_, lean_object* v_inst_573_, lean_object* v_toBind_574_, lean_object* v_a_575_, lean_object* v_n_576_, lean_object* v_f_577_, lean_object* v_k_578_, lean_object* v_revertArgsTypes_579_, lean_object* v___x_580_, lean_object* v___f_581_, lean_object* v___x_582_, lean_object* v_____x_583_){
_start:
{
lean_object* v_fst_584_; lean_object* v_snd_585_; lean_object* v___f_586_; lean_object* v___f_587_; lean_object* v___x_588_; size_t v_sz_589_; size_t v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
v_fst_584_ = lean_ctor_get(v_____x_583_, 0);
lean_inc(v_fst_584_);
v_snd_585_ = lean_ctor_get(v_____x_583_, 1);
lean_inc(v_snd_585_);
lean_dec_ref(v_____x_583_);
lean_inc_n(v_toBind_574_, 2);
lean_inc_n(v_inst_573_, 2);
lean_inc_ref(v_revertArgs_568_);
v___f_586_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___boxed), 18, 17);
lean_closure_set(v___f_586_, 0, v_u_567_);
lean_closure_set(v___f_586_, 1, v_snd_585_);
lean_closure_set(v___f_586_, 2, v_revertArgs_568_);
lean_closure_set(v___f_586_, 3, v_00_u03c3s_569_);
lean_closure_set(v___f_586_, 4, v_hyps_570_);
lean_closure_set(v___f_586_, 5, v_target_571_);
lean_closure_set(v___f_586_, 6, v_toPure_572_);
lean_closure_set(v___f_586_, 7, v_inst_573_);
lean_closure_set(v___f_586_, 8, v_toBind_574_);
lean_closure_set(v___f_586_, 9, v_a_575_);
lean_closure_set(v___f_586_, 10, v_n_576_);
lean_closure_set(v___f_586_, 11, v_f_577_);
lean_closure_set(v___f_586_, 12, v_k_578_);
lean_closure_set(v___f_586_, 13, v_fst_584_);
lean_closure_set(v___f_586_, 14, v_revertArgsTypes_579_);
lean_closure_set(v___f_586_, 15, v___x_580_);
lean_closure_set(v___f_586_, 16, v___f_581_);
v___f_587_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__16), 4, 3);
lean_closure_set(v___f_587_, 0, v_inst_573_);
lean_closure_set(v___f_587_, 1, v_toBind_574_);
lean_closure_set(v___f_587_, 2, v___f_586_);
v___x_588_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__17___closed__0));
v_sz_589_ = lean_array_size(v_revertArgs_568_);
v___x_590_ = ((size_t)0ULL);
v___x_591_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_582_, v___x_588_, v_sz_589_, v___x_590_, v_revertArgs_568_);
v___x_592_ = lean_apply_2(v_inst_573_, lean_box(0), v___x_591_);
v___x_593_ = lean_apply_4(v_toBind_574_, lean_box(0), lean_box(0), v___x_592_, v___f_587_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__17___boxed(lean_object** _args){
lean_object* v_u_594_ = _args[0];
lean_object* v_revertArgs_595_ = _args[1];
lean_object* v_00_u03c3s_596_ = _args[2];
lean_object* v_hyps_597_ = _args[3];
lean_object* v_target_598_ = _args[4];
lean_object* v_toPure_599_ = _args[5];
lean_object* v_inst_600_ = _args[6];
lean_object* v_toBind_601_ = _args[7];
lean_object* v_a_602_ = _args[8];
lean_object* v_n_603_ = _args[9];
lean_object* v_f_604_ = _args[10];
lean_object* v_k_605_ = _args[11];
lean_object* v_revertArgsTypes_606_ = _args[12];
lean_object* v___x_607_ = _args[13];
lean_object* v___f_608_ = _args[14];
lean_object* v___x_609_ = _args[15];
lean_object* v_____x_610_ = _args[16];
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__17(v_u_594_, v_revertArgs_595_, v_00_u03c3s_596_, v_hyps_597_, v_target_598_, v_toPure_599_, v_inst_600_, v_toBind_601_, v_a_602_, v_n_603_, v_f_604_, v_k_605_, v_revertArgsTypes_606_, v___x_607_, v___f_608_, v___x_609_, v_____x_610_);
return v_res_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__18(lean_object* v_inst_612_, lean_object* v_inst_613_, lean_object* v___f_614_, lean_object* v_toBind_615_, lean_object* v___f_616_, lean_object* v_declInfos_617_){
_start:
{
uint8_t v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_618_ = 0;
v___x_619_ = l_Lean_Meta_withLocalDeclsDND___redArg(v_inst_612_, v_inst_613_, v_declInfos_617_, v___f_614_, v___x_618_);
v___x_620_ = lean_apply_4(v_toBind_615_, lean_box(0), lean_box(0), v___x_619_, v___f_616_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__19(lean_object* v_u_621_, lean_object* v_revertArgs_622_, lean_object* v_00_u03c3s_623_, lean_object* v_hyps_624_, lean_object* v_target_625_, lean_object* v_toPure_626_, lean_object* v_inst_627_, lean_object* v_toBind_628_, lean_object* v_a_629_, lean_object* v_n_630_, lean_object* v_f_631_, lean_object* v_k_632_, lean_object* v___x_633_, lean_object* v___f_634_, lean_object* v___x_635_, lean_object* v_inst_636_, lean_object* v_inst_637_, lean_object* v___f_638_, lean_object* v___f_639_, lean_object* v_revertArgsTypes_640_){
_start:
{
lean_object* v___f_641_; lean_object* v___f_642_; size_t v_sz_643_; size_t v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
lean_inc_ref_n(v_revertArgsTypes_640_, 2);
lean_inc_n(v_toBind_628_, 2);
v___f_641_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__17___boxed), 17, 16);
lean_closure_set(v___f_641_, 0, v_u_621_);
lean_closure_set(v___f_641_, 1, v_revertArgs_622_);
lean_closure_set(v___f_641_, 2, v_00_u03c3s_623_);
lean_closure_set(v___f_641_, 3, v_hyps_624_);
lean_closure_set(v___f_641_, 4, v_target_625_);
lean_closure_set(v___f_641_, 5, v_toPure_626_);
lean_closure_set(v___f_641_, 6, v_inst_627_);
lean_closure_set(v___f_641_, 7, v_toBind_628_);
lean_closure_set(v___f_641_, 8, v_a_629_);
lean_closure_set(v___f_641_, 9, v_n_630_);
lean_closure_set(v___f_641_, 10, v_f_631_);
lean_closure_set(v___f_641_, 11, v_k_632_);
lean_closure_set(v___f_641_, 12, v_revertArgsTypes_640_);
lean_closure_set(v___f_641_, 13, v___x_633_);
lean_closure_set(v___f_641_, 14, v___f_634_);
lean_closure_set(v___f_641_, 15, v___x_635_);
lean_inc_ref(v_inst_637_);
v___f_642_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__18), 6, 5);
lean_closure_set(v___f_642_, 0, v_inst_636_);
lean_closure_set(v___f_642_, 1, v_inst_637_);
lean_closure_set(v___f_642_, 2, v___f_638_);
lean_closure_set(v___f_642_, 3, v_toBind_628_);
lean_closure_set(v___f_642_, 4, v___f_641_);
v_sz_643_ = lean_array_size(v_revertArgsTypes_640_);
v___x_644_ = ((size_t)0ULL);
v___x_645_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_637_, v_revertArgsTypes_640_, v___f_639_, v_sz_643_, v___x_644_, v_revertArgsTypes_640_);
lean_dec_ref(v_revertArgsTypes_640_);
v___x_646_ = lean_apply_4(v_toBind_628_, lean_box(0), lean_box(0), v___x_645_, v___f_642_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__19___boxed(lean_object** _args){
lean_object* v_u_647_ = _args[0];
lean_object* v_revertArgs_648_ = _args[1];
lean_object* v_00_u03c3s_649_ = _args[2];
lean_object* v_hyps_650_ = _args[3];
lean_object* v_target_651_ = _args[4];
lean_object* v_toPure_652_ = _args[5];
lean_object* v_inst_653_ = _args[6];
lean_object* v_toBind_654_ = _args[7];
lean_object* v_a_655_ = _args[8];
lean_object* v_n_656_ = _args[9];
lean_object* v_f_657_ = _args[10];
lean_object* v_k_658_ = _args[11];
lean_object* v___x_659_ = _args[12];
lean_object* v___f_660_ = _args[13];
lean_object* v___x_661_ = _args[14];
lean_object* v_inst_662_ = _args[15];
lean_object* v_inst_663_ = _args[16];
lean_object* v___f_664_ = _args[17];
lean_object* v___f_665_ = _args[18];
lean_object* v_revertArgsTypes_666_ = _args[19];
_start:
{
lean_object* v_res_667_; 
v_res_667_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__19(v_u_647_, v_revertArgs_648_, v_00_u03c3s_649_, v_hyps_650_, v_target_651_, v_toPure_652_, v_inst_653_, v_toBind_654_, v_a_655_, v_n_656_, v_f_657_, v_k_658_, v___x_659_, v___f_660_, v___x_661_, v_inst_662_, v_inst_663_, v___f_664_, v___f_665_, v_revertArgsTypes_666_);
return v_res_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20(lean_object* v_revertArgs_669_, lean_object* v___x_670_, lean_object* v_inst_671_, lean_object* v_toBind_672_, lean_object* v___f_673_, lean_object* v_____r_674_){
_start:
{
lean_object* v___x_675_; size_t v_sz_676_; size_t v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_675_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__0));
v_sz_676_ = lean_array_size(v_revertArgs_669_);
v___x_677_ = ((size_t)0ULL);
v___x_678_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_670_, v___x_675_, v_sz_676_, v___x_677_, v_revertArgs_669_);
v___x_679_ = lean_apply_2(v_inst_671_, lean_box(0), v___x_678_);
v___x_680_ = lean_apply_4(v_toBind_672_, lean_box(0), lean_box(0), v___x_679_, v___f_673_);
return v___x_680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__21(lean_object* v___f_681_, lean_object* v_____r_682_){
_start:
{
lean_object* v___x_683_; 
v___x_683_ = lean_apply_1(v___f_681_, v_____r_682_);
return v___x_683_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__3(void){
_start:
{
lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_688_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__2));
v___x_689_ = l_Lean_stringToMessageData(v___x_688_);
return v___x_689_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__5(void){
_start:
{
lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_691_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__4));
v___x_692_ = l_Lean_stringToMessageData(v___x_691_);
return v___x_692_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__7(void){
_start:
{
lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_694_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__6));
v___x_695_ = l_Lean_stringToMessageData(v___x_694_);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg(lean_object* v_inst_696_, lean_object* v_inst_697_, lean_object* v_inst_698_, lean_object* v_goal_699_, lean_object* v_n_700_, lean_object* v_hypName_701_, lean_object* v_k_702_){
_start:
{
lean_object* v___x_703_; lean_object* v_toApplicative_704_; lean_object* v_toFunctor_705_; lean_object* v_toSeq_706_; lean_object* v_toSeqLeft_707_; lean_object* v_toSeqRight_708_; lean_object* v___f_709_; lean_object* v___f_710_; lean_object* v___f_711_; lean_object* v___f_712_; lean_object* v___x_713_; lean_object* v___f_714_; lean_object* v___f_715_; lean_object* v___f_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v_toApplicative_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_804_; 
v___x_703_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__1);
v_toApplicative_704_ = lean_ctor_get(v___x_703_, 0);
v_toFunctor_705_ = lean_ctor_get(v_toApplicative_704_, 0);
v_toSeq_706_ = lean_ctor_get(v_toApplicative_704_, 2);
v_toSeqLeft_707_ = lean_ctor_get(v_toApplicative_704_, 3);
v_toSeqRight_708_ = lean_ctor_get(v_toApplicative_704_, 4);
v___f_709_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__2));
v___f_710_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_705_, 2);
v___f_711_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_711_, 0, v_toFunctor_705_);
v___f_712_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_712_, 0, v_toFunctor_705_);
v___x_713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_713_, 0, v___f_711_);
lean_ctor_set(v___x_713_, 1, v___f_712_);
lean_inc(v_toSeqRight_708_);
v___f_714_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_714_, 0, v_toSeqRight_708_);
lean_inc(v_toSeqLeft_707_);
v___f_715_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_715_, 0, v_toSeqLeft_707_);
lean_inc(v_toSeq_706_);
v___f_716_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_716_, 0, v_toSeq_706_);
v___x_717_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_717_, 0, v___x_713_);
lean_ctor_set(v___x_717_, 1, v___f_709_);
lean_ctor_set(v___x_717_, 2, v___f_716_);
lean_ctor_set(v___x_717_, 3, v___f_715_);
lean_ctor_set(v___x_717_, 4, v___f_714_);
v___x_718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_718_, 0, v___x_717_);
lean_ctor_set(v___x_718_, 1, v___f_710_);
v___x_719_ = l_StateRefT_x27_instMonad___redArg(v___x_718_);
v_toApplicative_720_ = lean_ctor_get(v___x_719_, 0);
v_isSharedCheck_804_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_804_ == 0)
{
lean_object* v_unused_805_; 
v_unused_805_ = lean_ctor_get(v___x_719_, 1);
lean_dec(v_unused_805_);
v___x_722_ = v___x_719_;
v_isShared_723_ = v_isSharedCheck_804_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_toApplicative_720_);
lean_dec(v___x_719_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_804_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v_toFunctor_724_; lean_object* v_toSeq_725_; lean_object* v_toSeqLeft_726_; lean_object* v_toSeqRight_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_802_; 
v_toFunctor_724_ = lean_ctor_get(v_toApplicative_720_, 0);
v_toSeq_725_ = lean_ctor_get(v_toApplicative_720_, 2);
v_toSeqLeft_726_ = lean_ctor_get(v_toApplicative_720_, 3);
v_toSeqRight_727_ = lean_ctor_get(v_toApplicative_720_, 4);
v_isSharedCheck_802_ = !lean_is_exclusive(v_toApplicative_720_);
if (v_isSharedCheck_802_ == 0)
{
lean_object* v_unused_803_; 
v_unused_803_ = lean_ctor_get(v_toApplicative_720_, 1);
lean_dec(v_unused_803_);
v___x_729_ = v_toApplicative_720_;
v_isShared_730_ = v_isSharedCheck_802_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_toSeqRight_727_);
lean_inc(v_toSeqLeft_726_);
lean_inc(v_toSeq_725_);
lean_inc(v_toFunctor_724_);
lean_dec(v_toApplicative_720_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_802_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___f_731_; lean_object* v___f_732_; lean_object* v___f_733_; lean_object* v___f_734_; lean_object* v___x_735_; lean_object* v___f_736_; lean_object* v___f_737_; lean_object* v___f_738_; lean_object* v___x_740_; 
v___f_731_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__4));
v___f_732_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__5));
lean_inc_ref(v_toFunctor_724_);
v___f_733_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_733_, 0, v_toFunctor_724_);
v___f_734_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_734_, 0, v_toFunctor_724_);
v___x_735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_735_, 0, v___f_733_);
lean_ctor_set(v___x_735_, 1, v___f_734_);
v___f_736_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_736_, 0, v_toSeqRight_727_);
v___f_737_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_737_, 0, v_toSeqLeft_726_);
v___f_738_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_738_, 0, v_toSeq_725_);
if (v_isShared_730_ == 0)
{
lean_ctor_set(v___x_729_, 4, v___f_736_);
lean_ctor_set(v___x_729_, 3, v___f_737_);
lean_ctor_set(v___x_729_, 2, v___f_738_);
lean_ctor_set(v___x_729_, 1, v___f_731_);
lean_ctor_set(v___x_729_, 0, v___x_735_);
v___x_740_ = v___x_729_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v___x_735_);
lean_ctor_set(v_reuseFailAlloc_801_, 1, v___f_731_);
lean_ctor_set(v_reuseFailAlloc_801_, 2, v___f_738_);
lean_ctor_set(v_reuseFailAlloc_801_, 3, v___f_737_);
lean_ctor_set(v_reuseFailAlloc_801_, 4, v___f_736_);
v___x_740_ = v_reuseFailAlloc_801_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
lean_object* v___x_742_; 
if (v_isShared_723_ == 0)
{
lean_ctor_set(v___x_722_, 1, v___f_732_);
lean_ctor_set(v___x_722_, 0, v___x_740_);
v___x_742_ = v___x_722_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v___x_740_);
lean_ctor_set(v_reuseFailAlloc_800_, 1, v___f_732_);
v___x_742_ = v_reuseFailAlloc_800_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v_toMonadRef_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v_toApplicative_749_; lean_object* v_toBind_750_; lean_object* v_toPure_751_; lean_object* v___x_752_; uint8_t v___x_753_; 
v___x_743_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__11, &l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__11_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__11);
v___x_744_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__17, &l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__17_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__17);
v_toMonadRef_745_ = lean_ctor_get(v___x_744_, 0);
v___x_746_ = l_Lean_Meta_instAddMessageContextMetaM;
lean_inc_ref(v___x_742_);
v___x_747_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___x_746_, v___x_742_);
lean_inc_ref(v_toMonadRef_745_);
v___x_748_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_748_, 0, v___x_743_);
lean_ctor_set(v___x_748_, 1, v_toMonadRef_745_);
lean_ctor_set(v___x_748_, 2, v___x_747_);
v_toApplicative_749_ = lean_ctor_get(v_inst_696_, 0);
v_toBind_750_ = lean_ctor_get(v_inst_696_, 1);
lean_inc(v_toBind_750_);
v_toPure_751_ = lean_ctor_get(v_toApplicative_749_, 1);
lean_inc(v_toPure_751_);
v___x_752_ = lean_unsigned_to_nat(0u);
v___x_753_ = lean_nat_dec_eq(v_n_700_, v___x_752_);
if (v___x_753_ == 0)
{
lean_object* v_u_754_; lean_object* v_00_u03c3s_755_; lean_object* v_hyps_756_; lean_object* v_target_757_; lean_object* v___f_758_; lean_object* v___f_759_; lean_object* v___f_760_; lean_object* v___f_761_; lean_object* v___f_762_; lean_object* v_T_763_; lean_object* v_f_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v_a_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v_revertArgs_771_; lean_object* v___x_772_; lean_object* v___f_773_; lean_object* v___f_774_; lean_object* v___f_775_; lean_object* v___x_776_; uint8_t v___x_777_; 
v_u_754_ = lean_ctor_get(v_goal_699_, 0);
lean_inc_n(v_u_754_, 3);
v_00_u03c3s_755_ = lean_ctor_get(v_goal_699_, 1);
lean_inc_ref_n(v_00_u03c3s_755_, 2);
v_hyps_756_ = lean_ctor_get(v_goal_699_, 2);
lean_inc_ref_n(v_hyps_756_, 2);
v_target_757_ = lean_ctor_get(v_goal_699_, 3);
lean_inc_ref(v_target_757_);
lean_dec_ref(v_goal_699_);
v___f_758_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__0));
lean_inc_n(v_inst_698_, 5);
v___f_759_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__1), 2, 1);
lean_closure_set(v___f_759_, 0, v_inst_698_);
lean_inc(v_hypName_701_);
v___f_760_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_760_, 0, v_hypName_701_);
lean_inc_n(v_toBind_750_, 4);
lean_inc_n(v_toPure_751_, 2);
v___f_761_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__5), 6, 3);
lean_closure_set(v___f_761_, 0, v_toPure_751_);
lean_closure_set(v___f_761_, 1, v_inst_698_);
lean_closure_set(v___f_761_, 2, v_toBind_750_);
v___f_762_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__6), 3, 1);
lean_closure_set(v___f_762_, 0, v_u_754_);
v_T_763_ = l_Lean_Expr_consumeMData(v_target_757_);
v_f_764_ = l_Lean_Expr_getAppFn(v_T_763_);
v___x_765_ = l_Lean_Expr_getAppNumArgs(v_T_763_);
v___x_766_ = lean_mk_empty_array_with_capacity(v___x_765_);
lean_dec(v___x_765_);
lean_inc_ref(v_T_763_);
v_a_767_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_T_763_, v___x_766_);
lean_inc_n(v_n_700_, 2);
lean_inc_ref(v_a_767_);
v___x_768_ = l_Array_toSubarray___redArg(v_a_767_, v___x_752_, v_n_700_);
v___x_769_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__1));
v___x_770_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_758_, v___x_768_, v___x_769_);
v_revertArgs_771_ = l_Array_reverse___redArg(v___x_770_);
v___x_772_ = lean_box(v___x_753_);
lean_inc_ref(v_inst_696_);
lean_inc_ref_n(v_revertArgs_771_, 3);
v___f_773_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__11___boxed), 13, 12);
lean_closure_set(v___f_773_, 0, v_u_754_);
lean_closure_set(v___f_773_, 1, v_00_u03c3s_755_);
lean_closure_set(v___f_773_, 2, v_hypName_701_);
lean_closure_set(v___f_773_, 3, v_toPure_751_);
lean_closure_set(v___f_773_, 4, v_hyps_756_);
lean_closure_set(v___f_773_, 5, v___x_772_);
lean_closure_set(v___f_773_, 6, v_inst_698_);
lean_closure_set(v___f_773_, 7, v_toBind_750_);
lean_closure_set(v___f_773_, 8, v___f_760_);
lean_closure_set(v___f_773_, 9, v_revertArgs_771_);
lean_closure_set(v___f_773_, 10, v_inst_696_);
lean_closure_set(v___f_773_, 11, v___f_759_);
lean_inc_ref_n(v___x_742_, 2);
v___f_774_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__19___boxed), 20, 19);
lean_closure_set(v___f_774_, 0, v_u_754_);
lean_closure_set(v___f_774_, 1, v_revertArgs_771_);
lean_closure_set(v___f_774_, 2, v_00_u03c3s_755_);
lean_closure_set(v___f_774_, 3, v_hyps_756_);
lean_closure_set(v___f_774_, 4, v_target_757_);
lean_closure_set(v___f_774_, 5, v_toPure_751_);
lean_closure_set(v___f_774_, 6, v_inst_698_);
lean_closure_set(v___f_774_, 7, v_toBind_750_);
lean_closure_set(v___f_774_, 8, v_a_767_);
lean_closure_set(v___f_774_, 9, v_n_700_);
lean_closure_set(v___f_774_, 10, v_f_764_);
lean_closure_set(v___f_774_, 11, v_k_702_);
lean_closure_set(v___f_774_, 12, v___x_752_);
lean_closure_set(v___f_774_, 13, v___f_762_);
lean_closure_set(v___f_774_, 14, v___x_742_);
lean_closure_set(v___f_774_, 15, v_inst_697_);
lean_closure_set(v___f_774_, 16, v_inst_696_);
lean_closure_set(v___f_774_, 17, v___f_773_);
lean_closure_set(v___f_774_, 18, v___f_761_);
lean_inc_ref(v___f_774_);
v___f_775_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20), 6, 5);
lean_closure_set(v___f_775_, 0, v_revertArgs_771_);
lean_closure_set(v___f_775_, 1, v___x_742_);
lean_closure_set(v___f_775_, 2, v_inst_698_);
lean_closure_set(v___f_775_, 3, v_toBind_750_);
lean_closure_set(v___f_775_, 4, v___f_774_);
v___x_776_ = lean_array_get_size(v_revertArgs_771_);
v___x_777_ = lean_nat_dec_eq(v___x_776_, v_n_700_);
if (v___x_777_ == 0)
{
lean_object* v___f_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; 
lean_dec_ref(v___f_774_);
lean_dec_ref(v_revertArgs_771_);
v___f_778_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__21), 2, 1);
lean_closure_set(v___f_778_, 0, v___f_775_);
v___x_779_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__3, &l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__3_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__3);
v___x_780_ = l_Nat_reprFast(v_n_700_);
v___x_781_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_781_, 0, v___x_780_);
v___x_782_ = l_Lean_MessageData_ofFormat(v___x_781_);
v___x_783_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_783_, 0, v___x_779_);
lean_ctor_set(v___x_783_, 1, v___x_782_);
v___x_784_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__5, &l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__5_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__5);
v___x_785_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_785_, 0, v___x_783_);
lean_ctor_set(v___x_785_, 1, v___x_784_);
v___x_786_ = l_Lean_MessageData_ofExpr(v_T_763_);
v___x_787_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_787_, 0, v___x_785_);
lean_ctor_set(v___x_787_, 1, v___x_786_);
v___x_788_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__7, &l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__7_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__7);
v___x_789_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_789_, 0, v___x_787_);
lean_ctor_set(v___x_789_, 1, v___x_788_);
v___x_790_ = l_Nat_reprFast(v___x_776_);
v___x_791_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_791_, 0, v___x_790_);
v___x_792_ = l_Lean_MessageData_ofFormat(v___x_791_);
v___x_793_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_793_, 0, v___x_789_);
lean_ctor_set(v___x_793_, 1, v___x_792_);
v___x_794_ = l_Lean_throwError___redArg(v___x_742_, v___x_748_, v___x_793_);
v___x_795_ = lean_apply_2(v_inst_698_, lean_box(0), v___x_794_);
v___x_796_ = lean_apply_4(v_toBind_750_, lean_box(0), lean_box(0), v___x_795_, v___f_778_);
return v___x_796_;
}
else
{
lean_object* v___x_797_; lean_object* v___x_798_; 
lean_dec_ref(v___f_775_);
lean_dec_ref(v_T_763_);
lean_dec_ref_known(v___x_748_, 3);
lean_dec(v_n_700_);
v___x_797_ = lean_box(0);
v___x_798_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20(v_revertArgs_771_, v___x_742_, v_inst_698_, v_toBind_750_, v___f_774_, v___x_797_);
return v___x_798_;
}
}
else
{
lean_object* v___x_799_; 
lean_dec(v_toPure_751_);
lean_dec(v_toBind_750_);
lean_dec_ref_known(v___x_748_, 3);
lean_dec_ref(v___x_742_);
lean_dec(v_hypName_701_);
lean_dec(v_n_700_);
lean_dec(v_inst_698_);
lean_dec_ref(v_inst_697_);
lean_dec_ref(v_inst_696_);
v___x_799_ = lean_apply_1(v_k_702_, v_goal_699_);
return v___x_799_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN(lean_object* v_m_806_, lean_object* v_inst_807_, lean_object* v_inst_808_, lean_object* v_inst_809_, lean_object* v_goal_810_, lean_object* v_n_811_, lean_object* v_hypName_812_, lean_object* v_k_813_){
_start:
{
lean_object* v___x_814_; 
v___x_814_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg(v_inst_807_, v_inst_808_, v_inst_809_, v_goal_810_, v_n_811_, v_hypName_812_, v_k_813_);
return v___x_814_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; 
v___x_815_ = lean_box(0);
v___x_816_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_817_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_817_, 0, v___x_816_);
lean_ctor_set(v___x_817_, 1, v___x_815_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg(){
_start:
{
lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_819_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg___closed__0);
v___x_820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_820_, 0, v___x_819_);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg___boxed(lean_object* v___y_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg();
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0(lean_object* v_00_u03b1_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_){
_start:
{
lean_object* v___x_833_; 
v___x_833_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg();
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___boxed(lean_object* v_00_u03b1_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_){
_start:
{
lean_object* v_res_844_; 
v_res_844_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0(v_00_u03b1_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_);
lean_dec(v___y_842_);
lean_dec_ref(v___y_841_);
lean_dec(v___y_840_);
lean_dec_ref(v___y_839_);
lean_dec(v___y_838_);
lean_dec_ref(v___y_837_);
lean_dec(v___y_836_);
lean_dec_ref(v___y_835_);
return v_res_844_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___redArg___lam__0(lean_object* v_x_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_){
_start:
{
lean_object* v___x_855_; 
lean_inc(v___y_849_);
lean_inc_ref(v___y_848_);
lean_inc(v___y_847_);
lean_inc_ref(v___y_846_);
v___x_855_ = lean_apply_9(v_x_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_, v___y_853_, lean_box(0));
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___redArg___lam__0___boxed(lean_object* v_x_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___redArg___lam__0(v_x_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_);
lean_dec(v___y_860_);
lean_dec_ref(v___y_859_);
lean_dec(v___y_858_);
lean_dec_ref(v___y_857_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___redArg(lean_object* v_mvarId_867_, lean_object* v_x_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_){
_start:
{
lean_object* v___f_878_; lean_object* v___x_879_; 
lean_inc(v___y_872_);
lean_inc_ref(v___y_871_);
lean_inc(v___y_870_);
lean_inc_ref(v___y_869_);
v___f_878_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_878_, 0, v_x_868_);
lean_closure_set(v___f_878_, 1, v___y_869_);
lean_closure_set(v___f_878_, 2, v___y_870_);
lean_closure_set(v___f_878_, 3, v___y_871_);
lean_closure_set(v___f_878_, 4, v___y_872_);
v___x_879_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_867_, v___f_878_, v___y_873_, v___y_874_, v___y_875_, v___y_876_);
if (lean_obj_tag(v___x_879_) == 0)
{
return v___x_879_;
}
else
{
lean_object* v_a_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_887_; 
v_a_880_ = lean_ctor_get(v___x_879_, 0);
v_isSharedCheck_887_ = !lean_is_exclusive(v___x_879_);
if (v_isSharedCheck_887_ == 0)
{
v___x_882_ = v___x_879_;
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_a_880_);
lean_dec(v___x_879_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v___x_885_; 
if (v_isShared_883_ == 0)
{
v___x_885_ = v___x_882_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v_a_880_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
return v___x_885_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___redArg___boxed(lean_object* v_mvarId_888_, lean_object* v_x_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___redArg(v_mvarId_888_, v_x_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_);
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
lean_dec(v___y_895_);
lean_dec_ref(v___y_894_);
lean_dec(v___y_893_);
lean_dec_ref(v___y_892_);
lean_dec(v___y_891_);
lean_dec_ref(v___y_890_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3(lean_object* v_00_u03b1_900_, lean_object* v_mvarId_901_, lean_object* v_x_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_){
_start:
{
lean_object* v___x_912_; 
v___x_912_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___redArg(v_mvarId_901_, v_x_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___boxed(lean_object* v_00_u03b1_913_, lean_object* v_mvarId_914_, lean_object* v_x_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_){
_start:
{
lean_object* v_res_925_; 
v_res_925_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3(v_00_u03b1_913_, v_mvarId_914_, v_x_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_);
lean_dec(v___y_923_);
lean_dec_ref(v___y_922_);
lean_dec(v___y_921_);
lean_dec_ref(v___y_920_);
lean_dec(v___y_919_);
lean_dec_ref(v___y_918_);
lean_dec(v___y_917_);
lean_dec_ref(v___y_916_);
return v_res_925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__0(lean_object* v_val_926_, lean_object* v_newGoal_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_){
_start:
{
lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_937_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v_newGoal_927_);
v___x_938_ = lean_box(0);
v___x_939_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_937_, v___x_938_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
if (lean_obj_tag(v___x_939_) == 0)
{
lean_object* v_a_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_951_; 
v_a_940_ = lean_ctor_get(v___x_939_, 0);
v_isSharedCheck_951_ = !lean_is_exclusive(v___x_939_);
if (v_isSharedCheck_951_ == 0)
{
v___x_942_ = v___x_939_;
v_isShared_943_ = v_isSharedCheck_951_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_a_940_);
lean_dec(v___x_939_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_951_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_949_; 
v___x_944_ = lean_st_ref_take(v_val_926_);
v___x_945_ = l_Lean_Expr_mvarId_x21(v_a_940_);
v___x_946_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_946_, 0, v___x_945_);
lean_ctor_set(v___x_946_, 1, v___x_944_);
v___x_947_ = lean_st_ref_put(v_val_926_, v___x_946_);
if (v_isShared_943_ == 0)
{
v___x_949_ = v___x_942_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v_a_940_);
v___x_949_ = v_reuseFailAlloc_950_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
return v___x_949_;
}
}
}
else
{
return v___x_939_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__0___boxed(lean_object* v_val_952_, lean_object* v_newGoal_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__0(v_val_952_, v_newGoal_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_);
lean_dec(v___y_961_);
lean_dec_ref(v___y_960_);
lean_dec(v___y_959_);
lean_dec_ref(v___y_958_);
lean_dec(v___y_957_);
lean_dec_ref(v___y_956_);
lean_dec(v___y_955_);
lean_dec_ref(v___y_954_);
lean_dec(v_val_952_);
return v_res_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14_spec__20_spec__22___redArg(lean_object* v_x_964_, lean_object* v_x_965_, lean_object* v_x_966_, lean_object* v_x_967_){
_start:
{
lean_object* v_ks_968_; lean_object* v_vs_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_993_; 
v_ks_968_ = lean_ctor_get(v_x_964_, 0);
v_vs_969_ = lean_ctor_get(v_x_964_, 1);
v_isSharedCheck_993_ = !lean_is_exclusive(v_x_964_);
if (v_isSharedCheck_993_ == 0)
{
v___x_971_ = v_x_964_;
v_isShared_972_ = v_isSharedCheck_993_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_vs_969_);
lean_inc(v_ks_968_);
lean_dec(v_x_964_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_993_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v___x_973_; uint8_t v___x_974_; 
v___x_973_ = lean_array_get_size(v_ks_968_);
v___x_974_ = lean_nat_dec_lt(v_x_965_, v___x_973_);
if (v___x_974_ == 0)
{
lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_978_; 
lean_dec(v_x_965_);
v___x_975_ = lean_array_push(v_ks_968_, v_x_966_);
v___x_976_ = lean_array_push(v_vs_969_, v_x_967_);
if (v_isShared_972_ == 0)
{
lean_ctor_set(v___x_971_, 1, v___x_976_);
lean_ctor_set(v___x_971_, 0, v___x_975_);
v___x_978_ = v___x_971_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v___x_975_);
lean_ctor_set(v_reuseFailAlloc_979_, 1, v___x_976_);
v___x_978_ = v_reuseFailAlloc_979_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
return v___x_978_;
}
}
else
{
lean_object* v_k_x27_980_; uint8_t v___x_981_; 
v_k_x27_980_ = lean_array_fget_borrowed(v_ks_968_, v_x_965_);
v___x_981_ = l_Lean_instBEqMVarId_beq(v_x_966_, v_k_x27_980_);
if (v___x_981_ == 0)
{
lean_object* v___x_983_; 
if (v_isShared_972_ == 0)
{
v___x_983_ = v___x_971_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v_ks_968_);
lean_ctor_set(v_reuseFailAlloc_987_, 1, v_vs_969_);
v___x_983_ = v_reuseFailAlloc_987_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_984_ = lean_unsigned_to_nat(1u);
v___x_985_ = lean_nat_add(v_x_965_, v___x_984_);
lean_dec(v_x_965_);
v_x_964_ = v___x_983_;
v_x_965_ = v___x_985_;
goto _start;
}
}
else
{
lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_991_; 
v___x_988_ = lean_array_fset(v_ks_968_, v_x_965_, v_x_966_);
v___x_989_ = lean_array_fset(v_vs_969_, v_x_965_, v_x_967_);
lean_dec(v_x_965_);
if (v_isShared_972_ == 0)
{
lean_ctor_set(v___x_971_, 1, v___x_989_);
lean_ctor_set(v___x_971_, 0, v___x_988_);
v___x_991_ = v___x_971_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v___x_988_);
lean_ctor_set(v_reuseFailAlloc_992_, 1, v___x_989_);
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
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14_spec__20___redArg(lean_object* v_n_994_, lean_object* v_k_995_, lean_object* v_v_996_){
_start:
{
lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_997_ = lean_unsigned_to_nat(0u);
v___x_998_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14_spec__20_spec__22___redArg(v_n_994_, v___x_997_, v_k_995_, v_v_996_);
return v___x_998_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14___redArg___closed__0(void){
_start:
{
lean_object* v___x_999_; 
v___x_999_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_999_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14___redArg(lean_object* v_x_1000_, size_t v_x_1001_, size_t v_x_1002_, lean_object* v_x_1003_, lean_object* v_x_1004_){
_start:
{
if (lean_obj_tag(v_x_1000_) == 0)
{
lean_object* v_es_1005_; size_t v___x_1006_; size_t v___x_1007_; lean_object* v_j_1008_; lean_object* v___x_1009_; uint8_t v___x_1010_; 
v_es_1005_ = lean_ctor_get(v_x_1000_, 0);
v___x_1006_ = ((size_t)31ULL);
v___x_1007_ = lean_usize_land(v_x_1001_, v___x_1006_);
v_j_1008_ = lean_usize_to_nat(v___x_1007_);
v___x_1009_ = lean_array_get_size(v_es_1005_);
v___x_1010_ = lean_nat_dec_lt(v_j_1008_, v___x_1009_);
if (v___x_1010_ == 0)
{
lean_dec(v_j_1008_);
lean_dec(v_x_1004_);
lean_dec(v_x_1003_);
return v_x_1000_;
}
else
{
lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1049_; 
lean_inc_ref(v_es_1005_);
v_isSharedCheck_1049_ = !lean_is_exclusive(v_x_1000_);
if (v_isSharedCheck_1049_ == 0)
{
lean_object* v_unused_1050_; 
v_unused_1050_ = lean_ctor_get(v_x_1000_, 0);
lean_dec(v_unused_1050_);
v___x_1012_ = v_x_1000_;
v_isShared_1013_ = v_isSharedCheck_1049_;
goto v_resetjp_1011_;
}
else
{
lean_dec(v_x_1000_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1049_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
lean_object* v_v_1014_; lean_object* v___x_1015_; lean_object* v_xs_x27_1016_; lean_object* v___y_1018_; 
v_v_1014_ = lean_array_fget(v_es_1005_, v_j_1008_);
v___x_1015_ = lean_box(0);
v_xs_x27_1016_ = lean_array_fset(v_es_1005_, v_j_1008_, v___x_1015_);
switch(lean_obj_tag(v_v_1014_))
{
case 0:
{
lean_object* v_key_1023_; lean_object* v_val_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1034_; 
v_key_1023_ = lean_ctor_get(v_v_1014_, 0);
v_val_1024_ = lean_ctor_get(v_v_1014_, 1);
v_isSharedCheck_1034_ = !lean_is_exclusive(v_v_1014_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1026_ = v_v_1014_;
v_isShared_1027_ = v_isSharedCheck_1034_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_val_1024_);
lean_inc(v_key_1023_);
lean_dec(v_v_1014_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1034_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
uint8_t v___x_1028_; 
v___x_1028_ = l_Lean_instBEqMVarId_beq(v_x_1003_, v_key_1023_);
if (v___x_1028_ == 0)
{
lean_object* v___x_1029_; lean_object* v___x_1030_; 
lean_del_object(v___x_1026_);
v___x_1029_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1023_, v_val_1024_, v_x_1003_, v_x_1004_);
v___x_1030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1029_);
v___y_1018_ = v___x_1030_;
goto v___jp_1017_;
}
else
{
lean_object* v___x_1032_; 
lean_dec(v_val_1024_);
lean_dec(v_key_1023_);
if (v_isShared_1027_ == 0)
{
lean_ctor_set(v___x_1026_, 1, v_x_1004_);
lean_ctor_set(v___x_1026_, 0, v_x_1003_);
v___x_1032_ = v___x_1026_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v_x_1003_);
lean_ctor_set(v_reuseFailAlloc_1033_, 1, v_x_1004_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
v___y_1018_ = v___x_1032_;
goto v___jp_1017_;
}
}
}
}
case 1:
{
lean_object* v_node_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1047_; 
v_node_1035_ = lean_ctor_get(v_v_1014_, 0);
v_isSharedCheck_1047_ = !lean_is_exclusive(v_v_1014_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_1037_ = v_v_1014_;
v_isShared_1038_ = v_isSharedCheck_1047_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_node_1035_);
lean_dec(v_v_1014_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1047_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
size_t v___x_1039_; size_t v___x_1040_; size_t v___x_1041_; size_t v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1045_; 
v___x_1039_ = ((size_t)5ULL);
v___x_1040_ = lean_usize_shift_right(v_x_1001_, v___x_1039_);
v___x_1041_ = ((size_t)1ULL);
v___x_1042_ = lean_usize_add(v_x_1002_, v___x_1041_);
v___x_1043_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14___redArg(v_node_1035_, v___x_1040_, v___x_1042_, v_x_1003_, v_x_1004_);
if (v_isShared_1038_ == 0)
{
lean_ctor_set(v___x_1037_, 0, v___x_1043_);
v___x_1045_ = v___x_1037_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v___x_1043_);
v___x_1045_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
v___y_1018_ = v___x_1045_;
goto v___jp_1017_;
}
}
}
default: 
{
lean_object* v___x_1048_; 
v___x_1048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1048_, 0, v_x_1003_);
lean_ctor_set(v___x_1048_, 1, v_x_1004_);
v___y_1018_ = v___x_1048_;
goto v___jp_1017_;
}
}
v___jp_1017_:
{
lean_object* v___x_1019_; lean_object* v___x_1021_; 
v___x_1019_ = lean_array_fset(v_xs_x27_1016_, v_j_1008_, v___y_1018_);
lean_dec(v_j_1008_);
if (v_isShared_1013_ == 0)
{
lean_ctor_set(v___x_1012_, 0, v___x_1019_);
v___x_1021_ = v___x_1012_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v___x_1019_);
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
}
else
{
lean_object* v_ks_1051_; lean_object* v_vs_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1070_; 
v_ks_1051_ = lean_ctor_get(v_x_1000_, 0);
v_vs_1052_ = lean_ctor_get(v_x_1000_, 1);
v_isSharedCheck_1070_ = !lean_is_exclusive(v_x_1000_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_1054_ = v_x_1000_;
v_isShared_1055_ = v_isSharedCheck_1070_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_vs_1052_);
lean_inc(v_ks_1051_);
lean_dec(v_x_1000_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1070_;
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
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v_ks_1051_);
lean_ctor_set(v_reuseFailAlloc_1069_, 1, v_vs_1052_);
v___x_1057_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
lean_object* v_newNode_1058_; size_t v___x_1059_; uint8_t v___x_1060_; 
v_newNode_1058_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14_spec__20___redArg(v___x_1057_, v_x_1003_, v_x_1004_);
v___x_1059_ = ((size_t)7ULL);
v___x_1060_ = lean_usize_dec_le(v___x_1059_, v_x_1002_);
if (v___x_1060_ == 0)
{
lean_object* v___x_1061_; lean_object* v___x_1062_; uint8_t v___x_1063_; 
v___x_1061_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1058_);
v___x_1062_ = lean_unsigned_to_nat(4u);
v___x_1063_ = lean_nat_dec_lt(v___x_1061_, v___x_1062_);
lean_dec(v___x_1061_);
if (v___x_1063_ == 0)
{
lean_object* v_ks_1064_; lean_object* v_vs_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; 
v_ks_1064_ = lean_ctor_get(v_newNode_1058_, 0);
lean_inc_ref(v_ks_1064_);
v_vs_1065_ = lean_ctor_get(v_newNode_1058_, 1);
lean_inc_ref(v_vs_1065_);
lean_dec_ref(v_newNode_1058_);
v___x_1066_ = lean_unsigned_to_nat(0u);
v___x_1067_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14___redArg___closed__0);
v___x_1068_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14_spec__21___redArg(v_x_1002_, v_ks_1064_, v_vs_1065_, v___x_1066_, v___x_1067_);
lean_dec_ref(v_vs_1065_);
lean_dec_ref(v_ks_1064_);
return v___x_1068_;
}
else
{
return v_newNode_1058_;
}
}
else
{
return v_newNode_1058_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14_spec__21___redArg(size_t v_depth_1071_, lean_object* v_keys_1072_, lean_object* v_vals_1073_, lean_object* v_i_1074_, lean_object* v_entries_1075_){
_start:
{
lean_object* v___x_1076_; uint8_t v___x_1077_; 
v___x_1076_ = lean_array_get_size(v_keys_1072_);
v___x_1077_ = lean_nat_dec_lt(v_i_1074_, v___x_1076_);
if (v___x_1077_ == 0)
{
lean_dec(v_i_1074_);
return v_entries_1075_;
}
else
{
lean_object* v_k_1078_; lean_object* v_v_1079_; uint64_t v___x_1080_; size_t v_h_1081_; size_t v___x_1082_; lean_object* v___x_1083_; size_t v___x_1084_; size_t v___x_1085_; size_t v___x_1086_; size_t v_h_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; 
v_k_1078_ = lean_array_fget_borrowed(v_keys_1072_, v_i_1074_);
v_v_1079_ = lean_array_fget_borrowed(v_vals_1073_, v_i_1074_);
v___x_1080_ = l_Lean_instHashableMVarId_hash(v_k_1078_);
v_h_1081_ = lean_uint64_to_usize(v___x_1080_);
v___x_1082_ = ((size_t)5ULL);
v___x_1083_ = lean_unsigned_to_nat(1u);
v___x_1084_ = ((size_t)1ULL);
v___x_1085_ = lean_usize_sub(v_depth_1071_, v___x_1084_);
v___x_1086_ = lean_usize_mul(v___x_1082_, v___x_1085_);
v_h_1087_ = lean_usize_shift_right(v_h_1081_, v___x_1086_);
v___x_1088_ = lean_nat_add(v_i_1074_, v___x_1083_);
lean_dec(v_i_1074_);
lean_inc(v_v_1079_);
lean_inc(v_k_1078_);
v___x_1089_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14___redArg(v_entries_1075_, v_h_1087_, v_depth_1071_, v_k_1078_, v_v_1079_);
v_i_1074_ = v___x_1088_;
v_entries_1075_ = v___x_1089_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14_spec__21___redArg___boxed(lean_object* v_depth_1091_, lean_object* v_keys_1092_, lean_object* v_vals_1093_, lean_object* v_i_1094_, lean_object* v_entries_1095_){
_start:
{
size_t v_depth_boxed_1096_; lean_object* v_res_1097_; 
v_depth_boxed_1096_ = lean_unbox_usize(v_depth_1091_);
lean_dec(v_depth_1091_);
v_res_1097_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14_spec__21___redArg(v_depth_boxed_1096_, v_keys_1092_, v_vals_1093_, v_i_1094_, v_entries_1095_);
lean_dec_ref(v_vals_1093_);
lean_dec_ref(v_keys_1092_);
return v_res_1097_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14___redArg___boxed(lean_object* v_x_1098_, lean_object* v_x_1099_, lean_object* v_x_1100_, lean_object* v_x_1101_, lean_object* v_x_1102_){
_start:
{
size_t v_x_16991__boxed_1103_; size_t v_x_16992__boxed_1104_; lean_object* v_res_1105_; 
v_x_16991__boxed_1103_ = lean_unbox_usize(v_x_1099_);
lean_dec(v_x_1099_);
v_x_16992__boxed_1104_ = lean_unbox_usize(v_x_1100_);
lean_dec(v_x_1100_);
v_res_1105_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14___redArg(v_x_1098_, v_x_16991__boxed_1103_, v_x_16992__boxed_1104_, v_x_1101_, v_x_1102_);
return v_res_1105_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10___redArg(lean_object* v_x_1106_, lean_object* v_x_1107_, lean_object* v_x_1108_){
_start:
{
uint64_t v___x_1109_; size_t v___x_1110_; size_t v___x_1111_; lean_object* v___x_1112_; 
v___x_1109_ = l_Lean_instHashableMVarId_hash(v_x_1107_);
v___x_1110_ = lean_uint64_to_usize(v___x_1109_);
v___x_1111_ = ((size_t)1ULL);
v___x_1112_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14___redArg(v_x_1106_, v___x_1110_, v___x_1111_, v_x_1107_, v_x_1108_);
return v___x_1112_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2___redArg(lean_object* v_mvarId_1113_, lean_object* v_val_1114_, lean_object* v___y_1115_){
_start:
{
lean_object* v___x_1117_; lean_object* v_mctx_1118_; lean_object* v_cache_1119_; lean_object* v_zetaDeltaFVarIds_1120_; lean_object* v_postponed_1121_; lean_object* v_diag_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1152_; 
v___x_1117_ = lean_st_ref_take(v___y_1115_);
v_mctx_1118_ = lean_ctor_get(v___x_1117_, 0);
v_cache_1119_ = lean_ctor_get(v___x_1117_, 1);
v_zetaDeltaFVarIds_1120_ = lean_ctor_get(v___x_1117_, 2);
v_postponed_1121_ = lean_ctor_get(v___x_1117_, 3);
v_diag_1122_ = lean_ctor_get(v___x_1117_, 4);
v_isSharedCheck_1152_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_1124_ = v___x_1117_;
v_isShared_1125_ = v_isSharedCheck_1152_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_diag_1122_);
lean_inc(v_postponed_1121_);
lean_inc(v_zetaDeltaFVarIds_1120_);
lean_inc(v_cache_1119_);
lean_inc(v_mctx_1118_);
lean_dec(v___x_1117_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1152_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v_depth_1126_; lean_object* v_levelAssignDepth_1127_; lean_object* v_lmvarCounter_1128_; lean_object* v_mvarCounter_1129_; lean_object* v_lDecls_1130_; lean_object* v_decls_1131_; lean_object* v_userNames_1132_; lean_object* v_lAssignment_1133_; lean_object* v_eAssignment_1134_; lean_object* v_dAssignment_1135_; lean_object* v_instanceTypedMVars_1136_; lean_object* v_synthNormMemo_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1151_; 
v_depth_1126_ = lean_ctor_get(v_mctx_1118_, 0);
v_levelAssignDepth_1127_ = lean_ctor_get(v_mctx_1118_, 1);
v_lmvarCounter_1128_ = lean_ctor_get(v_mctx_1118_, 2);
v_mvarCounter_1129_ = lean_ctor_get(v_mctx_1118_, 3);
v_lDecls_1130_ = lean_ctor_get(v_mctx_1118_, 4);
v_decls_1131_ = lean_ctor_get(v_mctx_1118_, 5);
v_userNames_1132_ = lean_ctor_get(v_mctx_1118_, 6);
v_lAssignment_1133_ = lean_ctor_get(v_mctx_1118_, 7);
v_eAssignment_1134_ = lean_ctor_get(v_mctx_1118_, 8);
v_dAssignment_1135_ = lean_ctor_get(v_mctx_1118_, 9);
v_instanceTypedMVars_1136_ = lean_ctor_get(v_mctx_1118_, 10);
v_synthNormMemo_1137_ = lean_ctor_get(v_mctx_1118_, 11);
v_isSharedCheck_1151_ = !lean_is_exclusive(v_mctx_1118_);
if (v_isSharedCheck_1151_ == 0)
{
v___x_1139_ = v_mctx_1118_;
v_isShared_1140_ = v_isSharedCheck_1151_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_synthNormMemo_1137_);
lean_inc(v_instanceTypedMVars_1136_);
lean_inc(v_dAssignment_1135_);
lean_inc(v_eAssignment_1134_);
lean_inc(v_lAssignment_1133_);
lean_inc(v_userNames_1132_);
lean_inc(v_decls_1131_);
lean_inc(v_lDecls_1130_);
lean_inc(v_mvarCounter_1129_);
lean_inc(v_lmvarCounter_1128_);
lean_inc(v_levelAssignDepth_1127_);
lean_inc(v_depth_1126_);
lean_dec(v_mctx_1118_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1151_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1144_; 
v___x_1141_ = lean_box(0);
v___x_1142_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10___redArg(v_eAssignment_1134_, v_mvarId_1113_, v_val_1114_);
if (v_isShared_1140_ == 0)
{
lean_ctor_set(v___x_1139_, 8, v___x_1142_);
v___x_1144_ = v___x_1139_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v_depth_1126_);
lean_ctor_set(v_reuseFailAlloc_1150_, 1, v_levelAssignDepth_1127_);
lean_ctor_set(v_reuseFailAlloc_1150_, 2, v_lmvarCounter_1128_);
lean_ctor_set(v_reuseFailAlloc_1150_, 3, v_mvarCounter_1129_);
lean_ctor_set(v_reuseFailAlloc_1150_, 4, v_lDecls_1130_);
lean_ctor_set(v_reuseFailAlloc_1150_, 5, v_decls_1131_);
lean_ctor_set(v_reuseFailAlloc_1150_, 6, v_userNames_1132_);
lean_ctor_set(v_reuseFailAlloc_1150_, 7, v_lAssignment_1133_);
lean_ctor_set(v_reuseFailAlloc_1150_, 8, v___x_1142_);
lean_ctor_set(v_reuseFailAlloc_1150_, 9, v_dAssignment_1135_);
lean_ctor_set(v_reuseFailAlloc_1150_, 10, v_instanceTypedMVars_1136_);
lean_ctor_set(v_reuseFailAlloc_1150_, 11, v_synthNormMemo_1137_);
v___x_1144_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
lean_object* v___x_1146_; 
if (v_isShared_1125_ == 0)
{
lean_ctor_set(v___x_1124_, 0, v___x_1144_);
v___x_1146_ = v___x_1124_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v___x_1144_);
lean_ctor_set(v_reuseFailAlloc_1149_, 1, v_cache_1119_);
lean_ctor_set(v_reuseFailAlloc_1149_, 2, v_zetaDeltaFVarIds_1120_);
lean_ctor_set(v_reuseFailAlloc_1149_, 3, v_postponed_1121_);
lean_ctor_set(v_reuseFailAlloc_1149_, 4, v_diag_1122_);
v___x_1146_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
lean_object* v___x_1147_; lean_object* v___x_1148_; 
v___x_1147_ = lean_st_ref_put(v___y_1115_, v___x_1146_);
v___x_1148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1148_, 0, v___x_1141_);
return v___x_1148_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2___redArg___boxed(lean_object* v_mvarId_1153_, lean_object* v_val_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_){
_start:
{
lean_object* v_res_1157_; 
v_res_1157_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2___redArg(v_mvarId_1153_, v_val_1154_, v___y_1155_);
lean_dec(v___y_1155_);
return v_res_1157_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5_spec__14(lean_object* v_msgData_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_){
_start:
{
lean_object* v___x_1164_; lean_object* v_env_1165_; uint8_t v___x_1166_; lean_object* v_env_1167_; lean_object* v___x_1168_; lean_object* v_toCold_1169_; lean_object* v_mctx_1170_; lean_object* v_lctx_1171_; lean_object* v_options_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; 
v___x_1164_ = lean_st_ref_get(v___y_1162_);
v_env_1165_ = lean_ctor_get(v___x_1164_, 0);
lean_inc_ref(v_env_1165_);
lean_dec(v___x_1164_);
v___x_1166_ = 0;
v_env_1167_ = l_Lean_Environment_setRecordingDeps(v_env_1165_, v___x_1166_);
v___x_1168_ = lean_st_ref_get(v___y_1160_);
v_toCold_1169_ = lean_ctor_get(v___y_1161_, 0);
v_mctx_1170_ = lean_ctor_get(v___x_1168_, 0);
lean_inc_ref(v_mctx_1170_);
lean_dec(v___x_1168_);
v_lctx_1171_ = lean_ctor_get(v___y_1159_, 2);
v_options_1172_ = lean_ctor_get(v_toCold_1169_, 2);
lean_inc_ref(v_options_1172_);
lean_inc_ref(v_lctx_1171_);
v___x_1173_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1173_, 0, v_env_1167_);
lean_ctor_set(v___x_1173_, 1, v_mctx_1170_);
lean_ctor_set(v___x_1173_, 2, v_lctx_1171_);
lean_ctor_set(v___x_1173_, 3, v_options_1172_);
v___x_1174_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1174_, 0, v___x_1173_);
lean_ctor_set(v___x_1174_, 1, v_msgData_1158_);
v___x_1175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1175_, 0, v___x_1174_);
return v___x_1175_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5_spec__14___boxed(lean_object* v_msgData_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_){
_start:
{
lean_object* v_res_1182_; 
v_res_1182_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5_spec__14(v_msgData_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_);
lean_dec(v___y_1180_);
lean_dec_ref(v___y_1179_);
lean_dec(v___y_1178_);
lean_dec_ref(v___y_1177_);
return v_res_1182_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__8___redArg(lean_object* v_msg_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_){
_start:
{
lean_object* v_ref_1189_; lean_object* v___x_1190_; lean_object* v_a_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1199_; 
v_ref_1189_ = lean_ctor_get(v___y_1186_, 2);
v___x_1190_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5_spec__14(v_msg_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_);
v_a_1191_ = lean_ctor_get(v___x_1190_, 0);
v_isSharedCheck_1199_ = !lean_is_exclusive(v___x_1190_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1193_ = v___x_1190_;
v_isShared_1194_ = v_isSharedCheck_1199_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_a_1191_);
lean_dec(v___x_1190_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1199_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v___x_1195_; lean_object* v___x_1197_; 
lean_inc(v_ref_1189_);
v___x_1195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1195_, 0, v_ref_1189_);
lean_ctor_set(v___x_1195_, 1, v_a_1191_);
if (v_isShared_1194_ == 0)
{
lean_ctor_set_tag(v___x_1193_, 1);
lean_ctor_set(v___x_1193_, 0, v___x_1195_);
v___x_1197_ = v___x_1193_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v___x_1195_);
v___x_1197_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
return v___x_1197_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__8___redArg___boxed(lean_object* v_msg_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_){
_start:
{
lean_object* v_res_1206_; 
v_res_1206_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__8___redArg(v_msg_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_);
lean_dec(v___y_1204_);
lean_dec_ref(v___y_1203_);
lean_dec(v___y_1202_);
lean_dec_ref(v___y_1201_);
return v_res_1206_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__7(lean_object* v_u_1207_, lean_object* v_as_1208_, size_t v_i_1209_, size_t v_stop_1210_, lean_object* v_b_1211_){
_start:
{
uint8_t v___x_1212_; 
v___x_1212_ = lean_usize_dec_eq(v_i_1209_, v_stop_1210_);
if (v___x_1212_ == 0)
{
size_t v___x_1213_; size_t v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; 
v___x_1213_ = ((size_t)1ULL);
v___x_1214_ = lean_usize_sub(v_i_1209_, v___x_1213_);
v___x_1215_ = lean_array_uget_borrowed(v_as_1208_, v___x_1214_);
lean_inc(v___x_1215_);
lean_inc(v_u_1207_);
v___x_1216_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkCons(v_u_1207_, v___x_1215_, v_b_1211_);
v_i_1209_ = v___x_1214_;
v_b_1211_ = v___x_1216_;
goto _start;
}
else
{
lean_dec(v_u_1207_);
return v_b_1211_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__7___boxed(lean_object* v_u_1218_, lean_object* v_as_1219_, lean_object* v_i_1220_, lean_object* v_stop_1221_, lean_object* v_b_1222_){
_start:
{
size_t v_i_boxed_1223_; size_t v_stop_boxed_1224_; lean_object* v_res_1225_; 
v_i_boxed_1223_ = lean_unbox_usize(v_i_1220_);
lean_dec(v_i_1220_);
v_stop_boxed_1224_ = lean_unbox_usize(v_stop_1221_);
lean_dec(v_stop_1221_);
v_res_1225_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__7(v_u_1218_, v_as_1219_, v_i_boxed_1223_, v_stop_boxed_1224_, v_b_1222_);
lean_dec_ref(v_as_1219_);
return v_res_1225_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__6(size_t v_sz_1226_, size_t v_i_1227_, lean_object* v_bs_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_){
_start:
{
uint8_t v___x_1234_; 
v___x_1234_ = lean_usize_dec_lt(v_i_1227_, v_sz_1226_);
if (v___x_1234_ == 0)
{
lean_object* v___x_1235_; 
v___x_1235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1235_, 0, v_bs_1228_);
return v___x_1235_;
}
else
{
lean_object* v_v_1236_; lean_object* v___x_1237_; lean_object* v_bs_x27_1238_; lean_object* v___x_1239_; 
v_v_1236_ = lean_array_uget(v_bs_1228_, v_i_1227_);
v___x_1237_ = lean_unsigned_to_nat(0u);
v_bs_x27_1238_ = lean_array_uset(v_bs_1228_, v_i_1227_, v___x_1237_);
v___x_1239_ = l_Lean_Meta_mkEqRefl(v_v_1236_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_);
if (lean_obj_tag(v___x_1239_) == 0)
{
lean_object* v_a_1240_; size_t v___x_1241_; size_t v___x_1242_; lean_object* v___x_1243_; 
v_a_1240_ = lean_ctor_get(v___x_1239_, 0);
lean_inc(v_a_1240_);
lean_dec_ref_known(v___x_1239_, 1);
v___x_1241_ = ((size_t)1ULL);
v___x_1242_ = lean_usize_add(v_i_1227_, v___x_1241_);
v___x_1243_ = lean_array_uset(v_bs_x27_1238_, v_i_1227_, v_a_1240_);
v_i_1227_ = v___x_1242_;
v_bs_1228_ = v___x_1243_;
goto _start;
}
else
{
lean_object* v_a_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1252_; 
lean_dec_ref(v_bs_x27_1238_);
v_a_1245_ = lean_ctor_get(v___x_1239_, 0);
v_isSharedCheck_1252_ = !lean_is_exclusive(v___x_1239_);
if (v_isSharedCheck_1252_ == 0)
{
v___x_1247_ = v___x_1239_;
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_a_1245_);
lean_dec(v___x_1239_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___x_1250_; 
if (v_isShared_1248_ == 0)
{
v___x_1250_ = v___x_1247_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v_a_1245_);
v___x_1250_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
return v___x_1250_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__6___boxed(lean_object* v_sz_1253_, lean_object* v_i_1254_, lean_object* v_bs_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_){
_start:
{
size_t v_sz_boxed_1261_; size_t v_i_boxed_1262_; lean_object* v_res_1263_; 
v_sz_boxed_1261_ = lean_unbox_usize(v_sz_1253_);
lean_dec(v_sz_1253_);
v_i_boxed_1262_ = lean_unbox_usize(v_i_1254_);
lean_dec(v_i_1254_);
v_res_1263_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__6(v_sz_boxed_1261_, v_i_boxed_1262_, v_bs_1255_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_);
lean_dec(v___y_1259_);
lean_dec_ref(v___y_1258_);
lean_dec(v___y_1257_);
lean_dec_ref(v___y_1256_);
return v_res_1263_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__4___redArg(size_t v_sz_1264_, size_t v_i_1265_, lean_object* v_bs_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_){
_start:
{
uint8_t v___x_1270_; 
v___x_1270_ = lean_usize_dec_lt(v_i_1265_, v_sz_1264_);
if (v___x_1270_ == 0)
{
lean_object* v___x_1271_; 
v___x_1271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1271_, 0, v_bs_1266_);
return v___x_1271_;
}
else
{
lean_object* v_v_1272_; lean_object* v___x_1273_; lean_object* v_bs_x27_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; 
v_v_1272_ = lean_array_uget(v_bs_1266_, v_i_1265_);
v___x_1273_ = lean_unsigned_to_nat(0u);
v_bs_x27_1274_ = lean_array_uset(v_bs_1266_, v_i_1265_, v___x_1273_);
v___x_1275_ = lean_usize_to_nat(v_i_1265_);
v___x_1276_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__5___closed__1));
v___x_1277_ = l_Lean_Core_mkFreshUserName(v___x_1276_, v___y_1267_, v___y_1268_);
if (lean_obj_tag(v___x_1277_) == 0)
{
lean_object* v_a_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; size_t v___x_1283_; size_t v___x_1284_; lean_object* v___x_1285_; 
v_a_1278_ = lean_ctor_get(v___x_1277_, 0);
lean_inc(v_a_1278_);
lean_dec_ref_known(v___x_1277_, 1);
v___x_1279_ = lean_unsigned_to_nat(1u);
v___x_1280_ = lean_nat_add(v___x_1275_, v___x_1279_);
lean_dec(v___x_1275_);
v___x_1281_ = lean_name_append_index_after(v_a_1278_, v___x_1280_);
v___x_1282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1282_, 0, v___x_1281_);
lean_ctor_set(v___x_1282_, 1, v_v_1272_);
v___x_1283_ = ((size_t)1ULL);
v___x_1284_ = lean_usize_add(v_i_1265_, v___x_1283_);
v___x_1285_ = lean_array_uset(v_bs_x27_1274_, v_i_1265_, v___x_1282_);
v_i_1265_ = v___x_1284_;
v_bs_1266_ = v___x_1285_;
goto _start;
}
else
{
lean_object* v_a_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1294_; 
lean_dec(v___x_1275_);
lean_dec_ref(v_bs_x27_1274_);
lean_dec(v_v_1272_);
v_a_1287_ = lean_ctor_get(v___x_1277_, 0);
v_isSharedCheck_1294_ = !lean_is_exclusive(v___x_1277_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1289_ = v___x_1277_;
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_a_1287_);
lean_dec(v___x_1277_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v___x_1292_; 
if (v_isShared_1290_ == 0)
{
v___x_1292_ = v___x_1289_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_a_1287_);
v___x_1292_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
return v___x_1292_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__4___redArg___boxed(lean_object* v_sz_1295_, lean_object* v_i_1296_, lean_object* v_bs_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_){
_start:
{
size_t v_sz_boxed_1301_; size_t v_i_boxed_1302_; lean_object* v_res_1303_; 
v_sz_boxed_1301_ = lean_unbox_usize(v_sz_1295_);
lean_dec(v_sz_1295_);
v_i_boxed_1302_ = lean_unbox_usize(v_i_1296_);
lean_dec(v_i_1296_);
v_res_1303_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__4___redArg(v_sz_boxed_1301_, v_i_boxed_1302_, v_bs_1297_, v___y_1298_, v___y_1299_);
lean_dec(v___y_1299_);
lean_dec_ref(v___y_1298_);
return v_res_1303_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__1___redArg(lean_object* v_a_1304_, lean_object* v_b_1305_){
_start:
{
lean_object* v_array_1306_; lean_object* v_start_1307_; lean_object* v_stop_1308_; lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1321_; 
v_array_1306_ = lean_ctor_get(v_a_1304_, 0);
v_start_1307_ = lean_ctor_get(v_a_1304_, 1);
v_stop_1308_ = lean_ctor_get(v_a_1304_, 2);
v_isSharedCheck_1321_ = !lean_is_exclusive(v_a_1304_);
if (v_isSharedCheck_1321_ == 0)
{
v___x_1310_ = v_a_1304_;
v_isShared_1311_ = v_isSharedCheck_1321_;
goto v_resetjp_1309_;
}
else
{
lean_inc(v_stop_1308_);
lean_inc(v_start_1307_);
lean_inc(v_array_1306_);
lean_dec(v_a_1304_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1321_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
uint8_t v___x_1312_; 
v___x_1312_ = lean_nat_dec_lt(v_start_1307_, v_stop_1308_);
if (v___x_1312_ == 0)
{
lean_del_object(v___x_1310_);
lean_dec(v_stop_1308_);
lean_dec(v_start_1307_);
lean_dec_ref(v_array_1306_);
return v_b_1305_;
}
else
{
lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1316_; 
v___x_1313_ = lean_unsigned_to_nat(1u);
v___x_1314_ = lean_nat_add(v_start_1307_, v___x_1313_);
lean_inc_ref(v_array_1306_);
if (v_isShared_1311_ == 0)
{
lean_ctor_set(v___x_1310_, 1, v___x_1314_);
v___x_1316_ = v___x_1310_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v_array_1306_);
lean_ctor_set(v_reuseFailAlloc_1320_, 1, v___x_1314_);
lean_ctor_set(v_reuseFailAlloc_1320_, 2, v_stop_1308_);
v___x_1316_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
lean_object* v___x_1317_; lean_object* v___x_1318_; 
v___x_1317_ = lean_array_fget(v_array_1306_, v_start_1307_);
lean_dec(v_start_1307_);
lean_dec_ref(v_array_1306_);
v___x_1318_ = lean_array_push(v_b_1305_, v___x_1317_);
v_a_1304_ = v___x_1316_;
v_b_1305_ = v___x_1318_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___lam__0(lean_object* v___x_1322_, lean_object* v___x_1323_, lean_object* v_a_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_){
_start:
{
lean_object* v___x_16690__overap_1334_; lean_object* v___x_1335_; 
v___x_16690__overap_1334_ = l_instInhabitedOfMonad___redArg(v___x_1322_, v___x_1323_);
lean_inc(v___y_1332_);
lean_inc_ref(v___y_1331_);
lean_inc(v___y_1330_);
lean_inc_ref(v___y_1329_);
lean_inc(v___y_1328_);
lean_inc_ref(v___y_1327_);
lean_inc(v___y_1326_);
lean_inc_ref(v___y_1325_);
v___x_1335_ = lean_apply_9(v___x_16690__overap_1334_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_, lean_box(0));
return v___x_1335_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___lam__0___boxed(lean_object* v___x_1336_, lean_object* v___x_1337_, lean_object* v_a_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_){
_start:
{
lean_object* v_res_1348_; 
v_res_1348_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___lam__0(v___x_1336_, v___x_1337_, v_a_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_);
lean_dec(v___y_1346_);
lean_dec_ref(v___y_1345_);
lean_dec(v___y_1344_);
lean_dec_ref(v___y_1343_);
lean_dec(v___y_1342_);
lean_dec_ref(v___y_1341_);
lean_dec(v___y_1340_);
lean_dec_ref(v___y_1339_);
lean_dec_ref(v_a_1338_);
return v_res_1348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19_spec__21___redArg___lam__0(lean_object* v_k_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v_b_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_){
_start:
{
lean_object* v___x_1360_; 
lean_inc(v___y_1358_);
lean_inc_ref(v___y_1357_);
lean_inc(v___y_1356_);
lean_inc_ref(v___y_1355_);
lean_inc(v___y_1353_);
lean_inc_ref(v___y_1352_);
lean_inc(v___y_1351_);
lean_inc_ref(v___y_1350_);
v___x_1360_ = lean_apply_10(v_k_1349_, v_b_1354_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, lean_box(0));
return v___x_1360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19_spec__21___redArg___lam__0___boxed(lean_object* v_k_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v_b_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_){
_start:
{
lean_object* v_res_1372_; 
v_res_1372_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19_spec__21___redArg___lam__0(v_k_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v_b_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_);
lean_dec(v___y_1370_);
lean_dec_ref(v___y_1369_);
lean_dec(v___y_1368_);
lean_dec_ref(v___y_1367_);
lean_dec(v___y_1365_);
lean_dec_ref(v___y_1364_);
lean_dec(v___y_1363_);
lean_dec_ref(v___y_1362_);
return v_res_1372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19_spec__21___redArg(lean_object* v_name_1373_, uint8_t v_bi_1374_, lean_object* v_type_1375_, lean_object* v_k_1376_, uint8_t v_kind_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_){
_start:
{
lean_object* v___f_1387_; lean_object* v___x_1388_; 
lean_inc(v___y_1381_);
lean_inc_ref(v___y_1380_);
lean_inc(v___y_1379_);
lean_inc_ref(v___y_1378_);
v___f_1387_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19_spec__21___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_1387_, 0, v_k_1376_);
lean_closure_set(v___f_1387_, 1, v___y_1378_);
lean_closure_set(v___f_1387_, 2, v___y_1379_);
lean_closure_set(v___f_1387_, 3, v___y_1380_);
lean_closure_set(v___f_1387_, 4, v___y_1381_);
v___x_1388_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1373_, v_bi_1374_, v_type_1375_, v___f_1387_, v_kind_1377_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_);
if (lean_obj_tag(v___x_1388_) == 0)
{
return v___x_1388_;
}
else
{
lean_object* v_a_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1396_; 
v_a_1389_ = lean_ctor_get(v___x_1388_, 0);
v_isSharedCheck_1396_ = !lean_is_exclusive(v___x_1388_);
if (v_isSharedCheck_1396_ == 0)
{
v___x_1391_ = v___x_1388_;
v_isShared_1392_ = v_isSharedCheck_1396_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_a_1389_);
lean_dec(v___x_1388_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19_spec__21___redArg___boxed(lean_object* v_name_1397_, lean_object* v_bi_1398_, lean_object* v_type_1399_, lean_object* v_k_1400_, lean_object* v_kind_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_){
_start:
{
uint8_t v_bi_boxed_1411_; uint8_t v_kind_boxed_1412_; lean_object* v_res_1413_; 
v_bi_boxed_1411_ = lean_unbox(v_bi_1398_);
v_kind_boxed_1412_ = lean_unbox(v_kind_1401_);
v_res_1413_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19_spec__21___redArg(v_name_1397_, v_bi_boxed_1411_, v_type_1399_, v_k_1400_, v_kind_boxed_1412_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_);
lean_dec(v___y_1409_);
lean_dec_ref(v___y_1408_);
lean_dec(v___y_1407_);
lean_dec_ref(v___y_1406_);
lean_dec(v___y_1405_);
lean_dec_ref(v___y_1404_);
lean_dec(v___y_1403_);
lean_dec_ref(v___y_1402_);
return v_res_1413_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___lam__1___boxed(lean_object* v_acc_1418_, lean_object* v_declInfos_1419_, lean_object* v_k_1420_, lean_object* v_kind_1421_, lean_object* v_x_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_){
_start:
{
uint8_t v_kind_boxed_1432_; lean_object* v_res_1433_; 
v_kind_boxed_1432_ = lean_unbox(v_kind_1421_);
v_res_1433_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___lam__1(v_acc_1418_, v_declInfos_1419_, v_k_1420_, v_kind_boxed_1432_, v_x_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_);
lean_dec(v___y_1430_);
lean_dec_ref(v___y_1429_);
lean_dec(v___y_1428_);
lean_dec_ref(v___y_1427_);
lean_dec(v___y_1426_);
lean_dec_ref(v___y_1425_);
lean_dec(v___y_1424_);
lean_dec_ref(v___y_1423_);
return v_res_1433_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19(lean_object* v_declInfos_1434_, lean_object* v_k_1435_, uint8_t v_kind_1436_, lean_object* v_acc_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_){
_start:
{
lean_object* v___x_1447_; lean_object* v_toApplicative_1448_; lean_object* v_toFunctor_1449_; lean_object* v_toSeq_1450_; lean_object* v_toSeqLeft_1451_; lean_object* v_toSeqRight_1452_; lean_object* v___f_1453_; lean_object* v___f_1454_; lean_object* v___f_1455_; lean_object* v___f_1456_; lean_object* v___x_1457_; lean_object* v___f_1458_; lean_object* v___f_1459_; lean_object* v___f_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v_toApplicative_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1582_; 
v___x_1447_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__1);
v_toApplicative_1448_ = lean_ctor_get(v___x_1447_, 0);
v_toFunctor_1449_ = lean_ctor_get(v_toApplicative_1448_, 0);
v_toSeq_1450_ = lean_ctor_get(v_toApplicative_1448_, 2);
v_toSeqLeft_1451_ = lean_ctor_get(v_toApplicative_1448_, 3);
v_toSeqRight_1452_ = lean_ctor_get(v_toApplicative_1448_, 4);
v___f_1453_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__2));
v___f_1454_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_1449_, 2);
v___f_1455_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1455_, 0, v_toFunctor_1449_);
v___f_1456_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1456_, 0, v_toFunctor_1449_);
v___x_1457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1457_, 0, v___f_1455_);
lean_ctor_set(v___x_1457_, 1, v___f_1456_);
lean_inc(v_toSeqRight_1452_);
v___f_1458_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1458_, 0, v_toSeqRight_1452_);
lean_inc(v_toSeqLeft_1451_);
v___f_1459_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1459_, 0, v_toSeqLeft_1451_);
lean_inc(v_toSeq_1450_);
v___f_1460_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1460_, 0, v_toSeq_1450_);
v___x_1461_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1461_, 0, v___x_1457_);
lean_ctor_set(v___x_1461_, 1, v___f_1453_);
lean_ctor_set(v___x_1461_, 2, v___f_1460_);
lean_ctor_set(v___x_1461_, 3, v___f_1459_);
lean_ctor_set(v___x_1461_, 4, v___f_1458_);
v___x_1462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1462_, 0, v___x_1461_);
lean_ctor_set(v___x_1462_, 1, v___f_1454_);
v___x_1463_ = l_StateRefT_x27_instMonad___redArg(v___x_1462_);
v_toApplicative_1464_ = lean_ctor_get(v___x_1463_, 0);
v_isSharedCheck_1582_ = !lean_is_exclusive(v___x_1463_);
if (v_isSharedCheck_1582_ == 0)
{
lean_object* v_unused_1583_; 
v_unused_1583_ = lean_ctor_get(v___x_1463_, 1);
lean_dec(v_unused_1583_);
v___x_1466_ = v___x_1463_;
v_isShared_1467_ = v_isSharedCheck_1582_;
goto v_resetjp_1465_;
}
else
{
lean_inc(v_toApplicative_1464_);
lean_dec(v___x_1463_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1582_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v_toFunctor_1468_; lean_object* v_toSeq_1469_; lean_object* v_toSeqLeft_1470_; lean_object* v_toSeqRight_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1580_; 
v_toFunctor_1468_ = lean_ctor_get(v_toApplicative_1464_, 0);
v_toSeq_1469_ = lean_ctor_get(v_toApplicative_1464_, 2);
v_toSeqLeft_1470_ = lean_ctor_get(v_toApplicative_1464_, 3);
v_toSeqRight_1471_ = lean_ctor_get(v_toApplicative_1464_, 4);
v_isSharedCheck_1580_ = !lean_is_exclusive(v_toApplicative_1464_);
if (v_isSharedCheck_1580_ == 0)
{
lean_object* v_unused_1581_; 
v_unused_1581_ = lean_ctor_get(v_toApplicative_1464_, 1);
lean_dec(v_unused_1581_);
v___x_1473_ = v_toApplicative_1464_;
v_isShared_1474_ = v_isSharedCheck_1580_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_toSeqRight_1471_);
lean_inc(v_toSeqLeft_1470_);
lean_inc(v_toSeq_1469_);
lean_inc(v_toFunctor_1468_);
lean_dec(v_toApplicative_1464_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1580_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v___f_1475_; lean_object* v___f_1476_; lean_object* v___f_1477_; lean_object* v___f_1478_; lean_object* v___x_1479_; lean_object* v___f_1480_; lean_object* v___f_1481_; lean_object* v___f_1482_; lean_object* v___x_1484_; 
v___f_1475_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__4));
v___f_1476_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__5));
lean_inc_ref(v_toFunctor_1468_);
v___f_1477_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1477_, 0, v_toFunctor_1468_);
v___f_1478_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1478_, 0, v_toFunctor_1468_);
v___x_1479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1479_, 0, v___f_1477_);
lean_ctor_set(v___x_1479_, 1, v___f_1478_);
v___f_1480_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1480_, 0, v_toSeqRight_1471_);
v___f_1481_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1481_, 0, v_toSeqLeft_1470_);
v___f_1482_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1482_, 0, v_toSeq_1469_);
if (v_isShared_1474_ == 0)
{
lean_ctor_set(v___x_1473_, 4, v___f_1480_);
lean_ctor_set(v___x_1473_, 3, v___f_1481_);
lean_ctor_set(v___x_1473_, 2, v___f_1482_);
lean_ctor_set(v___x_1473_, 1, v___f_1475_);
lean_ctor_set(v___x_1473_, 0, v___x_1479_);
v___x_1484_ = v___x_1473_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v___x_1479_);
lean_ctor_set(v_reuseFailAlloc_1579_, 1, v___f_1475_);
lean_ctor_set(v_reuseFailAlloc_1579_, 2, v___f_1482_);
lean_ctor_set(v_reuseFailAlloc_1579_, 3, v___f_1481_);
lean_ctor_set(v_reuseFailAlloc_1579_, 4, v___f_1480_);
v___x_1484_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
lean_object* v___x_1486_; 
if (v_isShared_1467_ == 0)
{
lean_ctor_set(v___x_1466_, 1, v___f_1476_);
lean_ctor_set(v___x_1466_, 0, v___x_1484_);
v___x_1486_ = v___x_1466_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v___x_1484_);
lean_ctor_set(v_reuseFailAlloc_1578_, 1, v___f_1476_);
v___x_1486_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
lean_object* v___x_1487_; lean_object* v_toApplicative_1488_; lean_object* v___x_1490_; uint8_t v_isShared_1491_; uint8_t v_isSharedCheck_1576_; 
v___x_1487_ = l_StateRefT_x27_instMonad___redArg(v___x_1486_);
v_toApplicative_1488_ = lean_ctor_get(v___x_1487_, 0);
v_isSharedCheck_1576_ = !lean_is_exclusive(v___x_1487_);
if (v_isSharedCheck_1576_ == 0)
{
lean_object* v_unused_1577_; 
v_unused_1577_ = lean_ctor_get(v___x_1487_, 1);
lean_dec(v_unused_1577_);
v___x_1490_ = v___x_1487_;
v_isShared_1491_ = v_isSharedCheck_1576_;
goto v_resetjp_1489_;
}
else
{
lean_inc(v_toApplicative_1488_);
lean_dec(v___x_1487_);
v___x_1490_ = lean_box(0);
v_isShared_1491_ = v_isSharedCheck_1576_;
goto v_resetjp_1489_;
}
v_resetjp_1489_:
{
lean_object* v_toFunctor_1492_; lean_object* v_toSeq_1493_; lean_object* v_toSeqLeft_1494_; lean_object* v_toSeqRight_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1574_; 
v_toFunctor_1492_ = lean_ctor_get(v_toApplicative_1488_, 0);
v_toSeq_1493_ = lean_ctor_get(v_toApplicative_1488_, 2);
v_toSeqLeft_1494_ = lean_ctor_get(v_toApplicative_1488_, 3);
v_toSeqRight_1495_ = lean_ctor_get(v_toApplicative_1488_, 4);
v_isSharedCheck_1574_ = !lean_is_exclusive(v_toApplicative_1488_);
if (v_isSharedCheck_1574_ == 0)
{
lean_object* v_unused_1575_; 
v_unused_1575_ = lean_ctor_get(v_toApplicative_1488_, 1);
lean_dec(v_unused_1575_);
v___x_1497_ = v_toApplicative_1488_;
v_isShared_1498_ = v_isSharedCheck_1574_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_toSeqRight_1495_);
lean_inc(v_toSeqLeft_1494_);
lean_inc(v_toSeq_1493_);
lean_inc(v_toFunctor_1492_);
lean_dec(v_toApplicative_1488_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1574_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
lean_object* v___f_1499_; lean_object* v___f_1500_; lean_object* v___f_1501_; lean_object* v___f_1502_; lean_object* v___x_1503_; lean_object* v___f_1504_; lean_object* v___f_1505_; lean_object* v___f_1506_; lean_object* v___x_1508_; 
v___f_1499_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___closed__0));
v___f_1500_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___closed__1));
lean_inc_ref(v_toFunctor_1492_);
v___f_1501_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1501_, 0, v_toFunctor_1492_);
v___f_1502_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1502_, 0, v_toFunctor_1492_);
v___x_1503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1503_, 0, v___f_1501_);
lean_ctor_set(v___x_1503_, 1, v___f_1502_);
v___f_1504_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1504_, 0, v_toSeqRight_1495_);
v___f_1505_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1505_, 0, v_toSeqLeft_1494_);
v___f_1506_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1506_, 0, v_toSeq_1493_);
if (v_isShared_1498_ == 0)
{
lean_ctor_set(v___x_1497_, 4, v___f_1504_);
lean_ctor_set(v___x_1497_, 3, v___f_1505_);
lean_ctor_set(v___x_1497_, 2, v___f_1506_);
lean_ctor_set(v___x_1497_, 1, v___f_1499_);
lean_ctor_set(v___x_1497_, 0, v___x_1503_);
v___x_1508_ = v___x_1497_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v___x_1503_);
lean_ctor_set(v_reuseFailAlloc_1573_, 1, v___f_1499_);
lean_ctor_set(v_reuseFailAlloc_1573_, 2, v___f_1506_);
lean_ctor_set(v_reuseFailAlloc_1573_, 3, v___f_1505_);
lean_ctor_set(v_reuseFailAlloc_1573_, 4, v___f_1504_);
v___x_1508_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
lean_object* v___x_1510_; 
if (v_isShared_1491_ == 0)
{
lean_ctor_set(v___x_1490_, 1, v___f_1500_);
lean_ctor_set(v___x_1490_, 0, v___x_1508_);
v___x_1510_ = v___x_1490_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v___x_1508_);
lean_ctor_set(v_reuseFailAlloc_1572_, 1, v___f_1500_);
v___x_1510_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
lean_object* v___x_1511_; lean_object* v_toApplicative_1512_; lean_object* v___x_1514_; uint8_t v_isShared_1515_; uint8_t v_isSharedCheck_1570_; 
v___x_1511_ = l_StateRefT_x27_instMonad___redArg(v___x_1510_);
v_toApplicative_1512_ = lean_ctor_get(v___x_1511_, 0);
v_isSharedCheck_1570_ = !lean_is_exclusive(v___x_1511_);
if (v_isSharedCheck_1570_ == 0)
{
lean_object* v_unused_1571_; 
v_unused_1571_ = lean_ctor_get(v___x_1511_, 1);
lean_dec(v_unused_1571_);
v___x_1514_ = v___x_1511_;
v_isShared_1515_ = v_isSharedCheck_1570_;
goto v_resetjp_1513_;
}
else
{
lean_inc(v_toApplicative_1512_);
lean_dec(v___x_1511_);
v___x_1514_ = lean_box(0);
v_isShared_1515_ = v_isSharedCheck_1570_;
goto v_resetjp_1513_;
}
v_resetjp_1513_:
{
lean_object* v_toFunctor_1516_; lean_object* v_toSeq_1517_; lean_object* v_toSeqLeft_1518_; lean_object* v_toSeqRight_1519_; lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1568_; 
v_toFunctor_1516_ = lean_ctor_get(v_toApplicative_1512_, 0);
v_toSeq_1517_ = lean_ctor_get(v_toApplicative_1512_, 2);
v_toSeqLeft_1518_ = lean_ctor_get(v_toApplicative_1512_, 3);
v_toSeqRight_1519_ = lean_ctor_get(v_toApplicative_1512_, 4);
v_isSharedCheck_1568_ = !lean_is_exclusive(v_toApplicative_1512_);
if (v_isSharedCheck_1568_ == 0)
{
lean_object* v_unused_1569_; 
v_unused_1569_ = lean_ctor_get(v_toApplicative_1512_, 1);
lean_dec(v_unused_1569_);
v___x_1521_ = v_toApplicative_1512_;
v_isShared_1522_ = v_isSharedCheck_1568_;
goto v_resetjp_1520_;
}
else
{
lean_inc(v_toSeqRight_1519_);
lean_inc(v_toSeqLeft_1518_);
lean_inc(v_toSeq_1517_);
lean_inc(v_toFunctor_1516_);
lean_dec(v_toApplicative_1512_);
v___x_1521_ = lean_box(0);
v_isShared_1522_ = v_isSharedCheck_1568_;
goto v_resetjp_1520_;
}
v_resetjp_1520_:
{
lean_object* v___f_1523_; lean_object* v___f_1524_; lean_object* v___f_1525_; lean_object* v___f_1526_; lean_object* v___x_1527_; lean_object* v___f_1528_; lean_object* v___f_1529_; lean_object* v___f_1530_; lean_object* v___x_1532_; 
v___f_1523_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___closed__2));
v___f_1524_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___closed__3));
lean_inc_ref(v_toFunctor_1516_);
v___f_1525_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1525_, 0, v_toFunctor_1516_);
v___f_1526_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1526_, 0, v_toFunctor_1516_);
v___x_1527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1527_, 0, v___f_1525_);
lean_ctor_set(v___x_1527_, 1, v___f_1526_);
v___f_1528_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1528_, 0, v_toSeqRight_1519_);
v___f_1529_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1529_, 0, v_toSeqLeft_1518_);
v___f_1530_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1530_, 0, v_toSeq_1517_);
if (v_isShared_1522_ == 0)
{
lean_ctor_set(v___x_1521_, 4, v___f_1528_);
lean_ctor_set(v___x_1521_, 3, v___f_1529_);
lean_ctor_set(v___x_1521_, 2, v___f_1530_);
lean_ctor_set(v___x_1521_, 1, v___f_1523_);
lean_ctor_set(v___x_1521_, 0, v___x_1527_);
v___x_1532_ = v___x_1521_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v___x_1527_);
lean_ctor_set(v_reuseFailAlloc_1567_, 1, v___f_1523_);
lean_ctor_set(v_reuseFailAlloc_1567_, 2, v___f_1530_);
lean_ctor_set(v_reuseFailAlloc_1567_, 3, v___f_1529_);
lean_ctor_set(v_reuseFailAlloc_1567_, 4, v___f_1528_);
v___x_1532_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1531_;
}
v_reusejp_1531_:
{
lean_object* v___x_1534_; 
if (v_isShared_1515_ == 0)
{
lean_ctor_set(v___x_1514_, 1, v___f_1524_);
lean_ctor_set(v___x_1514_, 0, v___x_1532_);
v___x_1534_ = v___x_1514_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v___x_1532_);
lean_ctor_set(v_reuseFailAlloc_1566_, 1, v___f_1524_);
v___x_1534_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
lean_object* v___x_1535_; lean_object* v___x_1536_; uint8_t v___x_1537_; 
v___x_1535_ = lean_array_get_size(v_acc_1437_);
v___x_1536_ = lean_array_get_size(v_declInfos_1434_);
v___x_1537_ = lean_nat_dec_lt(v___x_1535_, v___x_1536_);
if (v___x_1537_ == 0)
{
lean_object* v___x_1538_; 
lean_dec_ref(v___x_1534_);
lean_dec_ref(v_declInfos_1434_);
lean_inc(v___y_1445_);
lean_inc_ref(v___y_1444_);
lean_inc(v___y_1443_);
lean_inc_ref(v___y_1442_);
lean_inc(v___y_1441_);
lean_inc_ref(v___y_1440_);
lean_inc(v___y_1439_);
lean_inc_ref(v___y_1438_);
v___x_1538_ = lean_apply_10(v_k_1435_, v_acc_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, lean_box(0));
return v___x_1538_;
}
else
{
lean_object* v___x_1539_; uint8_t v___x_1540_; lean_object* v___x_1541_; lean_object* v___f_1542_; lean_object* v___f_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v_snd_1548_; lean_object* v_fst_1549_; lean_object* v_fst_1550_; lean_object* v_snd_1551_; lean_object* v___x_1552_; lean_object* v___f_1553_; lean_object* v___x_1554_; 
v___x_1539_ = lean_box(0);
v___x_1540_ = 0;
v___x_1541_ = l_Lean_instInhabitedExpr;
v___f_1542_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___lam__0___boxed), 12, 2);
lean_closure_set(v___f_1542_, 0, v___x_1534_);
lean_closure_set(v___f_1542_, 1, v___x_1541_);
v___f_1543_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1543_, 0, v___f_1542_);
v___x_1544_ = lean_box(v___x_1540_);
v___x_1545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1545_, 0, v___x_1544_);
lean_ctor_set(v___x_1545_, 1, v___f_1543_);
v___x_1546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1546_, 0, v___x_1539_);
lean_ctor_set(v___x_1546_, 1, v___x_1545_);
v___x_1547_ = lean_array_get(v___x_1546_, v_declInfos_1434_, v___x_1535_);
lean_dec_ref_known(v___x_1546_, 2);
v_snd_1548_ = lean_ctor_get(v___x_1547_, 1);
lean_inc(v_snd_1548_);
v_fst_1549_ = lean_ctor_get(v___x_1547_, 0);
lean_inc(v_fst_1549_);
lean_dec(v___x_1547_);
v_fst_1550_ = lean_ctor_get(v_snd_1548_, 0);
lean_inc(v_fst_1550_);
v_snd_1551_ = lean_ctor_get(v_snd_1548_, 1);
lean_inc(v_snd_1551_);
lean_dec(v_snd_1548_);
v___x_1552_ = lean_box(v_kind_1436_);
lean_inc_ref(v_acc_1437_);
v___f_1553_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___lam__1___boxed), 14, 4);
lean_closure_set(v___f_1553_, 0, v_acc_1437_);
lean_closure_set(v___f_1553_, 1, v_declInfos_1434_);
lean_closure_set(v___f_1553_, 2, v_k_1435_);
lean_closure_set(v___f_1553_, 3, v___x_1552_);
lean_inc(v___y_1445_);
lean_inc_ref(v___y_1444_);
lean_inc(v___y_1443_);
lean_inc_ref(v___y_1442_);
lean_inc(v___y_1441_);
lean_inc_ref(v___y_1440_);
lean_inc(v___y_1439_);
lean_inc_ref(v___y_1438_);
v___x_1554_ = lean_apply_10(v_snd_1551_, v_acc_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, lean_box(0));
if (lean_obj_tag(v___x_1554_) == 0)
{
lean_object* v_a_1555_; uint8_t v___x_1556_; lean_object* v___x_1557_; 
v_a_1555_ = lean_ctor_get(v___x_1554_, 0);
lean_inc(v_a_1555_);
lean_dec_ref_known(v___x_1554_, 1);
v___x_1556_ = lean_unbox(v_fst_1550_);
lean_dec(v_fst_1550_);
v___x_1557_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19_spec__21___redArg(v_fst_1549_, v___x_1556_, v_a_1555_, v___f_1553_, v_kind_1436_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_);
return v___x_1557_;
}
else
{
lean_object* v_a_1558_; lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1565_; 
lean_dec_ref(v___f_1553_);
lean_dec(v_fst_1550_);
lean_dec(v_fst_1549_);
v_a_1558_ = lean_ctor_get(v___x_1554_, 0);
v_isSharedCheck_1565_ = !lean_is_exclusive(v___x_1554_);
if (v_isSharedCheck_1565_ == 0)
{
v___x_1560_ = v___x_1554_;
v_isShared_1561_ = v_isSharedCheck_1565_;
goto v_resetjp_1559_;
}
else
{
lean_inc(v_a_1558_);
lean_dec(v___x_1554_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1565_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
lean_object* v___x_1563_; 
if (v_isShared_1561_ == 0)
{
v___x_1563_ = v___x_1560_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v_a_1558_);
v___x_1563_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
return v___x_1563_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___lam__1(lean_object* v_acc_1584_, lean_object* v_declInfos_1585_, lean_object* v_k_1586_, uint8_t v_kind_1587_, lean_object* v_x_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_){
_start:
{
lean_object* v___x_1598_; lean_object* v___x_1599_; 
v___x_1598_ = lean_array_push(v_acc_1584_, v_x_1588_);
v___x_1599_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19(v_declInfos_1585_, v_k_1586_, v_kind_1587_, v___x_1598_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_);
return v___x_1599_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___boxed(lean_object* v_declInfos_1600_, lean_object* v_k_1601_, lean_object* v_kind_1602_, lean_object* v_acc_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_){
_start:
{
uint8_t v_kind_boxed_1613_; lean_object* v_res_1614_; 
v_kind_boxed_1613_ = lean_unbox(v_kind_1602_);
v_res_1614_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19(v_declInfos_1600_, v_k_1601_, v_kind_boxed_1613_, v_acc_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_);
lean_dec(v___y_1611_);
lean_dec_ref(v___y_1610_);
lean_dec(v___y_1609_);
lean_dec_ref(v___y_1608_);
lean_dec(v___y_1607_);
lean_dec_ref(v___y_1606_);
lean_dec(v___y_1605_);
lean_dec_ref(v___y_1604_);
return v_res_1614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14(lean_object* v_declInfos_1615_, lean_object* v_k_1616_, uint8_t v_kind_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_){
_start:
{
lean_object* v___x_1627_; lean_object* v___x_1628_; 
v___x_1627_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__1));
v___x_1628_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19(v_declInfos_1615_, v_k_1616_, v_kind_1617_, v___x_1627_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_);
return v___x_1628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14___boxed(lean_object* v_declInfos_1629_, lean_object* v_k_1630_, lean_object* v_kind_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_){
_start:
{
uint8_t v_kind_boxed_1641_; lean_object* v_res_1642_; 
v_kind_boxed_1641_ = lean_unbox(v_kind_1631_);
v_res_1642_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14(v_declInfos_1629_, v_k_1630_, v_kind_boxed_1641_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__13(size_t v_sz_1643_, size_t v_i_1644_, lean_object* v_bs_1645_){
_start:
{
uint8_t v___x_1646_; 
v___x_1646_ = lean_usize_dec_lt(v_i_1644_, v_sz_1643_);
if (v___x_1646_ == 0)
{
return v_bs_1645_;
}
else
{
lean_object* v_v_1647_; lean_object* v_fst_1648_; lean_object* v_snd_1649_; lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1665_; 
v_v_1647_ = lean_array_uget(v_bs_1645_, v_i_1644_);
v_fst_1648_ = lean_ctor_get(v_v_1647_, 0);
v_snd_1649_ = lean_ctor_get(v_v_1647_, 1);
v_isSharedCheck_1665_ = !lean_is_exclusive(v_v_1647_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1651_ = v_v_1647_;
v_isShared_1652_ = v_isSharedCheck_1665_;
goto v_resetjp_1650_;
}
else
{
lean_inc(v_snd_1649_);
lean_inc(v_fst_1648_);
lean_dec(v_v_1647_);
v___x_1651_ = lean_box(0);
v_isShared_1652_ = v_isSharedCheck_1665_;
goto v_resetjp_1650_;
}
v_resetjp_1650_:
{
lean_object* v___x_1653_; lean_object* v_bs_x27_1654_; uint8_t v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1658_; 
v___x_1653_ = lean_unsigned_to_nat(0u);
v_bs_x27_1654_ = lean_array_uset(v_bs_1645_, v_i_1644_, v___x_1653_);
v___x_1655_ = 0;
v___x_1656_ = lean_box(v___x_1655_);
if (v_isShared_1652_ == 0)
{
lean_ctor_set(v___x_1651_, 0, v___x_1656_);
v___x_1658_ = v___x_1651_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v___x_1656_);
lean_ctor_set(v_reuseFailAlloc_1664_, 1, v_snd_1649_);
v___x_1658_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
lean_object* v___x_1659_; size_t v___x_1660_; size_t v___x_1661_; lean_object* v___x_1662_; 
v___x_1659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1659_, 0, v_fst_1648_);
lean_ctor_set(v___x_1659_, 1, v___x_1658_);
v___x_1660_ = ((size_t)1ULL);
v___x_1661_ = lean_usize_add(v_i_1644_, v___x_1660_);
v___x_1662_ = lean_array_uset(v_bs_x27_1654_, v_i_1644_, v___x_1659_);
v_i_1644_ = v___x_1661_;
v_bs_1645_ = v___x_1662_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__13___boxed(lean_object* v_sz_1666_, lean_object* v_i_1667_, lean_object* v_bs_1668_){
_start:
{
size_t v_sz_boxed_1669_; size_t v_i_boxed_1670_; lean_object* v_res_1671_; 
v_sz_boxed_1669_ = lean_unbox_usize(v_sz_1666_);
lean_dec(v_sz_1666_);
v_i_boxed_1670_ = lean_unbox_usize(v_i_1667_);
lean_dec(v_i_1667_);
v_res_1671_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__13(v_sz_boxed_1669_, v_i_boxed_1670_, v_bs_1668_);
return v_res_1671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8(lean_object* v_declInfos_1672_, lean_object* v_k_1673_, uint8_t v_kind_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_){
_start:
{
size_t v_sz_1684_; size_t v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; 
v_sz_1684_ = lean_array_size(v_declInfos_1672_);
v___x_1685_ = ((size_t)0ULL);
v___x_1686_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__13(v_sz_1684_, v___x_1685_, v_declInfos_1672_);
v___x_1687_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14(v___x_1686_, v_k_1673_, v_kind_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_);
return v___x_1687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8___boxed(lean_object* v_declInfos_1688_, lean_object* v_k_1689_, lean_object* v_kind_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_){
_start:
{
uint8_t v_kind_boxed_1700_; lean_object* v_res_1701_; 
v_kind_boxed_1700_ = lean_unbox(v_kind_1690_);
v_res_1701_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8(v_declInfos_1688_, v_k_1689_, v_kind_boxed_1700_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_);
lean_dec(v___y_1698_);
lean_dec_ref(v___y_1697_);
lean_dec(v___y_1696_);
lean_dec_ref(v___y_1695_);
lean_dec(v___y_1694_);
lean_dec_ref(v___y_1693_);
lean_dec(v___y_1692_);
lean_dec_ref(v___y_1691_);
return v_res_1701_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__7___lam__0(lean_object* v_snd_1702_, lean_object* v_x_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_){
_start:
{
lean_object* v___x_1713_; 
v___x_1713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1713_, 0, v_snd_1702_);
return v___x_1713_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__7___lam__0___boxed(lean_object* v_snd_1714_, lean_object* v_x_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_){
_start:
{
lean_object* v_res_1725_; 
v_res_1725_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__7___lam__0(v_snd_1714_, v_x_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_);
lean_dec(v___y_1723_);
lean_dec_ref(v___y_1722_);
lean_dec(v___y_1721_);
lean_dec_ref(v___y_1720_);
lean_dec(v___y_1719_);
lean_dec_ref(v___y_1718_);
lean_dec(v___y_1717_);
lean_dec_ref(v___y_1716_);
lean_dec_ref(v_x_1715_);
return v_res_1725_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__7(size_t v_sz_1726_, size_t v_i_1727_, lean_object* v_bs_1728_){
_start:
{
uint8_t v___x_1729_; 
v___x_1729_ = lean_usize_dec_lt(v_i_1727_, v_sz_1726_);
if (v___x_1729_ == 0)
{
return v_bs_1728_;
}
else
{
lean_object* v_v_1730_; lean_object* v_fst_1731_; lean_object* v_snd_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1746_; 
v_v_1730_ = lean_array_uget(v_bs_1728_, v_i_1727_);
v_fst_1731_ = lean_ctor_get(v_v_1730_, 0);
v_snd_1732_ = lean_ctor_get(v_v_1730_, 1);
v_isSharedCheck_1746_ = !lean_is_exclusive(v_v_1730_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1734_ = v_v_1730_;
v_isShared_1735_ = v_isSharedCheck_1746_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_snd_1732_);
lean_inc(v_fst_1731_);
lean_dec(v_v_1730_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1746_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
lean_object* v___x_1736_; lean_object* v_bs_x27_1737_; lean_object* v___f_1738_; lean_object* v___x_1740_; 
v___x_1736_ = lean_unsigned_to_nat(0u);
v_bs_x27_1737_ = lean_array_uset(v_bs_1728_, v_i_1727_, v___x_1736_);
v___f_1738_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__7___lam__0___boxed), 11, 1);
lean_closure_set(v___f_1738_, 0, v_snd_1732_);
if (v_isShared_1735_ == 0)
{
lean_ctor_set(v___x_1734_, 1, v___f_1738_);
v___x_1740_ = v___x_1734_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v_fst_1731_);
lean_ctor_set(v_reuseFailAlloc_1745_, 1, v___f_1738_);
v___x_1740_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
size_t v___x_1741_; size_t v___x_1742_; lean_object* v___x_1743_; 
v___x_1741_ = ((size_t)1ULL);
v___x_1742_ = lean_usize_add(v_i_1727_, v___x_1741_);
v___x_1743_ = lean_array_uset(v_bs_x27_1737_, v_i_1727_, v___x_1740_);
v_i_1727_ = v___x_1742_;
v_bs_1728_ = v___x_1743_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__7___boxed(lean_object* v_sz_1747_, lean_object* v_i_1748_, lean_object* v_bs_1749_){
_start:
{
size_t v_sz_boxed_1750_; size_t v_i_boxed_1751_; lean_object* v_res_1752_; 
v_sz_boxed_1750_ = lean_unbox_usize(v_sz_1747_);
lean_dec(v_sz_1747_);
v_i_boxed_1751_ = lean_unbox_usize(v_i_1748_);
lean_dec(v_i_1748_);
v_res_1752_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__7(v_sz_boxed_1750_, v_i_boxed_1751_, v_bs_1749_);
return v_res_1752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5(lean_object* v_declInfos_1753_, lean_object* v_k_1754_, uint8_t v_kind_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_){
_start:
{
size_t v_sz_1765_; size_t v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; 
v_sz_1765_ = lean_array_size(v_declInfos_1753_);
v___x_1766_ = ((size_t)0ULL);
v___x_1767_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__7(v_sz_1765_, v___x_1766_, v_declInfos_1753_);
v___x_1768_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8(v___x_1767_, v_k_1754_, v_kind_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_);
return v___x_1768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5___boxed(lean_object* v_declInfos_1769_, lean_object* v_k_1770_, lean_object* v_kind_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_){
_start:
{
uint8_t v_kind_boxed_1781_; lean_object* v_res_1782_; 
v_kind_boxed_1781_ = lean_unbox(v_kind_1771_);
v_res_1782_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5(v_declInfos_1769_, v_k_1770_, v_kind_boxed_1781_, v___y_1772_, v___y_1773_, v___y_1774_, v___y_1775_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_);
lean_dec(v___y_1779_);
lean_dec_ref(v___y_1778_);
lean_dec(v___y_1777_);
lean_dec_ref(v___y_1776_);
lean_dec(v___y_1775_);
lean_dec_ref(v___y_1774_);
lean_dec(v___y_1773_);
lean_dec_ref(v___y_1772_);
return v_res_1782_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__3(size_t v_sz_1783_, size_t v_i_1784_, lean_object* v_bs_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_){
_start:
{
uint8_t v___x_1791_; 
v___x_1791_ = lean_usize_dec_lt(v_i_1784_, v_sz_1783_);
if (v___x_1791_ == 0)
{
lean_object* v___x_1792_; 
v___x_1792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1792_, 0, v_bs_1785_);
return v___x_1792_;
}
else
{
lean_object* v_v_1793_; lean_object* v___x_1794_; lean_object* v_bs_x27_1795_; lean_object* v___x_1796_; 
v_v_1793_ = lean_array_uget(v_bs_1785_, v_i_1784_);
v___x_1794_ = lean_unsigned_to_nat(0u);
v_bs_x27_1795_ = lean_array_uset(v_bs_1785_, v_i_1784_, v___x_1794_);
lean_inc(v___y_1789_);
lean_inc_ref(v___y_1788_);
lean_inc(v___y_1787_);
lean_inc_ref(v___y_1786_);
v___x_1796_ = lean_infer_type(v_v_1793_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_);
if (lean_obj_tag(v___x_1796_) == 0)
{
lean_object* v_a_1797_; size_t v___x_1798_; size_t v___x_1799_; lean_object* v___x_1800_; 
v_a_1797_ = lean_ctor_get(v___x_1796_, 0);
lean_inc(v_a_1797_);
lean_dec_ref_known(v___x_1796_, 1);
v___x_1798_ = ((size_t)1ULL);
v___x_1799_ = lean_usize_add(v_i_1784_, v___x_1798_);
v___x_1800_ = lean_array_uset(v_bs_x27_1795_, v_i_1784_, v_a_1797_);
v_i_1784_ = v___x_1799_;
v_bs_1785_ = v___x_1800_;
goto _start;
}
else
{
lean_object* v_a_1802_; lean_object* v___x_1804_; uint8_t v_isShared_1805_; uint8_t v_isSharedCheck_1809_; 
lean_dec_ref(v_bs_x27_1795_);
v_a_1802_ = lean_ctor_get(v___x_1796_, 0);
v_isSharedCheck_1809_ = !lean_is_exclusive(v___x_1796_);
if (v_isSharedCheck_1809_ == 0)
{
v___x_1804_ = v___x_1796_;
v_isShared_1805_ = v_isSharedCheck_1809_;
goto v_resetjp_1803_;
}
else
{
lean_inc(v_a_1802_);
lean_dec(v___x_1796_);
v___x_1804_ = lean_box(0);
v_isShared_1805_ = v_isSharedCheck_1809_;
goto v_resetjp_1803_;
}
v_resetjp_1803_:
{
lean_object* v___x_1807_; 
if (v_isShared_1805_ == 0)
{
v___x_1807_ = v___x_1804_;
goto v_reusejp_1806_;
}
else
{
lean_object* v_reuseFailAlloc_1808_; 
v_reuseFailAlloc_1808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1808_, 0, v_a_1802_);
v___x_1807_ = v_reuseFailAlloc_1808_;
goto v_reusejp_1806_;
}
v_reusejp_1806_:
{
return v___x_1807_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__3___boxed(lean_object* v_sz_1810_, lean_object* v_i_1811_, lean_object* v_bs_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_){
_start:
{
size_t v_sz_boxed_1818_; size_t v_i_boxed_1819_; lean_object* v_res_1820_; 
v_sz_boxed_1818_ = lean_unbox_usize(v_sz_1810_);
lean_dec(v_sz_1810_);
v_i_boxed_1819_ = lean_unbox_usize(v_i_1811_);
lean_dec(v_i_1811_);
v_res_1820_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__3(v_sz_boxed_1818_, v_i_boxed_1819_, v_bs_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_);
lean_dec(v___y_1816_);
lean_dec_ref(v___y_1815_);
lean_dec(v___y_1814_);
lean_dec_ref(v___y_1813_);
return v_res_1820_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__2___redArg(size_t v_sz_1821_, size_t v_i_1822_, lean_object* v_bs_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_){
_start:
{
uint8_t v___x_1829_; 
v___x_1829_ = lean_usize_dec_lt(v_i_1822_, v_sz_1821_);
if (v___x_1829_ == 0)
{
lean_object* v___x_1830_; 
v___x_1830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1830_, 0, v_bs_1823_);
return v___x_1830_;
}
else
{
lean_object* v_v_1831_; lean_object* v_fst_1832_; lean_object* v_snd_1833_; lean_object* v___x_1834_; lean_object* v_bs_x27_1835_; lean_object* v___x_1836_; 
v_v_1831_ = lean_array_uget_borrowed(v_bs_1823_, v_i_1822_);
v_fst_1832_ = lean_ctor_get(v_v_1831_, 0);
lean_inc(v_fst_1832_);
v_snd_1833_ = lean_ctor_get(v_v_1831_, 1);
lean_inc(v_snd_1833_);
v___x_1834_ = lean_unsigned_to_nat(0u);
v_bs_x27_1835_ = lean_array_uset(v_bs_1823_, v_i_1822_, v___x_1834_);
v___x_1836_ = l_Lean_Meta_mkEq(v_snd_1833_, v_fst_1832_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_);
if (lean_obj_tag(v___x_1836_) == 0)
{
lean_object* v_a_1837_; size_t v___x_1838_; size_t v___x_1839_; lean_object* v___x_1840_; 
v_a_1837_ = lean_ctor_get(v___x_1836_, 0);
lean_inc(v_a_1837_);
lean_dec_ref_known(v___x_1836_, 1);
v___x_1838_ = ((size_t)1ULL);
v___x_1839_ = lean_usize_add(v_i_1822_, v___x_1838_);
v___x_1840_ = lean_array_uset(v_bs_x27_1835_, v_i_1822_, v_a_1837_);
v_i_1822_ = v___x_1839_;
v_bs_1823_ = v___x_1840_;
goto _start;
}
else
{
lean_object* v_a_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1849_; 
lean_dec_ref(v_bs_x27_1835_);
v_a_1842_ = lean_ctor_get(v___x_1836_, 0);
v_isSharedCheck_1849_ = !lean_is_exclusive(v___x_1836_);
if (v_isSharedCheck_1849_ == 0)
{
v___x_1844_ = v___x_1836_;
v_isShared_1845_ = v_isSharedCheck_1849_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_a_1842_);
lean_dec(v___x_1836_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1849_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
lean_object* v___x_1847_; 
if (v_isShared_1845_ == 0)
{
v___x_1847_ = v___x_1844_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v_a_1842_);
v___x_1847_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
return v___x_1847_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__2___redArg___boxed(lean_object* v_sz_1850_, lean_object* v_i_1851_, lean_object* v_bs_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_){
_start:
{
size_t v_sz_boxed_1858_; size_t v_i_boxed_1859_; lean_object* v_res_1860_; 
v_sz_boxed_1858_ = lean_unbox_usize(v_sz_1850_);
lean_dec(v_sz_1850_);
v_i_boxed_1859_ = lean_unbox_usize(v_i_1851_);
lean_dec(v_i_1851_);
v_res_1860_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__2___redArg(v_sz_boxed_1858_, v_i_boxed_1859_, v_bs_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_);
lean_dec(v___y_1856_);
lean_dec_ref(v___y_1855_);
lean_dec(v___y_1854_);
lean_dec_ref(v___y_1853_);
return v_res_1860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1___lam__0(lean_object* v_revertArgs_1861_, lean_object* v_u_1862_, lean_object* v_00_u03c3s_1863_, lean_object* v_hypName_1864_, uint8_t v___x_1865_, lean_object* v_hyps_1866_, lean_object* v_ss_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_){
_start:
{
lean_object* v___x_1877_; size_t v_sz_1878_; size_t v___x_1879_; lean_object* v___x_1880_; 
v___x_1877_ = l_Array_zip___redArg(v_revertArgs_1861_, v_ss_1867_);
v_sz_1878_ = lean_array_size(v___x_1877_);
v___x_1879_ = ((size_t)0ULL);
v___x_1880_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__2___redArg(v_sz_1878_, v___x_1879_, v___x_1877_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_);
if (lean_obj_tag(v___x_1880_) == 0)
{
lean_object* v_a_1881_; lean_object* v_eqs_1882_; lean_object* v_00_u03c6_1883_; lean_object* v_00_u03c6_1884_; lean_object* v___x_1885_; 
v_a_1881_ = lean_ctor_get(v___x_1880_, 0);
lean_inc(v_a_1881_);
lean_dec_ref_known(v___x_1880_, 1);
v_eqs_1882_ = lean_array_to_list(v_a_1881_);
v_00_u03c6_1883_ = l_Lean_mkAndN(v_eqs_1882_);
v_00_u03c6_1884_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure(v_u_1862_, v_00_u03c3s_1863_, v_00_u03c6_1883_);
lean_inc(v_hypName_1864_);
v___x_1885_ = l_Lean_Core_mkFreshUserName(v_hypName_1864_, v___y_1874_, v___y_1875_);
if (lean_obj_tag(v___x_1885_) == 0)
{
lean_object* v_a_1886_; uint8_t v___x_1887_; uint8_t v___x_1888_; lean_object* v___x_1889_; 
v_a_1886_ = lean_ctor_get(v___x_1885_, 0);
lean_inc(v_a_1886_);
lean_dec_ref_known(v___x_1885_, 1);
v___x_1887_ = 1;
v___x_1888_ = 1;
v___x_1889_ = l_Lean_Meta_mkLambdaFVars(v_ss_1867_, v_00_u03c6_1884_, v___x_1865_, v___x_1887_, v___x_1865_, v___x_1887_, v___x_1888_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_);
if (lean_obj_tag(v___x_1889_) == 0)
{
lean_object* v_a_1890_; lean_object* v___x_1891_; lean_object* v_00_u03c6_1892_; lean_object* v___x_1893_; 
v_a_1890_ = lean_ctor_get(v___x_1889_, 0);
lean_inc(v_a_1890_);
lean_dec_ref_known(v___x_1889_, 1);
v___x_1891_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1891_, 0, v_hypName_1864_);
lean_ctor_set(v___x_1891_, 1, v_a_1886_);
lean_ctor_set(v___x_1891_, 2, v_a_1890_);
v_00_u03c6_1892_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_1891_);
v___x_1893_ = l_Lean_Meta_mkLambdaFVars(v_ss_1867_, v_hyps_1866_, v___x_1865_, v___x_1887_, v___x_1865_, v___x_1887_, v___x_1888_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_);
if (lean_obj_tag(v___x_1893_) == 0)
{
lean_object* v_a_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1902_; 
v_a_1894_ = lean_ctor_get(v___x_1893_, 0);
v_isSharedCheck_1902_ = !lean_is_exclusive(v___x_1893_);
if (v_isSharedCheck_1902_ == 0)
{
v___x_1896_ = v___x_1893_;
v_isShared_1897_ = v_isSharedCheck_1902_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_a_1894_);
lean_dec(v___x_1893_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1902_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v___x_1898_; lean_object* v___x_1900_; 
v___x_1898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1898_, 0, v_a_1894_);
lean_ctor_set(v___x_1898_, 1, v_00_u03c6_1892_);
if (v_isShared_1897_ == 0)
{
lean_ctor_set(v___x_1896_, 0, v___x_1898_);
v___x_1900_ = v___x_1896_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v___x_1898_);
v___x_1900_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
return v___x_1900_;
}
}
}
else
{
lean_object* v_a_1903_; lean_object* v___x_1905_; uint8_t v_isShared_1906_; uint8_t v_isSharedCheck_1910_; 
lean_dec_ref(v_00_u03c6_1892_);
v_a_1903_ = lean_ctor_get(v___x_1893_, 0);
v_isSharedCheck_1910_ = !lean_is_exclusive(v___x_1893_);
if (v_isSharedCheck_1910_ == 0)
{
v___x_1905_ = v___x_1893_;
v_isShared_1906_ = v_isSharedCheck_1910_;
goto v_resetjp_1904_;
}
else
{
lean_inc(v_a_1903_);
lean_dec(v___x_1893_);
v___x_1905_ = lean_box(0);
v_isShared_1906_ = v_isSharedCheck_1910_;
goto v_resetjp_1904_;
}
v_resetjp_1904_:
{
lean_object* v___x_1908_; 
if (v_isShared_1906_ == 0)
{
v___x_1908_ = v___x_1905_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1909_; 
v_reuseFailAlloc_1909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1909_, 0, v_a_1903_);
v___x_1908_ = v_reuseFailAlloc_1909_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
return v___x_1908_;
}
}
}
}
else
{
lean_object* v_a_1911_; lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_1918_; 
lean_dec(v_a_1886_);
lean_dec_ref(v_hyps_1866_);
lean_dec(v_hypName_1864_);
v_a_1911_ = lean_ctor_get(v___x_1889_, 0);
v_isSharedCheck_1918_ = !lean_is_exclusive(v___x_1889_);
if (v_isSharedCheck_1918_ == 0)
{
v___x_1913_ = v___x_1889_;
v_isShared_1914_ = v_isSharedCheck_1918_;
goto v_resetjp_1912_;
}
else
{
lean_inc(v_a_1911_);
lean_dec(v___x_1889_);
v___x_1913_ = lean_box(0);
v_isShared_1914_ = v_isSharedCheck_1918_;
goto v_resetjp_1912_;
}
v_resetjp_1912_:
{
lean_object* v___x_1916_; 
if (v_isShared_1914_ == 0)
{
v___x_1916_ = v___x_1913_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v_a_1911_);
v___x_1916_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
return v___x_1916_;
}
}
}
}
else
{
lean_object* v_a_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1926_; 
lean_dec_ref(v_00_u03c6_1884_);
lean_dec_ref(v_hyps_1866_);
lean_dec(v_hypName_1864_);
v_a_1919_ = lean_ctor_get(v___x_1885_, 0);
v_isSharedCheck_1926_ = !lean_is_exclusive(v___x_1885_);
if (v_isSharedCheck_1926_ == 0)
{
v___x_1921_ = v___x_1885_;
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_a_1919_);
lean_dec(v___x_1885_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
lean_object* v___x_1924_; 
if (v_isShared_1922_ == 0)
{
v___x_1924_ = v___x_1921_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v_a_1919_);
v___x_1924_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
return v___x_1924_;
}
}
}
}
else
{
lean_object* v_a_1927_; lean_object* v___x_1929_; uint8_t v_isShared_1930_; uint8_t v_isSharedCheck_1934_; 
lean_dec_ref(v_hyps_1866_);
lean_dec(v_hypName_1864_);
lean_dec_ref(v_00_u03c3s_1863_);
lean_dec(v_u_1862_);
v_a_1927_ = lean_ctor_get(v___x_1880_, 0);
v_isSharedCheck_1934_ = !lean_is_exclusive(v___x_1880_);
if (v_isSharedCheck_1934_ == 0)
{
v___x_1929_ = v___x_1880_;
v_isShared_1930_ = v_isSharedCheck_1934_;
goto v_resetjp_1928_;
}
else
{
lean_inc(v_a_1927_);
lean_dec(v___x_1880_);
v___x_1929_ = lean_box(0);
v_isShared_1930_ = v_isSharedCheck_1934_;
goto v_resetjp_1928_;
}
v_resetjp_1928_:
{
lean_object* v___x_1932_; 
if (v_isShared_1930_ == 0)
{
v___x_1932_ = v___x_1929_;
goto v_reusejp_1931_;
}
else
{
lean_object* v_reuseFailAlloc_1933_; 
v_reuseFailAlloc_1933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1933_, 0, v_a_1927_);
v___x_1932_ = v_reuseFailAlloc_1933_;
goto v_reusejp_1931_;
}
v_reusejp_1931_:
{
return v___x_1932_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1___lam__0___boxed(lean_object* v_revertArgs_1935_, lean_object* v_u_1936_, lean_object* v_00_u03c3s_1937_, lean_object* v_hypName_1938_, lean_object* v___x_1939_, lean_object* v_hyps_1940_, lean_object* v_ss_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_){
_start:
{
uint8_t v___x_18137__boxed_1951_; lean_object* v_res_1952_; 
v___x_18137__boxed_1951_ = lean_unbox(v___x_1939_);
v_res_1952_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1___lam__0(v_revertArgs_1935_, v_u_1936_, v_00_u03c3s_1937_, v_hypName_1938_, v___x_18137__boxed_1951_, v_hyps_1940_, v_ss_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_);
lean_dec(v___y_1949_);
lean_dec_ref(v___y_1948_);
lean_dec(v___y_1947_);
lean_dec_ref(v___y_1946_);
lean_dec(v___y_1945_);
lean_dec_ref(v___y_1944_);
lean_dec(v___y_1943_);
lean_dec_ref(v___y_1942_);
lean_dec_ref(v_ss_1941_);
lean_dec_ref(v_revertArgs_1935_);
return v_res_1952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1(lean_object* v_goal_1953_, lean_object* v_n_1954_, lean_object* v_hypName_1955_, lean_object* v_k_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_){
_start:
{
lean_object* v___x_1966_; uint8_t v___x_1967_; 
v___x_1966_ = lean_unsigned_to_nat(0u);
v___x_1967_ = lean_nat_dec_eq(v_n_1954_, v___x_1966_);
if (v___x_1967_ == 0)
{
lean_object* v_u_1968_; lean_object* v_00_u03c3s_1969_; lean_object* v_hyps_1970_; lean_object* v_target_1971_; lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_2125_; 
v_u_1968_ = lean_ctor_get(v_goal_1953_, 0);
v_00_u03c3s_1969_ = lean_ctor_get(v_goal_1953_, 1);
v_hyps_1970_ = lean_ctor_get(v_goal_1953_, 2);
v_target_1971_ = lean_ctor_get(v_goal_1953_, 3);
v_isSharedCheck_2125_ = !lean_is_exclusive(v_goal_1953_);
if (v_isSharedCheck_2125_ == 0)
{
v___x_1973_ = v_goal_1953_;
v_isShared_1974_ = v_isSharedCheck_2125_;
goto v_resetjp_1972_;
}
else
{
lean_inc(v_target_1971_);
lean_inc(v_hyps_1970_);
lean_inc(v_00_u03c3s_1969_);
lean_inc(v_u_1968_);
lean_dec(v_goal_1953_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_2125_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
lean_object* v_T_1975_; lean_object* v_f_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v_a_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v_revertArgs_1983_; lean_object* v___y_1985_; lean_object* v___y_1986_; lean_object* v___y_1987_; lean_object* v___y_1988_; lean_object* v___y_1989_; lean_object* v___y_1990_; lean_object* v___y_1991_; lean_object* v___y_1992_; lean_object* v___y_1993_; lean_object* v___y_1994_; lean_object* v___y_1995_; lean_object* v___y_1996_; lean_object* v___x_2035_; lean_object* v___f_2036_; lean_object* v___y_2038_; lean_object* v___y_2039_; lean_object* v___y_2040_; lean_object* v___y_2041_; lean_object* v___y_2042_; lean_object* v___y_2043_; lean_object* v___y_2044_; lean_object* v___y_2045_; lean_object* v___x_2099_; uint8_t v___x_2100_; 
v_T_1975_ = l_Lean_Expr_consumeMData(v_target_1971_);
v_f_1976_ = l_Lean_Expr_getAppFn(v_T_1975_);
v___x_1977_ = l_Lean_Expr_getAppNumArgs(v_T_1975_);
v___x_1978_ = lean_mk_empty_array_with_capacity(v___x_1977_);
lean_dec(v___x_1977_);
lean_inc_ref(v_T_1975_);
v_a_1979_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_T_1975_, v___x_1978_);
lean_inc(v_n_1954_);
lean_inc_ref(v_a_1979_);
v___x_1980_ = l_Array_toSubarray___redArg(v_a_1979_, v___x_1966_, v_n_1954_);
v___x_1981_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__1));
v___x_1982_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__1___redArg(v___x_1980_, v___x_1981_);
v_revertArgs_1983_ = l_Array_reverse___redArg(v___x_1982_);
v___x_2035_ = lean_box(v___x_1967_);
lean_inc_ref(v_hyps_1970_);
lean_inc_ref(v_00_u03c3s_1969_);
lean_inc(v_u_1968_);
lean_inc_ref(v_revertArgs_1983_);
v___f_2036_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1___lam__0___boxed), 16, 6);
lean_closure_set(v___f_2036_, 0, v_revertArgs_1983_);
lean_closure_set(v___f_2036_, 1, v_u_1968_);
lean_closure_set(v___f_2036_, 2, v_00_u03c3s_1969_);
lean_closure_set(v___f_2036_, 3, v_hypName_1955_);
lean_closure_set(v___f_2036_, 4, v___x_2035_);
lean_closure_set(v___f_2036_, 5, v_hyps_1970_);
v___x_2099_ = lean_array_get_size(v_revertArgs_1983_);
v___x_2100_ = lean_nat_dec_eq(v___x_2099_, v_n_1954_);
if (v___x_2100_ == 0)
{
lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v_a_2117_; lean_object* v___x_2119_; uint8_t v_isShared_2120_; uint8_t v_isSharedCheck_2124_; 
lean_dec_ref(v___f_2036_);
lean_dec_ref(v_revertArgs_1983_);
lean_dec_ref(v_a_1979_);
lean_dec_ref(v_f_1976_);
lean_del_object(v___x_1973_);
lean_dec_ref(v_target_1971_);
lean_dec_ref(v_hyps_1970_);
lean_dec_ref(v_00_u03c3s_1969_);
lean_dec(v_u_1968_);
lean_dec_ref(v_k_1956_);
v___x_2101_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__3, &l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__3_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__3);
v___x_2102_ = l_Nat_reprFast(v_n_1954_);
v___x_2103_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2103_, 0, v___x_2102_);
v___x_2104_ = l_Lean_MessageData_ofFormat(v___x_2103_);
v___x_2105_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2105_, 0, v___x_2101_);
lean_ctor_set(v___x_2105_, 1, v___x_2104_);
v___x_2106_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__5, &l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__5_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__5);
v___x_2107_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2107_, 0, v___x_2105_);
lean_ctor_set(v___x_2107_, 1, v___x_2106_);
v___x_2108_ = l_Lean_MessageData_ofExpr(v_T_1975_);
v___x_2109_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2109_, 0, v___x_2107_);
lean_ctor_set(v___x_2109_, 1, v___x_2108_);
v___x_2110_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__7, &l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__7_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__7);
v___x_2111_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2111_, 0, v___x_2109_);
lean_ctor_set(v___x_2111_, 1, v___x_2110_);
v___x_2112_ = l_Nat_reprFast(v___x_2099_);
v___x_2113_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2113_, 0, v___x_2112_);
v___x_2114_ = l_Lean_MessageData_ofFormat(v___x_2113_);
v___x_2115_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2115_, 0, v___x_2111_);
lean_ctor_set(v___x_2115_, 1, v___x_2114_);
v___x_2116_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__8___redArg(v___x_2115_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_);
v_a_2117_ = lean_ctor_get(v___x_2116_, 0);
v_isSharedCheck_2124_ = !lean_is_exclusive(v___x_2116_);
if (v_isSharedCheck_2124_ == 0)
{
v___x_2119_ = v___x_2116_;
v_isShared_2120_ = v_isSharedCheck_2124_;
goto v_resetjp_2118_;
}
else
{
lean_inc(v_a_2117_);
lean_dec(v___x_2116_);
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
else
{
lean_dec_ref(v_T_1975_);
v___y_2038_ = v___y_1957_;
v___y_2039_ = v___y_1958_;
v___y_2040_ = v___y_1959_;
v___y_2041_ = v___y_1960_;
v___y_2042_ = v___y_1961_;
v___y_2043_ = v___y_1962_;
v___y_2044_ = v___y_1963_;
v___y_2045_ = v___y_1964_;
goto v___jp_2037_;
}
v___jp_1984_:
{
lean_object* v___x_1997_; 
v___x_1997_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v___y_1989_, v___y_1988_);
if (lean_obj_tag(v___x_1997_) == 0)
{
lean_object* v_a_1998_; lean_object* v_H_1999_; lean_object* v___x_2000_; lean_object* v_fst_2001_; lean_object* v_snd_2002_; lean_object* v___x_2004_; uint8_t v_isShared_2005_; uint8_t v_isSharedCheck_2034_; 
v_a_1998_ = lean_ctor_get(v___x_1997_, 0);
lean_inc(v_a_1998_);
lean_dec_ref_known(v___x_1997_, 1);
lean_inc_ref_n(v___y_1996_, 2);
v_H_1999_ = l_Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps(v___y_1996_, v_a_1998_);
lean_inc(v_u_1968_);
v___x_2000_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd(v_u_1968_, v___y_1996_, v_H_1999_, v___y_1985_);
v_fst_2001_ = lean_ctor_get(v___x_2000_, 0);
v_snd_2002_ = lean_ctor_get(v___x_2000_, 1);
v_isSharedCheck_2034_ = !lean_is_exclusive(v___x_2000_);
if (v_isSharedCheck_2034_ == 0)
{
v___x_2004_ = v___x_2000_;
v_isShared_2005_ = v_isSharedCheck_2034_;
goto v_resetjp_2003_;
}
else
{
lean_inc(v_snd_2002_);
lean_inc(v_fst_2001_);
lean_dec(v___x_2000_);
v___x_2004_ = lean_box(0);
v_isShared_2005_ = v_isSharedCheck_2034_;
goto v_resetjp_2003_;
}
v_resetjp_2003_:
{
lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v_goal_x27_2011_; 
v___x_2006_ = lean_array_get_size(v_a_1979_);
v___x_2007_ = l_Array_toSubarray___redArg(v_a_1979_, v_n_1954_, v___x_2006_);
v___x_2008_ = l_Subarray_copy___redArg(v___x_2007_);
v___x_2009_ = l_Lean_mkAppRev(v_f_1976_, v___x_2008_);
lean_dec_ref(v___x_2008_);
lean_inc(v_fst_2001_);
lean_inc(v_u_1968_);
if (v_isShared_1974_ == 0)
{
lean_ctor_set(v___x_1973_, 3, v___x_2009_);
lean_ctor_set(v___x_1973_, 2, v_fst_2001_);
lean_ctor_set(v___x_1973_, 1, v___y_1996_);
v_goal_x27_2011_ = v___x_1973_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v_u_1968_);
lean_ctor_set(v_reuseFailAlloc_2033_, 1, v___y_1996_);
lean_ctor_set(v_reuseFailAlloc_2033_, 2, v_fst_2001_);
lean_ctor_set(v_reuseFailAlloc_2033_, 3, v___x_2009_);
v_goal_x27_2011_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
lean_object* v___x_2012_; 
lean_inc(v___y_1986_);
lean_inc_ref(v___y_1991_);
lean_inc(v___y_1988_);
lean_inc_ref(v___y_1994_);
lean_inc(v___y_1987_);
lean_inc_ref(v___y_1992_);
lean_inc(v___y_1990_);
lean_inc_ref(v___y_1995_);
v___x_2012_ = lean_apply_10(v_k_1956_, v_goal_x27_2011_, v___y_1995_, v___y_1990_, v___y_1992_, v___y_1987_, v___y_1994_, v___y_1988_, v___y_1991_, v___y_1986_, lean_box(0));
if (lean_obj_tag(v___x_2012_) == 0)
{
lean_object* v_a_2013_; lean_object* v___x_2014_; 
v_a_2013_ = lean_ctor_get(v___x_2012_, 0);
lean_inc(v_a_2013_);
lean_dec_ref_known(v___x_2012_, 1);
lean_inc(v___y_1986_);
lean_inc_ref(v___y_1991_);
lean_inc(v___y_1988_);
lean_inc_ref(v___y_1994_);
lean_inc_ref(v___y_1993_);
v___x_2014_ = lean_infer_type(v___y_1993_, v___y_1994_, v___y_1988_, v___y_1991_, v___y_1986_);
if (lean_obj_tag(v___x_2014_) == 0)
{
lean_object* v_a_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2032_; 
v_a_2015_ = lean_ctor_get(v___x_2014_, 0);
v_isSharedCheck_2032_ = !lean_is_exclusive(v___x_2014_);
if (v_isSharedCheck_2032_ == 0)
{
v___x_2017_ = v___x_2014_;
v_isShared_2018_ = v_isSharedCheck_2032_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_a_2015_);
lean_dec(v___x_2014_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2032_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2022_; 
v___x_2019_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__12___closed__1));
v___x_2020_ = lean_box(0);
if (v_isShared_2005_ == 0)
{
lean_ctor_set_tag(v___x_2004_, 1);
lean_ctor_set(v___x_2004_, 1, v___x_2020_);
lean_ctor_set(v___x_2004_, 0, v_u_1968_);
v___x_2022_ = v___x_2004_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v_u_1968_);
lean_ctor_set(v_reuseFailAlloc_2031_, 1, v___x_2020_);
v___x_2022_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v_prf_2027_; lean_object* v___x_2029_; 
v___x_2023_ = l_Lean_mkConst(v___x_2019_, v___x_2022_);
v___x_2024_ = l_Lean_mkAppN(v_fst_2001_, v_revertArgs_1983_);
v___x_2025_ = l_Lean_mkAppN(v_snd_2002_, v_revertArgs_1983_);
v___x_2026_ = l_Lean_mkAppN(v_a_2013_, v_revertArgs_1983_);
lean_dec_ref(v_revertArgs_1983_);
v_prf_2027_ = l_Lean_mkApp8(v___x_2023_, v_00_u03c3s_1969_, v_a_2015_, v_hyps_1970_, v___x_2024_, v_target_1971_, v___y_1993_, v___x_2025_, v___x_2026_);
if (v_isShared_2018_ == 0)
{
lean_ctor_set(v___x_2017_, 0, v_prf_2027_);
v___x_2029_ = v___x_2017_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2030_; 
v_reuseFailAlloc_2030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2030_, 0, v_prf_2027_);
v___x_2029_ = v_reuseFailAlloc_2030_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
return v___x_2029_;
}
}
}
}
else
{
lean_dec(v_a_2013_);
lean_del_object(v___x_2004_);
lean_dec(v_snd_2002_);
lean_dec(v_fst_2001_);
lean_dec_ref(v___y_1993_);
lean_dec_ref(v_revertArgs_1983_);
lean_dec_ref(v_target_1971_);
lean_dec_ref(v_hyps_1970_);
lean_dec_ref(v_00_u03c3s_1969_);
lean_dec(v_u_1968_);
return v___x_2014_;
}
}
else
{
lean_del_object(v___x_2004_);
lean_dec(v_snd_2002_);
lean_dec(v_fst_2001_);
lean_dec_ref(v___y_1993_);
lean_dec_ref(v_revertArgs_1983_);
lean_dec_ref(v_target_1971_);
lean_dec_ref(v_hyps_1970_);
lean_dec_ref(v_00_u03c3s_1969_);
lean_dec(v_u_1968_);
return v___x_2012_;
}
}
}
}
else
{
lean_dec_ref(v___y_1996_);
lean_dec_ref(v___y_1993_);
lean_dec_ref(v___y_1985_);
lean_dec_ref(v_revertArgs_1983_);
lean_dec_ref(v_a_1979_);
lean_dec_ref(v_f_1976_);
lean_del_object(v___x_1973_);
lean_dec_ref(v_target_1971_);
lean_dec_ref(v_hyps_1970_);
lean_dec_ref(v_00_u03c3s_1969_);
lean_dec(v_u_1968_);
lean_dec_ref(v_k_1956_);
lean_dec(v_n_1954_);
return v___x_1997_;
}
}
v___jp_2037_:
{
size_t v_sz_2046_; size_t v___x_2047_; lean_object* v___x_2048_; 
v_sz_2046_ = lean_array_size(v_revertArgs_1983_);
v___x_2047_ = ((size_t)0ULL);
lean_inc_ref(v_revertArgs_1983_);
v___x_2048_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__3(v_sz_2046_, v___x_2047_, v_revertArgs_1983_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_);
if (lean_obj_tag(v___x_2048_) == 0)
{
lean_object* v_a_2049_; size_t v_sz_2050_; lean_object* v___x_2051_; 
v_a_2049_ = lean_ctor_get(v___x_2048_, 0);
lean_inc_n(v_a_2049_, 2);
lean_dec_ref_known(v___x_2048_, 1);
v_sz_2050_ = lean_array_size(v_a_2049_);
v___x_2051_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__4___redArg(v_sz_2050_, v___x_2047_, v_a_2049_, v___y_2044_, v___y_2045_);
if (lean_obj_tag(v___x_2051_) == 0)
{
lean_object* v_a_2052_; uint8_t v___x_2053_; lean_object* v___x_2054_; 
v_a_2052_ = lean_ctor_get(v___x_2051_, 0);
lean_inc(v_a_2052_);
lean_dec_ref_known(v___x_2051_, 1);
v___x_2053_ = 0;
v___x_2054_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5(v_a_2052_, v___f_2036_, v___x_2053_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_);
if (lean_obj_tag(v___x_2054_) == 0)
{
lean_object* v_a_2055_; lean_object* v_fst_2056_; lean_object* v_snd_2057_; lean_object* v___x_2058_; 
v_a_2055_ = lean_ctor_get(v___x_2054_, 0);
lean_inc(v_a_2055_);
lean_dec_ref_known(v___x_2054_, 1);
v_fst_2056_ = lean_ctor_get(v_a_2055_, 0);
lean_inc(v_fst_2056_);
v_snd_2057_ = lean_ctor_get(v_a_2055_, 1);
lean_inc(v_snd_2057_);
lean_dec(v_a_2055_);
lean_inc_ref(v_revertArgs_1983_);
v___x_2058_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__6(v_sz_2046_, v___x_2047_, v_revertArgs_1983_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_);
if (lean_obj_tag(v___x_2058_) == 0)
{
lean_object* v_a_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; 
v_a_2059_ = lean_ctor_get(v___x_2058_, 0);
lean_inc(v_a_2059_);
lean_dec_ref_known(v___x_2058_, 1);
v___x_2060_ = lean_array_to_list(v_a_2059_);
v___x_2061_ = l_Lean_Meta_mkAndIntroN(v___x_2060_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_);
if (lean_obj_tag(v___x_2061_) == 0)
{
lean_object* v_a_2062_; lean_object* v___x_2063_; uint8_t v___x_2064_; 
v_a_2062_ = lean_ctor_get(v___x_2061_, 0);
lean_inc(v_a_2062_);
lean_dec_ref_known(v___x_2061_, 1);
v___x_2063_ = lean_array_get_size(v_a_2049_);
v___x_2064_ = lean_nat_dec_lt(v___x_1966_, v___x_2063_);
if (v___x_2064_ == 0)
{
lean_dec(v_a_2049_);
lean_inc_ref(v_00_u03c3s_1969_);
v___y_1985_ = v_snd_2057_;
v___y_1986_ = v___y_2045_;
v___y_1987_ = v___y_2041_;
v___y_1988_ = v___y_2043_;
v___y_1989_ = v_fst_2056_;
v___y_1990_ = v___y_2039_;
v___y_1991_ = v___y_2044_;
v___y_1992_ = v___y_2040_;
v___y_1993_ = v_a_2062_;
v___y_1994_ = v___y_2042_;
v___y_1995_ = v___y_2038_;
v___y_1996_ = v_00_u03c3s_1969_;
goto v___jp_1984_;
}
else
{
size_t v___x_2065_; lean_object* v___x_2066_; 
v___x_2065_ = lean_usize_of_nat(v___x_2063_);
lean_inc_ref(v_00_u03c3s_1969_);
lean_inc(v_u_1968_);
v___x_2066_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__7(v_u_1968_, v_a_2049_, v___x_2065_, v___x_2047_, v_00_u03c3s_1969_);
lean_dec(v_a_2049_);
v___y_1985_ = v_snd_2057_;
v___y_1986_ = v___y_2045_;
v___y_1987_ = v___y_2041_;
v___y_1988_ = v___y_2043_;
v___y_1989_ = v_fst_2056_;
v___y_1990_ = v___y_2039_;
v___y_1991_ = v___y_2044_;
v___y_1992_ = v___y_2040_;
v___y_1993_ = v_a_2062_;
v___y_1994_ = v___y_2042_;
v___y_1995_ = v___y_2038_;
v___y_1996_ = v___x_2066_;
goto v___jp_1984_;
}
}
else
{
lean_dec(v_snd_2057_);
lean_dec(v_fst_2056_);
lean_dec(v_a_2049_);
lean_dec_ref(v_revertArgs_1983_);
lean_dec_ref(v_a_1979_);
lean_dec_ref(v_f_1976_);
lean_del_object(v___x_1973_);
lean_dec_ref(v_target_1971_);
lean_dec_ref(v_hyps_1970_);
lean_dec_ref(v_00_u03c3s_1969_);
lean_dec(v_u_1968_);
lean_dec_ref(v_k_1956_);
lean_dec(v_n_1954_);
return v___x_2061_;
}
}
else
{
lean_object* v_a_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2074_; 
lean_dec(v_snd_2057_);
lean_dec(v_fst_2056_);
lean_dec(v_a_2049_);
lean_dec_ref(v_revertArgs_1983_);
lean_dec_ref(v_a_1979_);
lean_dec_ref(v_f_1976_);
lean_del_object(v___x_1973_);
lean_dec_ref(v_target_1971_);
lean_dec_ref(v_hyps_1970_);
lean_dec_ref(v_00_u03c3s_1969_);
lean_dec(v_u_1968_);
lean_dec_ref(v_k_1956_);
lean_dec(v_n_1954_);
v_a_2067_ = lean_ctor_get(v___x_2058_, 0);
v_isSharedCheck_2074_ = !lean_is_exclusive(v___x_2058_);
if (v_isSharedCheck_2074_ == 0)
{
v___x_2069_ = v___x_2058_;
v_isShared_2070_ = v_isSharedCheck_2074_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_a_2067_);
lean_dec(v___x_2058_);
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
else
{
lean_object* v_a_2075_; lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2082_; 
lean_dec(v_a_2049_);
lean_dec_ref(v_revertArgs_1983_);
lean_dec_ref(v_a_1979_);
lean_dec_ref(v_f_1976_);
lean_del_object(v___x_1973_);
lean_dec_ref(v_target_1971_);
lean_dec_ref(v_hyps_1970_);
lean_dec_ref(v_00_u03c3s_1969_);
lean_dec(v_u_1968_);
lean_dec_ref(v_k_1956_);
lean_dec(v_n_1954_);
v_a_2075_ = lean_ctor_get(v___x_2054_, 0);
v_isSharedCheck_2082_ = !lean_is_exclusive(v___x_2054_);
if (v_isSharedCheck_2082_ == 0)
{
v___x_2077_ = v___x_2054_;
v_isShared_2078_ = v_isSharedCheck_2082_;
goto v_resetjp_2076_;
}
else
{
lean_inc(v_a_2075_);
lean_dec(v___x_2054_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2082_;
goto v_resetjp_2076_;
}
v_resetjp_2076_:
{
lean_object* v___x_2080_; 
if (v_isShared_2078_ == 0)
{
v___x_2080_ = v___x_2077_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v_a_2075_);
v___x_2080_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
return v___x_2080_;
}
}
}
}
else
{
lean_object* v_a_2083_; lean_object* v___x_2085_; uint8_t v_isShared_2086_; uint8_t v_isSharedCheck_2090_; 
lean_dec(v_a_2049_);
lean_dec_ref(v___f_2036_);
lean_dec_ref(v_revertArgs_1983_);
lean_dec_ref(v_a_1979_);
lean_dec_ref(v_f_1976_);
lean_del_object(v___x_1973_);
lean_dec_ref(v_target_1971_);
lean_dec_ref(v_hyps_1970_);
lean_dec_ref(v_00_u03c3s_1969_);
lean_dec(v_u_1968_);
lean_dec_ref(v_k_1956_);
lean_dec(v_n_1954_);
v_a_2083_ = lean_ctor_get(v___x_2051_, 0);
v_isSharedCheck_2090_ = !lean_is_exclusive(v___x_2051_);
if (v_isSharedCheck_2090_ == 0)
{
v___x_2085_ = v___x_2051_;
v_isShared_2086_ = v_isSharedCheck_2090_;
goto v_resetjp_2084_;
}
else
{
lean_inc(v_a_2083_);
lean_dec(v___x_2051_);
v___x_2085_ = lean_box(0);
v_isShared_2086_ = v_isSharedCheck_2090_;
goto v_resetjp_2084_;
}
v_resetjp_2084_:
{
lean_object* v___x_2088_; 
if (v_isShared_2086_ == 0)
{
v___x_2088_ = v___x_2085_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v_a_2083_);
v___x_2088_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
return v___x_2088_;
}
}
}
}
else
{
lean_object* v_a_2091_; lean_object* v___x_2093_; uint8_t v_isShared_2094_; uint8_t v_isSharedCheck_2098_; 
lean_dec_ref(v___f_2036_);
lean_dec_ref(v_revertArgs_1983_);
lean_dec_ref(v_a_1979_);
lean_dec_ref(v_f_1976_);
lean_del_object(v___x_1973_);
lean_dec_ref(v_target_1971_);
lean_dec_ref(v_hyps_1970_);
lean_dec_ref(v_00_u03c3s_1969_);
lean_dec(v_u_1968_);
lean_dec_ref(v_k_1956_);
lean_dec(v_n_1954_);
v_a_2091_ = lean_ctor_get(v___x_2048_, 0);
v_isSharedCheck_2098_ = !lean_is_exclusive(v___x_2048_);
if (v_isSharedCheck_2098_ == 0)
{
v___x_2093_ = v___x_2048_;
v_isShared_2094_ = v_isSharedCheck_2098_;
goto v_resetjp_2092_;
}
else
{
lean_inc(v_a_2091_);
lean_dec(v___x_2048_);
v___x_2093_ = lean_box(0);
v_isShared_2094_ = v_isSharedCheck_2098_;
goto v_resetjp_2092_;
}
v_resetjp_2092_:
{
lean_object* v___x_2096_; 
if (v_isShared_2094_ == 0)
{
v___x_2096_ = v___x_2093_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v_a_2091_);
v___x_2096_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
return v___x_2096_;
}
}
}
}
}
}
else
{
lean_object* v___x_2126_; 
lean_dec(v_hypName_1955_);
lean_dec(v_n_1954_);
lean_inc(v___y_1964_);
lean_inc_ref(v___y_1963_);
lean_inc(v___y_1962_);
lean_inc_ref(v___y_1961_);
lean_inc(v___y_1960_);
lean_inc_ref(v___y_1959_);
lean_inc(v___y_1958_);
lean_inc_ref(v___y_1957_);
v___x_2126_ = lean_apply_10(v_k_1956_, v_goal_1953_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_, lean_box(0));
return v___x_2126_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1___boxed(lean_object* v_goal_2127_, lean_object* v_n_2128_, lean_object* v_hypName_2129_, lean_object* v_k_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_){
_start:
{
lean_object* v_res_2140_; 
v_res_2140_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1(v_goal_2127_, v_n_2128_, v_hypName_2129_, v_k_2130_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_);
lean_dec(v___y_2138_);
lean_dec_ref(v___y_2137_);
lean_dec(v___y_2136_);
lean_dec_ref(v___y_2135_);
lean_dec(v___y_2134_);
lean_dec_ref(v___y_2133_);
lean_dec(v___y_2132_);
lean_dec_ref(v___y_2131_);
return v_res_2140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__1(lean_object* v___x_2144_, lean_object* v_snd_2145_, lean_object* v___y_2146_, lean_object* v_fst_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_){
_start:
{
lean_object* v___x_2157_; lean_object* v___f_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; 
v___x_2157_ = lean_st_mk_ref(v___x_2144_);
lean_inc(v___x_2157_);
v___f_2158_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__0___boxed), 11, 1);
lean_closure_set(v___f_2158_, 0, v___x_2157_);
v___x_2159_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__1___closed__1));
v___x_2160_ = l_Lean_Core_mkFreshUserName(v___x_2159_, v___y_2154_, v___y_2155_);
if (lean_obj_tag(v___x_2160_) == 0)
{
lean_object* v_a_2161_; lean_object* v___x_2162_; 
v_a_2161_ = lean_ctor_get(v___x_2160_, 0);
lean_inc(v_a_2161_);
lean_dec_ref_known(v___x_2160_, 1);
v___x_2162_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1(v_snd_2145_, v___y_2146_, v_a_2161_, v___f_2158_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_);
if (lean_obj_tag(v___x_2162_) == 0)
{
lean_object* v_a_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; 
v_a_2163_ = lean_ctor_get(v___x_2162_, 0);
lean_inc(v_a_2163_);
lean_dec_ref_known(v___x_2162_, 1);
v___x_2164_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2___redArg(v_fst_2147_, v_a_2163_, v___y_2153_);
lean_dec_ref(v___x_2164_);
v___x_2165_ = lean_st_ref_get(v___x_2157_);
lean_dec(v___x_2157_);
v___x_2166_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2165_, v___y_2149_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_);
return v___x_2166_;
}
else
{
lean_object* v_a_2167_; lean_object* v___x_2169_; uint8_t v_isShared_2170_; uint8_t v_isSharedCheck_2174_; 
lean_dec(v___x_2157_);
lean_dec(v_fst_2147_);
v_a_2167_ = lean_ctor_get(v___x_2162_, 0);
v_isSharedCheck_2174_ = !lean_is_exclusive(v___x_2162_);
if (v_isSharedCheck_2174_ == 0)
{
v___x_2169_ = v___x_2162_;
v_isShared_2170_ = v_isSharedCheck_2174_;
goto v_resetjp_2168_;
}
else
{
lean_inc(v_a_2167_);
lean_dec(v___x_2162_);
v___x_2169_ = lean_box(0);
v_isShared_2170_ = v_isSharedCheck_2174_;
goto v_resetjp_2168_;
}
v_resetjp_2168_:
{
lean_object* v___x_2172_; 
if (v_isShared_2170_ == 0)
{
v___x_2172_ = v___x_2169_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v_a_2167_);
v___x_2172_ = v_reuseFailAlloc_2173_;
goto v_reusejp_2171_;
}
v_reusejp_2171_:
{
return v___x_2172_;
}
}
}
}
else
{
lean_object* v_a_2175_; lean_object* v___x_2177_; uint8_t v_isShared_2178_; uint8_t v_isSharedCheck_2182_; 
lean_dec_ref(v___f_2158_);
lean_dec(v___x_2157_);
lean_dec(v_fst_2147_);
lean_dec(v___y_2146_);
lean_dec_ref(v_snd_2145_);
v_a_2175_ = lean_ctor_get(v___x_2160_, 0);
v_isSharedCheck_2182_ = !lean_is_exclusive(v___x_2160_);
if (v_isSharedCheck_2182_ == 0)
{
v___x_2177_ = v___x_2160_;
v_isShared_2178_ = v_isSharedCheck_2182_;
goto v_resetjp_2176_;
}
else
{
lean_inc(v_a_2175_);
lean_dec(v___x_2160_);
v___x_2177_ = lean_box(0);
v_isShared_2178_ = v_isSharedCheck_2182_;
goto v_resetjp_2176_;
}
v_resetjp_2176_:
{
lean_object* v___x_2180_; 
if (v_isShared_2178_ == 0)
{
v___x_2180_ = v___x_2177_;
goto v_reusejp_2179_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v_a_2175_);
v___x_2180_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2179_;
}
v_reusejp_2179_:
{
return v___x_2180_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__1___boxed(lean_object* v___x_2183_, lean_object* v_snd_2184_, lean_object* v___y_2185_, lean_object* v_fst_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_){
_start:
{
lean_object* v_res_2196_; 
v_res_2196_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__1(v___x_2183_, v_snd_2184_, v___y_2185_, v_fst_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_);
lean_dec(v___y_2194_);
lean_dec_ref(v___y_2193_);
lean_dec(v___y_2192_);
lean_dec_ref(v___y_2191_);
lean_dec(v___y_2190_);
lean_dec_ref(v___y_2189_);
lean_dec(v___y_2188_);
lean_dec_ref(v___y_2187_);
return v_res_2196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevert___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__4(lean_object* v_goal_2204_, lean_object* v_ref_2205_, lean_object* v_k_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_){
_start:
{
lean_object* v___x_2216_; 
lean_inc_ref(v_goal_2204_);
v___x_2216_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo(v_goal_2204_, v_ref_2205_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_);
if (lean_obj_tag(v___x_2216_) == 0)
{
lean_object* v_a_2217_; lean_object* v_focusHyp_2218_; lean_object* v_restHyps_2219_; lean_object* v_proof_2220_; lean_object* v___x_2221_; 
v_a_2217_ = lean_ctor_get(v___x_2216_, 0);
lean_inc(v_a_2217_);
lean_dec_ref_known(v___x_2216_, 1);
v_focusHyp_2218_ = lean_ctor_get(v_a_2217_, 0);
lean_inc_ref_n(v_focusHyp_2218_, 2);
v_restHyps_2219_ = lean_ctor_get(v_a_2217_, 1);
lean_inc_ref(v_restHyps_2219_);
v_proof_2220_ = lean_ctor_get(v_a_2217_, 2);
lean_inc_ref(v_proof_2220_);
lean_dec(v_a_2217_);
v___x_2221_ = l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(v_focusHyp_2218_);
if (lean_obj_tag(v___x_2221_) == 1)
{
lean_object* v_val_2222_; lean_object* v_u_2223_; lean_object* v_00_u03c3s_2224_; lean_object* v_hyps_2225_; lean_object* v_target_2226_; lean_object* v___x_2228_; uint8_t v_isShared_2229_; uint8_t v_isSharedCheck_2251_; 
v_val_2222_ = lean_ctor_get(v___x_2221_, 0);
lean_inc(v_val_2222_);
lean_dec_ref_known(v___x_2221_, 1);
v_u_2223_ = lean_ctor_get(v_goal_2204_, 0);
v_00_u03c3s_2224_ = lean_ctor_get(v_goal_2204_, 1);
v_hyps_2225_ = lean_ctor_get(v_goal_2204_, 2);
v_target_2226_ = lean_ctor_get(v_goal_2204_, 3);
v_isSharedCheck_2251_ = !lean_is_exclusive(v_goal_2204_);
if (v_isSharedCheck_2251_ == 0)
{
v___x_2228_ = v_goal_2204_;
v_isShared_2229_ = v_isSharedCheck_2251_;
goto v_resetjp_2227_;
}
else
{
lean_inc(v_target_2226_);
lean_inc(v_hyps_2225_);
lean_inc(v_00_u03c3s_2224_);
lean_inc(v_u_2223_);
lean_dec(v_goal_2204_);
v___x_2228_ = lean_box(0);
v_isShared_2229_ = v_isSharedCheck_2251_;
goto v_resetjp_2227_;
}
v_resetjp_2227_:
{
lean_object* v_p_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2237_; 
v_p_2230_ = lean_ctor_get(v_val_2222_, 2);
lean_inc_ref(v_p_2230_);
lean_dec(v_val_2222_);
v___x_2231_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__4));
v___x_2232_ = lean_box(0);
lean_inc(v_u_2223_);
v___x_2233_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2233_, 0, v_u_2223_);
lean_ctor_set(v___x_2233_, 1, v___x_2232_);
lean_inc_ref(v___x_2233_);
v___x_2234_ = l_Lean_mkConst(v___x_2231_, v___x_2233_);
lean_inc_ref(v_target_2226_);
lean_inc_ref_n(v_00_u03c3s_2224_, 2);
v___x_2235_ = l_Lean_mkApp3(v___x_2234_, v_00_u03c3s_2224_, v_p_2230_, v_target_2226_);
lean_inc_ref(v_restHyps_2219_);
if (v_isShared_2229_ == 0)
{
lean_ctor_set(v___x_2228_, 3, v___x_2235_);
lean_ctor_set(v___x_2228_, 2, v_restHyps_2219_);
v___x_2237_ = v___x_2228_;
goto v_reusejp_2236_;
}
else
{
lean_object* v_reuseFailAlloc_2250_; 
v_reuseFailAlloc_2250_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2250_, 0, v_u_2223_);
lean_ctor_set(v_reuseFailAlloc_2250_, 1, v_00_u03c3s_2224_);
lean_ctor_set(v_reuseFailAlloc_2250_, 2, v_restHyps_2219_);
lean_ctor_set(v_reuseFailAlloc_2250_, 3, v___x_2235_);
v___x_2237_ = v_reuseFailAlloc_2250_;
goto v_reusejp_2236_;
}
v_reusejp_2236_:
{
lean_object* v___x_2238_; 
lean_inc(v___y_2214_);
lean_inc_ref(v___y_2213_);
lean_inc(v___y_2212_);
lean_inc_ref(v___y_2211_);
lean_inc(v___y_2210_);
lean_inc_ref(v___y_2209_);
lean_inc(v___y_2208_);
lean_inc_ref(v___y_2207_);
v___x_2238_ = lean_apply_10(v_k_2206_, v___x_2237_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, lean_box(0));
if (lean_obj_tag(v___x_2238_) == 0)
{
lean_object* v_a_2239_; lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2249_; 
v_a_2239_ = lean_ctor_get(v___x_2238_, 0);
v_isSharedCheck_2249_ = !lean_is_exclusive(v___x_2238_);
if (v_isSharedCheck_2249_ == 0)
{
v___x_2241_ = v___x_2238_;
v_isShared_2242_ = v_isSharedCheck_2249_;
goto v_resetjp_2240_;
}
else
{
lean_inc(v_a_2239_);
lean_dec(v___x_2238_);
v___x_2241_ = lean_box(0);
v_isShared_2242_ = v_isSharedCheck_2249_;
goto v_resetjp_2240_;
}
v_resetjp_2240_:
{
lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v_prf_2245_; lean_object* v___x_2247_; 
v___x_2243_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__4___closed__0));
v___x_2244_ = l_Lean_mkConst(v___x_2243_, v___x_2233_);
v_prf_2245_ = l_Lean_mkApp7(v___x_2244_, v_00_u03c3s_2224_, v_hyps_2225_, v_restHyps_2219_, v_focusHyp_2218_, v_target_2226_, v_proof_2220_, v_a_2239_);
if (v_isShared_2242_ == 0)
{
lean_ctor_set(v___x_2241_, 0, v_prf_2245_);
v___x_2247_ = v___x_2241_;
goto v_reusejp_2246_;
}
else
{
lean_object* v_reuseFailAlloc_2248_; 
v_reuseFailAlloc_2248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2248_, 0, v_prf_2245_);
v___x_2247_ = v_reuseFailAlloc_2248_;
goto v_reusejp_2246_;
}
v_reusejp_2246_:
{
return v___x_2247_;
}
}
}
else
{
lean_dec_ref_known(v___x_2233_, 2);
lean_dec_ref(v_target_2226_);
lean_dec_ref(v_hyps_2225_);
lean_dec_ref(v_00_u03c3s_2224_);
lean_dec_ref(v_proof_2220_);
lean_dec_ref(v_restHyps_2219_);
lean_dec_ref(v_focusHyp_2218_);
return v___x_2238_;
}
}
}
}
else
{
lean_object* v___x_2252_; lean_object* v___x_2253_; 
lean_dec(v___x_2221_);
lean_dec_ref(v_proof_2220_);
lean_dec_ref(v_restHyps_2219_);
lean_dec_ref(v_focusHyp_2218_);
lean_dec_ref(v_k_2206_);
lean_dec_ref(v_goal_2204_);
v___x_2252_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__6, &l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__6_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__6);
v___x_2253_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__8___redArg(v___x_2252_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_);
return v___x_2253_;
}
}
else
{
lean_object* v_a_2254_; lean_object* v___x_2256_; uint8_t v_isShared_2257_; uint8_t v_isSharedCheck_2261_; 
lean_dec_ref(v_k_2206_);
lean_dec_ref(v_goal_2204_);
v_a_2254_ = lean_ctor_get(v___x_2216_, 0);
v_isSharedCheck_2261_ = !lean_is_exclusive(v___x_2216_);
if (v_isSharedCheck_2261_ == 0)
{
v___x_2256_ = v___x_2216_;
v_isShared_2257_ = v_isSharedCheck_2261_;
goto v_resetjp_2255_;
}
else
{
lean_inc(v_a_2254_);
lean_dec(v___x_2216_);
v___x_2256_ = lean_box(0);
v_isShared_2257_ = v_isSharedCheck_2261_;
goto v_resetjp_2255_;
}
v_resetjp_2255_:
{
lean_object* v___x_2259_; 
if (v_isShared_2257_ == 0)
{
v___x_2259_ = v___x_2256_;
goto v_reusejp_2258_;
}
else
{
lean_object* v_reuseFailAlloc_2260_; 
v_reuseFailAlloc_2260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2260_, 0, v_a_2254_);
v___x_2259_ = v_reuseFailAlloc_2260_;
goto v_reusejp_2258_;
}
v_reusejp_2258_:
{
return v___x_2259_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevert___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__4___boxed(lean_object* v_goal_2262_, lean_object* v_ref_2263_, lean_object* v_k_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_){
_start:
{
lean_object* v_res_2274_; 
v_res_2274_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevert___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__4(v_goal_2262_, v_ref_2263_, v_k_2264_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_);
lean_dec(v___y_2272_);
lean_dec_ref(v___y_2271_);
lean_dec(v___y_2270_);
lean_dec_ref(v___y_2269_);
lean_dec(v___y_2268_);
lean_dec_ref(v___y_2267_);
lean_dec(v___y_2266_);
lean_dec_ref(v___y_2265_);
return v_res_2274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__3(lean_object* v___x_2275_, lean_object* v_val_2276_, lean_object* v_h_2277_, lean_object* v_a_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_){
_start:
{
lean_object* v___x_2288_; lean_object* v___f_2289_; lean_object* v___x_2290_; 
v___x_2288_ = lean_st_mk_ref(v___x_2275_);
lean_inc(v___x_2288_);
v___f_2289_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__0___boxed), 11, 1);
lean_closure_set(v___f_2289_, 0, v___x_2288_);
v___x_2290_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevert___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__4(v_val_2276_, v_h_2277_, v___f_2289_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_);
if (lean_obj_tag(v___x_2290_) == 0)
{
lean_object* v_a_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; 
v_a_2291_ = lean_ctor_get(v___x_2290_, 0);
lean_inc(v_a_2291_);
lean_dec_ref_known(v___x_2290_, 1);
v___x_2292_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2___redArg(v_a_2278_, v_a_2291_, v___y_2284_);
lean_dec_ref(v___x_2292_);
v___x_2293_ = lean_st_ref_get(v___x_2288_);
lean_dec(v___x_2288_);
v___x_2294_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2293_, v___y_2280_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_);
return v___x_2294_;
}
else
{
lean_object* v_a_2295_; lean_object* v___x_2297_; uint8_t v_isShared_2298_; uint8_t v_isSharedCheck_2302_; 
lean_dec(v___x_2288_);
lean_dec(v_a_2278_);
v_a_2295_ = lean_ctor_get(v___x_2290_, 0);
v_isSharedCheck_2302_ = !lean_is_exclusive(v___x_2290_);
if (v_isSharedCheck_2302_ == 0)
{
v___x_2297_ = v___x_2290_;
v_isShared_2298_ = v_isSharedCheck_2302_;
goto v_resetjp_2296_;
}
else
{
lean_inc(v_a_2295_);
lean_dec(v___x_2290_);
v___x_2297_ = lean_box(0);
v_isShared_2298_ = v_isSharedCheck_2302_;
goto v_resetjp_2296_;
}
v_resetjp_2296_:
{
lean_object* v___x_2300_; 
if (v_isShared_2298_ == 0)
{
v___x_2300_ = v___x_2297_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2301_, 0, v_a_2295_);
v___x_2300_ = v_reuseFailAlloc_2301_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
return v___x_2300_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__3___boxed(lean_object* v___x_2303_, lean_object* v_val_2304_, lean_object* v_h_2305_, lean_object* v_a_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_){
_start:
{
lean_object* v_res_2316_; 
v_res_2316_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__3(v___x_2303_, v_val_2304_, v_h_2305_, v_a_2306_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_);
lean_dec(v___y_2314_);
lean_dec_ref(v___y_2313_);
lean_dec(v___y_2312_);
lean_dec_ref(v___y_2311_);
lean_dec(v___y_2310_);
lean_dec_ref(v___y_2309_);
lean_dec(v___y_2308_);
lean_dec_ref(v___y_2307_);
return v_res_2316_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5___redArg(lean_object* v_msg_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_){
_start:
{
lean_object* v_ref_2323_; lean_object* v___x_2324_; lean_object* v_a_2325_; lean_object* v___x_2327_; uint8_t v_isShared_2328_; uint8_t v_isSharedCheck_2333_; 
v_ref_2323_ = lean_ctor_get(v___y_2320_, 2);
v___x_2324_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5_spec__14(v_msg_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_);
v_a_2325_ = lean_ctor_get(v___x_2324_, 0);
v_isSharedCheck_2333_ = !lean_is_exclusive(v___x_2324_);
if (v_isSharedCheck_2333_ == 0)
{
v___x_2327_ = v___x_2324_;
v_isShared_2328_ = v_isSharedCheck_2333_;
goto v_resetjp_2326_;
}
else
{
lean_inc(v_a_2325_);
lean_dec(v___x_2324_);
v___x_2327_ = lean_box(0);
v_isShared_2328_ = v_isSharedCheck_2333_;
goto v_resetjp_2326_;
}
v_resetjp_2326_:
{
lean_object* v___x_2329_; lean_object* v___x_2331_; 
lean_inc(v_ref_2323_);
v___x_2329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2329_, 0, v_ref_2323_);
lean_ctor_set(v___x_2329_, 1, v_a_2325_);
if (v_isShared_2328_ == 0)
{
lean_ctor_set_tag(v___x_2327_, 1);
lean_ctor_set(v___x_2327_, 0, v___x_2329_);
v___x_2331_ = v___x_2327_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v___x_2329_);
v___x_2331_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
return v___x_2331_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5___redArg___boxed(lean_object* v_msg_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_){
_start:
{
lean_object* v_res_2340_; 
v_res_2340_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5___redArg(v_msg_2334_, v___y_2335_, v___y_2336_, v___y_2337_, v___y_2338_);
lean_dec(v___y_2338_);
lean_dec_ref(v___y_2337_);
lean_dec(v___y_2336_);
lean_dec_ref(v___y_2335_);
return v_res_2340_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__11(void){
_start:
{
lean_object* v___x_2365_; lean_object* v___x_2366_; 
v___x_2365_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__10));
v___x_2366_ = l_Lean_stringToMessageData(v___x_2365_);
return v___x_2366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert(lean_object* v_x_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_){
_start:
{
lean_object* v___y_2378_; lean_object* v___y_2379_; lean_object* v___y_2380_; lean_object* v___y_2381_; lean_object* v___y_2382_; lean_object* v___y_2383_; lean_object* v___y_2384_; lean_object* v___y_2385_; lean_object* v___y_2386_; lean_object* v___y_2387_; lean_object* v___y_2388_; lean_object* v___x_2392_; uint8_t v___x_2393_; 
v___x_2392_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__3));
lean_inc(v_x_2367_);
v___x_2393_ = l_Lean_Syntax_isOfKind(v_x_2367_, v___x_2392_);
if (v___x_2393_ == 0)
{
lean_object* v___x_2394_; 
lean_dec(v_x_2367_);
v___x_2394_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg();
return v___x_2394_;
}
else
{
lean_object* v___x_2395_; lean_object* v_n_2397_; lean_object* v___y_2398_; lean_object* v___y_2399_; lean_object* v___y_2400_; lean_object* v___y_2401_; lean_object* v___y_2402_; lean_object* v___y_2403_; lean_object* v___y_2404_; lean_object* v___y_2405_; lean_object* v___x_2422_; uint8_t v___x_2423_; 
v___x_2395_ = lean_unsigned_to_nat(1u);
v___x_2422_ = l_Lean_Syntax_getArg(v_x_2367_, v___x_2395_);
lean_dec(v_x_2367_);
lean_inc(v___x_2422_);
v___x_2423_ = l_Lean_Syntax_matchesNull(v___x_2422_, v___x_2395_);
if (v___x_2423_ == 0)
{
lean_object* v___x_2424_; 
lean_dec(v___x_2422_);
v___x_2424_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg();
return v___x_2424_;
}
else
{
lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; uint8_t v___x_2428_; 
v___x_2425_ = lean_unsigned_to_nat(0u);
v___x_2426_ = l_Lean_Syntax_getArg(v___x_2422_, v___x_2425_);
lean_dec(v___x_2422_);
v___x_2427_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__5));
lean_inc(v___x_2426_);
v___x_2428_ = l_Lean_Syntax_isOfKind(v___x_2426_, v___x_2427_);
if (v___x_2428_ == 0)
{
lean_object* v___x_2429_; uint8_t v___x_2430_; 
v___x_2429_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__7));
lean_inc(v___x_2426_);
v___x_2430_ = l_Lean_Syntax_isOfKind(v___x_2426_, v___x_2429_);
if (v___x_2430_ == 0)
{
lean_object* v___x_2431_; 
lean_dec(v___x_2426_);
v___x_2431_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg();
return v___x_2431_;
}
else
{
lean_object* v___x_2432_; uint8_t v___x_2433_; 
v___x_2432_ = l_Lean_Syntax_getArg(v___x_2426_, v___x_2395_);
lean_dec(v___x_2426_);
v___x_2433_ = l_Lean_Syntax_isNone(v___x_2432_);
if (v___x_2433_ == 0)
{
uint8_t v___x_2434_; 
lean_inc(v___x_2432_);
v___x_2434_ = l_Lean_Syntax_matchesNull(v___x_2432_, v___x_2395_);
if (v___x_2434_ == 0)
{
lean_object* v___x_2435_; 
lean_dec(v___x_2432_);
v___x_2435_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg();
return v___x_2435_;
}
else
{
lean_object* v_n_2436_; lean_object* v___x_2437_; 
v_n_2436_ = l_Lean_Syntax_getArg(v___x_2432_, v___x_2425_);
lean_dec(v___x_2432_);
v___x_2437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2437_, 0, v_n_2436_);
v_n_2397_ = v___x_2437_;
v___y_2398_ = v_a_2368_;
v___y_2399_ = v_a_2369_;
v___y_2400_ = v_a_2370_;
v___y_2401_ = v_a_2371_;
v___y_2402_ = v_a_2372_;
v___y_2403_ = v_a_2373_;
v___y_2404_ = v_a_2374_;
v___y_2405_ = v_a_2375_;
goto v___jp_2396_;
}
}
else
{
lean_object* v___x_2438_; 
lean_dec(v___x_2432_);
v___x_2438_ = lean_box(0);
v_n_2397_ = v___x_2438_;
v___y_2398_ = v_a_2368_;
v___y_2399_ = v_a_2369_;
v___y_2400_ = v_a_2370_;
v___y_2401_ = v_a_2371_;
v___y_2402_ = v_a_2372_;
v___y_2403_ = v_a_2373_;
v___y_2404_ = v_a_2374_;
v___y_2405_ = v_a_2375_;
goto v___jp_2396_;
}
}
}
else
{
lean_object* v_h_2439_; lean_object* v___x_2440_; uint8_t v___x_2441_; 
v_h_2439_ = l_Lean_Syntax_getArg(v___x_2426_, v___x_2425_);
lean_dec(v___x_2426_);
v___x_2440_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__9));
lean_inc(v_h_2439_);
v___x_2441_ = l_Lean_Syntax_isOfKind(v_h_2439_, v___x_2440_);
if (v___x_2441_ == 0)
{
lean_object* v___x_2442_; 
lean_dec(v_h_2439_);
v___x_2442_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg();
return v___x_2442_;
}
else
{
lean_object* v___x_2443_; 
v___x_2443_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_2369_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_);
if (lean_obj_tag(v___x_2443_) == 0)
{
lean_object* v_a_2444_; lean_object* v___x_2445_; 
v_a_2444_ = lean_ctor_get(v___x_2443_, 0);
lean_inc_n(v_a_2444_, 2);
lean_dec_ref_known(v___x_2443_, 1);
v___x_2445_ = l_Lean_MVarId_getType(v_a_2444_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_);
if (lean_obj_tag(v___x_2445_) == 0)
{
lean_object* v_a_2446_; lean_object* v___x_2447_; 
v_a_2446_ = lean_ctor_get(v___x_2445_, 0);
lean_inc(v_a_2446_);
lean_dec_ref_known(v___x_2445_, 1);
v___x_2447_ = l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f(v_a_2446_);
lean_dec(v_a_2446_);
if (lean_obj_tag(v___x_2447_) == 1)
{
lean_object* v_val_2448_; lean_object* v___x_2449_; lean_object* v___f_2450_; lean_object* v___x_2451_; 
v_val_2448_ = lean_ctor_get(v___x_2447_, 0);
lean_inc(v_val_2448_);
lean_dec_ref_known(v___x_2447_, 1);
v___x_2449_ = lean_box(0);
lean_inc(v_a_2444_);
v___f_2450_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__3___boxed), 13, 4);
lean_closure_set(v___f_2450_, 0, v___x_2449_);
lean_closure_set(v___f_2450_, 1, v_val_2448_);
lean_closure_set(v___f_2450_, 2, v_h_2439_);
lean_closure_set(v___f_2450_, 3, v_a_2444_);
v___x_2451_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___redArg(v_a_2444_, v___f_2450_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_);
return v___x_2451_;
}
else
{
lean_object* v___x_2452_; lean_object* v___x_2453_; 
lean_dec(v___x_2447_);
lean_dec(v_a_2444_);
lean_dec(v_h_2439_);
v___x_2452_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__11, &l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__11_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__11);
v___x_2453_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5___redArg(v___x_2452_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_);
return v___x_2453_;
}
}
else
{
lean_object* v_a_2454_; lean_object* v___x_2456_; uint8_t v_isShared_2457_; uint8_t v_isSharedCheck_2461_; 
lean_dec(v_a_2444_);
lean_dec(v_h_2439_);
v_a_2454_ = lean_ctor_get(v___x_2445_, 0);
v_isSharedCheck_2461_ = !lean_is_exclusive(v___x_2445_);
if (v_isSharedCheck_2461_ == 0)
{
v___x_2456_ = v___x_2445_;
v_isShared_2457_ = v_isSharedCheck_2461_;
goto v_resetjp_2455_;
}
else
{
lean_inc(v_a_2454_);
lean_dec(v___x_2445_);
v___x_2456_ = lean_box(0);
v_isShared_2457_ = v_isSharedCheck_2461_;
goto v_resetjp_2455_;
}
v_resetjp_2455_:
{
lean_object* v___x_2459_; 
if (v_isShared_2457_ == 0)
{
v___x_2459_ = v___x_2456_;
goto v_reusejp_2458_;
}
else
{
lean_object* v_reuseFailAlloc_2460_; 
v_reuseFailAlloc_2460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2460_, 0, v_a_2454_);
v___x_2459_ = v_reuseFailAlloc_2460_;
goto v_reusejp_2458_;
}
v_reusejp_2458_:
{
return v___x_2459_;
}
}
}
}
else
{
lean_object* v_a_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2469_; 
lean_dec(v_h_2439_);
v_a_2462_ = lean_ctor_get(v___x_2443_, 0);
v_isSharedCheck_2469_ = !lean_is_exclusive(v___x_2443_);
if (v_isSharedCheck_2469_ == 0)
{
v___x_2464_ = v___x_2443_;
v_isShared_2465_ = v_isSharedCheck_2469_;
goto v_resetjp_2463_;
}
else
{
lean_inc(v_a_2462_);
lean_dec(v___x_2443_);
v___x_2464_ = lean_box(0);
v_isShared_2465_ = v_isSharedCheck_2469_;
goto v_resetjp_2463_;
}
v_resetjp_2463_:
{
lean_object* v___x_2467_; 
if (v_isShared_2465_ == 0)
{
v___x_2467_ = v___x_2464_;
goto v_reusejp_2466_;
}
else
{
lean_object* v_reuseFailAlloc_2468_; 
v_reuseFailAlloc_2468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2468_, 0, v_a_2462_);
v___x_2467_ = v_reuseFailAlloc_2468_;
goto v_reusejp_2466_;
}
v_reusejp_2466_:
{
return v___x_2467_;
}
}
}
}
}
}
v___jp_2396_:
{
lean_object* v___x_2406_; 
v___x_2406_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg(v___y_2399_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_);
if (lean_obj_tag(v___x_2406_) == 0)
{
lean_object* v_a_2407_; 
v_a_2407_ = lean_ctor_get(v___x_2406_, 0);
lean_inc(v_a_2407_);
lean_dec_ref_known(v___x_2406_, 1);
if (lean_obj_tag(v_n_2397_) == 0)
{
lean_object* v_fst_2408_; lean_object* v_snd_2409_; 
v_fst_2408_ = lean_ctor_get(v_a_2407_, 0);
lean_inc(v_fst_2408_);
v_snd_2409_ = lean_ctor_get(v_a_2407_, 1);
lean_inc(v_snd_2409_);
lean_dec(v_a_2407_);
v___y_2378_ = v_snd_2409_;
v___y_2379_ = v_fst_2408_;
v___y_2380_ = v___y_2402_;
v___y_2381_ = v___y_2405_;
v___y_2382_ = v___y_2399_;
v___y_2383_ = v___y_2404_;
v___y_2384_ = v___y_2403_;
v___y_2385_ = v___y_2400_;
v___y_2386_ = v___y_2398_;
v___y_2387_ = v___y_2401_;
v___y_2388_ = v___x_2395_;
goto v___jp_2377_;
}
else
{
lean_object* v_fst_2410_; lean_object* v_snd_2411_; lean_object* v_val_2412_; lean_object* v___x_2413_; 
v_fst_2410_ = lean_ctor_get(v_a_2407_, 0);
lean_inc(v_fst_2410_);
v_snd_2411_ = lean_ctor_get(v_a_2407_, 1);
lean_inc(v_snd_2411_);
lean_dec(v_a_2407_);
v_val_2412_ = lean_ctor_get(v_n_2397_, 0);
lean_inc(v_val_2412_);
lean_dec_ref_known(v_n_2397_, 1);
v___x_2413_ = l_Lean_TSyntax_getNat(v_val_2412_);
lean_dec(v_val_2412_);
v___y_2378_ = v_snd_2411_;
v___y_2379_ = v_fst_2410_;
v___y_2380_ = v___y_2402_;
v___y_2381_ = v___y_2405_;
v___y_2382_ = v___y_2399_;
v___y_2383_ = v___y_2404_;
v___y_2384_ = v___y_2403_;
v___y_2385_ = v___y_2400_;
v___y_2386_ = v___y_2398_;
v___y_2387_ = v___y_2401_;
v___y_2388_ = v___x_2413_;
goto v___jp_2377_;
}
}
else
{
lean_object* v_a_2414_; lean_object* v___x_2416_; uint8_t v_isShared_2417_; uint8_t v_isSharedCheck_2421_; 
lean_dec(v_n_2397_);
v_a_2414_ = lean_ctor_get(v___x_2406_, 0);
v_isSharedCheck_2421_ = !lean_is_exclusive(v___x_2406_);
if (v_isSharedCheck_2421_ == 0)
{
v___x_2416_ = v___x_2406_;
v_isShared_2417_ = v_isSharedCheck_2421_;
goto v_resetjp_2415_;
}
else
{
lean_inc(v_a_2414_);
lean_dec(v___x_2406_);
v___x_2416_ = lean_box(0);
v_isShared_2417_ = v_isSharedCheck_2421_;
goto v_resetjp_2415_;
}
v_resetjp_2415_:
{
lean_object* v___x_2419_; 
if (v_isShared_2417_ == 0)
{
v___x_2419_ = v___x_2416_;
goto v_reusejp_2418_;
}
else
{
lean_object* v_reuseFailAlloc_2420_; 
v_reuseFailAlloc_2420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2420_, 0, v_a_2414_);
v___x_2419_ = v_reuseFailAlloc_2420_;
goto v_reusejp_2418_;
}
v_reusejp_2418_:
{
return v___x_2419_;
}
}
}
}
}
v___jp_2377_:
{
lean_object* v___x_2389_; lean_object* v___f_2390_; lean_object* v___x_2391_; 
v___x_2389_ = lean_box(0);
lean_inc(v___y_2379_);
v___f_2390_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__1___boxed), 13, 4);
lean_closure_set(v___f_2390_, 0, v___x_2389_);
lean_closure_set(v___f_2390_, 1, v___y_2378_);
lean_closure_set(v___f_2390_, 2, v___y_2388_);
lean_closure_set(v___f_2390_, 3, v___y_2379_);
v___x_2391_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___redArg(v___y_2379_, v___f_2390_, v___y_2386_, v___y_2382_, v___y_2385_, v___y_2387_, v___y_2380_, v___y_2384_, v___y_2383_, v___y_2381_);
return v___x_2391_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___boxed(lean_object* v_x_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_, lean_object* v_a_2477_, lean_object* v_a_2478_, lean_object* v_a_2479_){
_start:
{
lean_object* v_res_2480_; 
v_res_2480_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert(v_x_2470_, v_a_2471_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_, v_a_2476_, v_a_2477_, v_a_2478_);
lean_dec(v_a_2478_);
lean_dec_ref(v_a_2477_);
lean_dec(v_a_2476_);
lean_dec_ref(v_a_2475_);
lean_dec(v_a_2474_);
lean_dec_ref(v_a_2473_);
lean_dec(v_a_2472_);
lean_dec_ref(v_a_2471_);
return v_res_2480_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2(lean_object* v_mvarId_2481_, lean_object* v_val_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_){
_start:
{
lean_object* v___x_2492_; 
v___x_2492_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2___redArg(v_mvarId_2481_, v_val_2482_, v___y_2488_);
return v___x_2492_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2___boxed(lean_object* v_mvarId_2493_, lean_object* v_val_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_){
_start:
{
lean_object* v_res_2504_; 
v_res_2504_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2(v_mvarId_2493_, v_val_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_);
lean_dec(v___y_2502_);
lean_dec_ref(v___y_2501_);
lean_dec(v___y_2500_);
lean_dec_ref(v___y_2499_);
lean_dec(v___y_2498_);
lean_dec_ref(v___y_2497_);
lean_dec(v___y_2496_);
lean_dec_ref(v___y_2495_);
return v_res_2504_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5(lean_object* v_00_u03b1_2505_, lean_object* v_msg_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_){
_start:
{
lean_object* v___x_2516_; 
v___x_2516_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5___redArg(v_msg_2506_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_);
return v___x_2516_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5___boxed(lean_object* v_00_u03b1_2517_, lean_object* v_msg_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_){
_start:
{
lean_object* v_res_2528_; 
v_res_2528_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5(v_00_u03b1_2517_, v_msg_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_);
lean_dec(v___y_2526_);
lean_dec_ref(v___y_2525_);
lean_dec(v___y_2524_);
lean_dec_ref(v___y_2523_);
lean_dec(v___y_2522_);
lean_dec_ref(v___y_2521_);
lean_dec(v___y_2520_);
lean_dec_ref(v___y_2519_);
return v_res_2528_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__1(lean_object* v_inst_2529_, lean_object* v_R_2530_, lean_object* v_a_2531_, lean_object* v_b_2532_){
_start:
{
lean_object* v___x_2533_; 
v___x_2533_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__1___redArg(v_a_2531_, v_b_2532_);
return v___x_2533_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__2(size_t v_sz_2534_, size_t v_i_2535_, lean_object* v_bs_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_){
_start:
{
lean_object* v___x_2546_; 
v___x_2546_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__2___redArg(v_sz_2534_, v_i_2535_, v_bs_2536_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_);
return v___x_2546_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__2___boxed(lean_object* v_sz_2547_, lean_object* v_i_2548_, lean_object* v_bs_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_){
_start:
{
size_t v_sz_boxed_2559_; size_t v_i_boxed_2560_; lean_object* v_res_2561_; 
v_sz_boxed_2559_ = lean_unbox_usize(v_sz_2547_);
lean_dec(v_sz_2547_);
v_i_boxed_2560_ = lean_unbox_usize(v_i_2548_);
lean_dec(v_i_2548_);
v_res_2561_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__2(v_sz_boxed_2559_, v_i_boxed_2560_, v_bs_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_);
lean_dec(v___y_2557_);
lean_dec_ref(v___y_2556_);
lean_dec(v___y_2555_);
lean_dec_ref(v___y_2554_);
lean_dec(v___y_2553_);
lean_dec_ref(v___y_2552_);
lean_dec(v___y_2551_);
lean_dec_ref(v___y_2550_);
return v_res_2561_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__4(lean_object* v_as_2562_, size_t v_sz_2563_, size_t v_i_2564_, lean_object* v_bs_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_){
_start:
{
lean_object* v___x_2575_; 
v___x_2575_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__4___redArg(v_sz_2563_, v_i_2564_, v_bs_2565_, v___y_2572_, v___y_2573_);
return v___x_2575_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__4___boxed(lean_object* v_as_2576_, lean_object* v_sz_2577_, lean_object* v_i_2578_, lean_object* v_bs_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_){
_start:
{
size_t v_sz_boxed_2589_; size_t v_i_boxed_2590_; lean_object* v_res_2591_; 
v_sz_boxed_2589_ = lean_unbox_usize(v_sz_2577_);
lean_dec(v_sz_2577_);
v_i_boxed_2590_ = lean_unbox_usize(v_i_2578_);
lean_dec(v_i_2578_);
v_res_2591_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__4(v_as_2576_, v_sz_boxed_2589_, v_i_boxed_2590_, v_bs_2579_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_);
lean_dec(v___y_2587_);
lean_dec_ref(v___y_2586_);
lean_dec(v___y_2585_);
lean_dec_ref(v___y_2584_);
lean_dec(v___y_2583_);
lean_dec_ref(v___y_2582_);
lean_dec(v___y_2581_);
lean_dec_ref(v___y_2580_);
lean_dec_ref(v_as_2576_);
return v_res_2591_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__8(lean_object* v_00_u03b1_2592_, lean_object* v_msg_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_){
_start:
{
lean_object* v___x_2599_; 
v___x_2599_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__8___redArg(v_msg_2593_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_);
return v___x_2599_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__8___boxed(lean_object* v_00_u03b1_2600_, lean_object* v_msg_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_){
_start:
{
lean_object* v_res_2607_; 
v_res_2607_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__8(v_00_u03b1_2600_, v_msg_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_);
lean_dec(v___y_2605_);
lean_dec_ref(v___y_2604_);
lean_dec(v___y_2603_);
lean_dec_ref(v___y_2602_);
return v_res_2607_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10(lean_object* v_00_u03b2_2608_, lean_object* v_x_2609_, lean_object* v_x_2610_, lean_object* v_x_2611_){
_start:
{
lean_object* v___x_2612_; 
v___x_2612_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10___redArg(v_x_2609_, v_x_2610_, v_x_2611_);
return v___x_2612_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14(lean_object* v_00_u03b2_2613_, lean_object* v_x_2614_, size_t v_x_2615_, size_t v_x_2616_, lean_object* v_x_2617_, lean_object* v_x_2618_){
_start:
{
lean_object* v___x_2619_; 
v___x_2619_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14___redArg(v_x_2614_, v_x_2615_, v_x_2616_, v_x_2617_, v_x_2618_);
return v___x_2619_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14___boxed(lean_object* v_00_u03b2_2620_, lean_object* v_x_2621_, lean_object* v_x_2622_, lean_object* v_x_2623_, lean_object* v_x_2624_, lean_object* v_x_2625_){
_start:
{
size_t v_x_19393__boxed_2626_; size_t v_x_19394__boxed_2627_; lean_object* v_res_2628_; 
v_x_19393__boxed_2626_ = lean_unbox_usize(v_x_2622_);
lean_dec(v_x_2622_);
v_x_19394__boxed_2627_ = lean_unbox_usize(v_x_2623_);
lean_dec(v_x_2623_);
v_res_2628_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14(v_00_u03b2_2620_, v_x_2621_, v_x_19393__boxed_2626_, v_x_19394__boxed_2627_, v_x_2624_, v_x_2625_);
return v_res_2628_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14_spec__20(lean_object* v_00_u03b2_2629_, lean_object* v_n_2630_, lean_object* v_k_2631_, lean_object* v_v_2632_){
_start:
{
lean_object* v___x_2633_; 
v___x_2633_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14_spec__20___redArg(v_n_2630_, v_k_2631_, v_v_2632_);
return v___x_2633_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14_spec__21(lean_object* v_00_u03b2_2634_, size_t v_depth_2635_, lean_object* v_keys_2636_, lean_object* v_vals_2637_, lean_object* v_heq_2638_, lean_object* v_i_2639_, lean_object* v_entries_2640_){
_start:
{
lean_object* v___x_2641_; 
v___x_2641_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14_spec__21___redArg(v_depth_2635_, v_keys_2636_, v_vals_2637_, v_i_2639_, v_entries_2640_);
return v___x_2641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14_spec__21___boxed(lean_object* v_00_u03b2_2642_, lean_object* v_depth_2643_, lean_object* v_keys_2644_, lean_object* v_vals_2645_, lean_object* v_heq_2646_, lean_object* v_i_2647_, lean_object* v_entries_2648_){
_start:
{
size_t v_depth_boxed_2649_; lean_object* v_res_2650_; 
v_depth_boxed_2649_ = lean_unbox_usize(v_depth_2643_);
lean_dec(v_depth_2643_);
v_res_2650_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14_spec__21(v_00_u03b2_2642_, v_depth_boxed_2649_, v_keys_2644_, v_vals_2645_, v_heq_2646_, v_i_2647_, v_entries_2648_);
lean_dec_ref(v_vals_2645_);
lean_dec_ref(v_keys_2644_);
return v_res_2650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19_spec__21(lean_object* v_00_u03b1_2651_, lean_object* v_name_2652_, uint8_t v_bi_2653_, lean_object* v_type_2654_, lean_object* v_k_2655_, uint8_t v_kind_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_){
_start:
{
lean_object* v___x_2666_; 
v___x_2666_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19_spec__21___redArg(v_name_2652_, v_bi_2653_, v_type_2654_, v_k_2655_, v_kind_2656_, v___y_2657_, v___y_2658_, v___y_2659_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_, v___y_2664_);
return v___x_2666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19_spec__21___boxed(lean_object* v_00_u03b1_2667_, lean_object* v_name_2668_, lean_object* v_bi_2669_, lean_object* v_type_2670_, lean_object* v_k_2671_, lean_object* v_kind_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_){
_start:
{
uint8_t v_bi_boxed_2682_; uint8_t v_kind_boxed_2683_; lean_object* v_res_2684_; 
v_bi_boxed_2682_ = lean_unbox(v_bi_2669_);
v_kind_boxed_2683_ = lean_unbox(v_kind_2672_);
v_res_2684_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19_spec__21(v_00_u03b1_2667_, v_name_2668_, v_bi_boxed_2682_, v_type_2670_, v_k_2671_, v_kind_boxed_2683_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_);
lean_dec(v___y_2680_);
lean_dec_ref(v___y_2679_);
lean_dec(v___y_2678_);
lean_dec_ref(v___y_2677_);
lean_dec(v___y_2676_);
lean_dec_ref(v___y_2675_);
lean_dec(v___y_2674_);
lean_dec_ref(v___y_2673_);
return v_res_2684_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14_spec__20_spec__22(lean_object* v_00_u03b2_2685_, lean_object* v_x_2686_, lean_object* v_x_2687_, lean_object* v_x_2688_, lean_object* v_x_2689_){
_start:
{
lean_object* v___x_2690_; 
v___x_2690_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14_spec__20_spec__22___redArg(v_x_2686_, v_x_2687_, v_x_2688_, v_x_2689_);
return v___x_2690_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Revert_0__Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1(){
_start:
{
lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; 
v___x_2702_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2703_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__3));
v___x_2704_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Revert_0__Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__3));
v___x_2705_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___boxed), 10, 0);
v___x_2706_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2702_, v___x_2703_, v___x_2704_, v___x_2705_);
return v___x_2706_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Revert_0__Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___boxed(lean_object* v_a_2707_){
_start:
{
lean_object* v_res_2708_; 
v_res_2708_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Revert_0__Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1();
return v_res_2708_;
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
