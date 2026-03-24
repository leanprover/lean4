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
lean_object* l_instMonadEIO(lean_object*);
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
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
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
extern lean_object* l_Lean_Core_instMonadQuotationCoreM;
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadFunctor___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadLift___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadFunctor___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instMonadExceptOfExceptionCoreM;
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_instMonadFunctor___aux__1___boxed, .m_arity = 7, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__10_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__11_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__12;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__13;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "mrevert: expected "};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__14 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__14_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__15;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = " excess arguments in "};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__16 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__16_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__17;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = ", got "};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__18 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__18_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__19;
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
lean_dec(v___y_98_);
lean_dec_ref(v___y_97_);
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
lean_dec(v___y_150_);
lean_dec_ref(v___y_149_);
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
uint8_t v___x_1118__boxed_207_; uint8_t v___x_1119__boxed_208_; uint8_t v___x_1120__boxed_209_; lean_object* v_res_210_; 
v___x_1118__boxed_207_ = lean_unbox(v___x_201_);
v___x_1119__boxed_208_ = lean_unbox(v___x_202_);
v___x_1120__boxed_209_ = lean_unbox(v___x_203_);
v_res_210_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__8(v_hypName_196_, v_uniq_197_, v_toApplicative_198_, v_ss_199_, v_hyps_200_, v___x_1118__boxed_207_, v___x_1119__boxed_208_, v___x_1120__boxed_209_, v_inst_204_, v_toBind_205_, v_____do__lift_206_);
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
uint8_t v___x_1153__boxed_243_; lean_object* v_res_244_; 
v___x_1153__boxed_243_ = lean_unbox(v___x_238_);
v_res_244_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__9(v_hypName_234_, v_toApplicative_235_, v_ss_236_, v_hyps_237_, v___x_1153__boxed_243_, v_inst_239_, v_toBind_240_, v_00_u03c6_241_, v_uniq_242_);
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
uint8_t v___x_1187__boxed_274_; lean_object* v_res_275_; 
v___x_1187__boxed_274_ = lean_unbox(v___x_269_);
v_res_275_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__10(v_u_263_, v_00_u03c3s_264_, v_hypName_265_, v_toApplicative_266_, v_ss_267_, v_hyps_268_, v___x_1187__boxed_274_, v_inst_270_, v_toBind_271_, v___f_272_, v_eqs_273_);
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
uint8_t v___x_1204__boxed_309_; lean_object* v_res_310_; 
v___x_1204__boxed_309_ = lean_unbox(v___x_301_);
v_res_310_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__11(v_u_296_, v_00_u03c3s_297_, v_hypName_298_, v_toApplicative_299_, v_hyps_300_, v___x_1204__boxed_309_, v_inst_302_, v_toBind_303_, v___f_304_, v_revertArgs_305_, v_inst_306_, v___f_307_, v_ss_308_);
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
v___x_574_ = l_instMonadEIO(lean_box(0));
return v___x_574_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__1(void){
_start:
{
lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_575_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__0, &l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__0_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__0);
v___x_576_ = l_StateRefT_x27_instMonad___redArg(v___x_575_);
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
v___x_627_ = l_StateRefT_x27_instMonad___redArg(v___x_626_);
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
uint8_t v___x_1548__boxed_692_; lean_object* v_res_693_; 
v___x_1548__boxed_692_ = lean_unbox(v___x_679_);
v_res_693_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20(v_inst_673_, v_inst_674_, v_u_675_, v_00_u03c3s_676_, v_hypName_677_, v_hyps_678_, v___x_1548__boxed_692_, v___f_680_, v_revertArgs_681_, v___f_682_, v_target_683_, v_a_684_, v_n_685_, v_f_686_, v_k_687_, v___x_688_, v___f_689_, v_inst_690_, v_____r_691_);
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
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__12(void){
_start:
{
lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_718_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_719_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__11));
v___x_720_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__10));
v___x_721_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_720_, v___x_719_, v___x_718_);
return v___x_721_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__13(void){
_start:
{
lean_object* v___x_722_; lean_object* v___f_723_; lean_object* v___f_724_; lean_object* v___x_725_; 
v___x_722_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__12, &l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__12_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__12);
v___f_723_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__9));
v___f_724_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__8));
v___x_725_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_724_, v___f_723_, v___x_722_);
return v___x_725_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__15(void){
_start:
{
lean_object* v___x_727_; lean_object* v___x_728_; 
v___x_727_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__14));
v___x_728_ = l_Lean_stringToMessageData(v___x_727_);
return v___x_728_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__17(void){
_start:
{
lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_730_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__16));
v___x_731_ = l_Lean_stringToMessageData(v___x_730_);
return v___x_731_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__19(void){
_start:
{
lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_733_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__18));
v___x_734_ = l_Lean_stringToMessageData(v___x_733_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg(lean_object* v_inst_735_, lean_object* v_inst_736_, lean_object* v_inst_737_, lean_object* v_goal_738_, lean_object* v_n_739_, lean_object* v_hypName_740_, lean_object* v_k_741_){
_start:
{
lean_object* v___x_742_; uint8_t v___x_743_; 
v___x_742_ = lean_unsigned_to_nat(0u);
v___x_743_ = lean_nat_dec_eq(v_n_739_, v___x_742_);
if (v___x_743_ == 0)
{
lean_object* v_u_744_; lean_object* v_00_u03c3s_745_; lean_object* v_hyps_746_; lean_object* v_target_747_; lean_object* v___f_748_; lean_object* v___f_749_; lean_object* v___f_750_; lean_object* v___f_751_; lean_object* v_T_752_; lean_object* v_f_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v_a_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v_revertArgs_760_; lean_object* v___x_761_; lean_object* v___f_762_; lean_object* v___x_763_; uint8_t v___x_764_; 
v_u_744_ = lean_ctor_get(v_goal_738_, 0);
lean_inc(v_u_744_);
v_00_u03c3s_745_ = lean_ctor_get(v_goal_738_, 1);
lean_inc_ref(v_00_u03c3s_745_);
v_hyps_746_ = lean_ctor_get(v_goal_738_, 2);
lean_inc_ref(v_hyps_746_);
v_target_747_ = lean_ctor_get(v_goal_738_, 3);
lean_inc_ref(v_target_747_);
lean_dec_ref(v_goal_738_);
lean_inc(v_inst_737_);
v___f_748_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__0), 2, 1);
lean_closure_set(v___f_748_, 0, v_inst_737_);
lean_inc(v_hypName_740_);
v___f_749_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__1___boxed), 6, 1);
lean_closure_set(v___f_749_, 0, v_hypName_740_);
v___f_750_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__0));
lean_inc(v_u_744_);
v___f_751_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__3), 3, 1);
lean_closure_set(v___f_751_, 0, v_u_744_);
v_T_752_ = l_Lean_Expr_consumeMData(v_target_747_);
v_f_753_ = l_Lean_Expr_getAppFn(v_T_752_);
v___x_754_ = l_Lean_Expr_getAppNumArgs(v_T_752_);
v___x_755_ = lean_mk_empty_array_with_capacity(v___x_754_);
lean_dec(v___x_754_);
lean_inc_ref(v_T_752_);
v_a_756_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_T_752_, v___x_755_);
lean_inc(v_n_739_);
lean_inc_ref(v_a_756_);
v___x_757_ = l_Array_toSubarray___redArg(v_a_756_, v___x_742_, v_n_739_);
v___x_758_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__1));
v___x_759_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_750_, v___x_757_, v___x_758_);
v_revertArgs_760_ = l_Array_reverse___redArg(v___x_759_);
v___x_761_ = lean_box(v___x_743_);
lean_inc_ref(v_inst_736_);
lean_inc_ref(v___f_751_);
lean_inc(v_k_741_);
lean_inc_ref(v_f_753_);
lean_inc(v_n_739_);
lean_inc_ref(v_a_756_);
lean_inc_ref(v_target_747_);
lean_inc_ref(v___f_748_);
lean_inc_ref(v_revertArgs_760_);
lean_inc_ref(v___f_749_);
lean_inc_ref(v_hyps_746_);
lean_inc(v_hypName_740_);
lean_inc_ref(v_00_u03c3s_745_);
lean_inc(v_u_744_);
lean_inc(v_inst_737_);
lean_inc_ref(v_inst_735_);
v___f_762_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___boxed), 19, 18);
lean_closure_set(v___f_762_, 0, v_inst_735_);
lean_closure_set(v___f_762_, 1, v_inst_737_);
lean_closure_set(v___f_762_, 2, v_u_744_);
lean_closure_set(v___f_762_, 3, v_00_u03c3s_745_);
lean_closure_set(v___f_762_, 4, v_hypName_740_);
lean_closure_set(v___f_762_, 5, v_hyps_746_);
lean_closure_set(v___f_762_, 6, v___x_761_);
lean_closure_set(v___f_762_, 7, v___f_749_);
lean_closure_set(v___f_762_, 8, v_revertArgs_760_);
lean_closure_set(v___f_762_, 9, v___f_748_);
lean_closure_set(v___f_762_, 10, v_target_747_);
lean_closure_set(v___f_762_, 11, v_a_756_);
lean_closure_set(v___f_762_, 12, v_n_739_);
lean_closure_set(v___f_762_, 13, v_f_753_);
lean_closure_set(v___f_762_, 14, v_k_741_);
lean_closure_set(v___f_762_, 15, v___x_742_);
lean_closure_set(v___f_762_, 16, v___f_751_);
lean_closure_set(v___f_762_, 17, v_inst_736_);
v___x_763_ = lean_array_get_size(v_revertArgs_760_);
v___x_764_ = lean_nat_dec_eq(v___x_763_, v_n_739_);
if (v___x_764_ == 0)
{
lean_object* v_toBind_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_856_; 
lean_dec_ref(v_revertArgs_760_);
lean_dec_ref(v_a_756_);
lean_dec_ref(v_f_753_);
lean_dec_ref(v___f_751_);
lean_dec_ref(v___f_749_);
lean_dec_ref(v___f_748_);
lean_dec_ref(v_target_747_);
lean_dec_ref(v_hyps_746_);
lean_dec_ref(v_00_u03c3s_745_);
lean_dec(v_u_744_);
lean_dec(v_k_741_);
lean_dec(v_hypName_740_);
lean_dec_ref(v_inst_736_);
v_toBind_765_ = lean_ctor_get(v_inst_735_, 1);
v_isSharedCheck_856_ = !lean_is_exclusive(v_inst_735_);
if (v_isSharedCheck_856_ == 0)
{
lean_object* v_unused_857_; 
v_unused_857_ = lean_ctor_get(v_inst_735_, 0);
lean_dec(v_unused_857_);
v___x_767_ = v_inst_735_;
v_isShared_768_ = v_isSharedCheck_856_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_toBind_765_);
lean_dec(v_inst_735_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_856_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___x_769_; lean_object* v_toApplicative_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_854_; 
v___x_769_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__1);
v_toApplicative_770_ = lean_ctor_get(v___x_769_, 0);
v_isSharedCheck_854_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_854_ == 0)
{
lean_object* v_unused_855_; 
v_unused_855_ = lean_ctor_get(v___x_769_, 1);
lean_dec(v_unused_855_);
v___x_772_ = v___x_769_;
v_isShared_773_ = v_isSharedCheck_854_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_toApplicative_770_);
lean_dec(v___x_769_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_854_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v_toFunctor_774_; lean_object* v_toSeq_775_; lean_object* v_toSeqLeft_776_; lean_object* v_toSeqRight_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_852_; 
v_toFunctor_774_ = lean_ctor_get(v_toApplicative_770_, 0);
v_toSeq_775_ = lean_ctor_get(v_toApplicative_770_, 2);
v_toSeqLeft_776_ = lean_ctor_get(v_toApplicative_770_, 3);
v_toSeqRight_777_ = lean_ctor_get(v_toApplicative_770_, 4);
v_isSharedCheck_852_ = !lean_is_exclusive(v_toApplicative_770_);
if (v_isSharedCheck_852_ == 0)
{
lean_object* v_unused_853_; 
v_unused_853_ = lean_ctor_get(v_toApplicative_770_, 1);
lean_dec(v_unused_853_);
v___x_779_ = v_toApplicative_770_;
v_isShared_780_ = v_isSharedCheck_852_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_toSeqRight_777_);
lean_inc(v_toSeqLeft_776_);
lean_inc(v_toSeq_775_);
lean_inc(v_toFunctor_774_);
lean_dec(v_toApplicative_770_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_852_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v___f_781_; lean_object* v___f_782_; lean_object* v___f_783_; lean_object* v___f_784_; lean_object* v___x_786_; 
v___f_781_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__2));
v___f_782_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__3));
lean_inc_ref(v_toFunctor_774_);
v___f_783_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_783_, 0, v_toFunctor_774_);
v___f_784_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_784_, 0, v_toFunctor_774_);
if (v_isShared_768_ == 0)
{
lean_ctor_set(v___x_767_, 1, v___f_784_);
lean_ctor_set(v___x_767_, 0, v___f_783_);
v___x_786_ = v___x_767_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v___f_783_);
lean_ctor_set(v_reuseFailAlloc_851_, 1, v___f_784_);
v___x_786_ = v_reuseFailAlloc_851_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
lean_object* v___f_787_; lean_object* v___f_788_; lean_object* v___f_789_; lean_object* v___x_791_; 
v___f_787_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_787_, 0, v_toSeqRight_777_);
v___f_788_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_788_, 0, v_toSeqLeft_776_);
v___f_789_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_789_, 0, v_toSeq_775_);
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 4, v___f_787_);
lean_ctor_set(v___x_779_, 3, v___f_788_);
lean_ctor_set(v___x_779_, 2, v___f_789_);
lean_ctor_set(v___x_779_, 1, v___f_781_);
lean_ctor_set(v___x_779_, 0, v___x_786_);
v___x_791_ = v___x_779_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v___x_786_);
lean_ctor_set(v_reuseFailAlloc_850_, 1, v___f_781_);
lean_ctor_set(v_reuseFailAlloc_850_, 2, v___f_789_);
lean_ctor_set(v_reuseFailAlloc_850_, 3, v___f_788_);
lean_ctor_set(v_reuseFailAlloc_850_, 4, v___f_787_);
v___x_791_ = v_reuseFailAlloc_850_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
lean_object* v___x_793_; 
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 1, v___f_782_);
lean_ctor_set(v___x_772_, 0, v___x_791_);
v___x_793_ = v___x_772_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v___x_791_);
lean_ctor_set(v_reuseFailAlloc_849_, 1, v___f_782_);
v___x_793_ = v_reuseFailAlloc_849_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
lean_object* v___x_794_; lean_object* v_toApplicative_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_847_; 
v___x_794_ = l_StateRefT_x27_instMonad___redArg(v___x_793_);
v_toApplicative_795_ = lean_ctor_get(v___x_794_, 0);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_794_);
if (v_isSharedCheck_847_ == 0)
{
lean_object* v_unused_848_; 
v_unused_848_ = lean_ctor_get(v___x_794_, 1);
lean_dec(v_unused_848_);
v___x_797_ = v___x_794_;
v_isShared_798_ = v_isSharedCheck_847_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_toApplicative_795_);
lean_dec(v___x_794_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_847_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v_toFunctor_799_; lean_object* v_toSeq_800_; lean_object* v_toSeqLeft_801_; lean_object* v_toSeqRight_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_845_; 
v_toFunctor_799_ = lean_ctor_get(v_toApplicative_795_, 0);
v_toSeq_800_ = lean_ctor_get(v_toApplicative_795_, 2);
v_toSeqLeft_801_ = lean_ctor_get(v_toApplicative_795_, 3);
v_toSeqRight_802_ = lean_ctor_get(v_toApplicative_795_, 4);
v_isSharedCheck_845_ = !lean_is_exclusive(v_toApplicative_795_);
if (v_isSharedCheck_845_ == 0)
{
lean_object* v_unused_846_; 
v_unused_846_ = lean_ctor_get(v_toApplicative_795_, 1);
lean_dec(v_unused_846_);
v___x_804_ = v_toApplicative_795_;
v_isShared_805_ = v_isSharedCheck_845_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_toSeqRight_802_);
lean_inc(v_toSeqLeft_801_);
lean_inc(v_toSeq_800_);
lean_inc(v_toFunctor_799_);
lean_dec(v_toApplicative_795_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_845_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v___f_806_; lean_object* v___f_807_; lean_object* v___f_808_; lean_object* v___f_809_; lean_object* v___x_810_; lean_object* v___f_811_; lean_object* v___f_812_; lean_object* v___f_813_; lean_object* v___x_815_; 
v___f_806_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__4));
v___f_807_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__5));
lean_inc_ref(v_toFunctor_799_);
v___f_808_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_808_, 0, v_toFunctor_799_);
v___f_809_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_809_, 0, v_toFunctor_799_);
v___x_810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_810_, 0, v___f_808_);
lean_ctor_set(v___x_810_, 1, v___f_809_);
v___f_811_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_811_, 0, v_toSeqRight_802_);
v___f_812_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_812_, 0, v_toSeqLeft_801_);
v___f_813_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_813_, 0, v_toSeq_800_);
if (v_isShared_805_ == 0)
{
lean_ctor_set(v___x_804_, 4, v___f_811_);
lean_ctor_set(v___x_804_, 3, v___f_812_);
lean_ctor_set(v___x_804_, 2, v___f_813_);
lean_ctor_set(v___x_804_, 1, v___f_806_);
lean_ctor_set(v___x_804_, 0, v___x_810_);
v___x_815_ = v___x_804_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v___x_810_);
lean_ctor_set(v_reuseFailAlloc_844_, 1, v___f_806_);
lean_ctor_set(v_reuseFailAlloc_844_, 2, v___f_813_);
lean_ctor_set(v_reuseFailAlloc_844_, 3, v___f_812_);
lean_ctor_set(v_reuseFailAlloc_844_, 4, v___f_811_);
v___x_815_ = v_reuseFailAlloc_844_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
lean_object* v___x_817_; 
if (v_isShared_798_ == 0)
{
lean_ctor_set(v___x_797_, 1, v___f_807_);
lean_ctor_set(v___x_797_, 0, v___x_815_);
v___x_817_ = v___x_797_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v___x_815_);
lean_ctor_set(v_reuseFailAlloc_843_, 1, v___f_807_);
v___x_817_ = v_reuseFailAlloc_843_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v_toMonadRef_820_; lean_object* v___f_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_818_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__7, &l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__7_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__7);
v___x_819_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__13, &l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__13_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__13);
v_toMonadRef_820_ = lean_ctor_get(v___x_819_, 0);
lean_inc_ref(v_toMonadRef_820_);
v___f_821_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__21), 2, 1);
lean_closure_set(v___f_821_, 0, v___f_762_);
v___x_822_ = l_Lean_Meta_instAddMessageContextMetaM;
lean_inc_ref(v___x_817_);
v___x_823_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___x_822_, v___x_817_);
v___x_824_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_824_, 0, v___x_818_);
lean_ctor_set(v___x_824_, 1, v_toMonadRef_820_);
lean_ctor_set(v___x_824_, 2, v___x_823_);
v___x_825_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__15, &l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__15_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__15);
v___x_826_ = l_Nat_reprFast(v_n_739_);
v___x_827_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_827_, 0, v___x_826_);
v___x_828_ = l_Lean_MessageData_ofFormat(v___x_827_);
v___x_829_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_829_, 0, v___x_825_);
lean_ctor_set(v___x_829_, 1, v___x_828_);
v___x_830_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__17, &l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__17_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__17);
v___x_831_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_831_, 0, v___x_829_);
lean_ctor_set(v___x_831_, 1, v___x_830_);
v___x_832_ = l_Lean_MessageData_ofExpr(v_T_752_);
v___x_833_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_833_, 0, v___x_831_);
lean_ctor_set(v___x_833_, 1, v___x_832_);
v___x_834_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__19, &l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__19_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__19);
v___x_835_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_835_, 0, v___x_833_);
lean_ctor_set(v___x_835_, 1, v___x_834_);
v___x_836_ = l_Nat_reprFast(v___x_763_);
v___x_837_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_837_, 0, v___x_836_);
v___x_838_ = l_Lean_MessageData_ofFormat(v___x_837_);
v___x_839_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_839_, 0, v___x_835_);
lean_ctor_set(v___x_839_, 1, v___x_838_);
v___x_840_ = l_Lean_throwError___redArg(v___x_817_, v___x_824_, v___x_839_);
v___x_841_ = lean_apply_2(v_inst_737_, lean_box(0), v___x_840_);
v___x_842_ = lean_apply_4(v_toBind_765_, lean_box(0), lean_box(0), v___x_841_, v___f_821_);
return v___x_842_;
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
lean_object* v___x_858_; lean_object* v___x_859_; 
lean_dec_ref(v___f_762_);
lean_dec_ref(v_T_752_);
v___x_858_ = lean_box(0);
v___x_859_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20(v_inst_735_, v_inst_737_, v_u_744_, v_00_u03c3s_745_, v_hypName_740_, v_hyps_746_, v___x_743_, v___f_749_, v_revertArgs_760_, v___f_748_, v_target_747_, v_a_756_, v_n_739_, v_f_753_, v_k_741_, v___x_742_, v___f_751_, v_inst_736_, v___x_858_);
return v___x_859_;
}
}
else
{
lean_object* v___x_860_; 
lean_dec(v_hypName_740_);
lean_dec(v_n_739_);
lean_dec(v_inst_737_);
lean_dec_ref(v_inst_736_);
lean_dec_ref(v_inst_735_);
v___x_860_ = lean_apply_1(v_k_741_, v_goal_738_);
return v___x_860_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN(lean_object* v_m_861_, lean_object* v_inst_862_, lean_object* v_inst_863_, lean_object* v_inst_864_, lean_object* v_goal_865_, lean_object* v_n_866_, lean_object* v_hypName_867_, lean_object* v_k_868_){
_start:
{
lean_object* v___x_869_; 
v___x_869_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg(v_inst_862_, v_inst_863_, v_inst_864_, v_goal_865_, v_n_866_, v_hypName_867_, v_k_868_);
return v___x_869_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; 
v___x_870_ = lean_box(0);
v___x_871_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_872_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_872_, 0, v___x_871_);
lean_ctor_set(v___x_872_, 1, v___x_870_);
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg(){
_start:
{
lean_object* v___x_874_; lean_object* v___x_875_; 
v___x_874_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg___closed__0);
v___x_875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_875_, 0, v___x_874_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg___boxed(lean_object* v___y_876_){
_start:
{
lean_object* v_res_877_; 
v_res_877_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg();
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0(lean_object* v_00_u03b1_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_){
_start:
{
lean_object* v___x_888_; 
v___x_888_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg();
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___boxed(lean_object* v_00_u03b1_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0(v_00_u03b1_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___redArg___lam__0(lean_object* v_x_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_){
_start:
{
lean_object* v___x_910_; 
lean_inc(v___y_904_);
lean_inc_ref(v___y_903_);
lean_inc(v___y_902_);
lean_inc_ref(v___y_901_);
v___x_910_ = lean_apply_9(v_x_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, lean_box(0));
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___redArg___lam__0___boxed(lean_object* v_x_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___redArg___lam__0(v_x_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_);
lean_dec(v___y_915_);
lean_dec_ref(v___y_914_);
lean_dec(v___y_913_);
lean_dec_ref(v___y_912_);
return v_res_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___redArg(lean_object* v_mvarId_922_, lean_object* v_x_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_){
_start:
{
lean_object* v___f_933_; lean_object* v___x_934_; 
lean_inc(v___y_927_);
lean_inc_ref(v___y_926_);
lean_inc(v___y_925_);
lean_inc_ref(v___y_924_);
v___f_933_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_933_, 0, v_x_923_);
lean_closure_set(v___f_933_, 1, v___y_924_);
lean_closure_set(v___f_933_, 2, v___y_925_);
lean_closure_set(v___f_933_, 3, v___y_926_);
lean_closure_set(v___f_933_, 4, v___y_927_);
v___x_934_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_922_, v___f_933_, v___y_928_, v___y_929_, v___y_930_, v___y_931_);
if (lean_obj_tag(v___x_934_) == 0)
{
return v___x_934_;
}
else
{
lean_object* v_a_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_942_; 
v_a_935_ = lean_ctor_get(v___x_934_, 0);
v_isSharedCheck_942_ = !lean_is_exclusive(v___x_934_);
if (v_isSharedCheck_942_ == 0)
{
v___x_937_ = v___x_934_;
v_isShared_938_ = v_isSharedCheck_942_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_a_935_);
lean_dec(v___x_934_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_942_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
lean_object* v___x_940_; 
if (v_isShared_938_ == 0)
{
v___x_940_ = v___x_937_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v_a_935_);
v___x_940_ = v_reuseFailAlloc_941_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
return v___x_940_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___redArg___boxed(lean_object* v_mvarId_943_, lean_object* v_x_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_){
_start:
{
lean_object* v_res_954_; 
v_res_954_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___redArg(v_mvarId_943_, v_x_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_);
lean_dec(v___y_952_);
lean_dec_ref(v___y_951_);
lean_dec(v___y_950_);
lean_dec_ref(v___y_949_);
lean_dec(v___y_948_);
lean_dec_ref(v___y_947_);
lean_dec(v___y_946_);
lean_dec_ref(v___y_945_);
return v_res_954_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3(lean_object* v_00_u03b1_955_, lean_object* v_mvarId_956_, lean_object* v_x_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_){
_start:
{
lean_object* v___x_967_; 
v___x_967_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___redArg(v_mvarId_956_, v_x_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___boxed(lean_object* v_00_u03b1_968_, lean_object* v_mvarId_969_, lean_object* v_x_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3(v_00_u03b1_968_, v_mvarId_969_, v_x_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_);
lean_dec(v___y_978_);
lean_dec_ref(v___y_977_);
lean_dec(v___y_976_);
lean_dec_ref(v___y_975_);
lean_dec(v___y_974_);
lean_dec_ref(v___y_973_);
lean_dec(v___y_972_);
lean_dec_ref(v___y_971_);
return v_res_980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevert___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__4(lean_object* v_goal_988_, lean_object* v_ref_989_, lean_object* v_k_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_){
_start:
{
lean_object* v___x_1000_; 
lean_inc_ref(v_goal_988_);
v___x_1000_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo(v_goal_988_, v_ref_989_, v___y_995_, v___y_996_, v___y_997_, v___y_998_);
if (lean_obj_tag(v___x_1000_) == 0)
{
lean_object* v_a_1001_; lean_object* v_u_1002_; lean_object* v_00_u03c3s_1003_; lean_object* v_hyps_1004_; lean_object* v_target_1005_; lean_object* v___x_1007_; uint8_t v_isShared_1008_; uint8_t v_isSharedCheck_1032_; 
v_a_1001_ = lean_ctor_get(v___x_1000_, 0);
lean_inc(v_a_1001_);
lean_dec_ref(v___x_1000_);
v_u_1002_ = lean_ctor_get(v_goal_988_, 0);
v_00_u03c3s_1003_ = lean_ctor_get(v_goal_988_, 1);
v_hyps_1004_ = lean_ctor_get(v_goal_988_, 2);
v_target_1005_ = lean_ctor_get(v_goal_988_, 3);
v_isSharedCheck_1032_ = !lean_is_exclusive(v_goal_988_);
if (v_isSharedCheck_1032_ == 0)
{
v___x_1007_ = v_goal_988_;
v_isShared_1008_ = v_isSharedCheck_1032_;
goto v_resetjp_1006_;
}
else
{
lean_inc(v_target_1005_);
lean_inc(v_hyps_1004_);
lean_inc(v_00_u03c3s_1003_);
lean_inc(v_u_1002_);
lean_dec(v_goal_988_);
v___x_1007_ = lean_box(0);
v_isShared_1008_ = v_isSharedCheck_1032_;
goto v_resetjp_1006_;
}
v_resetjp_1006_:
{
lean_object* v_focusHyp_1009_; lean_object* v_restHyps_1010_; lean_object* v_proof_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1018_; 
v_focusHyp_1009_ = lean_ctor_get(v_a_1001_, 0);
lean_inc_ref(v_focusHyp_1009_);
v_restHyps_1010_ = lean_ctor_get(v_a_1001_, 1);
lean_inc_ref(v_restHyps_1010_);
v_proof_1011_ = lean_ctor_get(v_a_1001_, 2);
lean_inc_ref(v_proof_1011_);
lean_dec(v_a_1001_);
v___x_1012_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__4));
v___x_1013_ = lean_box(0);
lean_inc(v_u_1002_);
v___x_1014_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1014_, 0, v_u_1002_);
lean_ctor_set(v___x_1014_, 1, v___x_1013_);
lean_inc_ref(v___x_1014_);
v___x_1015_ = l_Lean_mkConst(v___x_1012_, v___x_1014_);
lean_inc_ref(v_target_1005_);
lean_inc_ref(v_focusHyp_1009_);
lean_inc_ref(v_00_u03c3s_1003_);
v___x_1016_ = l_Lean_mkApp3(v___x_1015_, v_00_u03c3s_1003_, v_focusHyp_1009_, v_target_1005_);
lean_inc_ref(v_restHyps_1010_);
lean_inc_ref(v_00_u03c3s_1003_);
if (v_isShared_1008_ == 0)
{
lean_ctor_set(v___x_1007_, 3, v___x_1016_);
lean_ctor_set(v___x_1007_, 2, v_restHyps_1010_);
v___x_1018_ = v___x_1007_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v_u_1002_);
lean_ctor_set(v_reuseFailAlloc_1031_, 1, v_00_u03c3s_1003_);
lean_ctor_set(v_reuseFailAlloc_1031_, 2, v_restHyps_1010_);
lean_ctor_set(v_reuseFailAlloc_1031_, 3, v___x_1016_);
v___x_1018_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
lean_object* v___x_1019_; 
lean_inc(v___y_998_);
lean_inc_ref(v___y_997_);
lean_inc(v___y_996_);
lean_inc_ref(v___y_995_);
lean_inc(v___y_994_);
lean_inc_ref(v___y_993_);
lean_inc(v___y_992_);
lean_inc_ref(v___y_991_);
v___x_1019_ = lean_apply_10(v_k_990_, v___x_1018_, v___y_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, lean_box(0));
if (lean_obj_tag(v___x_1019_) == 0)
{
lean_object* v_a_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1030_; 
v_a_1020_ = lean_ctor_get(v___x_1019_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_1019_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1022_ = v___x_1019_;
v_isShared_1023_ = v_isSharedCheck_1030_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_a_1020_);
lean_dec(v___x_1019_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1030_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v_prf_1026_; lean_object* v___x_1028_; 
v___x_1024_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__4___closed__0));
v___x_1025_ = l_Lean_mkConst(v___x_1024_, v___x_1014_);
v_prf_1026_ = l_Lean_mkApp7(v___x_1025_, v_00_u03c3s_1003_, v_hyps_1004_, v_restHyps_1010_, v_focusHyp_1009_, v_target_1005_, v_proof_1011_, v_a_1020_);
if (v_isShared_1023_ == 0)
{
lean_ctor_set(v___x_1022_, 0, v_prf_1026_);
v___x_1028_ = v___x_1022_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_prf_1026_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
return v___x_1028_;
}
}
}
else
{
lean_dec_ref(v___x_1014_);
lean_dec_ref(v_proof_1011_);
lean_dec_ref(v_restHyps_1010_);
lean_dec_ref(v_focusHyp_1009_);
lean_dec_ref(v_target_1005_);
lean_dec_ref(v_hyps_1004_);
lean_dec_ref(v_00_u03c3s_1003_);
return v___x_1019_;
}
}
}
}
else
{
lean_object* v_a_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1040_; 
lean_dec_ref(v_k_990_);
lean_dec_ref(v_goal_988_);
v_a_1033_ = lean_ctor_get(v___x_1000_, 0);
v_isSharedCheck_1040_ = !lean_is_exclusive(v___x_1000_);
if (v_isSharedCheck_1040_ == 0)
{
v___x_1035_ = v___x_1000_;
v_isShared_1036_ = v_isSharedCheck_1040_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_a_1033_);
lean_dec(v___x_1000_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1040_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
lean_object* v___x_1038_; 
if (v_isShared_1036_ == 0)
{
v___x_1038_ = v___x_1035_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v_a_1033_);
v___x_1038_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
return v___x_1038_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevert___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__4___boxed(lean_object* v_goal_1041_, lean_object* v_ref_1042_, lean_object* v_k_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_){
_start:
{
lean_object* v_res_1053_; 
v_res_1053_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevert___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__4(v_goal_1041_, v_ref_1042_, v_k_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_);
lean_dec(v___y_1051_);
lean_dec_ref(v___y_1050_);
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
lean_dec(v___y_1047_);
lean_dec_ref(v___y_1046_);
lean_dec(v___y_1045_);
lean_dec_ref(v___y_1044_);
return v_res_1053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__0(lean_object* v_val_1054_, lean_object* v_newGoal_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_){
_start:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1065_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v_newGoal_1055_);
v___x_1066_ = lean_box(0);
v___x_1067_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_1065_, v___x_1066_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_);
if (lean_obj_tag(v___x_1067_) == 0)
{
lean_object* v_a_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1079_; 
v_a_1068_ = lean_ctor_get(v___x_1067_, 0);
v_isSharedCheck_1079_ = !lean_is_exclusive(v___x_1067_);
if (v_isSharedCheck_1079_ == 0)
{
v___x_1070_ = v___x_1067_;
v_isShared_1071_ = v_isSharedCheck_1079_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_a_1068_);
lean_dec(v___x_1067_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1079_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1077_; 
v___x_1072_ = lean_st_ref_take(v_val_1054_);
v___x_1073_ = l_Lean_Expr_mvarId_x21(v_a_1068_);
v___x_1074_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1073_);
lean_ctor_set(v___x_1074_, 1, v___x_1072_);
v___x_1075_ = lean_st_ref_set(v_val_1054_, v___x_1074_);
if (v_isShared_1071_ == 0)
{
v___x_1077_ = v___x_1070_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v_a_1068_);
v___x_1077_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
return v___x_1077_;
}
}
}
else
{
return v___x_1067_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__0___boxed(lean_object* v_val_1080_, lean_object* v_newGoal_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_){
_start:
{
lean_object* v_res_1091_; 
v_res_1091_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__0(v_val_1080_, v_newGoal_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_);
lean_dec(v___y_1089_);
lean_dec_ref(v___y_1088_);
lean_dec(v___y_1087_);
lean_dec_ref(v___y_1086_);
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1084_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1082_);
lean_dec(v_val_1080_);
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15_spec__20_spec__22___redArg(lean_object* v_x_1092_, lean_object* v_x_1093_, lean_object* v_x_1094_, lean_object* v_x_1095_){
_start:
{
lean_object* v_ks_1096_; lean_object* v_vs_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1121_; 
v_ks_1096_ = lean_ctor_get(v_x_1092_, 0);
v_vs_1097_ = lean_ctor_get(v_x_1092_, 1);
v_isSharedCheck_1121_ = !lean_is_exclusive(v_x_1092_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1099_ = v_x_1092_;
v_isShared_1100_ = v_isSharedCheck_1121_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_vs_1097_);
lean_inc(v_ks_1096_);
lean_dec(v_x_1092_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1121_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v___x_1101_; uint8_t v___x_1102_; 
v___x_1101_ = lean_array_get_size(v_ks_1096_);
v___x_1102_ = lean_nat_dec_lt(v_x_1093_, v___x_1101_);
if (v___x_1102_ == 0)
{
lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1106_; 
lean_dec(v_x_1093_);
v___x_1103_ = lean_array_push(v_ks_1096_, v_x_1094_);
v___x_1104_ = lean_array_push(v_vs_1097_, v_x_1095_);
if (v_isShared_1100_ == 0)
{
lean_ctor_set(v___x_1099_, 1, v___x_1104_);
lean_ctor_set(v___x_1099_, 0, v___x_1103_);
v___x_1106_ = v___x_1099_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v___x_1103_);
lean_ctor_set(v_reuseFailAlloc_1107_, 1, v___x_1104_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
return v___x_1106_;
}
}
else
{
lean_object* v_k_x27_1108_; uint8_t v___x_1109_; 
v_k_x27_1108_ = lean_array_fget_borrowed(v_ks_1096_, v_x_1093_);
v___x_1109_ = l_Lean_instBEqMVarId_beq(v_x_1094_, v_k_x27_1108_);
if (v___x_1109_ == 0)
{
lean_object* v___x_1111_; 
if (v_isShared_1100_ == 0)
{
v___x_1111_ = v___x_1099_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v_ks_1096_);
lean_ctor_set(v_reuseFailAlloc_1115_, 1, v_vs_1097_);
v___x_1111_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1112_ = lean_unsigned_to_nat(1u);
v___x_1113_ = lean_nat_add(v_x_1093_, v___x_1112_);
lean_dec(v_x_1093_);
v_x_1092_ = v___x_1111_;
v_x_1093_ = v___x_1113_;
goto _start;
}
}
else
{
lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1119_; 
v___x_1116_ = lean_array_fset(v_ks_1096_, v_x_1093_, v_x_1094_);
v___x_1117_ = lean_array_fset(v_vs_1097_, v_x_1093_, v_x_1095_);
lean_dec(v_x_1093_);
if (v_isShared_1100_ == 0)
{
lean_ctor_set(v___x_1099_, 1, v___x_1117_);
lean_ctor_set(v___x_1099_, 0, v___x_1116_);
v___x_1119_ = v___x_1099_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v___x_1116_);
lean_ctor_set(v_reuseFailAlloc_1120_, 1, v___x_1117_);
v___x_1119_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
return v___x_1119_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15_spec__20___redArg(lean_object* v_n_1122_, lean_object* v_k_1123_, lean_object* v_v_1124_){
_start:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1125_ = lean_unsigned_to_nat(0u);
v___x_1126_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15_spec__20_spec__22___redArg(v_n_1122_, v___x_1125_, v_k_1123_, v_v_1124_);
return v___x_1126_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15___redArg___closed__0(void){
_start:
{
size_t v___x_1127_; size_t v___x_1128_; size_t v___x_1129_; 
v___x_1127_ = ((size_t)5ULL);
v___x_1128_ = ((size_t)1ULL);
v___x_1129_ = lean_usize_shift_left(v___x_1128_, v___x_1127_);
return v___x_1129_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15___redArg___closed__1(void){
_start:
{
size_t v___x_1130_; size_t v___x_1131_; size_t v___x_1132_; 
v___x_1130_ = ((size_t)1ULL);
v___x_1131_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15___redArg___closed__0);
v___x_1132_ = lean_usize_sub(v___x_1131_, v___x_1130_);
return v___x_1132_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15___redArg___closed__2(void){
_start:
{
lean_object* v___x_1133_; 
v___x_1133_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15___redArg(lean_object* v_x_1134_, size_t v_x_1135_, size_t v_x_1136_, lean_object* v_x_1137_, lean_object* v_x_1138_){
_start:
{
if (lean_obj_tag(v_x_1134_) == 0)
{
lean_object* v_es_1139_; size_t v___x_1140_; size_t v___x_1141_; size_t v___x_1142_; size_t v___x_1143_; lean_object* v_j_1144_; lean_object* v___x_1145_; uint8_t v___x_1146_; 
v_es_1139_ = lean_ctor_get(v_x_1134_, 0);
v___x_1140_ = ((size_t)5ULL);
v___x_1141_ = ((size_t)1ULL);
v___x_1142_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15___redArg___closed__1);
v___x_1143_ = lean_usize_land(v_x_1135_, v___x_1142_);
v_j_1144_ = lean_usize_to_nat(v___x_1143_);
v___x_1145_ = lean_array_get_size(v_es_1139_);
v___x_1146_ = lean_nat_dec_lt(v_j_1144_, v___x_1145_);
if (v___x_1146_ == 0)
{
lean_dec(v_j_1144_);
lean_dec(v_x_1138_);
lean_dec(v_x_1137_);
return v_x_1134_;
}
else
{
lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1183_; 
lean_inc_ref(v_es_1139_);
v_isSharedCheck_1183_ = !lean_is_exclusive(v_x_1134_);
if (v_isSharedCheck_1183_ == 0)
{
lean_object* v_unused_1184_; 
v_unused_1184_ = lean_ctor_get(v_x_1134_, 0);
lean_dec(v_unused_1184_);
v___x_1148_ = v_x_1134_;
v_isShared_1149_ = v_isSharedCheck_1183_;
goto v_resetjp_1147_;
}
else
{
lean_dec(v_x_1134_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1183_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v_v_1150_; lean_object* v___x_1151_; lean_object* v_xs_x27_1152_; lean_object* v___y_1154_; 
v_v_1150_ = lean_array_fget(v_es_1139_, v_j_1144_);
v___x_1151_ = lean_box(0);
v_xs_x27_1152_ = lean_array_fset(v_es_1139_, v_j_1144_, v___x_1151_);
switch(lean_obj_tag(v_v_1150_))
{
case 0:
{
lean_object* v_key_1159_; lean_object* v_val_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1170_; 
v_key_1159_ = lean_ctor_get(v_v_1150_, 0);
v_val_1160_ = lean_ctor_get(v_v_1150_, 1);
v_isSharedCheck_1170_ = !lean_is_exclusive(v_v_1150_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1162_ = v_v_1150_;
v_isShared_1163_ = v_isSharedCheck_1170_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_val_1160_);
lean_inc(v_key_1159_);
lean_dec(v_v_1150_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1170_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
uint8_t v___x_1164_; 
v___x_1164_ = l_Lean_instBEqMVarId_beq(v_x_1137_, v_key_1159_);
if (v___x_1164_ == 0)
{
lean_object* v___x_1165_; lean_object* v___x_1166_; 
lean_del_object(v___x_1162_);
v___x_1165_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1159_, v_val_1160_, v_x_1137_, v_x_1138_);
v___x_1166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1166_, 0, v___x_1165_);
v___y_1154_ = v___x_1166_;
goto v___jp_1153_;
}
else
{
lean_object* v___x_1168_; 
lean_dec(v_val_1160_);
lean_dec(v_key_1159_);
if (v_isShared_1163_ == 0)
{
lean_ctor_set(v___x_1162_, 1, v_x_1138_);
lean_ctor_set(v___x_1162_, 0, v_x_1137_);
v___x_1168_ = v___x_1162_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v_x_1137_);
lean_ctor_set(v_reuseFailAlloc_1169_, 1, v_x_1138_);
v___x_1168_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
v___y_1154_ = v___x_1168_;
goto v___jp_1153_;
}
}
}
}
case 1:
{
lean_object* v_node_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1181_; 
v_node_1171_ = lean_ctor_get(v_v_1150_, 0);
v_isSharedCheck_1181_ = !lean_is_exclusive(v_v_1150_);
if (v_isSharedCheck_1181_ == 0)
{
v___x_1173_ = v_v_1150_;
v_isShared_1174_ = v_isSharedCheck_1181_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_node_1171_);
lean_dec(v_v_1150_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1181_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
size_t v___x_1175_; size_t v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1179_; 
v___x_1175_ = lean_usize_shift_right(v_x_1135_, v___x_1140_);
v___x_1176_ = lean_usize_add(v_x_1136_, v___x_1141_);
v___x_1177_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15___redArg(v_node_1171_, v___x_1175_, v___x_1176_, v_x_1137_, v_x_1138_);
if (v_isShared_1174_ == 0)
{
lean_ctor_set(v___x_1173_, 0, v___x_1177_);
v___x_1179_ = v___x_1173_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v___x_1177_);
v___x_1179_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
v___y_1154_ = v___x_1179_;
goto v___jp_1153_;
}
}
}
default: 
{
lean_object* v___x_1182_; 
v___x_1182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1182_, 0, v_x_1137_);
lean_ctor_set(v___x_1182_, 1, v_x_1138_);
v___y_1154_ = v___x_1182_;
goto v___jp_1153_;
}
}
v___jp_1153_:
{
lean_object* v___x_1155_; lean_object* v___x_1157_; 
v___x_1155_ = lean_array_fset(v_xs_x27_1152_, v_j_1144_, v___y_1154_);
lean_dec(v_j_1144_);
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 0, v___x_1155_);
v___x_1157_ = v___x_1148_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v___x_1155_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
}
}
}
else
{
lean_object* v_ks_1185_; lean_object* v_vs_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1206_; 
v_ks_1185_ = lean_ctor_get(v_x_1134_, 0);
v_vs_1186_ = lean_ctor_get(v_x_1134_, 1);
v_isSharedCheck_1206_ = !lean_is_exclusive(v_x_1134_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_1188_ = v_x_1134_;
v_isShared_1189_ = v_isSharedCheck_1206_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_vs_1186_);
lean_inc(v_ks_1185_);
lean_dec(v_x_1134_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1206_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___x_1191_; 
if (v_isShared_1189_ == 0)
{
v___x_1191_ = v___x_1188_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v_ks_1185_);
lean_ctor_set(v_reuseFailAlloc_1205_, 1, v_vs_1186_);
v___x_1191_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
lean_object* v_newNode_1192_; uint8_t v___y_1194_; size_t v___x_1200_; uint8_t v___x_1201_; 
v_newNode_1192_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15_spec__20___redArg(v___x_1191_, v_x_1137_, v_x_1138_);
v___x_1200_ = ((size_t)7ULL);
v___x_1201_ = lean_usize_dec_le(v___x_1200_, v_x_1136_);
if (v___x_1201_ == 0)
{
lean_object* v___x_1202_; lean_object* v___x_1203_; uint8_t v___x_1204_; 
v___x_1202_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1192_);
v___x_1203_ = lean_unsigned_to_nat(4u);
v___x_1204_ = lean_nat_dec_lt(v___x_1202_, v___x_1203_);
lean_dec(v___x_1202_);
v___y_1194_ = v___x_1204_;
goto v___jp_1193_;
}
else
{
v___y_1194_ = v___x_1201_;
goto v___jp_1193_;
}
v___jp_1193_:
{
if (v___y_1194_ == 0)
{
lean_object* v_ks_1195_; lean_object* v_vs_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; 
v_ks_1195_ = lean_ctor_get(v_newNode_1192_, 0);
lean_inc_ref(v_ks_1195_);
v_vs_1196_ = lean_ctor_get(v_newNode_1192_, 1);
lean_inc_ref(v_vs_1196_);
lean_dec_ref(v_newNode_1192_);
v___x_1197_ = lean_unsigned_to_nat(0u);
v___x_1198_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15___redArg___closed__2);
v___x_1199_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15_spec__21___redArg(v_x_1136_, v_ks_1195_, v_vs_1196_, v___x_1197_, v___x_1198_);
lean_dec_ref(v_vs_1196_);
lean_dec_ref(v_ks_1195_);
return v___x_1199_;
}
else
{
return v_newNode_1192_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15_spec__21___redArg(size_t v_depth_1207_, lean_object* v_keys_1208_, lean_object* v_vals_1209_, lean_object* v_i_1210_, lean_object* v_entries_1211_){
_start:
{
lean_object* v___x_1212_; uint8_t v___x_1213_; 
v___x_1212_ = lean_array_get_size(v_keys_1208_);
v___x_1213_ = lean_nat_dec_lt(v_i_1210_, v___x_1212_);
if (v___x_1213_ == 0)
{
lean_dec(v_i_1210_);
return v_entries_1211_;
}
else
{
lean_object* v_k_1214_; lean_object* v_v_1215_; uint64_t v___x_1216_; size_t v_h_1217_; size_t v___x_1218_; lean_object* v___x_1219_; size_t v___x_1220_; size_t v___x_1221_; size_t v___x_1222_; size_t v_h_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; 
v_k_1214_ = lean_array_fget_borrowed(v_keys_1208_, v_i_1210_);
v_v_1215_ = lean_array_fget_borrowed(v_vals_1209_, v_i_1210_);
v___x_1216_ = l_Lean_instHashableMVarId_hash(v_k_1214_);
v_h_1217_ = lean_uint64_to_usize(v___x_1216_);
v___x_1218_ = ((size_t)5ULL);
v___x_1219_ = lean_unsigned_to_nat(1u);
v___x_1220_ = ((size_t)1ULL);
v___x_1221_ = lean_usize_sub(v_depth_1207_, v___x_1220_);
v___x_1222_ = lean_usize_mul(v___x_1218_, v___x_1221_);
v_h_1223_ = lean_usize_shift_right(v_h_1217_, v___x_1222_);
v___x_1224_ = lean_nat_add(v_i_1210_, v___x_1219_);
lean_dec(v_i_1210_);
lean_inc(v_v_1215_);
lean_inc(v_k_1214_);
v___x_1225_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15___redArg(v_entries_1211_, v_h_1223_, v_depth_1207_, v_k_1214_, v_v_1215_);
v_i_1210_ = v___x_1224_;
v_entries_1211_ = v___x_1225_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15_spec__21___redArg___boxed(lean_object* v_depth_1227_, lean_object* v_keys_1228_, lean_object* v_vals_1229_, lean_object* v_i_1230_, lean_object* v_entries_1231_){
_start:
{
size_t v_depth_boxed_1232_; lean_object* v_res_1233_; 
v_depth_boxed_1232_ = lean_unbox_usize(v_depth_1227_);
lean_dec(v_depth_1227_);
v_res_1233_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15_spec__21___redArg(v_depth_boxed_1232_, v_keys_1228_, v_vals_1229_, v_i_1230_, v_entries_1231_);
lean_dec_ref(v_vals_1229_);
lean_dec_ref(v_keys_1228_);
return v_res_1233_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15___redArg___boxed(lean_object* v_x_1234_, lean_object* v_x_1235_, lean_object* v_x_1236_, lean_object* v_x_1237_, lean_object* v_x_1238_){
_start:
{
size_t v_x_20362__boxed_1239_; size_t v_x_20363__boxed_1240_; lean_object* v_res_1241_; 
v_x_20362__boxed_1239_ = lean_unbox_usize(v_x_1235_);
lean_dec(v_x_1235_);
v_x_20363__boxed_1240_ = lean_unbox_usize(v_x_1236_);
lean_dec(v_x_1236_);
v_res_1241_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15___redArg(v_x_1234_, v_x_20362__boxed_1239_, v_x_20363__boxed_1240_, v_x_1237_, v_x_1238_);
return v_res_1241_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10___redArg(lean_object* v_x_1242_, lean_object* v_x_1243_, lean_object* v_x_1244_){
_start:
{
uint64_t v___x_1245_; size_t v___x_1246_; size_t v___x_1247_; lean_object* v___x_1248_; 
v___x_1245_ = l_Lean_instHashableMVarId_hash(v_x_1243_);
v___x_1246_ = lean_uint64_to_usize(v___x_1245_);
v___x_1247_ = ((size_t)1ULL);
v___x_1248_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15___redArg(v_x_1242_, v___x_1246_, v___x_1247_, v_x_1243_, v_x_1244_);
return v___x_1248_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2___redArg(lean_object* v_mvarId_1249_, lean_object* v_val_1250_, lean_object* v___y_1251_){
_start:
{
lean_object* v___x_1253_; lean_object* v_mctx_1254_; lean_object* v_cache_1255_; lean_object* v_zetaDeltaFVarIds_1256_; lean_object* v_postponed_1257_; lean_object* v_diag_1258_; lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1285_; 
v___x_1253_ = lean_st_ref_take(v___y_1251_);
v_mctx_1254_ = lean_ctor_get(v___x_1253_, 0);
v_cache_1255_ = lean_ctor_get(v___x_1253_, 1);
v_zetaDeltaFVarIds_1256_ = lean_ctor_get(v___x_1253_, 2);
v_postponed_1257_ = lean_ctor_get(v___x_1253_, 3);
v_diag_1258_ = lean_ctor_get(v___x_1253_, 4);
v_isSharedCheck_1285_ = !lean_is_exclusive(v___x_1253_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1260_ = v___x_1253_;
v_isShared_1261_ = v_isSharedCheck_1285_;
goto v_resetjp_1259_;
}
else
{
lean_inc(v_diag_1258_);
lean_inc(v_postponed_1257_);
lean_inc(v_zetaDeltaFVarIds_1256_);
lean_inc(v_cache_1255_);
lean_inc(v_mctx_1254_);
lean_dec(v___x_1253_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1285_;
goto v_resetjp_1259_;
}
v_resetjp_1259_:
{
lean_object* v_depth_1262_; lean_object* v_levelAssignDepth_1263_; lean_object* v_mvarCounter_1264_; lean_object* v_lDepth_1265_; lean_object* v_decls_1266_; lean_object* v_userNames_1267_; lean_object* v_lAssignment_1268_; lean_object* v_eAssignment_1269_; lean_object* v_dAssignment_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1284_; 
v_depth_1262_ = lean_ctor_get(v_mctx_1254_, 0);
v_levelAssignDepth_1263_ = lean_ctor_get(v_mctx_1254_, 1);
v_mvarCounter_1264_ = lean_ctor_get(v_mctx_1254_, 2);
v_lDepth_1265_ = lean_ctor_get(v_mctx_1254_, 3);
v_decls_1266_ = lean_ctor_get(v_mctx_1254_, 4);
v_userNames_1267_ = lean_ctor_get(v_mctx_1254_, 5);
v_lAssignment_1268_ = lean_ctor_get(v_mctx_1254_, 6);
v_eAssignment_1269_ = lean_ctor_get(v_mctx_1254_, 7);
v_dAssignment_1270_ = lean_ctor_get(v_mctx_1254_, 8);
v_isSharedCheck_1284_ = !lean_is_exclusive(v_mctx_1254_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1272_ = v_mctx_1254_;
v_isShared_1273_ = v_isSharedCheck_1284_;
goto v_resetjp_1271_;
}
else
{
lean_inc(v_dAssignment_1270_);
lean_inc(v_eAssignment_1269_);
lean_inc(v_lAssignment_1268_);
lean_inc(v_userNames_1267_);
lean_inc(v_decls_1266_);
lean_inc(v_lDepth_1265_);
lean_inc(v_mvarCounter_1264_);
lean_inc(v_levelAssignDepth_1263_);
lean_inc(v_depth_1262_);
lean_dec(v_mctx_1254_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1284_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
lean_object* v___x_1274_; lean_object* v___x_1276_; 
v___x_1274_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10___redArg(v_eAssignment_1269_, v_mvarId_1249_, v_val_1250_);
if (v_isShared_1273_ == 0)
{
lean_ctor_set(v___x_1272_, 7, v___x_1274_);
v___x_1276_ = v___x_1272_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v_depth_1262_);
lean_ctor_set(v_reuseFailAlloc_1283_, 1, v_levelAssignDepth_1263_);
lean_ctor_set(v_reuseFailAlloc_1283_, 2, v_mvarCounter_1264_);
lean_ctor_set(v_reuseFailAlloc_1283_, 3, v_lDepth_1265_);
lean_ctor_set(v_reuseFailAlloc_1283_, 4, v_decls_1266_);
lean_ctor_set(v_reuseFailAlloc_1283_, 5, v_userNames_1267_);
lean_ctor_set(v_reuseFailAlloc_1283_, 6, v_lAssignment_1268_);
lean_ctor_set(v_reuseFailAlloc_1283_, 7, v___x_1274_);
lean_ctor_set(v_reuseFailAlloc_1283_, 8, v_dAssignment_1270_);
v___x_1276_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
lean_object* v___x_1278_; 
if (v_isShared_1261_ == 0)
{
lean_ctor_set(v___x_1260_, 0, v___x_1276_);
v___x_1278_ = v___x_1260_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v___x_1276_);
lean_ctor_set(v_reuseFailAlloc_1282_, 1, v_cache_1255_);
lean_ctor_set(v_reuseFailAlloc_1282_, 2, v_zetaDeltaFVarIds_1256_);
lean_ctor_set(v_reuseFailAlloc_1282_, 3, v_postponed_1257_);
lean_ctor_set(v_reuseFailAlloc_1282_, 4, v_diag_1258_);
v___x_1278_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; 
v___x_1279_ = lean_st_ref_set(v___y_1251_, v___x_1278_);
v___x_1280_ = lean_box(0);
v___x_1281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1281_, 0, v___x_1280_);
return v___x_1281_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2___redArg___boxed(lean_object* v_mvarId_1286_, lean_object* v_val_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_){
_start:
{
lean_object* v_res_1290_; 
v_res_1290_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2___redArg(v_mvarId_1286_, v_val_1287_, v___y_1288_);
lean_dec(v___y_1288_);
return v_res_1290_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__4___redArg(lean_object* v_as_1291_, lean_object* v_i_1292_, lean_object* v_j_1293_, lean_object* v_bs_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_){
_start:
{
lean_object* v_zero_1298_; uint8_t v_isZero_1299_; 
v_zero_1298_ = lean_unsigned_to_nat(0u);
v_isZero_1299_ = lean_nat_dec_eq(v_i_1292_, v_zero_1298_);
if (v_isZero_1299_ == 1)
{
lean_object* v___x_1300_; 
lean_dec(v_j_1293_);
lean_dec(v_i_1292_);
v___x_1300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1300_, 0, v_bs_1294_);
return v___x_1300_;
}
else
{
lean_object* v___x_1301_; lean_object* v___x_1302_; 
v___x_1301_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__6___closed__1));
v___x_1302_ = l_Lean_Core_mkFreshUserName(v___x_1301_, v___y_1295_, v___y_1296_);
if (lean_obj_tag(v___x_1302_) == 0)
{
lean_object* v_a_1303_; lean_object* v_one_1304_; lean_object* v_n_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; 
v_a_1303_ = lean_ctor_get(v___x_1302_, 0);
lean_inc(v_a_1303_);
lean_dec_ref(v___x_1302_);
v_one_1304_ = lean_unsigned_to_nat(1u);
v_n_1305_ = lean_nat_sub(v_i_1292_, v_one_1304_);
lean_dec(v_i_1292_);
v___x_1306_ = lean_array_fget_borrowed(v_as_1291_, v_j_1293_);
v___x_1307_ = lean_nat_add(v_j_1293_, v_one_1304_);
lean_dec(v_j_1293_);
lean_inc(v___x_1307_);
v___x_1308_ = lean_name_append_index_after(v_a_1303_, v___x_1307_);
lean_inc(v___x_1306_);
v___x_1309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1309_, 0, v___x_1308_);
lean_ctor_set(v___x_1309_, 1, v___x_1306_);
v___x_1310_ = lean_array_push(v_bs_1294_, v___x_1309_);
v_i_1292_ = v_n_1305_;
v_j_1293_ = v___x_1307_;
v_bs_1294_ = v___x_1310_;
goto _start;
}
else
{
lean_object* v_a_1312_; lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1319_; 
lean_dec_ref(v_bs_1294_);
lean_dec(v_j_1293_);
lean_dec(v_i_1292_);
v_a_1312_ = lean_ctor_get(v___x_1302_, 0);
v_isSharedCheck_1319_ = !lean_is_exclusive(v___x_1302_);
if (v_isSharedCheck_1319_ == 0)
{
v___x_1314_ = v___x_1302_;
v_isShared_1315_ = v_isSharedCheck_1319_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_a_1312_);
lean_dec(v___x_1302_);
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
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__4___redArg___boxed(lean_object* v_as_1320_, lean_object* v_i_1321_, lean_object* v_j_1322_, lean_object* v_bs_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_){
_start:
{
lean_object* v_res_1327_; 
v_res_1327_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__4___redArg(v_as_1320_, v_i_1321_, v_j_1322_, v_bs_1323_, v___y_1324_, v___y_1325_);
lean_dec(v___y_1325_);
lean_dec_ref(v___y_1324_);
lean_dec_ref(v_as_1320_);
return v_res_1327_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5_spec__14(lean_object* v_msgData_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_){
_start:
{
lean_object* v___x_1334_; lean_object* v_env_1335_; lean_object* v___x_1336_; lean_object* v_mctx_1337_; lean_object* v_lctx_1338_; lean_object* v_options_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; 
v___x_1334_ = lean_st_ref_get(v___y_1332_);
v_env_1335_ = lean_ctor_get(v___x_1334_, 0);
lean_inc_ref(v_env_1335_);
lean_dec(v___x_1334_);
v___x_1336_ = lean_st_ref_get(v___y_1330_);
v_mctx_1337_ = lean_ctor_get(v___x_1336_, 0);
lean_inc_ref(v_mctx_1337_);
lean_dec(v___x_1336_);
v_lctx_1338_ = lean_ctor_get(v___y_1329_, 2);
v_options_1339_ = lean_ctor_get(v___y_1331_, 2);
lean_inc_ref(v_options_1339_);
lean_inc_ref(v_lctx_1338_);
v___x_1340_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1340_, 0, v_env_1335_);
lean_ctor_set(v___x_1340_, 1, v_mctx_1337_);
lean_ctor_set(v___x_1340_, 2, v_lctx_1338_);
lean_ctor_set(v___x_1340_, 3, v_options_1339_);
v___x_1341_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1341_, 0, v___x_1340_);
lean_ctor_set(v___x_1341_, 1, v_msgData_1328_);
v___x_1342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1342_, 0, v___x_1341_);
return v___x_1342_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5_spec__14___boxed(lean_object* v_msgData_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_){
_start:
{
lean_object* v_res_1349_; 
v_res_1349_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5_spec__14(v_msgData_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_);
lean_dec(v___y_1347_);
lean_dec_ref(v___y_1346_);
lean_dec(v___y_1345_);
lean_dec_ref(v___y_1344_);
return v_res_1349_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__8___redArg(lean_object* v_msg_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_){
_start:
{
lean_object* v_ref_1356_; lean_object* v___x_1357_; lean_object* v_a_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1366_; 
v_ref_1356_ = lean_ctor_get(v___y_1353_, 5);
v___x_1357_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5_spec__14(v_msg_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_);
v_a_1358_ = lean_ctor_get(v___x_1357_, 0);
v_isSharedCheck_1366_ = !lean_is_exclusive(v___x_1357_);
if (v_isSharedCheck_1366_ == 0)
{
v___x_1360_ = v___x_1357_;
v_isShared_1361_ = v_isSharedCheck_1366_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_a_1358_);
lean_dec(v___x_1357_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1366_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
lean_object* v___x_1362_; lean_object* v___x_1364_; 
lean_inc(v_ref_1356_);
v___x_1362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1362_, 0, v_ref_1356_);
lean_ctor_set(v___x_1362_, 1, v_a_1358_);
if (v_isShared_1361_ == 0)
{
lean_ctor_set_tag(v___x_1360_, 1);
lean_ctor_set(v___x_1360_, 0, v___x_1362_);
v___x_1364_ = v___x_1360_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v___x_1362_);
v___x_1364_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
return v___x_1364_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__8___redArg___boxed(lean_object* v_msg_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_){
_start:
{
lean_object* v_res_1373_; 
v_res_1373_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__8___redArg(v_msg_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_);
lean_dec(v___y_1371_);
lean_dec_ref(v___y_1370_);
lean_dec(v___y_1369_);
lean_dec_ref(v___y_1368_);
return v_res_1373_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__7(lean_object* v_u_1374_, lean_object* v_as_1375_, size_t v_i_1376_, size_t v_stop_1377_, lean_object* v_b_1378_){
_start:
{
uint8_t v___x_1379_; 
v___x_1379_ = lean_usize_dec_eq(v_i_1376_, v_stop_1377_);
if (v___x_1379_ == 0)
{
size_t v___x_1380_; size_t v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; 
v___x_1380_ = ((size_t)1ULL);
v___x_1381_ = lean_usize_sub(v_i_1376_, v___x_1380_);
v___x_1382_ = lean_array_uget_borrowed(v_as_1375_, v___x_1381_);
lean_inc(v___x_1382_);
lean_inc(v_u_1374_);
v___x_1383_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkCons(v_u_1374_, v___x_1382_, v_b_1378_);
v_i_1376_ = v___x_1381_;
v_b_1378_ = v___x_1383_;
goto _start;
}
else
{
lean_dec(v_u_1374_);
return v_b_1378_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__7___boxed(lean_object* v_u_1385_, lean_object* v_as_1386_, lean_object* v_i_1387_, lean_object* v_stop_1388_, lean_object* v_b_1389_){
_start:
{
size_t v_i_boxed_1390_; size_t v_stop_boxed_1391_; lean_object* v_res_1392_; 
v_i_boxed_1390_ = lean_unbox_usize(v_i_1387_);
lean_dec(v_i_1387_);
v_stop_boxed_1391_ = lean_unbox_usize(v_stop_1388_);
lean_dec(v_stop_1388_);
v_res_1392_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__7(v_u_1385_, v_as_1386_, v_i_boxed_1390_, v_stop_boxed_1391_, v_b_1389_);
lean_dec_ref(v_as_1386_);
return v_res_1392_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__6(size_t v_sz_1393_, size_t v_i_1394_, lean_object* v_bs_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_){
_start:
{
uint8_t v___x_1401_; 
v___x_1401_ = lean_usize_dec_lt(v_i_1394_, v_sz_1393_);
if (v___x_1401_ == 0)
{
lean_object* v___x_1402_; 
v___x_1402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1402_, 0, v_bs_1395_);
return v___x_1402_;
}
else
{
lean_object* v_v_1403_; lean_object* v___x_1404_; 
v_v_1403_ = lean_array_uget_borrowed(v_bs_1395_, v_i_1394_);
lean_inc(v_v_1403_);
v___x_1404_ = l_Lean_Meta_mkEqRefl(v_v_1403_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_);
if (lean_obj_tag(v___x_1404_) == 0)
{
lean_object* v_a_1405_; lean_object* v___x_1406_; lean_object* v_bs_x27_1407_; size_t v___x_1408_; size_t v___x_1409_; lean_object* v___x_1410_; 
v_a_1405_ = lean_ctor_get(v___x_1404_, 0);
lean_inc(v_a_1405_);
lean_dec_ref(v___x_1404_);
v___x_1406_ = lean_unsigned_to_nat(0u);
v_bs_x27_1407_ = lean_array_uset(v_bs_1395_, v_i_1394_, v___x_1406_);
v___x_1408_ = ((size_t)1ULL);
v___x_1409_ = lean_usize_add(v_i_1394_, v___x_1408_);
v___x_1410_ = lean_array_uset(v_bs_x27_1407_, v_i_1394_, v_a_1405_);
v_i_1394_ = v___x_1409_;
v_bs_1395_ = v___x_1410_;
goto _start;
}
else
{
lean_object* v_a_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1419_; 
lean_dec_ref(v_bs_1395_);
v_a_1412_ = lean_ctor_get(v___x_1404_, 0);
v_isSharedCheck_1419_ = !lean_is_exclusive(v___x_1404_);
if (v_isSharedCheck_1419_ == 0)
{
v___x_1414_ = v___x_1404_;
v_isShared_1415_ = v_isSharedCheck_1419_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_a_1412_);
lean_dec(v___x_1404_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1419_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v___x_1417_; 
if (v_isShared_1415_ == 0)
{
v___x_1417_ = v___x_1414_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v_a_1412_);
v___x_1417_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
return v___x_1417_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__6___boxed(lean_object* v_sz_1420_, lean_object* v_i_1421_, lean_object* v_bs_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_){
_start:
{
size_t v_sz_boxed_1428_; size_t v_i_boxed_1429_; lean_object* v_res_1430_; 
v_sz_boxed_1428_ = lean_unbox_usize(v_sz_1420_);
lean_dec(v_sz_1420_);
v_i_boxed_1429_ = lean_unbox_usize(v_i_1421_);
lean_dec(v_i_1421_);
v_res_1430_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__6(v_sz_boxed_1428_, v_i_boxed_1429_, v_bs_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_);
lean_dec(v___y_1426_);
lean_dec_ref(v___y_1425_);
lean_dec(v___y_1424_);
lean_dec_ref(v___y_1423_);
return v_res_1430_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__1___redArg(lean_object* v_a_1431_, lean_object* v_b_1432_){
_start:
{
lean_object* v_array_1433_; lean_object* v_start_1434_; lean_object* v_stop_1435_; lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1448_; 
v_array_1433_ = lean_ctor_get(v_a_1431_, 0);
v_start_1434_ = lean_ctor_get(v_a_1431_, 1);
v_stop_1435_ = lean_ctor_get(v_a_1431_, 2);
v_isSharedCheck_1448_ = !lean_is_exclusive(v_a_1431_);
if (v_isSharedCheck_1448_ == 0)
{
v___x_1437_ = v_a_1431_;
v_isShared_1438_ = v_isSharedCheck_1448_;
goto v_resetjp_1436_;
}
else
{
lean_inc(v_stop_1435_);
lean_inc(v_start_1434_);
lean_inc(v_array_1433_);
lean_dec(v_a_1431_);
v___x_1437_ = lean_box(0);
v_isShared_1438_ = v_isSharedCheck_1448_;
goto v_resetjp_1436_;
}
v_resetjp_1436_:
{
uint8_t v___x_1439_; 
v___x_1439_ = lean_nat_dec_lt(v_start_1434_, v_stop_1435_);
if (v___x_1439_ == 0)
{
lean_del_object(v___x_1437_);
lean_dec(v_stop_1435_);
lean_dec(v_start_1434_);
lean_dec_ref(v_array_1433_);
return v_b_1432_;
}
else
{
lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1443_; 
v___x_1440_ = lean_unsigned_to_nat(1u);
v___x_1441_ = lean_nat_add(v_start_1434_, v___x_1440_);
lean_inc_ref(v_array_1433_);
if (v_isShared_1438_ == 0)
{
lean_ctor_set(v___x_1437_, 1, v___x_1441_);
v___x_1443_ = v___x_1437_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v_array_1433_);
lean_ctor_set(v_reuseFailAlloc_1447_, 1, v___x_1441_);
lean_ctor_set(v_reuseFailAlloc_1447_, 2, v_stop_1435_);
v___x_1443_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
lean_object* v___x_1444_; lean_object* v___x_1445_; 
v___x_1444_ = lean_array_fget(v_array_1433_, v_start_1434_);
lean_dec(v_start_1434_);
lean_dec_ref(v_array_1433_);
v___x_1445_ = lean_array_push(v_b_1432_, v___x_1444_);
v_a_1431_ = v___x_1443_;
v_b_1432_ = v___x_1445_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__3(size_t v_sz_1449_, size_t v_i_1450_, lean_object* v_bs_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_){
_start:
{
uint8_t v___x_1457_; 
v___x_1457_ = lean_usize_dec_lt(v_i_1450_, v_sz_1449_);
if (v___x_1457_ == 0)
{
lean_object* v___x_1458_; 
v___x_1458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1458_, 0, v_bs_1451_);
return v___x_1458_;
}
else
{
lean_object* v_v_1459_; lean_object* v___x_1460_; 
v_v_1459_ = lean_array_uget_borrowed(v_bs_1451_, v_i_1450_);
lean_inc(v___y_1455_);
lean_inc_ref(v___y_1454_);
lean_inc(v___y_1453_);
lean_inc_ref(v___y_1452_);
lean_inc(v_v_1459_);
v___x_1460_ = lean_infer_type(v_v_1459_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_);
if (lean_obj_tag(v___x_1460_) == 0)
{
lean_object* v_a_1461_; lean_object* v___x_1462_; lean_object* v_bs_x27_1463_; size_t v___x_1464_; size_t v___x_1465_; lean_object* v___x_1466_; 
v_a_1461_ = lean_ctor_get(v___x_1460_, 0);
lean_inc(v_a_1461_);
lean_dec_ref(v___x_1460_);
v___x_1462_ = lean_unsigned_to_nat(0u);
v_bs_x27_1463_ = lean_array_uset(v_bs_1451_, v_i_1450_, v___x_1462_);
v___x_1464_ = ((size_t)1ULL);
v___x_1465_ = lean_usize_add(v_i_1450_, v___x_1464_);
v___x_1466_ = lean_array_uset(v_bs_x27_1463_, v_i_1450_, v_a_1461_);
v_i_1450_ = v___x_1465_;
v_bs_1451_ = v___x_1466_;
goto _start;
}
else
{
lean_object* v_a_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1475_; 
lean_dec_ref(v_bs_1451_);
v_a_1468_ = lean_ctor_get(v___x_1460_, 0);
v_isSharedCheck_1475_ = !lean_is_exclusive(v___x_1460_);
if (v_isSharedCheck_1475_ == 0)
{
v___x_1470_ = v___x_1460_;
v_isShared_1471_ = v_isSharedCheck_1475_;
goto v_resetjp_1469_;
}
else
{
lean_inc(v_a_1468_);
lean_dec(v___x_1460_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1475_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
lean_object* v___x_1473_; 
if (v_isShared_1471_ == 0)
{
v___x_1473_ = v___x_1470_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v_a_1468_);
v___x_1473_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
return v___x_1473_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__3___boxed(lean_object* v_sz_1476_, lean_object* v_i_1477_, lean_object* v_bs_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_){
_start:
{
size_t v_sz_boxed_1484_; size_t v_i_boxed_1485_; lean_object* v_res_1486_; 
v_sz_boxed_1484_ = lean_unbox_usize(v_sz_1476_);
lean_dec(v_sz_1476_);
v_i_boxed_1485_ = lean_unbox_usize(v_i_1477_);
lean_dec(v_i_1477_);
v_res_1486_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__3(v_sz_boxed_1484_, v_i_boxed_1485_, v_bs_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_);
lean_dec(v___y_1482_);
lean_dec_ref(v___y_1481_);
lean_dec(v___y_1480_);
lean_dec_ref(v___y_1479_);
return v_res_1486_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__13(size_t v_sz_1487_, size_t v_i_1488_, lean_object* v_bs_1489_){
_start:
{
uint8_t v___x_1490_; 
v___x_1490_ = lean_usize_dec_lt(v_i_1488_, v_sz_1487_);
if (v___x_1490_ == 0)
{
return v_bs_1489_;
}
else
{
lean_object* v_v_1491_; lean_object* v_fst_1492_; lean_object* v_snd_1493_; lean_object* v___x_1495_; uint8_t v_isShared_1496_; uint8_t v_isSharedCheck_1509_; 
v_v_1491_ = lean_array_uget(v_bs_1489_, v_i_1488_);
v_fst_1492_ = lean_ctor_get(v_v_1491_, 0);
v_snd_1493_ = lean_ctor_get(v_v_1491_, 1);
v_isSharedCheck_1509_ = !lean_is_exclusive(v_v_1491_);
if (v_isSharedCheck_1509_ == 0)
{
v___x_1495_ = v_v_1491_;
v_isShared_1496_ = v_isSharedCheck_1509_;
goto v_resetjp_1494_;
}
else
{
lean_inc(v_snd_1493_);
lean_inc(v_fst_1492_);
lean_dec(v_v_1491_);
v___x_1495_ = lean_box(0);
v_isShared_1496_ = v_isSharedCheck_1509_;
goto v_resetjp_1494_;
}
v_resetjp_1494_:
{
lean_object* v___x_1497_; lean_object* v_bs_x27_1498_; uint8_t v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1502_; 
v___x_1497_ = lean_unsigned_to_nat(0u);
v_bs_x27_1498_ = lean_array_uset(v_bs_1489_, v_i_1488_, v___x_1497_);
v___x_1499_ = 0;
v___x_1500_ = lean_box(v___x_1499_);
if (v_isShared_1496_ == 0)
{
lean_ctor_set(v___x_1495_, 0, v___x_1500_);
v___x_1502_ = v___x_1495_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v___x_1500_);
lean_ctor_set(v_reuseFailAlloc_1508_, 1, v_snd_1493_);
v___x_1502_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
lean_object* v___x_1503_; size_t v___x_1504_; size_t v___x_1505_; lean_object* v___x_1506_; 
v___x_1503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1503_, 0, v_fst_1492_);
lean_ctor_set(v___x_1503_, 1, v___x_1502_);
v___x_1504_ = ((size_t)1ULL);
v___x_1505_ = lean_usize_add(v_i_1488_, v___x_1504_);
v___x_1506_ = lean_array_uset(v_bs_x27_1498_, v_i_1488_, v___x_1503_);
v_i_1488_ = v___x_1505_;
v_bs_1489_ = v___x_1506_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__13___boxed(lean_object* v_sz_1510_, lean_object* v_i_1511_, lean_object* v_bs_1512_){
_start:
{
size_t v_sz_boxed_1513_; size_t v_i_boxed_1514_; lean_object* v_res_1515_; 
v_sz_boxed_1513_ = lean_unbox_usize(v_sz_1510_);
lean_dec(v_sz_1510_);
v_i_boxed_1514_ = lean_unbox_usize(v_i_1511_);
lean_dec(v_i_1511_);
v_res_1515_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__13(v_sz_boxed_1513_, v_i_boxed_1514_, v_bs_1512_);
return v_res_1515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19_spec__21___redArg___lam__0(lean_object* v_k_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v_b_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_){
_start:
{
lean_object* v___x_1527_; 
lean_inc(v___y_1525_);
lean_inc_ref(v___y_1524_);
lean_inc(v___y_1523_);
lean_inc_ref(v___y_1522_);
lean_inc(v___y_1520_);
lean_inc_ref(v___y_1519_);
lean_inc(v___y_1518_);
lean_inc_ref(v___y_1517_);
v___x_1527_ = lean_apply_10(v_k_1516_, v_b_1521_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_, lean_box(0));
return v___x_1527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19_spec__21___redArg___lam__0___boxed(lean_object* v_k_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v_b_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_){
_start:
{
lean_object* v_res_1539_; 
v_res_1539_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19_spec__21___redArg___lam__0(v_k_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v_b_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_);
lean_dec(v___y_1537_);
lean_dec_ref(v___y_1536_);
lean_dec(v___y_1535_);
lean_dec_ref(v___y_1534_);
lean_dec(v___y_1532_);
lean_dec_ref(v___y_1531_);
lean_dec(v___y_1530_);
lean_dec_ref(v___y_1529_);
return v_res_1539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19_spec__21___redArg(lean_object* v_name_1540_, uint8_t v_bi_1541_, lean_object* v_type_1542_, lean_object* v_k_1543_, uint8_t v_kind_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_){
_start:
{
lean_object* v___f_1554_; lean_object* v___x_1555_; 
lean_inc(v___y_1548_);
lean_inc_ref(v___y_1547_);
lean_inc(v___y_1546_);
lean_inc_ref(v___y_1545_);
v___f_1554_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19_spec__21___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_1554_, 0, v_k_1543_);
lean_closure_set(v___f_1554_, 1, v___y_1545_);
lean_closure_set(v___f_1554_, 2, v___y_1546_);
lean_closure_set(v___f_1554_, 3, v___y_1547_);
lean_closure_set(v___f_1554_, 4, v___y_1548_);
v___x_1555_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1540_, v_bi_1541_, v_type_1542_, v___f_1554_, v_kind_1544_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_);
if (lean_obj_tag(v___x_1555_) == 0)
{
return v___x_1555_;
}
else
{
lean_object* v_a_1556_; lean_object* v___x_1558_; uint8_t v_isShared_1559_; uint8_t v_isSharedCheck_1563_; 
v_a_1556_ = lean_ctor_get(v___x_1555_, 0);
v_isSharedCheck_1563_ = !lean_is_exclusive(v___x_1555_);
if (v_isSharedCheck_1563_ == 0)
{
v___x_1558_ = v___x_1555_;
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
else
{
lean_inc(v_a_1556_);
lean_dec(v___x_1555_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19_spec__21___redArg___boxed(lean_object* v_name_1564_, lean_object* v_bi_1565_, lean_object* v_type_1566_, lean_object* v_k_1567_, lean_object* v_kind_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_){
_start:
{
uint8_t v_bi_boxed_1578_; uint8_t v_kind_boxed_1579_; lean_object* v_res_1580_; 
v_bi_boxed_1578_ = lean_unbox(v_bi_1565_);
v_kind_boxed_1579_ = lean_unbox(v_kind_1568_);
v_res_1580_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19_spec__21___redArg(v_name_1564_, v_bi_boxed_1578_, v_type_1566_, v_k_1567_, v_kind_boxed_1579_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_);
lean_dec(v___y_1576_);
lean_dec_ref(v___y_1575_);
lean_dec(v___y_1574_);
lean_dec_ref(v___y_1573_);
lean_dec(v___y_1572_);
lean_dec_ref(v___y_1571_);
lean_dec(v___y_1570_);
lean_dec_ref(v___y_1569_);
return v_res_1580_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___redArg___lam__0(lean_object* v___x_1581_, lean_object* v_a_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_){
_start:
{
lean_object* v___x_1592_; lean_object* v___x_19922__overap_1593_; lean_object* v___x_1594_; 
v___x_1592_ = l_Lean_instInhabitedExpr;
v___x_19922__overap_1593_ = l_instInhabitedOfMonad___redArg(v___x_1581_, v___x_1592_);
lean_inc(v___y_1590_);
lean_inc_ref(v___y_1589_);
lean_inc(v___y_1588_);
lean_inc_ref(v___y_1587_);
lean_inc(v___y_1586_);
lean_inc_ref(v___y_1585_);
lean_inc(v___y_1584_);
lean_inc_ref(v___y_1583_);
v___x_1594_ = lean_apply_9(v___x_19922__overap_1593_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, lean_box(0));
return v___x_1594_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___redArg___lam__0___boxed(lean_object* v___x_1595_, lean_object* v_a_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_){
_start:
{
lean_object* v_res_1606_; 
v_res_1606_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___redArg___lam__0(v___x_1595_, v_a_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_);
lean_dec(v___y_1604_);
lean_dec_ref(v___y_1603_);
lean_dec(v___y_1602_);
lean_dec_ref(v___y_1601_);
lean_dec(v___y_1600_);
lean_dec_ref(v___y_1599_);
lean_dec(v___y_1598_);
lean_dec_ref(v___y_1597_);
lean_dec_ref(v_a_1596_);
return v_res_1606_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___redArg___lam__1___boxed(lean_object* v_acc_1611_, lean_object* v_declInfos_1612_, lean_object* v_k_1613_, lean_object* v_kind_1614_, lean_object* v_x_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_){
_start:
{
uint8_t v_kind_boxed_1625_; lean_object* v_res_1626_; 
v_kind_boxed_1625_ = lean_unbox(v_kind_1614_);
v_res_1626_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___redArg___lam__1(v_acc_1611_, v_declInfos_1612_, v_k_1613_, v_kind_boxed_1625_, v_x_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_);
lean_dec(v___y_1623_);
lean_dec_ref(v___y_1622_);
lean_dec(v___y_1621_);
lean_dec_ref(v___y_1620_);
lean_dec(v___y_1619_);
lean_dec_ref(v___y_1618_);
lean_dec(v___y_1617_);
lean_dec_ref(v___y_1616_);
return v_res_1626_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___redArg(lean_object* v_declInfos_1627_, lean_object* v_k_1628_, uint8_t v_kind_1629_, lean_object* v_acc_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_){
_start:
{
lean_object* v___x_1640_; lean_object* v_toApplicative_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1788_; 
v___x_1640_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__1);
v_toApplicative_1641_ = lean_ctor_get(v___x_1640_, 0);
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1640_);
if (v_isSharedCheck_1788_ == 0)
{
lean_object* v_unused_1789_; 
v_unused_1789_ = lean_ctor_get(v___x_1640_, 1);
lean_dec(v_unused_1789_);
v___x_1643_ = v___x_1640_;
v_isShared_1644_ = v_isSharedCheck_1788_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_toApplicative_1641_);
lean_dec(v___x_1640_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1788_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
lean_object* v_toFunctor_1645_; lean_object* v_toSeq_1646_; lean_object* v_toSeqLeft_1647_; lean_object* v_toSeqRight_1648_; lean_object* v___x_1650_; uint8_t v_isShared_1651_; uint8_t v_isSharedCheck_1786_; 
v_toFunctor_1645_ = lean_ctor_get(v_toApplicative_1641_, 0);
v_toSeq_1646_ = lean_ctor_get(v_toApplicative_1641_, 2);
v_toSeqLeft_1647_ = lean_ctor_get(v_toApplicative_1641_, 3);
v_toSeqRight_1648_ = lean_ctor_get(v_toApplicative_1641_, 4);
v_isSharedCheck_1786_ = !lean_is_exclusive(v_toApplicative_1641_);
if (v_isSharedCheck_1786_ == 0)
{
lean_object* v_unused_1787_; 
v_unused_1787_ = lean_ctor_get(v_toApplicative_1641_, 1);
lean_dec(v_unused_1787_);
v___x_1650_ = v_toApplicative_1641_;
v_isShared_1651_ = v_isSharedCheck_1786_;
goto v_resetjp_1649_;
}
else
{
lean_inc(v_toSeqRight_1648_);
lean_inc(v_toSeqLeft_1647_);
lean_inc(v_toSeq_1646_);
lean_inc(v_toFunctor_1645_);
lean_dec(v_toApplicative_1641_);
v___x_1650_ = lean_box(0);
v_isShared_1651_ = v_isSharedCheck_1786_;
goto v_resetjp_1649_;
}
v_resetjp_1649_:
{
lean_object* v___f_1652_; lean_object* v___f_1653_; lean_object* v___f_1654_; lean_object* v___f_1655_; lean_object* v___x_1656_; lean_object* v___f_1657_; lean_object* v___f_1658_; lean_object* v___f_1659_; lean_object* v___x_1661_; 
v___f_1652_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__2));
v___f_1653_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__3));
lean_inc_ref(v_toFunctor_1645_);
v___f_1654_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1654_, 0, v_toFunctor_1645_);
v___f_1655_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1655_, 0, v_toFunctor_1645_);
v___x_1656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1656_, 0, v___f_1654_);
lean_ctor_set(v___x_1656_, 1, v___f_1655_);
v___f_1657_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1657_, 0, v_toSeqRight_1648_);
v___f_1658_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1658_, 0, v_toSeqLeft_1647_);
v___f_1659_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1659_, 0, v_toSeq_1646_);
if (v_isShared_1651_ == 0)
{
lean_ctor_set(v___x_1650_, 4, v___f_1657_);
lean_ctor_set(v___x_1650_, 3, v___f_1658_);
lean_ctor_set(v___x_1650_, 2, v___f_1659_);
lean_ctor_set(v___x_1650_, 1, v___f_1652_);
lean_ctor_set(v___x_1650_, 0, v___x_1656_);
v___x_1661_ = v___x_1650_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v___x_1656_);
lean_ctor_set(v_reuseFailAlloc_1785_, 1, v___f_1652_);
lean_ctor_set(v_reuseFailAlloc_1785_, 2, v___f_1659_);
lean_ctor_set(v_reuseFailAlloc_1785_, 3, v___f_1658_);
lean_ctor_set(v_reuseFailAlloc_1785_, 4, v___f_1657_);
v___x_1661_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
lean_object* v___x_1663_; 
if (v_isShared_1644_ == 0)
{
lean_ctor_set(v___x_1643_, 1, v___f_1653_);
lean_ctor_set(v___x_1643_, 0, v___x_1661_);
v___x_1663_ = v___x_1643_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v___x_1661_);
lean_ctor_set(v_reuseFailAlloc_1784_, 1, v___f_1653_);
v___x_1663_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
lean_object* v___x_1664_; lean_object* v_toApplicative_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1782_; 
v___x_1664_ = l_StateRefT_x27_instMonad___redArg(v___x_1663_);
v_toApplicative_1665_ = lean_ctor_get(v___x_1664_, 0);
v_isSharedCheck_1782_ = !lean_is_exclusive(v___x_1664_);
if (v_isSharedCheck_1782_ == 0)
{
lean_object* v_unused_1783_; 
v_unused_1783_ = lean_ctor_get(v___x_1664_, 1);
lean_dec(v_unused_1783_);
v___x_1667_ = v___x_1664_;
v_isShared_1668_ = v_isSharedCheck_1782_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_toApplicative_1665_);
lean_dec(v___x_1664_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1782_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v_toFunctor_1669_; lean_object* v_toSeq_1670_; lean_object* v_toSeqLeft_1671_; lean_object* v_toSeqRight_1672_; lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1780_; 
v_toFunctor_1669_ = lean_ctor_get(v_toApplicative_1665_, 0);
v_toSeq_1670_ = lean_ctor_get(v_toApplicative_1665_, 2);
v_toSeqLeft_1671_ = lean_ctor_get(v_toApplicative_1665_, 3);
v_toSeqRight_1672_ = lean_ctor_get(v_toApplicative_1665_, 4);
v_isSharedCheck_1780_ = !lean_is_exclusive(v_toApplicative_1665_);
if (v_isSharedCheck_1780_ == 0)
{
lean_object* v_unused_1781_; 
v_unused_1781_ = lean_ctor_get(v_toApplicative_1665_, 1);
lean_dec(v_unused_1781_);
v___x_1674_ = v_toApplicative_1665_;
v_isShared_1675_ = v_isSharedCheck_1780_;
goto v_resetjp_1673_;
}
else
{
lean_inc(v_toSeqRight_1672_);
lean_inc(v_toSeqLeft_1671_);
lean_inc(v_toSeq_1670_);
lean_inc(v_toFunctor_1669_);
lean_dec(v_toApplicative_1665_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1780_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
lean_object* v___f_1676_; lean_object* v___f_1677_; lean_object* v___f_1678_; lean_object* v___f_1679_; lean_object* v___x_1680_; lean_object* v___f_1681_; lean_object* v___f_1682_; lean_object* v___f_1683_; lean_object* v___x_1685_; 
v___f_1676_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__4));
v___f_1677_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__5));
lean_inc_ref(v_toFunctor_1669_);
v___f_1678_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1678_, 0, v_toFunctor_1669_);
v___f_1679_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1679_, 0, v_toFunctor_1669_);
v___x_1680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1680_, 0, v___f_1678_);
lean_ctor_set(v___x_1680_, 1, v___f_1679_);
v___f_1681_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1681_, 0, v_toSeqRight_1672_);
v___f_1682_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1682_, 0, v_toSeqLeft_1671_);
v___f_1683_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1683_, 0, v_toSeq_1670_);
if (v_isShared_1675_ == 0)
{
lean_ctor_set(v___x_1674_, 4, v___f_1681_);
lean_ctor_set(v___x_1674_, 3, v___f_1682_);
lean_ctor_set(v___x_1674_, 2, v___f_1683_);
lean_ctor_set(v___x_1674_, 1, v___f_1676_);
lean_ctor_set(v___x_1674_, 0, v___x_1680_);
v___x_1685_ = v___x_1674_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v___x_1680_);
lean_ctor_set(v_reuseFailAlloc_1779_, 1, v___f_1676_);
lean_ctor_set(v_reuseFailAlloc_1779_, 2, v___f_1683_);
lean_ctor_set(v_reuseFailAlloc_1779_, 3, v___f_1682_);
lean_ctor_set(v_reuseFailAlloc_1779_, 4, v___f_1681_);
v___x_1685_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
lean_object* v___x_1687_; 
if (v_isShared_1668_ == 0)
{
lean_ctor_set(v___x_1667_, 1, v___f_1677_);
lean_ctor_set(v___x_1667_, 0, v___x_1685_);
v___x_1687_ = v___x_1667_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v___x_1685_);
lean_ctor_set(v_reuseFailAlloc_1778_, 1, v___f_1677_);
v___x_1687_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
lean_object* v___x_1688_; lean_object* v_toApplicative_1689_; lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1776_; 
v___x_1688_ = l_StateRefT_x27_instMonad___redArg(v___x_1687_);
v_toApplicative_1689_ = lean_ctor_get(v___x_1688_, 0);
v_isSharedCheck_1776_ = !lean_is_exclusive(v___x_1688_);
if (v_isSharedCheck_1776_ == 0)
{
lean_object* v_unused_1777_; 
v_unused_1777_ = lean_ctor_get(v___x_1688_, 1);
lean_dec(v_unused_1777_);
v___x_1691_ = v___x_1688_;
v_isShared_1692_ = v_isSharedCheck_1776_;
goto v_resetjp_1690_;
}
else
{
lean_inc(v_toApplicative_1689_);
lean_dec(v___x_1688_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1776_;
goto v_resetjp_1690_;
}
v_resetjp_1690_:
{
lean_object* v_toFunctor_1693_; lean_object* v_toSeq_1694_; lean_object* v_toSeqLeft_1695_; lean_object* v_toSeqRight_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1774_; 
v_toFunctor_1693_ = lean_ctor_get(v_toApplicative_1689_, 0);
v_toSeq_1694_ = lean_ctor_get(v_toApplicative_1689_, 2);
v_toSeqLeft_1695_ = lean_ctor_get(v_toApplicative_1689_, 3);
v_toSeqRight_1696_ = lean_ctor_get(v_toApplicative_1689_, 4);
v_isSharedCheck_1774_ = !lean_is_exclusive(v_toApplicative_1689_);
if (v_isSharedCheck_1774_ == 0)
{
lean_object* v_unused_1775_; 
v_unused_1775_ = lean_ctor_get(v_toApplicative_1689_, 1);
lean_dec(v_unused_1775_);
v___x_1698_ = v_toApplicative_1689_;
v_isShared_1699_ = v_isSharedCheck_1774_;
goto v_resetjp_1697_;
}
else
{
lean_inc(v_toSeqRight_1696_);
lean_inc(v_toSeqLeft_1695_);
lean_inc(v_toSeq_1694_);
lean_inc(v_toFunctor_1693_);
lean_dec(v_toApplicative_1689_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1774_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
lean_object* v___f_1700_; lean_object* v___f_1701_; lean_object* v___f_1702_; lean_object* v___f_1703_; lean_object* v___x_1704_; lean_object* v___f_1705_; lean_object* v___f_1706_; lean_object* v___f_1707_; lean_object* v___x_1709_; 
v___f_1700_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___redArg___closed__0));
v___f_1701_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___redArg___closed__1));
lean_inc_ref(v_toFunctor_1693_);
v___f_1702_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1702_, 0, v_toFunctor_1693_);
v___f_1703_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1703_, 0, v_toFunctor_1693_);
v___x_1704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1704_, 0, v___f_1702_);
lean_ctor_set(v___x_1704_, 1, v___f_1703_);
v___f_1705_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1705_, 0, v_toSeqRight_1696_);
v___f_1706_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1706_, 0, v_toSeqLeft_1695_);
v___f_1707_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1707_, 0, v_toSeq_1694_);
if (v_isShared_1699_ == 0)
{
lean_ctor_set(v___x_1698_, 4, v___f_1705_);
lean_ctor_set(v___x_1698_, 3, v___f_1706_);
lean_ctor_set(v___x_1698_, 2, v___f_1707_);
lean_ctor_set(v___x_1698_, 1, v___f_1700_);
lean_ctor_set(v___x_1698_, 0, v___x_1704_);
v___x_1709_ = v___x_1698_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1773_; 
v_reuseFailAlloc_1773_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1773_, 0, v___x_1704_);
lean_ctor_set(v_reuseFailAlloc_1773_, 1, v___f_1700_);
lean_ctor_set(v_reuseFailAlloc_1773_, 2, v___f_1707_);
lean_ctor_set(v_reuseFailAlloc_1773_, 3, v___f_1706_);
lean_ctor_set(v_reuseFailAlloc_1773_, 4, v___f_1705_);
v___x_1709_ = v_reuseFailAlloc_1773_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
lean_object* v___x_1711_; 
if (v_isShared_1692_ == 0)
{
lean_ctor_set(v___x_1691_, 1, v___f_1701_);
lean_ctor_set(v___x_1691_, 0, v___x_1709_);
v___x_1711_ = v___x_1691_;
goto v_reusejp_1710_;
}
else
{
lean_object* v_reuseFailAlloc_1772_; 
v_reuseFailAlloc_1772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1772_, 0, v___x_1709_);
lean_ctor_set(v_reuseFailAlloc_1772_, 1, v___f_1701_);
v___x_1711_ = v_reuseFailAlloc_1772_;
goto v_reusejp_1710_;
}
v_reusejp_1710_:
{
lean_object* v___x_1712_; lean_object* v_toApplicative_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1770_; 
v___x_1712_ = l_StateRefT_x27_instMonad___redArg(v___x_1711_);
v_toApplicative_1713_ = lean_ctor_get(v___x_1712_, 0);
v_isSharedCheck_1770_ = !lean_is_exclusive(v___x_1712_);
if (v_isSharedCheck_1770_ == 0)
{
lean_object* v_unused_1771_; 
v_unused_1771_ = lean_ctor_get(v___x_1712_, 1);
lean_dec(v_unused_1771_);
v___x_1715_ = v___x_1712_;
v_isShared_1716_ = v_isSharedCheck_1770_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_toApplicative_1713_);
lean_dec(v___x_1712_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1770_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
lean_object* v_toFunctor_1717_; lean_object* v_toSeq_1718_; lean_object* v_toSeqLeft_1719_; lean_object* v_toSeqRight_1720_; lean_object* v___x_1722_; uint8_t v_isShared_1723_; uint8_t v_isSharedCheck_1768_; 
v_toFunctor_1717_ = lean_ctor_get(v_toApplicative_1713_, 0);
v_toSeq_1718_ = lean_ctor_get(v_toApplicative_1713_, 2);
v_toSeqLeft_1719_ = lean_ctor_get(v_toApplicative_1713_, 3);
v_toSeqRight_1720_ = lean_ctor_get(v_toApplicative_1713_, 4);
v_isSharedCheck_1768_ = !lean_is_exclusive(v_toApplicative_1713_);
if (v_isSharedCheck_1768_ == 0)
{
lean_object* v_unused_1769_; 
v_unused_1769_ = lean_ctor_get(v_toApplicative_1713_, 1);
lean_dec(v_unused_1769_);
v___x_1722_ = v_toApplicative_1713_;
v_isShared_1723_ = v_isSharedCheck_1768_;
goto v_resetjp_1721_;
}
else
{
lean_inc(v_toSeqRight_1720_);
lean_inc(v_toSeqLeft_1719_);
lean_inc(v_toSeq_1718_);
lean_inc(v_toFunctor_1717_);
lean_dec(v_toApplicative_1713_);
v___x_1722_ = lean_box(0);
v_isShared_1723_ = v_isSharedCheck_1768_;
goto v_resetjp_1721_;
}
v_resetjp_1721_:
{
lean_object* v___f_1724_; lean_object* v___f_1725_; lean_object* v___f_1726_; lean_object* v___f_1727_; lean_object* v___x_1728_; lean_object* v___f_1729_; lean_object* v___f_1730_; lean_object* v___f_1731_; lean_object* v___x_1733_; 
v___f_1724_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___redArg___closed__2));
v___f_1725_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___redArg___closed__3));
lean_inc_ref(v_toFunctor_1717_);
v___f_1726_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1726_, 0, v_toFunctor_1717_);
v___f_1727_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1727_, 0, v_toFunctor_1717_);
v___x_1728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1728_, 0, v___f_1726_);
lean_ctor_set(v___x_1728_, 1, v___f_1727_);
v___f_1729_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1729_, 0, v_toSeqRight_1720_);
v___f_1730_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1730_, 0, v_toSeqLeft_1719_);
v___f_1731_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1731_, 0, v_toSeq_1718_);
if (v_isShared_1723_ == 0)
{
lean_ctor_set(v___x_1722_, 4, v___f_1729_);
lean_ctor_set(v___x_1722_, 3, v___f_1730_);
lean_ctor_set(v___x_1722_, 2, v___f_1731_);
lean_ctor_set(v___x_1722_, 1, v___f_1724_);
lean_ctor_set(v___x_1722_, 0, v___x_1728_);
v___x_1733_ = v___x_1722_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v___x_1728_);
lean_ctor_set(v_reuseFailAlloc_1767_, 1, v___f_1724_);
lean_ctor_set(v_reuseFailAlloc_1767_, 2, v___f_1731_);
lean_ctor_set(v_reuseFailAlloc_1767_, 3, v___f_1730_);
lean_ctor_set(v_reuseFailAlloc_1767_, 4, v___f_1729_);
v___x_1733_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1732_;
}
v_reusejp_1732_:
{
lean_object* v___x_1735_; 
if (v_isShared_1716_ == 0)
{
lean_ctor_set(v___x_1715_, 1, v___f_1725_);
lean_ctor_set(v___x_1715_, 0, v___x_1733_);
v___x_1735_ = v___x_1715_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1766_; 
v_reuseFailAlloc_1766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1766_, 0, v___x_1733_);
lean_ctor_set(v_reuseFailAlloc_1766_, 1, v___f_1725_);
v___x_1735_ = v_reuseFailAlloc_1766_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
lean_object* v___x_1736_; lean_object* v___x_1737_; uint8_t v___x_1738_; 
v___x_1736_ = lean_array_get_size(v_acc_1630_);
v___x_1737_ = lean_array_get_size(v_declInfos_1627_);
v___x_1738_ = lean_nat_dec_lt(v___x_1736_, v___x_1737_);
if (v___x_1738_ == 0)
{
lean_object* v___x_1739_; 
lean_dec_ref(v___x_1735_);
lean_dec_ref(v_declInfos_1627_);
lean_inc(v___y_1638_);
lean_inc_ref(v___y_1637_);
lean_inc(v___y_1636_);
lean_inc_ref(v___y_1635_);
lean_inc(v___y_1634_);
lean_inc_ref(v___y_1633_);
lean_inc(v___y_1632_);
lean_inc_ref(v___y_1631_);
v___x_1739_ = lean_apply_10(v_k_1628_, v_acc_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, lean_box(0));
return v___x_1739_;
}
else
{
lean_object* v___f_1740_; lean_object* v___x_1741_; uint8_t v___x_1742_; lean_object* v___f_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v_snd_1748_; lean_object* v_fst_1749_; lean_object* v_fst_1750_; lean_object* v_snd_1751_; lean_object* v___x_1752_; 
v___f_1740_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___redArg___lam__0___boxed), 11, 1);
lean_closure_set(v___f_1740_, 0, v___x_1735_);
v___x_1741_ = lean_box(0);
v___x_1742_ = 0;
v___f_1743_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1743_, 0, v___f_1740_);
v___x_1744_ = lean_box(v___x_1742_);
v___x_1745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1745_, 0, v___x_1744_);
lean_ctor_set(v___x_1745_, 1, v___f_1743_);
v___x_1746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1746_, 0, v___x_1741_);
lean_ctor_set(v___x_1746_, 1, v___x_1745_);
v___x_1747_ = lean_array_get_borrowed(v___x_1746_, v_declInfos_1627_, v___x_1736_);
v_snd_1748_ = lean_ctor_get(v___x_1747_, 1);
v_fst_1749_ = lean_ctor_get(v___x_1747_, 0);
lean_inc(v_fst_1749_);
v_fst_1750_ = lean_ctor_get(v_snd_1748_, 0);
lean_inc(v_fst_1750_);
v_snd_1751_ = lean_ctor_get(v_snd_1748_, 1);
lean_inc(v_snd_1751_);
lean_inc(v___y_1638_);
lean_inc_ref(v___y_1637_);
lean_inc(v___y_1636_);
lean_inc_ref(v___y_1635_);
lean_inc(v___y_1634_);
lean_inc_ref(v___y_1633_);
lean_inc(v___y_1632_);
lean_inc_ref(v___y_1631_);
lean_inc_ref(v_acc_1630_);
v___x_1752_ = lean_apply_10(v_snd_1751_, v_acc_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, lean_box(0));
if (lean_obj_tag(v___x_1752_) == 0)
{
lean_object* v_a_1753_; lean_object* v___x_1754_; lean_object* v___f_1755_; uint8_t v___x_1756_; lean_object* v___x_1757_; 
v_a_1753_ = lean_ctor_get(v___x_1752_, 0);
lean_inc(v_a_1753_);
lean_dec_ref(v___x_1752_);
v___x_1754_ = lean_box(v_kind_1629_);
v___f_1755_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___redArg___lam__1___boxed), 14, 4);
lean_closure_set(v___f_1755_, 0, v_acc_1630_);
lean_closure_set(v___f_1755_, 1, v_declInfos_1627_);
lean_closure_set(v___f_1755_, 2, v_k_1628_);
lean_closure_set(v___f_1755_, 3, v___x_1754_);
v___x_1756_ = lean_unbox(v_fst_1750_);
lean_dec(v_fst_1750_);
v___x_1757_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19_spec__21___redArg(v_fst_1749_, v___x_1756_, v_a_1753_, v___f_1755_, v_kind_1629_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_);
return v___x_1757_;
}
else
{
lean_object* v_a_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1765_; 
lean_dec(v_fst_1750_);
lean_dec(v_fst_1749_);
lean_dec_ref(v_acc_1630_);
lean_dec_ref(v_k_1628_);
lean_dec_ref(v_declInfos_1627_);
v_a_1758_ = lean_ctor_get(v___x_1752_, 0);
v_isSharedCheck_1765_ = !lean_is_exclusive(v___x_1752_);
if (v_isSharedCheck_1765_ == 0)
{
v___x_1760_ = v___x_1752_;
v_isShared_1761_ = v_isSharedCheck_1765_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_a_1758_);
lean_dec(v___x_1752_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1765_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
lean_object* v___x_1763_; 
if (v_isShared_1761_ == 0)
{
v___x_1763_ = v___x_1760_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v_a_1758_);
v___x_1763_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
return v___x_1763_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___redArg___lam__1(lean_object* v_acc_1790_, lean_object* v_declInfos_1791_, lean_object* v_k_1792_, uint8_t v_kind_1793_, lean_object* v_x_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_){
_start:
{
lean_object* v___x_1804_; lean_object* v___x_1805_; 
v___x_1804_ = lean_array_push(v_acc_1790_, v_x_1794_);
v___x_1805_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___redArg(v_declInfos_1791_, v_k_1792_, v_kind_1793_, v___x_1804_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_);
return v___x_1805_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___redArg___boxed(lean_object* v_declInfos_1806_, lean_object* v_k_1807_, lean_object* v_kind_1808_, lean_object* v_acc_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_){
_start:
{
uint8_t v_kind_boxed_1819_; lean_object* v_res_1820_; 
v_kind_boxed_1819_ = lean_unbox(v_kind_1808_);
v_res_1820_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___redArg(v_declInfos_1806_, v_k_1807_, v_kind_boxed_1819_, v_acc_1809_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_);
lean_dec(v___y_1817_);
lean_dec_ref(v___y_1816_);
lean_dec(v___y_1815_);
lean_dec_ref(v___y_1814_);
lean_dec(v___y_1813_);
lean_dec_ref(v___y_1812_);
lean_dec(v___y_1811_);
lean_dec_ref(v___y_1810_);
return v_res_1820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14___redArg(lean_object* v_inst_1821_, lean_object* v_declInfos_1822_, lean_object* v_k_1823_, uint8_t v_kind_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_){
_start:
{
lean_object* v___x_1834_; lean_object* v___x_1835_; 
v___x_1834_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__1));
v___x_1835_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___redArg(v_declInfos_1822_, v_k_1823_, v_kind_1824_, v___x_1834_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
return v___x_1835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14___redArg___boxed(lean_object* v_inst_1836_, lean_object* v_declInfos_1837_, lean_object* v_k_1838_, lean_object* v_kind_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_){
_start:
{
uint8_t v_kind_boxed_1849_; lean_object* v_res_1850_; 
v_kind_boxed_1849_ = lean_unbox(v_kind_1839_);
v_res_1850_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14___redArg(v_inst_1836_, v_declInfos_1837_, v_k_1838_, v_kind_boxed_1849_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_);
lean_dec(v___y_1847_);
lean_dec_ref(v___y_1846_);
lean_dec(v___y_1845_);
lean_dec_ref(v___y_1844_);
lean_dec(v___y_1843_);
lean_dec_ref(v___y_1842_);
lean_dec(v___y_1841_);
lean_dec_ref(v___y_1840_);
lean_dec(v_inst_1836_);
return v_res_1850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9___redArg(lean_object* v_inst_1851_, lean_object* v_declInfos_1852_, lean_object* v_k_1853_, uint8_t v_kind_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_){
_start:
{
size_t v_sz_1864_; size_t v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; 
v_sz_1864_ = lean_array_size(v_declInfos_1852_);
v___x_1865_ = ((size_t)0ULL);
v___x_1866_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__13(v_sz_1864_, v___x_1865_, v_declInfos_1852_);
v___x_1867_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14___redArg(v_inst_1851_, v___x_1866_, v_k_1853_, v_kind_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_);
return v___x_1867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9___redArg___boxed(lean_object* v_inst_1868_, lean_object* v_declInfos_1869_, lean_object* v_k_1870_, lean_object* v_kind_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_){
_start:
{
uint8_t v_kind_boxed_1881_; lean_object* v_res_1882_; 
v_kind_boxed_1881_ = lean_unbox(v_kind_1871_);
v_res_1882_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9___redArg(v_inst_1868_, v_declInfos_1869_, v_k_1870_, v_kind_boxed_1881_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_);
lean_dec(v___y_1879_);
lean_dec_ref(v___y_1878_);
lean_dec(v___y_1877_);
lean_dec_ref(v___y_1876_);
lean_dec(v___y_1875_);
lean_dec_ref(v___y_1874_);
lean_dec(v___y_1873_);
lean_dec_ref(v___y_1872_);
lean_dec(v_inst_1868_);
return v_res_1882_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8___lam__0(lean_object* v_snd_1883_, lean_object* v_x_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_){
_start:
{
lean_object* v___x_1894_; 
v___x_1894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1894_, 0, v_snd_1883_);
return v___x_1894_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8___lam__0___boxed(lean_object* v_snd_1895_, lean_object* v_x_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_){
_start:
{
lean_object* v_res_1906_; 
v_res_1906_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8___lam__0(v_snd_1895_, v_x_1896_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_);
lean_dec(v___y_1904_);
lean_dec_ref(v___y_1903_);
lean_dec(v___y_1902_);
lean_dec_ref(v___y_1901_);
lean_dec(v___y_1900_);
lean_dec_ref(v___y_1899_);
lean_dec(v___y_1898_);
lean_dec_ref(v___y_1897_);
lean_dec_ref(v_x_1896_);
return v_res_1906_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8(size_t v_sz_1907_, size_t v_i_1908_, lean_object* v_bs_1909_){
_start:
{
uint8_t v___x_1910_; 
v___x_1910_ = lean_usize_dec_lt(v_i_1908_, v_sz_1907_);
if (v___x_1910_ == 0)
{
return v_bs_1909_;
}
else
{
lean_object* v_v_1911_; lean_object* v_fst_1912_; lean_object* v_snd_1913_; lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_1927_; 
v_v_1911_ = lean_array_uget(v_bs_1909_, v_i_1908_);
v_fst_1912_ = lean_ctor_get(v_v_1911_, 0);
v_snd_1913_ = lean_ctor_get(v_v_1911_, 1);
v_isSharedCheck_1927_ = !lean_is_exclusive(v_v_1911_);
if (v_isSharedCheck_1927_ == 0)
{
v___x_1915_ = v_v_1911_;
v_isShared_1916_ = v_isSharedCheck_1927_;
goto v_resetjp_1914_;
}
else
{
lean_inc(v_snd_1913_);
lean_inc(v_fst_1912_);
lean_dec(v_v_1911_);
v___x_1915_ = lean_box(0);
v_isShared_1916_ = v_isSharedCheck_1927_;
goto v_resetjp_1914_;
}
v_resetjp_1914_:
{
lean_object* v___x_1917_; lean_object* v_bs_x27_1918_; lean_object* v___f_1919_; lean_object* v___x_1921_; 
v___x_1917_ = lean_unsigned_to_nat(0u);
v_bs_x27_1918_ = lean_array_uset(v_bs_1909_, v_i_1908_, v___x_1917_);
v___f_1919_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8___lam__0___boxed), 11, 1);
lean_closure_set(v___f_1919_, 0, v_snd_1913_);
if (v_isShared_1916_ == 0)
{
lean_ctor_set(v___x_1915_, 1, v___f_1919_);
v___x_1921_ = v___x_1915_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v_fst_1912_);
lean_ctor_set(v_reuseFailAlloc_1926_, 1, v___f_1919_);
v___x_1921_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
size_t v___x_1922_; size_t v___x_1923_; lean_object* v___x_1924_; 
v___x_1922_ = ((size_t)1ULL);
v___x_1923_ = lean_usize_add(v_i_1908_, v___x_1922_);
v___x_1924_ = lean_array_uset(v_bs_x27_1918_, v_i_1908_, v___x_1921_);
v_i_1908_ = v___x_1923_;
v_bs_1909_ = v___x_1924_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8___boxed(lean_object* v_sz_1928_, lean_object* v_i_1929_, lean_object* v_bs_1930_){
_start:
{
size_t v_sz_boxed_1931_; size_t v_i_boxed_1932_; lean_object* v_res_1933_; 
v_sz_boxed_1931_ = lean_unbox_usize(v_sz_1928_);
lean_dec(v_sz_1928_);
v_i_boxed_1932_ = lean_unbox_usize(v_i_1929_);
lean_dec(v_i_1929_);
v_res_1933_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8(v_sz_boxed_1931_, v_i_boxed_1932_, v_bs_1930_);
return v_res_1933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5___redArg(lean_object* v_inst_1934_, lean_object* v_declInfos_1935_, lean_object* v_k_1936_, uint8_t v_kind_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_){
_start:
{
size_t v_sz_1947_; size_t v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; 
v_sz_1947_ = lean_array_size(v_declInfos_1935_);
v___x_1948_ = ((size_t)0ULL);
v___x_1949_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8(v_sz_1947_, v___x_1948_, v_declInfos_1935_);
v___x_1950_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9___redArg(v_inst_1934_, v___x_1949_, v_k_1936_, v_kind_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_);
return v___x_1950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5___redArg___boxed(lean_object* v_inst_1951_, lean_object* v_declInfos_1952_, lean_object* v_k_1953_, lean_object* v_kind_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_){
_start:
{
uint8_t v_kind_boxed_1964_; lean_object* v_res_1965_; 
v_kind_boxed_1964_ = lean_unbox(v_kind_1954_);
v_res_1965_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5___redArg(v_inst_1951_, v_declInfos_1952_, v_k_1953_, v_kind_boxed_1964_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_);
lean_dec(v___y_1962_);
lean_dec_ref(v___y_1961_);
lean_dec(v___y_1960_);
lean_dec_ref(v___y_1959_);
lean_dec(v___y_1958_);
lean_dec_ref(v___y_1957_);
lean_dec(v___y_1956_);
lean_dec_ref(v___y_1955_);
lean_dec(v_inst_1951_);
return v_res_1965_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__2___redArg(size_t v_sz_1966_, size_t v_i_1967_, lean_object* v_bs_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_){
_start:
{
uint8_t v___x_1974_; 
v___x_1974_ = lean_usize_dec_lt(v_i_1967_, v_sz_1966_);
if (v___x_1974_ == 0)
{
lean_object* v___x_1975_; 
v___x_1975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1975_, 0, v_bs_1968_);
return v___x_1975_;
}
else
{
lean_object* v_v_1976_; lean_object* v_fst_1977_; lean_object* v_snd_1978_; lean_object* v___x_1979_; 
v_v_1976_ = lean_array_uget_borrowed(v_bs_1968_, v_i_1967_);
v_fst_1977_ = lean_ctor_get(v_v_1976_, 0);
v_snd_1978_ = lean_ctor_get(v_v_1976_, 1);
lean_inc(v_fst_1977_);
lean_inc(v_snd_1978_);
v___x_1979_ = l_Lean_Meta_mkEq(v_snd_1978_, v_fst_1977_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_);
if (lean_obj_tag(v___x_1979_) == 0)
{
lean_object* v_a_1980_; lean_object* v___x_1981_; lean_object* v_bs_x27_1982_; size_t v___x_1983_; size_t v___x_1984_; lean_object* v___x_1985_; 
v_a_1980_ = lean_ctor_get(v___x_1979_, 0);
lean_inc(v_a_1980_);
lean_dec_ref(v___x_1979_);
v___x_1981_ = lean_unsigned_to_nat(0u);
v_bs_x27_1982_ = lean_array_uset(v_bs_1968_, v_i_1967_, v___x_1981_);
v___x_1983_ = ((size_t)1ULL);
v___x_1984_ = lean_usize_add(v_i_1967_, v___x_1983_);
v___x_1985_ = lean_array_uset(v_bs_x27_1982_, v_i_1967_, v_a_1980_);
v_i_1967_ = v___x_1984_;
v_bs_1968_ = v___x_1985_;
goto _start;
}
else
{
lean_object* v_a_1987_; lean_object* v___x_1989_; uint8_t v_isShared_1990_; uint8_t v_isSharedCheck_1994_; 
lean_dec_ref(v_bs_1968_);
v_a_1987_ = lean_ctor_get(v___x_1979_, 0);
v_isSharedCheck_1994_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_1994_ == 0)
{
v___x_1989_ = v___x_1979_;
v_isShared_1990_ = v_isSharedCheck_1994_;
goto v_resetjp_1988_;
}
else
{
lean_inc(v_a_1987_);
lean_dec(v___x_1979_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__2___redArg___boxed(lean_object* v_sz_1995_, lean_object* v_i_1996_, lean_object* v_bs_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_){
_start:
{
size_t v_sz_boxed_2003_; size_t v_i_boxed_2004_; lean_object* v_res_2005_; 
v_sz_boxed_2003_ = lean_unbox_usize(v_sz_1995_);
lean_dec(v_sz_1995_);
v_i_boxed_2004_ = lean_unbox_usize(v_i_1996_);
lean_dec(v_i_1996_);
v_res_2005_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__2___redArg(v_sz_boxed_2003_, v_i_boxed_2004_, v_bs_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_);
lean_dec(v___y_2001_);
lean_dec_ref(v___y_2000_);
lean_dec(v___y_1999_);
lean_dec_ref(v___y_1998_);
return v_res_2005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1___lam__0(lean_object* v_revertArgs_2006_, lean_object* v_hypName_2007_, lean_object* v_u_2008_, lean_object* v_00_u03c3s_2009_, uint8_t v___x_2010_, lean_object* v_hyps_2011_, lean_object* v_ss_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_){
_start:
{
lean_object* v___x_2022_; size_t v_sz_2023_; size_t v___x_2024_; lean_object* v___x_2025_; 
v___x_2022_ = l_Array_zip___redArg(v_revertArgs_2006_, v_ss_2012_);
v_sz_2023_ = lean_array_size(v___x_2022_);
v___x_2024_ = ((size_t)0ULL);
v___x_2025_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__2___redArg(v_sz_2023_, v___x_2024_, v___x_2022_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_);
if (lean_obj_tag(v___x_2025_) == 0)
{
lean_object* v_a_2026_; lean_object* v___x_2027_; 
v_a_2026_ = lean_ctor_get(v___x_2025_, 0);
lean_inc(v_a_2026_);
lean_dec_ref(v___x_2025_);
lean_inc(v_hypName_2007_);
v___x_2027_ = l_Lean_Core_mkFreshUserName(v_hypName_2007_, v___y_2019_, v___y_2020_);
if (lean_obj_tag(v___x_2027_) == 0)
{
lean_object* v_a_2028_; lean_object* v_eqs_2029_; lean_object* v_00_u03c6_2030_; lean_object* v_00_u03c6_2031_; uint8_t v___x_2032_; uint8_t v___x_2033_; lean_object* v___x_2034_; 
v_a_2028_ = lean_ctor_get(v___x_2027_, 0);
lean_inc(v_a_2028_);
lean_dec_ref(v___x_2027_);
v_eqs_2029_ = lean_array_to_list(v_a_2026_);
v_00_u03c6_2030_ = l_Lean_mkAndN(v_eqs_2029_);
v_00_u03c6_2031_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure(v_u_2008_, v_00_u03c3s_2009_, v_00_u03c6_2030_);
v___x_2032_ = 1;
v___x_2033_ = 1;
v___x_2034_ = l_Lean_Meta_mkLambdaFVars(v_ss_2012_, v_00_u03c6_2031_, v___x_2010_, v___x_2032_, v___x_2010_, v___x_2032_, v___x_2033_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_);
if (lean_obj_tag(v___x_2034_) == 0)
{
lean_object* v_a_2035_; lean_object* v___x_2036_; 
v_a_2035_ = lean_ctor_get(v___x_2034_, 0);
lean_inc(v_a_2035_);
lean_dec_ref(v___x_2034_);
v___x_2036_ = l_Lean_Meta_mkLambdaFVars(v_ss_2012_, v_hyps_2011_, v___x_2010_, v___x_2032_, v___x_2010_, v___x_2032_, v___x_2033_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_);
if (lean_obj_tag(v___x_2036_) == 0)
{
lean_object* v_a_2037_; lean_object* v___x_2039_; uint8_t v_isShared_2040_; uint8_t v_isSharedCheck_2047_; 
v_a_2037_ = lean_ctor_get(v___x_2036_, 0);
v_isSharedCheck_2047_ = !lean_is_exclusive(v___x_2036_);
if (v_isSharedCheck_2047_ == 0)
{
v___x_2039_ = v___x_2036_;
v_isShared_2040_ = v_isSharedCheck_2047_;
goto v_resetjp_2038_;
}
else
{
lean_inc(v_a_2037_);
lean_dec(v___x_2036_);
v___x_2039_ = lean_box(0);
v_isShared_2040_ = v_isSharedCheck_2047_;
goto v_resetjp_2038_;
}
v_resetjp_2038_:
{
lean_object* v___x_2041_; lean_object* v_00_u03c6_2042_; lean_object* v___x_2043_; lean_object* v___x_2045_; 
v___x_2041_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2041_, 0, v_hypName_2007_);
lean_ctor_set(v___x_2041_, 1, v_a_2028_);
lean_ctor_set(v___x_2041_, 2, v_a_2035_);
v_00_u03c6_2042_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_2041_);
v___x_2043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2043_, 0, v_a_2037_);
lean_ctor_set(v___x_2043_, 1, v_00_u03c6_2042_);
if (v_isShared_2040_ == 0)
{
lean_ctor_set(v___x_2039_, 0, v___x_2043_);
v___x_2045_ = v___x_2039_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v___x_2043_);
v___x_2045_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
return v___x_2045_;
}
}
}
else
{
lean_object* v_a_2048_; lean_object* v___x_2050_; uint8_t v_isShared_2051_; uint8_t v_isSharedCheck_2055_; 
lean_dec(v_a_2035_);
lean_dec(v_a_2028_);
lean_dec(v_hypName_2007_);
v_a_2048_ = lean_ctor_get(v___x_2036_, 0);
v_isSharedCheck_2055_ = !lean_is_exclusive(v___x_2036_);
if (v_isSharedCheck_2055_ == 0)
{
v___x_2050_ = v___x_2036_;
v_isShared_2051_ = v_isSharedCheck_2055_;
goto v_resetjp_2049_;
}
else
{
lean_inc(v_a_2048_);
lean_dec(v___x_2036_);
v___x_2050_ = lean_box(0);
v_isShared_2051_ = v_isSharedCheck_2055_;
goto v_resetjp_2049_;
}
v_resetjp_2049_:
{
lean_object* v___x_2053_; 
if (v_isShared_2051_ == 0)
{
v___x_2053_ = v___x_2050_;
goto v_reusejp_2052_;
}
else
{
lean_object* v_reuseFailAlloc_2054_; 
v_reuseFailAlloc_2054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2054_, 0, v_a_2048_);
v___x_2053_ = v_reuseFailAlloc_2054_;
goto v_reusejp_2052_;
}
v_reusejp_2052_:
{
return v___x_2053_;
}
}
}
}
else
{
lean_object* v_a_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2063_; 
lean_dec(v_a_2028_);
lean_dec_ref(v_hyps_2011_);
lean_dec(v_hypName_2007_);
v_a_2056_ = lean_ctor_get(v___x_2034_, 0);
v_isSharedCheck_2063_ = !lean_is_exclusive(v___x_2034_);
if (v_isSharedCheck_2063_ == 0)
{
v___x_2058_ = v___x_2034_;
v_isShared_2059_ = v_isSharedCheck_2063_;
goto v_resetjp_2057_;
}
else
{
lean_inc(v_a_2056_);
lean_dec(v___x_2034_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2063_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
lean_object* v___x_2061_; 
if (v_isShared_2059_ == 0)
{
v___x_2061_ = v___x_2058_;
goto v_reusejp_2060_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v_a_2056_);
v___x_2061_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2060_;
}
v_reusejp_2060_:
{
return v___x_2061_;
}
}
}
}
else
{
lean_object* v_a_2064_; lean_object* v___x_2066_; uint8_t v_isShared_2067_; uint8_t v_isSharedCheck_2071_; 
lean_dec(v_a_2026_);
lean_dec_ref(v_hyps_2011_);
lean_dec_ref(v_00_u03c3s_2009_);
lean_dec(v_u_2008_);
lean_dec(v_hypName_2007_);
v_a_2064_ = lean_ctor_get(v___x_2027_, 0);
v_isSharedCheck_2071_ = !lean_is_exclusive(v___x_2027_);
if (v_isSharedCheck_2071_ == 0)
{
v___x_2066_ = v___x_2027_;
v_isShared_2067_ = v_isSharedCheck_2071_;
goto v_resetjp_2065_;
}
else
{
lean_inc(v_a_2064_);
lean_dec(v___x_2027_);
v___x_2066_ = lean_box(0);
v_isShared_2067_ = v_isSharedCheck_2071_;
goto v_resetjp_2065_;
}
v_resetjp_2065_:
{
lean_object* v___x_2069_; 
if (v_isShared_2067_ == 0)
{
v___x_2069_ = v___x_2066_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v_a_2064_);
v___x_2069_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
return v___x_2069_;
}
}
}
}
else
{
lean_object* v_a_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2079_; 
lean_dec_ref(v_hyps_2011_);
lean_dec_ref(v_00_u03c3s_2009_);
lean_dec(v_u_2008_);
lean_dec(v_hypName_2007_);
v_a_2072_ = lean_ctor_get(v___x_2025_, 0);
v_isSharedCheck_2079_ = !lean_is_exclusive(v___x_2025_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2074_ = v___x_2025_;
v_isShared_2075_ = v_isSharedCheck_2079_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_a_2072_);
lean_dec(v___x_2025_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1___lam__0___boxed(lean_object* v_revertArgs_2080_, lean_object* v_hypName_2081_, lean_object* v_u_2082_, lean_object* v_00_u03c3s_2083_, lean_object* v___x_2084_, lean_object* v_hyps_2085_, lean_object* v_ss_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_){
_start:
{
uint8_t v___x_21542__boxed_2096_; lean_object* v_res_2097_; 
v___x_21542__boxed_2096_ = lean_unbox(v___x_2084_);
v_res_2097_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1___lam__0(v_revertArgs_2080_, v_hypName_2081_, v_u_2082_, v_00_u03c3s_2083_, v___x_21542__boxed_2096_, v_hyps_2085_, v_ss_2086_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_);
lean_dec(v___y_2094_);
lean_dec_ref(v___y_2093_);
lean_dec(v___y_2092_);
lean_dec_ref(v___y_2091_);
lean_dec(v___y_2090_);
lean_dec_ref(v___y_2089_);
lean_dec(v___y_2088_);
lean_dec_ref(v___y_2087_);
lean_dec_ref(v_ss_2086_);
lean_dec_ref(v_revertArgs_2080_);
return v_res_2097_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2098_; lean_object* v___x_2099_; 
v___x_2098_ = l_Lean_instInhabitedExpr;
v___x_2099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2099_, 0, v___x_2098_);
lean_ctor_set(v___x_2099_, 1, v___x_2098_);
return v___x_2099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1(lean_object* v_goal_2100_, lean_object* v_n_2101_, lean_object* v_hypName_2102_, lean_object* v_k_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_){
_start:
{
lean_object* v___x_2113_; uint8_t v___x_2114_; 
v___x_2113_ = lean_unsigned_to_nat(0u);
v___x_2114_ = lean_nat_dec_eq(v_n_2101_, v___x_2113_);
if (v___x_2114_ == 0)
{
lean_object* v_u_2115_; lean_object* v_00_u03c3s_2116_; lean_object* v_hyps_2117_; lean_object* v_target_2118_; lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2273_; 
v_u_2115_ = lean_ctor_get(v_goal_2100_, 0);
v_00_u03c3s_2116_ = lean_ctor_get(v_goal_2100_, 1);
v_hyps_2117_ = lean_ctor_get(v_goal_2100_, 2);
v_target_2118_ = lean_ctor_get(v_goal_2100_, 3);
v_isSharedCheck_2273_ = !lean_is_exclusive(v_goal_2100_);
if (v_isSharedCheck_2273_ == 0)
{
v___x_2120_ = v_goal_2100_;
v_isShared_2121_ = v_isSharedCheck_2273_;
goto v_resetjp_2119_;
}
else
{
lean_inc(v_target_2118_);
lean_inc(v_hyps_2117_);
lean_inc(v_00_u03c3s_2116_);
lean_inc(v_u_2115_);
lean_dec(v_goal_2100_);
v___x_2120_ = lean_box(0);
v_isShared_2121_ = v_isSharedCheck_2273_;
goto v_resetjp_2119_;
}
v_resetjp_2119_:
{
lean_object* v_T_2122_; lean_object* v_f_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v_a_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v_revertArgs_2130_; lean_object* v___y_2132_; lean_object* v___y_2133_; lean_object* v___y_2134_; lean_object* v___y_2135_; lean_object* v___y_2136_; lean_object* v___y_2137_; lean_object* v___y_2138_; lean_object* v___y_2139_; lean_object* v___y_2140_; lean_object* v___y_2141_; lean_object* v___y_2142_; lean_object* v___y_2143_; lean_object* v___x_2182_; lean_object* v___f_2183_; lean_object* v___y_2185_; lean_object* v___y_2186_; lean_object* v___y_2187_; lean_object* v___y_2188_; lean_object* v___y_2189_; lean_object* v___y_2190_; lean_object* v___y_2191_; lean_object* v___y_2192_; lean_object* v___x_2247_; uint8_t v___x_2248_; 
v_T_2122_ = l_Lean_Expr_consumeMData(v_target_2118_);
v_f_2123_ = l_Lean_Expr_getAppFn(v_T_2122_);
v___x_2124_ = l_Lean_Expr_getAppNumArgs(v_T_2122_);
v___x_2125_ = lean_mk_empty_array_with_capacity(v___x_2124_);
lean_dec(v___x_2124_);
lean_inc_ref(v_T_2122_);
v_a_2126_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_T_2122_, v___x_2125_);
lean_inc(v_n_2101_);
lean_inc_ref(v_a_2126_);
v___x_2127_ = l_Array_toSubarray___redArg(v_a_2126_, v___x_2113_, v_n_2101_);
v___x_2128_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__1));
v___x_2129_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__1___redArg(v___x_2127_, v___x_2128_);
v_revertArgs_2130_ = l_Array_reverse___redArg(v___x_2129_);
v___x_2182_ = lean_box(v___x_2114_);
lean_inc_ref(v_hyps_2117_);
lean_inc_ref(v_00_u03c3s_2116_);
lean_inc(v_u_2115_);
lean_inc_ref(v_revertArgs_2130_);
v___f_2183_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1___lam__0___boxed), 16, 6);
lean_closure_set(v___f_2183_, 0, v_revertArgs_2130_);
lean_closure_set(v___f_2183_, 1, v_hypName_2102_);
lean_closure_set(v___f_2183_, 2, v_u_2115_);
lean_closure_set(v___f_2183_, 3, v_00_u03c3s_2116_);
lean_closure_set(v___f_2183_, 4, v___x_2182_);
lean_closure_set(v___f_2183_, 5, v_hyps_2117_);
v___x_2247_ = lean_array_get_size(v_revertArgs_2130_);
v___x_2248_ = lean_nat_dec_eq(v___x_2247_, v_n_2101_);
if (v___x_2248_ == 0)
{
lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v_a_2265_; lean_object* v___x_2267_; uint8_t v_isShared_2268_; uint8_t v_isSharedCheck_2272_; 
lean_dec_ref(v___f_2183_);
lean_dec_ref(v_revertArgs_2130_);
lean_dec_ref(v_a_2126_);
lean_dec_ref(v_f_2123_);
lean_del_object(v___x_2120_);
lean_dec_ref(v_target_2118_);
lean_dec_ref(v_hyps_2117_);
lean_dec_ref(v_00_u03c3s_2116_);
lean_dec(v_u_2115_);
lean_dec_ref(v_k_2103_);
v___x_2249_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__15, &l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__15_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__15);
v___x_2250_ = l_Nat_reprFast(v_n_2101_);
v___x_2251_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2251_, 0, v___x_2250_);
v___x_2252_ = l_Lean_MessageData_ofFormat(v___x_2251_);
v___x_2253_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2253_, 0, v___x_2249_);
lean_ctor_set(v___x_2253_, 1, v___x_2252_);
v___x_2254_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__17, &l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__17_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__17);
v___x_2255_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2255_, 0, v___x_2253_);
lean_ctor_set(v___x_2255_, 1, v___x_2254_);
v___x_2256_ = l_Lean_MessageData_ofExpr(v_T_2122_);
v___x_2257_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2257_, 0, v___x_2255_);
lean_ctor_set(v___x_2257_, 1, v___x_2256_);
v___x_2258_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__19, &l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__19_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__19);
v___x_2259_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2259_, 0, v___x_2257_);
lean_ctor_set(v___x_2259_, 1, v___x_2258_);
v___x_2260_ = l_Nat_reprFast(v___x_2247_);
v___x_2261_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2261_, 0, v___x_2260_);
v___x_2262_ = l_Lean_MessageData_ofFormat(v___x_2261_);
v___x_2263_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2263_, 0, v___x_2259_);
lean_ctor_set(v___x_2263_, 1, v___x_2262_);
v___x_2264_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__8___redArg(v___x_2263_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_);
v_a_2265_ = lean_ctor_get(v___x_2264_, 0);
v_isSharedCheck_2272_ = !lean_is_exclusive(v___x_2264_);
if (v_isSharedCheck_2272_ == 0)
{
v___x_2267_ = v___x_2264_;
v_isShared_2268_ = v_isSharedCheck_2272_;
goto v_resetjp_2266_;
}
else
{
lean_inc(v_a_2265_);
lean_dec(v___x_2264_);
v___x_2267_ = lean_box(0);
v_isShared_2268_ = v_isSharedCheck_2272_;
goto v_resetjp_2266_;
}
v_resetjp_2266_:
{
lean_object* v___x_2270_; 
if (v_isShared_2268_ == 0)
{
v___x_2270_ = v___x_2267_;
goto v_reusejp_2269_;
}
else
{
lean_object* v_reuseFailAlloc_2271_; 
v_reuseFailAlloc_2271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2271_, 0, v_a_2265_);
v___x_2270_ = v_reuseFailAlloc_2271_;
goto v_reusejp_2269_;
}
v_reusejp_2269_:
{
return v___x_2270_;
}
}
}
else
{
lean_dec_ref(v_T_2122_);
v___y_2185_ = v___y_2104_;
v___y_2186_ = v___y_2105_;
v___y_2187_ = v___y_2106_;
v___y_2188_ = v___y_2107_;
v___y_2189_ = v___y_2108_;
v___y_2190_ = v___y_2109_;
v___y_2191_ = v___y_2110_;
v___y_2192_ = v___y_2111_;
goto v___jp_2184_;
}
v___jp_2131_:
{
lean_object* v___x_2144_; 
v___x_2144_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v___y_2142_, v___y_2141_);
if (lean_obj_tag(v___x_2144_) == 0)
{
lean_object* v_a_2145_; lean_object* v_H_2146_; lean_object* v___x_2147_; lean_object* v_fst_2148_; lean_object* v_snd_2149_; lean_object* v___x_2151_; uint8_t v_isShared_2152_; uint8_t v_isSharedCheck_2181_; 
v_a_2145_ = lean_ctor_get(v___x_2144_, 0);
lean_inc(v_a_2145_);
lean_dec_ref(v___x_2144_);
lean_inc_ref(v___y_2143_);
v_H_2146_ = l_Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps(v___y_2143_, v_a_2145_);
lean_inc_ref(v___y_2143_);
lean_inc(v_u_2115_);
v___x_2147_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd(v_u_2115_, v___y_2143_, v_H_2146_, v___y_2137_);
v_fst_2148_ = lean_ctor_get(v___x_2147_, 0);
v_snd_2149_ = lean_ctor_get(v___x_2147_, 1);
v_isSharedCheck_2181_ = !lean_is_exclusive(v___x_2147_);
if (v_isSharedCheck_2181_ == 0)
{
v___x_2151_ = v___x_2147_;
v_isShared_2152_ = v_isSharedCheck_2181_;
goto v_resetjp_2150_;
}
else
{
lean_inc(v_snd_2149_);
lean_inc(v_fst_2148_);
lean_dec(v___x_2147_);
v___x_2151_ = lean_box(0);
v_isShared_2152_ = v_isSharedCheck_2181_;
goto v_resetjp_2150_;
}
v_resetjp_2150_:
{
lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v_goal_x27_2158_; 
v___x_2153_ = lean_array_get_size(v_a_2126_);
v___x_2154_ = l_Array_toSubarray___redArg(v_a_2126_, v_n_2101_, v___x_2153_);
v___x_2155_ = l_Subarray_copy___redArg(v___x_2154_);
v___x_2156_ = l_Lean_mkAppRev(v_f_2123_, v___x_2155_);
lean_dec_ref(v___x_2155_);
lean_inc(v_fst_2148_);
lean_inc(v_u_2115_);
if (v_isShared_2121_ == 0)
{
lean_ctor_set(v___x_2120_, 3, v___x_2156_);
lean_ctor_set(v___x_2120_, 2, v_fst_2148_);
lean_ctor_set(v___x_2120_, 1, v___y_2143_);
v_goal_x27_2158_ = v___x_2120_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v_u_2115_);
lean_ctor_set(v_reuseFailAlloc_2180_, 1, v___y_2143_);
lean_ctor_set(v_reuseFailAlloc_2180_, 2, v_fst_2148_);
lean_ctor_set(v_reuseFailAlloc_2180_, 3, v___x_2156_);
v_goal_x27_2158_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
lean_object* v___x_2159_; 
lean_inc(v___y_2139_);
lean_inc_ref(v___y_2135_);
lean_inc(v___y_2141_);
lean_inc_ref(v___y_2134_);
lean_inc(v___y_2138_);
lean_inc_ref(v___y_2132_);
lean_inc(v___y_2136_);
lean_inc_ref(v___y_2133_);
v___x_2159_ = lean_apply_10(v_k_2103_, v_goal_x27_2158_, v___y_2133_, v___y_2136_, v___y_2132_, v___y_2138_, v___y_2134_, v___y_2141_, v___y_2135_, v___y_2139_, lean_box(0));
if (lean_obj_tag(v___x_2159_) == 0)
{
lean_object* v_a_2160_; lean_object* v___x_2161_; 
v_a_2160_ = lean_ctor_get(v___x_2159_, 0);
lean_inc(v_a_2160_);
lean_dec_ref(v___x_2159_);
lean_inc(v___y_2139_);
lean_inc_ref(v___y_2135_);
lean_inc(v___y_2141_);
lean_inc_ref(v___y_2134_);
lean_inc_ref(v___y_2140_);
v___x_2161_ = lean_infer_type(v___y_2140_, v___y_2134_, v___y_2141_, v___y_2135_, v___y_2139_);
if (lean_obj_tag(v___x_2161_) == 0)
{
lean_object* v_a_2162_; lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2179_; 
v_a_2162_ = lean_ctor_get(v___x_2161_, 0);
v_isSharedCheck_2179_ = !lean_is_exclusive(v___x_2161_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_2164_ = v___x_2161_;
v_isShared_2165_ = v_isSharedCheck_2179_;
goto v_resetjp_2163_;
}
else
{
lean_inc(v_a_2162_);
lean_dec(v___x_2161_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2179_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2169_; 
v___x_2166_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__12___closed__1));
v___x_2167_ = lean_box(0);
if (v_isShared_2152_ == 0)
{
lean_ctor_set_tag(v___x_2151_, 1);
lean_ctor_set(v___x_2151_, 1, v___x_2167_);
lean_ctor_set(v___x_2151_, 0, v_u_2115_);
v___x_2169_ = v___x_2151_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v_u_2115_);
lean_ctor_set(v_reuseFailAlloc_2178_, 1, v___x_2167_);
v___x_2169_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v_prf_2174_; lean_object* v___x_2176_; 
v___x_2170_ = l_Lean_mkConst(v___x_2166_, v___x_2169_);
v___x_2171_ = l_Lean_mkAppN(v_fst_2148_, v_revertArgs_2130_);
v___x_2172_ = l_Lean_mkAppN(v_snd_2149_, v_revertArgs_2130_);
v___x_2173_ = l_Lean_mkAppN(v_a_2160_, v_revertArgs_2130_);
lean_dec_ref(v_revertArgs_2130_);
v_prf_2174_ = l_Lean_mkApp8(v___x_2170_, v_00_u03c3s_2116_, v_a_2162_, v_hyps_2117_, v___x_2171_, v_target_2118_, v___y_2140_, v___x_2172_, v___x_2173_);
if (v_isShared_2165_ == 0)
{
lean_ctor_set(v___x_2164_, 0, v_prf_2174_);
v___x_2176_ = v___x_2164_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v_prf_2174_);
v___x_2176_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
return v___x_2176_;
}
}
}
}
else
{
lean_dec(v_a_2160_);
lean_del_object(v___x_2151_);
lean_dec(v_snd_2149_);
lean_dec(v_fst_2148_);
lean_dec_ref(v___y_2140_);
lean_dec_ref(v_revertArgs_2130_);
lean_dec_ref(v_target_2118_);
lean_dec_ref(v_hyps_2117_);
lean_dec_ref(v_00_u03c3s_2116_);
lean_dec(v_u_2115_);
return v___x_2161_;
}
}
else
{
lean_del_object(v___x_2151_);
lean_dec(v_snd_2149_);
lean_dec(v_fst_2148_);
lean_dec_ref(v___y_2140_);
lean_dec_ref(v_revertArgs_2130_);
lean_dec_ref(v_target_2118_);
lean_dec_ref(v_hyps_2117_);
lean_dec_ref(v_00_u03c3s_2116_);
lean_dec(v_u_2115_);
return v___x_2159_;
}
}
}
}
else
{
lean_dec_ref(v___y_2143_);
lean_dec_ref(v___y_2140_);
lean_dec_ref(v___y_2137_);
lean_dec_ref(v_revertArgs_2130_);
lean_dec_ref(v_a_2126_);
lean_dec_ref(v_f_2123_);
lean_del_object(v___x_2120_);
lean_dec_ref(v_target_2118_);
lean_dec_ref(v_hyps_2117_);
lean_dec_ref(v_00_u03c3s_2116_);
lean_dec(v_u_2115_);
lean_dec_ref(v_k_2103_);
lean_dec(v_n_2101_);
return v___x_2144_;
}
}
v___jp_2184_:
{
size_t v_sz_2193_; size_t v___x_2194_; lean_object* v___x_2195_; 
v_sz_2193_ = lean_array_size(v_revertArgs_2130_);
v___x_2194_ = ((size_t)0ULL);
lean_inc_ref(v_revertArgs_2130_);
v___x_2195_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__3(v_sz_2193_, v___x_2194_, v_revertArgs_2130_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_);
if (lean_obj_tag(v___x_2195_) == 0)
{
lean_object* v_a_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; 
v_a_2196_ = lean_ctor_get(v___x_2195_, 0);
lean_inc(v_a_2196_);
lean_dec_ref(v___x_2195_);
v___x_2197_ = lean_array_get_size(v_a_2196_);
v___x_2198_ = lean_mk_empty_array_with_capacity(v___x_2197_);
v___x_2199_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__4___redArg(v_a_2196_, v___x_2197_, v___x_2113_, v___x_2198_, v___y_2191_, v___y_2192_);
if (lean_obj_tag(v___x_2199_) == 0)
{
lean_object* v_a_2200_; lean_object* v___x_2201_; uint8_t v___x_2202_; lean_object* v___x_2203_; 
v_a_2200_ = lean_ctor_get(v___x_2199_, 0);
lean_inc(v_a_2200_);
lean_dec_ref(v___x_2199_);
v___x_2201_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1___closed__0, &l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1___closed__0_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1___closed__0);
v___x_2202_ = 0;
v___x_2203_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5___redArg(v___x_2201_, v_a_2200_, v___f_2183_, v___x_2202_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_);
if (lean_obj_tag(v___x_2203_) == 0)
{
lean_object* v_a_2204_; lean_object* v_fst_2205_; lean_object* v_snd_2206_; lean_object* v___x_2207_; 
v_a_2204_ = lean_ctor_get(v___x_2203_, 0);
lean_inc(v_a_2204_);
lean_dec_ref(v___x_2203_);
v_fst_2205_ = lean_ctor_get(v_a_2204_, 0);
lean_inc(v_fst_2205_);
v_snd_2206_ = lean_ctor_get(v_a_2204_, 1);
lean_inc(v_snd_2206_);
lean_dec(v_a_2204_);
lean_inc_ref(v_revertArgs_2130_);
v___x_2207_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__6(v_sz_2193_, v___x_2194_, v_revertArgs_2130_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_);
if (lean_obj_tag(v___x_2207_) == 0)
{
lean_object* v_a_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; 
v_a_2208_ = lean_ctor_get(v___x_2207_, 0);
lean_inc(v_a_2208_);
lean_dec_ref(v___x_2207_);
v___x_2209_ = lean_array_to_list(v_a_2208_);
v___x_2210_ = l_Lean_Meta_mkAndIntroN(v___x_2209_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_);
if (lean_obj_tag(v___x_2210_) == 0)
{
lean_object* v_a_2211_; uint8_t v___x_2212_; 
v_a_2211_ = lean_ctor_get(v___x_2210_, 0);
lean_inc(v_a_2211_);
lean_dec_ref(v___x_2210_);
v___x_2212_ = lean_nat_dec_lt(v___x_2113_, v___x_2197_);
if (v___x_2212_ == 0)
{
lean_dec(v_a_2196_);
lean_inc_ref(v_00_u03c3s_2116_);
v___y_2132_ = v___y_2187_;
v___y_2133_ = v___y_2185_;
v___y_2134_ = v___y_2189_;
v___y_2135_ = v___y_2191_;
v___y_2136_ = v___y_2186_;
v___y_2137_ = v_snd_2206_;
v___y_2138_ = v___y_2188_;
v___y_2139_ = v___y_2192_;
v___y_2140_ = v_a_2211_;
v___y_2141_ = v___y_2190_;
v___y_2142_ = v_fst_2205_;
v___y_2143_ = v_00_u03c3s_2116_;
goto v___jp_2131_;
}
else
{
size_t v___x_2213_; lean_object* v___x_2214_; 
v___x_2213_ = lean_usize_of_nat(v___x_2197_);
lean_inc_ref(v_00_u03c3s_2116_);
lean_inc(v_u_2115_);
v___x_2214_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__7(v_u_2115_, v_a_2196_, v___x_2213_, v___x_2194_, v_00_u03c3s_2116_);
lean_dec(v_a_2196_);
v___y_2132_ = v___y_2187_;
v___y_2133_ = v___y_2185_;
v___y_2134_ = v___y_2189_;
v___y_2135_ = v___y_2191_;
v___y_2136_ = v___y_2186_;
v___y_2137_ = v_snd_2206_;
v___y_2138_ = v___y_2188_;
v___y_2139_ = v___y_2192_;
v___y_2140_ = v_a_2211_;
v___y_2141_ = v___y_2190_;
v___y_2142_ = v_fst_2205_;
v___y_2143_ = v___x_2214_;
goto v___jp_2131_;
}
}
else
{
lean_dec(v_snd_2206_);
lean_dec(v_fst_2205_);
lean_dec(v_a_2196_);
lean_dec_ref(v_revertArgs_2130_);
lean_dec_ref(v_a_2126_);
lean_dec_ref(v_f_2123_);
lean_del_object(v___x_2120_);
lean_dec_ref(v_target_2118_);
lean_dec_ref(v_hyps_2117_);
lean_dec_ref(v_00_u03c3s_2116_);
lean_dec(v_u_2115_);
lean_dec_ref(v_k_2103_);
lean_dec(v_n_2101_);
return v___x_2210_;
}
}
else
{
lean_object* v_a_2215_; lean_object* v___x_2217_; uint8_t v_isShared_2218_; uint8_t v_isSharedCheck_2222_; 
lean_dec(v_snd_2206_);
lean_dec(v_fst_2205_);
lean_dec(v_a_2196_);
lean_dec_ref(v_revertArgs_2130_);
lean_dec_ref(v_a_2126_);
lean_dec_ref(v_f_2123_);
lean_del_object(v___x_2120_);
lean_dec_ref(v_target_2118_);
lean_dec_ref(v_hyps_2117_);
lean_dec_ref(v_00_u03c3s_2116_);
lean_dec(v_u_2115_);
lean_dec_ref(v_k_2103_);
lean_dec(v_n_2101_);
v_a_2215_ = lean_ctor_get(v___x_2207_, 0);
v_isSharedCheck_2222_ = !lean_is_exclusive(v___x_2207_);
if (v_isSharedCheck_2222_ == 0)
{
v___x_2217_ = v___x_2207_;
v_isShared_2218_ = v_isSharedCheck_2222_;
goto v_resetjp_2216_;
}
else
{
lean_inc(v_a_2215_);
lean_dec(v___x_2207_);
v___x_2217_ = lean_box(0);
v_isShared_2218_ = v_isSharedCheck_2222_;
goto v_resetjp_2216_;
}
v_resetjp_2216_:
{
lean_object* v___x_2220_; 
if (v_isShared_2218_ == 0)
{
v___x_2220_ = v___x_2217_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2221_; 
v_reuseFailAlloc_2221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2221_, 0, v_a_2215_);
v___x_2220_ = v_reuseFailAlloc_2221_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
return v___x_2220_;
}
}
}
}
else
{
lean_object* v_a_2223_; lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2230_; 
lean_dec(v_a_2196_);
lean_dec_ref(v_revertArgs_2130_);
lean_dec_ref(v_a_2126_);
lean_dec_ref(v_f_2123_);
lean_del_object(v___x_2120_);
lean_dec_ref(v_target_2118_);
lean_dec_ref(v_hyps_2117_);
lean_dec_ref(v_00_u03c3s_2116_);
lean_dec(v_u_2115_);
lean_dec_ref(v_k_2103_);
lean_dec(v_n_2101_);
v_a_2223_ = lean_ctor_get(v___x_2203_, 0);
v_isSharedCheck_2230_ = !lean_is_exclusive(v___x_2203_);
if (v_isSharedCheck_2230_ == 0)
{
v___x_2225_ = v___x_2203_;
v_isShared_2226_ = v_isSharedCheck_2230_;
goto v_resetjp_2224_;
}
else
{
lean_inc(v_a_2223_);
lean_dec(v___x_2203_);
v___x_2225_ = lean_box(0);
v_isShared_2226_ = v_isSharedCheck_2230_;
goto v_resetjp_2224_;
}
v_resetjp_2224_:
{
lean_object* v___x_2228_; 
if (v_isShared_2226_ == 0)
{
v___x_2228_ = v___x_2225_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v_a_2223_);
v___x_2228_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
return v___x_2228_;
}
}
}
}
else
{
lean_object* v_a_2231_; lean_object* v___x_2233_; uint8_t v_isShared_2234_; uint8_t v_isSharedCheck_2238_; 
lean_dec(v_a_2196_);
lean_dec_ref(v___f_2183_);
lean_dec_ref(v_revertArgs_2130_);
lean_dec_ref(v_a_2126_);
lean_dec_ref(v_f_2123_);
lean_del_object(v___x_2120_);
lean_dec_ref(v_target_2118_);
lean_dec_ref(v_hyps_2117_);
lean_dec_ref(v_00_u03c3s_2116_);
lean_dec(v_u_2115_);
lean_dec_ref(v_k_2103_);
lean_dec(v_n_2101_);
v_a_2231_ = lean_ctor_get(v___x_2199_, 0);
v_isSharedCheck_2238_ = !lean_is_exclusive(v___x_2199_);
if (v_isSharedCheck_2238_ == 0)
{
v___x_2233_ = v___x_2199_;
v_isShared_2234_ = v_isSharedCheck_2238_;
goto v_resetjp_2232_;
}
else
{
lean_inc(v_a_2231_);
lean_dec(v___x_2199_);
v___x_2233_ = lean_box(0);
v_isShared_2234_ = v_isSharedCheck_2238_;
goto v_resetjp_2232_;
}
v_resetjp_2232_:
{
lean_object* v___x_2236_; 
if (v_isShared_2234_ == 0)
{
v___x_2236_ = v___x_2233_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v_a_2231_);
v___x_2236_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
return v___x_2236_;
}
}
}
}
else
{
lean_object* v_a_2239_; lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2246_; 
lean_dec_ref(v___f_2183_);
lean_dec_ref(v_revertArgs_2130_);
lean_dec_ref(v_a_2126_);
lean_dec_ref(v_f_2123_);
lean_del_object(v___x_2120_);
lean_dec_ref(v_target_2118_);
lean_dec_ref(v_hyps_2117_);
lean_dec_ref(v_00_u03c3s_2116_);
lean_dec(v_u_2115_);
lean_dec_ref(v_k_2103_);
lean_dec(v_n_2101_);
v_a_2239_ = lean_ctor_get(v___x_2195_, 0);
v_isSharedCheck_2246_ = !lean_is_exclusive(v___x_2195_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2241_ = v___x_2195_;
v_isShared_2242_ = v_isSharedCheck_2246_;
goto v_resetjp_2240_;
}
else
{
lean_inc(v_a_2239_);
lean_dec(v___x_2195_);
v___x_2241_ = lean_box(0);
v_isShared_2242_ = v_isSharedCheck_2246_;
goto v_resetjp_2240_;
}
v_resetjp_2240_:
{
lean_object* v___x_2244_; 
if (v_isShared_2242_ == 0)
{
v___x_2244_ = v___x_2241_;
goto v_reusejp_2243_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v_a_2239_);
v___x_2244_ = v_reuseFailAlloc_2245_;
goto v_reusejp_2243_;
}
v_reusejp_2243_:
{
return v___x_2244_;
}
}
}
}
}
}
else
{
lean_object* v___x_2274_; 
lean_dec(v_hypName_2102_);
lean_dec(v_n_2101_);
lean_inc(v___y_2111_);
lean_inc_ref(v___y_2110_);
lean_inc(v___y_2109_);
lean_inc_ref(v___y_2108_);
lean_inc(v___y_2107_);
lean_inc_ref(v___y_2106_);
lean_inc(v___y_2105_);
lean_inc_ref(v___y_2104_);
v___x_2274_ = lean_apply_10(v_k_2103_, v_goal_2100_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_, lean_box(0));
return v___x_2274_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1___boxed(lean_object* v_goal_2275_, lean_object* v_n_2276_, lean_object* v_hypName_2277_, lean_object* v_k_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_){
_start:
{
lean_object* v_res_2288_; 
v_res_2288_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1(v_goal_2275_, v_n_2276_, v_hypName_2277_, v_k_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_);
lean_dec(v___y_2286_);
lean_dec_ref(v___y_2285_);
lean_dec(v___y_2284_);
lean_dec_ref(v___y_2283_);
lean_dec(v___y_2282_);
lean_dec_ref(v___y_2281_);
lean_dec(v___y_2280_);
lean_dec_ref(v___y_2279_);
return v_res_2288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__1(lean_object* v___x_2292_, lean_object* v_snd_2293_, lean_object* v___y_2294_, lean_object* v_fst_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_){
_start:
{
lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; 
v___x_2305_ = lean_st_mk_ref(v___x_2292_);
v___x_2306_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__1___closed__1));
v___x_2307_ = l_Lean_Core_mkFreshUserName(v___x_2306_, v___y_2302_, v___y_2303_);
if (lean_obj_tag(v___x_2307_) == 0)
{
lean_object* v_a_2308_; lean_object* v___f_2309_; lean_object* v___x_2310_; 
v_a_2308_ = lean_ctor_get(v___x_2307_, 0);
lean_inc(v_a_2308_);
lean_dec_ref(v___x_2307_);
lean_inc(v___x_2305_);
v___f_2309_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__0___boxed), 11, 1);
lean_closure_set(v___f_2309_, 0, v___x_2305_);
v___x_2310_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1(v_snd_2293_, v___y_2294_, v_a_2308_, v___f_2309_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_);
if (lean_obj_tag(v___x_2310_) == 0)
{
lean_object* v_a_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; 
v_a_2311_ = lean_ctor_get(v___x_2310_, 0);
lean_inc(v_a_2311_);
lean_dec_ref(v___x_2310_);
v___x_2312_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2___redArg(v_fst_2295_, v_a_2311_, v___y_2301_);
lean_dec_ref(v___x_2312_);
v___x_2313_ = lean_st_ref_get(v___x_2305_);
lean_dec(v___x_2305_);
v___x_2314_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2313_, v___y_2297_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_);
return v___x_2314_;
}
else
{
lean_object* v_a_2315_; lean_object* v___x_2317_; uint8_t v_isShared_2318_; uint8_t v_isSharedCheck_2322_; 
lean_dec(v___x_2305_);
lean_dec(v_fst_2295_);
v_a_2315_ = lean_ctor_get(v___x_2310_, 0);
v_isSharedCheck_2322_ = !lean_is_exclusive(v___x_2310_);
if (v_isSharedCheck_2322_ == 0)
{
v___x_2317_ = v___x_2310_;
v_isShared_2318_ = v_isSharedCheck_2322_;
goto v_resetjp_2316_;
}
else
{
lean_inc(v_a_2315_);
lean_dec(v___x_2310_);
v___x_2317_ = lean_box(0);
v_isShared_2318_ = v_isSharedCheck_2322_;
goto v_resetjp_2316_;
}
v_resetjp_2316_:
{
lean_object* v___x_2320_; 
if (v_isShared_2318_ == 0)
{
v___x_2320_ = v___x_2317_;
goto v_reusejp_2319_;
}
else
{
lean_object* v_reuseFailAlloc_2321_; 
v_reuseFailAlloc_2321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2321_, 0, v_a_2315_);
v___x_2320_ = v_reuseFailAlloc_2321_;
goto v_reusejp_2319_;
}
v_reusejp_2319_:
{
return v___x_2320_;
}
}
}
}
else
{
lean_object* v_a_2323_; lean_object* v___x_2325_; uint8_t v_isShared_2326_; uint8_t v_isSharedCheck_2330_; 
lean_dec(v___x_2305_);
lean_dec(v_fst_2295_);
lean_dec(v___y_2294_);
lean_dec_ref(v_snd_2293_);
v_a_2323_ = lean_ctor_get(v___x_2307_, 0);
v_isSharedCheck_2330_ = !lean_is_exclusive(v___x_2307_);
if (v_isSharedCheck_2330_ == 0)
{
v___x_2325_ = v___x_2307_;
v_isShared_2326_ = v_isSharedCheck_2330_;
goto v_resetjp_2324_;
}
else
{
lean_inc(v_a_2323_);
lean_dec(v___x_2307_);
v___x_2325_ = lean_box(0);
v_isShared_2326_ = v_isSharedCheck_2330_;
goto v_resetjp_2324_;
}
v_resetjp_2324_:
{
lean_object* v___x_2328_; 
if (v_isShared_2326_ == 0)
{
v___x_2328_ = v___x_2325_;
goto v_reusejp_2327_;
}
else
{
lean_object* v_reuseFailAlloc_2329_; 
v_reuseFailAlloc_2329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2329_, 0, v_a_2323_);
v___x_2328_ = v_reuseFailAlloc_2329_;
goto v_reusejp_2327_;
}
v_reusejp_2327_:
{
return v___x_2328_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__1___boxed(lean_object* v___x_2331_, lean_object* v_snd_2332_, lean_object* v___y_2333_, lean_object* v_fst_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_){
_start:
{
lean_object* v_res_2344_; 
v_res_2344_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__1(v___x_2331_, v_snd_2332_, v___y_2333_, v_fst_2334_, v___y_2335_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_);
lean_dec(v___y_2342_);
lean_dec_ref(v___y_2341_);
lean_dec(v___y_2340_);
lean_dec_ref(v___y_2339_);
lean_dec(v___y_2338_);
lean_dec_ref(v___y_2337_);
lean_dec(v___y_2336_);
lean_dec_ref(v___y_2335_);
return v_res_2344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__3(lean_object* v___x_2345_, lean_object* v_val_2346_, lean_object* v_h_2347_, lean_object* v_a_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_){
_start:
{
lean_object* v___x_2358_; lean_object* v___f_2359_; lean_object* v___x_2360_; 
v___x_2358_ = lean_st_mk_ref(v___x_2345_);
lean_inc(v___x_2358_);
v___f_2359_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__0___boxed), 11, 1);
lean_closure_set(v___f_2359_, 0, v___x_2358_);
v___x_2360_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevert___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__4(v_val_2346_, v_h_2347_, v___f_2359_, v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_);
if (lean_obj_tag(v___x_2360_) == 0)
{
lean_object* v_a_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; 
v_a_2361_ = lean_ctor_get(v___x_2360_, 0);
lean_inc(v_a_2361_);
lean_dec_ref(v___x_2360_);
v___x_2362_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2___redArg(v_a_2348_, v_a_2361_, v___y_2354_);
lean_dec_ref(v___x_2362_);
v___x_2363_ = lean_st_ref_get(v___x_2358_);
lean_dec(v___x_2358_);
v___x_2364_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2363_, v___y_2350_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_);
return v___x_2364_;
}
else
{
lean_object* v_a_2365_; lean_object* v___x_2367_; uint8_t v_isShared_2368_; uint8_t v_isSharedCheck_2372_; 
lean_dec(v___x_2358_);
lean_dec(v_a_2348_);
v_a_2365_ = lean_ctor_get(v___x_2360_, 0);
v_isSharedCheck_2372_ = !lean_is_exclusive(v___x_2360_);
if (v_isSharedCheck_2372_ == 0)
{
v___x_2367_ = v___x_2360_;
v_isShared_2368_ = v_isSharedCheck_2372_;
goto v_resetjp_2366_;
}
else
{
lean_inc(v_a_2365_);
lean_dec(v___x_2360_);
v___x_2367_ = lean_box(0);
v_isShared_2368_ = v_isSharedCheck_2372_;
goto v_resetjp_2366_;
}
v_resetjp_2366_:
{
lean_object* v___x_2370_; 
if (v_isShared_2368_ == 0)
{
v___x_2370_ = v___x_2367_;
goto v_reusejp_2369_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v_a_2365_);
v___x_2370_ = v_reuseFailAlloc_2371_;
goto v_reusejp_2369_;
}
v_reusejp_2369_:
{
return v___x_2370_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__3___boxed(lean_object* v___x_2373_, lean_object* v_val_2374_, lean_object* v_h_2375_, lean_object* v_a_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_){
_start:
{
lean_object* v_res_2386_; 
v_res_2386_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__3(v___x_2373_, v_val_2374_, v_h_2375_, v_a_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_);
lean_dec(v___y_2384_);
lean_dec_ref(v___y_2383_);
lean_dec(v___y_2382_);
lean_dec_ref(v___y_2381_);
lean_dec(v___y_2380_);
lean_dec_ref(v___y_2379_);
lean_dec(v___y_2378_);
lean_dec_ref(v___y_2377_);
return v_res_2386_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5___redArg(lean_object* v_msg_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_){
_start:
{
lean_object* v_ref_2393_; lean_object* v___x_2394_; lean_object* v_a_2395_; lean_object* v___x_2397_; uint8_t v_isShared_2398_; uint8_t v_isSharedCheck_2403_; 
v_ref_2393_ = lean_ctor_get(v___y_2390_, 5);
v___x_2394_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5_spec__14(v_msg_2387_, v___y_2388_, v___y_2389_, v___y_2390_, v___y_2391_);
v_a_2395_ = lean_ctor_get(v___x_2394_, 0);
v_isSharedCheck_2403_ = !lean_is_exclusive(v___x_2394_);
if (v_isSharedCheck_2403_ == 0)
{
v___x_2397_ = v___x_2394_;
v_isShared_2398_ = v_isSharedCheck_2403_;
goto v_resetjp_2396_;
}
else
{
lean_inc(v_a_2395_);
lean_dec(v___x_2394_);
v___x_2397_ = lean_box(0);
v_isShared_2398_ = v_isSharedCheck_2403_;
goto v_resetjp_2396_;
}
v_resetjp_2396_:
{
lean_object* v___x_2399_; lean_object* v___x_2401_; 
lean_inc(v_ref_2393_);
v___x_2399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2399_, 0, v_ref_2393_);
lean_ctor_set(v___x_2399_, 1, v_a_2395_);
if (v_isShared_2398_ == 0)
{
lean_ctor_set_tag(v___x_2397_, 1);
lean_ctor_set(v___x_2397_, 0, v___x_2399_);
v___x_2401_ = v___x_2397_;
goto v_reusejp_2400_;
}
else
{
lean_object* v_reuseFailAlloc_2402_; 
v_reuseFailAlloc_2402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2402_, 0, v___x_2399_);
v___x_2401_ = v_reuseFailAlloc_2402_;
goto v_reusejp_2400_;
}
v_reusejp_2400_:
{
return v___x_2401_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5___redArg___boxed(lean_object* v_msg_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_){
_start:
{
lean_object* v_res_2410_; 
v_res_2410_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5___redArg(v_msg_2404_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_);
lean_dec(v___y_2408_);
lean_dec_ref(v___y_2407_);
lean_dec(v___y_2406_);
lean_dec_ref(v___y_2405_);
return v_res_2410_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__11(void){
_start:
{
lean_object* v___x_2435_; lean_object* v___x_2436_; 
v___x_2435_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__10));
v___x_2436_ = l_Lean_stringToMessageData(v___x_2435_);
return v___x_2436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert(lean_object* v_x_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_){
_start:
{
lean_object* v___y_2448_; lean_object* v___y_2449_; lean_object* v___y_2450_; lean_object* v___y_2451_; lean_object* v___y_2452_; lean_object* v___y_2453_; lean_object* v___y_2454_; lean_object* v___y_2455_; lean_object* v___y_2456_; lean_object* v___y_2457_; lean_object* v___y_2458_; lean_object* v___x_2462_; uint8_t v___x_2463_; 
v___x_2462_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__3));
lean_inc(v_x_2437_);
v___x_2463_ = l_Lean_Syntax_isOfKind(v_x_2437_, v___x_2462_);
if (v___x_2463_ == 0)
{
lean_object* v___x_2464_; 
lean_dec(v_x_2437_);
v___x_2464_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg();
return v___x_2464_;
}
else
{
lean_object* v___x_2465_; lean_object* v_n_2467_; lean_object* v___y_2468_; lean_object* v___y_2469_; lean_object* v___y_2470_; lean_object* v___y_2471_; lean_object* v___y_2472_; lean_object* v___y_2473_; lean_object* v___y_2474_; lean_object* v___y_2475_; lean_object* v___x_2492_; uint8_t v___x_2493_; 
v___x_2465_ = lean_unsigned_to_nat(1u);
v___x_2492_ = l_Lean_Syntax_getArg(v_x_2437_, v___x_2465_);
lean_dec(v_x_2437_);
lean_inc(v___x_2492_);
v___x_2493_ = l_Lean_Syntax_matchesNull(v___x_2492_, v___x_2465_);
if (v___x_2493_ == 0)
{
lean_object* v___x_2494_; 
lean_dec(v___x_2492_);
v___x_2494_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg();
return v___x_2494_;
}
else
{
lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; uint8_t v___x_2498_; 
v___x_2495_ = lean_unsigned_to_nat(0u);
v___x_2496_ = l_Lean_Syntax_getArg(v___x_2492_, v___x_2495_);
lean_dec(v___x_2492_);
v___x_2497_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__5));
lean_inc(v___x_2496_);
v___x_2498_ = l_Lean_Syntax_isOfKind(v___x_2496_, v___x_2497_);
if (v___x_2498_ == 0)
{
lean_object* v___x_2499_; uint8_t v___x_2500_; 
v___x_2499_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__7));
lean_inc(v___x_2496_);
v___x_2500_ = l_Lean_Syntax_isOfKind(v___x_2496_, v___x_2499_);
if (v___x_2500_ == 0)
{
lean_object* v___x_2501_; 
lean_dec(v___x_2496_);
v___x_2501_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg();
return v___x_2501_;
}
else
{
lean_object* v___x_2502_; uint8_t v___x_2503_; 
v___x_2502_ = l_Lean_Syntax_getArg(v___x_2496_, v___x_2465_);
lean_dec(v___x_2496_);
v___x_2503_ = l_Lean_Syntax_isNone(v___x_2502_);
if (v___x_2503_ == 0)
{
uint8_t v___x_2504_; 
lean_inc(v___x_2502_);
v___x_2504_ = l_Lean_Syntax_matchesNull(v___x_2502_, v___x_2465_);
if (v___x_2504_ == 0)
{
lean_object* v___x_2505_; 
lean_dec(v___x_2502_);
v___x_2505_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg();
return v___x_2505_;
}
else
{
lean_object* v_n_2506_; lean_object* v___x_2507_; 
v_n_2506_ = l_Lean_Syntax_getArg(v___x_2502_, v___x_2495_);
lean_dec(v___x_2502_);
v___x_2507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2507_, 0, v_n_2506_);
v_n_2467_ = v___x_2507_;
v___y_2468_ = v_a_2438_;
v___y_2469_ = v_a_2439_;
v___y_2470_ = v_a_2440_;
v___y_2471_ = v_a_2441_;
v___y_2472_ = v_a_2442_;
v___y_2473_ = v_a_2443_;
v___y_2474_ = v_a_2444_;
v___y_2475_ = v_a_2445_;
goto v___jp_2466_;
}
}
else
{
lean_object* v___x_2508_; 
lean_dec(v___x_2502_);
v___x_2508_ = lean_box(0);
v_n_2467_ = v___x_2508_;
v___y_2468_ = v_a_2438_;
v___y_2469_ = v_a_2439_;
v___y_2470_ = v_a_2440_;
v___y_2471_ = v_a_2441_;
v___y_2472_ = v_a_2442_;
v___y_2473_ = v_a_2443_;
v___y_2474_ = v_a_2444_;
v___y_2475_ = v_a_2445_;
goto v___jp_2466_;
}
}
}
else
{
lean_object* v_h_2509_; lean_object* v___x_2510_; uint8_t v___x_2511_; 
v_h_2509_ = l_Lean_Syntax_getArg(v___x_2496_, v___x_2495_);
lean_dec(v___x_2496_);
v___x_2510_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__9));
lean_inc(v_h_2509_);
v___x_2511_ = l_Lean_Syntax_isOfKind(v_h_2509_, v___x_2510_);
if (v___x_2511_ == 0)
{
lean_object* v___x_2512_; 
lean_dec(v_h_2509_);
v___x_2512_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg();
return v___x_2512_;
}
else
{
lean_object* v___x_2513_; 
v___x_2513_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_2439_, v_a_2442_, v_a_2443_, v_a_2444_, v_a_2445_);
if (lean_obj_tag(v___x_2513_) == 0)
{
lean_object* v_a_2514_; lean_object* v___x_2515_; 
v_a_2514_ = lean_ctor_get(v___x_2513_, 0);
lean_inc(v_a_2514_);
lean_dec_ref(v___x_2513_);
lean_inc(v_a_2514_);
v___x_2515_ = l_Lean_MVarId_getType(v_a_2514_, v_a_2442_, v_a_2443_, v_a_2444_, v_a_2445_);
if (lean_obj_tag(v___x_2515_) == 0)
{
lean_object* v_a_2516_; lean_object* v___x_2517_; 
v_a_2516_ = lean_ctor_get(v___x_2515_, 0);
lean_inc(v_a_2516_);
lean_dec_ref(v___x_2515_);
v___x_2517_ = l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f(v_a_2516_);
lean_dec(v_a_2516_);
if (lean_obj_tag(v___x_2517_) == 1)
{
lean_object* v_val_2518_; lean_object* v___x_2519_; lean_object* v___f_2520_; lean_object* v___x_2521_; 
v_val_2518_ = lean_ctor_get(v___x_2517_, 0);
lean_inc(v_val_2518_);
lean_dec_ref(v___x_2517_);
v___x_2519_ = lean_box(0);
lean_inc(v_a_2514_);
v___f_2520_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__3___boxed), 13, 4);
lean_closure_set(v___f_2520_, 0, v___x_2519_);
lean_closure_set(v___f_2520_, 1, v_val_2518_);
lean_closure_set(v___f_2520_, 2, v_h_2509_);
lean_closure_set(v___f_2520_, 3, v_a_2514_);
v___x_2521_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___redArg(v_a_2514_, v___f_2520_, v_a_2438_, v_a_2439_, v_a_2440_, v_a_2441_, v_a_2442_, v_a_2443_, v_a_2444_, v_a_2445_);
return v___x_2521_;
}
else
{
lean_object* v___x_2522_; lean_object* v___x_2523_; 
lean_dec(v___x_2517_);
lean_dec(v_a_2514_);
lean_dec(v_h_2509_);
v___x_2522_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__11, &l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__11_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__11);
v___x_2523_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5___redArg(v___x_2522_, v_a_2442_, v_a_2443_, v_a_2444_, v_a_2445_);
return v___x_2523_;
}
}
else
{
lean_object* v_a_2524_; lean_object* v___x_2526_; uint8_t v_isShared_2527_; uint8_t v_isSharedCheck_2531_; 
lean_dec(v_a_2514_);
lean_dec(v_h_2509_);
v_a_2524_ = lean_ctor_get(v___x_2515_, 0);
v_isSharedCheck_2531_ = !lean_is_exclusive(v___x_2515_);
if (v_isSharedCheck_2531_ == 0)
{
v___x_2526_ = v___x_2515_;
v_isShared_2527_ = v_isSharedCheck_2531_;
goto v_resetjp_2525_;
}
else
{
lean_inc(v_a_2524_);
lean_dec(v___x_2515_);
v___x_2526_ = lean_box(0);
v_isShared_2527_ = v_isSharedCheck_2531_;
goto v_resetjp_2525_;
}
v_resetjp_2525_:
{
lean_object* v___x_2529_; 
if (v_isShared_2527_ == 0)
{
v___x_2529_ = v___x_2526_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v_a_2524_);
v___x_2529_ = v_reuseFailAlloc_2530_;
goto v_reusejp_2528_;
}
v_reusejp_2528_:
{
return v___x_2529_;
}
}
}
}
else
{
lean_object* v_a_2532_; lean_object* v___x_2534_; uint8_t v_isShared_2535_; uint8_t v_isSharedCheck_2539_; 
lean_dec(v_h_2509_);
v_a_2532_ = lean_ctor_get(v___x_2513_, 0);
v_isSharedCheck_2539_ = !lean_is_exclusive(v___x_2513_);
if (v_isSharedCheck_2539_ == 0)
{
v___x_2534_ = v___x_2513_;
v_isShared_2535_ = v_isSharedCheck_2539_;
goto v_resetjp_2533_;
}
else
{
lean_inc(v_a_2532_);
lean_dec(v___x_2513_);
v___x_2534_ = lean_box(0);
v_isShared_2535_ = v_isSharedCheck_2539_;
goto v_resetjp_2533_;
}
v_resetjp_2533_:
{
lean_object* v___x_2537_; 
if (v_isShared_2535_ == 0)
{
v___x_2537_ = v___x_2534_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2538_; 
v_reuseFailAlloc_2538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2538_, 0, v_a_2532_);
v___x_2537_ = v_reuseFailAlloc_2538_;
goto v_reusejp_2536_;
}
v_reusejp_2536_:
{
return v___x_2537_;
}
}
}
}
}
}
v___jp_2466_:
{
lean_object* v___x_2476_; 
v___x_2476_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg(v___y_2469_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_);
if (lean_obj_tag(v___x_2476_) == 0)
{
lean_object* v_a_2477_; 
v_a_2477_ = lean_ctor_get(v___x_2476_, 0);
lean_inc(v_a_2477_);
lean_dec_ref(v___x_2476_);
if (lean_obj_tag(v_n_2467_) == 0)
{
lean_object* v_fst_2478_; lean_object* v_snd_2479_; 
v_fst_2478_ = lean_ctor_get(v_a_2477_, 0);
lean_inc(v_fst_2478_);
v_snd_2479_ = lean_ctor_get(v_a_2477_, 1);
lean_inc(v_snd_2479_);
lean_dec(v_a_2477_);
v___y_2448_ = v_fst_2478_;
v___y_2449_ = v_snd_2479_;
v___y_2450_ = v___y_2471_;
v___y_2451_ = v___y_2474_;
v___y_2452_ = v___y_2470_;
v___y_2453_ = v___y_2473_;
v___y_2454_ = v___y_2468_;
v___y_2455_ = v___y_2472_;
v___y_2456_ = v___y_2475_;
v___y_2457_ = v___y_2469_;
v___y_2458_ = v___x_2465_;
goto v___jp_2447_;
}
else
{
lean_object* v_fst_2480_; lean_object* v_snd_2481_; lean_object* v_val_2482_; lean_object* v___x_2483_; 
v_fst_2480_ = lean_ctor_get(v_a_2477_, 0);
lean_inc(v_fst_2480_);
v_snd_2481_ = lean_ctor_get(v_a_2477_, 1);
lean_inc(v_snd_2481_);
lean_dec(v_a_2477_);
v_val_2482_ = lean_ctor_get(v_n_2467_, 0);
lean_inc(v_val_2482_);
lean_dec_ref(v_n_2467_);
v___x_2483_ = l_Lean_TSyntax_getNat(v_val_2482_);
lean_dec(v_val_2482_);
v___y_2448_ = v_fst_2480_;
v___y_2449_ = v_snd_2481_;
v___y_2450_ = v___y_2471_;
v___y_2451_ = v___y_2474_;
v___y_2452_ = v___y_2470_;
v___y_2453_ = v___y_2473_;
v___y_2454_ = v___y_2468_;
v___y_2455_ = v___y_2472_;
v___y_2456_ = v___y_2475_;
v___y_2457_ = v___y_2469_;
v___y_2458_ = v___x_2483_;
goto v___jp_2447_;
}
}
else
{
lean_object* v_a_2484_; lean_object* v___x_2486_; uint8_t v_isShared_2487_; uint8_t v_isSharedCheck_2491_; 
lean_dec(v_n_2467_);
v_a_2484_ = lean_ctor_get(v___x_2476_, 0);
v_isSharedCheck_2491_ = !lean_is_exclusive(v___x_2476_);
if (v_isSharedCheck_2491_ == 0)
{
v___x_2486_ = v___x_2476_;
v_isShared_2487_ = v_isSharedCheck_2491_;
goto v_resetjp_2485_;
}
else
{
lean_inc(v_a_2484_);
lean_dec(v___x_2476_);
v___x_2486_ = lean_box(0);
v_isShared_2487_ = v_isSharedCheck_2491_;
goto v_resetjp_2485_;
}
v_resetjp_2485_:
{
lean_object* v___x_2489_; 
if (v_isShared_2487_ == 0)
{
v___x_2489_ = v___x_2486_;
goto v_reusejp_2488_;
}
else
{
lean_object* v_reuseFailAlloc_2490_; 
v_reuseFailAlloc_2490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2490_, 0, v_a_2484_);
v___x_2489_ = v_reuseFailAlloc_2490_;
goto v_reusejp_2488_;
}
v_reusejp_2488_:
{
return v___x_2489_;
}
}
}
}
}
v___jp_2447_:
{
lean_object* v___x_2459_; lean_object* v___f_2460_; lean_object* v___x_2461_; 
v___x_2459_ = lean_box(0);
lean_inc(v___y_2448_);
v___f_2460_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__1___boxed), 13, 4);
lean_closure_set(v___f_2460_, 0, v___x_2459_);
lean_closure_set(v___f_2460_, 1, v___y_2449_);
lean_closure_set(v___f_2460_, 2, v___y_2458_);
lean_closure_set(v___f_2460_, 3, v___y_2448_);
v___x_2461_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___redArg(v___y_2448_, v___f_2460_, v___y_2454_, v___y_2457_, v___y_2452_, v___y_2450_, v___y_2455_, v___y_2453_, v___y_2451_, v___y_2456_);
return v___x_2461_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___boxed(lean_object* v_x_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_){
_start:
{
lean_object* v_res_2550_; 
v_res_2550_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert(v_x_2540_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_);
lean_dec(v_a_2548_);
lean_dec_ref(v_a_2547_);
lean_dec(v_a_2546_);
lean_dec_ref(v_a_2545_);
lean_dec(v_a_2544_);
lean_dec_ref(v_a_2543_);
lean_dec(v_a_2542_);
lean_dec_ref(v_a_2541_);
return v_res_2550_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2(lean_object* v_mvarId_2551_, lean_object* v_val_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_){
_start:
{
lean_object* v___x_2562_; 
v___x_2562_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2___redArg(v_mvarId_2551_, v_val_2552_, v___y_2558_);
return v___x_2562_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2___boxed(lean_object* v_mvarId_2563_, lean_object* v_val_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_){
_start:
{
lean_object* v_res_2574_; 
v_res_2574_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2(v_mvarId_2563_, v_val_2564_, v___y_2565_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_);
lean_dec(v___y_2572_);
lean_dec_ref(v___y_2571_);
lean_dec(v___y_2570_);
lean_dec_ref(v___y_2569_);
lean_dec(v___y_2568_);
lean_dec_ref(v___y_2567_);
lean_dec(v___y_2566_);
lean_dec_ref(v___y_2565_);
return v_res_2574_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5(lean_object* v_00_u03b1_2575_, lean_object* v_msg_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_){
_start:
{
lean_object* v___x_2586_; 
v___x_2586_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5___redArg(v_msg_2576_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_);
return v___x_2586_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5___boxed(lean_object* v_00_u03b1_2587_, lean_object* v_msg_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_){
_start:
{
lean_object* v_res_2598_; 
v_res_2598_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5(v_00_u03b1_2587_, v_msg_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_);
lean_dec(v___y_2596_);
lean_dec_ref(v___y_2595_);
lean_dec(v___y_2594_);
lean_dec_ref(v___y_2593_);
lean_dec(v___y_2592_);
lean_dec_ref(v___y_2591_);
lean_dec(v___y_2590_);
lean_dec_ref(v___y_2589_);
return v_res_2598_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__1(lean_object* v_inst_2599_, lean_object* v_R_2600_, lean_object* v_a_2601_, lean_object* v_b_2602_){
_start:
{
lean_object* v___x_2603_; 
v___x_2603_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__1___redArg(v_a_2601_, v_b_2602_);
return v___x_2603_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__2(size_t v_sz_2604_, size_t v_i_2605_, lean_object* v_bs_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_){
_start:
{
lean_object* v___x_2616_; 
v___x_2616_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__2___redArg(v_sz_2604_, v_i_2605_, v_bs_2606_, v___y_2611_, v___y_2612_, v___y_2613_, v___y_2614_);
return v___x_2616_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__2___boxed(lean_object* v_sz_2617_, lean_object* v_i_2618_, lean_object* v_bs_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_){
_start:
{
size_t v_sz_boxed_2629_; size_t v_i_boxed_2630_; lean_object* v_res_2631_; 
v_sz_boxed_2629_ = lean_unbox_usize(v_sz_2617_);
lean_dec(v_sz_2617_);
v_i_boxed_2630_ = lean_unbox_usize(v_i_2618_);
lean_dec(v_i_2618_);
v_res_2631_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__2(v_sz_boxed_2629_, v_i_boxed_2630_, v_bs_2619_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_);
lean_dec(v___y_2627_);
lean_dec_ref(v___y_2626_);
lean_dec(v___y_2625_);
lean_dec_ref(v___y_2624_);
lean_dec(v___y_2623_);
lean_dec_ref(v___y_2622_);
lean_dec(v___y_2621_);
lean_dec_ref(v___y_2620_);
return v_res_2631_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__4(lean_object* v_as_2632_, lean_object* v_i_2633_, lean_object* v_j_2634_, lean_object* v_inv_2635_, lean_object* v_bs_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_){
_start:
{
lean_object* v___x_2646_; 
v___x_2646_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__4___redArg(v_as_2632_, v_i_2633_, v_j_2634_, v_bs_2636_, v___y_2643_, v___y_2644_);
return v___x_2646_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__4___boxed(lean_object* v_as_2647_, lean_object* v_i_2648_, lean_object* v_j_2649_, lean_object* v_inv_2650_, lean_object* v_bs_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_){
_start:
{
lean_object* v_res_2661_; 
v_res_2661_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__4(v_as_2647_, v_i_2648_, v_j_2649_, v_inv_2650_, v_bs_2651_, v___y_2652_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_);
lean_dec(v___y_2659_);
lean_dec_ref(v___y_2658_);
lean_dec(v___y_2657_);
lean_dec_ref(v___y_2656_);
lean_dec(v___y_2655_);
lean_dec_ref(v___y_2654_);
lean_dec(v___y_2653_);
lean_dec_ref(v___y_2652_);
lean_dec_ref(v_as_2647_);
return v_res_2661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5(lean_object* v_00_u03b1_2662_, lean_object* v_inst_2663_, lean_object* v_declInfos_2664_, lean_object* v_k_2665_, uint8_t v_kind_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_){
_start:
{
lean_object* v___x_2676_; 
v___x_2676_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5___redArg(v_inst_2663_, v_declInfos_2664_, v_k_2665_, v_kind_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_, v___y_2673_, v___y_2674_);
return v___x_2676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5___boxed(lean_object* v_00_u03b1_2677_, lean_object* v_inst_2678_, lean_object* v_declInfos_2679_, lean_object* v_k_2680_, lean_object* v_kind_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_){
_start:
{
uint8_t v_kind_boxed_2691_; lean_object* v_res_2692_; 
v_kind_boxed_2691_ = lean_unbox(v_kind_2681_);
v_res_2692_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5(v_00_u03b1_2677_, v_inst_2678_, v_declInfos_2679_, v_k_2680_, v_kind_boxed_2691_, v___y_2682_, v___y_2683_, v___y_2684_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_);
lean_dec(v___y_2689_);
lean_dec_ref(v___y_2688_);
lean_dec(v___y_2687_);
lean_dec_ref(v___y_2686_);
lean_dec(v___y_2685_);
lean_dec_ref(v___y_2684_);
lean_dec(v___y_2683_);
lean_dec_ref(v___y_2682_);
lean_dec(v_inst_2678_);
return v_res_2692_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__8(lean_object* v_00_u03b1_2693_, lean_object* v_msg_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_){
_start:
{
lean_object* v___x_2700_; 
v___x_2700_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__8___redArg(v_msg_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_);
return v___x_2700_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__8___boxed(lean_object* v_00_u03b1_2701_, lean_object* v_msg_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_){
_start:
{
lean_object* v_res_2708_; 
v_res_2708_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__8(v_00_u03b1_2701_, v_msg_2702_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_);
lean_dec(v___y_2706_);
lean_dec_ref(v___y_2705_);
lean_dec(v___y_2704_);
lean_dec_ref(v___y_2703_);
return v_res_2708_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10(lean_object* v_00_u03b2_2709_, lean_object* v_x_2710_, lean_object* v_x_2711_, lean_object* v_x_2712_){
_start:
{
lean_object* v___x_2713_; 
v___x_2713_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10___redArg(v_x_2710_, v_x_2711_, v_x_2712_);
return v___x_2713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9(lean_object* v_00_u03b1_2714_, lean_object* v_inst_2715_, lean_object* v_declInfos_2716_, lean_object* v_k_2717_, uint8_t v_kind_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_){
_start:
{
lean_object* v___x_2728_; 
v___x_2728_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9___redArg(v_inst_2715_, v_declInfos_2716_, v_k_2717_, v_kind_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_, v___y_2726_);
return v___x_2728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9___boxed(lean_object* v_00_u03b1_2729_, lean_object* v_inst_2730_, lean_object* v_declInfos_2731_, lean_object* v_k_2732_, lean_object* v_kind_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_){
_start:
{
uint8_t v_kind_boxed_2743_; lean_object* v_res_2744_; 
v_kind_boxed_2743_ = lean_unbox(v_kind_2733_);
v_res_2744_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9(v_00_u03b1_2729_, v_inst_2730_, v_declInfos_2731_, v_k_2732_, v_kind_boxed_2743_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_);
lean_dec(v___y_2741_);
lean_dec_ref(v___y_2740_);
lean_dec(v___y_2739_);
lean_dec_ref(v___y_2738_);
lean_dec(v___y_2737_);
lean_dec_ref(v___y_2736_);
lean_dec(v___y_2735_);
lean_dec_ref(v___y_2734_);
lean_dec(v_inst_2730_);
return v_res_2744_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15(lean_object* v_00_u03b2_2745_, lean_object* v_x_2746_, size_t v_x_2747_, size_t v_x_2748_, lean_object* v_x_2749_, lean_object* v_x_2750_){
_start:
{
lean_object* v___x_2751_; 
v___x_2751_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15___redArg(v_x_2746_, v_x_2747_, v_x_2748_, v_x_2749_, v_x_2750_);
return v___x_2751_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15___boxed(lean_object* v_00_u03b2_2752_, lean_object* v_x_2753_, lean_object* v_x_2754_, lean_object* v_x_2755_, lean_object* v_x_2756_, lean_object* v_x_2757_){
_start:
{
size_t v_x_22727__boxed_2758_; size_t v_x_22728__boxed_2759_; lean_object* v_res_2760_; 
v_x_22727__boxed_2758_ = lean_unbox_usize(v_x_2754_);
lean_dec(v_x_2754_);
v_x_22728__boxed_2759_ = lean_unbox_usize(v_x_2755_);
lean_dec(v_x_2755_);
v_res_2760_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15(v_00_u03b2_2752_, v_x_2753_, v_x_22727__boxed_2758_, v_x_22728__boxed_2759_, v_x_2756_, v_x_2757_);
return v_res_2760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14(lean_object* v_00_u03b1_2761_, lean_object* v_inst_2762_, lean_object* v_declInfos_2763_, lean_object* v_k_2764_, uint8_t v_kind_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_){
_start:
{
lean_object* v___x_2775_; 
v___x_2775_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14___redArg(v_inst_2762_, v_declInfos_2763_, v_k_2764_, v_kind_2765_, v___y_2766_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_);
return v___x_2775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14___boxed(lean_object* v_00_u03b1_2776_, lean_object* v_inst_2777_, lean_object* v_declInfos_2778_, lean_object* v_k_2779_, lean_object* v_kind_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_){
_start:
{
uint8_t v_kind_boxed_2790_; lean_object* v_res_2791_; 
v_kind_boxed_2790_ = lean_unbox(v_kind_2780_);
v_res_2791_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14(v_00_u03b1_2776_, v_inst_2777_, v_declInfos_2778_, v_k_2779_, v_kind_boxed_2790_, v___y_2781_, v___y_2782_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_);
lean_dec(v___y_2788_);
lean_dec_ref(v___y_2787_);
lean_dec(v___y_2786_);
lean_dec_ref(v___y_2785_);
lean_dec(v___y_2784_);
lean_dec_ref(v___y_2783_);
lean_dec(v___y_2782_);
lean_dec_ref(v___y_2781_);
lean_dec(v_inst_2777_);
return v_res_2791_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15_spec__20(lean_object* v_00_u03b2_2792_, lean_object* v_n_2793_, lean_object* v_k_2794_, lean_object* v_v_2795_){
_start:
{
lean_object* v___x_2796_; 
v___x_2796_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15_spec__20___redArg(v_n_2793_, v_k_2794_, v_v_2795_);
return v___x_2796_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15_spec__21(lean_object* v_00_u03b2_2797_, size_t v_depth_2798_, lean_object* v_keys_2799_, lean_object* v_vals_2800_, lean_object* v_heq_2801_, lean_object* v_i_2802_, lean_object* v_entries_2803_){
_start:
{
lean_object* v___x_2804_; 
v___x_2804_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15_spec__21___redArg(v_depth_2798_, v_keys_2799_, v_vals_2800_, v_i_2802_, v_entries_2803_);
return v___x_2804_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15_spec__21___boxed(lean_object* v_00_u03b2_2805_, lean_object* v_depth_2806_, lean_object* v_keys_2807_, lean_object* v_vals_2808_, lean_object* v_heq_2809_, lean_object* v_i_2810_, lean_object* v_entries_2811_){
_start:
{
size_t v_depth_boxed_2812_; lean_object* v_res_2813_; 
v_depth_boxed_2812_ = lean_unbox_usize(v_depth_2806_);
lean_dec(v_depth_2806_);
v_res_2813_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15_spec__21(v_00_u03b2_2805_, v_depth_boxed_2812_, v_keys_2807_, v_vals_2808_, v_heq_2809_, v_i_2810_, v_entries_2811_);
lean_dec_ref(v_vals_2808_);
lean_dec_ref(v_keys_2807_);
return v_res_2813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19_spec__21(lean_object* v_00_u03b1_2814_, lean_object* v_name_2815_, uint8_t v_bi_2816_, lean_object* v_type_2817_, lean_object* v_k_2818_, uint8_t v_kind_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_){
_start:
{
lean_object* v___x_2829_; 
v___x_2829_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19_spec__21___redArg(v_name_2815_, v_bi_2816_, v_type_2817_, v_k_2818_, v_kind_2819_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_);
return v___x_2829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19_spec__21___boxed(lean_object* v_00_u03b1_2830_, lean_object* v_name_2831_, lean_object* v_bi_2832_, lean_object* v_type_2833_, lean_object* v_k_2834_, lean_object* v_kind_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_){
_start:
{
uint8_t v_bi_boxed_2845_; uint8_t v_kind_boxed_2846_; lean_object* v_res_2847_; 
v_bi_boxed_2845_ = lean_unbox(v_bi_2832_);
v_kind_boxed_2846_ = lean_unbox(v_kind_2835_);
v_res_2847_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19_spec__21(v_00_u03b1_2830_, v_name_2831_, v_bi_boxed_2845_, v_type_2833_, v_k_2834_, v_kind_boxed_2846_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_);
lean_dec(v___y_2843_);
lean_dec_ref(v___y_2842_);
lean_dec(v___y_2841_);
lean_dec_ref(v___y_2840_);
lean_dec(v___y_2839_);
lean_dec_ref(v___y_2838_);
lean_dec(v___y_2837_);
lean_dec_ref(v___y_2836_);
return v_res_2847_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19(lean_object* v_00_u03b1_2848_, lean_object* v_declInfos_2849_, lean_object* v_k_2850_, uint8_t v_kind_2851_, lean_object* v_inst_2852_, lean_object* v_acc_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_){
_start:
{
lean_object* v___x_2863_; 
v___x_2863_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___redArg(v_declInfos_2849_, v_k_2850_, v_kind_2851_, v_acc_2853_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_);
return v___x_2863_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___boxed(lean_object* v_00_u03b1_2864_, lean_object* v_declInfos_2865_, lean_object* v_k_2866_, lean_object* v_kind_2867_, lean_object* v_inst_2868_, lean_object* v_acc_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_){
_start:
{
uint8_t v_kind_boxed_2879_; lean_object* v_res_2880_; 
v_kind_boxed_2879_ = lean_unbox(v_kind_2867_);
v_res_2880_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19(v_00_u03b1_2864_, v_declInfos_2865_, v_k_2866_, v_kind_boxed_2879_, v_inst_2868_, v_acc_2869_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_);
lean_dec(v___y_2877_);
lean_dec_ref(v___y_2876_);
lean_dec(v___y_2875_);
lean_dec_ref(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec_ref(v___y_2872_);
lean_dec(v___y_2871_);
lean_dec_ref(v___y_2870_);
lean_dec(v_inst_2868_);
return v_res_2880_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15_spec__20_spec__22(lean_object* v_00_u03b2_2881_, lean_object* v_x_2882_, lean_object* v_x_2883_, lean_object* v_x_2884_, lean_object* v_x_2885_){
_start:
{
lean_object* v___x_2886_; 
v___x_2886_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15_spec__20_spec__22___redArg(v_x_2882_, v_x_2883_, v_x_2884_, v_x_2885_);
return v___x_2886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1(){
_start:
{
lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; 
v___x_2898_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2899_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__3));
v___x_2900_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__3));
v___x_2901_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___boxed), 10, 0);
v___x_2902_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2898_, v___x_2899_, v___x_2900_, v___x_2901_);
return v___x_2902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___boxed(lean_object* v_a_2903_){
_start:
{
lean_object* v_res_2904_; 
v_res_2904_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1();
return v_res_2904_;
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
