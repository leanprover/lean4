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
lean_object* l_Lean_Elab_Term_instMonadTermElabM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Elab_Term_instMonadTermElabM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_instMonadTacticM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_instMonadTacticM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_Pi_instInhabited___redArg___lam__0(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19_spec__21___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19_spec__21___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19_spec__21___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19_spec__21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_instMonadTermElabM___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___closed__0 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___closed__0_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_instMonadTermElabM___lam__1___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___closed__1 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___closed__1_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_instMonadTacticM___lam__0___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___closed__2 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___closed__2_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_instMonadTacticM___lam__1___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___closed__3 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__13(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__13___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15_spec__20(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15_spec__21(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19_spec__21(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_inc_ref_n(v_focusHyp_44_, 2);
v_restHyps_45_ = lean_ctor_get(v_res_36_, 1);
lean_inc_ref_n(v_restHyps_45_, 2);
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
lean_inc_ref_n(v_00_u03c3s_38_, 2);
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
lean_inc_n(v_toBind_68_, 2);
lean_dec_ref(v_inst_62_);
v_toPure_69_ = lean_ctor_get(v_toApplicative_67_, 1);
lean_inc(v_toPure_69_);
lean_dec_ref(v_toApplicative_67_);
lean_inc_ref(v_goal_64_);
v___x_70_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___boxed), 7, 2);
lean_closure_set(v___x_70_, 0, v_goal_64_);
lean_closure_set(v___x_70_, 1, v_ref_65_);
v___x_71_ = lean_apply_2(v_inst_63_, lean_box(0), v___x_70_);
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
lean_inc_ref_n(v___y_368_, 2);
v_H_384_ = l_Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps(v___y_368_, v_H_383_);
lean_inc_n(v_u_369_, 2);
v___x_385_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd(v_u_369_, v___y_368_, v_H_384_, v_snd_370_);
v_fst_386_ = lean_ctor_get(v___x_385_, 0);
lean_inc_n(v_fst_386_, 2);
v_snd_387_ = lean_ctor_get(v___x_385_, 1);
lean_inc(v_snd_387_);
lean_dec_ref(v___x_385_);
lean_inc(v_toBind_378_);
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
lean_inc_n(v_toBind_480_, 2);
lean_inc_n(v_inst_479_, 2);
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
lean_inc_n(v_toBind_534_, 2);
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
lean_object* v_toApplicative_601_; lean_object* v_toBind_602_; lean_object* v___x_603_; lean_object* v_toApplicative_604_; lean_object* v_toFunctor_605_; lean_object* v_toSeq_606_; lean_object* v_toSeqLeft_607_; lean_object* v_toSeqRight_608_; lean_object* v___f_609_; lean_object* v___f_610_; lean_object* v___f_611_; lean_object* v___f_612_; lean_object* v___x_613_; lean_object* v___f_614_; lean_object* v___f_615_; lean_object* v___f_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v_toApplicative_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_657_; 
v_toApplicative_601_ = lean_ctor_get(v_inst_582_, 0);
lean_inc_ref(v_toApplicative_601_);
v_toBind_602_ = lean_ctor_get(v_inst_582_, 1);
lean_inc(v_toBind_602_);
v___x_603_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__1);
v_toApplicative_604_ = lean_ctor_get(v___x_603_, 0);
v_toFunctor_605_ = lean_ctor_get(v_toApplicative_604_, 0);
v_toSeq_606_ = lean_ctor_get(v_toApplicative_604_, 2);
v_toSeqLeft_607_ = lean_ctor_get(v_toApplicative_604_, 3);
v_toSeqRight_608_ = lean_ctor_get(v_toApplicative_604_, 4);
v___f_609_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__2));
v___f_610_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__3));
lean_inc_ref_n(v_toFunctor_605_, 2);
v___f_611_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_611_, 0, v_toFunctor_605_);
v___f_612_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_612_, 0, v_toFunctor_605_);
v___x_613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_613_, 0, v___f_611_);
lean_ctor_set(v___x_613_, 1, v___f_612_);
lean_inc(v_toSeqRight_608_);
v___f_614_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_614_, 0, v_toSeqRight_608_);
lean_inc(v_toSeqLeft_607_);
v___f_615_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_615_, 0, v_toSeqLeft_607_);
lean_inc(v_toSeq_606_);
v___f_616_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_616_, 0, v_toSeq_606_);
v___x_617_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_617_, 0, v___x_613_);
lean_ctor_set(v___x_617_, 1, v___f_609_);
lean_ctor_set(v___x_617_, 2, v___f_616_);
lean_ctor_set(v___x_617_, 3, v___f_615_);
lean_ctor_set(v___x_617_, 4, v___f_614_);
v___x_618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_618_, 0, v___x_617_);
lean_ctor_set(v___x_618_, 1, v___f_610_);
v___x_619_ = l_StateRefT_x27_instMonad___redArg(v___x_618_);
v_toApplicative_620_ = lean_ctor_get(v___x_619_, 0);
v_isSharedCheck_657_ = !lean_is_exclusive(v___x_619_);
if (v_isSharedCheck_657_ == 0)
{
lean_object* v_unused_658_; 
v_unused_658_ = lean_ctor_get(v___x_619_, 1);
lean_dec(v_unused_658_);
v___x_622_ = v___x_619_;
v_isShared_623_ = v_isSharedCheck_657_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_toApplicative_620_);
lean_dec(v___x_619_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_657_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v_toFunctor_624_; lean_object* v_toSeq_625_; lean_object* v_toSeqLeft_626_; lean_object* v_toSeqRight_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_655_; 
v_toFunctor_624_ = lean_ctor_get(v_toApplicative_620_, 0);
v_toSeq_625_ = lean_ctor_get(v_toApplicative_620_, 2);
v_toSeqLeft_626_ = lean_ctor_get(v_toApplicative_620_, 3);
v_toSeqRight_627_ = lean_ctor_get(v_toApplicative_620_, 4);
v_isSharedCheck_655_ = !lean_is_exclusive(v_toApplicative_620_);
if (v_isSharedCheck_655_ == 0)
{
lean_object* v_unused_656_; 
v_unused_656_ = lean_ctor_get(v_toApplicative_620_, 1);
lean_dec(v_unused_656_);
v___x_629_ = v_toApplicative_620_;
v_isShared_630_ = v_isSharedCheck_655_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_toSeqRight_627_);
lean_inc(v_toSeqLeft_626_);
lean_inc(v_toSeq_625_);
lean_inc(v_toFunctor_624_);
lean_dec(v_toApplicative_620_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_655_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v___f_631_; lean_object* v___x_632_; lean_object* v___f_633_; lean_object* v___f_634_; lean_object* v___f_635_; lean_object* v___f_636_; lean_object* v___f_637_; lean_object* v___x_638_; lean_object* v___f_639_; lean_object* v___f_640_; lean_object* v___f_641_; lean_object* v___x_643_; 
lean_inc_n(v_toBind_602_, 2);
lean_inc_n(v_inst_583_, 2);
lean_inc_ref_n(v_toApplicative_601_, 2);
v___f_631_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__6), 6, 3);
lean_closure_set(v___f_631_, 0, v_toApplicative_601_);
lean_closure_set(v___f_631_, 1, v_inst_583_);
lean_closure_set(v___f_631_, 2, v_toBind_602_);
v___x_632_ = lean_box(v___x_588_);
lean_inc_ref(v_inst_582_);
lean_inc_ref(v_revertArgs_590_);
lean_inc_ref(v_hyps_587_);
lean_inc_ref(v_00_u03c3s_585_);
lean_inc(v_u_584_);
v___f_633_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__11___boxed), 13, 12);
lean_closure_set(v___f_633_, 0, v_u_584_);
lean_closure_set(v___f_633_, 1, v_00_u03c3s_585_);
lean_closure_set(v___f_633_, 2, v_hypName_586_);
lean_closure_set(v___f_633_, 3, v_toApplicative_601_);
lean_closure_set(v___f_633_, 4, v_hyps_587_);
lean_closure_set(v___f_633_, 5, v___x_632_);
lean_closure_set(v___f_633_, 6, v_inst_583_);
lean_closure_set(v___f_633_, 7, v_toBind_602_);
lean_closure_set(v___f_633_, 8, v___f_589_);
lean_closure_set(v___f_633_, 9, v_revertArgs_590_);
lean_closure_set(v___f_633_, 10, v_inst_582_);
lean_closure_set(v___f_633_, 11, v___f_591_);
v___f_634_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__4));
v___f_635_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__5));
lean_inc_ref(v_toFunctor_624_);
v___f_636_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_636_, 0, v_toFunctor_624_);
v___f_637_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_637_, 0, v_toFunctor_624_);
v___x_638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_638_, 0, v___f_636_);
lean_ctor_set(v___x_638_, 1, v___f_637_);
v___f_639_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_639_, 0, v_toSeqRight_627_);
v___f_640_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_640_, 0, v_toSeqLeft_626_);
v___f_641_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_641_, 0, v_toSeq_625_);
if (v_isShared_630_ == 0)
{
lean_ctor_set(v___x_629_, 4, v___f_639_);
lean_ctor_set(v___x_629_, 3, v___f_640_);
lean_ctor_set(v___x_629_, 2, v___f_641_);
lean_ctor_set(v___x_629_, 1, v___f_634_);
lean_ctor_set(v___x_629_, 0, v___x_638_);
v___x_643_ = v___x_629_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v___x_638_);
lean_ctor_set(v_reuseFailAlloc_654_, 1, v___f_634_);
lean_ctor_set(v_reuseFailAlloc_654_, 2, v___f_641_);
lean_ctor_set(v_reuseFailAlloc_654_, 3, v___f_640_);
lean_ctor_set(v_reuseFailAlloc_654_, 4, v___f_639_);
v___x_643_ = v_reuseFailAlloc_654_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
lean_object* v___x_645_; 
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 1, v___f_635_);
lean_ctor_set(v___x_622_, 0, v___x_643_);
v___x_645_ = v___x_622_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v___x_643_);
lean_ctor_set(v_reuseFailAlloc_653_, 1, v___f_635_);
v___x_645_ = v_reuseFailAlloc_653_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
lean_object* v___f_646_; lean_object* v___x_647_; size_t v_sz_648_; size_t v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
lean_inc_ref(v___x_645_);
lean_inc(v_toBind_602_);
lean_inc(v_inst_583_);
lean_inc_ref(v_revertArgs_590_);
v___f_646_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__19___boxed), 20, 19);
lean_closure_set(v___f_646_, 0, v_u_584_);
lean_closure_set(v___f_646_, 1, v_toApplicative_601_);
lean_closure_set(v___f_646_, 2, v_revertArgs_590_);
lean_closure_set(v___f_646_, 3, v_00_u03c3s_585_);
lean_closure_set(v___f_646_, 4, v_hyps_587_);
lean_closure_set(v___f_646_, 5, v_target_592_);
lean_closure_set(v___f_646_, 6, v_inst_583_);
lean_closure_set(v___f_646_, 7, v_toBind_602_);
lean_closure_set(v___f_646_, 8, v_a_593_);
lean_closure_set(v___f_646_, 9, v_n_594_);
lean_closure_set(v___f_646_, 10, v_f_595_);
lean_closure_set(v___f_646_, 11, v_k_596_);
lean_closure_set(v___f_646_, 12, v___x_597_);
lean_closure_set(v___f_646_, 13, v___f_598_);
lean_closure_set(v___f_646_, 14, v___x_645_);
lean_closure_set(v___f_646_, 15, v_inst_599_);
lean_closure_set(v___f_646_, 16, v_inst_582_);
lean_closure_set(v___f_646_, 17, v___f_633_);
lean_closure_set(v___f_646_, 18, v___f_631_);
v___x_647_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__6));
v_sz_648_ = lean_array_size(v_revertArgs_590_);
v___x_649_ = ((size_t)0ULL);
v___x_650_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_645_, v___x_647_, v_sz_648_, v___x_649_, v_revertArgs_590_);
v___x_651_ = lean_apply_2(v_inst_583_, lean_box(0), v___x_650_);
v___x_652_ = lean_apply_4(v_toBind_602_, lean_box(0), lean_box(0), v___x_651_, v___f_646_);
return v___x_652_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___boxed(lean_object** _args){
lean_object* v_inst_659_ = _args[0];
lean_object* v_inst_660_ = _args[1];
lean_object* v_u_661_ = _args[2];
lean_object* v_00_u03c3s_662_ = _args[3];
lean_object* v_hypName_663_ = _args[4];
lean_object* v_hyps_664_ = _args[5];
lean_object* v___x_665_ = _args[6];
lean_object* v___f_666_ = _args[7];
lean_object* v_revertArgs_667_ = _args[8];
lean_object* v___f_668_ = _args[9];
lean_object* v_target_669_ = _args[10];
lean_object* v_a_670_ = _args[11];
lean_object* v_n_671_ = _args[12];
lean_object* v_f_672_ = _args[13];
lean_object* v_k_673_ = _args[14];
lean_object* v___x_674_ = _args[15];
lean_object* v___f_675_ = _args[16];
lean_object* v_inst_676_ = _args[17];
lean_object* v_____r_677_ = _args[18];
_start:
{
uint8_t v___x_1548__boxed_678_; lean_object* v_res_679_; 
v___x_1548__boxed_678_ = lean_unbox(v___x_665_);
v_res_679_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20(v_inst_659_, v_inst_660_, v_u_661_, v_00_u03c3s_662_, v_hypName_663_, v_hyps_664_, v___x_1548__boxed_678_, v___f_666_, v_revertArgs_667_, v___f_668_, v_target_669_, v_a_670_, v_n_671_, v_f_672_, v_k_673_, v___x_674_, v___f_675_, v_inst_676_, v_____r_677_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__21(lean_object* v___f_680_, lean_object* v_____r_681_){
_start:
{
lean_object* v___x_682_; 
v___x_682_ = lean_apply_1(v___f_680_, v_____r_681_);
return v___x_682_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__2(void){
_start:
{
lean_object* v___x_686_; lean_object* v___f_687_; 
v___x_686_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_687_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_687_, 0, v___x_686_);
return v___f_687_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__3(void){
_start:
{
lean_object* v___x_688_; lean_object* v___f_689_; 
v___x_688_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_689_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_689_, 0, v___x_688_);
return v___f_689_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__4(void){
_start:
{
lean_object* v___f_690_; lean_object* v___f_691_; lean_object* v___x_692_; 
v___f_690_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__3, &l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__3_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__3);
v___f_691_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__2, &l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__2);
v___x_692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_692_, 0, v___f_691_);
lean_ctor_set(v___x_692_, 1, v___f_690_);
return v___x_692_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__5(void){
_start:
{
lean_object* v___x_693_; lean_object* v___f_694_; 
v___x_693_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__4, &l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__4_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__4);
v___f_694_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_694_, 0, v___x_693_);
return v___f_694_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__6(void){
_start:
{
lean_object* v___x_695_; lean_object* v___f_696_; 
v___x_695_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__4, &l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__4_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__4);
v___f_696_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_696_, 0, v___x_695_);
return v___f_696_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__7(void){
_start:
{
lean_object* v___f_697_; lean_object* v___f_698_; lean_object* v___x_699_; 
v___f_697_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__6, &l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__6_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__6);
v___f_698_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__5, &l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__5_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__5);
v___x_699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_699_, 0, v___f_698_);
lean_ctor_set(v___x_699_, 1, v___f_697_);
return v___x_699_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__12(void){
_start:
{
lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_704_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_705_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__11));
v___x_706_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__10));
v___x_707_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_706_, v___x_705_, v___x_704_);
return v___x_707_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__13(void){
_start:
{
lean_object* v___x_708_; lean_object* v___f_709_; lean_object* v___f_710_; lean_object* v___x_711_; 
v___x_708_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__12, &l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__12_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__12);
v___f_709_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__9));
v___f_710_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__8));
v___x_711_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_710_, v___f_709_, v___x_708_);
return v___x_711_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__15(void){
_start:
{
lean_object* v___x_713_; lean_object* v___x_714_; 
v___x_713_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__14));
v___x_714_ = l_Lean_stringToMessageData(v___x_713_);
return v___x_714_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__17(void){
_start:
{
lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_716_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__16));
v___x_717_ = l_Lean_stringToMessageData(v___x_716_);
return v___x_717_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__19(void){
_start:
{
lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_719_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__18));
v___x_720_ = l_Lean_stringToMessageData(v___x_719_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg(lean_object* v_inst_721_, lean_object* v_inst_722_, lean_object* v_inst_723_, lean_object* v_goal_724_, lean_object* v_n_725_, lean_object* v_hypName_726_, lean_object* v_k_727_){
_start:
{
lean_object* v___x_728_; uint8_t v___x_729_; 
v___x_728_ = lean_unsigned_to_nat(0u);
v___x_729_ = lean_nat_dec_eq(v_n_725_, v___x_728_);
if (v___x_729_ == 0)
{
lean_object* v_u_730_; lean_object* v_00_u03c3s_731_; lean_object* v_hyps_732_; lean_object* v_target_733_; lean_object* v___f_734_; lean_object* v___f_735_; lean_object* v___f_736_; lean_object* v___f_737_; lean_object* v_T_738_; lean_object* v_f_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v_a_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v_revertArgs_746_; lean_object* v___x_747_; lean_object* v___f_748_; lean_object* v___x_749_; uint8_t v___x_750_; 
v_u_730_ = lean_ctor_get(v_goal_724_, 0);
lean_inc_n(v_u_730_, 3);
v_00_u03c3s_731_ = lean_ctor_get(v_goal_724_, 1);
lean_inc_ref_n(v_00_u03c3s_731_, 2);
v_hyps_732_ = lean_ctor_get(v_goal_724_, 2);
lean_inc_ref_n(v_hyps_732_, 2);
v_target_733_ = lean_ctor_get(v_goal_724_, 3);
lean_inc_ref_n(v_target_733_, 2);
lean_dec_ref(v_goal_724_);
lean_inc_n(v_inst_723_, 2);
v___f_734_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__0), 2, 1);
lean_closure_set(v___f_734_, 0, v_inst_723_);
lean_inc_n(v_hypName_726_, 2);
v___f_735_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__1___boxed), 6, 1);
lean_closure_set(v___f_735_, 0, v_hypName_726_);
v___f_736_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__0));
v___f_737_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__3), 3, 1);
lean_closure_set(v___f_737_, 0, v_u_730_);
v_T_738_ = l_Lean_Expr_consumeMData(v_target_733_);
v_f_739_ = l_Lean_Expr_getAppFn(v_T_738_);
v___x_740_ = l_Lean_Expr_getAppNumArgs(v_T_738_);
v___x_741_ = lean_mk_empty_array_with_capacity(v___x_740_);
lean_dec(v___x_740_);
lean_inc_ref(v_T_738_);
v_a_742_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_T_738_, v___x_741_);
lean_inc_n(v_n_725_, 2);
lean_inc_ref_n(v_a_742_, 2);
v___x_743_ = l_Array_toSubarray___redArg(v_a_742_, v___x_728_, v_n_725_);
v___x_744_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__1));
v___x_745_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_736_, v___x_743_, v___x_744_);
v_revertArgs_746_ = l_Array_reverse___redArg(v___x_745_);
v___x_747_ = lean_box(v___x_729_);
lean_inc_ref(v_inst_722_);
lean_inc_ref(v___f_737_);
lean_inc(v_k_727_);
lean_inc_ref(v_f_739_);
lean_inc_ref(v___f_734_);
lean_inc_ref(v_revertArgs_746_);
lean_inc_ref(v___f_735_);
lean_inc_ref(v_inst_721_);
v___f_748_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___boxed), 19, 18);
lean_closure_set(v___f_748_, 0, v_inst_721_);
lean_closure_set(v___f_748_, 1, v_inst_723_);
lean_closure_set(v___f_748_, 2, v_u_730_);
lean_closure_set(v___f_748_, 3, v_00_u03c3s_731_);
lean_closure_set(v___f_748_, 4, v_hypName_726_);
lean_closure_set(v___f_748_, 5, v_hyps_732_);
lean_closure_set(v___f_748_, 6, v___x_747_);
lean_closure_set(v___f_748_, 7, v___f_735_);
lean_closure_set(v___f_748_, 8, v_revertArgs_746_);
lean_closure_set(v___f_748_, 9, v___f_734_);
lean_closure_set(v___f_748_, 10, v_target_733_);
lean_closure_set(v___f_748_, 11, v_a_742_);
lean_closure_set(v___f_748_, 12, v_n_725_);
lean_closure_set(v___f_748_, 13, v_f_739_);
lean_closure_set(v___f_748_, 14, v_k_727_);
lean_closure_set(v___f_748_, 15, v___x_728_);
lean_closure_set(v___f_748_, 16, v___f_737_);
lean_closure_set(v___f_748_, 17, v_inst_722_);
v___x_749_ = lean_array_get_size(v_revertArgs_746_);
v___x_750_ = lean_nat_dec_eq(v___x_749_, v_n_725_);
if (v___x_750_ == 0)
{
lean_object* v_toBind_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_828_; 
lean_dec_ref(v_revertArgs_746_);
lean_dec_ref(v_a_742_);
lean_dec_ref(v_f_739_);
lean_dec_ref(v___f_737_);
lean_dec_ref(v___f_735_);
lean_dec_ref(v___f_734_);
lean_dec_ref(v_target_733_);
lean_dec_ref(v_hyps_732_);
lean_dec_ref(v_00_u03c3s_731_);
lean_dec(v_u_730_);
lean_dec(v_k_727_);
lean_dec(v_hypName_726_);
lean_dec_ref(v_inst_722_);
v_toBind_751_ = lean_ctor_get(v_inst_721_, 1);
v_isSharedCheck_828_ = !lean_is_exclusive(v_inst_721_);
if (v_isSharedCheck_828_ == 0)
{
lean_object* v_unused_829_; 
v_unused_829_ = lean_ctor_get(v_inst_721_, 0);
lean_dec(v_unused_829_);
v___x_753_ = v_inst_721_;
v_isShared_754_ = v_isSharedCheck_828_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_toBind_751_);
lean_dec(v_inst_721_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_828_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v___x_755_; lean_object* v_toApplicative_756_; lean_object* v_toFunctor_757_; lean_object* v_toSeq_758_; lean_object* v_toSeqLeft_759_; lean_object* v_toSeqRight_760_; lean_object* v___f_761_; lean_object* v___f_762_; lean_object* v___f_763_; lean_object* v___f_764_; lean_object* v___x_765_; lean_object* v___f_766_; lean_object* v___f_767_; lean_object* v___f_768_; lean_object* v___x_769_; lean_object* v___x_771_; 
v___x_755_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__1);
v_toApplicative_756_ = lean_ctor_get(v___x_755_, 0);
v_toFunctor_757_ = lean_ctor_get(v_toApplicative_756_, 0);
v_toSeq_758_ = lean_ctor_get(v_toApplicative_756_, 2);
v_toSeqLeft_759_ = lean_ctor_get(v_toApplicative_756_, 3);
v_toSeqRight_760_ = lean_ctor_get(v_toApplicative_756_, 4);
v___f_761_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__2));
v___f_762_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__3));
lean_inc_ref_n(v_toFunctor_757_, 2);
v___f_763_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_763_, 0, v_toFunctor_757_);
v___f_764_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_764_, 0, v_toFunctor_757_);
v___x_765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_765_, 0, v___f_763_);
lean_ctor_set(v___x_765_, 1, v___f_764_);
lean_inc(v_toSeqRight_760_);
v___f_766_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_766_, 0, v_toSeqRight_760_);
lean_inc(v_toSeqLeft_759_);
v___f_767_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_767_, 0, v_toSeqLeft_759_);
lean_inc(v_toSeq_758_);
v___f_768_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_768_, 0, v_toSeq_758_);
v___x_769_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_769_, 0, v___x_765_);
lean_ctor_set(v___x_769_, 1, v___f_761_);
lean_ctor_set(v___x_769_, 2, v___f_768_);
lean_ctor_set(v___x_769_, 3, v___f_767_);
lean_ctor_set(v___x_769_, 4, v___f_766_);
if (v_isShared_754_ == 0)
{
lean_ctor_set(v___x_753_, 1, v___f_762_);
lean_ctor_set(v___x_753_, 0, v___x_769_);
v___x_771_ = v___x_753_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v___x_769_);
lean_ctor_set(v_reuseFailAlloc_827_, 1, v___f_762_);
v___x_771_ = v_reuseFailAlloc_827_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
lean_object* v___x_772_; lean_object* v_toApplicative_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_825_; 
v___x_772_ = l_StateRefT_x27_instMonad___redArg(v___x_771_);
v_toApplicative_773_ = lean_ctor_get(v___x_772_, 0);
v_isSharedCheck_825_ = !lean_is_exclusive(v___x_772_);
if (v_isSharedCheck_825_ == 0)
{
lean_object* v_unused_826_; 
v_unused_826_ = lean_ctor_get(v___x_772_, 1);
lean_dec(v_unused_826_);
v___x_775_ = v___x_772_;
v_isShared_776_ = v_isSharedCheck_825_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_toApplicative_773_);
lean_dec(v___x_772_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_825_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v_toFunctor_777_; lean_object* v_toSeq_778_; lean_object* v_toSeqLeft_779_; lean_object* v_toSeqRight_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_823_; 
v_toFunctor_777_ = lean_ctor_get(v_toApplicative_773_, 0);
v_toSeq_778_ = lean_ctor_get(v_toApplicative_773_, 2);
v_toSeqLeft_779_ = lean_ctor_get(v_toApplicative_773_, 3);
v_toSeqRight_780_ = lean_ctor_get(v_toApplicative_773_, 4);
v_isSharedCheck_823_ = !lean_is_exclusive(v_toApplicative_773_);
if (v_isSharedCheck_823_ == 0)
{
lean_object* v_unused_824_; 
v_unused_824_ = lean_ctor_get(v_toApplicative_773_, 1);
lean_dec(v_unused_824_);
v___x_782_ = v_toApplicative_773_;
v_isShared_783_ = v_isSharedCheck_823_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_toSeqRight_780_);
lean_inc(v_toSeqLeft_779_);
lean_inc(v_toSeq_778_);
lean_inc(v_toFunctor_777_);
lean_dec(v_toApplicative_773_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_823_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___f_784_; lean_object* v___f_785_; lean_object* v___f_786_; lean_object* v___f_787_; lean_object* v___x_788_; lean_object* v___f_789_; lean_object* v___f_790_; lean_object* v___f_791_; lean_object* v___x_793_; 
v___f_784_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__4));
v___f_785_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__5));
lean_inc_ref(v_toFunctor_777_);
v___f_786_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_786_, 0, v_toFunctor_777_);
v___f_787_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_787_, 0, v_toFunctor_777_);
v___x_788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_788_, 0, v___f_786_);
lean_ctor_set(v___x_788_, 1, v___f_787_);
v___f_789_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_789_, 0, v_toSeqRight_780_);
v___f_790_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_790_, 0, v_toSeqLeft_779_);
v___f_791_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_791_, 0, v_toSeq_778_);
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 4, v___f_789_);
lean_ctor_set(v___x_782_, 3, v___f_790_);
lean_ctor_set(v___x_782_, 2, v___f_791_);
lean_ctor_set(v___x_782_, 1, v___f_784_);
lean_ctor_set(v___x_782_, 0, v___x_788_);
v___x_793_ = v___x_782_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v___x_788_);
lean_ctor_set(v_reuseFailAlloc_822_, 1, v___f_784_);
lean_ctor_set(v_reuseFailAlloc_822_, 2, v___f_791_);
lean_ctor_set(v_reuseFailAlloc_822_, 3, v___f_790_);
lean_ctor_set(v_reuseFailAlloc_822_, 4, v___f_789_);
v___x_793_ = v_reuseFailAlloc_822_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
lean_object* v___x_795_; 
if (v_isShared_776_ == 0)
{
lean_ctor_set(v___x_775_, 1, v___f_785_);
lean_ctor_set(v___x_775_, 0, v___x_793_);
v___x_795_ = v___x_775_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v___x_793_);
lean_ctor_set(v_reuseFailAlloc_821_, 1, v___f_785_);
v___x_795_ = v_reuseFailAlloc_821_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v_toMonadRef_798_; lean_object* v___f_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_796_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__7, &l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__7_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__7);
v___x_797_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__13, &l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__13_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__13);
v_toMonadRef_798_ = lean_ctor_get(v___x_797_, 0);
v___f_799_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__21), 2, 1);
lean_closure_set(v___f_799_, 0, v___f_748_);
v___x_800_ = l_Lean_Meta_instAddMessageContextMetaM;
lean_inc_ref(v___x_795_);
v___x_801_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___x_800_, v___x_795_);
lean_inc_ref(v_toMonadRef_798_);
v___x_802_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_802_, 0, v___x_796_);
lean_ctor_set(v___x_802_, 1, v_toMonadRef_798_);
lean_ctor_set(v___x_802_, 2, v___x_801_);
v___x_803_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__15, &l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__15_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__15);
v___x_804_ = l_Nat_reprFast(v_n_725_);
v___x_805_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_805_, 0, v___x_804_);
v___x_806_ = l_Lean_MessageData_ofFormat(v___x_805_);
v___x_807_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_807_, 0, v___x_803_);
lean_ctor_set(v___x_807_, 1, v___x_806_);
v___x_808_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__17, &l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__17_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__17);
v___x_809_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_809_, 0, v___x_807_);
lean_ctor_set(v___x_809_, 1, v___x_808_);
v___x_810_ = l_Lean_MessageData_ofExpr(v_T_738_);
v___x_811_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_811_, 0, v___x_809_);
lean_ctor_set(v___x_811_, 1, v___x_810_);
v___x_812_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__19, &l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__19_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__19);
v___x_813_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_813_, 0, v___x_811_);
lean_ctor_set(v___x_813_, 1, v___x_812_);
v___x_814_ = l_Nat_reprFast(v___x_749_);
v___x_815_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_815_, 0, v___x_814_);
v___x_816_ = l_Lean_MessageData_ofFormat(v___x_815_);
v___x_817_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_817_, 0, v___x_813_);
lean_ctor_set(v___x_817_, 1, v___x_816_);
v___x_818_ = l_Lean_throwError___redArg(v___x_795_, v___x_802_, v___x_817_);
v___x_819_ = lean_apply_2(v_inst_723_, lean_box(0), v___x_818_);
v___x_820_ = lean_apply_4(v_toBind_751_, lean_box(0), lean_box(0), v___x_819_, v___f_799_);
return v___x_820_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_830_; lean_object* v___x_831_; 
lean_dec_ref(v___f_748_);
lean_dec_ref(v_T_738_);
v___x_830_ = lean_box(0);
v___x_831_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20(v_inst_721_, v_inst_723_, v_u_730_, v_00_u03c3s_731_, v_hypName_726_, v_hyps_732_, v___x_729_, v___f_735_, v_revertArgs_746_, v___f_734_, v_target_733_, v_a_742_, v_n_725_, v_f_739_, v_k_727_, v___x_728_, v___f_737_, v_inst_722_, v___x_830_);
return v___x_831_;
}
}
else
{
lean_object* v___x_832_; 
lean_dec(v_hypName_726_);
lean_dec(v_n_725_);
lean_dec(v_inst_723_);
lean_dec_ref(v_inst_722_);
lean_dec_ref(v_inst_721_);
v___x_832_ = lean_apply_1(v_k_727_, v_goal_724_);
return v___x_832_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN(lean_object* v_m_833_, lean_object* v_inst_834_, lean_object* v_inst_835_, lean_object* v_inst_836_, lean_object* v_goal_837_, lean_object* v_n_838_, lean_object* v_hypName_839_, lean_object* v_k_840_){
_start:
{
lean_object* v___x_841_; 
v___x_841_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg(v_inst_834_, v_inst_835_, v_inst_836_, v_goal_837_, v_n_838_, v_hypName_839_, v_k_840_);
return v___x_841_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; 
v___x_842_ = lean_box(0);
v___x_843_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_844_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_844_, 0, v___x_843_);
lean_ctor_set(v___x_844_, 1, v___x_842_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg(){
_start:
{
lean_object* v___x_846_; lean_object* v___x_847_; 
v___x_846_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg___closed__0);
v___x_847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_847_, 0, v___x_846_);
return v___x_847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg___boxed(lean_object* v___y_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg();
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0(lean_object* v_00_u03b1_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_){
_start:
{
lean_object* v___x_860_; 
v___x_860_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg();
return v___x_860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___boxed(lean_object* v_00_u03b1_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_){
_start:
{
lean_object* v_res_871_; 
v_res_871_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0(v_00_u03b1_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_);
lean_dec(v___y_869_);
lean_dec_ref(v___y_868_);
lean_dec(v___y_867_);
lean_dec_ref(v___y_866_);
lean_dec(v___y_865_);
lean_dec_ref(v___y_864_);
lean_dec(v___y_863_);
lean_dec_ref(v___y_862_);
return v_res_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___redArg___lam__0(lean_object* v_x_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_){
_start:
{
lean_object* v___x_882_; 
lean_inc(v___y_876_);
lean_inc_ref(v___y_875_);
lean_inc(v___y_874_);
lean_inc_ref(v___y_873_);
v___x_882_ = lean_apply_9(v_x_872_, v___y_873_, v___y_874_, v___y_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, lean_box(0));
return v___x_882_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___redArg___lam__0___boxed(lean_object* v_x_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_){
_start:
{
lean_object* v_res_893_; 
v_res_893_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___redArg___lam__0(v_x_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_, v___y_890_, v___y_891_);
lean_dec(v___y_887_);
lean_dec_ref(v___y_886_);
lean_dec(v___y_885_);
lean_dec_ref(v___y_884_);
return v_res_893_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___redArg(lean_object* v_mvarId_894_, lean_object* v_x_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_){
_start:
{
lean_object* v___f_905_; lean_object* v___x_906_; 
lean_inc(v___y_899_);
lean_inc_ref(v___y_898_);
lean_inc(v___y_897_);
lean_inc_ref(v___y_896_);
v___f_905_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_905_, 0, v_x_895_);
lean_closure_set(v___f_905_, 1, v___y_896_);
lean_closure_set(v___f_905_, 2, v___y_897_);
lean_closure_set(v___f_905_, 3, v___y_898_);
lean_closure_set(v___f_905_, 4, v___y_899_);
v___x_906_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_894_, v___f_905_, v___y_900_, v___y_901_, v___y_902_, v___y_903_);
if (lean_obj_tag(v___x_906_) == 0)
{
return v___x_906_;
}
else
{
lean_object* v_a_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_914_; 
v_a_907_ = lean_ctor_get(v___x_906_, 0);
v_isSharedCheck_914_ = !lean_is_exclusive(v___x_906_);
if (v_isSharedCheck_914_ == 0)
{
v___x_909_ = v___x_906_;
v_isShared_910_ = v_isSharedCheck_914_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_a_907_);
lean_dec(v___x_906_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_914_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v___x_912_; 
if (v_isShared_910_ == 0)
{
v___x_912_ = v___x_909_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v_a_907_);
v___x_912_ = v_reuseFailAlloc_913_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
return v___x_912_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___redArg___boxed(lean_object* v_mvarId_915_, lean_object* v_x_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_){
_start:
{
lean_object* v_res_926_; 
v_res_926_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___redArg(v_mvarId_915_, v_x_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
lean_dec(v___y_924_);
lean_dec_ref(v___y_923_);
lean_dec(v___y_922_);
lean_dec_ref(v___y_921_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
return v_res_926_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3(lean_object* v_00_u03b1_927_, lean_object* v_mvarId_928_, lean_object* v_x_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_){
_start:
{
lean_object* v___x_939_; 
v___x_939_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___redArg(v_mvarId_928_, v_x_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
return v___x_939_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___boxed(lean_object* v_00_u03b1_940_, lean_object* v_mvarId_941_, lean_object* v_x_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_){
_start:
{
lean_object* v_res_952_; 
v_res_952_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3(v_00_u03b1_940_, v_mvarId_941_, v_x_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_);
lean_dec(v___y_950_);
lean_dec_ref(v___y_949_);
lean_dec(v___y_948_);
lean_dec_ref(v___y_947_);
lean_dec(v___y_946_);
lean_dec_ref(v___y_945_);
lean_dec(v___y_944_);
lean_dec_ref(v___y_943_);
return v_res_952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevert___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__4(lean_object* v_goal_960_, lean_object* v_ref_961_, lean_object* v_k_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_){
_start:
{
lean_object* v___x_972_; 
lean_inc_ref(v_goal_960_);
v___x_972_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo(v_goal_960_, v_ref_961_, v___y_967_, v___y_968_, v___y_969_, v___y_970_);
if (lean_obj_tag(v___x_972_) == 0)
{
lean_object* v_a_973_; lean_object* v_u_974_; lean_object* v_00_u03c3s_975_; lean_object* v_hyps_976_; lean_object* v_target_977_; lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_1004_; 
v_a_973_ = lean_ctor_get(v___x_972_, 0);
lean_inc(v_a_973_);
lean_dec_ref(v___x_972_);
v_u_974_ = lean_ctor_get(v_goal_960_, 0);
v_00_u03c3s_975_ = lean_ctor_get(v_goal_960_, 1);
v_hyps_976_ = lean_ctor_get(v_goal_960_, 2);
v_target_977_ = lean_ctor_get(v_goal_960_, 3);
v_isSharedCheck_1004_ = !lean_is_exclusive(v_goal_960_);
if (v_isSharedCheck_1004_ == 0)
{
v___x_979_ = v_goal_960_;
v_isShared_980_ = v_isSharedCheck_1004_;
goto v_resetjp_978_;
}
else
{
lean_inc(v_target_977_);
lean_inc(v_hyps_976_);
lean_inc(v_00_u03c3s_975_);
lean_inc(v_u_974_);
lean_dec(v_goal_960_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_1004_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v_focusHyp_981_; lean_object* v_restHyps_982_; lean_object* v_proof_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_990_; 
v_focusHyp_981_ = lean_ctor_get(v_a_973_, 0);
lean_inc_ref_n(v_focusHyp_981_, 2);
v_restHyps_982_ = lean_ctor_get(v_a_973_, 1);
lean_inc_ref_n(v_restHyps_982_, 2);
v_proof_983_ = lean_ctor_get(v_a_973_, 2);
lean_inc_ref(v_proof_983_);
lean_dec(v_a_973_);
v___x_984_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__4));
v___x_985_ = lean_box(0);
lean_inc(v_u_974_);
v___x_986_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_986_, 0, v_u_974_);
lean_ctor_set(v___x_986_, 1, v___x_985_);
lean_inc_ref(v___x_986_);
v___x_987_ = l_Lean_mkConst(v___x_984_, v___x_986_);
lean_inc_ref(v_target_977_);
lean_inc_ref_n(v_00_u03c3s_975_, 2);
v___x_988_ = l_Lean_mkApp3(v___x_987_, v_00_u03c3s_975_, v_focusHyp_981_, v_target_977_);
if (v_isShared_980_ == 0)
{
lean_ctor_set(v___x_979_, 3, v___x_988_);
lean_ctor_set(v___x_979_, 2, v_restHyps_982_);
v___x_990_ = v___x_979_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v_u_974_);
lean_ctor_set(v_reuseFailAlloc_1003_, 1, v_00_u03c3s_975_);
lean_ctor_set(v_reuseFailAlloc_1003_, 2, v_restHyps_982_);
lean_ctor_set(v_reuseFailAlloc_1003_, 3, v___x_988_);
v___x_990_ = v_reuseFailAlloc_1003_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
lean_object* v___x_991_; 
lean_inc(v___y_970_);
lean_inc_ref(v___y_969_);
lean_inc(v___y_968_);
lean_inc_ref(v___y_967_);
lean_inc(v___y_966_);
lean_inc_ref(v___y_965_);
lean_inc(v___y_964_);
lean_inc_ref(v___y_963_);
v___x_991_ = lean_apply_10(v_k_962_, v___x_990_, v___y_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, lean_box(0));
if (lean_obj_tag(v___x_991_) == 0)
{
lean_object* v_a_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_1002_; 
v_a_992_ = lean_ctor_get(v___x_991_, 0);
v_isSharedCheck_1002_ = !lean_is_exclusive(v___x_991_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_994_ = v___x_991_;
v_isShared_995_ = v_isSharedCheck_1002_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_a_992_);
lean_dec(v___x_991_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_1002_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v_prf_998_; lean_object* v___x_1000_; 
v___x_996_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__4___closed__0));
v___x_997_ = l_Lean_mkConst(v___x_996_, v___x_986_);
v_prf_998_ = l_Lean_mkApp7(v___x_997_, v_00_u03c3s_975_, v_hyps_976_, v_restHyps_982_, v_focusHyp_981_, v_target_977_, v_proof_983_, v_a_992_);
if (v_isShared_995_ == 0)
{
lean_ctor_set(v___x_994_, 0, v_prf_998_);
v___x_1000_ = v___x_994_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v_prf_998_);
v___x_1000_ = v_reuseFailAlloc_1001_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
return v___x_1000_;
}
}
}
else
{
lean_dec_ref(v___x_986_);
lean_dec_ref(v_proof_983_);
lean_dec_ref(v_restHyps_982_);
lean_dec_ref(v_focusHyp_981_);
lean_dec_ref(v_target_977_);
lean_dec_ref(v_hyps_976_);
lean_dec_ref(v_00_u03c3s_975_);
return v___x_991_;
}
}
}
}
else
{
lean_object* v_a_1005_; lean_object* v___x_1007_; uint8_t v_isShared_1008_; uint8_t v_isSharedCheck_1012_; 
lean_dec_ref(v_k_962_);
lean_dec_ref(v_goal_960_);
v_a_1005_ = lean_ctor_get(v___x_972_, 0);
v_isSharedCheck_1012_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_1012_ == 0)
{
v___x_1007_ = v___x_972_;
v_isShared_1008_ = v_isSharedCheck_1012_;
goto v_resetjp_1006_;
}
else
{
lean_inc(v_a_1005_);
lean_dec(v___x_972_);
v___x_1007_ = lean_box(0);
v_isShared_1008_ = v_isSharedCheck_1012_;
goto v_resetjp_1006_;
}
v_resetjp_1006_:
{
lean_object* v___x_1010_; 
if (v_isShared_1008_ == 0)
{
v___x_1010_ = v___x_1007_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v_a_1005_);
v___x_1010_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
return v___x_1010_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevert___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__4___boxed(lean_object* v_goal_1013_, lean_object* v_ref_1014_, lean_object* v_k_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_){
_start:
{
lean_object* v_res_1025_; 
v_res_1025_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevert___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__4(v_goal_1013_, v_ref_1014_, v_k_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_);
lean_dec(v___y_1023_);
lean_dec_ref(v___y_1022_);
lean_dec(v___y_1021_);
lean_dec_ref(v___y_1020_);
lean_dec(v___y_1019_);
lean_dec_ref(v___y_1018_);
lean_dec(v___y_1017_);
lean_dec_ref(v___y_1016_);
return v_res_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__0(lean_object* v_val_1026_, lean_object* v_newGoal_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_){
_start:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; 
v___x_1037_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v_newGoal_1027_);
v___x_1038_ = lean_box(0);
v___x_1039_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_1037_, v___x_1038_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_);
if (lean_obj_tag(v___x_1039_) == 0)
{
lean_object* v_a_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1051_; 
v_a_1040_ = lean_ctor_get(v___x_1039_, 0);
v_isSharedCheck_1051_ = !lean_is_exclusive(v___x_1039_);
if (v_isSharedCheck_1051_ == 0)
{
v___x_1042_ = v___x_1039_;
v_isShared_1043_ = v_isSharedCheck_1051_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_a_1040_);
lean_dec(v___x_1039_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1051_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1049_; 
v___x_1044_ = lean_st_ref_take(v_val_1026_);
v___x_1045_ = l_Lean_Expr_mvarId_x21(v_a_1040_);
v___x_1046_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1045_);
lean_ctor_set(v___x_1046_, 1, v___x_1044_);
v___x_1047_ = lean_st_ref_set(v_val_1026_, v___x_1046_);
if (v_isShared_1043_ == 0)
{
v___x_1049_ = v___x_1042_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v_a_1040_);
v___x_1049_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
return v___x_1049_;
}
}
}
else
{
return v___x_1039_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__0___boxed(lean_object* v_val_1052_, lean_object* v_newGoal_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_){
_start:
{
lean_object* v_res_1063_; 
v_res_1063_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__0(v_val_1052_, v_newGoal_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_);
lean_dec(v___y_1061_);
lean_dec_ref(v___y_1060_);
lean_dec(v___y_1059_);
lean_dec_ref(v___y_1058_);
lean_dec(v___y_1057_);
lean_dec_ref(v___y_1056_);
lean_dec(v___y_1055_);
lean_dec_ref(v___y_1054_);
lean_dec(v_val_1052_);
return v_res_1063_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15_spec__20_spec__22___redArg(lean_object* v_x_1064_, lean_object* v_x_1065_, lean_object* v_x_1066_, lean_object* v_x_1067_){
_start:
{
lean_object* v_ks_1068_; lean_object* v_vs_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1093_; 
v_ks_1068_ = lean_ctor_get(v_x_1064_, 0);
v_vs_1069_ = lean_ctor_get(v_x_1064_, 1);
v_isSharedCheck_1093_ = !lean_is_exclusive(v_x_1064_);
if (v_isSharedCheck_1093_ == 0)
{
v___x_1071_ = v_x_1064_;
v_isShared_1072_ = v_isSharedCheck_1093_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_vs_1069_);
lean_inc(v_ks_1068_);
lean_dec(v_x_1064_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1093_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v___x_1073_; uint8_t v___x_1074_; 
v___x_1073_ = lean_array_get_size(v_ks_1068_);
v___x_1074_ = lean_nat_dec_lt(v_x_1065_, v___x_1073_);
if (v___x_1074_ == 0)
{
lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1078_; 
lean_dec(v_x_1065_);
v___x_1075_ = lean_array_push(v_ks_1068_, v_x_1066_);
v___x_1076_ = lean_array_push(v_vs_1069_, v_x_1067_);
if (v_isShared_1072_ == 0)
{
lean_ctor_set(v___x_1071_, 1, v___x_1076_);
lean_ctor_set(v___x_1071_, 0, v___x_1075_);
v___x_1078_ = v___x_1071_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v___x_1075_);
lean_ctor_set(v_reuseFailAlloc_1079_, 1, v___x_1076_);
v___x_1078_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
return v___x_1078_;
}
}
else
{
lean_object* v_k_x27_1080_; uint8_t v___x_1081_; 
v_k_x27_1080_ = lean_array_fget_borrowed(v_ks_1068_, v_x_1065_);
v___x_1081_ = l_Lean_instBEqMVarId_beq(v_x_1066_, v_k_x27_1080_);
if (v___x_1081_ == 0)
{
lean_object* v___x_1083_; 
if (v_isShared_1072_ == 0)
{
v___x_1083_ = v___x_1071_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v_ks_1068_);
lean_ctor_set(v_reuseFailAlloc_1087_, 1, v_vs_1069_);
v___x_1083_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
lean_object* v___x_1084_; lean_object* v___x_1085_; 
v___x_1084_ = lean_unsigned_to_nat(1u);
v___x_1085_ = lean_nat_add(v_x_1065_, v___x_1084_);
lean_dec(v_x_1065_);
v_x_1064_ = v___x_1083_;
v_x_1065_ = v___x_1085_;
goto _start;
}
}
else
{
lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1091_; 
v___x_1088_ = lean_array_fset(v_ks_1068_, v_x_1065_, v_x_1066_);
v___x_1089_ = lean_array_fset(v_vs_1069_, v_x_1065_, v_x_1067_);
lean_dec(v_x_1065_);
if (v_isShared_1072_ == 0)
{
lean_ctor_set(v___x_1071_, 1, v___x_1089_);
lean_ctor_set(v___x_1071_, 0, v___x_1088_);
v___x_1091_ = v___x_1071_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v___x_1088_);
lean_ctor_set(v_reuseFailAlloc_1092_, 1, v___x_1089_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
return v___x_1091_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15_spec__20___redArg(lean_object* v_n_1094_, lean_object* v_k_1095_, lean_object* v_v_1096_){
_start:
{
lean_object* v___x_1097_; lean_object* v___x_1098_; 
v___x_1097_ = lean_unsigned_to_nat(0u);
v___x_1098_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15_spec__20_spec__22___redArg(v_n_1094_, v___x_1097_, v_k_1095_, v_v_1096_);
return v___x_1098_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15___redArg___closed__0(void){
_start:
{
size_t v___x_1099_; size_t v___x_1100_; size_t v___x_1101_; 
v___x_1099_ = ((size_t)5ULL);
v___x_1100_ = ((size_t)1ULL);
v___x_1101_ = lean_usize_shift_left(v___x_1100_, v___x_1099_);
return v___x_1101_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15___redArg___closed__1(void){
_start:
{
size_t v___x_1102_; size_t v___x_1103_; size_t v___x_1104_; 
v___x_1102_ = ((size_t)1ULL);
v___x_1103_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15___redArg___closed__0);
v___x_1104_ = lean_usize_sub(v___x_1103_, v___x_1102_);
return v___x_1104_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15___redArg___closed__2(void){
_start:
{
lean_object* v___x_1105_; 
v___x_1105_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15___redArg(lean_object* v_x_1106_, size_t v_x_1107_, size_t v_x_1108_, lean_object* v_x_1109_, lean_object* v_x_1110_){
_start:
{
if (lean_obj_tag(v_x_1106_) == 0)
{
lean_object* v_es_1111_; size_t v___x_1112_; size_t v___x_1113_; size_t v___x_1114_; size_t v___x_1115_; lean_object* v_j_1116_; lean_object* v___x_1117_; uint8_t v___x_1118_; 
v_es_1111_ = lean_ctor_get(v_x_1106_, 0);
v___x_1112_ = ((size_t)5ULL);
v___x_1113_ = ((size_t)1ULL);
v___x_1114_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15___redArg___closed__1);
v___x_1115_ = lean_usize_land(v_x_1107_, v___x_1114_);
v_j_1116_ = lean_usize_to_nat(v___x_1115_);
v___x_1117_ = lean_array_get_size(v_es_1111_);
v___x_1118_ = lean_nat_dec_lt(v_j_1116_, v___x_1117_);
if (v___x_1118_ == 0)
{
lean_dec(v_j_1116_);
lean_dec(v_x_1110_);
lean_dec(v_x_1109_);
return v_x_1106_;
}
else
{
lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1155_; 
lean_inc_ref(v_es_1111_);
v_isSharedCheck_1155_ = !lean_is_exclusive(v_x_1106_);
if (v_isSharedCheck_1155_ == 0)
{
lean_object* v_unused_1156_; 
v_unused_1156_ = lean_ctor_get(v_x_1106_, 0);
lean_dec(v_unused_1156_);
v___x_1120_ = v_x_1106_;
v_isShared_1121_ = v_isSharedCheck_1155_;
goto v_resetjp_1119_;
}
else
{
lean_dec(v_x_1106_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1155_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v_v_1122_; lean_object* v___x_1123_; lean_object* v_xs_x27_1124_; lean_object* v___y_1126_; 
v_v_1122_ = lean_array_fget(v_es_1111_, v_j_1116_);
v___x_1123_ = lean_box(0);
v_xs_x27_1124_ = lean_array_fset(v_es_1111_, v_j_1116_, v___x_1123_);
switch(lean_obj_tag(v_v_1122_))
{
case 0:
{
lean_object* v_key_1131_; lean_object* v_val_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1142_; 
v_key_1131_ = lean_ctor_get(v_v_1122_, 0);
v_val_1132_ = lean_ctor_get(v_v_1122_, 1);
v_isSharedCheck_1142_ = !lean_is_exclusive(v_v_1122_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1134_ = v_v_1122_;
v_isShared_1135_ = v_isSharedCheck_1142_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_val_1132_);
lean_inc(v_key_1131_);
lean_dec(v_v_1122_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1142_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
uint8_t v___x_1136_; 
v___x_1136_ = l_Lean_instBEqMVarId_beq(v_x_1109_, v_key_1131_);
if (v___x_1136_ == 0)
{
lean_object* v___x_1137_; lean_object* v___x_1138_; 
lean_del_object(v___x_1134_);
v___x_1137_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1131_, v_val_1132_, v_x_1109_, v_x_1110_);
v___x_1138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1138_, 0, v___x_1137_);
v___y_1126_ = v___x_1138_;
goto v___jp_1125_;
}
else
{
lean_object* v___x_1140_; 
lean_dec(v_val_1132_);
lean_dec(v_key_1131_);
if (v_isShared_1135_ == 0)
{
lean_ctor_set(v___x_1134_, 1, v_x_1110_);
lean_ctor_set(v___x_1134_, 0, v_x_1109_);
v___x_1140_ = v___x_1134_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v_x_1109_);
lean_ctor_set(v_reuseFailAlloc_1141_, 1, v_x_1110_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
v___y_1126_ = v___x_1140_;
goto v___jp_1125_;
}
}
}
}
case 1:
{
lean_object* v_node_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1153_; 
v_node_1143_ = lean_ctor_get(v_v_1122_, 0);
v_isSharedCheck_1153_ = !lean_is_exclusive(v_v_1122_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1145_ = v_v_1122_;
v_isShared_1146_ = v_isSharedCheck_1153_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_node_1143_);
lean_dec(v_v_1122_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1153_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
size_t v___x_1147_; size_t v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1151_; 
v___x_1147_ = lean_usize_shift_right(v_x_1107_, v___x_1112_);
v___x_1148_ = lean_usize_add(v_x_1108_, v___x_1113_);
v___x_1149_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15___redArg(v_node_1143_, v___x_1147_, v___x_1148_, v_x_1109_, v_x_1110_);
if (v_isShared_1146_ == 0)
{
lean_ctor_set(v___x_1145_, 0, v___x_1149_);
v___x_1151_ = v___x_1145_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v___x_1149_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
v___y_1126_ = v___x_1151_;
goto v___jp_1125_;
}
}
}
default: 
{
lean_object* v___x_1154_; 
v___x_1154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1154_, 0, v_x_1109_);
lean_ctor_set(v___x_1154_, 1, v_x_1110_);
v___y_1126_ = v___x_1154_;
goto v___jp_1125_;
}
}
v___jp_1125_:
{
lean_object* v___x_1127_; lean_object* v___x_1129_; 
v___x_1127_ = lean_array_fset(v_xs_x27_1124_, v_j_1116_, v___y_1126_);
lean_dec(v_j_1116_);
if (v_isShared_1121_ == 0)
{
lean_ctor_set(v___x_1120_, 0, v___x_1127_);
v___x_1129_ = v___x_1120_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v___x_1127_);
v___x_1129_ = v_reuseFailAlloc_1130_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
return v___x_1129_;
}
}
}
}
}
else
{
lean_object* v_ks_1157_; lean_object* v_vs_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1178_; 
v_ks_1157_ = lean_ctor_get(v_x_1106_, 0);
v_vs_1158_ = lean_ctor_get(v_x_1106_, 1);
v_isSharedCheck_1178_ = !lean_is_exclusive(v_x_1106_);
if (v_isSharedCheck_1178_ == 0)
{
v___x_1160_ = v_x_1106_;
v_isShared_1161_ = v_isSharedCheck_1178_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_vs_1158_);
lean_inc(v_ks_1157_);
lean_dec(v_x_1106_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1178_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___x_1163_; 
if (v_isShared_1161_ == 0)
{
v___x_1163_ = v___x_1160_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v_ks_1157_);
lean_ctor_set(v_reuseFailAlloc_1177_, 1, v_vs_1158_);
v___x_1163_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
lean_object* v_newNode_1164_; uint8_t v___y_1166_; size_t v___x_1172_; uint8_t v___x_1173_; 
v_newNode_1164_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15_spec__20___redArg(v___x_1163_, v_x_1109_, v_x_1110_);
v___x_1172_ = ((size_t)7ULL);
v___x_1173_ = lean_usize_dec_le(v___x_1172_, v_x_1108_);
if (v___x_1173_ == 0)
{
lean_object* v___x_1174_; lean_object* v___x_1175_; uint8_t v___x_1176_; 
v___x_1174_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1164_);
v___x_1175_ = lean_unsigned_to_nat(4u);
v___x_1176_ = lean_nat_dec_lt(v___x_1174_, v___x_1175_);
lean_dec(v___x_1174_);
v___y_1166_ = v___x_1176_;
goto v___jp_1165_;
}
else
{
v___y_1166_ = v___x_1173_;
goto v___jp_1165_;
}
v___jp_1165_:
{
if (v___y_1166_ == 0)
{
lean_object* v_ks_1167_; lean_object* v_vs_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; 
v_ks_1167_ = lean_ctor_get(v_newNode_1164_, 0);
lean_inc_ref(v_ks_1167_);
v_vs_1168_ = lean_ctor_get(v_newNode_1164_, 1);
lean_inc_ref(v_vs_1168_);
lean_dec_ref(v_newNode_1164_);
v___x_1169_ = lean_unsigned_to_nat(0u);
v___x_1170_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15___redArg___closed__2);
v___x_1171_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15_spec__21___redArg(v_x_1108_, v_ks_1167_, v_vs_1168_, v___x_1169_, v___x_1170_);
lean_dec_ref(v_vs_1168_);
lean_dec_ref(v_ks_1167_);
return v___x_1171_;
}
else
{
return v_newNode_1164_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15_spec__21___redArg(size_t v_depth_1179_, lean_object* v_keys_1180_, lean_object* v_vals_1181_, lean_object* v_i_1182_, lean_object* v_entries_1183_){
_start:
{
lean_object* v___x_1184_; uint8_t v___x_1185_; 
v___x_1184_ = lean_array_get_size(v_keys_1180_);
v___x_1185_ = lean_nat_dec_lt(v_i_1182_, v___x_1184_);
if (v___x_1185_ == 0)
{
lean_dec(v_i_1182_);
return v_entries_1183_;
}
else
{
lean_object* v_k_1186_; lean_object* v_v_1187_; uint64_t v___x_1188_; size_t v_h_1189_; size_t v___x_1190_; lean_object* v___x_1191_; size_t v___x_1192_; size_t v___x_1193_; size_t v___x_1194_; size_t v_h_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; 
v_k_1186_ = lean_array_fget_borrowed(v_keys_1180_, v_i_1182_);
v_v_1187_ = lean_array_fget_borrowed(v_vals_1181_, v_i_1182_);
v___x_1188_ = l_Lean_instHashableMVarId_hash(v_k_1186_);
v_h_1189_ = lean_uint64_to_usize(v___x_1188_);
v___x_1190_ = ((size_t)5ULL);
v___x_1191_ = lean_unsigned_to_nat(1u);
v___x_1192_ = ((size_t)1ULL);
v___x_1193_ = lean_usize_sub(v_depth_1179_, v___x_1192_);
v___x_1194_ = lean_usize_mul(v___x_1190_, v___x_1193_);
v_h_1195_ = lean_usize_shift_right(v_h_1189_, v___x_1194_);
v___x_1196_ = lean_nat_add(v_i_1182_, v___x_1191_);
lean_dec(v_i_1182_);
lean_inc(v_v_1187_);
lean_inc(v_k_1186_);
v___x_1197_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15___redArg(v_entries_1183_, v_h_1195_, v_depth_1179_, v_k_1186_, v_v_1187_);
v_i_1182_ = v___x_1196_;
v_entries_1183_ = v___x_1197_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15_spec__21___redArg___boxed(lean_object* v_depth_1199_, lean_object* v_keys_1200_, lean_object* v_vals_1201_, lean_object* v_i_1202_, lean_object* v_entries_1203_){
_start:
{
size_t v_depth_boxed_1204_; lean_object* v_res_1205_; 
v_depth_boxed_1204_ = lean_unbox_usize(v_depth_1199_);
lean_dec(v_depth_1199_);
v_res_1205_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15_spec__21___redArg(v_depth_boxed_1204_, v_keys_1200_, v_vals_1201_, v_i_1202_, v_entries_1203_);
lean_dec_ref(v_vals_1201_);
lean_dec_ref(v_keys_1200_);
return v_res_1205_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15___redArg___boxed(lean_object* v_x_1206_, lean_object* v_x_1207_, lean_object* v_x_1208_, lean_object* v_x_1209_, lean_object* v_x_1210_){
_start:
{
size_t v_x_20317__boxed_1211_; size_t v_x_20318__boxed_1212_; lean_object* v_res_1213_; 
v_x_20317__boxed_1211_ = lean_unbox_usize(v_x_1207_);
lean_dec(v_x_1207_);
v_x_20318__boxed_1212_ = lean_unbox_usize(v_x_1208_);
lean_dec(v_x_1208_);
v_res_1213_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15___redArg(v_x_1206_, v_x_20317__boxed_1211_, v_x_20318__boxed_1212_, v_x_1209_, v_x_1210_);
return v_res_1213_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10___redArg(lean_object* v_x_1214_, lean_object* v_x_1215_, lean_object* v_x_1216_){
_start:
{
uint64_t v___x_1217_; size_t v___x_1218_; size_t v___x_1219_; lean_object* v___x_1220_; 
v___x_1217_ = l_Lean_instHashableMVarId_hash(v_x_1215_);
v___x_1218_ = lean_uint64_to_usize(v___x_1217_);
v___x_1219_ = ((size_t)1ULL);
v___x_1220_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15___redArg(v_x_1214_, v___x_1218_, v___x_1219_, v_x_1215_, v_x_1216_);
return v___x_1220_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2___redArg(lean_object* v_mvarId_1221_, lean_object* v_val_1222_, lean_object* v___y_1223_){
_start:
{
lean_object* v___x_1225_; lean_object* v_mctx_1226_; lean_object* v_cache_1227_; lean_object* v_zetaDeltaFVarIds_1228_; lean_object* v_postponed_1229_; lean_object* v_diag_1230_; lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1257_; 
v___x_1225_ = lean_st_ref_take(v___y_1223_);
v_mctx_1226_ = lean_ctor_get(v___x_1225_, 0);
v_cache_1227_ = lean_ctor_get(v___x_1225_, 1);
v_zetaDeltaFVarIds_1228_ = lean_ctor_get(v___x_1225_, 2);
v_postponed_1229_ = lean_ctor_get(v___x_1225_, 3);
v_diag_1230_ = lean_ctor_get(v___x_1225_, 4);
v_isSharedCheck_1257_ = !lean_is_exclusive(v___x_1225_);
if (v_isSharedCheck_1257_ == 0)
{
v___x_1232_ = v___x_1225_;
v_isShared_1233_ = v_isSharedCheck_1257_;
goto v_resetjp_1231_;
}
else
{
lean_inc(v_diag_1230_);
lean_inc(v_postponed_1229_);
lean_inc(v_zetaDeltaFVarIds_1228_);
lean_inc(v_cache_1227_);
lean_inc(v_mctx_1226_);
lean_dec(v___x_1225_);
v___x_1232_ = lean_box(0);
v_isShared_1233_ = v_isSharedCheck_1257_;
goto v_resetjp_1231_;
}
v_resetjp_1231_:
{
lean_object* v_depth_1234_; lean_object* v_levelAssignDepth_1235_; lean_object* v_mvarCounter_1236_; lean_object* v_lDepth_1237_; lean_object* v_decls_1238_; lean_object* v_userNames_1239_; lean_object* v_lAssignment_1240_; lean_object* v_eAssignment_1241_; lean_object* v_dAssignment_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1256_; 
v_depth_1234_ = lean_ctor_get(v_mctx_1226_, 0);
v_levelAssignDepth_1235_ = lean_ctor_get(v_mctx_1226_, 1);
v_mvarCounter_1236_ = lean_ctor_get(v_mctx_1226_, 2);
v_lDepth_1237_ = lean_ctor_get(v_mctx_1226_, 3);
v_decls_1238_ = lean_ctor_get(v_mctx_1226_, 4);
v_userNames_1239_ = lean_ctor_get(v_mctx_1226_, 5);
v_lAssignment_1240_ = lean_ctor_get(v_mctx_1226_, 6);
v_eAssignment_1241_ = lean_ctor_get(v_mctx_1226_, 7);
v_dAssignment_1242_ = lean_ctor_get(v_mctx_1226_, 8);
v_isSharedCheck_1256_ = !lean_is_exclusive(v_mctx_1226_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1244_ = v_mctx_1226_;
v_isShared_1245_ = v_isSharedCheck_1256_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_dAssignment_1242_);
lean_inc(v_eAssignment_1241_);
lean_inc(v_lAssignment_1240_);
lean_inc(v_userNames_1239_);
lean_inc(v_decls_1238_);
lean_inc(v_lDepth_1237_);
lean_inc(v_mvarCounter_1236_);
lean_inc(v_levelAssignDepth_1235_);
lean_inc(v_depth_1234_);
lean_dec(v_mctx_1226_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1256_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v___x_1246_; lean_object* v___x_1248_; 
v___x_1246_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10___redArg(v_eAssignment_1241_, v_mvarId_1221_, v_val_1222_);
if (v_isShared_1245_ == 0)
{
lean_ctor_set(v___x_1244_, 7, v___x_1246_);
v___x_1248_ = v___x_1244_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v_depth_1234_);
lean_ctor_set(v_reuseFailAlloc_1255_, 1, v_levelAssignDepth_1235_);
lean_ctor_set(v_reuseFailAlloc_1255_, 2, v_mvarCounter_1236_);
lean_ctor_set(v_reuseFailAlloc_1255_, 3, v_lDepth_1237_);
lean_ctor_set(v_reuseFailAlloc_1255_, 4, v_decls_1238_);
lean_ctor_set(v_reuseFailAlloc_1255_, 5, v_userNames_1239_);
lean_ctor_set(v_reuseFailAlloc_1255_, 6, v_lAssignment_1240_);
lean_ctor_set(v_reuseFailAlloc_1255_, 7, v___x_1246_);
lean_ctor_set(v_reuseFailAlloc_1255_, 8, v_dAssignment_1242_);
v___x_1248_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
lean_object* v___x_1250_; 
if (v_isShared_1233_ == 0)
{
lean_ctor_set(v___x_1232_, 0, v___x_1248_);
v___x_1250_ = v___x_1232_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v___x_1248_);
lean_ctor_set(v_reuseFailAlloc_1254_, 1, v_cache_1227_);
lean_ctor_set(v_reuseFailAlloc_1254_, 2, v_zetaDeltaFVarIds_1228_);
lean_ctor_set(v_reuseFailAlloc_1254_, 3, v_postponed_1229_);
lean_ctor_set(v_reuseFailAlloc_1254_, 4, v_diag_1230_);
v___x_1250_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; 
v___x_1251_ = lean_st_ref_set(v___y_1223_, v___x_1250_);
v___x_1252_ = lean_box(0);
v___x_1253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1253_, 0, v___x_1252_);
return v___x_1253_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2___redArg___boxed(lean_object* v_mvarId_1258_, lean_object* v_val_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_){
_start:
{
lean_object* v_res_1262_; 
v_res_1262_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2___redArg(v_mvarId_1258_, v_val_1259_, v___y_1260_);
lean_dec(v___y_1260_);
return v_res_1262_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__4___redArg(lean_object* v_as_1263_, lean_object* v_i_1264_, lean_object* v_j_1265_, lean_object* v_bs_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_){
_start:
{
lean_object* v_zero_1270_; uint8_t v_isZero_1271_; 
v_zero_1270_ = lean_unsigned_to_nat(0u);
v_isZero_1271_ = lean_nat_dec_eq(v_i_1264_, v_zero_1270_);
if (v_isZero_1271_ == 1)
{
lean_object* v___x_1272_; 
lean_dec(v_j_1265_);
lean_dec(v_i_1264_);
v___x_1272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1272_, 0, v_bs_1266_);
return v___x_1272_;
}
else
{
lean_object* v___x_1273_; lean_object* v___x_1274_; 
v___x_1273_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__6___closed__1));
v___x_1274_ = l_Lean_Core_mkFreshUserName(v___x_1273_, v___y_1267_, v___y_1268_);
if (lean_obj_tag(v___x_1274_) == 0)
{
lean_object* v_a_1275_; lean_object* v_one_1276_; lean_object* v_n_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; 
v_a_1275_ = lean_ctor_get(v___x_1274_, 0);
lean_inc(v_a_1275_);
lean_dec_ref(v___x_1274_);
v_one_1276_ = lean_unsigned_to_nat(1u);
v_n_1277_ = lean_nat_sub(v_i_1264_, v_one_1276_);
lean_dec(v_i_1264_);
v___x_1278_ = lean_array_fget_borrowed(v_as_1263_, v_j_1265_);
v___x_1279_ = lean_nat_add(v_j_1265_, v_one_1276_);
lean_dec(v_j_1265_);
lean_inc(v___x_1279_);
v___x_1280_ = lean_name_append_index_after(v_a_1275_, v___x_1279_);
lean_inc(v___x_1278_);
v___x_1281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1281_, 0, v___x_1280_);
lean_ctor_set(v___x_1281_, 1, v___x_1278_);
v___x_1282_ = lean_array_push(v_bs_1266_, v___x_1281_);
v_i_1264_ = v_n_1277_;
v_j_1265_ = v___x_1279_;
v_bs_1266_ = v___x_1282_;
goto _start;
}
else
{
lean_object* v_a_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1291_; 
lean_dec_ref(v_bs_1266_);
lean_dec(v_j_1265_);
lean_dec(v_i_1264_);
v_a_1284_ = lean_ctor_get(v___x_1274_, 0);
v_isSharedCheck_1291_ = !lean_is_exclusive(v___x_1274_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1286_ = v___x_1274_;
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_a_1284_);
lean_dec(v___x_1274_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v___x_1289_; 
if (v_isShared_1287_ == 0)
{
v___x_1289_ = v___x_1286_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_a_1284_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__4___redArg___boxed(lean_object* v_as_1292_, lean_object* v_i_1293_, lean_object* v_j_1294_, lean_object* v_bs_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_){
_start:
{
lean_object* v_res_1299_; 
v_res_1299_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__4___redArg(v_as_1292_, v_i_1293_, v_j_1294_, v_bs_1295_, v___y_1296_, v___y_1297_);
lean_dec(v___y_1297_);
lean_dec_ref(v___y_1296_);
lean_dec_ref(v_as_1292_);
return v_res_1299_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5_spec__14(lean_object* v_msgData_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_){
_start:
{
lean_object* v___x_1306_; lean_object* v_env_1307_; lean_object* v___x_1308_; lean_object* v_mctx_1309_; lean_object* v_lctx_1310_; lean_object* v_options_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; 
v___x_1306_ = lean_st_ref_get(v___y_1304_);
v_env_1307_ = lean_ctor_get(v___x_1306_, 0);
lean_inc_ref(v_env_1307_);
lean_dec(v___x_1306_);
v___x_1308_ = lean_st_ref_get(v___y_1302_);
v_mctx_1309_ = lean_ctor_get(v___x_1308_, 0);
lean_inc_ref(v_mctx_1309_);
lean_dec(v___x_1308_);
v_lctx_1310_ = lean_ctor_get(v___y_1301_, 2);
v_options_1311_ = lean_ctor_get(v___y_1303_, 2);
lean_inc_ref(v_options_1311_);
lean_inc_ref(v_lctx_1310_);
v___x_1312_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1312_, 0, v_env_1307_);
lean_ctor_set(v___x_1312_, 1, v_mctx_1309_);
lean_ctor_set(v___x_1312_, 2, v_lctx_1310_);
lean_ctor_set(v___x_1312_, 3, v_options_1311_);
v___x_1313_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1313_, 0, v___x_1312_);
lean_ctor_set(v___x_1313_, 1, v_msgData_1300_);
v___x_1314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1314_, 0, v___x_1313_);
return v___x_1314_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5_spec__14___boxed(lean_object* v_msgData_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_){
_start:
{
lean_object* v_res_1321_; 
v_res_1321_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5_spec__14(v_msgData_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_);
lean_dec(v___y_1319_);
lean_dec_ref(v___y_1318_);
lean_dec(v___y_1317_);
lean_dec_ref(v___y_1316_);
return v_res_1321_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__8___redArg(lean_object* v_msg_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_){
_start:
{
lean_object* v_ref_1328_; lean_object* v___x_1329_; lean_object* v_a_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1338_; 
v_ref_1328_ = lean_ctor_get(v___y_1325_, 5);
v___x_1329_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5_spec__14(v_msg_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_);
v_a_1330_ = lean_ctor_get(v___x_1329_, 0);
v_isSharedCheck_1338_ = !lean_is_exclusive(v___x_1329_);
if (v_isSharedCheck_1338_ == 0)
{
v___x_1332_ = v___x_1329_;
v_isShared_1333_ = v_isSharedCheck_1338_;
goto v_resetjp_1331_;
}
else
{
lean_inc(v_a_1330_);
lean_dec(v___x_1329_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1338_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
lean_object* v___x_1334_; lean_object* v___x_1336_; 
lean_inc(v_ref_1328_);
v___x_1334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1334_, 0, v_ref_1328_);
lean_ctor_set(v___x_1334_, 1, v_a_1330_);
if (v_isShared_1333_ == 0)
{
lean_ctor_set_tag(v___x_1332_, 1);
lean_ctor_set(v___x_1332_, 0, v___x_1334_);
v___x_1336_ = v___x_1332_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1337_; 
v_reuseFailAlloc_1337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1337_, 0, v___x_1334_);
v___x_1336_ = v_reuseFailAlloc_1337_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
return v___x_1336_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__8___redArg___boxed(lean_object* v_msg_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_){
_start:
{
lean_object* v_res_1345_; 
v_res_1345_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__8___redArg(v_msg_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_);
lean_dec(v___y_1343_);
lean_dec_ref(v___y_1342_);
lean_dec(v___y_1341_);
lean_dec_ref(v___y_1340_);
return v_res_1345_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__7(lean_object* v_u_1346_, lean_object* v_as_1347_, size_t v_i_1348_, size_t v_stop_1349_, lean_object* v_b_1350_){
_start:
{
uint8_t v___x_1351_; 
v___x_1351_ = lean_usize_dec_eq(v_i_1348_, v_stop_1349_);
if (v___x_1351_ == 0)
{
size_t v___x_1352_; size_t v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; 
v___x_1352_ = ((size_t)1ULL);
v___x_1353_ = lean_usize_sub(v_i_1348_, v___x_1352_);
v___x_1354_ = lean_array_uget_borrowed(v_as_1347_, v___x_1353_);
lean_inc(v___x_1354_);
lean_inc(v_u_1346_);
v___x_1355_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkCons(v_u_1346_, v___x_1354_, v_b_1350_);
v_i_1348_ = v___x_1353_;
v_b_1350_ = v___x_1355_;
goto _start;
}
else
{
lean_dec(v_u_1346_);
return v_b_1350_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__7___boxed(lean_object* v_u_1357_, lean_object* v_as_1358_, lean_object* v_i_1359_, lean_object* v_stop_1360_, lean_object* v_b_1361_){
_start:
{
size_t v_i_boxed_1362_; size_t v_stop_boxed_1363_; lean_object* v_res_1364_; 
v_i_boxed_1362_ = lean_unbox_usize(v_i_1359_);
lean_dec(v_i_1359_);
v_stop_boxed_1363_ = lean_unbox_usize(v_stop_1360_);
lean_dec(v_stop_1360_);
v_res_1364_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__7(v_u_1357_, v_as_1358_, v_i_boxed_1362_, v_stop_boxed_1363_, v_b_1361_);
lean_dec_ref(v_as_1358_);
return v_res_1364_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__6(size_t v_sz_1365_, size_t v_i_1366_, lean_object* v_bs_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_){
_start:
{
uint8_t v___x_1373_; 
v___x_1373_ = lean_usize_dec_lt(v_i_1366_, v_sz_1365_);
if (v___x_1373_ == 0)
{
lean_object* v___x_1374_; 
v___x_1374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1374_, 0, v_bs_1367_);
return v___x_1374_;
}
else
{
lean_object* v_v_1375_; lean_object* v___x_1376_; 
v_v_1375_ = lean_array_uget_borrowed(v_bs_1367_, v_i_1366_);
lean_inc(v_v_1375_);
v___x_1376_ = l_Lean_Meta_mkEqRefl(v_v_1375_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_);
if (lean_obj_tag(v___x_1376_) == 0)
{
lean_object* v_a_1377_; lean_object* v___x_1378_; lean_object* v_bs_x27_1379_; size_t v___x_1380_; size_t v___x_1381_; lean_object* v___x_1382_; 
v_a_1377_ = lean_ctor_get(v___x_1376_, 0);
lean_inc(v_a_1377_);
lean_dec_ref(v___x_1376_);
v___x_1378_ = lean_unsigned_to_nat(0u);
v_bs_x27_1379_ = lean_array_uset(v_bs_1367_, v_i_1366_, v___x_1378_);
v___x_1380_ = ((size_t)1ULL);
v___x_1381_ = lean_usize_add(v_i_1366_, v___x_1380_);
v___x_1382_ = lean_array_uset(v_bs_x27_1379_, v_i_1366_, v_a_1377_);
v_i_1366_ = v___x_1381_;
v_bs_1367_ = v___x_1382_;
goto _start;
}
else
{
lean_object* v_a_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1391_; 
lean_dec_ref(v_bs_1367_);
v_a_1384_ = lean_ctor_get(v___x_1376_, 0);
v_isSharedCheck_1391_ = !lean_is_exclusive(v___x_1376_);
if (v_isSharedCheck_1391_ == 0)
{
v___x_1386_ = v___x_1376_;
v_isShared_1387_ = v_isSharedCheck_1391_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_a_1384_);
lean_dec(v___x_1376_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1391_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v___x_1389_; 
if (v_isShared_1387_ == 0)
{
v___x_1389_ = v___x_1386_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v_a_1384_);
v___x_1389_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
return v___x_1389_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__6___boxed(lean_object* v_sz_1392_, lean_object* v_i_1393_, lean_object* v_bs_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_){
_start:
{
size_t v_sz_boxed_1400_; size_t v_i_boxed_1401_; lean_object* v_res_1402_; 
v_sz_boxed_1400_ = lean_unbox_usize(v_sz_1392_);
lean_dec(v_sz_1392_);
v_i_boxed_1401_ = lean_unbox_usize(v_i_1393_);
lean_dec(v_i_1393_);
v_res_1402_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__6(v_sz_boxed_1400_, v_i_boxed_1401_, v_bs_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_);
lean_dec(v___y_1398_);
lean_dec_ref(v___y_1397_);
lean_dec(v___y_1396_);
lean_dec_ref(v___y_1395_);
return v_res_1402_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__1___redArg(lean_object* v_a_1403_, lean_object* v_b_1404_){
_start:
{
lean_object* v_array_1405_; lean_object* v_start_1406_; lean_object* v_stop_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1420_; 
v_array_1405_ = lean_ctor_get(v_a_1403_, 0);
v_start_1406_ = lean_ctor_get(v_a_1403_, 1);
v_stop_1407_ = lean_ctor_get(v_a_1403_, 2);
v_isSharedCheck_1420_ = !lean_is_exclusive(v_a_1403_);
if (v_isSharedCheck_1420_ == 0)
{
v___x_1409_ = v_a_1403_;
v_isShared_1410_ = v_isSharedCheck_1420_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_stop_1407_);
lean_inc(v_start_1406_);
lean_inc(v_array_1405_);
lean_dec(v_a_1403_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1420_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
uint8_t v___x_1411_; 
v___x_1411_ = lean_nat_dec_lt(v_start_1406_, v_stop_1407_);
if (v___x_1411_ == 0)
{
lean_del_object(v___x_1409_);
lean_dec(v_stop_1407_);
lean_dec(v_start_1406_);
lean_dec_ref(v_array_1405_);
return v_b_1404_;
}
else
{
lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1415_; 
v___x_1412_ = lean_unsigned_to_nat(1u);
v___x_1413_ = lean_nat_add(v_start_1406_, v___x_1412_);
lean_inc_ref(v_array_1405_);
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 1, v___x_1413_);
v___x_1415_ = v___x_1409_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v_array_1405_);
lean_ctor_set(v_reuseFailAlloc_1419_, 1, v___x_1413_);
lean_ctor_set(v_reuseFailAlloc_1419_, 2, v_stop_1407_);
v___x_1415_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
lean_object* v___x_1416_; lean_object* v___x_1417_; 
v___x_1416_ = lean_array_fget(v_array_1405_, v_start_1406_);
lean_dec(v_start_1406_);
lean_dec_ref(v_array_1405_);
v___x_1417_ = lean_array_push(v_b_1404_, v___x_1416_);
v_a_1403_ = v___x_1415_;
v_b_1404_ = v___x_1417_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19_spec__21___redArg___lam__0(lean_object* v_k_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v_b_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_){
_start:
{
lean_object* v___x_1432_; 
lean_inc(v___y_1430_);
lean_inc_ref(v___y_1429_);
lean_inc(v___y_1428_);
lean_inc_ref(v___y_1427_);
lean_inc(v___y_1425_);
lean_inc_ref(v___y_1424_);
lean_inc(v___y_1423_);
lean_inc_ref(v___y_1422_);
v___x_1432_ = lean_apply_10(v_k_1421_, v_b_1426_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_, lean_box(0));
return v___x_1432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19_spec__21___redArg___lam__0___boxed(lean_object* v_k_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v_b_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_){
_start:
{
lean_object* v_res_1444_; 
v_res_1444_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19_spec__21___redArg___lam__0(v_k_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v_b_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_);
lean_dec(v___y_1442_);
lean_dec_ref(v___y_1441_);
lean_dec(v___y_1440_);
lean_dec_ref(v___y_1439_);
lean_dec(v___y_1437_);
lean_dec_ref(v___y_1436_);
lean_dec(v___y_1435_);
lean_dec_ref(v___y_1434_);
return v_res_1444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19_spec__21___redArg(lean_object* v_name_1445_, uint8_t v_bi_1446_, lean_object* v_type_1447_, lean_object* v_k_1448_, uint8_t v_kind_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_){
_start:
{
lean_object* v___f_1459_; lean_object* v___x_1460_; 
lean_inc(v___y_1453_);
lean_inc_ref(v___y_1452_);
lean_inc(v___y_1451_);
lean_inc_ref(v___y_1450_);
v___f_1459_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19_spec__21___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_1459_, 0, v_k_1448_);
lean_closure_set(v___f_1459_, 1, v___y_1450_);
lean_closure_set(v___f_1459_, 2, v___y_1451_);
lean_closure_set(v___f_1459_, 3, v___y_1452_);
lean_closure_set(v___f_1459_, 4, v___y_1453_);
v___x_1460_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1445_, v_bi_1446_, v_type_1447_, v___f_1459_, v_kind_1449_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_);
if (lean_obj_tag(v___x_1460_) == 0)
{
return v___x_1460_;
}
else
{
lean_object* v_a_1461_; lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1468_; 
v_a_1461_ = lean_ctor_get(v___x_1460_, 0);
v_isSharedCheck_1468_ = !lean_is_exclusive(v___x_1460_);
if (v_isSharedCheck_1468_ == 0)
{
v___x_1463_ = v___x_1460_;
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
else
{
lean_inc(v_a_1461_);
lean_dec(v___x_1460_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19_spec__21___redArg___boxed(lean_object* v_name_1469_, lean_object* v_bi_1470_, lean_object* v_type_1471_, lean_object* v_k_1472_, lean_object* v_kind_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_){
_start:
{
uint8_t v_bi_boxed_1483_; uint8_t v_kind_boxed_1484_; lean_object* v_res_1485_; 
v_bi_boxed_1483_ = lean_unbox(v_bi_1470_);
v_kind_boxed_1484_ = lean_unbox(v_kind_1473_);
v_res_1485_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19_spec__21___redArg(v_name_1469_, v_bi_boxed_1483_, v_type_1471_, v_k_1472_, v_kind_boxed_1484_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_);
lean_dec(v___y_1481_);
lean_dec_ref(v___y_1480_);
lean_dec(v___y_1479_);
lean_dec_ref(v___y_1478_);
lean_dec(v___y_1477_);
lean_dec_ref(v___y_1476_);
lean_dec(v___y_1475_);
lean_dec_ref(v___y_1474_);
return v_res_1485_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___lam__0(lean_object* v___x_1486_, lean_object* v_a_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_){
_start:
{
lean_object* v___x_1497_; lean_object* v___x_19877__overap_1498_; lean_object* v___x_1499_; 
v___x_1497_ = l_Lean_instInhabitedExpr;
v___x_19877__overap_1498_ = l_instInhabitedOfMonad___redArg(v___x_1486_, v___x_1497_);
lean_inc(v___y_1495_);
lean_inc_ref(v___y_1494_);
lean_inc(v___y_1493_);
lean_inc_ref(v___y_1492_);
lean_inc(v___y_1491_);
lean_inc_ref(v___y_1490_);
lean_inc(v___y_1489_);
lean_inc_ref(v___y_1488_);
v___x_1499_ = lean_apply_9(v___x_19877__overap_1498_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, lean_box(0));
return v___x_1499_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___lam__0___boxed(lean_object* v___x_1500_, lean_object* v_a_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_){
_start:
{
lean_object* v_res_1511_; 
v_res_1511_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___lam__0(v___x_1500_, v_a_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_);
lean_dec(v___y_1509_);
lean_dec_ref(v___y_1508_);
lean_dec(v___y_1507_);
lean_dec_ref(v___y_1506_);
lean_dec(v___y_1505_);
lean_dec_ref(v___y_1504_);
lean_dec(v___y_1503_);
lean_dec_ref(v___y_1502_);
lean_dec_ref(v_a_1501_);
return v_res_1511_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___lam__1___boxed(lean_object* v_acc_1516_, lean_object* v_declInfos_1517_, lean_object* v_k_1518_, lean_object* v_kind_1519_, lean_object* v_x_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_){
_start:
{
uint8_t v_kind_boxed_1530_; lean_object* v_res_1531_; 
v_kind_boxed_1530_ = lean_unbox(v_kind_1519_);
v_res_1531_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___lam__1(v_acc_1516_, v_declInfos_1517_, v_k_1518_, v_kind_boxed_1530_, v_x_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_);
lean_dec(v___y_1528_);
lean_dec_ref(v___y_1527_);
lean_dec(v___y_1526_);
lean_dec_ref(v___y_1525_);
lean_dec(v___y_1524_);
lean_dec_ref(v___y_1523_);
lean_dec(v___y_1522_);
lean_dec_ref(v___y_1521_);
return v_res_1531_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19(lean_object* v_declInfos_1532_, lean_object* v_k_1533_, uint8_t v_kind_1534_, lean_object* v_acc_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_){
_start:
{
lean_object* v___x_1545_; lean_object* v_toApplicative_1546_; lean_object* v_toFunctor_1547_; lean_object* v_toSeq_1548_; lean_object* v_toSeqLeft_1549_; lean_object* v_toSeqRight_1550_; lean_object* v___f_1551_; lean_object* v___f_1552_; lean_object* v___f_1553_; lean_object* v___f_1554_; lean_object* v___x_1555_; lean_object* v___f_1556_; lean_object* v___f_1557_; lean_object* v___f_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v_toApplicative_1562_; lean_object* v___x_1564_; uint8_t v_isShared_1565_; uint8_t v_isSharedCheck_1679_; 
v___x_1545_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__1);
v_toApplicative_1546_ = lean_ctor_get(v___x_1545_, 0);
v_toFunctor_1547_ = lean_ctor_get(v_toApplicative_1546_, 0);
v_toSeq_1548_ = lean_ctor_get(v_toApplicative_1546_, 2);
v_toSeqLeft_1549_ = lean_ctor_get(v_toApplicative_1546_, 3);
v_toSeqRight_1550_ = lean_ctor_get(v_toApplicative_1546_, 4);
v___f_1551_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__2));
v___f_1552_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__3));
lean_inc_ref_n(v_toFunctor_1547_, 2);
v___f_1553_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1553_, 0, v_toFunctor_1547_);
v___f_1554_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1554_, 0, v_toFunctor_1547_);
v___x_1555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1555_, 0, v___f_1553_);
lean_ctor_set(v___x_1555_, 1, v___f_1554_);
lean_inc(v_toSeqRight_1550_);
v___f_1556_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1556_, 0, v_toSeqRight_1550_);
lean_inc(v_toSeqLeft_1549_);
v___f_1557_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1557_, 0, v_toSeqLeft_1549_);
lean_inc(v_toSeq_1548_);
v___f_1558_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1558_, 0, v_toSeq_1548_);
v___x_1559_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1559_, 0, v___x_1555_);
lean_ctor_set(v___x_1559_, 1, v___f_1551_);
lean_ctor_set(v___x_1559_, 2, v___f_1558_);
lean_ctor_set(v___x_1559_, 3, v___f_1557_);
lean_ctor_set(v___x_1559_, 4, v___f_1556_);
v___x_1560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1560_, 0, v___x_1559_);
lean_ctor_set(v___x_1560_, 1, v___f_1552_);
v___x_1561_ = l_StateRefT_x27_instMonad___redArg(v___x_1560_);
v_toApplicative_1562_ = lean_ctor_get(v___x_1561_, 0);
v_isSharedCheck_1679_ = !lean_is_exclusive(v___x_1561_);
if (v_isSharedCheck_1679_ == 0)
{
lean_object* v_unused_1680_; 
v_unused_1680_ = lean_ctor_get(v___x_1561_, 1);
lean_dec(v_unused_1680_);
v___x_1564_ = v___x_1561_;
v_isShared_1565_ = v_isSharedCheck_1679_;
goto v_resetjp_1563_;
}
else
{
lean_inc(v_toApplicative_1562_);
lean_dec(v___x_1561_);
v___x_1564_ = lean_box(0);
v_isShared_1565_ = v_isSharedCheck_1679_;
goto v_resetjp_1563_;
}
v_resetjp_1563_:
{
lean_object* v_toFunctor_1566_; lean_object* v_toSeq_1567_; lean_object* v_toSeqLeft_1568_; lean_object* v_toSeqRight_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1677_; 
v_toFunctor_1566_ = lean_ctor_get(v_toApplicative_1562_, 0);
v_toSeq_1567_ = lean_ctor_get(v_toApplicative_1562_, 2);
v_toSeqLeft_1568_ = lean_ctor_get(v_toApplicative_1562_, 3);
v_toSeqRight_1569_ = lean_ctor_get(v_toApplicative_1562_, 4);
v_isSharedCheck_1677_ = !lean_is_exclusive(v_toApplicative_1562_);
if (v_isSharedCheck_1677_ == 0)
{
lean_object* v_unused_1678_; 
v_unused_1678_ = lean_ctor_get(v_toApplicative_1562_, 1);
lean_dec(v_unused_1678_);
v___x_1571_ = v_toApplicative_1562_;
v_isShared_1572_ = v_isSharedCheck_1677_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_toSeqRight_1569_);
lean_inc(v_toSeqLeft_1568_);
lean_inc(v_toSeq_1567_);
lean_inc(v_toFunctor_1566_);
lean_dec(v_toApplicative_1562_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1677_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
lean_object* v___f_1573_; lean_object* v___f_1574_; lean_object* v___f_1575_; lean_object* v___f_1576_; lean_object* v___x_1577_; lean_object* v___f_1578_; lean_object* v___f_1579_; lean_object* v___f_1580_; lean_object* v___x_1582_; 
v___f_1573_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__4));
v___f_1574_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__5));
lean_inc_ref(v_toFunctor_1566_);
v___f_1575_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1575_, 0, v_toFunctor_1566_);
v___f_1576_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1576_, 0, v_toFunctor_1566_);
v___x_1577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1577_, 0, v___f_1575_);
lean_ctor_set(v___x_1577_, 1, v___f_1576_);
v___f_1578_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1578_, 0, v_toSeqRight_1569_);
v___f_1579_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1579_, 0, v_toSeqLeft_1568_);
v___f_1580_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1580_, 0, v_toSeq_1567_);
if (v_isShared_1572_ == 0)
{
lean_ctor_set(v___x_1571_, 4, v___f_1578_);
lean_ctor_set(v___x_1571_, 3, v___f_1579_);
lean_ctor_set(v___x_1571_, 2, v___f_1580_);
lean_ctor_set(v___x_1571_, 1, v___f_1573_);
lean_ctor_set(v___x_1571_, 0, v___x_1577_);
v___x_1582_ = v___x_1571_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v___x_1577_);
lean_ctor_set(v_reuseFailAlloc_1676_, 1, v___f_1573_);
lean_ctor_set(v_reuseFailAlloc_1676_, 2, v___f_1580_);
lean_ctor_set(v_reuseFailAlloc_1676_, 3, v___f_1579_);
lean_ctor_set(v_reuseFailAlloc_1676_, 4, v___f_1578_);
v___x_1582_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
lean_object* v___x_1584_; 
if (v_isShared_1565_ == 0)
{
lean_ctor_set(v___x_1564_, 1, v___f_1574_);
lean_ctor_set(v___x_1564_, 0, v___x_1582_);
v___x_1584_ = v___x_1564_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v___x_1582_);
lean_ctor_set(v_reuseFailAlloc_1675_, 1, v___f_1574_);
v___x_1584_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
lean_object* v___x_1585_; lean_object* v_toApplicative_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1673_; 
v___x_1585_ = l_StateRefT_x27_instMonad___redArg(v___x_1584_);
v_toApplicative_1586_ = lean_ctor_get(v___x_1585_, 0);
v_isSharedCheck_1673_ = !lean_is_exclusive(v___x_1585_);
if (v_isSharedCheck_1673_ == 0)
{
lean_object* v_unused_1674_; 
v_unused_1674_ = lean_ctor_get(v___x_1585_, 1);
lean_dec(v_unused_1674_);
v___x_1588_ = v___x_1585_;
v_isShared_1589_ = v_isSharedCheck_1673_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_toApplicative_1586_);
lean_dec(v___x_1585_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1673_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
lean_object* v_toFunctor_1590_; lean_object* v_toSeq_1591_; lean_object* v_toSeqLeft_1592_; lean_object* v_toSeqRight_1593_; lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1671_; 
v_toFunctor_1590_ = lean_ctor_get(v_toApplicative_1586_, 0);
v_toSeq_1591_ = lean_ctor_get(v_toApplicative_1586_, 2);
v_toSeqLeft_1592_ = lean_ctor_get(v_toApplicative_1586_, 3);
v_toSeqRight_1593_ = lean_ctor_get(v_toApplicative_1586_, 4);
v_isSharedCheck_1671_ = !lean_is_exclusive(v_toApplicative_1586_);
if (v_isSharedCheck_1671_ == 0)
{
lean_object* v_unused_1672_; 
v_unused_1672_ = lean_ctor_get(v_toApplicative_1586_, 1);
lean_dec(v_unused_1672_);
v___x_1595_ = v_toApplicative_1586_;
v_isShared_1596_ = v_isSharedCheck_1671_;
goto v_resetjp_1594_;
}
else
{
lean_inc(v_toSeqRight_1593_);
lean_inc(v_toSeqLeft_1592_);
lean_inc(v_toSeq_1591_);
lean_inc(v_toFunctor_1590_);
lean_dec(v_toApplicative_1586_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1671_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
lean_object* v___f_1597_; lean_object* v___f_1598_; lean_object* v___f_1599_; lean_object* v___f_1600_; lean_object* v___x_1601_; lean_object* v___f_1602_; lean_object* v___f_1603_; lean_object* v___f_1604_; lean_object* v___x_1606_; 
v___f_1597_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___closed__0));
v___f_1598_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___closed__1));
lean_inc_ref(v_toFunctor_1590_);
v___f_1599_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1599_, 0, v_toFunctor_1590_);
v___f_1600_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1600_, 0, v_toFunctor_1590_);
v___x_1601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1601_, 0, v___f_1599_);
lean_ctor_set(v___x_1601_, 1, v___f_1600_);
v___f_1602_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1602_, 0, v_toSeqRight_1593_);
v___f_1603_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1603_, 0, v_toSeqLeft_1592_);
v___f_1604_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1604_, 0, v_toSeq_1591_);
if (v_isShared_1596_ == 0)
{
lean_ctor_set(v___x_1595_, 4, v___f_1602_);
lean_ctor_set(v___x_1595_, 3, v___f_1603_);
lean_ctor_set(v___x_1595_, 2, v___f_1604_);
lean_ctor_set(v___x_1595_, 1, v___f_1597_);
lean_ctor_set(v___x_1595_, 0, v___x_1601_);
v___x_1606_ = v___x_1595_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v___x_1601_);
lean_ctor_set(v_reuseFailAlloc_1670_, 1, v___f_1597_);
lean_ctor_set(v_reuseFailAlloc_1670_, 2, v___f_1604_);
lean_ctor_set(v_reuseFailAlloc_1670_, 3, v___f_1603_);
lean_ctor_set(v_reuseFailAlloc_1670_, 4, v___f_1602_);
v___x_1606_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
lean_object* v___x_1608_; 
if (v_isShared_1589_ == 0)
{
lean_ctor_set(v___x_1588_, 1, v___f_1598_);
lean_ctor_set(v___x_1588_, 0, v___x_1606_);
v___x_1608_ = v___x_1588_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v___x_1606_);
lean_ctor_set(v_reuseFailAlloc_1669_, 1, v___f_1598_);
v___x_1608_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
lean_object* v___x_1609_; lean_object* v_toApplicative_1610_; lean_object* v___x_1612_; uint8_t v_isShared_1613_; uint8_t v_isSharedCheck_1667_; 
v___x_1609_ = l_StateRefT_x27_instMonad___redArg(v___x_1608_);
v_toApplicative_1610_ = lean_ctor_get(v___x_1609_, 0);
v_isSharedCheck_1667_ = !lean_is_exclusive(v___x_1609_);
if (v_isSharedCheck_1667_ == 0)
{
lean_object* v_unused_1668_; 
v_unused_1668_ = lean_ctor_get(v___x_1609_, 1);
lean_dec(v_unused_1668_);
v___x_1612_ = v___x_1609_;
v_isShared_1613_ = v_isSharedCheck_1667_;
goto v_resetjp_1611_;
}
else
{
lean_inc(v_toApplicative_1610_);
lean_dec(v___x_1609_);
v___x_1612_ = lean_box(0);
v_isShared_1613_ = v_isSharedCheck_1667_;
goto v_resetjp_1611_;
}
v_resetjp_1611_:
{
lean_object* v_toFunctor_1614_; lean_object* v_toSeq_1615_; lean_object* v_toSeqLeft_1616_; lean_object* v_toSeqRight_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1665_; 
v_toFunctor_1614_ = lean_ctor_get(v_toApplicative_1610_, 0);
v_toSeq_1615_ = lean_ctor_get(v_toApplicative_1610_, 2);
v_toSeqLeft_1616_ = lean_ctor_get(v_toApplicative_1610_, 3);
v_toSeqRight_1617_ = lean_ctor_get(v_toApplicative_1610_, 4);
v_isSharedCheck_1665_ = !lean_is_exclusive(v_toApplicative_1610_);
if (v_isSharedCheck_1665_ == 0)
{
lean_object* v_unused_1666_; 
v_unused_1666_ = lean_ctor_get(v_toApplicative_1610_, 1);
lean_dec(v_unused_1666_);
v___x_1619_ = v_toApplicative_1610_;
v_isShared_1620_ = v_isSharedCheck_1665_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_toSeqRight_1617_);
lean_inc(v_toSeqLeft_1616_);
lean_inc(v_toSeq_1615_);
lean_inc(v_toFunctor_1614_);
lean_dec(v_toApplicative_1610_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1665_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v___f_1621_; lean_object* v___f_1622_; lean_object* v___f_1623_; lean_object* v___f_1624_; lean_object* v___x_1625_; lean_object* v___f_1626_; lean_object* v___f_1627_; lean_object* v___f_1628_; lean_object* v___x_1630_; 
v___f_1621_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___closed__2));
v___f_1622_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___closed__3));
lean_inc_ref(v_toFunctor_1614_);
v___f_1623_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1623_, 0, v_toFunctor_1614_);
v___f_1624_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1624_, 0, v_toFunctor_1614_);
v___x_1625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1625_, 0, v___f_1623_);
lean_ctor_set(v___x_1625_, 1, v___f_1624_);
v___f_1626_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1626_, 0, v_toSeqRight_1617_);
v___f_1627_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1627_, 0, v_toSeqLeft_1616_);
v___f_1628_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1628_, 0, v_toSeq_1615_);
if (v_isShared_1620_ == 0)
{
lean_ctor_set(v___x_1619_, 4, v___f_1626_);
lean_ctor_set(v___x_1619_, 3, v___f_1627_);
lean_ctor_set(v___x_1619_, 2, v___f_1628_);
lean_ctor_set(v___x_1619_, 1, v___f_1621_);
lean_ctor_set(v___x_1619_, 0, v___x_1625_);
v___x_1630_ = v___x_1619_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v___x_1625_);
lean_ctor_set(v_reuseFailAlloc_1664_, 1, v___f_1621_);
lean_ctor_set(v_reuseFailAlloc_1664_, 2, v___f_1628_);
lean_ctor_set(v_reuseFailAlloc_1664_, 3, v___f_1627_);
lean_ctor_set(v_reuseFailAlloc_1664_, 4, v___f_1626_);
v___x_1630_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
lean_object* v___x_1632_; 
if (v_isShared_1613_ == 0)
{
lean_ctor_set(v___x_1612_, 1, v___f_1622_);
lean_ctor_set(v___x_1612_, 0, v___x_1630_);
v___x_1632_ = v___x_1612_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v___x_1630_);
lean_ctor_set(v_reuseFailAlloc_1663_, 1, v___f_1622_);
v___x_1632_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
lean_object* v___x_1633_; lean_object* v___x_1634_; uint8_t v___x_1635_; 
v___x_1633_ = lean_array_get_size(v_acc_1535_);
v___x_1634_ = lean_array_get_size(v_declInfos_1532_);
v___x_1635_ = lean_nat_dec_lt(v___x_1633_, v___x_1634_);
if (v___x_1635_ == 0)
{
lean_object* v___x_1636_; 
lean_dec_ref(v___x_1632_);
lean_dec_ref(v_declInfos_1532_);
lean_inc(v___y_1543_);
lean_inc_ref(v___y_1542_);
lean_inc(v___y_1541_);
lean_inc_ref(v___y_1540_);
lean_inc(v___y_1539_);
lean_inc_ref(v___y_1538_);
lean_inc(v___y_1537_);
lean_inc_ref(v___y_1536_);
v___x_1636_ = lean_apply_10(v_k_1533_, v_acc_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, lean_box(0));
return v___x_1636_;
}
else
{
lean_object* v___f_1637_; lean_object* v___x_1638_; uint8_t v___x_1639_; lean_object* v___f_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v_snd_1645_; lean_object* v_fst_1646_; lean_object* v_fst_1647_; lean_object* v_snd_1648_; lean_object* v___x_1649_; 
v___f_1637_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___lam__0___boxed), 11, 1);
lean_closure_set(v___f_1637_, 0, v___x_1632_);
v___x_1638_ = lean_box(0);
v___x_1639_ = 0;
v___f_1640_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1640_, 0, v___f_1637_);
v___x_1641_ = lean_box(v___x_1639_);
v___x_1642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1642_, 0, v___x_1641_);
lean_ctor_set(v___x_1642_, 1, v___f_1640_);
v___x_1643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1643_, 0, v___x_1638_);
lean_ctor_set(v___x_1643_, 1, v___x_1642_);
v___x_1644_ = lean_array_get(v___x_1643_, v_declInfos_1532_, v___x_1633_);
lean_dec_ref(v___x_1643_);
v_snd_1645_ = lean_ctor_get(v___x_1644_, 1);
lean_inc(v_snd_1645_);
v_fst_1646_ = lean_ctor_get(v___x_1644_, 0);
lean_inc(v_fst_1646_);
lean_dec(v___x_1644_);
v_fst_1647_ = lean_ctor_get(v_snd_1645_, 0);
lean_inc(v_fst_1647_);
v_snd_1648_ = lean_ctor_get(v_snd_1645_, 1);
lean_inc(v_snd_1648_);
lean_dec(v_snd_1645_);
lean_inc(v___y_1543_);
lean_inc_ref(v___y_1542_);
lean_inc(v___y_1541_);
lean_inc_ref(v___y_1540_);
lean_inc(v___y_1539_);
lean_inc_ref(v___y_1538_);
lean_inc(v___y_1537_);
lean_inc_ref(v___y_1536_);
lean_inc_ref(v_acc_1535_);
v___x_1649_ = lean_apply_10(v_snd_1648_, v_acc_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, lean_box(0));
if (lean_obj_tag(v___x_1649_) == 0)
{
lean_object* v_a_1650_; lean_object* v___x_1651_; lean_object* v___f_1652_; uint8_t v___x_1653_; lean_object* v___x_1654_; 
v_a_1650_ = lean_ctor_get(v___x_1649_, 0);
lean_inc(v_a_1650_);
lean_dec_ref(v___x_1649_);
v___x_1651_ = lean_box(v_kind_1534_);
v___f_1652_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___lam__1___boxed), 14, 4);
lean_closure_set(v___f_1652_, 0, v_acc_1535_);
lean_closure_set(v___f_1652_, 1, v_declInfos_1532_);
lean_closure_set(v___f_1652_, 2, v_k_1533_);
lean_closure_set(v___f_1652_, 3, v___x_1651_);
v___x_1653_ = lean_unbox(v_fst_1647_);
lean_dec(v_fst_1647_);
v___x_1654_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19_spec__21___redArg(v_fst_1646_, v___x_1653_, v_a_1650_, v___f_1652_, v_kind_1534_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_);
return v___x_1654_;
}
else
{
lean_object* v_a_1655_; lean_object* v___x_1657_; uint8_t v_isShared_1658_; uint8_t v_isSharedCheck_1662_; 
lean_dec(v_fst_1647_);
lean_dec(v_fst_1646_);
lean_dec_ref(v_acc_1535_);
lean_dec_ref(v_k_1533_);
lean_dec_ref(v_declInfos_1532_);
v_a_1655_ = lean_ctor_get(v___x_1649_, 0);
v_isSharedCheck_1662_ = !lean_is_exclusive(v___x_1649_);
if (v_isSharedCheck_1662_ == 0)
{
v___x_1657_ = v___x_1649_;
v_isShared_1658_ = v_isSharedCheck_1662_;
goto v_resetjp_1656_;
}
else
{
lean_inc(v_a_1655_);
lean_dec(v___x_1649_);
v___x_1657_ = lean_box(0);
v_isShared_1658_ = v_isSharedCheck_1662_;
goto v_resetjp_1656_;
}
v_resetjp_1656_:
{
lean_object* v___x_1660_; 
if (v_isShared_1658_ == 0)
{
v___x_1660_ = v___x_1657_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v_a_1655_);
v___x_1660_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1659_;
}
v_reusejp_1659_:
{
return v___x_1660_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___lam__1(lean_object* v_acc_1681_, lean_object* v_declInfos_1682_, lean_object* v_k_1683_, uint8_t v_kind_1684_, lean_object* v_x_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_){
_start:
{
lean_object* v___x_1695_; lean_object* v___x_1696_; 
v___x_1695_ = lean_array_push(v_acc_1681_, v_x_1685_);
v___x_1696_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19(v_declInfos_1682_, v_k_1683_, v_kind_1684_, v___x_1695_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_);
return v___x_1696_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19___boxed(lean_object* v_declInfos_1697_, lean_object* v_k_1698_, lean_object* v_kind_1699_, lean_object* v_acc_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_){
_start:
{
uint8_t v_kind_boxed_1710_; lean_object* v_res_1711_; 
v_kind_boxed_1710_ = lean_unbox(v_kind_1699_);
v_res_1711_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19(v_declInfos_1697_, v_k_1698_, v_kind_boxed_1710_, v_acc_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_);
lean_dec(v___y_1708_);
lean_dec_ref(v___y_1707_);
lean_dec(v___y_1706_);
lean_dec_ref(v___y_1705_);
lean_dec(v___y_1704_);
lean_dec_ref(v___y_1703_);
lean_dec(v___y_1702_);
lean_dec_ref(v___y_1701_);
return v_res_1711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14(lean_object* v_declInfos_1712_, lean_object* v_k_1713_, uint8_t v_kind_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_){
_start:
{
lean_object* v___x_1724_; lean_object* v___x_1725_; 
v___x_1724_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__1));
v___x_1725_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19(v_declInfos_1712_, v_k_1713_, v_kind_1714_, v___x_1724_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_);
return v___x_1725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14___boxed(lean_object* v_declInfos_1726_, lean_object* v_k_1727_, lean_object* v_kind_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_){
_start:
{
uint8_t v_kind_boxed_1738_; lean_object* v_res_1739_; 
v_kind_boxed_1738_ = lean_unbox(v_kind_1728_);
v_res_1739_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14(v_declInfos_1726_, v_k_1727_, v_kind_boxed_1738_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_);
lean_dec(v___y_1736_);
lean_dec_ref(v___y_1735_);
lean_dec(v___y_1734_);
lean_dec_ref(v___y_1733_);
lean_dec(v___y_1732_);
lean_dec_ref(v___y_1731_);
lean_dec(v___y_1730_);
lean_dec_ref(v___y_1729_);
return v_res_1739_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__13(size_t v_sz_1740_, size_t v_i_1741_, lean_object* v_bs_1742_){
_start:
{
uint8_t v___x_1743_; 
v___x_1743_ = lean_usize_dec_lt(v_i_1741_, v_sz_1740_);
if (v___x_1743_ == 0)
{
return v_bs_1742_;
}
else
{
lean_object* v_v_1744_; lean_object* v_fst_1745_; lean_object* v_snd_1746_; lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1762_; 
v_v_1744_ = lean_array_uget(v_bs_1742_, v_i_1741_);
v_fst_1745_ = lean_ctor_get(v_v_1744_, 0);
v_snd_1746_ = lean_ctor_get(v_v_1744_, 1);
v_isSharedCheck_1762_ = !lean_is_exclusive(v_v_1744_);
if (v_isSharedCheck_1762_ == 0)
{
v___x_1748_ = v_v_1744_;
v_isShared_1749_ = v_isSharedCheck_1762_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_snd_1746_);
lean_inc(v_fst_1745_);
lean_dec(v_v_1744_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1762_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
lean_object* v___x_1750_; lean_object* v_bs_x27_1751_; uint8_t v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1755_; 
v___x_1750_ = lean_unsigned_to_nat(0u);
v_bs_x27_1751_ = lean_array_uset(v_bs_1742_, v_i_1741_, v___x_1750_);
v___x_1752_ = 0;
v___x_1753_ = lean_box(v___x_1752_);
if (v_isShared_1749_ == 0)
{
lean_ctor_set(v___x_1748_, 0, v___x_1753_);
v___x_1755_ = v___x_1748_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v___x_1753_);
lean_ctor_set(v_reuseFailAlloc_1761_, 1, v_snd_1746_);
v___x_1755_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1754_;
}
v_reusejp_1754_:
{
lean_object* v___x_1756_; size_t v___x_1757_; size_t v___x_1758_; lean_object* v___x_1759_; 
v___x_1756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1756_, 0, v_fst_1745_);
lean_ctor_set(v___x_1756_, 1, v___x_1755_);
v___x_1757_ = ((size_t)1ULL);
v___x_1758_ = lean_usize_add(v_i_1741_, v___x_1757_);
v___x_1759_ = lean_array_uset(v_bs_x27_1751_, v_i_1741_, v___x_1756_);
v_i_1741_ = v___x_1758_;
v_bs_1742_ = v___x_1759_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__13___boxed(lean_object* v_sz_1763_, lean_object* v_i_1764_, lean_object* v_bs_1765_){
_start:
{
size_t v_sz_boxed_1766_; size_t v_i_boxed_1767_; lean_object* v_res_1768_; 
v_sz_boxed_1766_ = lean_unbox_usize(v_sz_1763_);
lean_dec(v_sz_1763_);
v_i_boxed_1767_ = lean_unbox_usize(v_i_1764_);
lean_dec(v_i_1764_);
v_res_1768_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__13(v_sz_boxed_1766_, v_i_boxed_1767_, v_bs_1765_);
return v_res_1768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9(lean_object* v_declInfos_1769_, lean_object* v_k_1770_, uint8_t v_kind_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_){
_start:
{
size_t v_sz_1781_; size_t v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; 
v_sz_1781_ = lean_array_size(v_declInfos_1769_);
v___x_1782_ = ((size_t)0ULL);
v___x_1783_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__13(v_sz_1781_, v___x_1782_, v_declInfos_1769_);
v___x_1784_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14(v___x_1783_, v_k_1770_, v_kind_1771_, v___y_1772_, v___y_1773_, v___y_1774_, v___y_1775_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_);
return v___x_1784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9___boxed(lean_object* v_declInfos_1785_, lean_object* v_k_1786_, lean_object* v_kind_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_){
_start:
{
uint8_t v_kind_boxed_1797_; lean_object* v_res_1798_; 
v_kind_boxed_1797_ = lean_unbox(v_kind_1787_);
v_res_1798_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9(v_declInfos_1785_, v_k_1786_, v_kind_boxed_1797_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_);
lean_dec(v___y_1795_);
lean_dec_ref(v___y_1794_);
lean_dec(v___y_1793_);
lean_dec_ref(v___y_1792_);
lean_dec(v___y_1791_);
lean_dec_ref(v___y_1790_);
lean_dec(v___y_1789_);
lean_dec_ref(v___y_1788_);
return v_res_1798_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8___lam__0(lean_object* v_snd_1799_, lean_object* v_x_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_){
_start:
{
lean_object* v___x_1810_; 
v___x_1810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1810_, 0, v_snd_1799_);
return v___x_1810_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8___lam__0___boxed(lean_object* v_snd_1811_, lean_object* v_x_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_){
_start:
{
lean_object* v_res_1822_; 
v_res_1822_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8___lam__0(v_snd_1811_, v_x_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_);
lean_dec(v___y_1820_);
lean_dec_ref(v___y_1819_);
lean_dec(v___y_1818_);
lean_dec_ref(v___y_1817_);
lean_dec(v___y_1816_);
lean_dec_ref(v___y_1815_);
lean_dec(v___y_1814_);
lean_dec_ref(v___y_1813_);
lean_dec_ref(v_x_1812_);
return v_res_1822_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8(size_t v_sz_1823_, size_t v_i_1824_, lean_object* v_bs_1825_){
_start:
{
uint8_t v___x_1826_; 
v___x_1826_ = lean_usize_dec_lt(v_i_1824_, v_sz_1823_);
if (v___x_1826_ == 0)
{
return v_bs_1825_;
}
else
{
lean_object* v_v_1827_; lean_object* v_fst_1828_; lean_object* v_snd_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1843_; 
v_v_1827_ = lean_array_uget(v_bs_1825_, v_i_1824_);
v_fst_1828_ = lean_ctor_get(v_v_1827_, 0);
v_snd_1829_ = lean_ctor_get(v_v_1827_, 1);
v_isSharedCheck_1843_ = !lean_is_exclusive(v_v_1827_);
if (v_isSharedCheck_1843_ == 0)
{
v___x_1831_ = v_v_1827_;
v_isShared_1832_ = v_isSharedCheck_1843_;
goto v_resetjp_1830_;
}
else
{
lean_inc(v_snd_1829_);
lean_inc(v_fst_1828_);
lean_dec(v_v_1827_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1843_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v___x_1833_; lean_object* v_bs_x27_1834_; lean_object* v___f_1835_; lean_object* v___x_1837_; 
v___x_1833_ = lean_unsigned_to_nat(0u);
v_bs_x27_1834_ = lean_array_uset(v_bs_1825_, v_i_1824_, v___x_1833_);
v___f_1835_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8___lam__0___boxed), 11, 1);
lean_closure_set(v___f_1835_, 0, v_snd_1829_);
if (v_isShared_1832_ == 0)
{
lean_ctor_set(v___x_1831_, 1, v___f_1835_);
v___x_1837_ = v___x_1831_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v_fst_1828_);
lean_ctor_set(v_reuseFailAlloc_1842_, 1, v___f_1835_);
v___x_1837_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
size_t v___x_1838_; size_t v___x_1839_; lean_object* v___x_1840_; 
v___x_1838_ = ((size_t)1ULL);
v___x_1839_ = lean_usize_add(v_i_1824_, v___x_1838_);
v___x_1840_ = lean_array_uset(v_bs_x27_1834_, v_i_1824_, v___x_1837_);
v_i_1824_ = v___x_1839_;
v_bs_1825_ = v___x_1840_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8___boxed(lean_object* v_sz_1844_, lean_object* v_i_1845_, lean_object* v_bs_1846_){
_start:
{
size_t v_sz_boxed_1847_; size_t v_i_boxed_1848_; lean_object* v_res_1849_; 
v_sz_boxed_1847_ = lean_unbox_usize(v_sz_1844_);
lean_dec(v_sz_1844_);
v_i_boxed_1848_ = lean_unbox_usize(v_i_1845_);
lean_dec(v_i_1845_);
v_res_1849_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8(v_sz_boxed_1847_, v_i_boxed_1848_, v_bs_1846_);
return v_res_1849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5(lean_object* v_declInfos_1850_, lean_object* v_k_1851_, uint8_t v_kind_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_){
_start:
{
size_t v_sz_1862_; size_t v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; 
v_sz_1862_ = lean_array_size(v_declInfos_1850_);
v___x_1863_ = ((size_t)0ULL);
v___x_1864_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8(v_sz_1862_, v___x_1863_, v_declInfos_1850_);
v___x_1865_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9(v___x_1864_, v_k_1851_, v_kind_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_);
return v___x_1865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5___boxed(lean_object* v_declInfos_1866_, lean_object* v_k_1867_, lean_object* v_kind_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_){
_start:
{
uint8_t v_kind_boxed_1878_; lean_object* v_res_1879_; 
v_kind_boxed_1878_ = lean_unbox(v_kind_1868_);
v_res_1879_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5(v_declInfos_1866_, v_k_1867_, v_kind_boxed_1878_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_);
lean_dec(v___y_1876_);
lean_dec_ref(v___y_1875_);
lean_dec(v___y_1874_);
lean_dec_ref(v___y_1873_);
lean_dec(v___y_1872_);
lean_dec_ref(v___y_1871_);
lean_dec(v___y_1870_);
lean_dec_ref(v___y_1869_);
return v_res_1879_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__3(size_t v_sz_1880_, size_t v_i_1881_, lean_object* v_bs_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_){
_start:
{
uint8_t v___x_1888_; 
v___x_1888_ = lean_usize_dec_lt(v_i_1881_, v_sz_1880_);
if (v___x_1888_ == 0)
{
lean_object* v___x_1889_; 
v___x_1889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1889_, 0, v_bs_1882_);
return v___x_1889_;
}
else
{
lean_object* v_v_1890_; lean_object* v___x_1891_; 
v_v_1890_ = lean_array_uget_borrowed(v_bs_1882_, v_i_1881_);
lean_inc(v___y_1886_);
lean_inc_ref(v___y_1885_);
lean_inc(v___y_1884_);
lean_inc_ref(v___y_1883_);
lean_inc(v_v_1890_);
v___x_1891_ = lean_infer_type(v_v_1890_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_);
if (lean_obj_tag(v___x_1891_) == 0)
{
lean_object* v_a_1892_; lean_object* v___x_1893_; lean_object* v_bs_x27_1894_; size_t v___x_1895_; size_t v___x_1896_; lean_object* v___x_1897_; 
v_a_1892_ = lean_ctor_get(v___x_1891_, 0);
lean_inc(v_a_1892_);
lean_dec_ref(v___x_1891_);
v___x_1893_ = lean_unsigned_to_nat(0u);
v_bs_x27_1894_ = lean_array_uset(v_bs_1882_, v_i_1881_, v___x_1893_);
v___x_1895_ = ((size_t)1ULL);
v___x_1896_ = lean_usize_add(v_i_1881_, v___x_1895_);
v___x_1897_ = lean_array_uset(v_bs_x27_1894_, v_i_1881_, v_a_1892_);
v_i_1881_ = v___x_1896_;
v_bs_1882_ = v___x_1897_;
goto _start;
}
else
{
lean_object* v_a_1899_; lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_1906_; 
lean_dec_ref(v_bs_1882_);
v_a_1899_ = lean_ctor_get(v___x_1891_, 0);
v_isSharedCheck_1906_ = !lean_is_exclusive(v___x_1891_);
if (v_isSharedCheck_1906_ == 0)
{
v___x_1901_ = v___x_1891_;
v_isShared_1902_ = v_isSharedCheck_1906_;
goto v_resetjp_1900_;
}
else
{
lean_inc(v_a_1899_);
lean_dec(v___x_1891_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__3___boxed(lean_object* v_sz_1907_, lean_object* v_i_1908_, lean_object* v_bs_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_){
_start:
{
size_t v_sz_boxed_1915_; size_t v_i_boxed_1916_; lean_object* v_res_1917_; 
v_sz_boxed_1915_ = lean_unbox_usize(v_sz_1907_);
lean_dec(v_sz_1907_);
v_i_boxed_1916_ = lean_unbox_usize(v_i_1908_);
lean_dec(v_i_1908_);
v_res_1917_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__3(v_sz_boxed_1915_, v_i_boxed_1916_, v_bs_1909_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_);
lean_dec(v___y_1913_);
lean_dec_ref(v___y_1912_);
lean_dec(v___y_1911_);
lean_dec_ref(v___y_1910_);
return v_res_1917_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__2___redArg(size_t v_sz_1918_, size_t v_i_1919_, lean_object* v_bs_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_){
_start:
{
uint8_t v___x_1926_; 
v___x_1926_ = lean_usize_dec_lt(v_i_1919_, v_sz_1918_);
if (v___x_1926_ == 0)
{
lean_object* v___x_1927_; 
v___x_1927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1927_, 0, v_bs_1920_);
return v___x_1927_;
}
else
{
lean_object* v_v_1928_; lean_object* v_fst_1929_; lean_object* v_snd_1930_; lean_object* v___x_1931_; 
v_v_1928_ = lean_array_uget_borrowed(v_bs_1920_, v_i_1919_);
v_fst_1929_ = lean_ctor_get(v_v_1928_, 0);
v_snd_1930_ = lean_ctor_get(v_v_1928_, 1);
lean_inc(v_fst_1929_);
lean_inc(v_snd_1930_);
v___x_1931_ = l_Lean_Meta_mkEq(v_snd_1930_, v_fst_1929_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_);
if (lean_obj_tag(v___x_1931_) == 0)
{
lean_object* v_a_1932_; lean_object* v___x_1933_; lean_object* v_bs_x27_1934_; size_t v___x_1935_; size_t v___x_1936_; lean_object* v___x_1937_; 
v_a_1932_ = lean_ctor_get(v___x_1931_, 0);
lean_inc(v_a_1932_);
lean_dec_ref(v___x_1931_);
v___x_1933_ = lean_unsigned_to_nat(0u);
v_bs_x27_1934_ = lean_array_uset(v_bs_1920_, v_i_1919_, v___x_1933_);
v___x_1935_ = ((size_t)1ULL);
v___x_1936_ = lean_usize_add(v_i_1919_, v___x_1935_);
v___x_1937_ = lean_array_uset(v_bs_x27_1934_, v_i_1919_, v_a_1932_);
v_i_1919_ = v___x_1936_;
v_bs_1920_ = v___x_1937_;
goto _start;
}
else
{
lean_object* v_a_1939_; lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_1946_; 
lean_dec_ref(v_bs_1920_);
v_a_1939_ = lean_ctor_get(v___x_1931_, 0);
v_isSharedCheck_1946_ = !lean_is_exclusive(v___x_1931_);
if (v_isSharedCheck_1946_ == 0)
{
v___x_1941_ = v___x_1931_;
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
else
{
lean_inc(v_a_1939_);
lean_dec(v___x_1931_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__2___redArg___boxed(lean_object* v_sz_1947_, lean_object* v_i_1948_, lean_object* v_bs_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_){
_start:
{
size_t v_sz_boxed_1955_; size_t v_i_boxed_1956_; lean_object* v_res_1957_; 
v_sz_boxed_1955_ = lean_unbox_usize(v_sz_1947_);
lean_dec(v_sz_1947_);
v_i_boxed_1956_ = lean_unbox_usize(v_i_1948_);
lean_dec(v_i_1948_);
v_res_1957_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__2___redArg(v_sz_boxed_1955_, v_i_boxed_1956_, v_bs_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_);
lean_dec(v___y_1953_);
lean_dec_ref(v___y_1952_);
lean_dec(v___y_1951_);
lean_dec_ref(v___y_1950_);
return v_res_1957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1___lam__0(lean_object* v_revertArgs_1958_, lean_object* v_hypName_1959_, lean_object* v_u_1960_, lean_object* v_00_u03c3s_1961_, uint8_t v___x_1962_, lean_object* v_hyps_1963_, lean_object* v_ss_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_){
_start:
{
lean_object* v___x_1974_; size_t v_sz_1975_; size_t v___x_1976_; lean_object* v___x_1977_; 
v___x_1974_ = l_Array_zip___redArg(v_revertArgs_1958_, v_ss_1964_);
v_sz_1975_ = lean_array_size(v___x_1974_);
v___x_1976_ = ((size_t)0ULL);
v___x_1977_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__2___redArg(v_sz_1975_, v___x_1976_, v___x_1974_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_);
if (lean_obj_tag(v___x_1977_) == 0)
{
lean_object* v_a_1978_; lean_object* v___x_1979_; 
v_a_1978_ = lean_ctor_get(v___x_1977_, 0);
lean_inc(v_a_1978_);
lean_dec_ref(v___x_1977_);
lean_inc(v_hypName_1959_);
v___x_1979_ = l_Lean_Core_mkFreshUserName(v_hypName_1959_, v___y_1971_, v___y_1972_);
if (lean_obj_tag(v___x_1979_) == 0)
{
lean_object* v_a_1980_; lean_object* v_eqs_1981_; lean_object* v_00_u03c6_1982_; lean_object* v_00_u03c6_1983_; uint8_t v___x_1984_; uint8_t v___x_1985_; lean_object* v___x_1986_; 
v_a_1980_ = lean_ctor_get(v___x_1979_, 0);
lean_inc(v_a_1980_);
lean_dec_ref(v___x_1979_);
v_eqs_1981_ = lean_array_to_list(v_a_1978_);
v_00_u03c6_1982_ = l_Lean_mkAndN(v_eqs_1981_);
v_00_u03c6_1983_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure(v_u_1960_, v_00_u03c3s_1961_, v_00_u03c6_1982_);
v___x_1984_ = 1;
v___x_1985_ = 1;
v___x_1986_ = l_Lean_Meta_mkLambdaFVars(v_ss_1964_, v_00_u03c6_1983_, v___x_1962_, v___x_1984_, v___x_1962_, v___x_1984_, v___x_1985_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_);
if (lean_obj_tag(v___x_1986_) == 0)
{
lean_object* v_a_1987_; lean_object* v___x_1988_; 
v_a_1987_ = lean_ctor_get(v___x_1986_, 0);
lean_inc(v_a_1987_);
lean_dec_ref(v___x_1986_);
v___x_1988_ = l_Lean_Meta_mkLambdaFVars(v_ss_1964_, v_hyps_1963_, v___x_1962_, v___x_1984_, v___x_1962_, v___x_1984_, v___x_1985_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_);
if (lean_obj_tag(v___x_1988_) == 0)
{
lean_object* v_a_1989_; lean_object* v___x_1991_; uint8_t v_isShared_1992_; uint8_t v_isSharedCheck_1999_; 
v_a_1989_ = lean_ctor_get(v___x_1988_, 0);
v_isSharedCheck_1999_ = !lean_is_exclusive(v___x_1988_);
if (v_isSharedCheck_1999_ == 0)
{
v___x_1991_ = v___x_1988_;
v_isShared_1992_ = v_isSharedCheck_1999_;
goto v_resetjp_1990_;
}
else
{
lean_inc(v_a_1989_);
lean_dec(v___x_1988_);
v___x_1991_ = lean_box(0);
v_isShared_1992_ = v_isSharedCheck_1999_;
goto v_resetjp_1990_;
}
v_resetjp_1990_:
{
lean_object* v___x_1993_; lean_object* v_00_u03c6_1994_; lean_object* v___x_1995_; lean_object* v___x_1997_; 
v___x_1993_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1993_, 0, v_hypName_1959_);
lean_ctor_set(v___x_1993_, 1, v_a_1980_);
lean_ctor_set(v___x_1993_, 2, v_a_1987_);
v_00_u03c6_1994_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_1993_);
v___x_1995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1995_, 0, v_a_1989_);
lean_ctor_set(v___x_1995_, 1, v_00_u03c6_1994_);
if (v_isShared_1992_ == 0)
{
lean_ctor_set(v___x_1991_, 0, v___x_1995_);
v___x_1997_ = v___x_1991_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v___x_1995_);
v___x_1997_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
return v___x_1997_;
}
}
}
else
{
lean_object* v_a_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2007_; 
lean_dec(v_a_1987_);
lean_dec(v_a_1980_);
lean_dec(v_hypName_1959_);
v_a_2000_ = lean_ctor_get(v___x_1988_, 0);
v_isSharedCheck_2007_ = !lean_is_exclusive(v___x_1988_);
if (v_isSharedCheck_2007_ == 0)
{
v___x_2002_ = v___x_1988_;
v_isShared_2003_ = v_isSharedCheck_2007_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_a_2000_);
lean_dec(v___x_1988_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2007_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
lean_object* v___x_2005_; 
if (v_isShared_2003_ == 0)
{
v___x_2005_ = v___x_2002_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v_a_2000_);
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
lean_object* v_a_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2015_; 
lean_dec(v_a_1980_);
lean_dec_ref(v_hyps_1963_);
lean_dec(v_hypName_1959_);
v_a_2008_ = lean_ctor_get(v___x_1986_, 0);
v_isSharedCheck_2015_ = !lean_is_exclusive(v___x_1986_);
if (v_isSharedCheck_2015_ == 0)
{
v___x_2010_ = v___x_1986_;
v_isShared_2011_ = v_isSharedCheck_2015_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_a_2008_);
lean_dec(v___x_1986_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2015_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v___x_2013_; 
if (v_isShared_2011_ == 0)
{
v___x_2013_ = v___x_2010_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v_a_2008_);
v___x_2013_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
return v___x_2013_;
}
}
}
}
else
{
lean_object* v_a_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2023_; 
lean_dec(v_a_1978_);
lean_dec_ref(v_hyps_1963_);
lean_dec_ref(v_00_u03c3s_1961_);
lean_dec(v_u_1960_);
lean_dec(v_hypName_1959_);
v_a_2016_ = lean_ctor_get(v___x_1979_, 0);
v_isSharedCheck_2023_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_2023_ == 0)
{
v___x_2018_ = v___x_1979_;
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_a_2016_);
lean_dec(v___x_1979_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
lean_object* v___x_2021_; 
if (v_isShared_2019_ == 0)
{
v___x_2021_ = v___x_2018_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v_a_2016_);
v___x_2021_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
return v___x_2021_;
}
}
}
}
else
{
lean_object* v_a_2024_; lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2031_; 
lean_dec_ref(v_hyps_1963_);
lean_dec_ref(v_00_u03c3s_1961_);
lean_dec(v_u_1960_);
lean_dec(v_hypName_1959_);
v_a_2024_ = lean_ctor_get(v___x_1977_, 0);
v_isSharedCheck_2031_ = !lean_is_exclusive(v___x_1977_);
if (v_isSharedCheck_2031_ == 0)
{
v___x_2026_ = v___x_1977_;
v_isShared_2027_ = v_isSharedCheck_2031_;
goto v_resetjp_2025_;
}
else
{
lean_inc(v_a_2024_);
lean_dec(v___x_1977_);
v___x_2026_ = lean_box(0);
v_isShared_2027_ = v_isSharedCheck_2031_;
goto v_resetjp_2025_;
}
v_resetjp_2025_:
{
lean_object* v___x_2029_; 
if (v_isShared_2027_ == 0)
{
v___x_2029_ = v___x_2026_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2030_; 
v_reuseFailAlloc_2030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2030_, 0, v_a_2024_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1___lam__0___boxed(lean_object* v_revertArgs_2032_, lean_object* v_hypName_2033_, lean_object* v_u_2034_, lean_object* v_00_u03c3s_2035_, lean_object* v___x_2036_, lean_object* v_hyps_2037_, lean_object* v_ss_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_){
_start:
{
uint8_t v___x_21460__boxed_2048_; lean_object* v_res_2049_; 
v___x_21460__boxed_2048_ = lean_unbox(v___x_2036_);
v_res_2049_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1___lam__0(v_revertArgs_2032_, v_hypName_2033_, v_u_2034_, v_00_u03c3s_2035_, v___x_21460__boxed_2048_, v_hyps_2037_, v_ss_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_);
lean_dec(v___y_2046_);
lean_dec_ref(v___y_2045_);
lean_dec(v___y_2044_);
lean_dec_ref(v___y_2043_);
lean_dec(v___y_2042_);
lean_dec_ref(v___y_2041_);
lean_dec(v___y_2040_);
lean_dec_ref(v___y_2039_);
lean_dec_ref(v_ss_2038_);
lean_dec_ref(v_revertArgs_2032_);
return v_res_2049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1(lean_object* v_goal_2050_, lean_object* v_n_2051_, lean_object* v_hypName_2052_, lean_object* v_k_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_){
_start:
{
lean_object* v___x_2063_; uint8_t v___x_2064_; 
v___x_2063_ = lean_unsigned_to_nat(0u);
v___x_2064_ = lean_nat_dec_eq(v_n_2051_, v___x_2063_);
if (v___x_2064_ == 0)
{
lean_object* v_u_2065_; lean_object* v_00_u03c3s_2066_; lean_object* v_hyps_2067_; lean_object* v_target_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2222_; 
v_u_2065_ = lean_ctor_get(v_goal_2050_, 0);
v_00_u03c3s_2066_ = lean_ctor_get(v_goal_2050_, 1);
v_hyps_2067_ = lean_ctor_get(v_goal_2050_, 2);
v_target_2068_ = lean_ctor_get(v_goal_2050_, 3);
v_isSharedCheck_2222_ = !lean_is_exclusive(v_goal_2050_);
if (v_isSharedCheck_2222_ == 0)
{
v___x_2070_ = v_goal_2050_;
v_isShared_2071_ = v_isSharedCheck_2222_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_target_2068_);
lean_inc(v_hyps_2067_);
lean_inc(v_00_u03c3s_2066_);
lean_inc(v_u_2065_);
lean_dec(v_goal_2050_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2222_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
lean_object* v_T_2072_; lean_object* v_f_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v_a_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v_revertArgs_2080_; lean_object* v___y_2082_; lean_object* v___y_2083_; lean_object* v___y_2084_; lean_object* v___y_2085_; lean_object* v___y_2086_; lean_object* v___y_2087_; lean_object* v___y_2088_; lean_object* v___y_2089_; lean_object* v___y_2090_; lean_object* v___y_2091_; lean_object* v___y_2092_; lean_object* v___y_2093_; lean_object* v___x_2132_; lean_object* v___f_2133_; lean_object* v___y_2135_; lean_object* v___y_2136_; lean_object* v___y_2137_; lean_object* v___y_2138_; lean_object* v___y_2139_; lean_object* v___y_2140_; lean_object* v___y_2141_; lean_object* v___y_2142_; lean_object* v___x_2196_; uint8_t v___x_2197_; 
v_T_2072_ = l_Lean_Expr_consumeMData(v_target_2068_);
v_f_2073_ = l_Lean_Expr_getAppFn(v_T_2072_);
v___x_2074_ = l_Lean_Expr_getAppNumArgs(v_T_2072_);
v___x_2075_ = lean_mk_empty_array_with_capacity(v___x_2074_);
lean_dec(v___x_2074_);
lean_inc_ref(v_T_2072_);
v_a_2076_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_T_2072_, v___x_2075_);
lean_inc(v_n_2051_);
lean_inc_ref(v_a_2076_);
v___x_2077_ = l_Array_toSubarray___redArg(v_a_2076_, v___x_2063_, v_n_2051_);
v___x_2078_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__1));
v___x_2079_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__1___redArg(v___x_2077_, v___x_2078_);
v_revertArgs_2080_ = l_Array_reverse___redArg(v___x_2079_);
v___x_2132_ = lean_box(v___x_2064_);
lean_inc_ref(v_hyps_2067_);
lean_inc_ref(v_00_u03c3s_2066_);
lean_inc(v_u_2065_);
lean_inc_ref(v_revertArgs_2080_);
v___f_2133_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1___lam__0___boxed), 16, 6);
lean_closure_set(v___f_2133_, 0, v_revertArgs_2080_);
lean_closure_set(v___f_2133_, 1, v_hypName_2052_);
lean_closure_set(v___f_2133_, 2, v_u_2065_);
lean_closure_set(v___f_2133_, 3, v_00_u03c3s_2066_);
lean_closure_set(v___f_2133_, 4, v___x_2132_);
lean_closure_set(v___f_2133_, 5, v_hyps_2067_);
v___x_2196_ = lean_array_get_size(v_revertArgs_2080_);
v___x_2197_ = lean_nat_dec_eq(v___x_2196_, v_n_2051_);
if (v___x_2197_ == 0)
{
lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v_a_2214_; lean_object* v___x_2216_; uint8_t v_isShared_2217_; uint8_t v_isSharedCheck_2221_; 
lean_dec_ref(v___f_2133_);
lean_dec_ref(v_revertArgs_2080_);
lean_dec_ref(v_a_2076_);
lean_dec_ref(v_f_2073_);
lean_del_object(v___x_2070_);
lean_dec_ref(v_target_2068_);
lean_dec_ref(v_hyps_2067_);
lean_dec_ref(v_00_u03c3s_2066_);
lean_dec(v_u_2065_);
lean_dec_ref(v_k_2053_);
v___x_2198_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__15, &l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__15_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__15);
v___x_2199_ = l_Nat_reprFast(v_n_2051_);
v___x_2200_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2200_, 0, v___x_2199_);
v___x_2201_ = l_Lean_MessageData_ofFormat(v___x_2200_);
v___x_2202_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2202_, 0, v___x_2198_);
lean_ctor_set(v___x_2202_, 1, v___x_2201_);
v___x_2203_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__17, &l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__17_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__17);
v___x_2204_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2204_, 0, v___x_2202_);
lean_ctor_set(v___x_2204_, 1, v___x_2203_);
v___x_2205_ = l_Lean_MessageData_ofExpr(v_T_2072_);
v___x_2206_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2206_, 0, v___x_2204_);
lean_ctor_set(v___x_2206_, 1, v___x_2205_);
v___x_2207_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__19, &l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__19_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__19);
v___x_2208_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2208_, 0, v___x_2206_);
lean_ctor_set(v___x_2208_, 1, v___x_2207_);
v___x_2209_ = l_Nat_reprFast(v___x_2196_);
v___x_2210_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2210_, 0, v___x_2209_);
v___x_2211_ = l_Lean_MessageData_ofFormat(v___x_2210_);
v___x_2212_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2212_, 0, v___x_2208_);
lean_ctor_set(v___x_2212_, 1, v___x_2211_);
v___x_2213_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__8___redArg(v___x_2212_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_);
v_a_2214_ = lean_ctor_get(v___x_2213_, 0);
v_isSharedCheck_2221_ = !lean_is_exclusive(v___x_2213_);
if (v_isSharedCheck_2221_ == 0)
{
v___x_2216_ = v___x_2213_;
v_isShared_2217_ = v_isSharedCheck_2221_;
goto v_resetjp_2215_;
}
else
{
lean_inc(v_a_2214_);
lean_dec(v___x_2213_);
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
else
{
lean_dec_ref(v_T_2072_);
v___y_2135_ = v___y_2054_;
v___y_2136_ = v___y_2055_;
v___y_2137_ = v___y_2056_;
v___y_2138_ = v___y_2057_;
v___y_2139_ = v___y_2058_;
v___y_2140_ = v___y_2059_;
v___y_2141_ = v___y_2060_;
v___y_2142_ = v___y_2061_;
goto v___jp_2134_;
}
v___jp_2081_:
{
lean_object* v___x_2094_; 
v___x_2094_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v___y_2092_, v___y_2091_);
if (lean_obj_tag(v___x_2094_) == 0)
{
lean_object* v_a_2095_; lean_object* v_H_2096_; lean_object* v___x_2097_; lean_object* v_fst_2098_; lean_object* v_snd_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2131_; 
v_a_2095_ = lean_ctor_get(v___x_2094_, 0);
lean_inc(v_a_2095_);
lean_dec_ref(v___x_2094_);
lean_inc_ref_n(v___y_2093_, 2);
v_H_2096_ = l_Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps(v___y_2093_, v_a_2095_);
lean_inc(v_u_2065_);
v___x_2097_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd(v_u_2065_, v___y_2093_, v_H_2096_, v___y_2087_);
v_fst_2098_ = lean_ctor_get(v___x_2097_, 0);
v_snd_2099_ = lean_ctor_get(v___x_2097_, 1);
v_isSharedCheck_2131_ = !lean_is_exclusive(v___x_2097_);
if (v_isSharedCheck_2131_ == 0)
{
v___x_2101_ = v___x_2097_;
v_isShared_2102_ = v_isSharedCheck_2131_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_snd_2099_);
lean_inc(v_fst_2098_);
lean_dec(v___x_2097_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2131_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v_goal_x27_2108_; 
v___x_2103_ = lean_array_get_size(v_a_2076_);
v___x_2104_ = l_Array_toSubarray___redArg(v_a_2076_, v_n_2051_, v___x_2103_);
v___x_2105_ = l_Subarray_copy___redArg(v___x_2104_);
v___x_2106_ = l_Lean_mkAppRev(v_f_2073_, v___x_2105_);
lean_dec_ref(v___x_2105_);
lean_inc(v_fst_2098_);
lean_inc(v_u_2065_);
if (v_isShared_2071_ == 0)
{
lean_ctor_set(v___x_2070_, 3, v___x_2106_);
lean_ctor_set(v___x_2070_, 2, v_fst_2098_);
lean_ctor_set(v___x_2070_, 1, v___y_2093_);
v_goal_x27_2108_ = v___x_2070_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v_u_2065_);
lean_ctor_set(v_reuseFailAlloc_2130_, 1, v___y_2093_);
lean_ctor_set(v_reuseFailAlloc_2130_, 2, v_fst_2098_);
lean_ctor_set(v_reuseFailAlloc_2130_, 3, v___x_2106_);
v_goal_x27_2108_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
lean_object* v___x_2109_; 
lean_inc(v___y_2089_);
lean_inc_ref(v___y_2085_);
lean_inc(v___y_2091_);
lean_inc_ref(v___y_2084_);
lean_inc(v___y_2088_);
lean_inc_ref(v___y_2082_);
lean_inc(v___y_2086_);
lean_inc_ref(v___y_2083_);
v___x_2109_ = lean_apply_10(v_k_2053_, v_goal_x27_2108_, v___y_2083_, v___y_2086_, v___y_2082_, v___y_2088_, v___y_2084_, v___y_2091_, v___y_2085_, v___y_2089_, lean_box(0));
if (lean_obj_tag(v___x_2109_) == 0)
{
lean_object* v_a_2110_; lean_object* v___x_2111_; 
v_a_2110_ = lean_ctor_get(v___x_2109_, 0);
lean_inc(v_a_2110_);
lean_dec_ref(v___x_2109_);
lean_inc(v___y_2089_);
lean_inc_ref(v___y_2085_);
lean_inc(v___y_2091_);
lean_inc_ref(v___y_2084_);
lean_inc_ref(v___y_2090_);
v___x_2111_ = lean_infer_type(v___y_2090_, v___y_2084_, v___y_2091_, v___y_2085_, v___y_2089_);
if (lean_obj_tag(v___x_2111_) == 0)
{
lean_object* v_a_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2129_; 
v_a_2112_ = lean_ctor_get(v___x_2111_, 0);
v_isSharedCheck_2129_ = !lean_is_exclusive(v___x_2111_);
if (v_isSharedCheck_2129_ == 0)
{
v___x_2114_ = v___x_2111_;
v_isShared_2115_ = v_isSharedCheck_2129_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_a_2112_);
lean_dec(v___x_2111_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2129_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2119_; 
v___x_2116_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__12___closed__1));
v___x_2117_ = lean_box(0);
if (v_isShared_2102_ == 0)
{
lean_ctor_set_tag(v___x_2101_, 1);
lean_ctor_set(v___x_2101_, 1, v___x_2117_);
lean_ctor_set(v___x_2101_, 0, v_u_2065_);
v___x_2119_ = v___x_2101_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v_u_2065_);
lean_ctor_set(v_reuseFailAlloc_2128_, 1, v___x_2117_);
v___x_2119_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v_prf_2124_; lean_object* v___x_2126_; 
v___x_2120_ = l_Lean_mkConst(v___x_2116_, v___x_2119_);
v___x_2121_ = l_Lean_mkAppN(v_fst_2098_, v_revertArgs_2080_);
v___x_2122_ = l_Lean_mkAppN(v_snd_2099_, v_revertArgs_2080_);
v___x_2123_ = l_Lean_mkAppN(v_a_2110_, v_revertArgs_2080_);
lean_dec_ref(v_revertArgs_2080_);
v_prf_2124_ = l_Lean_mkApp8(v___x_2120_, v_00_u03c3s_2066_, v_a_2112_, v_hyps_2067_, v___x_2121_, v_target_2068_, v___y_2090_, v___x_2122_, v___x_2123_);
if (v_isShared_2115_ == 0)
{
lean_ctor_set(v___x_2114_, 0, v_prf_2124_);
v___x_2126_ = v___x_2114_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v_prf_2124_);
v___x_2126_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
return v___x_2126_;
}
}
}
}
else
{
lean_dec(v_a_2110_);
lean_del_object(v___x_2101_);
lean_dec(v_snd_2099_);
lean_dec(v_fst_2098_);
lean_dec_ref(v___y_2090_);
lean_dec_ref(v_revertArgs_2080_);
lean_dec_ref(v_target_2068_);
lean_dec_ref(v_hyps_2067_);
lean_dec_ref(v_00_u03c3s_2066_);
lean_dec(v_u_2065_);
return v___x_2111_;
}
}
else
{
lean_del_object(v___x_2101_);
lean_dec(v_snd_2099_);
lean_dec(v_fst_2098_);
lean_dec_ref(v___y_2090_);
lean_dec_ref(v_revertArgs_2080_);
lean_dec_ref(v_target_2068_);
lean_dec_ref(v_hyps_2067_);
lean_dec_ref(v_00_u03c3s_2066_);
lean_dec(v_u_2065_);
return v___x_2109_;
}
}
}
}
else
{
lean_dec_ref(v___y_2093_);
lean_dec_ref(v___y_2090_);
lean_dec_ref(v___y_2087_);
lean_dec_ref(v_revertArgs_2080_);
lean_dec_ref(v_a_2076_);
lean_dec_ref(v_f_2073_);
lean_del_object(v___x_2070_);
lean_dec_ref(v_target_2068_);
lean_dec_ref(v_hyps_2067_);
lean_dec_ref(v_00_u03c3s_2066_);
lean_dec(v_u_2065_);
lean_dec_ref(v_k_2053_);
lean_dec(v_n_2051_);
return v___x_2094_;
}
}
v___jp_2134_:
{
size_t v_sz_2143_; size_t v___x_2144_; lean_object* v___x_2145_; 
v_sz_2143_ = lean_array_size(v_revertArgs_2080_);
v___x_2144_ = ((size_t)0ULL);
lean_inc_ref(v_revertArgs_2080_);
v___x_2145_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__3(v_sz_2143_, v___x_2144_, v_revertArgs_2080_, v___y_2139_, v___y_2140_, v___y_2141_, v___y_2142_);
if (lean_obj_tag(v___x_2145_) == 0)
{
lean_object* v_a_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; 
v_a_2146_ = lean_ctor_get(v___x_2145_, 0);
lean_inc(v_a_2146_);
lean_dec_ref(v___x_2145_);
v___x_2147_ = lean_array_get_size(v_a_2146_);
v___x_2148_ = lean_mk_empty_array_with_capacity(v___x_2147_);
v___x_2149_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__4___redArg(v_a_2146_, v___x_2147_, v___x_2063_, v___x_2148_, v___y_2141_, v___y_2142_);
if (lean_obj_tag(v___x_2149_) == 0)
{
lean_object* v_a_2150_; uint8_t v___x_2151_; lean_object* v___x_2152_; 
v_a_2150_ = lean_ctor_get(v___x_2149_, 0);
lean_inc(v_a_2150_);
lean_dec_ref(v___x_2149_);
v___x_2151_ = 0;
v___x_2152_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5(v_a_2150_, v___f_2133_, v___x_2151_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_, v___y_2142_);
if (lean_obj_tag(v___x_2152_) == 0)
{
lean_object* v_a_2153_; lean_object* v_fst_2154_; lean_object* v_snd_2155_; lean_object* v___x_2156_; 
v_a_2153_ = lean_ctor_get(v___x_2152_, 0);
lean_inc(v_a_2153_);
lean_dec_ref(v___x_2152_);
v_fst_2154_ = lean_ctor_get(v_a_2153_, 0);
lean_inc(v_fst_2154_);
v_snd_2155_ = lean_ctor_get(v_a_2153_, 1);
lean_inc(v_snd_2155_);
lean_dec(v_a_2153_);
lean_inc_ref(v_revertArgs_2080_);
v___x_2156_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__6(v_sz_2143_, v___x_2144_, v_revertArgs_2080_, v___y_2139_, v___y_2140_, v___y_2141_, v___y_2142_);
if (lean_obj_tag(v___x_2156_) == 0)
{
lean_object* v_a_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; 
v_a_2157_ = lean_ctor_get(v___x_2156_, 0);
lean_inc(v_a_2157_);
lean_dec_ref(v___x_2156_);
v___x_2158_ = lean_array_to_list(v_a_2157_);
v___x_2159_ = l_Lean_Meta_mkAndIntroN(v___x_2158_, v___y_2139_, v___y_2140_, v___y_2141_, v___y_2142_);
if (lean_obj_tag(v___x_2159_) == 0)
{
lean_object* v_a_2160_; uint8_t v___x_2161_; 
v_a_2160_ = lean_ctor_get(v___x_2159_, 0);
lean_inc(v_a_2160_);
lean_dec_ref(v___x_2159_);
v___x_2161_ = lean_nat_dec_lt(v___x_2063_, v___x_2147_);
if (v___x_2161_ == 0)
{
lean_dec(v_a_2146_);
lean_inc_ref(v_00_u03c3s_2066_);
v___y_2082_ = v___y_2137_;
v___y_2083_ = v___y_2135_;
v___y_2084_ = v___y_2139_;
v___y_2085_ = v___y_2141_;
v___y_2086_ = v___y_2136_;
v___y_2087_ = v_snd_2155_;
v___y_2088_ = v___y_2138_;
v___y_2089_ = v___y_2142_;
v___y_2090_ = v_a_2160_;
v___y_2091_ = v___y_2140_;
v___y_2092_ = v_fst_2154_;
v___y_2093_ = v_00_u03c3s_2066_;
goto v___jp_2081_;
}
else
{
size_t v___x_2162_; lean_object* v___x_2163_; 
v___x_2162_ = lean_usize_of_nat(v___x_2147_);
lean_inc_ref(v_00_u03c3s_2066_);
lean_inc(v_u_2065_);
v___x_2163_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__7(v_u_2065_, v_a_2146_, v___x_2162_, v___x_2144_, v_00_u03c3s_2066_);
lean_dec(v_a_2146_);
v___y_2082_ = v___y_2137_;
v___y_2083_ = v___y_2135_;
v___y_2084_ = v___y_2139_;
v___y_2085_ = v___y_2141_;
v___y_2086_ = v___y_2136_;
v___y_2087_ = v_snd_2155_;
v___y_2088_ = v___y_2138_;
v___y_2089_ = v___y_2142_;
v___y_2090_ = v_a_2160_;
v___y_2091_ = v___y_2140_;
v___y_2092_ = v_fst_2154_;
v___y_2093_ = v___x_2163_;
goto v___jp_2081_;
}
}
else
{
lean_dec(v_snd_2155_);
lean_dec(v_fst_2154_);
lean_dec(v_a_2146_);
lean_dec_ref(v_revertArgs_2080_);
lean_dec_ref(v_a_2076_);
lean_dec_ref(v_f_2073_);
lean_del_object(v___x_2070_);
lean_dec_ref(v_target_2068_);
lean_dec_ref(v_hyps_2067_);
lean_dec_ref(v_00_u03c3s_2066_);
lean_dec(v_u_2065_);
lean_dec_ref(v_k_2053_);
lean_dec(v_n_2051_);
return v___x_2159_;
}
}
else
{
lean_object* v_a_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2171_; 
lean_dec(v_snd_2155_);
lean_dec(v_fst_2154_);
lean_dec(v_a_2146_);
lean_dec_ref(v_revertArgs_2080_);
lean_dec_ref(v_a_2076_);
lean_dec_ref(v_f_2073_);
lean_del_object(v___x_2070_);
lean_dec_ref(v_target_2068_);
lean_dec_ref(v_hyps_2067_);
lean_dec_ref(v_00_u03c3s_2066_);
lean_dec(v_u_2065_);
lean_dec_ref(v_k_2053_);
lean_dec(v_n_2051_);
v_a_2164_ = lean_ctor_get(v___x_2156_, 0);
v_isSharedCheck_2171_ = !lean_is_exclusive(v___x_2156_);
if (v_isSharedCheck_2171_ == 0)
{
v___x_2166_ = v___x_2156_;
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
else
{
lean_inc(v_a_2164_);
lean_dec(v___x_2156_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
lean_object* v___x_2169_; 
if (v_isShared_2167_ == 0)
{
v___x_2169_ = v___x_2166_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v_a_2164_);
v___x_2169_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
return v___x_2169_;
}
}
}
}
else
{
lean_object* v_a_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2179_; 
lean_dec(v_a_2146_);
lean_dec_ref(v_revertArgs_2080_);
lean_dec_ref(v_a_2076_);
lean_dec_ref(v_f_2073_);
lean_del_object(v___x_2070_);
lean_dec_ref(v_target_2068_);
lean_dec_ref(v_hyps_2067_);
lean_dec_ref(v_00_u03c3s_2066_);
lean_dec(v_u_2065_);
lean_dec_ref(v_k_2053_);
lean_dec(v_n_2051_);
v_a_2172_ = lean_ctor_get(v___x_2152_, 0);
v_isSharedCheck_2179_ = !lean_is_exclusive(v___x_2152_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_2174_ = v___x_2152_;
v_isShared_2175_ = v_isSharedCheck_2179_;
goto v_resetjp_2173_;
}
else
{
lean_inc(v_a_2172_);
lean_dec(v___x_2152_);
v___x_2174_ = lean_box(0);
v_isShared_2175_ = v_isSharedCheck_2179_;
goto v_resetjp_2173_;
}
v_resetjp_2173_:
{
lean_object* v___x_2177_; 
if (v_isShared_2175_ == 0)
{
v___x_2177_ = v___x_2174_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v_a_2172_);
v___x_2177_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
return v___x_2177_;
}
}
}
}
else
{
lean_object* v_a_2180_; lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2187_; 
lean_dec(v_a_2146_);
lean_dec_ref(v___f_2133_);
lean_dec_ref(v_revertArgs_2080_);
lean_dec_ref(v_a_2076_);
lean_dec_ref(v_f_2073_);
lean_del_object(v___x_2070_);
lean_dec_ref(v_target_2068_);
lean_dec_ref(v_hyps_2067_);
lean_dec_ref(v_00_u03c3s_2066_);
lean_dec(v_u_2065_);
lean_dec_ref(v_k_2053_);
lean_dec(v_n_2051_);
v_a_2180_ = lean_ctor_get(v___x_2149_, 0);
v_isSharedCheck_2187_ = !lean_is_exclusive(v___x_2149_);
if (v_isSharedCheck_2187_ == 0)
{
v___x_2182_ = v___x_2149_;
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
else
{
lean_inc(v_a_2180_);
lean_dec(v___x_2149_);
v___x_2182_ = lean_box(0);
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
v_resetjp_2181_:
{
lean_object* v___x_2185_; 
if (v_isShared_2183_ == 0)
{
v___x_2185_ = v___x_2182_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v_a_2180_);
v___x_2185_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
return v___x_2185_;
}
}
}
}
else
{
lean_object* v_a_2188_; lean_object* v___x_2190_; uint8_t v_isShared_2191_; uint8_t v_isSharedCheck_2195_; 
lean_dec_ref(v___f_2133_);
lean_dec_ref(v_revertArgs_2080_);
lean_dec_ref(v_a_2076_);
lean_dec_ref(v_f_2073_);
lean_del_object(v___x_2070_);
lean_dec_ref(v_target_2068_);
lean_dec_ref(v_hyps_2067_);
lean_dec_ref(v_00_u03c3s_2066_);
lean_dec(v_u_2065_);
lean_dec_ref(v_k_2053_);
lean_dec(v_n_2051_);
v_a_2188_ = lean_ctor_get(v___x_2145_, 0);
v_isSharedCheck_2195_ = !lean_is_exclusive(v___x_2145_);
if (v_isSharedCheck_2195_ == 0)
{
v___x_2190_ = v___x_2145_;
v_isShared_2191_ = v_isSharedCheck_2195_;
goto v_resetjp_2189_;
}
else
{
lean_inc(v_a_2188_);
lean_dec(v___x_2145_);
v___x_2190_ = lean_box(0);
v_isShared_2191_ = v_isSharedCheck_2195_;
goto v_resetjp_2189_;
}
v_resetjp_2189_:
{
lean_object* v___x_2193_; 
if (v_isShared_2191_ == 0)
{
v___x_2193_ = v___x_2190_;
goto v_reusejp_2192_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v_a_2188_);
v___x_2193_ = v_reuseFailAlloc_2194_;
goto v_reusejp_2192_;
}
v_reusejp_2192_:
{
return v___x_2193_;
}
}
}
}
}
}
else
{
lean_object* v___x_2223_; 
lean_dec(v_hypName_2052_);
lean_dec(v_n_2051_);
lean_inc(v___y_2061_);
lean_inc_ref(v___y_2060_);
lean_inc(v___y_2059_);
lean_inc_ref(v___y_2058_);
lean_inc(v___y_2057_);
lean_inc_ref(v___y_2056_);
lean_inc(v___y_2055_);
lean_inc_ref(v___y_2054_);
v___x_2223_ = lean_apply_10(v_k_2053_, v_goal_2050_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_, lean_box(0));
return v___x_2223_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1___boxed(lean_object* v_goal_2224_, lean_object* v_n_2225_, lean_object* v_hypName_2226_, lean_object* v_k_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_){
_start:
{
lean_object* v_res_2237_; 
v_res_2237_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1(v_goal_2224_, v_n_2225_, v_hypName_2226_, v_k_2227_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_);
lean_dec(v___y_2235_);
lean_dec_ref(v___y_2234_);
lean_dec(v___y_2233_);
lean_dec_ref(v___y_2232_);
lean_dec(v___y_2231_);
lean_dec_ref(v___y_2230_);
lean_dec(v___y_2229_);
lean_dec_ref(v___y_2228_);
return v_res_2237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__1(lean_object* v___x_2241_, lean_object* v_snd_2242_, lean_object* v___y_2243_, lean_object* v_fst_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_){
_start:
{
lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; 
v___x_2254_ = lean_st_mk_ref(v___x_2241_);
v___x_2255_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__1___closed__1));
v___x_2256_ = l_Lean_Core_mkFreshUserName(v___x_2255_, v___y_2251_, v___y_2252_);
if (lean_obj_tag(v___x_2256_) == 0)
{
lean_object* v_a_2257_; lean_object* v___f_2258_; lean_object* v___x_2259_; 
v_a_2257_ = lean_ctor_get(v___x_2256_, 0);
lean_inc(v_a_2257_);
lean_dec_ref(v___x_2256_);
lean_inc(v___x_2254_);
v___f_2258_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__0___boxed), 11, 1);
lean_closure_set(v___f_2258_, 0, v___x_2254_);
v___x_2259_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1(v_snd_2242_, v___y_2243_, v_a_2257_, v___f_2258_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_);
if (lean_obj_tag(v___x_2259_) == 0)
{
lean_object* v_a_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; 
v_a_2260_ = lean_ctor_get(v___x_2259_, 0);
lean_inc(v_a_2260_);
lean_dec_ref(v___x_2259_);
v___x_2261_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2___redArg(v_fst_2244_, v_a_2260_, v___y_2250_);
lean_dec_ref(v___x_2261_);
v___x_2262_ = lean_st_ref_get(v___x_2254_);
lean_dec(v___x_2254_);
v___x_2263_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2262_, v___y_2246_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_);
return v___x_2263_;
}
else
{
lean_object* v_a_2264_; lean_object* v___x_2266_; uint8_t v_isShared_2267_; uint8_t v_isSharedCheck_2271_; 
lean_dec(v___x_2254_);
lean_dec(v_fst_2244_);
v_a_2264_ = lean_ctor_get(v___x_2259_, 0);
v_isSharedCheck_2271_ = !lean_is_exclusive(v___x_2259_);
if (v_isSharedCheck_2271_ == 0)
{
v___x_2266_ = v___x_2259_;
v_isShared_2267_ = v_isSharedCheck_2271_;
goto v_resetjp_2265_;
}
else
{
lean_inc(v_a_2264_);
lean_dec(v___x_2259_);
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
}
else
{
lean_object* v_a_2272_; lean_object* v___x_2274_; uint8_t v_isShared_2275_; uint8_t v_isSharedCheck_2279_; 
lean_dec(v___x_2254_);
lean_dec(v_fst_2244_);
lean_dec(v___y_2243_);
lean_dec_ref(v_snd_2242_);
v_a_2272_ = lean_ctor_get(v___x_2256_, 0);
v_isSharedCheck_2279_ = !lean_is_exclusive(v___x_2256_);
if (v_isSharedCheck_2279_ == 0)
{
v___x_2274_ = v___x_2256_;
v_isShared_2275_ = v_isSharedCheck_2279_;
goto v_resetjp_2273_;
}
else
{
lean_inc(v_a_2272_);
lean_dec(v___x_2256_);
v___x_2274_ = lean_box(0);
v_isShared_2275_ = v_isSharedCheck_2279_;
goto v_resetjp_2273_;
}
v_resetjp_2273_:
{
lean_object* v___x_2277_; 
if (v_isShared_2275_ == 0)
{
v___x_2277_ = v___x_2274_;
goto v_reusejp_2276_;
}
else
{
lean_object* v_reuseFailAlloc_2278_; 
v_reuseFailAlloc_2278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2278_, 0, v_a_2272_);
v___x_2277_ = v_reuseFailAlloc_2278_;
goto v_reusejp_2276_;
}
v_reusejp_2276_:
{
return v___x_2277_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__1___boxed(lean_object* v___x_2280_, lean_object* v_snd_2281_, lean_object* v___y_2282_, lean_object* v_fst_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_){
_start:
{
lean_object* v_res_2293_; 
v_res_2293_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__1(v___x_2280_, v_snd_2281_, v___y_2282_, v_fst_2283_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_);
lean_dec(v___y_2291_);
lean_dec_ref(v___y_2290_);
lean_dec(v___y_2289_);
lean_dec_ref(v___y_2288_);
lean_dec(v___y_2287_);
lean_dec_ref(v___y_2286_);
lean_dec(v___y_2285_);
lean_dec_ref(v___y_2284_);
return v_res_2293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__3(lean_object* v___x_2294_, lean_object* v_val_2295_, lean_object* v_h_2296_, lean_object* v_a_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_){
_start:
{
lean_object* v___x_2307_; lean_object* v___f_2308_; lean_object* v___x_2309_; 
v___x_2307_ = lean_st_mk_ref(v___x_2294_);
lean_inc(v___x_2307_);
v___f_2308_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__0___boxed), 11, 1);
lean_closure_set(v___f_2308_, 0, v___x_2307_);
v___x_2309_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevert___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__4(v_val_2295_, v_h_2296_, v___f_2308_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_);
if (lean_obj_tag(v___x_2309_) == 0)
{
lean_object* v_a_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; 
v_a_2310_ = lean_ctor_get(v___x_2309_, 0);
lean_inc(v_a_2310_);
lean_dec_ref(v___x_2309_);
v___x_2311_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2___redArg(v_a_2297_, v_a_2310_, v___y_2303_);
lean_dec_ref(v___x_2311_);
v___x_2312_ = lean_st_ref_get(v___x_2307_);
lean_dec(v___x_2307_);
v___x_2313_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2312_, v___y_2299_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_);
return v___x_2313_;
}
else
{
lean_object* v_a_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2321_; 
lean_dec(v___x_2307_);
lean_dec(v_a_2297_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__3___boxed(lean_object* v___x_2322_, lean_object* v_val_2323_, lean_object* v_h_2324_, lean_object* v_a_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_){
_start:
{
lean_object* v_res_2335_; 
v_res_2335_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__3(v___x_2322_, v_val_2323_, v_h_2324_, v_a_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_);
lean_dec(v___y_2333_);
lean_dec_ref(v___y_2332_);
lean_dec(v___y_2331_);
lean_dec_ref(v___y_2330_);
lean_dec(v___y_2329_);
lean_dec_ref(v___y_2328_);
lean_dec(v___y_2327_);
lean_dec_ref(v___y_2326_);
return v_res_2335_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5___redArg(lean_object* v_msg_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_){
_start:
{
lean_object* v_ref_2342_; lean_object* v___x_2343_; lean_object* v_a_2344_; lean_object* v___x_2346_; uint8_t v_isShared_2347_; uint8_t v_isSharedCheck_2352_; 
v_ref_2342_ = lean_ctor_get(v___y_2339_, 5);
v___x_2343_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5_spec__14(v_msg_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_);
v_a_2344_ = lean_ctor_get(v___x_2343_, 0);
v_isSharedCheck_2352_ = !lean_is_exclusive(v___x_2343_);
if (v_isSharedCheck_2352_ == 0)
{
v___x_2346_ = v___x_2343_;
v_isShared_2347_ = v_isSharedCheck_2352_;
goto v_resetjp_2345_;
}
else
{
lean_inc(v_a_2344_);
lean_dec(v___x_2343_);
v___x_2346_ = lean_box(0);
v_isShared_2347_ = v_isSharedCheck_2352_;
goto v_resetjp_2345_;
}
v_resetjp_2345_:
{
lean_object* v___x_2348_; lean_object* v___x_2350_; 
lean_inc(v_ref_2342_);
v___x_2348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2348_, 0, v_ref_2342_);
lean_ctor_set(v___x_2348_, 1, v_a_2344_);
if (v_isShared_2347_ == 0)
{
lean_ctor_set_tag(v___x_2346_, 1);
lean_ctor_set(v___x_2346_, 0, v___x_2348_);
v___x_2350_ = v___x_2346_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v___x_2348_);
v___x_2350_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
return v___x_2350_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5___redArg___boxed(lean_object* v_msg_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_){
_start:
{
lean_object* v_res_2359_; 
v_res_2359_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5___redArg(v_msg_2353_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_);
lean_dec(v___y_2357_);
lean_dec_ref(v___y_2356_);
lean_dec(v___y_2355_);
lean_dec_ref(v___y_2354_);
return v_res_2359_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__11(void){
_start:
{
lean_object* v___x_2384_; lean_object* v___x_2385_; 
v___x_2384_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__10));
v___x_2385_ = l_Lean_stringToMessageData(v___x_2384_);
return v___x_2385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert(lean_object* v_x_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_){
_start:
{
lean_object* v___y_2397_; lean_object* v___y_2398_; lean_object* v___y_2399_; lean_object* v___y_2400_; lean_object* v___y_2401_; lean_object* v___y_2402_; lean_object* v___y_2403_; lean_object* v___y_2404_; lean_object* v___y_2405_; lean_object* v___y_2406_; lean_object* v___y_2407_; lean_object* v___x_2411_; uint8_t v___x_2412_; 
v___x_2411_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__3));
lean_inc(v_x_2386_);
v___x_2412_ = l_Lean_Syntax_isOfKind(v_x_2386_, v___x_2411_);
if (v___x_2412_ == 0)
{
lean_object* v___x_2413_; 
lean_dec(v_x_2386_);
v___x_2413_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg();
return v___x_2413_;
}
else
{
lean_object* v___x_2414_; lean_object* v_n_2416_; lean_object* v___y_2417_; lean_object* v___y_2418_; lean_object* v___y_2419_; lean_object* v___y_2420_; lean_object* v___y_2421_; lean_object* v___y_2422_; lean_object* v___y_2423_; lean_object* v___y_2424_; lean_object* v___x_2441_; uint8_t v___x_2442_; 
v___x_2414_ = lean_unsigned_to_nat(1u);
v___x_2441_ = l_Lean_Syntax_getArg(v_x_2386_, v___x_2414_);
lean_dec(v_x_2386_);
lean_inc(v___x_2441_);
v___x_2442_ = l_Lean_Syntax_matchesNull(v___x_2441_, v___x_2414_);
if (v___x_2442_ == 0)
{
lean_object* v___x_2443_; 
lean_dec(v___x_2441_);
v___x_2443_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg();
return v___x_2443_;
}
else
{
lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; uint8_t v___x_2447_; 
v___x_2444_ = lean_unsigned_to_nat(0u);
v___x_2445_ = l_Lean_Syntax_getArg(v___x_2441_, v___x_2444_);
lean_dec(v___x_2441_);
v___x_2446_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__5));
lean_inc(v___x_2445_);
v___x_2447_ = l_Lean_Syntax_isOfKind(v___x_2445_, v___x_2446_);
if (v___x_2447_ == 0)
{
lean_object* v___x_2448_; uint8_t v___x_2449_; 
v___x_2448_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__7));
lean_inc(v___x_2445_);
v___x_2449_ = l_Lean_Syntax_isOfKind(v___x_2445_, v___x_2448_);
if (v___x_2449_ == 0)
{
lean_object* v___x_2450_; 
lean_dec(v___x_2445_);
v___x_2450_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg();
return v___x_2450_;
}
else
{
lean_object* v___x_2451_; uint8_t v___x_2452_; 
v___x_2451_ = l_Lean_Syntax_getArg(v___x_2445_, v___x_2414_);
lean_dec(v___x_2445_);
v___x_2452_ = l_Lean_Syntax_isNone(v___x_2451_);
if (v___x_2452_ == 0)
{
uint8_t v___x_2453_; 
lean_inc(v___x_2451_);
v___x_2453_ = l_Lean_Syntax_matchesNull(v___x_2451_, v___x_2414_);
if (v___x_2453_ == 0)
{
lean_object* v___x_2454_; 
lean_dec(v___x_2451_);
v___x_2454_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg();
return v___x_2454_;
}
else
{
lean_object* v_n_2455_; lean_object* v___x_2456_; 
v_n_2455_ = l_Lean_Syntax_getArg(v___x_2451_, v___x_2444_);
lean_dec(v___x_2451_);
v___x_2456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2456_, 0, v_n_2455_);
v_n_2416_ = v___x_2456_;
v___y_2417_ = v_a_2387_;
v___y_2418_ = v_a_2388_;
v___y_2419_ = v_a_2389_;
v___y_2420_ = v_a_2390_;
v___y_2421_ = v_a_2391_;
v___y_2422_ = v_a_2392_;
v___y_2423_ = v_a_2393_;
v___y_2424_ = v_a_2394_;
goto v___jp_2415_;
}
}
else
{
lean_object* v___x_2457_; 
lean_dec(v___x_2451_);
v___x_2457_ = lean_box(0);
v_n_2416_ = v___x_2457_;
v___y_2417_ = v_a_2387_;
v___y_2418_ = v_a_2388_;
v___y_2419_ = v_a_2389_;
v___y_2420_ = v_a_2390_;
v___y_2421_ = v_a_2391_;
v___y_2422_ = v_a_2392_;
v___y_2423_ = v_a_2393_;
v___y_2424_ = v_a_2394_;
goto v___jp_2415_;
}
}
}
else
{
lean_object* v_h_2458_; lean_object* v___x_2459_; uint8_t v___x_2460_; 
v_h_2458_ = l_Lean_Syntax_getArg(v___x_2445_, v___x_2444_);
lean_dec(v___x_2445_);
v___x_2459_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__9));
lean_inc(v_h_2458_);
v___x_2460_ = l_Lean_Syntax_isOfKind(v_h_2458_, v___x_2459_);
if (v___x_2460_ == 0)
{
lean_object* v___x_2461_; 
lean_dec(v_h_2458_);
v___x_2461_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg();
return v___x_2461_;
}
else
{
lean_object* v___x_2462_; 
v___x_2462_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_2388_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_);
if (lean_obj_tag(v___x_2462_) == 0)
{
lean_object* v_a_2463_; lean_object* v___x_2464_; 
v_a_2463_ = lean_ctor_get(v___x_2462_, 0);
lean_inc_n(v_a_2463_, 2);
lean_dec_ref(v___x_2462_);
v___x_2464_ = l_Lean_MVarId_getType(v_a_2463_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_);
if (lean_obj_tag(v___x_2464_) == 0)
{
lean_object* v_a_2465_; lean_object* v___x_2466_; 
v_a_2465_ = lean_ctor_get(v___x_2464_, 0);
lean_inc(v_a_2465_);
lean_dec_ref(v___x_2464_);
v___x_2466_ = l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f(v_a_2465_);
lean_dec(v_a_2465_);
if (lean_obj_tag(v___x_2466_) == 1)
{
lean_object* v_val_2467_; lean_object* v___x_2468_; lean_object* v___f_2469_; lean_object* v___x_2470_; 
v_val_2467_ = lean_ctor_get(v___x_2466_, 0);
lean_inc(v_val_2467_);
lean_dec_ref(v___x_2466_);
v___x_2468_ = lean_box(0);
lean_inc(v_a_2463_);
v___f_2469_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__3___boxed), 13, 4);
lean_closure_set(v___f_2469_, 0, v___x_2468_);
lean_closure_set(v___f_2469_, 1, v_val_2467_);
lean_closure_set(v___f_2469_, 2, v_h_2458_);
lean_closure_set(v___f_2469_, 3, v_a_2463_);
v___x_2470_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___redArg(v_a_2463_, v___f_2469_, v_a_2387_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_);
return v___x_2470_;
}
else
{
lean_object* v___x_2471_; lean_object* v___x_2472_; 
lean_dec(v___x_2466_);
lean_dec(v_a_2463_);
lean_dec(v_h_2458_);
v___x_2471_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__11, &l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__11_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__11);
v___x_2472_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5___redArg(v___x_2471_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_);
return v___x_2472_;
}
}
else
{
lean_object* v_a_2473_; lean_object* v___x_2475_; uint8_t v_isShared_2476_; uint8_t v_isSharedCheck_2480_; 
lean_dec(v_a_2463_);
lean_dec(v_h_2458_);
v_a_2473_ = lean_ctor_get(v___x_2464_, 0);
v_isSharedCheck_2480_ = !lean_is_exclusive(v___x_2464_);
if (v_isSharedCheck_2480_ == 0)
{
v___x_2475_ = v___x_2464_;
v_isShared_2476_ = v_isSharedCheck_2480_;
goto v_resetjp_2474_;
}
else
{
lean_inc(v_a_2473_);
lean_dec(v___x_2464_);
v___x_2475_ = lean_box(0);
v_isShared_2476_ = v_isSharedCheck_2480_;
goto v_resetjp_2474_;
}
v_resetjp_2474_:
{
lean_object* v___x_2478_; 
if (v_isShared_2476_ == 0)
{
v___x_2478_ = v___x_2475_;
goto v_reusejp_2477_;
}
else
{
lean_object* v_reuseFailAlloc_2479_; 
v_reuseFailAlloc_2479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2479_, 0, v_a_2473_);
v___x_2478_ = v_reuseFailAlloc_2479_;
goto v_reusejp_2477_;
}
v_reusejp_2477_:
{
return v___x_2478_;
}
}
}
}
else
{
lean_object* v_a_2481_; lean_object* v___x_2483_; uint8_t v_isShared_2484_; uint8_t v_isSharedCheck_2488_; 
lean_dec(v_h_2458_);
v_a_2481_ = lean_ctor_get(v___x_2462_, 0);
v_isSharedCheck_2488_ = !lean_is_exclusive(v___x_2462_);
if (v_isSharedCheck_2488_ == 0)
{
v___x_2483_ = v___x_2462_;
v_isShared_2484_ = v_isSharedCheck_2488_;
goto v_resetjp_2482_;
}
else
{
lean_inc(v_a_2481_);
lean_dec(v___x_2462_);
v___x_2483_ = lean_box(0);
v_isShared_2484_ = v_isSharedCheck_2488_;
goto v_resetjp_2482_;
}
v_resetjp_2482_:
{
lean_object* v___x_2486_; 
if (v_isShared_2484_ == 0)
{
v___x_2486_ = v___x_2483_;
goto v_reusejp_2485_;
}
else
{
lean_object* v_reuseFailAlloc_2487_; 
v_reuseFailAlloc_2487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2487_, 0, v_a_2481_);
v___x_2486_ = v_reuseFailAlloc_2487_;
goto v_reusejp_2485_;
}
v_reusejp_2485_:
{
return v___x_2486_;
}
}
}
}
}
}
v___jp_2415_:
{
lean_object* v___x_2425_; 
v___x_2425_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg(v___y_2418_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_);
if (lean_obj_tag(v___x_2425_) == 0)
{
lean_object* v_a_2426_; 
v_a_2426_ = lean_ctor_get(v___x_2425_, 0);
lean_inc(v_a_2426_);
lean_dec_ref(v___x_2425_);
if (lean_obj_tag(v_n_2416_) == 0)
{
lean_object* v_fst_2427_; lean_object* v_snd_2428_; 
v_fst_2427_ = lean_ctor_get(v_a_2426_, 0);
lean_inc(v_fst_2427_);
v_snd_2428_ = lean_ctor_get(v_a_2426_, 1);
lean_inc(v_snd_2428_);
lean_dec(v_a_2426_);
v___y_2397_ = v_fst_2427_;
v___y_2398_ = v_snd_2428_;
v___y_2399_ = v___y_2420_;
v___y_2400_ = v___y_2423_;
v___y_2401_ = v___y_2419_;
v___y_2402_ = v___y_2422_;
v___y_2403_ = v___y_2417_;
v___y_2404_ = v___y_2421_;
v___y_2405_ = v___y_2424_;
v___y_2406_ = v___y_2418_;
v___y_2407_ = v___x_2414_;
goto v___jp_2396_;
}
else
{
lean_object* v_fst_2429_; lean_object* v_snd_2430_; lean_object* v_val_2431_; lean_object* v___x_2432_; 
v_fst_2429_ = lean_ctor_get(v_a_2426_, 0);
lean_inc(v_fst_2429_);
v_snd_2430_ = lean_ctor_get(v_a_2426_, 1);
lean_inc(v_snd_2430_);
lean_dec(v_a_2426_);
v_val_2431_ = lean_ctor_get(v_n_2416_, 0);
lean_inc(v_val_2431_);
lean_dec_ref(v_n_2416_);
v___x_2432_ = l_Lean_TSyntax_getNat(v_val_2431_);
lean_dec(v_val_2431_);
v___y_2397_ = v_fst_2429_;
v___y_2398_ = v_snd_2430_;
v___y_2399_ = v___y_2420_;
v___y_2400_ = v___y_2423_;
v___y_2401_ = v___y_2419_;
v___y_2402_ = v___y_2422_;
v___y_2403_ = v___y_2417_;
v___y_2404_ = v___y_2421_;
v___y_2405_ = v___y_2424_;
v___y_2406_ = v___y_2418_;
v___y_2407_ = v___x_2432_;
goto v___jp_2396_;
}
}
else
{
lean_object* v_a_2433_; lean_object* v___x_2435_; uint8_t v_isShared_2436_; uint8_t v_isSharedCheck_2440_; 
lean_dec(v_n_2416_);
v_a_2433_ = lean_ctor_get(v___x_2425_, 0);
v_isSharedCheck_2440_ = !lean_is_exclusive(v___x_2425_);
if (v_isSharedCheck_2440_ == 0)
{
v___x_2435_ = v___x_2425_;
v_isShared_2436_ = v_isSharedCheck_2440_;
goto v_resetjp_2434_;
}
else
{
lean_inc(v_a_2433_);
lean_dec(v___x_2425_);
v___x_2435_ = lean_box(0);
v_isShared_2436_ = v_isSharedCheck_2440_;
goto v_resetjp_2434_;
}
v_resetjp_2434_:
{
lean_object* v___x_2438_; 
if (v_isShared_2436_ == 0)
{
v___x_2438_ = v___x_2435_;
goto v_reusejp_2437_;
}
else
{
lean_object* v_reuseFailAlloc_2439_; 
v_reuseFailAlloc_2439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2439_, 0, v_a_2433_);
v___x_2438_ = v_reuseFailAlloc_2439_;
goto v_reusejp_2437_;
}
v_reusejp_2437_:
{
return v___x_2438_;
}
}
}
}
}
v___jp_2396_:
{
lean_object* v___x_2408_; lean_object* v___f_2409_; lean_object* v___x_2410_; 
v___x_2408_ = lean_box(0);
lean_inc(v___y_2397_);
v___f_2409_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__1___boxed), 13, 4);
lean_closure_set(v___f_2409_, 0, v___x_2408_);
lean_closure_set(v___f_2409_, 1, v___y_2398_);
lean_closure_set(v___f_2409_, 2, v___y_2407_);
lean_closure_set(v___f_2409_, 3, v___y_2397_);
v___x_2410_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___redArg(v___y_2397_, v___f_2409_, v___y_2403_, v___y_2406_, v___y_2401_, v___y_2399_, v___y_2404_, v___y_2402_, v___y_2400_, v___y_2405_);
return v___x_2410_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___boxed(lean_object* v_x_2489_, lean_object* v_a_2490_, lean_object* v_a_2491_, lean_object* v_a_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_){
_start:
{
lean_object* v_res_2499_; 
v_res_2499_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert(v_x_2489_, v_a_2490_, v_a_2491_, v_a_2492_, v_a_2493_, v_a_2494_, v_a_2495_, v_a_2496_, v_a_2497_);
lean_dec(v_a_2497_);
lean_dec_ref(v_a_2496_);
lean_dec(v_a_2495_);
lean_dec_ref(v_a_2494_);
lean_dec(v_a_2493_);
lean_dec_ref(v_a_2492_);
lean_dec(v_a_2491_);
lean_dec_ref(v_a_2490_);
return v_res_2499_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2(lean_object* v_mvarId_2500_, lean_object* v_val_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_){
_start:
{
lean_object* v___x_2511_; 
v___x_2511_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2___redArg(v_mvarId_2500_, v_val_2501_, v___y_2507_);
return v___x_2511_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2___boxed(lean_object* v_mvarId_2512_, lean_object* v_val_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_){
_start:
{
lean_object* v_res_2523_; 
v_res_2523_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2(v_mvarId_2512_, v_val_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_);
lean_dec(v___y_2521_);
lean_dec_ref(v___y_2520_);
lean_dec(v___y_2519_);
lean_dec_ref(v___y_2518_);
lean_dec(v___y_2517_);
lean_dec_ref(v___y_2516_);
lean_dec(v___y_2515_);
lean_dec_ref(v___y_2514_);
return v_res_2523_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5(lean_object* v_00_u03b1_2524_, lean_object* v_msg_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_){
_start:
{
lean_object* v___x_2535_; 
v___x_2535_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5___redArg(v_msg_2525_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_);
return v___x_2535_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5___boxed(lean_object* v_00_u03b1_2536_, lean_object* v_msg_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_){
_start:
{
lean_object* v_res_2547_; 
v_res_2547_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5(v_00_u03b1_2536_, v_msg_2537_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_);
lean_dec(v___y_2545_);
lean_dec_ref(v___y_2544_);
lean_dec(v___y_2543_);
lean_dec_ref(v___y_2542_);
lean_dec(v___y_2541_);
lean_dec_ref(v___y_2540_);
lean_dec(v___y_2539_);
lean_dec_ref(v___y_2538_);
return v_res_2547_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__1(lean_object* v_inst_2548_, lean_object* v_R_2549_, lean_object* v_a_2550_, lean_object* v_b_2551_){
_start:
{
lean_object* v___x_2552_; 
v___x_2552_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__1___redArg(v_a_2550_, v_b_2551_);
return v___x_2552_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__2(size_t v_sz_2553_, size_t v_i_2554_, lean_object* v_bs_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_){
_start:
{
lean_object* v___x_2565_; 
v___x_2565_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__2___redArg(v_sz_2553_, v_i_2554_, v_bs_2555_, v___y_2560_, v___y_2561_, v___y_2562_, v___y_2563_);
return v___x_2565_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__2___boxed(lean_object* v_sz_2566_, lean_object* v_i_2567_, lean_object* v_bs_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_){
_start:
{
size_t v_sz_boxed_2578_; size_t v_i_boxed_2579_; lean_object* v_res_2580_; 
v_sz_boxed_2578_ = lean_unbox_usize(v_sz_2566_);
lean_dec(v_sz_2566_);
v_i_boxed_2579_ = lean_unbox_usize(v_i_2567_);
lean_dec(v_i_2567_);
v_res_2580_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__2(v_sz_boxed_2578_, v_i_boxed_2579_, v_bs_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_);
lean_dec(v___y_2576_);
lean_dec_ref(v___y_2575_);
lean_dec(v___y_2574_);
lean_dec_ref(v___y_2573_);
lean_dec(v___y_2572_);
lean_dec_ref(v___y_2571_);
lean_dec(v___y_2570_);
lean_dec_ref(v___y_2569_);
return v_res_2580_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__4(lean_object* v_as_2581_, lean_object* v_i_2582_, lean_object* v_j_2583_, lean_object* v_inv_2584_, lean_object* v_bs_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_){
_start:
{
lean_object* v___x_2595_; 
v___x_2595_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__4___redArg(v_as_2581_, v_i_2582_, v_j_2583_, v_bs_2585_, v___y_2592_, v___y_2593_);
return v___x_2595_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__4___boxed(lean_object* v_as_2596_, lean_object* v_i_2597_, lean_object* v_j_2598_, lean_object* v_inv_2599_, lean_object* v_bs_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_){
_start:
{
lean_object* v_res_2610_; 
v_res_2610_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__4(v_as_2596_, v_i_2597_, v_j_2598_, v_inv_2599_, v_bs_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_);
lean_dec(v___y_2608_);
lean_dec_ref(v___y_2607_);
lean_dec(v___y_2606_);
lean_dec_ref(v___y_2605_);
lean_dec(v___y_2604_);
lean_dec_ref(v___y_2603_);
lean_dec(v___y_2602_);
lean_dec_ref(v___y_2601_);
lean_dec_ref(v_as_2596_);
return v_res_2610_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__8(lean_object* v_00_u03b1_2611_, lean_object* v_msg_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_){
_start:
{
lean_object* v___x_2618_; 
v___x_2618_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__8___redArg(v_msg_2612_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_);
return v___x_2618_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__8___boxed(lean_object* v_00_u03b1_2619_, lean_object* v_msg_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_){
_start:
{
lean_object* v_res_2626_; 
v_res_2626_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__8(v_00_u03b1_2619_, v_msg_2620_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_);
lean_dec(v___y_2624_);
lean_dec_ref(v___y_2623_);
lean_dec(v___y_2622_);
lean_dec_ref(v___y_2621_);
return v_res_2626_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10(lean_object* v_00_u03b2_2627_, lean_object* v_x_2628_, lean_object* v_x_2629_, lean_object* v_x_2630_){
_start:
{
lean_object* v___x_2631_; 
v___x_2631_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10___redArg(v_x_2628_, v_x_2629_, v_x_2630_);
return v___x_2631_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15(lean_object* v_00_u03b2_2632_, lean_object* v_x_2633_, size_t v_x_2634_, size_t v_x_2635_, lean_object* v_x_2636_, lean_object* v_x_2637_){
_start:
{
lean_object* v___x_2638_; 
v___x_2638_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15___redArg(v_x_2633_, v_x_2634_, v_x_2635_, v_x_2636_, v_x_2637_);
return v___x_2638_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15___boxed(lean_object* v_00_u03b2_2639_, lean_object* v_x_2640_, lean_object* v_x_2641_, lean_object* v_x_2642_, lean_object* v_x_2643_, lean_object* v_x_2644_){
_start:
{
size_t v_x_22580__boxed_2645_; size_t v_x_22581__boxed_2646_; lean_object* v_res_2647_; 
v_x_22580__boxed_2645_ = lean_unbox_usize(v_x_2641_);
lean_dec(v_x_2641_);
v_x_22581__boxed_2646_ = lean_unbox_usize(v_x_2642_);
lean_dec(v_x_2642_);
v_res_2647_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15(v_00_u03b2_2639_, v_x_2640_, v_x_22580__boxed_2645_, v_x_22581__boxed_2646_, v_x_2643_, v_x_2644_);
return v_res_2647_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15_spec__20(lean_object* v_00_u03b2_2648_, lean_object* v_n_2649_, lean_object* v_k_2650_, lean_object* v_v_2651_){
_start:
{
lean_object* v___x_2652_; 
v___x_2652_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15_spec__20___redArg(v_n_2649_, v_k_2650_, v_v_2651_);
return v___x_2652_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15_spec__21(lean_object* v_00_u03b2_2653_, size_t v_depth_2654_, lean_object* v_keys_2655_, lean_object* v_vals_2656_, lean_object* v_heq_2657_, lean_object* v_i_2658_, lean_object* v_entries_2659_){
_start:
{
lean_object* v___x_2660_; 
v___x_2660_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15_spec__21___redArg(v_depth_2654_, v_keys_2655_, v_vals_2656_, v_i_2658_, v_entries_2659_);
return v___x_2660_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15_spec__21___boxed(lean_object* v_00_u03b2_2661_, lean_object* v_depth_2662_, lean_object* v_keys_2663_, lean_object* v_vals_2664_, lean_object* v_heq_2665_, lean_object* v_i_2666_, lean_object* v_entries_2667_){
_start:
{
size_t v_depth_boxed_2668_; lean_object* v_res_2669_; 
v_depth_boxed_2668_ = lean_unbox_usize(v_depth_2662_);
lean_dec(v_depth_2662_);
v_res_2669_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15_spec__21(v_00_u03b2_2661_, v_depth_boxed_2668_, v_keys_2663_, v_vals_2664_, v_heq_2665_, v_i_2666_, v_entries_2667_);
lean_dec_ref(v_vals_2664_);
lean_dec_ref(v_keys_2663_);
return v_res_2669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19_spec__21(lean_object* v_00_u03b1_2670_, lean_object* v_name_2671_, uint8_t v_bi_2672_, lean_object* v_type_2673_, lean_object* v_k_2674_, uint8_t v_kind_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_){
_start:
{
lean_object* v___x_2685_; 
v___x_2685_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19_spec__21___redArg(v_name_2671_, v_bi_2672_, v_type_2673_, v_k_2674_, v_kind_2675_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_);
return v___x_2685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19_spec__21___boxed(lean_object* v_00_u03b1_2686_, lean_object* v_name_2687_, lean_object* v_bi_2688_, lean_object* v_type_2689_, lean_object* v_k_2690_, lean_object* v_kind_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_){
_start:
{
uint8_t v_bi_boxed_2701_; uint8_t v_kind_boxed_2702_; lean_object* v_res_2703_; 
v_bi_boxed_2701_ = lean_unbox(v_bi_2688_);
v_kind_boxed_2702_ = lean_unbox(v_kind_2691_);
v_res_2703_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__9_spec__14_spec__19_spec__21(v_00_u03b1_2686_, v_name_2687_, v_bi_boxed_2701_, v_type_2689_, v_k_2690_, v_kind_boxed_2702_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_, v___y_2699_);
lean_dec(v___y_2699_);
lean_dec_ref(v___y_2698_);
lean_dec(v___y_2697_);
lean_dec_ref(v___y_2696_);
lean_dec(v___y_2695_);
lean_dec_ref(v___y_2694_);
lean_dec(v___y_2693_);
lean_dec_ref(v___y_2692_);
return v_res_2703_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15_spec__20_spec__22(lean_object* v_00_u03b2_2704_, lean_object* v_x_2705_, lean_object* v_x_2706_, lean_object* v_x_2707_, lean_object* v_x_2708_){
_start:
{
lean_object* v___x_2709_; 
v___x_2709_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__15_spec__20_spec__22___redArg(v_x_2705_, v_x_2706_, v_x_2707_, v_x_2708_);
return v___x_2709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1(){
_start:
{
lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; 
v___x_2721_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2722_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__3));
v___x_2723_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__3));
v___x_2724_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___boxed), 10, 0);
v___x_2725_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2721_, v___x_2722_, v___x_2723_, v___x_2724_);
return v___x_2725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___boxed(lean_object* v_a_2726_){
_start:
{
lean_object* v_res_2727_; 
v_res_2727_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1();
return v_res_2727_;
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
