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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
lean_object* l_instMonadEIO(lean_object*);
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
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
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
lean_object* lean_array_uget(lean_object*, size_t);
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
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkCons(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadFunctor___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadQuotationCoreM;
lean_object* l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadLift___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadFunctor___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instAddMessageContextMetaM;
lean_object* l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(lean_object*, lean_object*);
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
static const lean_closure_object l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadFunctor___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__12 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__12_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
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
static const lean_closure_object l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_inferType___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__21(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__2, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_74_ = l_instMonadEIO(lean_box(0));
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__0(lean_object* v_inst_178_, lean_object* v_x_179_){
_start:
{
lean_object* v_fst_180_; lean_object* v_snd_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v_fst_180_ = lean_ctor_get(v_x_179_, 0);
lean_inc(v_fst_180_);
v_snd_181_ = lean_ctor_get(v_x_179_, 1);
lean_inc(v_snd_181_);
lean_dec_ref(v_x_179_);
v___x_182_ = lean_alloc_closure((void*)(l_Lean_Meta_mkEq___boxed), 7, 2);
lean_closure_set(v___x_182_, 0, v_snd_181_);
lean_closure_set(v___x_182_, 1, v_fst_180_);
v___x_183_ = lean_apply_2(v_inst_178_, lean_box(0), v___x_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__1(lean_object* v_hypName_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_){
_start:
{
lean_object* v___x_190_; 
v___x_190_ = l_Lean_Core_mkFreshUserName(v_hypName_184_, v___y_187_, v___y_188_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__1___boxed(lean_object* v_hypName_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__1(v_hypName_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_);
lean_dec(v___y_195_);
lean_dec_ref(v___y_194_);
lean_dec(v___y_193_);
lean_dec_ref(v___y_192_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__2(lean_object* v_it_198_, lean_object* v_acc_199_, lean_object* v_recur_200_){
_start:
{
lean_object* v_array_201_; lean_object* v_start_202_; lean_object* v_stop_203_; lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_216_; 
v_array_201_ = lean_ctor_get(v_it_198_, 0);
v_start_202_ = lean_ctor_get(v_it_198_, 1);
v_stop_203_ = lean_ctor_get(v_it_198_, 2);
v_isSharedCheck_216_ = !lean_is_exclusive(v_it_198_);
if (v_isSharedCheck_216_ == 0)
{
v___x_205_ = v_it_198_;
v_isShared_206_ = v_isSharedCheck_216_;
goto v_resetjp_204_;
}
else
{
lean_inc(v_stop_203_);
lean_inc(v_start_202_);
lean_inc(v_array_201_);
lean_dec(v_it_198_);
v___x_205_ = lean_box(0);
v_isShared_206_ = v_isSharedCheck_216_;
goto v_resetjp_204_;
}
v_resetjp_204_:
{
uint8_t v___x_207_; 
v___x_207_ = lean_nat_dec_lt(v_start_202_, v_stop_203_);
if (v___x_207_ == 0)
{
lean_del_object(v___x_205_);
lean_dec(v_stop_203_);
lean_dec(v_start_202_);
lean_dec_ref(v_array_201_);
lean_dec_ref(v_recur_200_);
return v_acc_199_;
}
else
{
lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_211_; 
v___x_208_ = lean_unsigned_to_nat(1u);
v___x_209_ = lean_nat_add(v_start_202_, v___x_208_);
lean_inc_ref(v_array_201_);
if (v_isShared_206_ == 0)
{
lean_ctor_set(v___x_205_, 1, v___x_209_);
v___x_211_ = v___x_205_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v_array_201_);
lean_ctor_set(v_reuseFailAlloc_215_, 1, v___x_209_);
lean_ctor_set(v_reuseFailAlloc_215_, 2, v_stop_203_);
v___x_211_ = v_reuseFailAlloc_215_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_212_ = lean_array_fget(v_array_201_, v_start_202_);
lean_dec(v_start_202_);
lean_dec_ref(v_array_201_);
v___x_213_ = lean_array_push(v_acc_199_, v___x_212_);
v___x_214_ = lean_apply_3(v_recur_200_, v___x_211_, v___x_213_, lean_box(0));
return v___x_214_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__3(lean_object* v_u_217_, lean_object* v_x1_218_, lean_object* v_x2_219_){
_start:
{
lean_object* v___x_220_; 
v___x_220_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkCons(v_u_217_, v_x1_218_, v_x2_219_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__4(lean_object* v_toApplicative_221_, lean_object* v_i_222_, lean_object* v_a_223_, lean_object* v_____do__lift_224_){
_start:
{
lean_object* v_toPure_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
v_toPure_225_ = lean_ctor_get(v_toApplicative_221_, 1);
lean_inc(v_toPure_225_);
lean_dec_ref(v_toApplicative_221_);
v___x_226_ = lean_unsigned_to_nat(1u);
v___x_227_ = lean_nat_add(v_i_222_, v___x_226_);
v___x_228_ = lean_name_append_index_after(v_____do__lift_224_, v___x_227_);
v___x_229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_229_, 0, v___x_228_);
lean_ctor_set(v___x_229_, 1, v_a_223_);
v___x_230_ = lean_apply_2(v_toPure_225_, lean_box(0), v___x_229_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__4___boxed(lean_object* v_toApplicative_231_, lean_object* v_i_232_, lean_object* v_a_233_, lean_object* v_____do__lift_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__4(v_toApplicative_231_, v_i_232_, v_a_233_, v_____do__lift_234_);
lean_dec(v_i_232_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__5(lean_object* v___x_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_){
_start:
{
lean_object* v___x_242_; 
v___x_242_ = l_Lean_Core_mkFreshUserName(v___x_236_, v___y_239_, v___y_240_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__5___boxed(lean_object* v___x_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__5(v___x_243_, v___y_244_, v___y_245_, v___y_246_, v___y_247_);
lean_dec(v___y_247_);
lean_dec_ref(v___y_246_);
lean_dec(v___y_245_);
lean_dec_ref(v___y_244_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__6(lean_object* v_toApplicative_255_, lean_object* v_inst_256_, lean_object* v_toBind_257_, lean_object* v_i_258_, lean_object* v_a_259_, lean_object* v_x_260_){
_start:
{
lean_object* v___f_261_; lean_object* v___f_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v___f_261_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__4___boxed), 4, 3);
lean_closure_set(v___f_261_, 0, v_toApplicative_255_);
lean_closure_set(v___f_261_, 1, v_i_258_);
lean_closure_set(v___f_261_, 2, v_a_259_);
v___f_262_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__6___closed__2));
v___x_263_ = lean_apply_2(v_inst_256_, lean_box(0), v___f_262_);
v___x_264_ = lean_apply_4(v_toBind_257_, lean_box(0), lean_box(0), v___x_263_, v___f_261_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__7(lean_object* v_toApplicative_265_, lean_object* v_00_u03c6_266_, lean_object* v_____do__lift_267_){
_start:
{
lean_object* v_toPure_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v_toPure_268_ = lean_ctor_get(v_toApplicative_265_, 1);
lean_inc(v_toPure_268_);
lean_dec_ref(v_toApplicative_265_);
v___x_269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_269_, 0, v_____do__lift_267_);
lean_ctor_set(v___x_269_, 1, v_00_u03c6_266_);
v___x_270_ = lean_apply_2(v_toPure_268_, lean_box(0), v___x_269_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__8(lean_object* v_hypName_271_, lean_object* v_uniq_272_, lean_object* v_toApplicative_273_, lean_object* v_ss_274_, lean_object* v_hyps_275_, uint8_t v___x_276_, uint8_t v___x_277_, uint8_t v___x_278_, lean_object* v_inst_279_, lean_object* v_toBind_280_, lean_object* v_____do__lift_281_){
_start:
{
lean_object* v___x_282_; lean_object* v_00_u03c6_283_; lean_object* v___f_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_282_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_282_, 0, v_hypName_271_);
lean_ctor_set(v___x_282_, 1, v_uniq_272_);
lean_ctor_set(v___x_282_, 2, v_____do__lift_281_);
v_00_u03c6_283_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_282_);
v___f_284_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__7), 3, 2);
lean_closure_set(v___f_284_, 0, v_toApplicative_273_);
lean_closure_set(v___f_284_, 1, v_00_u03c6_283_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__8___boxed(lean_object* v_hypName_293_, lean_object* v_uniq_294_, lean_object* v_toApplicative_295_, lean_object* v_ss_296_, lean_object* v_hyps_297_, lean_object* v___x_298_, lean_object* v___x_299_, lean_object* v___x_300_, lean_object* v_inst_301_, lean_object* v_toBind_302_, lean_object* v_____do__lift_303_){
_start:
{
uint8_t v___x_1116__boxed_304_; uint8_t v___x_1117__boxed_305_; uint8_t v___x_1118__boxed_306_; lean_object* v_res_307_; 
v___x_1116__boxed_304_ = lean_unbox(v___x_298_);
v___x_1117__boxed_305_ = lean_unbox(v___x_299_);
v___x_1118__boxed_306_ = lean_unbox(v___x_300_);
v_res_307_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__8(v_hypName_293_, v_uniq_294_, v_toApplicative_295_, v_ss_296_, v_hyps_297_, v___x_1116__boxed_304_, v___x_1117__boxed_305_, v___x_1118__boxed_306_, v_inst_301_, v_toBind_302_, v_____do__lift_303_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__9(lean_object* v_hypName_308_, lean_object* v_toApplicative_309_, lean_object* v_ss_310_, lean_object* v_hyps_311_, uint8_t v___x_312_, lean_object* v_inst_313_, lean_object* v_toBind_314_, lean_object* v_00_u03c6_315_, lean_object* v_uniq_316_){
_start:
{
uint8_t v___x_317_; uint8_t v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___f_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_317_ = 1;
v___x_318_ = 1;
v___x_319_ = lean_box(v___x_312_);
v___x_320_ = lean_box(v___x_317_);
v___x_321_ = lean_box(v___x_318_);
lean_inc(v_toBind_314_);
lean_inc(v_inst_313_);
lean_inc_ref(v_ss_310_);
v___f_322_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__8___boxed), 11, 10);
lean_closure_set(v___f_322_, 0, v_hypName_308_);
lean_closure_set(v___f_322_, 1, v_uniq_316_);
lean_closure_set(v___f_322_, 2, v_toApplicative_309_);
lean_closure_set(v___f_322_, 3, v_ss_310_);
lean_closure_set(v___f_322_, 4, v_hyps_311_);
lean_closure_set(v___f_322_, 5, v___x_319_);
lean_closure_set(v___f_322_, 6, v___x_320_);
lean_closure_set(v___f_322_, 7, v___x_321_);
lean_closure_set(v___f_322_, 8, v_inst_313_);
lean_closure_set(v___f_322_, 9, v_toBind_314_);
v___x_323_ = lean_box(v___x_312_);
v___x_324_ = lean_box(v___x_317_);
v___x_325_ = lean_box(v___x_312_);
v___x_326_ = lean_box(v___x_317_);
v___x_327_ = lean_box(v___x_318_);
v___x_328_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(v___x_328_, 0, v_ss_310_);
lean_closure_set(v___x_328_, 1, v_00_u03c6_315_);
lean_closure_set(v___x_328_, 2, v___x_323_);
lean_closure_set(v___x_328_, 3, v___x_324_);
lean_closure_set(v___x_328_, 4, v___x_325_);
lean_closure_set(v___x_328_, 5, v___x_326_);
lean_closure_set(v___x_328_, 6, v___x_327_);
v___x_329_ = lean_apply_2(v_inst_313_, lean_box(0), v___x_328_);
v___x_330_ = lean_apply_4(v_toBind_314_, lean_box(0), lean_box(0), v___x_329_, v___f_322_);
return v___x_330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__9___boxed(lean_object* v_hypName_331_, lean_object* v_toApplicative_332_, lean_object* v_ss_333_, lean_object* v_hyps_334_, lean_object* v___x_335_, lean_object* v_inst_336_, lean_object* v_toBind_337_, lean_object* v_00_u03c6_338_, lean_object* v_uniq_339_){
_start:
{
uint8_t v___x_1151__boxed_340_; lean_object* v_res_341_; 
v___x_1151__boxed_340_ = lean_unbox(v___x_335_);
v_res_341_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__9(v_hypName_331_, v_toApplicative_332_, v_ss_333_, v_hyps_334_, v___x_1151__boxed_340_, v_inst_336_, v_toBind_337_, v_00_u03c6_338_, v_uniq_339_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__10(lean_object* v_u_342_, lean_object* v_00_u03c3s_343_, lean_object* v_hypName_344_, lean_object* v_toApplicative_345_, lean_object* v_ss_346_, lean_object* v_hyps_347_, uint8_t v___x_348_, lean_object* v_inst_349_, lean_object* v_toBind_350_, lean_object* v___f_351_, lean_object* v_eqs_352_){
_start:
{
lean_object* v_eqs_353_; lean_object* v_00_u03c6_354_; lean_object* v_00_u03c6_355_; lean_object* v___x_356_; lean_object* v___f_357_; lean_object* v___x_358_; lean_object* v___x_359_; 
v_eqs_353_ = lean_array_to_list(v_eqs_352_);
v_00_u03c6_354_ = l_Lean_mkAndN(v_eqs_353_);
v_00_u03c6_355_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure(v_u_342_, v_00_u03c3s_343_, v_00_u03c6_354_);
v___x_356_ = lean_box(v___x_348_);
lean_inc(v_toBind_350_);
lean_inc(v_inst_349_);
v___f_357_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__9___boxed), 9, 8);
lean_closure_set(v___f_357_, 0, v_hypName_344_);
lean_closure_set(v___f_357_, 1, v_toApplicative_345_);
lean_closure_set(v___f_357_, 2, v_ss_346_);
lean_closure_set(v___f_357_, 3, v_hyps_347_);
lean_closure_set(v___f_357_, 4, v___x_356_);
lean_closure_set(v___f_357_, 5, v_inst_349_);
lean_closure_set(v___f_357_, 6, v_toBind_350_);
lean_closure_set(v___f_357_, 7, v_00_u03c6_355_);
v___x_358_ = lean_apply_2(v_inst_349_, lean_box(0), v___f_351_);
v___x_359_ = lean_apply_4(v_toBind_350_, lean_box(0), lean_box(0), v___x_358_, v___f_357_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__10___boxed(lean_object* v_u_360_, lean_object* v_00_u03c3s_361_, lean_object* v_hypName_362_, lean_object* v_toApplicative_363_, lean_object* v_ss_364_, lean_object* v_hyps_365_, lean_object* v___x_366_, lean_object* v_inst_367_, lean_object* v_toBind_368_, lean_object* v___f_369_, lean_object* v_eqs_370_){
_start:
{
uint8_t v___x_1185__boxed_371_; lean_object* v_res_372_; 
v___x_1185__boxed_371_ = lean_unbox(v___x_366_);
v_res_372_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__10(v_u_360_, v_00_u03c3s_361_, v_hypName_362_, v_toApplicative_363_, v_ss_364_, v_hyps_365_, v___x_1185__boxed_371_, v_inst_367_, v_toBind_368_, v___f_369_, v_eqs_370_);
return v_res_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__11(lean_object* v_u_373_, lean_object* v_00_u03c3s_374_, lean_object* v_hypName_375_, lean_object* v_toApplicative_376_, lean_object* v_hyps_377_, uint8_t v___x_378_, lean_object* v_inst_379_, lean_object* v_toBind_380_, lean_object* v___f_381_, lean_object* v_revertArgs_382_, lean_object* v_inst_383_, lean_object* v___f_384_, lean_object* v_ss_385_){
_start:
{
lean_object* v___x_386_; lean_object* v___f_387_; lean_object* v___x_388_; size_t v_sz_389_; size_t v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_386_ = lean_box(v___x_378_);
lean_inc(v_toBind_380_);
lean_inc_ref(v_ss_385_);
v___f_387_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__10___boxed), 11, 10);
lean_closure_set(v___f_387_, 0, v_u_373_);
lean_closure_set(v___f_387_, 1, v_00_u03c3s_374_);
lean_closure_set(v___f_387_, 2, v_hypName_375_);
lean_closure_set(v___f_387_, 3, v_toApplicative_376_);
lean_closure_set(v___f_387_, 4, v_ss_385_);
lean_closure_set(v___f_387_, 5, v_hyps_377_);
lean_closure_set(v___f_387_, 6, v___x_386_);
lean_closure_set(v___f_387_, 7, v_inst_379_);
lean_closure_set(v___f_387_, 8, v_toBind_380_);
lean_closure_set(v___f_387_, 9, v___f_381_);
v___x_388_ = l_Array_zip___redArg(v_revertArgs_382_, v_ss_385_);
lean_dec_ref(v_ss_385_);
v_sz_389_ = lean_array_size(v___x_388_);
v___x_390_ = ((size_t)0ULL);
v___x_391_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_383_, v___f_384_, v_sz_389_, v___x_390_, v___x_388_);
v___x_392_ = lean_apply_4(v_toBind_380_, lean_box(0), lean_box(0), v___x_391_, v___f_387_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__11___boxed(lean_object* v_u_393_, lean_object* v_00_u03c3s_394_, lean_object* v_hypName_395_, lean_object* v_toApplicative_396_, lean_object* v_hyps_397_, lean_object* v___x_398_, lean_object* v_inst_399_, lean_object* v_toBind_400_, lean_object* v___f_401_, lean_object* v_revertArgs_402_, lean_object* v_inst_403_, lean_object* v___f_404_, lean_object* v_ss_405_){
_start:
{
uint8_t v___x_1202__boxed_406_; lean_object* v_res_407_; 
v___x_1202__boxed_406_ = lean_unbox(v___x_398_);
v_res_407_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__11(v_u_393_, v_00_u03c3s_394_, v_hypName_395_, v_toApplicative_396_, v_hyps_397_, v___x_1202__boxed_406_, v_inst_399_, v_toBind_400_, v___f_401_, v_revertArgs_402_, v_inst_403_, v___f_404_, v_ss_405_);
lean_dec_ref(v_revertArgs_402_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__12(lean_object* v_toApplicative_416_, lean_object* v_u_417_, lean_object* v_fst_418_, lean_object* v_revertArgs_419_, lean_object* v_snd_420_, lean_object* v_prf_421_, lean_object* v_00_u03c3s_422_, lean_object* v_hyps_423_, lean_object* v_target_424_, lean_object* v_h_425_, lean_object* v_____do__lift_426_){
_start:
{
lean_object* v_toPure_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v_prf_435_; lean_object* v___x_436_; 
v_toPure_427_ = lean_ctor_get(v_toApplicative_416_, 1);
lean_inc(v_toPure_427_);
lean_dec_ref(v_toApplicative_416_);
v___x_428_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__12___closed__1));
v___x_429_ = lean_box(0);
v___x_430_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_430_, 0, v_u_417_);
lean_ctor_set(v___x_430_, 1, v___x_429_);
v___x_431_ = l_Lean_mkConst(v___x_428_, v___x_430_);
v___x_432_ = l_Lean_mkAppN(v_fst_418_, v_revertArgs_419_);
v___x_433_ = l_Lean_mkAppN(v_snd_420_, v_revertArgs_419_);
v___x_434_ = l_Lean_mkAppN(v_prf_421_, v_revertArgs_419_);
v_prf_435_ = l_Lean_mkApp8(v___x_431_, v_00_u03c3s_422_, v_____do__lift_426_, v_hyps_423_, v___x_432_, v_target_424_, v_h_425_, v___x_433_, v___x_434_);
v___x_436_ = lean_apply_2(v_toPure_427_, lean_box(0), v_prf_435_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__12___boxed(lean_object* v_toApplicative_437_, lean_object* v_u_438_, lean_object* v_fst_439_, lean_object* v_revertArgs_440_, lean_object* v_snd_441_, lean_object* v_prf_442_, lean_object* v_00_u03c3s_443_, lean_object* v_hyps_444_, lean_object* v_target_445_, lean_object* v_h_446_, lean_object* v_____do__lift_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__12(v_toApplicative_437_, v_u_438_, v_fst_439_, v_revertArgs_440_, v_snd_441_, v_prf_442_, v_00_u03c3s_443_, v_hyps_444_, v_target_445_, v_h_446_, v_____do__lift_447_);
lean_dec_ref(v_revertArgs_440_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__13(lean_object* v_toApplicative_449_, lean_object* v_u_450_, lean_object* v_fst_451_, lean_object* v_revertArgs_452_, lean_object* v_snd_453_, lean_object* v_00_u03c3s_454_, lean_object* v_hyps_455_, lean_object* v_target_456_, lean_object* v_h_457_, lean_object* v_inst_458_, lean_object* v_toBind_459_, lean_object* v_prf_460_){
_start:
{
lean_object* v___f_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; 
lean_inc_ref(v_h_457_);
v___f_461_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__12___boxed), 11, 10);
lean_closure_set(v___f_461_, 0, v_toApplicative_449_);
lean_closure_set(v___f_461_, 1, v_u_450_);
lean_closure_set(v___f_461_, 2, v_fst_451_);
lean_closure_set(v___f_461_, 3, v_revertArgs_452_);
lean_closure_set(v___f_461_, 4, v_snd_453_);
lean_closure_set(v___f_461_, 5, v_prf_460_);
lean_closure_set(v___f_461_, 6, v_00_u03c3s_454_);
lean_closure_set(v___f_461_, 7, v_hyps_455_);
lean_closure_set(v___f_461_, 8, v_target_456_);
lean_closure_set(v___f_461_, 9, v_h_457_);
v___x_462_ = lean_alloc_closure((void*)(l_Lean_Meta_inferType___boxed), 6, 1);
lean_closure_set(v___x_462_, 0, v_h_457_);
v___x_463_ = lean_apply_2(v_inst_458_, lean_box(0), v___x_462_);
v___x_464_ = lean_apply_4(v_toBind_459_, lean_box(0), lean_box(0), v___x_463_, v___f_461_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__14(lean_object* v___y_465_, lean_object* v_u_466_, lean_object* v_snd_467_, lean_object* v_toApplicative_468_, lean_object* v_revertArgs_469_, lean_object* v_00_u03c3s_470_, lean_object* v_hyps_471_, lean_object* v_target_472_, lean_object* v_h_473_, lean_object* v_inst_474_, lean_object* v_toBind_475_, lean_object* v_a_476_, lean_object* v_n_477_, lean_object* v_f_478_, lean_object* v_k_479_, lean_object* v_H_480_){
_start:
{
lean_object* v_H_481_; lean_object* v___x_482_; lean_object* v_fst_483_; lean_object* v_snd_484_; lean_object* v___f_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v_goal_x27_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
lean_inc_ref_n(v___y_465_, 2);
v_H_481_ = l_Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps(v___y_465_, v_H_480_);
lean_inc_n(v_u_466_, 2);
v___x_482_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd(v_u_466_, v___y_465_, v_H_481_, v_snd_467_);
v_fst_483_ = lean_ctor_get(v___x_482_, 0);
lean_inc_n(v_fst_483_, 2);
v_snd_484_ = lean_ctor_get(v___x_482_, 1);
lean_inc(v_snd_484_);
lean_dec_ref(v___x_482_);
lean_inc(v_toBind_475_);
v___f_485_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__13), 12, 11);
lean_closure_set(v___f_485_, 0, v_toApplicative_468_);
lean_closure_set(v___f_485_, 1, v_u_466_);
lean_closure_set(v___f_485_, 2, v_fst_483_);
lean_closure_set(v___f_485_, 3, v_revertArgs_469_);
lean_closure_set(v___f_485_, 4, v_snd_484_);
lean_closure_set(v___f_485_, 5, v_00_u03c3s_470_);
lean_closure_set(v___f_485_, 6, v_hyps_471_);
lean_closure_set(v___f_485_, 7, v_target_472_);
lean_closure_set(v___f_485_, 8, v_h_473_);
lean_closure_set(v___f_485_, 9, v_inst_474_);
lean_closure_set(v___f_485_, 10, v_toBind_475_);
v___x_486_ = lean_array_get_size(v_a_476_);
v___x_487_ = l_Array_toSubarray___redArg(v_a_476_, v_n_477_, v___x_486_);
v___x_488_ = l_Subarray_copy___redArg(v___x_487_);
v___x_489_ = l_Lean_mkAppRev(v_f_478_, v___x_488_);
lean_dec_ref(v___x_488_);
v_goal_x27_490_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_goal_x27_490_, 0, v_u_466_);
lean_ctor_set(v_goal_x27_490_, 1, v___y_465_);
lean_ctor_set(v_goal_x27_490_, 2, v_fst_483_);
lean_ctor_set(v_goal_x27_490_, 3, v___x_489_);
v___x_491_ = lean_apply_1(v_k_479_, v_goal_x27_490_);
v___x_492_ = lean_apply_4(v_toBind_475_, lean_box(0), lean_box(0), v___x_491_, v___f_485_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15(lean_object* v_u_512_, lean_object* v_snd_513_, lean_object* v_toApplicative_514_, lean_object* v_revertArgs_515_, lean_object* v_00_u03c3s_516_, lean_object* v_hyps_517_, lean_object* v_target_518_, lean_object* v_inst_519_, lean_object* v_toBind_520_, lean_object* v_a_521_, lean_object* v_n_522_, lean_object* v_f_523_, lean_object* v_k_524_, lean_object* v_fst_525_, lean_object* v_revertArgsTypes_526_, lean_object* v___x_527_, lean_object* v___f_528_, lean_object* v_h_529_){
_start:
{
lean_object* v___y_531_; lean_object* v___x_536_; lean_object* v___x_537_; uint8_t v___x_538_; 
v___x_536_ = lean_array_get_size(v_revertArgsTypes_526_);
v___x_537_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__9));
v___x_538_ = lean_nat_dec_lt(v___x_527_, v___x_536_);
if (v___x_538_ == 0)
{
lean_dec_ref(v___f_528_);
lean_dec_ref(v_revertArgsTypes_526_);
lean_inc_ref(v_00_u03c3s_516_);
v___y_531_ = v_00_u03c3s_516_;
goto v___jp_530_;
}
else
{
size_t v___x_539_; size_t v___x_540_; lean_object* v___x_541_; 
v___x_539_ = lean_usize_of_nat(v___x_536_);
v___x_540_ = ((size_t)0ULL);
lean_inc_ref(v_00_u03c3s_516_);
v___x_541_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_537_, v___f_528_, v_revertArgsTypes_526_, v___x_539_, v___x_540_, v_00_u03c3s_516_);
v___y_531_ = v___x_541_;
goto v___jp_530_;
}
v___jp_530_:
{
lean_object* v___f_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
lean_inc(v_toBind_520_);
lean_inc(v_inst_519_);
v___f_532_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__14), 16, 15);
lean_closure_set(v___f_532_, 0, v___y_531_);
lean_closure_set(v___f_532_, 1, v_u_512_);
lean_closure_set(v___f_532_, 2, v_snd_513_);
lean_closure_set(v___f_532_, 3, v_toApplicative_514_);
lean_closure_set(v___f_532_, 4, v_revertArgs_515_);
lean_closure_set(v___f_532_, 5, v_00_u03c3s_516_);
lean_closure_set(v___f_532_, 6, v_hyps_517_);
lean_closure_set(v___f_532_, 7, v_target_518_);
lean_closure_set(v___f_532_, 8, v_h_529_);
lean_closure_set(v___f_532_, 9, v_inst_519_);
lean_closure_set(v___f_532_, 10, v_toBind_520_);
lean_closure_set(v___f_532_, 11, v_a_521_);
lean_closure_set(v___f_532_, 12, v_n_522_);
lean_closure_set(v___f_532_, 13, v_f_523_);
lean_closure_set(v___f_532_, 14, v_k_524_);
v___x_533_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateMVarsIfMVarApp___boxed), 6, 1);
lean_closure_set(v___x_533_, 0, v_fst_525_);
v___x_534_ = lean_apply_2(v_inst_519_, lean_box(0), v___x_533_);
v___x_535_ = lean_apply_4(v_toBind_520_, lean_box(0), lean_box(0), v___x_534_, v___f_532_);
return v___x_535_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___boxed(lean_object** _args){
lean_object* v_u_542_ = _args[0];
lean_object* v_snd_543_ = _args[1];
lean_object* v_toApplicative_544_ = _args[2];
lean_object* v_revertArgs_545_ = _args[3];
lean_object* v_00_u03c3s_546_ = _args[4];
lean_object* v_hyps_547_ = _args[5];
lean_object* v_target_548_ = _args[6];
lean_object* v_inst_549_ = _args[7];
lean_object* v_toBind_550_ = _args[8];
lean_object* v_a_551_ = _args[9];
lean_object* v_n_552_ = _args[10];
lean_object* v_f_553_ = _args[11];
lean_object* v_k_554_ = _args[12];
lean_object* v_fst_555_ = _args[13];
lean_object* v_revertArgsTypes_556_ = _args[14];
lean_object* v___x_557_ = _args[15];
lean_object* v___f_558_ = _args[16];
lean_object* v_h_559_ = _args[17];
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15(v_u_542_, v_snd_543_, v_toApplicative_544_, v_revertArgs_545_, v_00_u03c3s_546_, v_hyps_547_, v_target_548_, v_inst_549_, v_toBind_550_, v_a_551_, v_n_552_, v_f_553_, v_k_554_, v_fst_555_, v_revertArgsTypes_556_, v___x_557_, v___f_558_, v_h_559_);
lean_dec(v___x_557_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__16(lean_object* v_inst_561_, lean_object* v_toBind_562_, lean_object* v___f_563_, lean_object* v_prfs_564_){
_start:
{
lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_565_ = lean_array_to_list(v_prfs_564_);
v___x_566_ = lean_alloc_closure((void*)(l_Lean_Meta_mkAndIntroN___boxed), 6, 1);
lean_closure_set(v___x_566_, 0, v___x_565_);
v___x_567_ = lean_apply_2(v_inst_561_, lean_box(0), v___x_566_);
v___x_568_ = lean_apply_4(v_toBind_562_, lean_box(0), lean_box(0), v___x_567_, v___f_563_);
return v___x_568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__17(lean_object* v_u_570_, lean_object* v_toApplicative_571_, lean_object* v_revertArgs_572_, lean_object* v_00_u03c3s_573_, lean_object* v_hyps_574_, lean_object* v_target_575_, lean_object* v_inst_576_, lean_object* v_toBind_577_, lean_object* v_a_578_, lean_object* v_n_579_, lean_object* v_f_580_, lean_object* v_k_581_, lean_object* v_revertArgsTypes_582_, lean_object* v___x_583_, lean_object* v___f_584_, lean_object* v___x_585_, lean_object* v_____x_586_){
_start:
{
lean_object* v_fst_587_; lean_object* v_snd_588_; lean_object* v___f_589_; lean_object* v___f_590_; lean_object* v___x_591_; size_t v_sz_592_; size_t v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; 
v_fst_587_ = lean_ctor_get(v_____x_586_, 0);
lean_inc(v_fst_587_);
v_snd_588_ = lean_ctor_get(v_____x_586_, 1);
lean_inc(v_snd_588_);
lean_dec_ref(v_____x_586_);
lean_inc_n(v_toBind_577_, 2);
lean_inc_n(v_inst_576_, 2);
lean_inc_ref(v_revertArgs_572_);
v___f_589_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___boxed), 18, 17);
lean_closure_set(v___f_589_, 0, v_u_570_);
lean_closure_set(v___f_589_, 1, v_snd_588_);
lean_closure_set(v___f_589_, 2, v_toApplicative_571_);
lean_closure_set(v___f_589_, 3, v_revertArgs_572_);
lean_closure_set(v___f_589_, 4, v_00_u03c3s_573_);
lean_closure_set(v___f_589_, 5, v_hyps_574_);
lean_closure_set(v___f_589_, 6, v_target_575_);
lean_closure_set(v___f_589_, 7, v_inst_576_);
lean_closure_set(v___f_589_, 8, v_toBind_577_);
lean_closure_set(v___f_589_, 9, v_a_578_);
lean_closure_set(v___f_589_, 10, v_n_579_);
lean_closure_set(v___f_589_, 11, v_f_580_);
lean_closure_set(v___f_589_, 12, v_k_581_);
lean_closure_set(v___f_589_, 13, v_fst_587_);
lean_closure_set(v___f_589_, 14, v_revertArgsTypes_582_);
lean_closure_set(v___f_589_, 15, v___x_583_);
lean_closure_set(v___f_589_, 16, v___f_584_);
v___f_590_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__16), 4, 3);
lean_closure_set(v___f_590_, 0, v_inst_576_);
lean_closure_set(v___f_590_, 1, v_toBind_577_);
lean_closure_set(v___f_590_, 2, v___f_589_);
v___x_591_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__17___closed__0));
v_sz_592_ = lean_array_size(v_revertArgs_572_);
v___x_593_ = ((size_t)0ULL);
v___x_594_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_585_, v___x_591_, v_sz_592_, v___x_593_, v_revertArgs_572_);
v___x_595_ = lean_apply_2(v_inst_576_, lean_box(0), v___x_594_);
v___x_596_ = lean_apply_4(v_toBind_577_, lean_box(0), lean_box(0), v___x_595_, v___f_590_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__17___boxed(lean_object** _args){
lean_object* v_u_597_ = _args[0];
lean_object* v_toApplicative_598_ = _args[1];
lean_object* v_revertArgs_599_ = _args[2];
lean_object* v_00_u03c3s_600_ = _args[3];
lean_object* v_hyps_601_ = _args[4];
lean_object* v_target_602_ = _args[5];
lean_object* v_inst_603_ = _args[6];
lean_object* v_toBind_604_ = _args[7];
lean_object* v_a_605_ = _args[8];
lean_object* v_n_606_ = _args[9];
lean_object* v_f_607_ = _args[10];
lean_object* v_k_608_ = _args[11];
lean_object* v_revertArgsTypes_609_ = _args[12];
lean_object* v___x_610_ = _args[13];
lean_object* v___f_611_ = _args[14];
lean_object* v___x_612_ = _args[15];
lean_object* v_____x_613_ = _args[16];
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__17(v_u_597_, v_toApplicative_598_, v_revertArgs_599_, v_00_u03c3s_600_, v_hyps_601_, v_target_602_, v_inst_603_, v_toBind_604_, v_a_605_, v_n_606_, v_f_607_, v_k_608_, v_revertArgsTypes_609_, v___x_610_, v___f_611_, v___x_612_, v_____x_613_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__18(lean_object* v_inst_615_, lean_object* v_inst_616_, lean_object* v___f_617_, lean_object* v_toBind_618_, lean_object* v___f_619_, lean_object* v_declInfos_620_){
_start:
{
uint8_t v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_621_ = 0;
v___x_622_ = l_Lean_Meta_withLocalDeclsDND___redArg(v_inst_615_, v_inst_616_, v_declInfos_620_, v___f_617_, v___x_621_);
v___x_623_ = lean_apply_4(v_toBind_618_, lean_box(0), lean_box(0), v___x_622_, v___f_619_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__19(lean_object* v_u_624_, lean_object* v_toApplicative_625_, lean_object* v_revertArgs_626_, lean_object* v_00_u03c3s_627_, lean_object* v_hyps_628_, lean_object* v_target_629_, lean_object* v_inst_630_, lean_object* v_toBind_631_, lean_object* v_a_632_, lean_object* v_n_633_, lean_object* v_f_634_, lean_object* v_k_635_, lean_object* v___x_636_, lean_object* v___f_637_, lean_object* v___x_638_, lean_object* v_inst_639_, lean_object* v_inst_640_, lean_object* v___f_641_, lean_object* v___f_642_, lean_object* v_revertArgsTypes_643_){
_start:
{
lean_object* v___f_644_; lean_object* v___f_645_; size_t v_sz_646_; size_t v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
lean_inc_ref_n(v_revertArgsTypes_643_, 2);
lean_inc_n(v_toBind_631_, 2);
v___f_644_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__17___boxed), 17, 16);
lean_closure_set(v___f_644_, 0, v_u_624_);
lean_closure_set(v___f_644_, 1, v_toApplicative_625_);
lean_closure_set(v___f_644_, 2, v_revertArgs_626_);
lean_closure_set(v___f_644_, 3, v_00_u03c3s_627_);
lean_closure_set(v___f_644_, 4, v_hyps_628_);
lean_closure_set(v___f_644_, 5, v_target_629_);
lean_closure_set(v___f_644_, 6, v_inst_630_);
lean_closure_set(v___f_644_, 7, v_toBind_631_);
lean_closure_set(v___f_644_, 8, v_a_632_);
lean_closure_set(v___f_644_, 9, v_n_633_);
lean_closure_set(v___f_644_, 10, v_f_634_);
lean_closure_set(v___f_644_, 11, v_k_635_);
lean_closure_set(v___f_644_, 12, v_revertArgsTypes_643_);
lean_closure_set(v___f_644_, 13, v___x_636_);
lean_closure_set(v___f_644_, 14, v___f_637_);
lean_closure_set(v___f_644_, 15, v___x_638_);
lean_inc_ref(v_inst_640_);
v___f_645_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__18), 6, 5);
lean_closure_set(v___f_645_, 0, v_inst_639_);
lean_closure_set(v___f_645_, 1, v_inst_640_);
lean_closure_set(v___f_645_, 2, v___f_641_);
lean_closure_set(v___f_645_, 3, v_toBind_631_);
lean_closure_set(v___f_645_, 4, v___f_644_);
v_sz_646_ = lean_array_size(v_revertArgsTypes_643_);
v___x_647_ = ((size_t)0ULL);
v___x_648_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_640_, v_revertArgsTypes_643_, v___f_642_, v_sz_646_, v___x_647_, v_revertArgsTypes_643_);
lean_dec_ref(v_revertArgsTypes_643_);
v___x_649_ = lean_apply_4(v_toBind_631_, lean_box(0), lean_box(0), v___x_648_, v___f_645_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__19___boxed(lean_object** _args){
lean_object* v_u_650_ = _args[0];
lean_object* v_toApplicative_651_ = _args[1];
lean_object* v_revertArgs_652_ = _args[2];
lean_object* v_00_u03c3s_653_ = _args[3];
lean_object* v_hyps_654_ = _args[4];
lean_object* v_target_655_ = _args[5];
lean_object* v_inst_656_ = _args[6];
lean_object* v_toBind_657_ = _args[7];
lean_object* v_a_658_ = _args[8];
lean_object* v_n_659_ = _args[9];
lean_object* v_f_660_ = _args[10];
lean_object* v_k_661_ = _args[11];
lean_object* v___x_662_ = _args[12];
lean_object* v___f_663_ = _args[13];
lean_object* v___x_664_ = _args[14];
lean_object* v_inst_665_ = _args[15];
lean_object* v_inst_666_ = _args[16];
lean_object* v___f_667_ = _args[17];
lean_object* v___f_668_ = _args[18];
lean_object* v_revertArgsTypes_669_ = _args[19];
_start:
{
lean_object* v_res_670_; 
v_res_670_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__19(v_u_650_, v_toApplicative_651_, v_revertArgs_652_, v_00_u03c3s_653_, v_hyps_654_, v_target_655_, v_inst_656_, v_toBind_657_, v_a_658_, v_n_659_, v_f_660_, v_k_661_, v___x_662_, v___f_663_, v___x_664_, v_inst_665_, v_inst_666_, v___f_667_, v___f_668_, v_revertArgsTypes_669_);
return v_res_670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20(lean_object* v_inst_672_, lean_object* v_inst_673_, lean_object* v_u_674_, lean_object* v_00_u03c3s_675_, lean_object* v_hypName_676_, lean_object* v_hyps_677_, uint8_t v___x_678_, lean_object* v___f_679_, lean_object* v_revertArgs_680_, lean_object* v___f_681_, lean_object* v_target_682_, lean_object* v_a_683_, lean_object* v_n_684_, lean_object* v_f_685_, lean_object* v_k_686_, lean_object* v___x_687_, lean_object* v___f_688_, lean_object* v_inst_689_, lean_object* v_____r_690_){
_start:
{
lean_object* v_toApplicative_691_; lean_object* v_toBind_692_; lean_object* v___x_693_; lean_object* v_toApplicative_694_; lean_object* v_toFunctor_695_; lean_object* v_toSeq_696_; lean_object* v_toSeqLeft_697_; lean_object* v_toSeqRight_698_; lean_object* v___f_699_; lean_object* v___f_700_; lean_object* v___f_701_; lean_object* v___f_702_; lean_object* v___x_703_; lean_object* v___f_704_; lean_object* v___f_705_; lean_object* v___f_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v_toApplicative_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_747_; 
v_toApplicative_691_ = lean_ctor_get(v_inst_672_, 0);
lean_inc_ref(v_toApplicative_691_);
v_toBind_692_ = lean_ctor_get(v_inst_672_, 1);
lean_inc(v_toBind_692_);
v___x_693_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__1);
v_toApplicative_694_ = lean_ctor_get(v___x_693_, 0);
v_toFunctor_695_ = lean_ctor_get(v_toApplicative_694_, 0);
v_toSeq_696_ = lean_ctor_get(v_toApplicative_694_, 2);
v_toSeqLeft_697_ = lean_ctor_get(v_toApplicative_694_, 3);
v_toSeqRight_698_ = lean_ctor_get(v_toApplicative_694_, 4);
v___f_699_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__2));
v___f_700_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_695_, 2);
v___f_701_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_701_, 0, v_toFunctor_695_);
v___f_702_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_702_, 0, v_toFunctor_695_);
v___x_703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_703_, 0, v___f_701_);
lean_ctor_set(v___x_703_, 1, v___f_702_);
lean_inc(v_toSeqRight_698_);
v___f_704_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_704_, 0, v_toSeqRight_698_);
lean_inc(v_toSeqLeft_697_);
v___f_705_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_705_, 0, v_toSeqLeft_697_);
lean_inc(v_toSeq_696_);
v___f_706_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_706_, 0, v_toSeq_696_);
v___x_707_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_707_, 0, v___x_703_);
lean_ctor_set(v___x_707_, 1, v___f_699_);
lean_ctor_set(v___x_707_, 2, v___f_706_);
lean_ctor_set(v___x_707_, 3, v___f_705_);
lean_ctor_set(v___x_707_, 4, v___f_704_);
v___x_708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_708_, 0, v___x_707_);
lean_ctor_set(v___x_708_, 1, v___f_700_);
v___x_709_ = l_StateRefT_x27_instMonad___redArg(v___x_708_);
v_toApplicative_710_ = lean_ctor_get(v___x_709_, 0);
v_isSharedCheck_747_ = !lean_is_exclusive(v___x_709_);
if (v_isSharedCheck_747_ == 0)
{
lean_object* v_unused_748_; 
v_unused_748_ = lean_ctor_get(v___x_709_, 1);
lean_dec(v_unused_748_);
v___x_712_ = v___x_709_;
v_isShared_713_ = v_isSharedCheck_747_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_toApplicative_710_);
lean_dec(v___x_709_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_747_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v_toFunctor_714_; lean_object* v_toSeq_715_; lean_object* v_toSeqLeft_716_; lean_object* v_toSeqRight_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_745_; 
v_toFunctor_714_ = lean_ctor_get(v_toApplicative_710_, 0);
v_toSeq_715_ = lean_ctor_get(v_toApplicative_710_, 2);
v_toSeqLeft_716_ = lean_ctor_get(v_toApplicative_710_, 3);
v_toSeqRight_717_ = lean_ctor_get(v_toApplicative_710_, 4);
v_isSharedCheck_745_ = !lean_is_exclusive(v_toApplicative_710_);
if (v_isSharedCheck_745_ == 0)
{
lean_object* v_unused_746_; 
v_unused_746_ = lean_ctor_get(v_toApplicative_710_, 1);
lean_dec(v_unused_746_);
v___x_719_ = v_toApplicative_710_;
v_isShared_720_ = v_isSharedCheck_745_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_toSeqRight_717_);
lean_inc(v_toSeqLeft_716_);
lean_inc(v_toSeq_715_);
lean_inc(v_toFunctor_714_);
lean_dec(v_toApplicative_710_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_745_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v___f_721_; lean_object* v___x_722_; lean_object* v___f_723_; lean_object* v___f_724_; lean_object* v___f_725_; lean_object* v___f_726_; lean_object* v___f_727_; lean_object* v___x_728_; lean_object* v___f_729_; lean_object* v___f_730_; lean_object* v___f_731_; lean_object* v___x_733_; 
lean_inc_n(v_toBind_692_, 2);
lean_inc_n(v_inst_673_, 2);
lean_inc_ref_n(v_toApplicative_691_, 2);
v___f_721_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__6), 6, 3);
lean_closure_set(v___f_721_, 0, v_toApplicative_691_);
lean_closure_set(v___f_721_, 1, v_inst_673_);
lean_closure_set(v___f_721_, 2, v_toBind_692_);
v___x_722_ = lean_box(v___x_678_);
lean_inc_ref(v_inst_672_);
lean_inc_ref(v_revertArgs_680_);
lean_inc_ref(v_hyps_677_);
lean_inc_ref(v_00_u03c3s_675_);
lean_inc(v_u_674_);
v___f_723_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__11___boxed), 13, 12);
lean_closure_set(v___f_723_, 0, v_u_674_);
lean_closure_set(v___f_723_, 1, v_00_u03c3s_675_);
lean_closure_set(v___f_723_, 2, v_hypName_676_);
lean_closure_set(v___f_723_, 3, v_toApplicative_691_);
lean_closure_set(v___f_723_, 4, v_hyps_677_);
lean_closure_set(v___f_723_, 5, v___x_722_);
lean_closure_set(v___f_723_, 6, v_inst_673_);
lean_closure_set(v___f_723_, 7, v_toBind_692_);
lean_closure_set(v___f_723_, 8, v___f_679_);
lean_closure_set(v___f_723_, 9, v_revertArgs_680_);
lean_closure_set(v___f_723_, 10, v_inst_672_);
lean_closure_set(v___f_723_, 11, v___f_681_);
v___f_724_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__4));
v___f_725_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__5));
lean_inc_ref(v_toFunctor_714_);
v___f_726_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_726_, 0, v_toFunctor_714_);
v___f_727_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_727_, 0, v_toFunctor_714_);
v___x_728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_728_, 0, v___f_726_);
lean_ctor_set(v___x_728_, 1, v___f_727_);
v___f_729_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_729_, 0, v_toSeqRight_717_);
v___f_730_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_730_, 0, v_toSeqLeft_716_);
v___f_731_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_731_, 0, v_toSeq_715_);
if (v_isShared_720_ == 0)
{
lean_ctor_set(v___x_719_, 4, v___f_729_);
lean_ctor_set(v___x_719_, 3, v___f_730_);
lean_ctor_set(v___x_719_, 2, v___f_731_);
lean_ctor_set(v___x_719_, 1, v___f_724_);
lean_ctor_set(v___x_719_, 0, v___x_728_);
v___x_733_ = v___x_719_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v___x_728_);
lean_ctor_set(v_reuseFailAlloc_744_, 1, v___f_724_);
lean_ctor_set(v_reuseFailAlloc_744_, 2, v___f_731_);
lean_ctor_set(v_reuseFailAlloc_744_, 3, v___f_730_);
lean_ctor_set(v_reuseFailAlloc_744_, 4, v___f_729_);
v___x_733_ = v_reuseFailAlloc_744_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
lean_object* v___x_735_; 
if (v_isShared_713_ == 0)
{
lean_ctor_set(v___x_712_, 1, v___f_725_);
lean_ctor_set(v___x_712_, 0, v___x_733_);
v___x_735_ = v___x_712_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v___x_733_);
lean_ctor_set(v_reuseFailAlloc_743_, 1, v___f_725_);
v___x_735_ = v_reuseFailAlloc_743_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
lean_object* v___f_736_; lean_object* v___x_737_; size_t v_sz_738_; size_t v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; 
lean_inc_ref(v___x_735_);
lean_inc(v_toBind_692_);
lean_inc(v_inst_673_);
lean_inc_ref(v_revertArgs_680_);
v___f_736_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__19___boxed), 20, 19);
lean_closure_set(v___f_736_, 0, v_u_674_);
lean_closure_set(v___f_736_, 1, v_toApplicative_691_);
lean_closure_set(v___f_736_, 2, v_revertArgs_680_);
lean_closure_set(v___f_736_, 3, v_00_u03c3s_675_);
lean_closure_set(v___f_736_, 4, v_hyps_677_);
lean_closure_set(v___f_736_, 5, v_target_682_);
lean_closure_set(v___f_736_, 6, v_inst_673_);
lean_closure_set(v___f_736_, 7, v_toBind_692_);
lean_closure_set(v___f_736_, 8, v_a_683_);
lean_closure_set(v___f_736_, 9, v_n_684_);
lean_closure_set(v___f_736_, 10, v_f_685_);
lean_closure_set(v___f_736_, 11, v_k_686_);
lean_closure_set(v___f_736_, 12, v___x_687_);
lean_closure_set(v___f_736_, 13, v___f_688_);
lean_closure_set(v___f_736_, 14, v___x_735_);
lean_closure_set(v___f_736_, 15, v_inst_689_);
lean_closure_set(v___f_736_, 16, v_inst_672_);
lean_closure_set(v___f_736_, 17, v___f_723_);
lean_closure_set(v___f_736_, 18, v___f_721_);
v___x_737_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__0));
v_sz_738_ = lean_array_size(v_revertArgs_680_);
v___x_739_ = ((size_t)0ULL);
v___x_740_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_735_, v___x_737_, v_sz_738_, v___x_739_, v_revertArgs_680_);
v___x_741_ = lean_apply_2(v_inst_673_, lean_box(0), v___x_740_);
v___x_742_ = lean_apply_4(v_toBind_692_, lean_box(0), lean_box(0), v___x_741_, v___f_736_);
return v___x_742_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___boxed(lean_object** _args){
lean_object* v_inst_749_ = _args[0];
lean_object* v_inst_750_ = _args[1];
lean_object* v_u_751_ = _args[2];
lean_object* v_00_u03c3s_752_ = _args[3];
lean_object* v_hypName_753_ = _args[4];
lean_object* v_hyps_754_ = _args[5];
lean_object* v___x_755_ = _args[6];
lean_object* v___f_756_ = _args[7];
lean_object* v_revertArgs_757_ = _args[8];
lean_object* v___f_758_ = _args[9];
lean_object* v_target_759_ = _args[10];
lean_object* v_a_760_ = _args[11];
lean_object* v_n_761_ = _args[12];
lean_object* v_f_762_ = _args[13];
lean_object* v_k_763_ = _args[14];
lean_object* v___x_764_ = _args[15];
lean_object* v___f_765_ = _args[16];
lean_object* v_inst_766_ = _args[17];
lean_object* v_____r_767_ = _args[18];
_start:
{
uint8_t v___x_1537__boxed_768_; lean_object* v_res_769_; 
v___x_1537__boxed_768_ = lean_unbox(v___x_755_);
v_res_769_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20(v_inst_749_, v_inst_750_, v_u_751_, v_00_u03c3s_752_, v_hypName_753_, v_hyps_754_, v___x_1537__boxed_768_, v___f_756_, v_revertArgs_757_, v___f_758_, v_target_759_, v_a_760_, v_n_761_, v_f_762_, v_k_763_, v___x_764_, v___f_765_, v_inst_766_, v_____r_767_);
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__21(lean_object* v___f_770_, lean_object* v_____r_771_){
_start:
{
lean_object* v___x_772_; 
v___x_772_ = lean_apply_1(v___f_770_, v_____r_771_);
return v___x_772_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__3(void){
_start:
{
lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_777_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__2));
v___x_778_ = l_Lean_stringToMessageData(v___x_777_);
return v___x_778_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__5(void){
_start:
{
lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_780_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__4));
v___x_781_ = l_Lean_stringToMessageData(v___x_780_);
return v___x_781_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__7(void){
_start:
{
lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_783_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__6));
v___x_784_ = l_Lean_stringToMessageData(v___x_783_);
return v___x_784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg(lean_object* v_inst_785_, lean_object* v_inst_786_, lean_object* v_inst_787_, lean_object* v_goal_788_, lean_object* v_n_789_, lean_object* v_hypName_790_, lean_object* v_k_791_){
_start:
{
lean_object* v___x_792_; uint8_t v___x_793_; 
v___x_792_ = lean_unsigned_to_nat(0u);
v___x_793_ = lean_nat_dec_eq(v_n_789_, v___x_792_);
if (v___x_793_ == 0)
{
lean_object* v_u_794_; lean_object* v_00_u03c3s_795_; lean_object* v_hyps_796_; lean_object* v_target_797_; lean_object* v___f_798_; lean_object* v___f_799_; lean_object* v___f_800_; lean_object* v___f_801_; lean_object* v_T_802_; lean_object* v_f_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v_a_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v_revertArgs_810_; lean_object* v___x_811_; lean_object* v___f_812_; lean_object* v___x_813_; uint8_t v___x_814_; 
v_u_794_ = lean_ctor_get(v_goal_788_, 0);
lean_inc_n(v_u_794_, 3);
v_00_u03c3s_795_ = lean_ctor_get(v_goal_788_, 1);
lean_inc_ref_n(v_00_u03c3s_795_, 2);
v_hyps_796_ = lean_ctor_get(v_goal_788_, 2);
lean_inc_ref_n(v_hyps_796_, 2);
v_target_797_ = lean_ctor_get(v_goal_788_, 3);
lean_inc_ref_n(v_target_797_, 2);
lean_dec_ref(v_goal_788_);
lean_inc_n(v_inst_787_, 2);
v___f_798_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__0), 2, 1);
lean_closure_set(v___f_798_, 0, v_inst_787_);
lean_inc_n(v_hypName_790_, 2);
v___f_799_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__1___boxed), 6, 1);
lean_closure_set(v___f_799_, 0, v_hypName_790_);
v___f_800_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__0));
v___f_801_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__3), 3, 1);
lean_closure_set(v___f_801_, 0, v_u_794_);
v_T_802_ = l_Lean_Expr_consumeMData(v_target_797_);
v_f_803_ = l_Lean_Expr_getAppFn(v_T_802_);
v___x_804_ = l_Lean_Expr_getAppNumArgs(v_T_802_);
v___x_805_ = lean_mk_empty_array_with_capacity(v___x_804_);
lean_dec(v___x_804_);
lean_inc_ref(v_T_802_);
v_a_806_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_T_802_, v___x_805_);
lean_inc_n(v_n_789_, 2);
lean_inc_ref_n(v_a_806_, 2);
v___x_807_ = l_Array_toSubarray___redArg(v_a_806_, v___x_792_, v_n_789_);
v___x_808_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__1));
v___x_809_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_800_, v___x_807_, v___x_808_);
v_revertArgs_810_ = l_Array_reverse___redArg(v___x_809_);
v___x_811_ = lean_box(v___x_793_);
lean_inc_ref(v_inst_786_);
lean_inc_ref(v___f_801_);
lean_inc(v_k_791_);
lean_inc_ref(v_f_803_);
lean_inc_ref(v___f_798_);
lean_inc_ref(v_revertArgs_810_);
lean_inc_ref(v___f_799_);
lean_inc_ref(v_inst_785_);
v___f_812_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___boxed), 19, 18);
lean_closure_set(v___f_812_, 0, v_inst_785_);
lean_closure_set(v___f_812_, 1, v_inst_787_);
lean_closure_set(v___f_812_, 2, v_u_794_);
lean_closure_set(v___f_812_, 3, v_00_u03c3s_795_);
lean_closure_set(v___f_812_, 4, v_hypName_790_);
lean_closure_set(v___f_812_, 5, v_hyps_796_);
lean_closure_set(v___f_812_, 6, v___x_811_);
lean_closure_set(v___f_812_, 7, v___f_799_);
lean_closure_set(v___f_812_, 8, v_revertArgs_810_);
lean_closure_set(v___f_812_, 9, v___f_798_);
lean_closure_set(v___f_812_, 10, v_target_797_);
lean_closure_set(v___f_812_, 11, v_a_806_);
lean_closure_set(v___f_812_, 12, v_n_789_);
lean_closure_set(v___f_812_, 13, v_f_803_);
lean_closure_set(v___f_812_, 14, v_k_791_);
lean_closure_set(v___f_812_, 15, v___x_792_);
lean_closure_set(v___f_812_, 16, v___f_801_);
lean_closure_set(v___f_812_, 17, v_inst_786_);
v___x_813_ = lean_array_get_size(v_revertArgs_810_);
v___x_814_ = lean_nat_dec_eq(v___x_813_, v_n_789_);
if (v___x_814_ == 0)
{
lean_object* v_toBind_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_892_; 
lean_dec_ref(v_revertArgs_810_);
lean_dec_ref(v_a_806_);
lean_dec_ref(v_f_803_);
lean_dec_ref(v___f_801_);
lean_dec_ref(v___f_799_);
lean_dec_ref(v___f_798_);
lean_dec_ref(v_target_797_);
lean_dec_ref(v_hyps_796_);
lean_dec_ref(v_00_u03c3s_795_);
lean_dec(v_u_794_);
lean_dec(v_k_791_);
lean_dec(v_hypName_790_);
lean_dec_ref(v_inst_786_);
v_toBind_815_ = lean_ctor_get(v_inst_785_, 1);
v_isSharedCheck_892_ = !lean_is_exclusive(v_inst_785_);
if (v_isSharedCheck_892_ == 0)
{
lean_object* v_unused_893_; 
v_unused_893_ = lean_ctor_get(v_inst_785_, 0);
lean_dec(v_unused_893_);
v___x_817_ = v_inst_785_;
v_isShared_818_ = v_isSharedCheck_892_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_toBind_815_);
lean_dec(v_inst_785_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_892_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v___x_819_; lean_object* v_toApplicative_820_; lean_object* v_toFunctor_821_; lean_object* v_toSeq_822_; lean_object* v_toSeqLeft_823_; lean_object* v_toSeqRight_824_; lean_object* v___f_825_; lean_object* v___f_826_; lean_object* v___f_827_; lean_object* v___f_828_; lean_object* v___x_829_; lean_object* v___f_830_; lean_object* v___f_831_; lean_object* v___f_832_; lean_object* v___x_833_; lean_object* v___x_835_; 
v___x_819_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__1);
v_toApplicative_820_ = lean_ctor_get(v___x_819_, 0);
v_toFunctor_821_ = lean_ctor_get(v_toApplicative_820_, 0);
v_toSeq_822_ = lean_ctor_get(v_toApplicative_820_, 2);
v_toSeqLeft_823_ = lean_ctor_get(v_toApplicative_820_, 3);
v_toSeqRight_824_ = lean_ctor_get(v_toApplicative_820_, 4);
v___f_825_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__2));
v___f_826_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_821_, 2);
v___f_827_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_827_, 0, v_toFunctor_821_);
v___f_828_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_828_, 0, v_toFunctor_821_);
v___x_829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_829_, 0, v___f_827_);
lean_ctor_set(v___x_829_, 1, v___f_828_);
lean_inc(v_toSeqRight_824_);
v___f_830_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_830_, 0, v_toSeqRight_824_);
lean_inc(v_toSeqLeft_823_);
v___f_831_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_831_, 0, v_toSeqLeft_823_);
lean_inc(v_toSeq_822_);
v___f_832_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_832_, 0, v_toSeq_822_);
v___x_833_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_833_, 0, v___x_829_);
lean_ctor_set(v___x_833_, 1, v___f_825_);
lean_ctor_set(v___x_833_, 2, v___f_832_);
lean_ctor_set(v___x_833_, 3, v___f_831_);
lean_ctor_set(v___x_833_, 4, v___f_830_);
if (v_isShared_818_ == 0)
{
lean_ctor_set(v___x_817_, 1, v___f_826_);
lean_ctor_set(v___x_817_, 0, v___x_833_);
v___x_835_ = v___x_817_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v___x_833_);
lean_ctor_set(v_reuseFailAlloc_891_, 1, v___f_826_);
v___x_835_ = v_reuseFailAlloc_891_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
lean_object* v___x_836_; lean_object* v_toApplicative_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_889_; 
v___x_836_ = l_StateRefT_x27_instMonad___redArg(v___x_835_);
v_toApplicative_837_ = lean_ctor_get(v___x_836_, 0);
v_isSharedCheck_889_ = !lean_is_exclusive(v___x_836_);
if (v_isSharedCheck_889_ == 0)
{
lean_object* v_unused_890_; 
v_unused_890_ = lean_ctor_get(v___x_836_, 1);
lean_dec(v_unused_890_);
v___x_839_ = v___x_836_;
v_isShared_840_ = v_isSharedCheck_889_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_toApplicative_837_);
lean_dec(v___x_836_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_889_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v_toFunctor_841_; lean_object* v_toSeq_842_; lean_object* v_toSeqLeft_843_; lean_object* v_toSeqRight_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_887_; 
v_toFunctor_841_ = lean_ctor_get(v_toApplicative_837_, 0);
v_toSeq_842_ = lean_ctor_get(v_toApplicative_837_, 2);
v_toSeqLeft_843_ = lean_ctor_get(v_toApplicative_837_, 3);
v_toSeqRight_844_ = lean_ctor_get(v_toApplicative_837_, 4);
v_isSharedCheck_887_ = !lean_is_exclusive(v_toApplicative_837_);
if (v_isSharedCheck_887_ == 0)
{
lean_object* v_unused_888_; 
v_unused_888_ = lean_ctor_get(v_toApplicative_837_, 1);
lean_dec(v_unused_888_);
v___x_846_ = v_toApplicative_837_;
v_isShared_847_ = v_isSharedCheck_887_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_toSeqRight_844_);
lean_inc(v_toSeqLeft_843_);
lean_inc(v_toSeq_842_);
lean_inc(v_toFunctor_841_);
lean_dec(v_toApplicative_837_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_887_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___f_848_; lean_object* v___f_849_; lean_object* v___f_850_; lean_object* v___f_851_; lean_object* v___x_852_; lean_object* v___f_853_; lean_object* v___f_854_; lean_object* v___f_855_; lean_object* v___x_857_; 
v___f_848_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__4));
v___f_849_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__5));
lean_inc_ref(v_toFunctor_841_);
v___f_850_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_850_, 0, v_toFunctor_841_);
v___f_851_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_851_, 0, v_toFunctor_841_);
v___x_852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_852_, 0, v___f_850_);
lean_ctor_set(v___x_852_, 1, v___f_851_);
v___f_853_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_853_, 0, v_toSeqRight_844_);
v___f_854_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_854_, 0, v_toSeqLeft_843_);
v___f_855_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_855_, 0, v_toSeq_842_);
if (v_isShared_847_ == 0)
{
lean_ctor_set(v___x_846_, 4, v___f_853_);
lean_ctor_set(v___x_846_, 3, v___f_854_);
lean_ctor_set(v___x_846_, 2, v___f_855_);
lean_ctor_set(v___x_846_, 1, v___f_848_);
lean_ctor_set(v___x_846_, 0, v___x_852_);
v___x_857_ = v___x_846_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v___x_852_);
lean_ctor_set(v_reuseFailAlloc_886_, 1, v___f_848_);
lean_ctor_set(v_reuseFailAlloc_886_, 2, v___f_855_);
lean_ctor_set(v_reuseFailAlloc_886_, 3, v___f_854_);
lean_ctor_set(v_reuseFailAlloc_886_, 4, v___f_853_);
v___x_857_ = v_reuseFailAlloc_886_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
lean_object* v___x_859_; 
if (v_isShared_840_ == 0)
{
lean_ctor_set(v___x_839_, 1, v___f_849_);
lean_ctor_set(v___x_839_, 0, v___x_857_);
v___x_859_ = v___x_839_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v___x_857_);
lean_ctor_set(v_reuseFailAlloc_885_, 1, v___f_849_);
v___x_859_ = v_reuseFailAlloc_885_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v_toMonadRef_862_; lean_object* v___f_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_860_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__11, &l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__11_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__11);
v___x_861_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__17, &l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__17_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__17);
v_toMonadRef_862_ = lean_ctor_get(v___x_861_, 0);
v___f_863_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__21), 2, 1);
lean_closure_set(v___f_863_, 0, v___f_812_);
v___x_864_ = l_Lean_Meta_instAddMessageContextMetaM;
lean_inc_ref(v___x_859_);
v___x_865_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___x_864_, v___x_859_);
lean_inc_ref(v_toMonadRef_862_);
v___x_866_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_866_, 0, v___x_860_);
lean_ctor_set(v___x_866_, 1, v_toMonadRef_862_);
lean_ctor_set(v___x_866_, 2, v___x_865_);
v___x_867_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__3, &l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__3_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__3);
v___x_868_ = l_Nat_reprFast(v_n_789_);
v___x_869_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_869_, 0, v___x_868_);
v___x_870_ = l_Lean_MessageData_ofFormat(v___x_869_);
v___x_871_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_871_, 0, v___x_867_);
lean_ctor_set(v___x_871_, 1, v___x_870_);
v___x_872_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__5, &l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__5_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__5);
v___x_873_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_873_, 0, v___x_871_);
lean_ctor_set(v___x_873_, 1, v___x_872_);
v___x_874_ = l_Lean_MessageData_ofExpr(v_T_802_);
v___x_875_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_875_, 0, v___x_873_);
lean_ctor_set(v___x_875_, 1, v___x_874_);
v___x_876_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__7, &l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__7_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__7);
v___x_877_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_877_, 0, v___x_875_);
lean_ctor_set(v___x_877_, 1, v___x_876_);
v___x_878_ = l_Nat_reprFast(v___x_813_);
v___x_879_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_879_, 0, v___x_878_);
v___x_880_ = l_Lean_MessageData_ofFormat(v___x_879_);
v___x_881_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_881_, 0, v___x_877_);
lean_ctor_set(v___x_881_, 1, v___x_880_);
v___x_882_ = l_Lean_throwError___redArg(v___x_859_, v___x_866_, v___x_881_);
v___x_883_ = lean_apply_2(v_inst_787_, lean_box(0), v___x_882_);
v___x_884_ = lean_apply_4(v_toBind_815_, lean_box(0), lean_box(0), v___x_883_, v___f_863_);
return v___x_884_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_894_; lean_object* v___x_895_; 
lean_dec_ref(v___f_812_);
lean_dec_ref(v_T_802_);
v___x_894_ = lean_box(0);
v___x_895_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20(v_inst_785_, v_inst_787_, v_u_794_, v_00_u03c3s_795_, v_hypName_790_, v_hyps_796_, v___x_793_, v___f_799_, v_revertArgs_810_, v___f_798_, v_target_797_, v_a_806_, v_n_789_, v_f_803_, v_k_791_, v___x_792_, v___f_801_, v_inst_786_, v___x_894_);
return v___x_895_;
}
}
else
{
lean_object* v___x_896_; 
lean_dec(v_hypName_790_);
lean_dec(v_n_789_);
lean_dec(v_inst_787_);
lean_dec_ref(v_inst_786_);
lean_dec_ref(v_inst_785_);
v___x_896_ = lean_apply_1(v_k_791_, v_goal_788_);
return v___x_896_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN(lean_object* v_m_897_, lean_object* v_inst_898_, lean_object* v_inst_899_, lean_object* v_inst_900_, lean_object* v_goal_901_, lean_object* v_n_902_, lean_object* v_hypName_903_, lean_object* v_k_904_){
_start:
{
lean_object* v___x_905_; 
v___x_905_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg(v_inst_898_, v_inst_899_, v_inst_900_, v_goal_901_, v_n_902_, v_hypName_903_, v_k_904_);
return v___x_905_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; 
v___x_906_ = lean_box(0);
v___x_907_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_908_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_908_, 0, v___x_907_);
lean_ctor_set(v___x_908_, 1, v___x_906_);
return v___x_908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg(){
_start:
{
lean_object* v___x_910_; lean_object* v___x_911_; 
v___x_910_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg___closed__0);
v___x_911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_911_, 0, v___x_910_);
return v___x_911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg___boxed(lean_object* v___y_912_){
_start:
{
lean_object* v_res_913_; 
v_res_913_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg();
return v_res_913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0(lean_object* v_00_u03b1_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_){
_start:
{
lean_object* v___x_924_; 
v___x_924_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg();
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___boxed(lean_object* v_00_u03b1_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_){
_start:
{
lean_object* v_res_935_; 
v_res_935_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0(v_00_u03b1_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
lean_dec(v___y_931_);
lean_dec_ref(v___y_930_);
lean_dec(v___y_929_);
lean_dec_ref(v___y_928_);
lean_dec(v___y_927_);
lean_dec_ref(v___y_926_);
return v_res_935_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___redArg___lam__0(lean_object* v_x_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_){
_start:
{
lean_object* v___x_946_; 
lean_inc(v___y_940_);
lean_inc_ref(v___y_939_);
lean_inc(v___y_938_);
lean_inc_ref(v___y_937_);
v___x_946_ = lean_apply_9(v_x_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, lean_box(0));
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___redArg___lam__0___boxed(lean_object* v_x_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_){
_start:
{
lean_object* v_res_957_; 
v_res_957_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___redArg___lam__0(v_x_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_);
lean_dec(v___y_951_);
lean_dec_ref(v___y_950_);
lean_dec(v___y_949_);
lean_dec_ref(v___y_948_);
return v_res_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___redArg(lean_object* v_mvarId_958_, lean_object* v_x_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_){
_start:
{
lean_object* v___f_969_; lean_object* v___x_970_; 
lean_inc(v___y_963_);
lean_inc_ref(v___y_962_);
lean_inc(v___y_961_);
lean_inc_ref(v___y_960_);
v___f_969_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_969_, 0, v_x_959_);
lean_closure_set(v___f_969_, 1, v___y_960_);
lean_closure_set(v___f_969_, 2, v___y_961_);
lean_closure_set(v___f_969_, 3, v___y_962_);
lean_closure_set(v___f_969_, 4, v___y_963_);
v___x_970_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_958_, v___f_969_, v___y_964_, v___y_965_, v___y_966_, v___y_967_);
if (lean_obj_tag(v___x_970_) == 0)
{
return v___x_970_;
}
else
{
lean_object* v_a_971_; lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_978_; 
v_a_971_ = lean_ctor_get(v___x_970_, 0);
v_isSharedCheck_978_ = !lean_is_exclusive(v___x_970_);
if (v_isSharedCheck_978_ == 0)
{
v___x_973_ = v___x_970_;
v_isShared_974_ = v_isSharedCheck_978_;
goto v_resetjp_972_;
}
else
{
lean_inc(v_a_971_);
lean_dec(v___x_970_);
v___x_973_ = lean_box(0);
v_isShared_974_ = v_isSharedCheck_978_;
goto v_resetjp_972_;
}
v_resetjp_972_:
{
lean_object* v___x_976_; 
if (v_isShared_974_ == 0)
{
v___x_976_ = v___x_973_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v_a_971_);
v___x_976_ = v_reuseFailAlloc_977_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
return v___x_976_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___redArg___boxed(lean_object* v_mvarId_979_, lean_object* v_x_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_){
_start:
{
lean_object* v_res_990_; 
v_res_990_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___redArg(v_mvarId_979_, v_x_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_);
lean_dec(v___y_988_);
lean_dec_ref(v___y_987_);
lean_dec(v___y_986_);
lean_dec_ref(v___y_985_);
lean_dec(v___y_984_);
lean_dec_ref(v___y_983_);
lean_dec(v___y_982_);
lean_dec_ref(v___y_981_);
return v_res_990_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3(lean_object* v_00_u03b1_991_, lean_object* v_mvarId_992_, lean_object* v_x_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_){
_start:
{
lean_object* v___x_1003_; 
v___x_1003_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___redArg(v_mvarId_992_, v_x_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_);
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___boxed(lean_object* v_00_u03b1_1004_, lean_object* v_mvarId_1005_, lean_object* v_x_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_){
_start:
{
lean_object* v_res_1016_; 
v_res_1016_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3(v_00_u03b1_1004_, v_mvarId_1005_, v_x_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_);
lean_dec(v___y_1014_);
lean_dec_ref(v___y_1013_);
lean_dec(v___y_1012_);
lean_dec_ref(v___y_1011_);
lean_dec(v___y_1010_);
lean_dec_ref(v___y_1009_);
lean_dec(v___y_1008_);
lean_dec_ref(v___y_1007_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__0(lean_object* v_val_1017_, lean_object* v_newGoal_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_){
_start:
{
lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1028_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v_newGoal_1018_);
v___x_1029_ = lean_box(0);
v___x_1030_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_1028_, v___x_1029_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_);
if (lean_obj_tag(v___x_1030_) == 0)
{
lean_object* v_a_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1042_; 
v_a_1031_ = lean_ctor_get(v___x_1030_, 0);
v_isSharedCheck_1042_ = !lean_is_exclusive(v___x_1030_);
if (v_isSharedCheck_1042_ == 0)
{
v___x_1033_ = v___x_1030_;
v_isShared_1034_ = v_isSharedCheck_1042_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_a_1031_);
lean_dec(v___x_1030_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1042_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1040_; 
v___x_1035_ = lean_st_ref_take(v_val_1017_);
v___x_1036_ = l_Lean_Expr_mvarId_x21(v_a_1031_);
v___x_1037_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1036_);
lean_ctor_set(v___x_1037_, 1, v___x_1035_);
v___x_1038_ = lean_st_ref_set(v_val_1017_, v___x_1037_);
if (v_isShared_1034_ == 0)
{
v___x_1040_ = v___x_1033_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v_a_1031_);
v___x_1040_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
return v___x_1040_;
}
}
}
else
{
return v___x_1030_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__0___boxed(lean_object* v_val_1043_, lean_object* v_newGoal_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_){
_start:
{
lean_object* v_res_1054_; 
v_res_1054_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__0(v_val_1043_, v_newGoal_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_);
lean_dec(v___y_1052_);
lean_dec_ref(v___y_1051_);
lean_dec(v___y_1050_);
lean_dec_ref(v___y_1049_);
lean_dec(v___y_1048_);
lean_dec_ref(v___y_1047_);
lean_dec(v___y_1046_);
lean_dec_ref(v___y_1045_);
lean_dec(v_val_1043_);
return v_res_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14_spec__20_spec__22___redArg(lean_object* v_x_1055_, lean_object* v_x_1056_, lean_object* v_x_1057_, lean_object* v_x_1058_){
_start:
{
lean_object* v_ks_1059_; lean_object* v_vs_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1084_; 
v_ks_1059_ = lean_ctor_get(v_x_1055_, 0);
v_vs_1060_ = lean_ctor_get(v_x_1055_, 1);
v_isSharedCheck_1084_ = !lean_is_exclusive(v_x_1055_);
if (v_isSharedCheck_1084_ == 0)
{
v___x_1062_ = v_x_1055_;
v_isShared_1063_ = v_isSharedCheck_1084_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_vs_1060_);
lean_inc(v_ks_1059_);
lean_dec(v_x_1055_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1084_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
lean_object* v___x_1064_; uint8_t v___x_1065_; 
v___x_1064_ = lean_array_get_size(v_ks_1059_);
v___x_1065_ = lean_nat_dec_lt(v_x_1056_, v___x_1064_);
if (v___x_1065_ == 0)
{
lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1069_; 
lean_dec(v_x_1056_);
v___x_1066_ = lean_array_push(v_ks_1059_, v_x_1057_);
v___x_1067_ = lean_array_push(v_vs_1060_, v_x_1058_);
if (v_isShared_1063_ == 0)
{
lean_ctor_set(v___x_1062_, 1, v___x_1067_);
lean_ctor_set(v___x_1062_, 0, v___x_1066_);
v___x_1069_ = v___x_1062_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v___x_1066_);
lean_ctor_set(v_reuseFailAlloc_1070_, 1, v___x_1067_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
return v___x_1069_;
}
}
else
{
lean_object* v_k_x27_1071_; uint8_t v___x_1072_; 
v_k_x27_1071_ = lean_array_fget_borrowed(v_ks_1059_, v_x_1056_);
v___x_1072_ = l_Lean_instBEqMVarId_beq(v_x_1057_, v_k_x27_1071_);
if (v___x_1072_ == 0)
{
lean_object* v___x_1074_; 
if (v_isShared_1063_ == 0)
{
v___x_1074_ = v___x_1062_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v_ks_1059_);
lean_ctor_set(v_reuseFailAlloc_1078_, 1, v_vs_1060_);
v___x_1074_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; 
v___x_1075_ = lean_unsigned_to_nat(1u);
v___x_1076_ = lean_nat_add(v_x_1056_, v___x_1075_);
lean_dec(v_x_1056_);
v_x_1055_ = v___x_1074_;
v_x_1056_ = v___x_1076_;
goto _start;
}
}
else
{
lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1082_; 
v___x_1079_ = lean_array_fset(v_ks_1059_, v_x_1056_, v_x_1057_);
v___x_1080_ = lean_array_fset(v_vs_1060_, v_x_1056_, v_x_1058_);
lean_dec(v_x_1056_);
if (v_isShared_1063_ == 0)
{
lean_ctor_set(v___x_1062_, 1, v___x_1080_);
lean_ctor_set(v___x_1062_, 0, v___x_1079_);
v___x_1082_ = v___x_1062_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v___x_1079_);
lean_ctor_set(v_reuseFailAlloc_1083_, 1, v___x_1080_);
v___x_1082_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
return v___x_1082_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14_spec__20___redArg(lean_object* v_n_1085_, lean_object* v_k_1086_, lean_object* v_v_1087_){
_start:
{
lean_object* v___x_1088_; lean_object* v___x_1089_; 
v___x_1088_ = lean_unsigned_to_nat(0u);
v___x_1089_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14_spec__20_spec__22___redArg(v_n_1085_, v___x_1088_, v_k_1086_, v_v_1087_);
return v___x_1089_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14___redArg___closed__0(void){
_start:
{
lean_object* v___x_1090_; 
v___x_1090_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1090_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14___redArg(lean_object* v_x_1091_, size_t v_x_1092_, size_t v_x_1093_, lean_object* v_x_1094_, lean_object* v_x_1095_){
_start:
{
if (lean_obj_tag(v_x_1091_) == 0)
{
lean_object* v_es_1096_; size_t v___x_1097_; size_t v___x_1098_; lean_object* v_j_1099_; lean_object* v___x_1100_; uint8_t v___x_1101_; 
v_es_1096_ = lean_ctor_get(v_x_1091_, 0);
v___x_1097_ = ((size_t)31ULL);
v___x_1098_ = lean_usize_land(v_x_1092_, v___x_1097_);
v_j_1099_ = lean_usize_to_nat(v___x_1098_);
v___x_1100_ = lean_array_get_size(v_es_1096_);
v___x_1101_ = lean_nat_dec_lt(v_j_1099_, v___x_1100_);
if (v___x_1101_ == 0)
{
lean_dec(v_j_1099_);
lean_dec(v_x_1095_);
lean_dec(v_x_1094_);
return v_x_1091_;
}
else
{
lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1140_; 
lean_inc_ref(v_es_1096_);
v_isSharedCheck_1140_ = !lean_is_exclusive(v_x_1091_);
if (v_isSharedCheck_1140_ == 0)
{
lean_object* v_unused_1141_; 
v_unused_1141_ = lean_ctor_get(v_x_1091_, 0);
lean_dec(v_unused_1141_);
v___x_1103_ = v_x_1091_;
v_isShared_1104_ = v_isSharedCheck_1140_;
goto v_resetjp_1102_;
}
else
{
lean_dec(v_x_1091_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1140_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v_v_1105_; lean_object* v___x_1106_; lean_object* v_xs_x27_1107_; lean_object* v___y_1109_; 
v_v_1105_ = lean_array_fget(v_es_1096_, v_j_1099_);
v___x_1106_ = lean_box(0);
v_xs_x27_1107_ = lean_array_fset(v_es_1096_, v_j_1099_, v___x_1106_);
switch(lean_obj_tag(v_v_1105_))
{
case 0:
{
lean_object* v_key_1114_; lean_object* v_val_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1125_; 
v_key_1114_ = lean_ctor_get(v_v_1105_, 0);
v_val_1115_ = lean_ctor_get(v_v_1105_, 1);
v_isSharedCheck_1125_ = !lean_is_exclusive(v_v_1105_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1117_ = v_v_1105_;
v_isShared_1118_ = v_isSharedCheck_1125_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_val_1115_);
lean_inc(v_key_1114_);
lean_dec(v_v_1105_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1125_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
uint8_t v___x_1119_; 
v___x_1119_ = l_Lean_instBEqMVarId_beq(v_x_1094_, v_key_1114_);
if (v___x_1119_ == 0)
{
lean_object* v___x_1120_; lean_object* v___x_1121_; 
lean_del_object(v___x_1117_);
v___x_1120_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1114_, v_val_1115_, v_x_1094_, v_x_1095_);
v___x_1121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1121_, 0, v___x_1120_);
v___y_1109_ = v___x_1121_;
goto v___jp_1108_;
}
else
{
lean_object* v___x_1123_; 
lean_dec(v_val_1115_);
lean_dec(v_key_1114_);
if (v_isShared_1118_ == 0)
{
lean_ctor_set(v___x_1117_, 1, v_x_1095_);
lean_ctor_set(v___x_1117_, 0, v_x_1094_);
v___x_1123_ = v___x_1117_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v_x_1094_);
lean_ctor_set(v_reuseFailAlloc_1124_, 1, v_x_1095_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
v___y_1109_ = v___x_1123_;
goto v___jp_1108_;
}
}
}
}
case 1:
{
lean_object* v_node_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1138_; 
v_node_1126_ = lean_ctor_get(v_v_1105_, 0);
v_isSharedCheck_1138_ = !lean_is_exclusive(v_v_1105_);
if (v_isSharedCheck_1138_ == 0)
{
v___x_1128_ = v_v_1105_;
v_isShared_1129_ = v_isSharedCheck_1138_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_node_1126_);
lean_dec(v_v_1105_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1138_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
size_t v___x_1130_; size_t v___x_1131_; size_t v___x_1132_; size_t v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1136_; 
v___x_1130_ = ((size_t)5ULL);
v___x_1131_ = lean_usize_shift_right(v_x_1092_, v___x_1130_);
v___x_1132_ = ((size_t)1ULL);
v___x_1133_ = lean_usize_add(v_x_1093_, v___x_1132_);
v___x_1134_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14___redArg(v_node_1126_, v___x_1131_, v___x_1133_, v_x_1094_, v_x_1095_);
if (v_isShared_1129_ == 0)
{
lean_ctor_set(v___x_1128_, 0, v___x_1134_);
v___x_1136_ = v___x_1128_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v___x_1134_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
v___y_1109_ = v___x_1136_;
goto v___jp_1108_;
}
}
}
default: 
{
lean_object* v___x_1139_; 
v___x_1139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1139_, 0, v_x_1094_);
lean_ctor_set(v___x_1139_, 1, v_x_1095_);
v___y_1109_ = v___x_1139_;
goto v___jp_1108_;
}
}
v___jp_1108_:
{
lean_object* v___x_1110_; lean_object* v___x_1112_; 
v___x_1110_ = lean_array_fset(v_xs_x27_1107_, v_j_1099_, v___y_1109_);
lean_dec(v_j_1099_);
if (v_isShared_1104_ == 0)
{
lean_ctor_set(v___x_1103_, 0, v___x_1110_);
v___x_1112_ = v___x_1103_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v___x_1110_);
v___x_1112_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
return v___x_1112_;
}
}
}
}
}
else
{
lean_object* v_ks_1142_; lean_object* v_vs_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1163_; 
v_ks_1142_ = lean_ctor_get(v_x_1091_, 0);
v_vs_1143_ = lean_ctor_get(v_x_1091_, 1);
v_isSharedCheck_1163_ = !lean_is_exclusive(v_x_1091_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1145_ = v_x_1091_;
v_isShared_1146_ = v_isSharedCheck_1163_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_vs_1143_);
lean_inc(v_ks_1142_);
lean_dec(v_x_1091_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1163_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1148_; 
if (v_isShared_1146_ == 0)
{
v___x_1148_ = v___x_1145_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v_ks_1142_);
lean_ctor_set(v_reuseFailAlloc_1162_, 1, v_vs_1143_);
v___x_1148_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
lean_object* v_newNode_1149_; uint8_t v___y_1151_; size_t v___x_1157_; uint8_t v___x_1158_; 
v_newNode_1149_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14_spec__20___redArg(v___x_1148_, v_x_1094_, v_x_1095_);
v___x_1157_ = ((size_t)7ULL);
v___x_1158_ = lean_usize_dec_le(v___x_1157_, v_x_1093_);
if (v___x_1158_ == 0)
{
lean_object* v___x_1159_; lean_object* v___x_1160_; uint8_t v___x_1161_; 
v___x_1159_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1149_);
v___x_1160_ = lean_unsigned_to_nat(4u);
v___x_1161_ = lean_nat_dec_lt(v___x_1159_, v___x_1160_);
lean_dec(v___x_1159_);
v___y_1151_ = v___x_1161_;
goto v___jp_1150_;
}
else
{
v___y_1151_ = v___x_1158_;
goto v___jp_1150_;
}
v___jp_1150_:
{
if (v___y_1151_ == 0)
{
lean_object* v_ks_1152_; lean_object* v_vs_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; 
v_ks_1152_ = lean_ctor_get(v_newNode_1149_, 0);
lean_inc_ref(v_ks_1152_);
v_vs_1153_ = lean_ctor_get(v_newNode_1149_, 1);
lean_inc_ref(v_vs_1153_);
lean_dec_ref(v_newNode_1149_);
v___x_1154_ = lean_unsigned_to_nat(0u);
v___x_1155_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14___redArg___closed__0);
v___x_1156_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14_spec__21___redArg(v_x_1093_, v_ks_1152_, v_vs_1153_, v___x_1154_, v___x_1155_);
lean_dec_ref(v_vs_1153_);
lean_dec_ref(v_ks_1152_);
return v___x_1156_;
}
else
{
return v_newNode_1149_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14_spec__21___redArg(size_t v_depth_1164_, lean_object* v_keys_1165_, lean_object* v_vals_1166_, lean_object* v_i_1167_, lean_object* v_entries_1168_){
_start:
{
lean_object* v___x_1169_; uint8_t v___x_1170_; 
v___x_1169_ = lean_array_get_size(v_keys_1165_);
v___x_1170_ = lean_nat_dec_lt(v_i_1167_, v___x_1169_);
if (v___x_1170_ == 0)
{
lean_dec(v_i_1167_);
return v_entries_1168_;
}
else
{
lean_object* v_k_1171_; lean_object* v_v_1172_; uint64_t v___x_1173_; size_t v_h_1174_; size_t v___x_1175_; lean_object* v___x_1176_; size_t v___x_1177_; size_t v___x_1178_; size_t v___x_1179_; size_t v_h_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; 
v_k_1171_ = lean_array_fget_borrowed(v_keys_1165_, v_i_1167_);
v_v_1172_ = lean_array_fget_borrowed(v_vals_1166_, v_i_1167_);
v___x_1173_ = l_Lean_instHashableMVarId_hash(v_k_1171_);
v_h_1174_ = lean_uint64_to_usize(v___x_1173_);
v___x_1175_ = ((size_t)5ULL);
v___x_1176_ = lean_unsigned_to_nat(1u);
v___x_1177_ = ((size_t)1ULL);
v___x_1178_ = lean_usize_sub(v_depth_1164_, v___x_1177_);
v___x_1179_ = lean_usize_mul(v___x_1175_, v___x_1178_);
v_h_1180_ = lean_usize_shift_right(v_h_1174_, v___x_1179_);
v___x_1181_ = lean_nat_add(v_i_1167_, v___x_1176_);
lean_dec(v_i_1167_);
lean_inc(v_v_1172_);
lean_inc(v_k_1171_);
v___x_1182_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14___redArg(v_entries_1168_, v_h_1180_, v_depth_1164_, v_k_1171_, v_v_1172_);
v_i_1167_ = v___x_1181_;
v_entries_1168_ = v___x_1182_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14_spec__21___redArg___boxed(lean_object* v_depth_1184_, lean_object* v_keys_1185_, lean_object* v_vals_1186_, lean_object* v_i_1187_, lean_object* v_entries_1188_){
_start:
{
size_t v_depth_boxed_1189_; lean_object* v_res_1190_; 
v_depth_boxed_1189_ = lean_unbox_usize(v_depth_1184_);
lean_dec(v_depth_1184_);
v_res_1190_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14_spec__21___redArg(v_depth_boxed_1189_, v_keys_1185_, v_vals_1186_, v_i_1187_, v_entries_1188_);
lean_dec_ref(v_vals_1186_);
lean_dec_ref(v_keys_1185_);
return v_res_1190_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14___redArg___boxed(lean_object* v_x_1191_, lean_object* v_x_1192_, lean_object* v_x_1193_, lean_object* v_x_1194_, lean_object* v_x_1195_){
_start:
{
size_t v_x_20343__boxed_1196_; size_t v_x_20344__boxed_1197_; lean_object* v_res_1198_; 
v_x_20343__boxed_1196_ = lean_unbox_usize(v_x_1192_);
lean_dec(v_x_1192_);
v_x_20344__boxed_1197_ = lean_unbox_usize(v_x_1193_);
lean_dec(v_x_1193_);
v_res_1198_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14___redArg(v_x_1191_, v_x_20343__boxed_1196_, v_x_20344__boxed_1197_, v_x_1194_, v_x_1195_);
return v_res_1198_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10___redArg(lean_object* v_x_1199_, lean_object* v_x_1200_, lean_object* v_x_1201_){
_start:
{
uint64_t v___x_1202_; size_t v___x_1203_; size_t v___x_1204_; lean_object* v___x_1205_; 
v___x_1202_ = l_Lean_instHashableMVarId_hash(v_x_1200_);
v___x_1203_ = lean_uint64_to_usize(v___x_1202_);
v___x_1204_ = ((size_t)1ULL);
v___x_1205_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14___redArg(v_x_1199_, v___x_1203_, v___x_1204_, v_x_1200_, v_x_1201_);
return v___x_1205_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2___redArg(lean_object* v_mvarId_1206_, lean_object* v_val_1207_, lean_object* v___y_1208_){
_start:
{
lean_object* v___x_1210_; lean_object* v_mctx_1211_; lean_object* v_cache_1212_; lean_object* v_zetaDeltaFVarIds_1213_; lean_object* v_postponed_1214_; lean_object* v_diag_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1243_; 
v___x_1210_ = lean_st_ref_take(v___y_1208_);
v_mctx_1211_ = lean_ctor_get(v___x_1210_, 0);
v_cache_1212_ = lean_ctor_get(v___x_1210_, 1);
v_zetaDeltaFVarIds_1213_ = lean_ctor_get(v___x_1210_, 2);
v_postponed_1214_ = lean_ctor_get(v___x_1210_, 3);
v_diag_1215_ = lean_ctor_get(v___x_1210_, 4);
v_isSharedCheck_1243_ = !lean_is_exclusive(v___x_1210_);
if (v_isSharedCheck_1243_ == 0)
{
v___x_1217_ = v___x_1210_;
v_isShared_1218_ = v_isSharedCheck_1243_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_diag_1215_);
lean_inc(v_postponed_1214_);
lean_inc(v_zetaDeltaFVarIds_1213_);
lean_inc(v_cache_1212_);
lean_inc(v_mctx_1211_);
lean_dec(v___x_1210_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1243_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v_depth_1219_; lean_object* v_levelAssignDepth_1220_; lean_object* v_lmvarCounter_1221_; lean_object* v_mvarCounter_1222_; lean_object* v_lDecls_1223_; lean_object* v_decls_1224_; lean_object* v_userNames_1225_; lean_object* v_lAssignment_1226_; lean_object* v_eAssignment_1227_; lean_object* v_dAssignment_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1242_; 
v_depth_1219_ = lean_ctor_get(v_mctx_1211_, 0);
v_levelAssignDepth_1220_ = lean_ctor_get(v_mctx_1211_, 1);
v_lmvarCounter_1221_ = lean_ctor_get(v_mctx_1211_, 2);
v_mvarCounter_1222_ = lean_ctor_get(v_mctx_1211_, 3);
v_lDecls_1223_ = lean_ctor_get(v_mctx_1211_, 4);
v_decls_1224_ = lean_ctor_get(v_mctx_1211_, 5);
v_userNames_1225_ = lean_ctor_get(v_mctx_1211_, 6);
v_lAssignment_1226_ = lean_ctor_get(v_mctx_1211_, 7);
v_eAssignment_1227_ = lean_ctor_get(v_mctx_1211_, 8);
v_dAssignment_1228_ = lean_ctor_get(v_mctx_1211_, 9);
v_isSharedCheck_1242_ = !lean_is_exclusive(v_mctx_1211_);
if (v_isSharedCheck_1242_ == 0)
{
v___x_1230_ = v_mctx_1211_;
v_isShared_1231_ = v_isSharedCheck_1242_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_dAssignment_1228_);
lean_inc(v_eAssignment_1227_);
lean_inc(v_lAssignment_1226_);
lean_inc(v_userNames_1225_);
lean_inc(v_decls_1224_);
lean_inc(v_lDecls_1223_);
lean_inc(v_mvarCounter_1222_);
lean_inc(v_lmvarCounter_1221_);
lean_inc(v_levelAssignDepth_1220_);
lean_inc(v_depth_1219_);
lean_dec(v_mctx_1211_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1242_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v___x_1232_; lean_object* v___x_1234_; 
v___x_1232_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10___redArg(v_eAssignment_1227_, v_mvarId_1206_, v_val_1207_);
if (v_isShared_1231_ == 0)
{
lean_ctor_set(v___x_1230_, 8, v___x_1232_);
v___x_1234_ = v___x_1230_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v_depth_1219_);
lean_ctor_set(v_reuseFailAlloc_1241_, 1, v_levelAssignDepth_1220_);
lean_ctor_set(v_reuseFailAlloc_1241_, 2, v_lmvarCounter_1221_);
lean_ctor_set(v_reuseFailAlloc_1241_, 3, v_mvarCounter_1222_);
lean_ctor_set(v_reuseFailAlloc_1241_, 4, v_lDecls_1223_);
lean_ctor_set(v_reuseFailAlloc_1241_, 5, v_decls_1224_);
lean_ctor_set(v_reuseFailAlloc_1241_, 6, v_userNames_1225_);
lean_ctor_set(v_reuseFailAlloc_1241_, 7, v_lAssignment_1226_);
lean_ctor_set(v_reuseFailAlloc_1241_, 8, v___x_1232_);
lean_ctor_set(v_reuseFailAlloc_1241_, 9, v_dAssignment_1228_);
v___x_1234_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
lean_object* v___x_1236_; 
if (v_isShared_1218_ == 0)
{
lean_ctor_set(v___x_1217_, 0, v___x_1234_);
v___x_1236_ = v___x_1217_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v___x_1234_);
lean_ctor_set(v_reuseFailAlloc_1240_, 1, v_cache_1212_);
lean_ctor_set(v_reuseFailAlloc_1240_, 2, v_zetaDeltaFVarIds_1213_);
lean_ctor_set(v_reuseFailAlloc_1240_, 3, v_postponed_1214_);
lean_ctor_set(v_reuseFailAlloc_1240_, 4, v_diag_1215_);
v___x_1236_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; 
v___x_1237_ = lean_st_ref_set(v___y_1208_, v___x_1236_);
v___x_1238_ = lean_box(0);
v___x_1239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1239_, 0, v___x_1238_);
return v___x_1239_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2___redArg___boxed(lean_object* v_mvarId_1244_, lean_object* v_val_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_){
_start:
{
lean_object* v_res_1248_; 
v_res_1248_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2___redArg(v_mvarId_1244_, v_val_1245_, v___y_1246_);
lean_dec(v___y_1246_);
return v_res_1248_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5_spec__14(lean_object* v_msgData_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_){
_start:
{
lean_object* v___x_1255_; lean_object* v_env_1256_; lean_object* v___x_1257_; lean_object* v_mctx_1258_; lean_object* v_lctx_1259_; lean_object* v_options_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___x_1255_ = lean_st_ref_get(v___y_1253_);
v_env_1256_ = lean_ctor_get(v___x_1255_, 0);
lean_inc_ref(v_env_1256_);
lean_dec(v___x_1255_);
v___x_1257_ = lean_st_ref_get(v___y_1251_);
v_mctx_1258_ = lean_ctor_get(v___x_1257_, 0);
lean_inc_ref(v_mctx_1258_);
lean_dec(v___x_1257_);
v_lctx_1259_ = lean_ctor_get(v___y_1250_, 2);
v_options_1260_ = lean_ctor_get(v___y_1252_, 2);
lean_inc_ref(v_options_1260_);
lean_inc_ref(v_lctx_1259_);
v___x_1261_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1261_, 0, v_env_1256_);
lean_ctor_set(v___x_1261_, 1, v_mctx_1258_);
lean_ctor_set(v___x_1261_, 2, v_lctx_1259_);
lean_ctor_set(v___x_1261_, 3, v_options_1260_);
v___x_1262_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1262_, 0, v___x_1261_);
lean_ctor_set(v___x_1262_, 1, v_msgData_1249_);
v___x_1263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1263_, 0, v___x_1262_);
return v___x_1263_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5_spec__14___boxed(lean_object* v_msgData_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_){
_start:
{
lean_object* v_res_1270_; 
v_res_1270_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5_spec__14(v_msgData_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_);
lean_dec(v___y_1268_);
lean_dec_ref(v___y_1267_);
lean_dec(v___y_1266_);
lean_dec_ref(v___y_1265_);
return v_res_1270_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__8___redArg(lean_object* v_msg_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_){
_start:
{
lean_object* v_ref_1277_; lean_object* v___x_1278_; lean_object* v_a_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1287_; 
v_ref_1277_ = lean_ctor_get(v___y_1274_, 5);
v___x_1278_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5_spec__14(v_msg_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_);
v_a_1279_ = lean_ctor_get(v___x_1278_, 0);
v_isSharedCheck_1287_ = !lean_is_exclusive(v___x_1278_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1281_ = v___x_1278_;
v_isShared_1282_ = v_isSharedCheck_1287_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_a_1279_);
lean_dec(v___x_1278_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1287_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
lean_object* v___x_1283_; lean_object* v___x_1285_; 
lean_inc(v_ref_1277_);
v___x_1283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1283_, 0, v_ref_1277_);
lean_ctor_set(v___x_1283_, 1, v_a_1279_);
if (v_isShared_1282_ == 0)
{
lean_ctor_set_tag(v___x_1281_, 1);
lean_ctor_set(v___x_1281_, 0, v___x_1283_);
v___x_1285_ = v___x_1281_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v___x_1283_);
v___x_1285_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
return v___x_1285_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__8___redArg___boxed(lean_object* v_msg_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_){
_start:
{
lean_object* v_res_1294_; 
v_res_1294_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__8___redArg(v_msg_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_);
lean_dec(v___y_1292_);
lean_dec_ref(v___y_1291_);
lean_dec(v___y_1290_);
lean_dec_ref(v___y_1289_);
return v_res_1294_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__7(lean_object* v_u_1295_, lean_object* v_as_1296_, size_t v_i_1297_, size_t v_stop_1298_, lean_object* v_b_1299_){
_start:
{
uint8_t v___x_1300_; 
v___x_1300_ = lean_usize_dec_eq(v_i_1297_, v_stop_1298_);
if (v___x_1300_ == 0)
{
size_t v___x_1301_; size_t v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; 
v___x_1301_ = ((size_t)1ULL);
v___x_1302_ = lean_usize_sub(v_i_1297_, v___x_1301_);
v___x_1303_ = lean_array_uget_borrowed(v_as_1296_, v___x_1302_);
lean_inc(v___x_1303_);
lean_inc(v_u_1295_);
v___x_1304_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkCons(v_u_1295_, v___x_1303_, v_b_1299_);
v_i_1297_ = v___x_1302_;
v_b_1299_ = v___x_1304_;
goto _start;
}
else
{
lean_dec(v_u_1295_);
return v_b_1299_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__7___boxed(lean_object* v_u_1306_, lean_object* v_as_1307_, lean_object* v_i_1308_, lean_object* v_stop_1309_, lean_object* v_b_1310_){
_start:
{
size_t v_i_boxed_1311_; size_t v_stop_boxed_1312_; lean_object* v_res_1313_; 
v_i_boxed_1311_ = lean_unbox_usize(v_i_1308_);
lean_dec(v_i_1308_);
v_stop_boxed_1312_ = lean_unbox_usize(v_stop_1309_);
lean_dec(v_stop_1309_);
v_res_1313_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__7(v_u_1306_, v_as_1307_, v_i_boxed_1311_, v_stop_boxed_1312_, v_b_1310_);
lean_dec_ref(v_as_1307_);
return v_res_1313_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__6(size_t v_sz_1314_, size_t v_i_1315_, lean_object* v_bs_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_){
_start:
{
uint8_t v___x_1322_; 
v___x_1322_ = lean_usize_dec_lt(v_i_1315_, v_sz_1314_);
if (v___x_1322_ == 0)
{
lean_object* v___x_1323_; 
v___x_1323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1323_, 0, v_bs_1316_);
return v___x_1323_;
}
else
{
lean_object* v_v_1324_; lean_object* v___x_1325_; 
v_v_1324_ = lean_array_uget_borrowed(v_bs_1316_, v_i_1315_);
lean_inc(v_v_1324_);
v___x_1325_ = l_Lean_Meta_mkEqRefl(v_v_1324_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_);
if (lean_obj_tag(v___x_1325_) == 0)
{
lean_object* v_a_1326_; lean_object* v___x_1327_; lean_object* v_bs_x27_1328_; size_t v___x_1329_; size_t v___x_1330_; lean_object* v___x_1331_; 
v_a_1326_ = lean_ctor_get(v___x_1325_, 0);
lean_inc(v_a_1326_);
lean_dec_ref_known(v___x_1325_, 1);
v___x_1327_ = lean_unsigned_to_nat(0u);
v_bs_x27_1328_ = lean_array_uset(v_bs_1316_, v_i_1315_, v___x_1327_);
v___x_1329_ = ((size_t)1ULL);
v___x_1330_ = lean_usize_add(v_i_1315_, v___x_1329_);
v___x_1331_ = lean_array_uset(v_bs_x27_1328_, v_i_1315_, v_a_1326_);
v_i_1315_ = v___x_1330_;
v_bs_1316_ = v___x_1331_;
goto _start;
}
else
{
lean_object* v_a_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1340_; 
lean_dec_ref(v_bs_1316_);
v_a_1333_ = lean_ctor_get(v___x_1325_, 0);
v_isSharedCheck_1340_ = !lean_is_exclusive(v___x_1325_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1335_ = v___x_1325_;
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_a_1333_);
lean_dec(v___x_1325_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v___x_1338_; 
if (v_isShared_1336_ == 0)
{
v___x_1338_ = v___x_1335_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v_a_1333_);
v___x_1338_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
return v___x_1338_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__6___boxed(lean_object* v_sz_1341_, lean_object* v_i_1342_, lean_object* v_bs_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_){
_start:
{
size_t v_sz_boxed_1349_; size_t v_i_boxed_1350_; lean_object* v_res_1351_; 
v_sz_boxed_1349_ = lean_unbox_usize(v_sz_1341_);
lean_dec(v_sz_1341_);
v_i_boxed_1350_ = lean_unbox_usize(v_i_1342_);
lean_dec(v_i_1342_);
v_res_1351_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__6(v_sz_boxed_1349_, v_i_boxed_1350_, v_bs_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_);
lean_dec(v___y_1347_);
lean_dec_ref(v___y_1346_);
lean_dec(v___y_1345_);
lean_dec_ref(v___y_1344_);
return v_res_1351_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__4___redArg(size_t v_sz_1352_, size_t v_i_1353_, lean_object* v_bs_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_){
_start:
{
uint8_t v___x_1358_; 
v___x_1358_ = lean_usize_dec_lt(v_i_1353_, v_sz_1352_);
if (v___x_1358_ == 0)
{
lean_object* v___x_1359_; 
v___x_1359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1359_, 0, v_bs_1354_);
return v___x_1359_;
}
else
{
lean_object* v_v_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; 
v_v_1360_ = lean_array_uget(v_bs_1354_, v_i_1353_);
v___x_1361_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__6___closed__1));
v___x_1362_ = l_Lean_Core_mkFreshUserName(v___x_1361_, v___y_1355_, v___y_1356_);
if (lean_obj_tag(v___x_1362_) == 0)
{
lean_object* v_a_1363_; lean_object* v___x_1364_; lean_object* v_bs_x27_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; size_t v___x_1371_; size_t v___x_1372_; lean_object* v___x_1373_; 
v_a_1363_ = lean_ctor_get(v___x_1362_, 0);
lean_inc(v_a_1363_);
lean_dec_ref_known(v___x_1362_, 1);
v___x_1364_ = lean_unsigned_to_nat(0u);
v_bs_x27_1365_ = lean_array_uset(v_bs_1354_, v_i_1353_, v___x_1364_);
v___x_1366_ = lean_usize_to_nat(v_i_1353_);
v___x_1367_ = lean_unsigned_to_nat(1u);
v___x_1368_ = lean_nat_add(v___x_1366_, v___x_1367_);
lean_dec(v___x_1366_);
v___x_1369_ = lean_name_append_index_after(v_a_1363_, v___x_1368_);
v___x_1370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1370_, 0, v___x_1369_);
lean_ctor_set(v___x_1370_, 1, v_v_1360_);
v___x_1371_ = ((size_t)1ULL);
v___x_1372_ = lean_usize_add(v_i_1353_, v___x_1371_);
v___x_1373_ = lean_array_uset(v_bs_x27_1365_, v_i_1353_, v___x_1370_);
v_i_1353_ = v___x_1372_;
v_bs_1354_ = v___x_1373_;
goto _start;
}
else
{
lean_object* v_a_1375_; lean_object* v___x_1377_; uint8_t v_isShared_1378_; uint8_t v_isSharedCheck_1382_; 
lean_dec(v_v_1360_);
lean_dec_ref(v_bs_1354_);
v_a_1375_ = lean_ctor_get(v___x_1362_, 0);
v_isSharedCheck_1382_ = !lean_is_exclusive(v___x_1362_);
if (v_isSharedCheck_1382_ == 0)
{
v___x_1377_ = v___x_1362_;
v_isShared_1378_ = v_isSharedCheck_1382_;
goto v_resetjp_1376_;
}
else
{
lean_inc(v_a_1375_);
lean_dec(v___x_1362_);
v___x_1377_ = lean_box(0);
v_isShared_1378_ = v_isSharedCheck_1382_;
goto v_resetjp_1376_;
}
v_resetjp_1376_:
{
lean_object* v___x_1380_; 
if (v_isShared_1378_ == 0)
{
v___x_1380_ = v___x_1377_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v_a_1375_);
v___x_1380_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
return v___x_1380_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__4___redArg___boxed(lean_object* v_sz_1383_, lean_object* v_i_1384_, lean_object* v_bs_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_){
_start:
{
size_t v_sz_boxed_1389_; size_t v_i_boxed_1390_; lean_object* v_res_1391_; 
v_sz_boxed_1389_ = lean_unbox_usize(v_sz_1383_);
lean_dec(v_sz_1383_);
v_i_boxed_1390_ = lean_unbox_usize(v_i_1384_);
lean_dec(v_i_1384_);
v_res_1391_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__4___redArg(v_sz_boxed_1389_, v_i_boxed_1390_, v_bs_1385_, v___y_1386_, v___y_1387_);
lean_dec(v___y_1387_);
lean_dec_ref(v___y_1386_);
return v_res_1391_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__1___redArg(lean_object* v_a_1392_, lean_object* v_b_1393_){
_start:
{
lean_object* v_array_1394_; lean_object* v_start_1395_; lean_object* v_stop_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1409_; 
v_array_1394_ = lean_ctor_get(v_a_1392_, 0);
v_start_1395_ = lean_ctor_get(v_a_1392_, 1);
v_stop_1396_ = lean_ctor_get(v_a_1392_, 2);
v_isSharedCheck_1409_ = !lean_is_exclusive(v_a_1392_);
if (v_isSharedCheck_1409_ == 0)
{
v___x_1398_ = v_a_1392_;
v_isShared_1399_ = v_isSharedCheck_1409_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_stop_1396_);
lean_inc(v_start_1395_);
lean_inc(v_array_1394_);
lean_dec(v_a_1392_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1409_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
uint8_t v___x_1400_; 
v___x_1400_ = lean_nat_dec_lt(v_start_1395_, v_stop_1396_);
if (v___x_1400_ == 0)
{
lean_del_object(v___x_1398_);
lean_dec(v_stop_1396_);
lean_dec(v_start_1395_);
lean_dec_ref(v_array_1394_);
return v_b_1393_;
}
else
{
lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1404_; 
v___x_1401_ = lean_unsigned_to_nat(1u);
v___x_1402_ = lean_nat_add(v_start_1395_, v___x_1401_);
lean_inc_ref(v_array_1394_);
if (v_isShared_1399_ == 0)
{
lean_ctor_set(v___x_1398_, 1, v___x_1402_);
v___x_1404_ = v___x_1398_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v_array_1394_);
lean_ctor_set(v_reuseFailAlloc_1408_, 1, v___x_1402_);
lean_ctor_set(v_reuseFailAlloc_1408_, 2, v_stop_1396_);
v___x_1404_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
lean_object* v___x_1405_; lean_object* v___x_1406_; 
v___x_1405_ = lean_array_fget(v_array_1394_, v_start_1395_);
lean_dec(v_start_1395_);
lean_dec_ref(v_array_1394_);
v___x_1406_ = lean_array_push(v_b_1393_, v___x_1405_);
v_a_1392_ = v___x_1404_;
v_b_1393_ = v___x_1406_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___lam__0(lean_object* v___x_1410_, lean_object* v_a_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_){
_start:
{
lean_object* v___x_1421_; lean_object* v___x_20042__overap_1422_; lean_object* v___x_1423_; 
v___x_1421_ = l_Lean_instInhabitedExpr;
v___x_20042__overap_1422_ = l_instInhabitedOfMonad___redArg(v___x_1410_, v___x_1421_);
lean_inc(v___y_1419_);
lean_inc_ref(v___y_1418_);
lean_inc(v___y_1417_);
lean_inc_ref(v___y_1416_);
lean_inc(v___y_1415_);
lean_inc_ref(v___y_1414_);
lean_inc(v___y_1413_);
lean_inc_ref(v___y_1412_);
v___x_1423_ = lean_apply_9(v___x_20042__overap_1422_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_, lean_box(0));
return v___x_1423_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___lam__0___boxed(lean_object* v___x_1424_, lean_object* v_a_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_){
_start:
{
lean_object* v_res_1435_; 
v_res_1435_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___lam__0(v___x_1424_, v_a_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_);
lean_dec(v___y_1433_);
lean_dec_ref(v___y_1432_);
lean_dec(v___y_1431_);
lean_dec_ref(v___y_1430_);
lean_dec(v___y_1429_);
lean_dec_ref(v___y_1428_);
lean_dec(v___y_1427_);
lean_dec_ref(v___y_1426_);
lean_dec_ref(v_a_1425_);
return v_res_1435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19_spec__21___redArg___lam__0(lean_object* v_k_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v_b_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_){
_start:
{
lean_object* v___x_1447_; 
lean_inc(v___y_1445_);
lean_inc_ref(v___y_1444_);
lean_inc(v___y_1443_);
lean_inc_ref(v___y_1442_);
lean_inc(v___y_1440_);
lean_inc_ref(v___y_1439_);
lean_inc(v___y_1438_);
lean_inc_ref(v___y_1437_);
v___x_1447_ = lean_apply_10(v_k_1436_, v_b_1441_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, lean_box(0));
return v___x_1447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19_spec__21___redArg___lam__0___boxed(lean_object* v_k_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v_b_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_){
_start:
{
lean_object* v_res_1459_; 
v_res_1459_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19_spec__21___redArg___lam__0(v_k_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v_b_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_);
lean_dec(v___y_1457_);
lean_dec_ref(v___y_1456_);
lean_dec(v___y_1455_);
lean_dec_ref(v___y_1454_);
lean_dec(v___y_1452_);
lean_dec_ref(v___y_1451_);
lean_dec(v___y_1450_);
lean_dec_ref(v___y_1449_);
return v_res_1459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19_spec__21___redArg(lean_object* v_name_1460_, uint8_t v_bi_1461_, lean_object* v_type_1462_, lean_object* v_k_1463_, uint8_t v_kind_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_){
_start:
{
lean_object* v___f_1474_; lean_object* v___x_1475_; 
lean_inc(v___y_1468_);
lean_inc_ref(v___y_1467_);
lean_inc(v___y_1466_);
lean_inc_ref(v___y_1465_);
v___f_1474_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19_spec__21___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_1474_, 0, v_k_1463_);
lean_closure_set(v___f_1474_, 1, v___y_1465_);
lean_closure_set(v___f_1474_, 2, v___y_1466_);
lean_closure_set(v___f_1474_, 3, v___y_1467_);
lean_closure_set(v___f_1474_, 4, v___y_1468_);
v___x_1475_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1460_, v_bi_1461_, v_type_1462_, v___f_1474_, v_kind_1464_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_);
if (lean_obj_tag(v___x_1475_) == 0)
{
return v___x_1475_;
}
else
{
lean_object* v_a_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1483_; 
v_a_1476_ = lean_ctor_get(v___x_1475_, 0);
v_isSharedCheck_1483_ = !lean_is_exclusive(v___x_1475_);
if (v_isSharedCheck_1483_ == 0)
{
v___x_1478_ = v___x_1475_;
v_isShared_1479_ = v_isSharedCheck_1483_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_a_1476_);
lean_dec(v___x_1475_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1483_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
lean_object* v___x_1481_; 
if (v_isShared_1479_ == 0)
{
v___x_1481_ = v___x_1478_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v_a_1476_);
v___x_1481_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
return v___x_1481_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19_spec__21___redArg___boxed(lean_object* v_name_1484_, lean_object* v_bi_1485_, lean_object* v_type_1486_, lean_object* v_k_1487_, lean_object* v_kind_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_){
_start:
{
uint8_t v_bi_boxed_1498_; uint8_t v_kind_boxed_1499_; lean_object* v_res_1500_; 
v_bi_boxed_1498_ = lean_unbox(v_bi_1485_);
v_kind_boxed_1499_ = lean_unbox(v_kind_1488_);
v_res_1500_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19_spec__21___redArg(v_name_1484_, v_bi_boxed_1498_, v_type_1486_, v_k_1487_, v_kind_boxed_1499_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_);
lean_dec(v___y_1496_);
lean_dec_ref(v___y_1495_);
lean_dec(v___y_1494_);
lean_dec_ref(v___y_1493_);
lean_dec(v___y_1492_);
lean_dec_ref(v___y_1491_);
lean_dec(v___y_1490_);
lean_dec_ref(v___y_1489_);
return v_res_1500_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___lam__1___boxed(lean_object* v_acc_1505_, lean_object* v_declInfos_1506_, lean_object* v_k_1507_, lean_object* v_kind_1508_, lean_object* v_x_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_){
_start:
{
uint8_t v_kind_boxed_1519_; lean_object* v_res_1520_; 
v_kind_boxed_1519_ = lean_unbox(v_kind_1508_);
v_res_1520_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___lam__1(v_acc_1505_, v_declInfos_1506_, v_k_1507_, v_kind_boxed_1519_, v_x_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_);
lean_dec(v___y_1517_);
lean_dec_ref(v___y_1516_);
lean_dec(v___y_1515_);
lean_dec_ref(v___y_1514_);
lean_dec(v___y_1513_);
lean_dec_ref(v___y_1512_);
lean_dec(v___y_1511_);
lean_dec_ref(v___y_1510_);
return v_res_1520_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19(lean_object* v_declInfos_1521_, lean_object* v_k_1522_, uint8_t v_kind_1523_, lean_object* v_acc_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_){
_start:
{
lean_object* v___x_1534_; lean_object* v_toApplicative_1535_; lean_object* v_toFunctor_1536_; lean_object* v_toSeq_1537_; lean_object* v_toSeqLeft_1538_; lean_object* v_toSeqRight_1539_; lean_object* v___f_1540_; lean_object* v___f_1541_; lean_object* v___f_1542_; lean_object* v___f_1543_; lean_object* v___x_1544_; lean_object* v___f_1545_; lean_object* v___f_1546_; lean_object* v___f_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v_toApplicative_1551_; lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1668_; 
v___x_1534_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__1);
v_toApplicative_1535_ = lean_ctor_get(v___x_1534_, 0);
v_toFunctor_1536_ = lean_ctor_get(v_toApplicative_1535_, 0);
v_toSeq_1537_ = lean_ctor_get(v_toApplicative_1535_, 2);
v_toSeqLeft_1538_ = lean_ctor_get(v_toApplicative_1535_, 3);
v_toSeqRight_1539_ = lean_ctor_get(v_toApplicative_1535_, 4);
v___f_1540_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__2));
v___f_1541_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_1536_, 2);
v___f_1542_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1542_, 0, v_toFunctor_1536_);
v___f_1543_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1543_, 0, v_toFunctor_1536_);
v___x_1544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1544_, 0, v___f_1542_);
lean_ctor_set(v___x_1544_, 1, v___f_1543_);
lean_inc(v_toSeqRight_1539_);
v___f_1545_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1545_, 0, v_toSeqRight_1539_);
lean_inc(v_toSeqLeft_1538_);
v___f_1546_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1546_, 0, v_toSeqLeft_1538_);
lean_inc(v_toSeq_1537_);
v___f_1547_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1547_, 0, v_toSeq_1537_);
v___x_1548_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1548_, 0, v___x_1544_);
lean_ctor_set(v___x_1548_, 1, v___f_1540_);
lean_ctor_set(v___x_1548_, 2, v___f_1547_);
lean_ctor_set(v___x_1548_, 3, v___f_1546_);
lean_ctor_set(v___x_1548_, 4, v___f_1545_);
v___x_1549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1549_, 0, v___x_1548_);
lean_ctor_set(v___x_1549_, 1, v___f_1541_);
v___x_1550_ = l_StateRefT_x27_instMonad___redArg(v___x_1549_);
v_toApplicative_1551_ = lean_ctor_get(v___x_1550_, 0);
v_isSharedCheck_1668_ = !lean_is_exclusive(v___x_1550_);
if (v_isSharedCheck_1668_ == 0)
{
lean_object* v_unused_1669_; 
v_unused_1669_ = lean_ctor_get(v___x_1550_, 1);
lean_dec(v_unused_1669_);
v___x_1553_ = v___x_1550_;
v_isShared_1554_ = v_isSharedCheck_1668_;
goto v_resetjp_1552_;
}
else
{
lean_inc(v_toApplicative_1551_);
lean_dec(v___x_1550_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1668_;
goto v_resetjp_1552_;
}
v_resetjp_1552_:
{
lean_object* v_toFunctor_1555_; lean_object* v_toSeq_1556_; lean_object* v_toSeqLeft_1557_; lean_object* v_toSeqRight_1558_; lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1666_; 
v_toFunctor_1555_ = lean_ctor_get(v_toApplicative_1551_, 0);
v_toSeq_1556_ = lean_ctor_get(v_toApplicative_1551_, 2);
v_toSeqLeft_1557_ = lean_ctor_get(v_toApplicative_1551_, 3);
v_toSeqRight_1558_ = lean_ctor_get(v_toApplicative_1551_, 4);
v_isSharedCheck_1666_ = !lean_is_exclusive(v_toApplicative_1551_);
if (v_isSharedCheck_1666_ == 0)
{
lean_object* v_unused_1667_; 
v_unused_1667_ = lean_ctor_get(v_toApplicative_1551_, 1);
lean_dec(v_unused_1667_);
v___x_1560_ = v_toApplicative_1551_;
v_isShared_1561_ = v_isSharedCheck_1666_;
goto v_resetjp_1559_;
}
else
{
lean_inc(v_toSeqRight_1558_);
lean_inc(v_toSeqLeft_1557_);
lean_inc(v_toSeq_1556_);
lean_inc(v_toFunctor_1555_);
lean_dec(v_toApplicative_1551_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1666_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
lean_object* v___f_1562_; lean_object* v___f_1563_; lean_object* v___f_1564_; lean_object* v___f_1565_; lean_object* v___x_1566_; lean_object* v___f_1567_; lean_object* v___f_1568_; lean_object* v___f_1569_; lean_object* v___x_1571_; 
v___f_1562_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__4));
v___f_1563_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__5));
lean_inc_ref(v_toFunctor_1555_);
v___f_1564_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1564_, 0, v_toFunctor_1555_);
v___f_1565_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1565_, 0, v_toFunctor_1555_);
v___x_1566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1566_, 0, v___f_1564_);
lean_ctor_set(v___x_1566_, 1, v___f_1565_);
v___f_1567_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1567_, 0, v_toSeqRight_1558_);
v___f_1568_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1568_, 0, v_toSeqLeft_1557_);
v___f_1569_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1569_, 0, v_toSeq_1556_);
if (v_isShared_1561_ == 0)
{
lean_ctor_set(v___x_1560_, 4, v___f_1567_);
lean_ctor_set(v___x_1560_, 3, v___f_1568_);
lean_ctor_set(v___x_1560_, 2, v___f_1569_);
lean_ctor_set(v___x_1560_, 1, v___f_1562_);
lean_ctor_set(v___x_1560_, 0, v___x_1566_);
v___x_1571_ = v___x_1560_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v___x_1566_);
lean_ctor_set(v_reuseFailAlloc_1665_, 1, v___f_1562_);
lean_ctor_set(v_reuseFailAlloc_1665_, 2, v___f_1569_);
lean_ctor_set(v_reuseFailAlloc_1665_, 3, v___f_1568_);
lean_ctor_set(v_reuseFailAlloc_1665_, 4, v___f_1567_);
v___x_1571_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1570_;
}
v_reusejp_1570_:
{
lean_object* v___x_1573_; 
if (v_isShared_1554_ == 0)
{
lean_ctor_set(v___x_1553_, 1, v___f_1563_);
lean_ctor_set(v___x_1553_, 0, v___x_1571_);
v___x_1573_ = v___x_1553_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v___x_1571_);
lean_ctor_set(v_reuseFailAlloc_1664_, 1, v___f_1563_);
v___x_1573_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
lean_object* v___x_1574_; lean_object* v_toApplicative_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1662_; 
v___x_1574_ = l_StateRefT_x27_instMonad___redArg(v___x_1573_);
v_toApplicative_1575_ = lean_ctor_get(v___x_1574_, 0);
v_isSharedCheck_1662_ = !lean_is_exclusive(v___x_1574_);
if (v_isSharedCheck_1662_ == 0)
{
lean_object* v_unused_1663_; 
v_unused_1663_ = lean_ctor_get(v___x_1574_, 1);
lean_dec(v_unused_1663_);
v___x_1577_ = v___x_1574_;
v_isShared_1578_ = v_isSharedCheck_1662_;
goto v_resetjp_1576_;
}
else
{
lean_inc(v_toApplicative_1575_);
lean_dec(v___x_1574_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1662_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
lean_object* v_toFunctor_1579_; lean_object* v_toSeq_1580_; lean_object* v_toSeqLeft_1581_; lean_object* v_toSeqRight_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1660_; 
v_toFunctor_1579_ = lean_ctor_get(v_toApplicative_1575_, 0);
v_toSeq_1580_ = lean_ctor_get(v_toApplicative_1575_, 2);
v_toSeqLeft_1581_ = lean_ctor_get(v_toApplicative_1575_, 3);
v_toSeqRight_1582_ = lean_ctor_get(v_toApplicative_1575_, 4);
v_isSharedCheck_1660_ = !lean_is_exclusive(v_toApplicative_1575_);
if (v_isSharedCheck_1660_ == 0)
{
lean_object* v_unused_1661_; 
v_unused_1661_ = lean_ctor_get(v_toApplicative_1575_, 1);
lean_dec(v_unused_1661_);
v___x_1584_ = v_toApplicative_1575_;
v_isShared_1585_ = v_isSharedCheck_1660_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_toSeqRight_1582_);
lean_inc(v_toSeqLeft_1581_);
lean_inc(v_toSeq_1580_);
lean_inc(v_toFunctor_1579_);
lean_dec(v_toApplicative_1575_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1660_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v___f_1586_; lean_object* v___f_1587_; lean_object* v___f_1588_; lean_object* v___f_1589_; lean_object* v___x_1590_; lean_object* v___f_1591_; lean_object* v___f_1592_; lean_object* v___f_1593_; lean_object* v___x_1595_; 
v___f_1586_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___closed__0));
v___f_1587_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___closed__1));
lean_inc_ref(v_toFunctor_1579_);
v___f_1588_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1588_, 0, v_toFunctor_1579_);
v___f_1589_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1589_, 0, v_toFunctor_1579_);
v___x_1590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1590_, 0, v___f_1588_);
lean_ctor_set(v___x_1590_, 1, v___f_1589_);
v___f_1591_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1591_, 0, v_toSeqRight_1582_);
v___f_1592_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1592_, 0, v_toSeqLeft_1581_);
v___f_1593_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1593_, 0, v_toSeq_1580_);
if (v_isShared_1585_ == 0)
{
lean_ctor_set(v___x_1584_, 4, v___f_1591_);
lean_ctor_set(v___x_1584_, 3, v___f_1592_);
lean_ctor_set(v___x_1584_, 2, v___f_1593_);
lean_ctor_set(v___x_1584_, 1, v___f_1586_);
lean_ctor_set(v___x_1584_, 0, v___x_1590_);
v___x_1595_ = v___x_1584_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v___x_1590_);
lean_ctor_set(v_reuseFailAlloc_1659_, 1, v___f_1586_);
lean_ctor_set(v_reuseFailAlloc_1659_, 2, v___f_1593_);
lean_ctor_set(v_reuseFailAlloc_1659_, 3, v___f_1592_);
lean_ctor_set(v_reuseFailAlloc_1659_, 4, v___f_1591_);
v___x_1595_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
lean_object* v___x_1597_; 
if (v_isShared_1578_ == 0)
{
lean_ctor_set(v___x_1577_, 1, v___f_1587_);
lean_ctor_set(v___x_1577_, 0, v___x_1595_);
v___x_1597_ = v___x_1577_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v___x_1595_);
lean_ctor_set(v_reuseFailAlloc_1658_, 1, v___f_1587_);
v___x_1597_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
lean_object* v___x_1598_; lean_object* v_toApplicative_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1656_; 
v___x_1598_ = l_StateRefT_x27_instMonad___redArg(v___x_1597_);
v_toApplicative_1599_ = lean_ctor_get(v___x_1598_, 0);
v_isSharedCheck_1656_ = !lean_is_exclusive(v___x_1598_);
if (v_isSharedCheck_1656_ == 0)
{
lean_object* v_unused_1657_; 
v_unused_1657_ = lean_ctor_get(v___x_1598_, 1);
lean_dec(v_unused_1657_);
v___x_1601_ = v___x_1598_;
v_isShared_1602_ = v_isSharedCheck_1656_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_toApplicative_1599_);
lean_dec(v___x_1598_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1656_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v_toFunctor_1603_; lean_object* v_toSeq_1604_; lean_object* v_toSeqLeft_1605_; lean_object* v_toSeqRight_1606_; lean_object* v___x_1608_; uint8_t v_isShared_1609_; uint8_t v_isSharedCheck_1654_; 
v_toFunctor_1603_ = lean_ctor_get(v_toApplicative_1599_, 0);
v_toSeq_1604_ = lean_ctor_get(v_toApplicative_1599_, 2);
v_toSeqLeft_1605_ = lean_ctor_get(v_toApplicative_1599_, 3);
v_toSeqRight_1606_ = lean_ctor_get(v_toApplicative_1599_, 4);
v_isSharedCheck_1654_ = !lean_is_exclusive(v_toApplicative_1599_);
if (v_isSharedCheck_1654_ == 0)
{
lean_object* v_unused_1655_; 
v_unused_1655_ = lean_ctor_get(v_toApplicative_1599_, 1);
lean_dec(v_unused_1655_);
v___x_1608_ = v_toApplicative_1599_;
v_isShared_1609_ = v_isSharedCheck_1654_;
goto v_resetjp_1607_;
}
else
{
lean_inc(v_toSeqRight_1606_);
lean_inc(v_toSeqLeft_1605_);
lean_inc(v_toSeq_1604_);
lean_inc(v_toFunctor_1603_);
lean_dec(v_toApplicative_1599_);
v___x_1608_ = lean_box(0);
v_isShared_1609_ = v_isSharedCheck_1654_;
goto v_resetjp_1607_;
}
v_resetjp_1607_:
{
lean_object* v___f_1610_; lean_object* v___f_1611_; lean_object* v___f_1612_; lean_object* v___f_1613_; lean_object* v___x_1614_; lean_object* v___f_1615_; lean_object* v___f_1616_; lean_object* v___f_1617_; lean_object* v___x_1619_; 
v___f_1610_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___closed__2));
v___f_1611_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___closed__3));
lean_inc_ref(v_toFunctor_1603_);
v___f_1612_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1612_, 0, v_toFunctor_1603_);
v___f_1613_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1613_, 0, v_toFunctor_1603_);
v___x_1614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1614_, 0, v___f_1612_);
lean_ctor_set(v___x_1614_, 1, v___f_1613_);
v___f_1615_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1615_, 0, v_toSeqRight_1606_);
v___f_1616_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1616_, 0, v_toSeqLeft_1605_);
v___f_1617_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1617_, 0, v_toSeq_1604_);
if (v_isShared_1609_ == 0)
{
lean_ctor_set(v___x_1608_, 4, v___f_1615_);
lean_ctor_set(v___x_1608_, 3, v___f_1616_);
lean_ctor_set(v___x_1608_, 2, v___f_1617_);
lean_ctor_set(v___x_1608_, 1, v___f_1610_);
lean_ctor_set(v___x_1608_, 0, v___x_1614_);
v___x_1619_ = v___x_1608_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1653_; 
v_reuseFailAlloc_1653_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1653_, 0, v___x_1614_);
lean_ctor_set(v_reuseFailAlloc_1653_, 1, v___f_1610_);
lean_ctor_set(v_reuseFailAlloc_1653_, 2, v___f_1617_);
lean_ctor_set(v_reuseFailAlloc_1653_, 3, v___f_1616_);
lean_ctor_set(v_reuseFailAlloc_1653_, 4, v___f_1615_);
v___x_1619_ = v_reuseFailAlloc_1653_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
lean_object* v___x_1621_; 
if (v_isShared_1602_ == 0)
{
lean_ctor_set(v___x_1601_, 1, v___f_1611_);
lean_ctor_set(v___x_1601_, 0, v___x_1619_);
v___x_1621_ = v___x_1601_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v___x_1619_);
lean_ctor_set(v_reuseFailAlloc_1652_, 1, v___f_1611_);
v___x_1621_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
lean_object* v___x_1622_; lean_object* v___x_1623_; uint8_t v___x_1624_; 
v___x_1622_ = lean_array_get_size(v_acc_1524_);
v___x_1623_ = lean_array_get_size(v_declInfos_1521_);
v___x_1624_ = lean_nat_dec_lt(v___x_1622_, v___x_1623_);
if (v___x_1624_ == 0)
{
lean_object* v___x_1625_; 
lean_dec_ref(v___x_1621_);
lean_dec_ref(v_declInfos_1521_);
lean_inc(v___y_1532_);
lean_inc_ref(v___y_1531_);
lean_inc(v___y_1530_);
lean_inc_ref(v___y_1529_);
lean_inc(v___y_1528_);
lean_inc_ref(v___y_1527_);
lean_inc(v___y_1526_);
lean_inc_ref(v___y_1525_);
v___x_1625_ = lean_apply_10(v_k_1522_, v_acc_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, lean_box(0));
return v___x_1625_;
}
else
{
lean_object* v___f_1626_; lean_object* v___x_1627_; uint8_t v___x_1628_; lean_object* v___f_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v_snd_1634_; lean_object* v_fst_1635_; lean_object* v_fst_1636_; lean_object* v_snd_1637_; lean_object* v___x_1638_; 
v___f_1626_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___lam__0___boxed), 11, 1);
lean_closure_set(v___f_1626_, 0, v___x_1621_);
v___x_1627_ = lean_box(0);
v___x_1628_ = 0;
v___f_1629_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1629_, 0, v___f_1626_);
v___x_1630_ = lean_box(v___x_1628_);
v___x_1631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1631_, 0, v___x_1630_);
lean_ctor_set(v___x_1631_, 1, v___f_1629_);
v___x_1632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1627_);
lean_ctor_set(v___x_1632_, 1, v___x_1631_);
v___x_1633_ = lean_array_get(v___x_1632_, v_declInfos_1521_, v___x_1622_);
lean_dec_ref_known(v___x_1632_, 2);
v_snd_1634_ = lean_ctor_get(v___x_1633_, 1);
lean_inc(v_snd_1634_);
v_fst_1635_ = lean_ctor_get(v___x_1633_, 0);
lean_inc(v_fst_1635_);
lean_dec(v___x_1633_);
v_fst_1636_ = lean_ctor_get(v_snd_1634_, 0);
lean_inc(v_fst_1636_);
v_snd_1637_ = lean_ctor_get(v_snd_1634_, 1);
lean_inc(v_snd_1637_);
lean_dec(v_snd_1634_);
lean_inc(v___y_1532_);
lean_inc_ref(v___y_1531_);
lean_inc(v___y_1530_);
lean_inc_ref(v___y_1529_);
lean_inc(v___y_1528_);
lean_inc_ref(v___y_1527_);
lean_inc(v___y_1526_);
lean_inc_ref(v___y_1525_);
lean_inc_ref(v_acc_1524_);
v___x_1638_ = lean_apply_10(v_snd_1637_, v_acc_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, lean_box(0));
if (lean_obj_tag(v___x_1638_) == 0)
{
lean_object* v_a_1639_; lean_object* v___x_1640_; lean_object* v___f_1641_; uint8_t v___x_1642_; lean_object* v___x_1643_; 
v_a_1639_ = lean_ctor_get(v___x_1638_, 0);
lean_inc(v_a_1639_);
lean_dec_ref_known(v___x_1638_, 1);
v___x_1640_ = lean_box(v_kind_1523_);
v___f_1641_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___lam__1___boxed), 14, 4);
lean_closure_set(v___f_1641_, 0, v_acc_1524_);
lean_closure_set(v___f_1641_, 1, v_declInfos_1521_);
lean_closure_set(v___f_1641_, 2, v_k_1522_);
lean_closure_set(v___f_1641_, 3, v___x_1640_);
v___x_1642_ = lean_unbox(v_fst_1636_);
lean_dec(v_fst_1636_);
v___x_1643_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19_spec__21___redArg(v_fst_1635_, v___x_1642_, v_a_1639_, v___f_1641_, v_kind_1523_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_);
return v___x_1643_;
}
else
{
lean_object* v_a_1644_; lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1651_; 
lean_dec(v_fst_1636_);
lean_dec(v_fst_1635_);
lean_dec_ref(v_acc_1524_);
lean_dec_ref(v_k_1522_);
lean_dec_ref(v_declInfos_1521_);
v_a_1644_ = lean_ctor_get(v___x_1638_, 0);
v_isSharedCheck_1651_ = !lean_is_exclusive(v___x_1638_);
if (v_isSharedCheck_1651_ == 0)
{
v___x_1646_ = v___x_1638_;
v_isShared_1647_ = v_isSharedCheck_1651_;
goto v_resetjp_1645_;
}
else
{
lean_inc(v_a_1644_);
lean_dec(v___x_1638_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1651_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
lean_object* v___x_1649_; 
if (v_isShared_1647_ == 0)
{
v___x_1649_ = v___x_1646_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v_a_1644_);
v___x_1649_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
return v___x_1649_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___lam__1(lean_object* v_acc_1670_, lean_object* v_declInfos_1671_, lean_object* v_k_1672_, uint8_t v_kind_1673_, lean_object* v_x_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_){
_start:
{
lean_object* v___x_1684_; lean_object* v___x_1685_; 
v___x_1684_ = lean_array_push(v_acc_1670_, v_x_1674_);
v___x_1685_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19(v_declInfos_1671_, v_k_1672_, v_kind_1673_, v___x_1684_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_);
return v___x_1685_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___boxed(lean_object* v_declInfos_1686_, lean_object* v_k_1687_, lean_object* v_kind_1688_, lean_object* v_acc_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_){
_start:
{
uint8_t v_kind_boxed_1699_; lean_object* v_res_1700_; 
v_kind_boxed_1699_ = lean_unbox(v_kind_1688_);
v_res_1700_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19(v_declInfos_1686_, v_k_1687_, v_kind_boxed_1699_, v_acc_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_);
lean_dec(v___y_1697_);
lean_dec_ref(v___y_1696_);
lean_dec(v___y_1695_);
lean_dec_ref(v___y_1694_);
lean_dec(v___y_1693_);
lean_dec_ref(v___y_1692_);
lean_dec(v___y_1691_);
lean_dec_ref(v___y_1690_);
return v_res_1700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14(lean_object* v_declInfos_1701_, lean_object* v_k_1702_, uint8_t v_kind_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_){
_start:
{
lean_object* v___x_1713_; lean_object* v___x_1714_; 
v___x_1713_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__1));
v___x_1714_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19(v_declInfos_1701_, v_k_1702_, v_kind_1703_, v___x_1713_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_);
return v___x_1714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14___boxed(lean_object* v_declInfos_1715_, lean_object* v_k_1716_, lean_object* v_kind_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_){
_start:
{
uint8_t v_kind_boxed_1727_; lean_object* v_res_1728_; 
v_kind_boxed_1727_ = lean_unbox(v_kind_1717_);
v_res_1728_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14(v_declInfos_1715_, v_k_1716_, v_kind_boxed_1727_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_);
lean_dec(v___y_1725_);
lean_dec_ref(v___y_1724_);
lean_dec(v___y_1723_);
lean_dec_ref(v___y_1722_);
lean_dec(v___y_1721_);
lean_dec_ref(v___y_1720_);
lean_dec(v___y_1719_);
lean_dec_ref(v___y_1718_);
return v_res_1728_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__13(size_t v_sz_1729_, size_t v_i_1730_, lean_object* v_bs_1731_){
_start:
{
uint8_t v___x_1732_; 
v___x_1732_ = lean_usize_dec_lt(v_i_1730_, v_sz_1729_);
if (v___x_1732_ == 0)
{
return v_bs_1731_;
}
else
{
lean_object* v_v_1733_; lean_object* v_fst_1734_; lean_object* v_snd_1735_; lean_object* v___x_1737_; uint8_t v_isShared_1738_; uint8_t v_isSharedCheck_1751_; 
v_v_1733_ = lean_array_uget(v_bs_1731_, v_i_1730_);
v_fst_1734_ = lean_ctor_get(v_v_1733_, 0);
v_snd_1735_ = lean_ctor_get(v_v_1733_, 1);
v_isSharedCheck_1751_ = !lean_is_exclusive(v_v_1733_);
if (v_isSharedCheck_1751_ == 0)
{
v___x_1737_ = v_v_1733_;
v_isShared_1738_ = v_isSharedCheck_1751_;
goto v_resetjp_1736_;
}
else
{
lean_inc(v_snd_1735_);
lean_inc(v_fst_1734_);
lean_dec(v_v_1733_);
v___x_1737_ = lean_box(0);
v_isShared_1738_ = v_isSharedCheck_1751_;
goto v_resetjp_1736_;
}
v_resetjp_1736_:
{
lean_object* v___x_1739_; lean_object* v_bs_x27_1740_; uint8_t v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1744_; 
v___x_1739_ = lean_unsigned_to_nat(0u);
v_bs_x27_1740_ = lean_array_uset(v_bs_1731_, v_i_1730_, v___x_1739_);
v___x_1741_ = 0;
v___x_1742_ = lean_box(v___x_1741_);
if (v_isShared_1738_ == 0)
{
lean_ctor_set(v___x_1737_, 0, v___x_1742_);
v___x_1744_ = v___x_1737_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v___x_1742_);
lean_ctor_set(v_reuseFailAlloc_1750_, 1, v_snd_1735_);
v___x_1744_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
lean_object* v___x_1745_; size_t v___x_1746_; size_t v___x_1747_; lean_object* v___x_1748_; 
v___x_1745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1745_, 0, v_fst_1734_);
lean_ctor_set(v___x_1745_, 1, v___x_1744_);
v___x_1746_ = ((size_t)1ULL);
v___x_1747_ = lean_usize_add(v_i_1730_, v___x_1746_);
v___x_1748_ = lean_array_uset(v_bs_x27_1740_, v_i_1730_, v___x_1745_);
v_i_1730_ = v___x_1747_;
v_bs_1731_ = v___x_1748_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__13___boxed(lean_object* v_sz_1752_, lean_object* v_i_1753_, lean_object* v_bs_1754_){
_start:
{
size_t v_sz_boxed_1755_; size_t v_i_boxed_1756_; lean_object* v_res_1757_; 
v_sz_boxed_1755_ = lean_unbox_usize(v_sz_1752_);
lean_dec(v_sz_1752_);
v_i_boxed_1756_ = lean_unbox_usize(v_i_1753_);
lean_dec(v_i_1753_);
v_res_1757_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__13(v_sz_boxed_1755_, v_i_boxed_1756_, v_bs_1754_);
return v_res_1757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8(lean_object* v_declInfos_1758_, lean_object* v_k_1759_, uint8_t v_kind_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_){
_start:
{
size_t v_sz_1770_; size_t v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; 
v_sz_1770_ = lean_array_size(v_declInfos_1758_);
v___x_1771_ = ((size_t)0ULL);
v___x_1772_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__13(v_sz_1770_, v___x_1771_, v_declInfos_1758_);
v___x_1773_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14(v___x_1772_, v_k_1759_, v_kind_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_);
return v___x_1773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8___boxed(lean_object* v_declInfos_1774_, lean_object* v_k_1775_, lean_object* v_kind_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_){
_start:
{
uint8_t v_kind_boxed_1786_; lean_object* v_res_1787_; 
v_kind_boxed_1786_ = lean_unbox(v_kind_1776_);
v_res_1787_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8(v_declInfos_1774_, v_k_1775_, v_kind_boxed_1786_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_);
lean_dec(v___y_1784_);
lean_dec_ref(v___y_1783_);
lean_dec(v___y_1782_);
lean_dec_ref(v___y_1781_);
lean_dec(v___y_1780_);
lean_dec_ref(v___y_1779_);
lean_dec(v___y_1778_);
lean_dec_ref(v___y_1777_);
return v_res_1787_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__7___lam__0(lean_object* v_snd_1788_, lean_object* v_x_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_){
_start:
{
lean_object* v___x_1799_; 
v___x_1799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1799_, 0, v_snd_1788_);
return v___x_1799_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__7___lam__0___boxed(lean_object* v_snd_1800_, lean_object* v_x_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_){
_start:
{
lean_object* v_res_1811_; 
v_res_1811_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__7___lam__0(v_snd_1800_, v_x_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_);
lean_dec(v___y_1809_);
lean_dec_ref(v___y_1808_);
lean_dec(v___y_1807_);
lean_dec_ref(v___y_1806_);
lean_dec(v___y_1805_);
lean_dec_ref(v___y_1804_);
lean_dec(v___y_1803_);
lean_dec_ref(v___y_1802_);
lean_dec_ref(v_x_1801_);
return v_res_1811_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__7(size_t v_sz_1812_, size_t v_i_1813_, lean_object* v_bs_1814_){
_start:
{
uint8_t v___x_1815_; 
v___x_1815_ = lean_usize_dec_lt(v_i_1813_, v_sz_1812_);
if (v___x_1815_ == 0)
{
return v_bs_1814_;
}
else
{
lean_object* v_v_1816_; lean_object* v_fst_1817_; lean_object* v_snd_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1832_; 
v_v_1816_ = lean_array_uget(v_bs_1814_, v_i_1813_);
v_fst_1817_ = lean_ctor_get(v_v_1816_, 0);
v_snd_1818_ = lean_ctor_get(v_v_1816_, 1);
v_isSharedCheck_1832_ = !lean_is_exclusive(v_v_1816_);
if (v_isSharedCheck_1832_ == 0)
{
v___x_1820_ = v_v_1816_;
v_isShared_1821_ = v_isSharedCheck_1832_;
goto v_resetjp_1819_;
}
else
{
lean_inc(v_snd_1818_);
lean_inc(v_fst_1817_);
lean_dec(v_v_1816_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1832_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
lean_object* v___x_1822_; lean_object* v_bs_x27_1823_; lean_object* v___f_1824_; lean_object* v___x_1826_; 
v___x_1822_ = lean_unsigned_to_nat(0u);
v_bs_x27_1823_ = lean_array_uset(v_bs_1814_, v_i_1813_, v___x_1822_);
v___f_1824_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__7___lam__0___boxed), 11, 1);
lean_closure_set(v___f_1824_, 0, v_snd_1818_);
if (v_isShared_1821_ == 0)
{
lean_ctor_set(v___x_1820_, 1, v___f_1824_);
v___x_1826_ = v___x_1820_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v_fst_1817_);
lean_ctor_set(v_reuseFailAlloc_1831_, 1, v___f_1824_);
v___x_1826_ = v_reuseFailAlloc_1831_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
size_t v___x_1827_; size_t v___x_1828_; lean_object* v___x_1829_; 
v___x_1827_ = ((size_t)1ULL);
v___x_1828_ = lean_usize_add(v_i_1813_, v___x_1827_);
v___x_1829_ = lean_array_uset(v_bs_x27_1823_, v_i_1813_, v___x_1826_);
v_i_1813_ = v___x_1828_;
v_bs_1814_ = v___x_1829_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__7___boxed(lean_object* v_sz_1833_, lean_object* v_i_1834_, lean_object* v_bs_1835_){
_start:
{
size_t v_sz_boxed_1836_; size_t v_i_boxed_1837_; lean_object* v_res_1838_; 
v_sz_boxed_1836_ = lean_unbox_usize(v_sz_1833_);
lean_dec(v_sz_1833_);
v_i_boxed_1837_ = lean_unbox_usize(v_i_1834_);
lean_dec(v_i_1834_);
v_res_1838_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__7(v_sz_boxed_1836_, v_i_boxed_1837_, v_bs_1835_);
return v_res_1838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5(lean_object* v_declInfos_1839_, lean_object* v_k_1840_, uint8_t v_kind_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_){
_start:
{
size_t v_sz_1851_; size_t v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; 
v_sz_1851_ = lean_array_size(v_declInfos_1839_);
v___x_1852_ = ((size_t)0ULL);
v___x_1853_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__7(v_sz_1851_, v___x_1852_, v_declInfos_1839_);
v___x_1854_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8(v___x_1853_, v_k_1840_, v_kind_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_);
return v___x_1854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5___boxed(lean_object* v_declInfos_1855_, lean_object* v_k_1856_, lean_object* v_kind_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_){
_start:
{
uint8_t v_kind_boxed_1867_; lean_object* v_res_1868_; 
v_kind_boxed_1867_ = lean_unbox(v_kind_1857_);
v_res_1868_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5(v_declInfos_1855_, v_k_1856_, v_kind_boxed_1867_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_);
lean_dec(v___y_1865_);
lean_dec_ref(v___y_1864_);
lean_dec(v___y_1863_);
lean_dec_ref(v___y_1862_);
lean_dec(v___y_1861_);
lean_dec_ref(v___y_1860_);
lean_dec(v___y_1859_);
lean_dec_ref(v___y_1858_);
return v_res_1868_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__3(size_t v_sz_1869_, size_t v_i_1870_, lean_object* v_bs_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_){
_start:
{
uint8_t v___x_1877_; 
v___x_1877_ = lean_usize_dec_lt(v_i_1870_, v_sz_1869_);
if (v___x_1877_ == 0)
{
lean_object* v___x_1878_; 
v___x_1878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1878_, 0, v_bs_1871_);
return v___x_1878_;
}
else
{
lean_object* v_v_1879_; lean_object* v___x_1880_; 
v_v_1879_ = lean_array_uget_borrowed(v_bs_1871_, v_i_1870_);
lean_inc(v___y_1875_);
lean_inc_ref(v___y_1874_);
lean_inc(v___y_1873_);
lean_inc_ref(v___y_1872_);
lean_inc(v_v_1879_);
v___x_1880_ = lean_infer_type(v_v_1879_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_);
if (lean_obj_tag(v___x_1880_) == 0)
{
lean_object* v_a_1881_; lean_object* v___x_1882_; lean_object* v_bs_x27_1883_; size_t v___x_1884_; size_t v___x_1885_; lean_object* v___x_1886_; 
v_a_1881_ = lean_ctor_get(v___x_1880_, 0);
lean_inc(v_a_1881_);
lean_dec_ref_known(v___x_1880_, 1);
v___x_1882_ = lean_unsigned_to_nat(0u);
v_bs_x27_1883_ = lean_array_uset(v_bs_1871_, v_i_1870_, v___x_1882_);
v___x_1884_ = ((size_t)1ULL);
v___x_1885_ = lean_usize_add(v_i_1870_, v___x_1884_);
v___x_1886_ = lean_array_uset(v_bs_x27_1883_, v_i_1870_, v_a_1881_);
v_i_1870_ = v___x_1885_;
v_bs_1871_ = v___x_1886_;
goto _start;
}
else
{
lean_object* v_a_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1895_; 
lean_dec_ref(v_bs_1871_);
v_a_1888_ = lean_ctor_get(v___x_1880_, 0);
v_isSharedCheck_1895_ = !lean_is_exclusive(v___x_1880_);
if (v_isSharedCheck_1895_ == 0)
{
v___x_1890_ = v___x_1880_;
v_isShared_1891_ = v_isSharedCheck_1895_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_a_1888_);
lean_dec(v___x_1880_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1895_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
lean_object* v___x_1893_; 
if (v_isShared_1891_ == 0)
{
v___x_1893_ = v___x_1890_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v_a_1888_);
v___x_1893_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
return v___x_1893_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__3___boxed(lean_object* v_sz_1896_, lean_object* v_i_1897_, lean_object* v_bs_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_){
_start:
{
size_t v_sz_boxed_1904_; size_t v_i_boxed_1905_; lean_object* v_res_1906_; 
v_sz_boxed_1904_ = lean_unbox_usize(v_sz_1896_);
lean_dec(v_sz_1896_);
v_i_boxed_1905_ = lean_unbox_usize(v_i_1897_);
lean_dec(v_i_1897_);
v_res_1906_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__3(v_sz_boxed_1904_, v_i_boxed_1905_, v_bs_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_);
lean_dec(v___y_1902_);
lean_dec_ref(v___y_1901_);
lean_dec(v___y_1900_);
lean_dec_ref(v___y_1899_);
return v_res_1906_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__2___redArg(size_t v_sz_1907_, size_t v_i_1908_, lean_object* v_bs_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_){
_start:
{
uint8_t v___x_1915_; 
v___x_1915_ = lean_usize_dec_lt(v_i_1908_, v_sz_1907_);
if (v___x_1915_ == 0)
{
lean_object* v___x_1916_; 
v___x_1916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1916_, 0, v_bs_1909_);
return v___x_1916_;
}
else
{
lean_object* v_v_1917_; lean_object* v_fst_1918_; lean_object* v_snd_1919_; lean_object* v___x_1920_; 
v_v_1917_ = lean_array_uget_borrowed(v_bs_1909_, v_i_1908_);
v_fst_1918_ = lean_ctor_get(v_v_1917_, 0);
v_snd_1919_ = lean_ctor_get(v_v_1917_, 1);
lean_inc(v_fst_1918_);
lean_inc(v_snd_1919_);
v___x_1920_ = l_Lean_Meta_mkEq(v_snd_1919_, v_fst_1918_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_);
if (lean_obj_tag(v___x_1920_) == 0)
{
lean_object* v_a_1921_; lean_object* v___x_1922_; lean_object* v_bs_x27_1923_; size_t v___x_1924_; size_t v___x_1925_; lean_object* v___x_1926_; 
v_a_1921_ = lean_ctor_get(v___x_1920_, 0);
lean_inc(v_a_1921_);
lean_dec_ref_known(v___x_1920_, 1);
v___x_1922_ = lean_unsigned_to_nat(0u);
v_bs_x27_1923_ = lean_array_uset(v_bs_1909_, v_i_1908_, v___x_1922_);
v___x_1924_ = ((size_t)1ULL);
v___x_1925_ = lean_usize_add(v_i_1908_, v___x_1924_);
v___x_1926_ = lean_array_uset(v_bs_x27_1923_, v_i_1908_, v_a_1921_);
v_i_1908_ = v___x_1925_;
v_bs_1909_ = v___x_1926_;
goto _start;
}
else
{
lean_object* v_a_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1935_; 
lean_dec_ref(v_bs_1909_);
v_a_1928_ = lean_ctor_get(v___x_1920_, 0);
v_isSharedCheck_1935_ = !lean_is_exclusive(v___x_1920_);
if (v_isSharedCheck_1935_ == 0)
{
v___x_1930_ = v___x_1920_;
v_isShared_1931_ = v_isSharedCheck_1935_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_a_1928_);
lean_dec(v___x_1920_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1935_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v___x_1933_; 
if (v_isShared_1931_ == 0)
{
v___x_1933_ = v___x_1930_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v_a_1928_);
v___x_1933_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
return v___x_1933_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__2___redArg___boxed(lean_object* v_sz_1936_, lean_object* v_i_1937_, lean_object* v_bs_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_){
_start:
{
size_t v_sz_boxed_1944_; size_t v_i_boxed_1945_; lean_object* v_res_1946_; 
v_sz_boxed_1944_ = lean_unbox_usize(v_sz_1936_);
lean_dec(v_sz_1936_);
v_i_boxed_1945_ = lean_unbox_usize(v_i_1937_);
lean_dec(v_i_1937_);
v_res_1946_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__2___redArg(v_sz_boxed_1944_, v_i_boxed_1945_, v_bs_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_);
lean_dec(v___y_1942_);
lean_dec_ref(v___y_1941_);
lean_dec(v___y_1940_);
lean_dec_ref(v___y_1939_);
return v_res_1946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1___lam__0(lean_object* v_revertArgs_1947_, lean_object* v_hypName_1948_, lean_object* v_u_1949_, lean_object* v_00_u03c3s_1950_, uint8_t v___x_1951_, lean_object* v_hyps_1952_, lean_object* v_ss_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_){
_start:
{
lean_object* v___x_1963_; size_t v_sz_1964_; size_t v___x_1965_; lean_object* v___x_1966_; 
v___x_1963_ = l_Array_zip___redArg(v_revertArgs_1947_, v_ss_1953_);
v_sz_1964_ = lean_array_size(v___x_1963_);
v___x_1965_ = ((size_t)0ULL);
v___x_1966_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__2___redArg(v_sz_1964_, v___x_1965_, v___x_1963_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_);
if (lean_obj_tag(v___x_1966_) == 0)
{
lean_object* v_a_1967_; lean_object* v___x_1968_; 
v_a_1967_ = lean_ctor_get(v___x_1966_, 0);
lean_inc(v_a_1967_);
lean_dec_ref_known(v___x_1966_, 1);
lean_inc(v_hypName_1948_);
v___x_1968_ = l_Lean_Core_mkFreshUserName(v_hypName_1948_, v___y_1960_, v___y_1961_);
if (lean_obj_tag(v___x_1968_) == 0)
{
lean_object* v_a_1969_; lean_object* v_eqs_1970_; lean_object* v_00_u03c6_1971_; lean_object* v_00_u03c6_1972_; uint8_t v___x_1973_; uint8_t v___x_1974_; lean_object* v___x_1975_; 
v_a_1969_ = lean_ctor_get(v___x_1968_, 0);
lean_inc(v_a_1969_);
lean_dec_ref_known(v___x_1968_, 1);
v_eqs_1970_ = lean_array_to_list(v_a_1967_);
v_00_u03c6_1971_ = l_Lean_mkAndN(v_eqs_1970_);
v_00_u03c6_1972_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure(v_u_1949_, v_00_u03c3s_1950_, v_00_u03c6_1971_);
v___x_1973_ = 1;
v___x_1974_ = 1;
v___x_1975_ = l_Lean_Meta_mkLambdaFVars(v_ss_1953_, v_00_u03c6_1972_, v___x_1951_, v___x_1973_, v___x_1951_, v___x_1973_, v___x_1974_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_);
if (lean_obj_tag(v___x_1975_) == 0)
{
lean_object* v_a_1976_; lean_object* v___x_1977_; 
v_a_1976_ = lean_ctor_get(v___x_1975_, 0);
lean_inc(v_a_1976_);
lean_dec_ref_known(v___x_1975_, 1);
v___x_1977_ = l_Lean_Meta_mkLambdaFVars(v_ss_1953_, v_hyps_1952_, v___x_1951_, v___x_1973_, v___x_1951_, v___x_1973_, v___x_1974_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_);
if (lean_obj_tag(v___x_1977_) == 0)
{
lean_object* v_a_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_1988_; 
v_a_1978_ = lean_ctor_get(v___x_1977_, 0);
v_isSharedCheck_1988_ = !lean_is_exclusive(v___x_1977_);
if (v_isSharedCheck_1988_ == 0)
{
v___x_1980_ = v___x_1977_;
v_isShared_1981_ = v_isSharedCheck_1988_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_a_1978_);
lean_dec(v___x_1977_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_1988_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
lean_object* v___x_1982_; lean_object* v_00_u03c6_1983_; lean_object* v___x_1984_; lean_object* v___x_1986_; 
v___x_1982_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1982_, 0, v_hypName_1948_);
lean_ctor_set(v___x_1982_, 1, v_a_1969_);
lean_ctor_set(v___x_1982_, 2, v_a_1976_);
v_00_u03c6_1983_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_1982_);
v___x_1984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1984_, 0, v_a_1978_);
lean_ctor_set(v___x_1984_, 1, v_00_u03c6_1983_);
if (v_isShared_1981_ == 0)
{
lean_ctor_set(v___x_1980_, 0, v___x_1984_);
v___x_1986_ = v___x_1980_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v___x_1984_);
v___x_1986_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
return v___x_1986_;
}
}
}
else
{
lean_object* v_a_1989_; lean_object* v___x_1991_; uint8_t v_isShared_1992_; uint8_t v_isSharedCheck_1996_; 
lean_dec(v_a_1976_);
lean_dec(v_a_1969_);
lean_dec(v_hypName_1948_);
v_a_1989_ = lean_ctor_get(v___x_1977_, 0);
v_isSharedCheck_1996_ = !lean_is_exclusive(v___x_1977_);
if (v_isSharedCheck_1996_ == 0)
{
v___x_1991_ = v___x_1977_;
v_isShared_1992_ = v_isSharedCheck_1996_;
goto v_resetjp_1990_;
}
else
{
lean_inc(v_a_1989_);
lean_dec(v___x_1977_);
v___x_1991_ = lean_box(0);
v_isShared_1992_ = v_isSharedCheck_1996_;
goto v_resetjp_1990_;
}
v_resetjp_1990_:
{
lean_object* v___x_1994_; 
if (v_isShared_1992_ == 0)
{
v___x_1994_ = v___x_1991_;
goto v_reusejp_1993_;
}
else
{
lean_object* v_reuseFailAlloc_1995_; 
v_reuseFailAlloc_1995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1995_, 0, v_a_1989_);
v___x_1994_ = v_reuseFailAlloc_1995_;
goto v_reusejp_1993_;
}
v_reusejp_1993_:
{
return v___x_1994_;
}
}
}
}
else
{
lean_object* v_a_1997_; lean_object* v___x_1999_; uint8_t v_isShared_2000_; uint8_t v_isSharedCheck_2004_; 
lean_dec(v_a_1969_);
lean_dec_ref(v_hyps_1952_);
lean_dec(v_hypName_1948_);
v_a_1997_ = lean_ctor_get(v___x_1975_, 0);
v_isSharedCheck_2004_ = !lean_is_exclusive(v___x_1975_);
if (v_isSharedCheck_2004_ == 0)
{
v___x_1999_ = v___x_1975_;
v_isShared_2000_ = v_isSharedCheck_2004_;
goto v_resetjp_1998_;
}
else
{
lean_inc(v_a_1997_);
lean_dec(v___x_1975_);
v___x_1999_ = lean_box(0);
v_isShared_2000_ = v_isSharedCheck_2004_;
goto v_resetjp_1998_;
}
v_resetjp_1998_:
{
lean_object* v___x_2002_; 
if (v_isShared_2000_ == 0)
{
v___x_2002_ = v___x_1999_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v_a_1997_);
v___x_2002_ = v_reuseFailAlloc_2003_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
return v___x_2002_;
}
}
}
}
else
{
lean_object* v_a_2005_; lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2012_; 
lean_dec(v_a_1967_);
lean_dec_ref(v_hyps_1952_);
lean_dec_ref(v_00_u03c3s_1950_);
lean_dec(v_u_1949_);
lean_dec(v_hypName_1948_);
v_a_2005_ = lean_ctor_get(v___x_1968_, 0);
v_isSharedCheck_2012_ = !lean_is_exclusive(v___x_1968_);
if (v_isSharedCheck_2012_ == 0)
{
v___x_2007_ = v___x_1968_;
v_isShared_2008_ = v_isSharedCheck_2012_;
goto v_resetjp_2006_;
}
else
{
lean_inc(v_a_2005_);
lean_dec(v___x_1968_);
v___x_2007_ = lean_box(0);
v_isShared_2008_ = v_isSharedCheck_2012_;
goto v_resetjp_2006_;
}
v_resetjp_2006_:
{
lean_object* v___x_2010_; 
if (v_isShared_2008_ == 0)
{
v___x_2010_ = v___x_2007_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2011_; 
v_reuseFailAlloc_2011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2011_, 0, v_a_2005_);
v___x_2010_ = v_reuseFailAlloc_2011_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
return v___x_2010_;
}
}
}
}
else
{
lean_object* v_a_2013_; lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2020_; 
lean_dec_ref(v_hyps_1952_);
lean_dec_ref(v_00_u03c3s_1950_);
lean_dec(v_u_1949_);
lean_dec(v_hypName_1948_);
v_a_2013_ = lean_ctor_get(v___x_1966_, 0);
v_isSharedCheck_2020_ = !lean_is_exclusive(v___x_1966_);
if (v_isSharedCheck_2020_ == 0)
{
v___x_2015_ = v___x_1966_;
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
else
{
lean_inc(v_a_2013_);
lean_dec(v___x_1966_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
lean_object* v___x_2018_; 
if (v_isShared_2016_ == 0)
{
v___x_2018_ = v___x_2015_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v_a_2013_);
v___x_2018_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
return v___x_2018_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1___lam__0___boxed(lean_object* v_revertArgs_2021_, lean_object* v_hypName_2022_, lean_object* v_u_2023_, lean_object* v_00_u03c3s_2024_, lean_object* v___x_2025_, lean_object* v_hyps_2026_, lean_object* v_ss_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_){
_start:
{
uint8_t v___x_21488__boxed_2037_; lean_object* v_res_2038_; 
v___x_21488__boxed_2037_ = lean_unbox(v___x_2025_);
v_res_2038_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1___lam__0(v_revertArgs_2021_, v_hypName_2022_, v_u_2023_, v_00_u03c3s_2024_, v___x_21488__boxed_2037_, v_hyps_2026_, v_ss_2027_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_);
lean_dec(v___y_2035_);
lean_dec_ref(v___y_2034_);
lean_dec(v___y_2033_);
lean_dec_ref(v___y_2032_);
lean_dec(v___y_2031_);
lean_dec_ref(v___y_2030_);
lean_dec(v___y_2029_);
lean_dec_ref(v___y_2028_);
lean_dec_ref(v_ss_2027_);
lean_dec_ref(v_revertArgs_2021_);
return v_res_2038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1(lean_object* v_goal_2039_, lean_object* v_n_2040_, lean_object* v_hypName_2041_, lean_object* v_k_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_){
_start:
{
lean_object* v___x_2052_; uint8_t v___x_2053_; 
v___x_2052_ = lean_unsigned_to_nat(0u);
v___x_2053_ = lean_nat_dec_eq(v_n_2040_, v___x_2052_);
if (v___x_2053_ == 0)
{
lean_object* v_u_2054_; lean_object* v_00_u03c3s_2055_; lean_object* v_hyps_2056_; lean_object* v_target_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2211_; 
v_u_2054_ = lean_ctor_get(v_goal_2039_, 0);
v_00_u03c3s_2055_ = lean_ctor_get(v_goal_2039_, 1);
v_hyps_2056_ = lean_ctor_get(v_goal_2039_, 2);
v_target_2057_ = lean_ctor_get(v_goal_2039_, 3);
v_isSharedCheck_2211_ = !lean_is_exclusive(v_goal_2039_);
if (v_isSharedCheck_2211_ == 0)
{
v___x_2059_ = v_goal_2039_;
v_isShared_2060_ = v_isSharedCheck_2211_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_target_2057_);
lean_inc(v_hyps_2056_);
lean_inc(v_00_u03c3s_2055_);
lean_inc(v_u_2054_);
lean_dec(v_goal_2039_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2211_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v_T_2061_; lean_object* v_f_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v_a_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v_revertArgs_2069_; lean_object* v___y_2071_; lean_object* v___y_2072_; lean_object* v___y_2073_; lean_object* v___y_2074_; lean_object* v___y_2075_; lean_object* v___y_2076_; lean_object* v___y_2077_; lean_object* v___y_2078_; lean_object* v___y_2079_; lean_object* v___y_2080_; lean_object* v___y_2081_; lean_object* v___y_2082_; lean_object* v___x_2121_; lean_object* v___f_2122_; lean_object* v___y_2124_; lean_object* v___y_2125_; lean_object* v___y_2126_; lean_object* v___y_2127_; lean_object* v___y_2128_; lean_object* v___y_2129_; lean_object* v___y_2130_; lean_object* v___y_2131_; lean_object* v___x_2185_; uint8_t v___x_2186_; 
v_T_2061_ = l_Lean_Expr_consumeMData(v_target_2057_);
v_f_2062_ = l_Lean_Expr_getAppFn(v_T_2061_);
v___x_2063_ = l_Lean_Expr_getAppNumArgs(v_T_2061_);
v___x_2064_ = lean_mk_empty_array_with_capacity(v___x_2063_);
lean_dec(v___x_2063_);
lean_inc_ref(v_T_2061_);
v_a_2065_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_T_2061_, v___x_2064_);
lean_inc(v_n_2040_);
lean_inc_ref(v_a_2065_);
v___x_2066_ = l_Array_toSubarray___redArg(v_a_2065_, v___x_2052_, v_n_2040_);
v___x_2067_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__1));
v___x_2068_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__1___redArg(v___x_2066_, v___x_2067_);
v_revertArgs_2069_ = l_Array_reverse___redArg(v___x_2068_);
v___x_2121_ = lean_box(v___x_2053_);
lean_inc_ref(v_hyps_2056_);
lean_inc_ref(v_00_u03c3s_2055_);
lean_inc(v_u_2054_);
lean_inc_ref(v_revertArgs_2069_);
v___f_2122_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1___lam__0___boxed), 16, 6);
lean_closure_set(v___f_2122_, 0, v_revertArgs_2069_);
lean_closure_set(v___f_2122_, 1, v_hypName_2041_);
lean_closure_set(v___f_2122_, 2, v_u_2054_);
lean_closure_set(v___f_2122_, 3, v_00_u03c3s_2055_);
lean_closure_set(v___f_2122_, 4, v___x_2121_);
lean_closure_set(v___f_2122_, 5, v_hyps_2056_);
v___x_2185_ = lean_array_get_size(v_revertArgs_2069_);
v___x_2186_ = lean_nat_dec_eq(v___x_2185_, v_n_2040_);
if (v___x_2186_ == 0)
{
lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v_a_2203_; lean_object* v___x_2205_; uint8_t v_isShared_2206_; uint8_t v_isSharedCheck_2210_; 
lean_dec_ref(v___f_2122_);
lean_dec_ref(v_revertArgs_2069_);
lean_dec_ref(v_a_2065_);
lean_dec_ref(v_f_2062_);
lean_del_object(v___x_2059_);
lean_dec_ref(v_target_2057_);
lean_dec_ref(v_hyps_2056_);
lean_dec_ref(v_00_u03c3s_2055_);
lean_dec(v_u_2054_);
lean_dec_ref(v_k_2042_);
v___x_2187_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__3, &l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__3_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__3);
v___x_2188_ = l_Nat_reprFast(v_n_2040_);
v___x_2189_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2189_, 0, v___x_2188_);
v___x_2190_ = l_Lean_MessageData_ofFormat(v___x_2189_);
v___x_2191_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2191_, 0, v___x_2187_);
lean_ctor_set(v___x_2191_, 1, v___x_2190_);
v___x_2192_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__5, &l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__5_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__5);
v___x_2193_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2193_, 0, v___x_2191_);
lean_ctor_set(v___x_2193_, 1, v___x_2192_);
v___x_2194_ = l_Lean_MessageData_ofExpr(v_T_2061_);
v___x_2195_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2195_, 0, v___x_2193_);
lean_ctor_set(v___x_2195_, 1, v___x_2194_);
v___x_2196_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__7, &l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__7_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__7);
v___x_2197_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2197_, 0, v___x_2195_);
lean_ctor_set(v___x_2197_, 1, v___x_2196_);
v___x_2198_ = l_Nat_reprFast(v___x_2185_);
v___x_2199_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2199_, 0, v___x_2198_);
v___x_2200_ = l_Lean_MessageData_ofFormat(v___x_2199_);
v___x_2201_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2201_, 0, v___x_2197_);
lean_ctor_set(v___x_2201_, 1, v___x_2200_);
v___x_2202_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__8___redArg(v___x_2201_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_);
v_a_2203_ = lean_ctor_get(v___x_2202_, 0);
v_isSharedCheck_2210_ = !lean_is_exclusive(v___x_2202_);
if (v_isSharedCheck_2210_ == 0)
{
v___x_2205_ = v___x_2202_;
v_isShared_2206_ = v_isSharedCheck_2210_;
goto v_resetjp_2204_;
}
else
{
lean_inc(v_a_2203_);
lean_dec(v___x_2202_);
v___x_2205_ = lean_box(0);
v_isShared_2206_ = v_isSharedCheck_2210_;
goto v_resetjp_2204_;
}
v_resetjp_2204_:
{
lean_object* v___x_2208_; 
if (v_isShared_2206_ == 0)
{
v___x_2208_ = v___x_2205_;
goto v_reusejp_2207_;
}
else
{
lean_object* v_reuseFailAlloc_2209_; 
v_reuseFailAlloc_2209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2209_, 0, v_a_2203_);
v___x_2208_ = v_reuseFailAlloc_2209_;
goto v_reusejp_2207_;
}
v_reusejp_2207_:
{
return v___x_2208_;
}
}
}
else
{
lean_dec_ref(v_T_2061_);
v___y_2124_ = v___y_2043_;
v___y_2125_ = v___y_2044_;
v___y_2126_ = v___y_2045_;
v___y_2127_ = v___y_2046_;
v___y_2128_ = v___y_2047_;
v___y_2129_ = v___y_2048_;
v___y_2130_ = v___y_2049_;
v___y_2131_ = v___y_2050_;
goto v___jp_2123_;
}
v___jp_2070_:
{
lean_object* v___x_2083_; 
v___x_2083_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v___y_2074_, v___y_2076_);
if (lean_obj_tag(v___x_2083_) == 0)
{
lean_object* v_a_2084_; lean_object* v_H_2085_; lean_object* v___x_2086_; lean_object* v_fst_2087_; lean_object* v_snd_2088_; lean_object* v___x_2090_; uint8_t v_isShared_2091_; uint8_t v_isSharedCheck_2120_; 
v_a_2084_ = lean_ctor_get(v___x_2083_, 0);
lean_inc(v_a_2084_);
lean_dec_ref_known(v___x_2083_, 1);
lean_inc_ref_n(v___y_2082_, 2);
v_H_2085_ = l_Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps(v___y_2082_, v_a_2084_);
lean_inc(v_u_2054_);
v___x_2086_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd(v_u_2054_, v___y_2082_, v_H_2085_, v___y_2071_);
v_fst_2087_ = lean_ctor_get(v___x_2086_, 0);
v_snd_2088_ = lean_ctor_get(v___x_2086_, 1);
v_isSharedCheck_2120_ = !lean_is_exclusive(v___x_2086_);
if (v_isSharedCheck_2120_ == 0)
{
v___x_2090_ = v___x_2086_;
v_isShared_2091_ = v_isSharedCheck_2120_;
goto v_resetjp_2089_;
}
else
{
lean_inc(v_snd_2088_);
lean_inc(v_fst_2087_);
lean_dec(v___x_2086_);
v___x_2090_ = lean_box(0);
v_isShared_2091_ = v_isSharedCheck_2120_;
goto v_resetjp_2089_;
}
v_resetjp_2089_:
{
lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v_goal_x27_2097_; 
v___x_2092_ = lean_array_get_size(v_a_2065_);
v___x_2093_ = l_Array_toSubarray___redArg(v_a_2065_, v_n_2040_, v___x_2092_);
v___x_2094_ = l_Subarray_copy___redArg(v___x_2093_);
v___x_2095_ = l_Lean_mkAppRev(v_f_2062_, v___x_2094_);
lean_dec_ref(v___x_2094_);
lean_inc(v_fst_2087_);
lean_inc(v_u_2054_);
if (v_isShared_2060_ == 0)
{
lean_ctor_set(v___x_2059_, 3, v___x_2095_);
lean_ctor_set(v___x_2059_, 2, v_fst_2087_);
lean_ctor_set(v___x_2059_, 1, v___y_2082_);
v_goal_x27_2097_ = v___x_2059_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v_u_2054_);
lean_ctor_set(v_reuseFailAlloc_2119_, 1, v___y_2082_);
lean_ctor_set(v_reuseFailAlloc_2119_, 2, v_fst_2087_);
lean_ctor_set(v_reuseFailAlloc_2119_, 3, v___x_2095_);
v_goal_x27_2097_ = v_reuseFailAlloc_2119_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
lean_object* v___x_2098_; 
lean_inc(v___y_2075_);
lean_inc_ref(v___y_2079_);
lean_inc(v___y_2076_);
lean_inc_ref(v___y_2072_);
lean_inc(v___y_2073_);
lean_inc_ref(v___y_2078_);
lean_inc(v___y_2080_);
lean_inc_ref(v___y_2081_);
v___x_2098_ = lean_apply_10(v_k_2042_, v_goal_x27_2097_, v___y_2081_, v___y_2080_, v___y_2078_, v___y_2073_, v___y_2072_, v___y_2076_, v___y_2079_, v___y_2075_, lean_box(0));
if (lean_obj_tag(v___x_2098_) == 0)
{
lean_object* v_a_2099_; lean_object* v___x_2100_; 
v_a_2099_ = lean_ctor_get(v___x_2098_, 0);
lean_inc(v_a_2099_);
lean_dec_ref_known(v___x_2098_, 1);
lean_inc(v___y_2075_);
lean_inc_ref(v___y_2079_);
lean_inc(v___y_2076_);
lean_inc_ref(v___y_2072_);
lean_inc_ref(v___y_2077_);
v___x_2100_ = lean_infer_type(v___y_2077_, v___y_2072_, v___y_2076_, v___y_2079_, v___y_2075_);
if (lean_obj_tag(v___x_2100_) == 0)
{
lean_object* v_a_2101_; lean_object* v___x_2103_; uint8_t v_isShared_2104_; uint8_t v_isSharedCheck_2118_; 
v_a_2101_ = lean_ctor_get(v___x_2100_, 0);
v_isSharedCheck_2118_ = !lean_is_exclusive(v___x_2100_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_2103_ = v___x_2100_;
v_isShared_2104_ = v_isSharedCheck_2118_;
goto v_resetjp_2102_;
}
else
{
lean_inc(v_a_2101_);
lean_dec(v___x_2100_);
v___x_2103_ = lean_box(0);
v_isShared_2104_ = v_isSharedCheck_2118_;
goto v_resetjp_2102_;
}
v_resetjp_2102_:
{
lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2108_; 
v___x_2105_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__12___closed__1));
v___x_2106_ = lean_box(0);
if (v_isShared_2091_ == 0)
{
lean_ctor_set_tag(v___x_2090_, 1);
lean_ctor_set(v___x_2090_, 1, v___x_2106_);
lean_ctor_set(v___x_2090_, 0, v_u_2054_);
v___x_2108_ = v___x_2090_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v_u_2054_);
lean_ctor_set(v_reuseFailAlloc_2117_, 1, v___x_2106_);
v___x_2108_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v_prf_2113_; lean_object* v___x_2115_; 
v___x_2109_ = l_Lean_mkConst(v___x_2105_, v___x_2108_);
v___x_2110_ = l_Lean_mkAppN(v_fst_2087_, v_revertArgs_2069_);
v___x_2111_ = l_Lean_mkAppN(v_snd_2088_, v_revertArgs_2069_);
v___x_2112_ = l_Lean_mkAppN(v_a_2099_, v_revertArgs_2069_);
lean_dec_ref(v_revertArgs_2069_);
v_prf_2113_ = l_Lean_mkApp8(v___x_2109_, v_00_u03c3s_2055_, v_a_2101_, v_hyps_2056_, v___x_2110_, v_target_2057_, v___y_2077_, v___x_2111_, v___x_2112_);
if (v_isShared_2104_ == 0)
{
lean_ctor_set(v___x_2103_, 0, v_prf_2113_);
v___x_2115_ = v___x_2103_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v_prf_2113_);
v___x_2115_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2114_;
}
v_reusejp_2114_:
{
return v___x_2115_;
}
}
}
}
else
{
lean_dec(v_a_2099_);
lean_del_object(v___x_2090_);
lean_dec(v_snd_2088_);
lean_dec(v_fst_2087_);
lean_dec_ref(v___y_2077_);
lean_dec_ref(v_revertArgs_2069_);
lean_dec_ref(v_target_2057_);
lean_dec_ref(v_hyps_2056_);
lean_dec_ref(v_00_u03c3s_2055_);
lean_dec(v_u_2054_);
return v___x_2100_;
}
}
else
{
lean_del_object(v___x_2090_);
lean_dec(v_snd_2088_);
lean_dec(v_fst_2087_);
lean_dec_ref(v___y_2077_);
lean_dec_ref(v_revertArgs_2069_);
lean_dec_ref(v_target_2057_);
lean_dec_ref(v_hyps_2056_);
lean_dec_ref(v_00_u03c3s_2055_);
lean_dec(v_u_2054_);
return v___x_2098_;
}
}
}
}
else
{
lean_dec_ref(v___y_2082_);
lean_dec_ref(v___y_2077_);
lean_dec_ref(v___y_2071_);
lean_dec_ref(v_revertArgs_2069_);
lean_dec_ref(v_a_2065_);
lean_dec_ref(v_f_2062_);
lean_del_object(v___x_2059_);
lean_dec_ref(v_target_2057_);
lean_dec_ref(v_hyps_2056_);
lean_dec_ref(v_00_u03c3s_2055_);
lean_dec(v_u_2054_);
lean_dec_ref(v_k_2042_);
lean_dec(v_n_2040_);
return v___x_2083_;
}
}
v___jp_2123_:
{
size_t v_sz_2132_; size_t v___x_2133_; lean_object* v___x_2134_; 
v_sz_2132_ = lean_array_size(v_revertArgs_2069_);
v___x_2133_ = ((size_t)0ULL);
lean_inc_ref(v_revertArgs_2069_);
v___x_2134_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__3(v_sz_2132_, v___x_2133_, v_revertArgs_2069_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_);
if (lean_obj_tag(v___x_2134_) == 0)
{
lean_object* v_a_2135_; size_t v_sz_2136_; lean_object* v___x_2137_; 
v_a_2135_ = lean_ctor_get(v___x_2134_, 0);
lean_inc_n(v_a_2135_, 2);
lean_dec_ref_known(v___x_2134_, 1);
v_sz_2136_ = lean_array_size(v_a_2135_);
v___x_2137_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__4___redArg(v_sz_2136_, v___x_2133_, v_a_2135_, v___y_2130_, v___y_2131_);
if (lean_obj_tag(v___x_2137_) == 0)
{
lean_object* v_a_2138_; uint8_t v___x_2139_; lean_object* v___x_2140_; 
v_a_2138_ = lean_ctor_get(v___x_2137_, 0);
lean_inc(v_a_2138_);
lean_dec_ref_known(v___x_2137_, 1);
v___x_2139_ = 0;
v___x_2140_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5(v_a_2138_, v___f_2122_, v___x_2139_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_);
if (lean_obj_tag(v___x_2140_) == 0)
{
lean_object* v_a_2141_; lean_object* v_fst_2142_; lean_object* v_snd_2143_; lean_object* v___x_2144_; 
v_a_2141_ = lean_ctor_get(v___x_2140_, 0);
lean_inc(v_a_2141_);
lean_dec_ref_known(v___x_2140_, 1);
v_fst_2142_ = lean_ctor_get(v_a_2141_, 0);
lean_inc(v_fst_2142_);
v_snd_2143_ = lean_ctor_get(v_a_2141_, 1);
lean_inc(v_snd_2143_);
lean_dec(v_a_2141_);
lean_inc_ref(v_revertArgs_2069_);
v___x_2144_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__6(v_sz_2132_, v___x_2133_, v_revertArgs_2069_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_);
if (lean_obj_tag(v___x_2144_) == 0)
{
lean_object* v_a_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; 
v_a_2145_ = lean_ctor_get(v___x_2144_, 0);
lean_inc(v_a_2145_);
lean_dec_ref_known(v___x_2144_, 1);
v___x_2146_ = lean_array_to_list(v_a_2145_);
v___x_2147_ = l_Lean_Meta_mkAndIntroN(v___x_2146_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_);
if (lean_obj_tag(v___x_2147_) == 0)
{
lean_object* v_a_2148_; lean_object* v___x_2149_; uint8_t v___x_2150_; 
v_a_2148_ = lean_ctor_get(v___x_2147_, 0);
lean_inc(v_a_2148_);
lean_dec_ref_known(v___x_2147_, 1);
v___x_2149_ = lean_array_get_size(v_a_2135_);
v___x_2150_ = lean_nat_dec_lt(v___x_2052_, v___x_2149_);
if (v___x_2150_ == 0)
{
lean_dec(v_a_2135_);
lean_inc_ref(v_00_u03c3s_2055_);
v___y_2071_ = v_snd_2143_;
v___y_2072_ = v___y_2128_;
v___y_2073_ = v___y_2127_;
v___y_2074_ = v_fst_2142_;
v___y_2075_ = v___y_2131_;
v___y_2076_ = v___y_2129_;
v___y_2077_ = v_a_2148_;
v___y_2078_ = v___y_2126_;
v___y_2079_ = v___y_2130_;
v___y_2080_ = v___y_2125_;
v___y_2081_ = v___y_2124_;
v___y_2082_ = v_00_u03c3s_2055_;
goto v___jp_2070_;
}
else
{
size_t v___x_2151_; lean_object* v___x_2152_; 
v___x_2151_ = lean_usize_of_nat(v___x_2149_);
lean_inc_ref(v_00_u03c3s_2055_);
lean_inc(v_u_2054_);
v___x_2152_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__7(v_u_2054_, v_a_2135_, v___x_2151_, v___x_2133_, v_00_u03c3s_2055_);
lean_dec(v_a_2135_);
v___y_2071_ = v_snd_2143_;
v___y_2072_ = v___y_2128_;
v___y_2073_ = v___y_2127_;
v___y_2074_ = v_fst_2142_;
v___y_2075_ = v___y_2131_;
v___y_2076_ = v___y_2129_;
v___y_2077_ = v_a_2148_;
v___y_2078_ = v___y_2126_;
v___y_2079_ = v___y_2130_;
v___y_2080_ = v___y_2125_;
v___y_2081_ = v___y_2124_;
v___y_2082_ = v___x_2152_;
goto v___jp_2070_;
}
}
else
{
lean_dec(v_snd_2143_);
lean_dec(v_fst_2142_);
lean_dec(v_a_2135_);
lean_dec_ref(v_revertArgs_2069_);
lean_dec_ref(v_a_2065_);
lean_dec_ref(v_f_2062_);
lean_del_object(v___x_2059_);
lean_dec_ref(v_target_2057_);
lean_dec_ref(v_hyps_2056_);
lean_dec_ref(v_00_u03c3s_2055_);
lean_dec(v_u_2054_);
lean_dec_ref(v_k_2042_);
lean_dec(v_n_2040_);
return v___x_2147_;
}
}
else
{
lean_object* v_a_2153_; lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2160_; 
lean_dec(v_snd_2143_);
lean_dec(v_fst_2142_);
lean_dec(v_a_2135_);
lean_dec_ref(v_revertArgs_2069_);
lean_dec_ref(v_a_2065_);
lean_dec_ref(v_f_2062_);
lean_del_object(v___x_2059_);
lean_dec_ref(v_target_2057_);
lean_dec_ref(v_hyps_2056_);
lean_dec_ref(v_00_u03c3s_2055_);
lean_dec(v_u_2054_);
lean_dec_ref(v_k_2042_);
lean_dec(v_n_2040_);
v_a_2153_ = lean_ctor_get(v___x_2144_, 0);
v_isSharedCheck_2160_ = !lean_is_exclusive(v___x_2144_);
if (v_isSharedCheck_2160_ == 0)
{
v___x_2155_ = v___x_2144_;
v_isShared_2156_ = v_isSharedCheck_2160_;
goto v_resetjp_2154_;
}
else
{
lean_inc(v_a_2153_);
lean_dec(v___x_2144_);
v___x_2155_ = lean_box(0);
v_isShared_2156_ = v_isSharedCheck_2160_;
goto v_resetjp_2154_;
}
v_resetjp_2154_:
{
lean_object* v___x_2158_; 
if (v_isShared_2156_ == 0)
{
v___x_2158_ = v___x_2155_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v_a_2153_);
v___x_2158_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
return v___x_2158_;
}
}
}
}
else
{
lean_object* v_a_2161_; lean_object* v___x_2163_; uint8_t v_isShared_2164_; uint8_t v_isSharedCheck_2168_; 
lean_dec(v_a_2135_);
lean_dec_ref(v_revertArgs_2069_);
lean_dec_ref(v_a_2065_);
lean_dec_ref(v_f_2062_);
lean_del_object(v___x_2059_);
lean_dec_ref(v_target_2057_);
lean_dec_ref(v_hyps_2056_);
lean_dec_ref(v_00_u03c3s_2055_);
lean_dec(v_u_2054_);
lean_dec_ref(v_k_2042_);
lean_dec(v_n_2040_);
v_a_2161_ = lean_ctor_get(v___x_2140_, 0);
v_isSharedCheck_2168_ = !lean_is_exclusive(v___x_2140_);
if (v_isSharedCheck_2168_ == 0)
{
v___x_2163_ = v___x_2140_;
v_isShared_2164_ = v_isSharedCheck_2168_;
goto v_resetjp_2162_;
}
else
{
lean_inc(v_a_2161_);
lean_dec(v___x_2140_);
v___x_2163_ = lean_box(0);
v_isShared_2164_ = v_isSharedCheck_2168_;
goto v_resetjp_2162_;
}
v_resetjp_2162_:
{
lean_object* v___x_2166_; 
if (v_isShared_2164_ == 0)
{
v___x_2166_ = v___x_2163_;
goto v_reusejp_2165_;
}
else
{
lean_object* v_reuseFailAlloc_2167_; 
v_reuseFailAlloc_2167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2167_, 0, v_a_2161_);
v___x_2166_ = v_reuseFailAlloc_2167_;
goto v_reusejp_2165_;
}
v_reusejp_2165_:
{
return v___x_2166_;
}
}
}
}
else
{
lean_object* v_a_2169_; lean_object* v___x_2171_; uint8_t v_isShared_2172_; uint8_t v_isSharedCheck_2176_; 
lean_dec(v_a_2135_);
lean_dec_ref(v___f_2122_);
lean_dec_ref(v_revertArgs_2069_);
lean_dec_ref(v_a_2065_);
lean_dec_ref(v_f_2062_);
lean_del_object(v___x_2059_);
lean_dec_ref(v_target_2057_);
lean_dec_ref(v_hyps_2056_);
lean_dec_ref(v_00_u03c3s_2055_);
lean_dec(v_u_2054_);
lean_dec_ref(v_k_2042_);
lean_dec(v_n_2040_);
v_a_2169_ = lean_ctor_get(v___x_2137_, 0);
v_isSharedCheck_2176_ = !lean_is_exclusive(v___x_2137_);
if (v_isSharedCheck_2176_ == 0)
{
v___x_2171_ = v___x_2137_;
v_isShared_2172_ = v_isSharedCheck_2176_;
goto v_resetjp_2170_;
}
else
{
lean_inc(v_a_2169_);
lean_dec(v___x_2137_);
v___x_2171_ = lean_box(0);
v_isShared_2172_ = v_isSharedCheck_2176_;
goto v_resetjp_2170_;
}
v_resetjp_2170_:
{
lean_object* v___x_2174_; 
if (v_isShared_2172_ == 0)
{
v___x_2174_ = v___x_2171_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2175_; 
v_reuseFailAlloc_2175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2175_, 0, v_a_2169_);
v___x_2174_ = v_reuseFailAlloc_2175_;
goto v_reusejp_2173_;
}
v_reusejp_2173_:
{
return v___x_2174_;
}
}
}
}
else
{
lean_object* v_a_2177_; lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2184_; 
lean_dec_ref(v___f_2122_);
lean_dec_ref(v_revertArgs_2069_);
lean_dec_ref(v_a_2065_);
lean_dec_ref(v_f_2062_);
lean_del_object(v___x_2059_);
lean_dec_ref(v_target_2057_);
lean_dec_ref(v_hyps_2056_);
lean_dec_ref(v_00_u03c3s_2055_);
lean_dec(v_u_2054_);
lean_dec_ref(v_k_2042_);
lean_dec(v_n_2040_);
v_a_2177_ = lean_ctor_get(v___x_2134_, 0);
v_isSharedCheck_2184_ = !lean_is_exclusive(v___x_2134_);
if (v_isSharedCheck_2184_ == 0)
{
v___x_2179_ = v___x_2134_;
v_isShared_2180_ = v_isSharedCheck_2184_;
goto v_resetjp_2178_;
}
else
{
lean_inc(v_a_2177_);
lean_dec(v___x_2134_);
v___x_2179_ = lean_box(0);
v_isShared_2180_ = v_isSharedCheck_2184_;
goto v_resetjp_2178_;
}
v_resetjp_2178_:
{
lean_object* v___x_2182_; 
if (v_isShared_2180_ == 0)
{
v___x_2182_ = v___x_2179_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2183_; 
v_reuseFailAlloc_2183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2183_, 0, v_a_2177_);
v___x_2182_ = v_reuseFailAlloc_2183_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
return v___x_2182_;
}
}
}
}
}
}
else
{
lean_object* v___x_2212_; 
lean_dec(v_hypName_2041_);
lean_dec(v_n_2040_);
lean_inc(v___y_2050_);
lean_inc_ref(v___y_2049_);
lean_inc(v___y_2048_);
lean_inc_ref(v___y_2047_);
lean_inc(v___y_2046_);
lean_inc_ref(v___y_2045_);
lean_inc(v___y_2044_);
lean_inc_ref(v___y_2043_);
v___x_2212_ = lean_apply_10(v_k_2042_, v_goal_2039_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_, lean_box(0));
return v___x_2212_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1___boxed(lean_object* v_goal_2213_, lean_object* v_n_2214_, lean_object* v_hypName_2215_, lean_object* v_k_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_){
_start:
{
lean_object* v_res_2226_; 
v_res_2226_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1(v_goal_2213_, v_n_2214_, v_hypName_2215_, v_k_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_);
lean_dec(v___y_2224_);
lean_dec_ref(v___y_2223_);
lean_dec(v___y_2222_);
lean_dec_ref(v___y_2221_);
lean_dec(v___y_2220_);
lean_dec_ref(v___y_2219_);
lean_dec(v___y_2218_);
lean_dec_ref(v___y_2217_);
return v_res_2226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__1(lean_object* v___x_2230_, lean_object* v_snd_2231_, lean_object* v___y_2232_, lean_object* v_fst_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_){
_start:
{
lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; 
v___x_2243_ = lean_st_mk_ref(v___x_2230_);
v___x_2244_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__1___closed__1));
v___x_2245_ = l_Lean_Core_mkFreshUserName(v___x_2244_, v___y_2240_, v___y_2241_);
if (lean_obj_tag(v___x_2245_) == 0)
{
lean_object* v_a_2246_; lean_object* v___f_2247_; lean_object* v___x_2248_; 
v_a_2246_ = lean_ctor_get(v___x_2245_, 0);
lean_inc(v_a_2246_);
lean_dec_ref_known(v___x_2245_, 1);
lean_inc(v___x_2243_);
v___f_2247_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__0___boxed), 11, 1);
lean_closure_set(v___f_2247_, 0, v___x_2243_);
v___x_2248_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1(v_snd_2231_, v___y_2232_, v_a_2246_, v___f_2247_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_);
if (lean_obj_tag(v___x_2248_) == 0)
{
lean_object* v_a_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; 
v_a_2249_ = lean_ctor_get(v___x_2248_, 0);
lean_inc(v_a_2249_);
lean_dec_ref_known(v___x_2248_, 1);
v___x_2250_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2___redArg(v_fst_2233_, v_a_2249_, v___y_2239_);
lean_dec_ref(v___x_2250_);
v___x_2251_ = lean_st_ref_get(v___x_2243_);
lean_dec(v___x_2243_);
v___x_2252_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2251_, v___y_2235_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_);
return v___x_2252_;
}
else
{
lean_object* v_a_2253_; lean_object* v___x_2255_; uint8_t v_isShared_2256_; uint8_t v_isSharedCheck_2260_; 
lean_dec(v___x_2243_);
lean_dec(v_fst_2233_);
v_a_2253_ = lean_ctor_get(v___x_2248_, 0);
v_isSharedCheck_2260_ = !lean_is_exclusive(v___x_2248_);
if (v_isSharedCheck_2260_ == 0)
{
v___x_2255_ = v___x_2248_;
v_isShared_2256_ = v_isSharedCheck_2260_;
goto v_resetjp_2254_;
}
else
{
lean_inc(v_a_2253_);
lean_dec(v___x_2248_);
v___x_2255_ = lean_box(0);
v_isShared_2256_ = v_isSharedCheck_2260_;
goto v_resetjp_2254_;
}
v_resetjp_2254_:
{
lean_object* v___x_2258_; 
if (v_isShared_2256_ == 0)
{
v___x_2258_ = v___x_2255_;
goto v_reusejp_2257_;
}
else
{
lean_object* v_reuseFailAlloc_2259_; 
v_reuseFailAlloc_2259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2259_, 0, v_a_2253_);
v___x_2258_ = v_reuseFailAlloc_2259_;
goto v_reusejp_2257_;
}
v_reusejp_2257_:
{
return v___x_2258_;
}
}
}
}
else
{
lean_object* v_a_2261_; lean_object* v___x_2263_; uint8_t v_isShared_2264_; uint8_t v_isSharedCheck_2268_; 
lean_dec(v___x_2243_);
lean_dec(v_fst_2233_);
lean_dec(v___y_2232_);
lean_dec_ref(v_snd_2231_);
v_a_2261_ = lean_ctor_get(v___x_2245_, 0);
v_isSharedCheck_2268_ = !lean_is_exclusive(v___x_2245_);
if (v_isSharedCheck_2268_ == 0)
{
v___x_2263_ = v___x_2245_;
v_isShared_2264_ = v_isSharedCheck_2268_;
goto v_resetjp_2262_;
}
else
{
lean_inc(v_a_2261_);
lean_dec(v___x_2245_);
v___x_2263_ = lean_box(0);
v_isShared_2264_ = v_isSharedCheck_2268_;
goto v_resetjp_2262_;
}
v_resetjp_2262_:
{
lean_object* v___x_2266_; 
if (v_isShared_2264_ == 0)
{
v___x_2266_ = v___x_2263_;
goto v_reusejp_2265_;
}
else
{
lean_object* v_reuseFailAlloc_2267_; 
v_reuseFailAlloc_2267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2267_, 0, v_a_2261_);
v___x_2266_ = v_reuseFailAlloc_2267_;
goto v_reusejp_2265_;
}
v_reusejp_2265_:
{
return v___x_2266_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__1___boxed(lean_object* v___x_2269_, lean_object* v_snd_2270_, lean_object* v___y_2271_, lean_object* v_fst_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_){
_start:
{
lean_object* v_res_2282_; 
v_res_2282_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__1(v___x_2269_, v_snd_2270_, v___y_2271_, v_fst_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_);
lean_dec(v___y_2280_);
lean_dec_ref(v___y_2279_);
lean_dec(v___y_2278_);
lean_dec_ref(v___y_2277_);
lean_dec(v___y_2276_);
lean_dec_ref(v___y_2275_);
lean_dec(v___y_2274_);
lean_dec_ref(v___y_2273_);
return v_res_2282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevert___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__4(lean_object* v_goal_2290_, lean_object* v_ref_2291_, lean_object* v_k_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_){
_start:
{
lean_object* v___x_2302_; 
lean_inc_ref(v_goal_2290_);
v___x_2302_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo(v_goal_2290_, v_ref_2291_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_);
if (lean_obj_tag(v___x_2302_) == 0)
{
lean_object* v_a_2303_; lean_object* v_focusHyp_2304_; lean_object* v_restHyps_2305_; lean_object* v_proof_2306_; lean_object* v___x_2307_; 
v_a_2303_ = lean_ctor_get(v___x_2302_, 0);
lean_inc(v_a_2303_);
lean_dec_ref_known(v___x_2302_, 1);
v_focusHyp_2304_ = lean_ctor_get(v_a_2303_, 0);
lean_inc_ref_n(v_focusHyp_2304_, 2);
v_restHyps_2305_ = lean_ctor_get(v_a_2303_, 1);
lean_inc_ref(v_restHyps_2305_);
v_proof_2306_ = lean_ctor_get(v_a_2303_, 2);
lean_inc_ref(v_proof_2306_);
lean_dec(v_a_2303_);
v___x_2307_ = l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(v_focusHyp_2304_);
if (lean_obj_tag(v___x_2307_) == 1)
{
lean_object* v_val_2308_; lean_object* v_u_2309_; lean_object* v_00_u03c3s_2310_; lean_object* v_hyps_2311_; lean_object* v_target_2312_; lean_object* v___x_2314_; uint8_t v_isShared_2315_; uint8_t v_isSharedCheck_2337_; 
v_val_2308_ = lean_ctor_get(v___x_2307_, 0);
lean_inc(v_val_2308_);
lean_dec_ref_known(v___x_2307_, 1);
v_u_2309_ = lean_ctor_get(v_goal_2290_, 0);
v_00_u03c3s_2310_ = lean_ctor_get(v_goal_2290_, 1);
v_hyps_2311_ = lean_ctor_get(v_goal_2290_, 2);
v_target_2312_ = lean_ctor_get(v_goal_2290_, 3);
v_isSharedCheck_2337_ = !lean_is_exclusive(v_goal_2290_);
if (v_isSharedCheck_2337_ == 0)
{
v___x_2314_ = v_goal_2290_;
v_isShared_2315_ = v_isSharedCheck_2337_;
goto v_resetjp_2313_;
}
else
{
lean_inc(v_target_2312_);
lean_inc(v_hyps_2311_);
lean_inc(v_00_u03c3s_2310_);
lean_inc(v_u_2309_);
lean_dec(v_goal_2290_);
v___x_2314_ = lean_box(0);
v_isShared_2315_ = v_isSharedCheck_2337_;
goto v_resetjp_2313_;
}
v_resetjp_2313_:
{
lean_object* v_p_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2323_; 
v_p_2316_ = lean_ctor_get(v_val_2308_, 2);
lean_inc_ref(v_p_2316_);
lean_dec(v_val_2308_);
v___x_2317_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__4));
v___x_2318_ = lean_box(0);
lean_inc(v_u_2309_);
v___x_2319_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2319_, 0, v_u_2309_);
lean_ctor_set(v___x_2319_, 1, v___x_2318_);
lean_inc_ref(v___x_2319_);
v___x_2320_ = l_Lean_mkConst(v___x_2317_, v___x_2319_);
lean_inc_ref(v_target_2312_);
lean_inc_ref_n(v_00_u03c3s_2310_, 2);
v___x_2321_ = l_Lean_mkApp3(v___x_2320_, v_00_u03c3s_2310_, v_p_2316_, v_target_2312_);
lean_inc_ref(v_restHyps_2305_);
if (v_isShared_2315_ == 0)
{
lean_ctor_set(v___x_2314_, 3, v___x_2321_);
lean_ctor_set(v___x_2314_, 2, v_restHyps_2305_);
v___x_2323_ = v___x_2314_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2336_; 
v_reuseFailAlloc_2336_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2336_, 0, v_u_2309_);
lean_ctor_set(v_reuseFailAlloc_2336_, 1, v_00_u03c3s_2310_);
lean_ctor_set(v_reuseFailAlloc_2336_, 2, v_restHyps_2305_);
lean_ctor_set(v_reuseFailAlloc_2336_, 3, v___x_2321_);
v___x_2323_ = v_reuseFailAlloc_2336_;
goto v_reusejp_2322_;
}
v_reusejp_2322_:
{
lean_object* v___x_2324_; 
lean_inc(v___y_2300_);
lean_inc_ref(v___y_2299_);
lean_inc(v___y_2298_);
lean_inc_ref(v___y_2297_);
lean_inc(v___y_2296_);
lean_inc_ref(v___y_2295_);
lean_inc(v___y_2294_);
lean_inc_ref(v___y_2293_);
v___x_2324_ = lean_apply_10(v_k_2292_, v___x_2323_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_, lean_box(0));
if (lean_obj_tag(v___x_2324_) == 0)
{
lean_object* v_a_2325_; lean_object* v___x_2327_; uint8_t v_isShared_2328_; uint8_t v_isSharedCheck_2335_; 
v_a_2325_ = lean_ctor_get(v___x_2324_, 0);
v_isSharedCheck_2335_ = !lean_is_exclusive(v___x_2324_);
if (v_isSharedCheck_2335_ == 0)
{
v___x_2327_ = v___x_2324_;
v_isShared_2328_ = v_isSharedCheck_2335_;
goto v_resetjp_2326_;
}
else
{
lean_inc(v_a_2325_);
lean_dec(v___x_2324_);
v___x_2327_ = lean_box(0);
v_isShared_2328_ = v_isSharedCheck_2335_;
goto v_resetjp_2326_;
}
v_resetjp_2326_:
{
lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v_prf_2331_; lean_object* v___x_2333_; 
v___x_2329_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__4___closed__0));
v___x_2330_ = l_Lean_mkConst(v___x_2329_, v___x_2319_);
v_prf_2331_ = l_Lean_mkApp7(v___x_2330_, v_00_u03c3s_2310_, v_hyps_2311_, v_restHyps_2305_, v_focusHyp_2304_, v_target_2312_, v_proof_2306_, v_a_2325_);
if (v_isShared_2328_ == 0)
{
lean_ctor_set(v___x_2327_, 0, v_prf_2331_);
v___x_2333_ = v___x_2327_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2334_; 
v_reuseFailAlloc_2334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2334_, 0, v_prf_2331_);
v___x_2333_ = v_reuseFailAlloc_2334_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
return v___x_2333_;
}
}
}
else
{
lean_dec_ref_known(v___x_2319_, 2);
lean_dec_ref(v_target_2312_);
lean_dec_ref(v_hyps_2311_);
lean_dec_ref(v_00_u03c3s_2310_);
lean_dec_ref(v_proof_2306_);
lean_dec_ref(v_restHyps_2305_);
lean_dec_ref(v_focusHyp_2304_);
return v___x_2324_;
}
}
}
}
else
{
lean_object* v___x_2338_; lean_object* v___x_2339_; 
lean_dec(v___x_2307_);
lean_dec_ref(v_proof_2306_);
lean_dec_ref(v_restHyps_2305_);
lean_dec_ref(v_focusHyp_2304_);
lean_dec_ref(v_k_2292_);
lean_dec_ref(v_goal_2290_);
v___x_2338_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__6, &l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__6_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__6);
v___x_2339_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__8___redArg(v___x_2338_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_);
return v___x_2339_;
}
}
else
{
lean_object* v_a_2340_; lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2347_; 
lean_dec_ref(v_k_2292_);
lean_dec_ref(v_goal_2290_);
v_a_2340_ = lean_ctor_get(v___x_2302_, 0);
v_isSharedCheck_2347_ = !lean_is_exclusive(v___x_2302_);
if (v_isSharedCheck_2347_ == 0)
{
v___x_2342_ = v___x_2302_;
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
else
{
lean_inc(v_a_2340_);
lean_dec(v___x_2302_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
lean_object* v___x_2345_; 
if (v_isShared_2343_ == 0)
{
v___x_2345_ = v___x_2342_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v_a_2340_);
v___x_2345_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
return v___x_2345_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRevert___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__4___boxed(lean_object* v_goal_2348_, lean_object* v_ref_2349_, lean_object* v_k_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_){
_start:
{
lean_object* v_res_2360_; 
v_res_2360_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevert___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__4(v_goal_2348_, v_ref_2349_, v_k_2350_, v___y_2351_, v___y_2352_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_);
lean_dec(v___y_2358_);
lean_dec_ref(v___y_2357_);
lean_dec(v___y_2356_);
lean_dec_ref(v___y_2355_);
lean_dec(v___y_2354_);
lean_dec_ref(v___y_2353_);
lean_dec(v___y_2352_);
lean_dec_ref(v___y_2351_);
return v_res_2360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__3(lean_object* v___x_2361_, lean_object* v_val_2362_, lean_object* v_h_2363_, lean_object* v_a_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_){
_start:
{
lean_object* v___x_2374_; lean_object* v___f_2375_; lean_object* v___x_2376_; 
v___x_2374_ = lean_st_mk_ref(v___x_2361_);
lean_inc(v___x_2374_);
v___f_2375_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__0___boxed), 11, 1);
lean_closure_set(v___f_2375_, 0, v___x_2374_);
v___x_2376_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevert___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__4(v_val_2362_, v_h_2363_, v___f_2375_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_);
if (lean_obj_tag(v___x_2376_) == 0)
{
lean_object* v_a_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; 
v_a_2377_ = lean_ctor_get(v___x_2376_, 0);
lean_inc(v_a_2377_);
lean_dec_ref_known(v___x_2376_, 1);
v___x_2378_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2___redArg(v_a_2364_, v_a_2377_, v___y_2370_);
lean_dec_ref(v___x_2378_);
v___x_2379_ = lean_st_ref_get(v___x_2374_);
lean_dec(v___x_2374_);
v___x_2380_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2379_, v___y_2366_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_);
return v___x_2380_;
}
else
{
lean_object* v_a_2381_; lean_object* v___x_2383_; uint8_t v_isShared_2384_; uint8_t v_isSharedCheck_2388_; 
lean_dec(v___x_2374_);
lean_dec(v_a_2364_);
v_a_2381_ = lean_ctor_get(v___x_2376_, 0);
v_isSharedCheck_2388_ = !lean_is_exclusive(v___x_2376_);
if (v_isSharedCheck_2388_ == 0)
{
v___x_2383_ = v___x_2376_;
v_isShared_2384_ = v_isSharedCheck_2388_;
goto v_resetjp_2382_;
}
else
{
lean_inc(v_a_2381_);
lean_dec(v___x_2376_);
v___x_2383_ = lean_box(0);
v_isShared_2384_ = v_isSharedCheck_2388_;
goto v_resetjp_2382_;
}
v_resetjp_2382_:
{
lean_object* v___x_2386_; 
if (v_isShared_2384_ == 0)
{
v___x_2386_ = v___x_2383_;
goto v_reusejp_2385_;
}
else
{
lean_object* v_reuseFailAlloc_2387_; 
v_reuseFailAlloc_2387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2387_, 0, v_a_2381_);
v___x_2386_ = v_reuseFailAlloc_2387_;
goto v_reusejp_2385_;
}
v_reusejp_2385_:
{
return v___x_2386_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__3___boxed(lean_object* v___x_2389_, lean_object* v_val_2390_, lean_object* v_h_2391_, lean_object* v_a_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_){
_start:
{
lean_object* v_res_2402_; 
v_res_2402_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__3(v___x_2389_, v_val_2390_, v_h_2391_, v_a_2392_, v___y_2393_, v___y_2394_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_);
lean_dec(v___y_2400_);
lean_dec_ref(v___y_2399_);
lean_dec(v___y_2398_);
lean_dec_ref(v___y_2397_);
lean_dec(v___y_2396_);
lean_dec_ref(v___y_2395_);
lean_dec(v___y_2394_);
lean_dec_ref(v___y_2393_);
return v_res_2402_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5___redArg(lean_object* v_msg_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_){
_start:
{
lean_object* v_ref_2409_; lean_object* v___x_2410_; lean_object* v_a_2411_; lean_object* v___x_2413_; uint8_t v_isShared_2414_; uint8_t v_isSharedCheck_2419_; 
v_ref_2409_ = lean_ctor_get(v___y_2406_, 5);
v___x_2410_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5_spec__14(v_msg_2403_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_);
v_a_2411_ = lean_ctor_get(v___x_2410_, 0);
v_isSharedCheck_2419_ = !lean_is_exclusive(v___x_2410_);
if (v_isSharedCheck_2419_ == 0)
{
v___x_2413_ = v___x_2410_;
v_isShared_2414_ = v_isSharedCheck_2419_;
goto v_resetjp_2412_;
}
else
{
lean_inc(v_a_2411_);
lean_dec(v___x_2410_);
v___x_2413_ = lean_box(0);
v_isShared_2414_ = v_isSharedCheck_2419_;
goto v_resetjp_2412_;
}
v_resetjp_2412_:
{
lean_object* v___x_2415_; lean_object* v___x_2417_; 
lean_inc(v_ref_2409_);
v___x_2415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2415_, 0, v_ref_2409_);
lean_ctor_set(v___x_2415_, 1, v_a_2411_);
if (v_isShared_2414_ == 0)
{
lean_ctor_set_tag(v___x_2413_, 1);
lean_ctor_set(v___x_2413_, 0, v___x_2415_);
v___x_2417_ = v___x_2413_;
goto v_reusejp_2416_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v___x_2415_);
v___x_2417_ = v_reuseFailAlloc_2418_;
goto v_reusejp_2416_;
}
v_reusejp_2416_:
{
return v___x_2417_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5___redArg___boxed(lean_object* v_msg_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_){
_start:
{
lean_object* v_res_2426_; 
v_res_2426_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5___redArg(v_msg_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_);
lean_dec(v___y_2424_);
lean_dec_ref(v___y_2423_);
lean_dec(v___y_2422_);
lean_dec_ref(v___y_2421_);
return v_res_2426_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__11(void){
_start:
{
lean_object* v___x_2451_; lean_object* v___x_2452_; 
v___x_2451_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__10));
v___x_2452_ = l_Lean_stringToMessageData(v___x_2451_);
return v___x_2452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert(lean_object* v_x_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_, lean_object* v_a_2458_, lean_object* v_a_2459_, lean_object* v_a_2460_, lean_object* v_a_2461_){
_start:
{
lean_object* v___y_2464_; lean_object* v___y_2465_; lean_object* v___y_2466_; lean_object* v___y_2467_; lean_object* v___y_2468_; lean_object* v___y_2469_; lean_object* v___y_2470_; lean_object* v___y_2471_; lean_object* v___y_2472_; lean_object* v___y_2473_; lean_object* v___y_2474_; lean_object* v___x_2478_; uint8_t v___x_2479_; 
v___x_2478_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__3));
lean_inc(v_x_2453_);
v___x_2479_ = l_Lean_Syntax_isOfKind(v_x_2453_, v___x_2478_);
if (v___x_2479_ == 0)
{
lean_object* v___x_2480_; 
lean_dec(v_x_2453_);
v___x_2480_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg();
return v___x_2480_;
}
else
{
lean_object* v___x_2481_; lean_object* v_n_2483_; lean_object* v___y_2484_; lean_object* v___y_2485_; lean_object* v___y_2486_; lean_object* v___y_2487_; lean_object* v___y_2488_; lean_object* v___y_2489_; lean_object* v___y_2490_; lean_object* v___y_2491_; lean_object* v___x_2508_; uint8_t v___x_2509_; 
v___x_2481_ = lean_unsigned_to_nat(1u);
v___x_2508_ = l_Lean_Syntax_getArg(v_x_2453_, v___x_2481_);
lean_dec(v_x_2453_);
lean_inc(v___x_2508_);
v___x_2509_ = l_Lean_Syntax_matchesNull(v___x_2508_, v___x_2481_);
if (v___x_2509_ == 0)
{
lean_object* v___x_2510_; 
lean_dec(v___x_2508_);
v___x_2510_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg();
return v___x_2510_;
}
else
{
lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; uint8_t v___x_2514_; 
v___x_2511_ = lean_unsigned_to_nat(0u);
v___x_2512_ = l_Lean_Syntax_getArg(v___x_2508_, v___x_2511_);
lean_dec(v___x_2508_);
v___x_2513_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__5));
lean_inc(v___x_2512_);
v___x_2514_ = l_Lean_Syntax_isOfKind(v___x_2512_, v___x_2513_);
if (v___x_2514_ == 0)
{
lean_object* v___x_2515_; uint8_t v___x_2516_; 
v___x_2515_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__7));
lean_inc(v___x_2512_);
v___x_2516_ = l_Lean_Syntax_isOfKind(v___x_2512_, v___x_2515_);
if (v___x_2516_ == 0)
{
lean_object* v___x_2517_; 
lean_dec(v___x_2512_);
v___x_2517_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg();
return v___x_2517_;
}
else
{
lean_object* v___x_2518_; uint8_t v___x_2519_; 
v___x_2518_ = l_Lean_Syntax_getArg(v___x_2512_, v___x_2481_);
lean_dec(v___x_2512_);
v___x_2519_ = l_Lean_Syntax_isNone(v___x_2518_);
if (v___x_2519_ == 0)
{
uint8_t v___x_2520_; 
lean_inc(v___x_2518_);
v___x_2520_ = l_Lean_Syntax_matchesNull(v___x_2518_, v___x_2481_);
if (v___x_2520_ == 0)
{
lean_object* v___x_2521_; 
lean_dec(v___x_2518_);
v___x_2521_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg();
return v___x_2521_;
}
else
{
lean_object* v_n_2522_; lean_object* v___x_2523_; 
v_n_2522_ = l_Lean_Syntax_getArg(v___x_2518_, v___x_2511_);
lean_dec(v___x_2518_);
v___x_2523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2523_, 0, v_n_2522_);
v_n_2483_ = v___x_2523_;
v___y_2484_ = v_a_2454_;
v___y_2485_ = v_a_2455_;
v___y_2486_ = v_a_2456_;
v___y_2487_ = v_a_2457_;
v___y_2488_ = v_a_2458_;
v___y_2489_ = v_a_2459_;
v___y_2490_ = v_a_2460_;
v___y_2491_ = v_a_2461_;
goto v___jp_2482_;
}
}
else
{
lean_object* v___x_2524_; 
lean_dec(v___x_2518_);
v___x_2524_ = lean_box(0);
v_n_2483_ = v___x_2524_;
v___y_2484_ = v_a_2454_;
v___y_2485_ = v_a_2455_;
v___y_2486_ = v_a_2456_;
v___y_2487_ = v_a_2457_;
v___y_2488_ = v_a_2458_;
v___y_2489_ = v_a_2459_;
v___y_2490_ = v_a_2460_;
v___y_2491_ = v_a_2461_;
goto v___jp_2482_;
}
}
}
else
{
lean_object* v_h_2525_; lean_object* v___x_2526_; uint8_t v___x_2527_; 
v_h_2525_ = l_Lean_Syntax_getArg(v___x_2512_, v___x_2511_);
lean_dec(v___x_2512_);
v___x_2526_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__9));
lean_inc(v_h_2525_);
v___x_2527_ = l_Lean_Syntax_isOfKind(v_h_2525_, v___x_2526_);
if (v___x_2527_ == 0)
{
lean_object* v___x_2528_; 
lean_dec(v_h_2525_);
v___x_2528_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg();
return v___x_2528_;
}
else
{
lean_object* v___x_2529_; 
v___x_2529_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_2455_, v_a_2458_, v_a_2459_, v_a_2460_, v_a_2461_);
if (lean_obj_tag(v___x_2529_) == 0)
{
lean_object* v_a_2530_; lean_object* v___x_2531_; 
v_a_2530_ = lean_ctor_get(v___x_2529_, 0);
lean_inc_n(v_a_2530_, 2);
lean_dec_ref_known(v___x_2529_, 1);
v___x_2531_ = l_Lean_MVarId_getType(v_a_2530_, v_a_2458_, v_a_2459_, v_a_2460_, v_a_2461_);
if (lean_obj_tag(v___x_2531_) == 0)
{
lean_object* v_a_2532_; lean_object* v___x_2533_; 
v_a_2532_ = lean_ctor_get(v___x_2531_, 0);
lean_inc(v_a_2532_);
lean_dec_ref_known(v___x_2531_, 1);
v___x_2533_ = l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f(v_a_2532_);
lean_dec(v_a_2532_);
if (lean_obj_tag(v___x_2533_) == 1)
{
lean_object* v_val_2534_; lean_object* v___x_2535_; lean_object* v___f_2536_; lean_object* v___x_2537_; 
v_val_2534_ = lean_ctor_get(v___x_2533_, 0);
lean_inc(v_val_2534_);
lean_dec_ref_known(v___x_2533_, 1);
v___x_2535_ = lean_box(0);
lean_inc(v_a_2530_);
v___f_2536_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__3___boxed), 13, 4);
lean_closure_set(v___f_2536_, 0, v___x_2535_);
lean_closure_set(v___f_2536_, 1, v_val_2534_);
lean_closure_set(v___f_2536_, 2, v_h_2525_);
lean_closure_set(v___f_2536_, 3, v_a_2530_);
v___x_2537_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___redArg(v_a_2530_, v___f_2536_, v_a_2454_, v_a_2455_, v_a_2456_, v_a_2457_, v_a_2458_, v_a_2459_, v_a_2460_, v_a_2461_);
return v___x_2537_;
}
else
{
lean_object* v___x_2538_; lean_object* v___x_2539_; 
lean_dec(v___x_2533_);
lean_dec(v_a_2530_);
lean_dec(v_h_2525_);
v___x_2538_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__11, &l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__11_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__11);
v___x_2539_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5___redArg(v___x_2538_, v_a_2458_, v_a_2459_, v_a_2460_, v_a_2461_);
return v___x_2539_;
}
}
else
{
lean_object* v_a_2540_; lean_object* v___x_2542_; uint8_t v_isShared_2543_; uint8_t v_isSharedCheck_2547_; 
lean_dec(v_a_2530_);
lean_dec(v_h_2525_);
v_a_2540_ = lean_ctor_get(v___x_2531_, 0);
v_isSharedCheck_2547_ = !lean_is_exclusive(v___x_2531_);
if (v_isSharedCheck_2547_ == 0)
{
v___x_2542_ = v___x_2531_;
v_isShared_2543_ = v_isSharedCheck_2547_;
goto v_resetjp_2541_;
}
else
{
lean_inc(v_a_2540_);
lean_dec(v___x_2531_);
v___x_2542_ = lean_box(0);
v_isShared_2543_ = v_isSharedCheck_2547_;
goto v_resetjp_2541_;
}
v_resetjp_2541_:
{
lean_object* v___x_2545_; 
if (v_isShared_2543_ == 0)
{
v___x_2545_ = v___x_2542_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2546_; 
v_reuseFailAlloc_2546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2546_, 0, v_a_2540_);
v___x_2545_ = v_reuseFailAlloc_2546_;
goto v_reusejp_2544_;
}
v_reusejp_2544_:
{
return v___x_2545_;
}
}
}
}
else
{
lean_object* v_a_2548_; lean_object* v___x_2550_; uint8_t v_isShared_2551_; uint8_t v_isSharedCheck_2555_; 
lean_dec(v_h_2525_);
v_a_2548_ = lean_ctor_get(v___x_2529_, 0);
v_isSharedCheck_2555_ = !lean_is_exclusive(v___x_2529_);
if (v_isSharedCheck_2555_ == 0)
{
v___x_2550_ = v___x_2529_;
v_isShared_2551_ = v_isSharedCheck_2555_;
goto v_resetjp_2549_;
}
else
{
lean_inc(v_a_2548_);
lean_dec(v___x_2529_);
v___x_2550_ = lean_box(0);
v_isShared_2551_ = v_isSharedCheck_2555_;
goto v_resetjp_2549_;
}
v_resetjp_2549_:
{
lean_object* v___x_2553_; 
if (v_isShared_2551_ == 0)
{
v___x_2553_ = v___x_2550_;
goto v_reusejp_2552_;
}
else
{
lean_object* v_reuseFailAlloc_2554_; 
v_reuseFailAlloc_2554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2554_, 0, v_a_2548_);
v___x_2553_ = v_reuseFailAlloc_2554_;
goto v_reusejp_2552_;
}
v_reusejp_2552_:
{
return v___x_2553_;
}
}
}
}
}
}
v___jp_2482_:
{
lean_object* v___x_2492_; 
v___x_2492_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg(v___y_2485_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_);
if (lean_obj_tag(v___x_2492_) == 0)
{
lean_object* v_a_2493_; 
v_a_2493_ = lean_ctor_get(v___x_2492_, 0);
lean_inc(v_a_2493_);
lean_dec_ref_known(v___x_2492_, 1);
if (lean_obj_tag(v_n_2483_) == 0)
{
lean_object* v_fst_2494_; lean_object* v_snd_2495_; 
v_fst_2494_ = lean_ctor_get(v_a_2493_, 0);
lean_inc(v_fst_2494_);
v_snd_2495_ = lean_ctor_get(v_a_2493_, 1);
lean_inc(v_snd_2495_);
lean_dec(v_a_2493_);
v___y_2464_ = v_snd_2495_;
v___y_2465_ = v_fst_2494_;
v___y_2466_ = v___y_2490_;
v___y_2467_ = v___y_2487_;
v___y_2468_ = v___y_2489_;
v___y_2469_ = v___y_2486_;
v___y_2470_ = v___y_2485_;
v___y_2471_ = v___y_2491_;
v___y_2472_ = v___y_2488_;
v___y_2473_ = v___y_2484_;
v___y_2474_ = v___x_2481_;
goto v___jp_2463_;
}
else
{
lean_object* v_fst_2496_; lean_object* v_snd_2497_; lean_object* v_val_2498_; lean_object* v___x_2499_; 
v_fst_2496_ = lean_ctor_get(v_a_2493_, 0);
lean_inc(v_fst_2496_);
v_snd_2497_ = lean_ctor_get(v_a_2493_, 1);
lean_inc(v_snd_2497_);
lean_dec(v_a_2493_);
v_val_2498_ = lean_ctor_get(v_n_2483_, 0);
lean_inc(v_val_2498_);
lean_dec_ref_known(v_n_2483_, 1);
v___x_2499_ = l_Lean_TSyntax_getNat(v_val_2498_);
lean_dec(v_val_2498_);
v___y_2464_ = v_snd_2497_;
v___y_2465_ = v_fst_2496_;
v___y_2466_ = v___y_2490_;
v___y_2467_ = v___y_2487_;
v___y_2468_ = v___y_2489_;
v___y_2469_ = v___y_2486_;
v___y_2470_ = v___y_2485_;
v___y_2471_ = v___y_2491_;
v___y_2472_ = v___y_2488_;
v___y_2473_ = v___y_2484_;
v___y_2474_ = v___x_2499_;
goto v___jp_2463_;
}
}
else
{
lean_object* v_a_2500_; lean_object* v___x_2502_; uint8_t v_isShared_2503_; uint8_t v_isSharedCheck_2507_; 
lean_dec(v_n_2483_);
v_a_2500_ = lean_ctor_get(v___x_2492_, 0);
v_isSharedCheck_2507_ = !lean_is_exclusive(v___x_2492_);
if (v_isSharedCheck_2507_ == 0)
{
v___x_2502_ = v___x_2492_;
v_isShared_2503_ = v_isSharedCheck_2507_;
goto v_resetjp_2501_;
}
else
{
lean_inc(v_a_2500_);
lean_dec(v___x_2492_);
v___x_2502_ = lean_box(0);
v_isShared_2503_ = v_isSharedCheck_2507_;
goto v_resetjp_2501_;
}
v_resetjp_2501_:
{
lean_object* v___x_2505_; 
if (v_isShared_2503_ == 0)
{
v___x_2505_ = v___x_2502_;
goto v_reusejp_2504_;
}
else
{
lean_object* v_reuseFailAlloc_2506_; 
v_reuseFailAlloc_2506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2506_, 0, v_a_2500_);
v___x_2505_ = v_reuseFailAlloc_2506_;
goto v_reusejp_2504_;
}
v_reusejp_2504_:
{
return v___x_2505_;
}
}
}
}
}
v___jp_2463_:
{
lean_object* v___x_2475_; lean_object* v___f_2476_; lean_object* v___x_2477_; 
v___x_2475_ = lean_box(0);
lean_inc(v___y_2465_);
v___f_2476_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__1___boxed), 13, 4);
lean_closure_set(v___f_2476_, 0, v___x_2475_);
lean_closure_set(v___f_2476_, 1, v___y_2464_);
lean_closure_set(v___f_2476_, 2, v___y_2474_);
lean_closure_set(v___f_2476_, 3, v___y_2465_);
v___x_2477_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___redArg(v___y_2465_, v___f_2476_, v___y_2473_, v___y_2470_, v___y_2469_, v___y_2467_, v___y_2472_, v___y_2468_, v___y_2466_, v___y_2471_);
return v___x_2477_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___boxed(lean_object* v_x_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_, lean_object* v_a_2565_){
_start:
{
lean_object* v_res_2566_; 
v_res_2566_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert(v_x_2556_, v_a_2557_, v_a_2558_, v_a_2559_, v_a_2560_, v_a_2561_, v_a_2562_, v_a_2563_, v_a_2564_);
lean_dec(v_a_2564_);
lean_dec_ref(v_a_2563_);
lean_dec(v_a_2562_);
lean_dec_ref(v_a_2561_);
lean_dec(v_a_2560_);
lean_dec_ref(v_a_2559_);
lean_dec(v_a_2558_);
lean_dec_ref(v_a_2557_);
return v_res_2566_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2(lean_object* v_mvarId_2567_, lean_object* v_val_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_){
_start:
{
lean_object* v___x_2578_; 
v___x_2578_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2___redArg(v_mvarId_2567_, v_val_2568_, v___y_2574_);
return v___x_2578_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2___boxed(lean_object* v_mvarId_2579_, lean_object* v_val_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_){
_start:
{
lean_object* v_res_2590_; 
v_res_2590_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2(v_mvarId_2579_, v_val_2580_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_);
lean_dec(v___y_2588_);
lean_dec_ref(v___y_2587_);
lean_dec(v___y_2586_);
lean_dec_ref(v___y_2585_);
lean_dec(v___y_2584_);
lean_dec_ref(v___y_2583_);
lean_dec(v___y_2582_);
lean_dec_ref(v___y_2581_);
return v_res_2590_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5(lean_object* v_00_u03b1_2591_, lean_object* v_msg_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_){
_start:
{
lean_object* v___x_2602_; 
v___x_2602_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5___redArg(v_msg_2592_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_);
return v___x_2602_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5___boxed(lean_object* v_00_u03b1_2603_, lean_object* v_msg_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_){
_start:
{
lean_object* v_res_2614_; 
v_res_2614_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5(v_00_u03b1_2603_, v_msg_2604_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_);
lean_dec(v___y_2612_);
lean_dec_ref(v___y_2611_);
lean_dec(v___y_2610_);
lean_dec_ref(v___y_2609_);
lean_dec(v___y_2608_);
lean_dec_ref(v___y_2607_);
lean_dec(v___y_2606_);
lean_dec_ref(v___y_2605_);
return v_res_2614_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__1(lean_object* v_inst_2615_, lean_object* v_R_2616_, lean_object* v_a_2617_, lean_object* v_b_2618_){
_start:
{
lean_object* v___x_2619_; 
v___x_2619_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__1___redArg(v_a_2617_, v_b_2618_);
return v___x_2619_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__2(size_t v_sz_2620_, size_t v_i_2621_, lean_object* v_bs_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_){
_start:
{
lean_object* v___x_2632_; 
v___x_2632_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__2___redArg(v_sz_2620_, v_i_2621_, v_bs_2622_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_);
return v___x_2632_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__2___boxed(lean_object* v_sz_2633_, lean_object* v_i_2634_, lean_object* v_bs_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_){
_start:
{
size_t v_sz_boxed_2645_; size_t v_i_boxed_2646_; lean_object* v_res_2647_; 
v_sz_boxed_2645_ = lean_unbox_usize(v_sz_2633_);
lean_dec(v_sz_2633_);
v_i_boxed_2646_ = lean_unbox_usize(v_i_2634_);
lean_dec(v_i_2634_);
v_res_2647_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__2(v_sz_boxed_2645_, v_i_boxed_2646_, v_bs_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_);
lean_dec(v___y_2643_);
lean_dec_ref(v___y_2642_);
lean_dec(v___y_2641_);
lean_dec_ref(v___y_2640_);
lean_dec(v___y_2639_);
lean_dec_ref(v___y_2638_);
lean_dec(v___y_2637_);
lean_dec_ref(v___y_2636_);
return v_res_2647_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__4(lean_object* v_as_2648_, size_t v_sz_2649_, size_t v_i_2650_, lean_object* v_bs_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_){
_start:
{
lean_object* v___x_2661_; 
v___x_2661_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__4___redArg(v_sz_2649_, v_i_2650_, v_bs_2651_, v___y_2658_, v___y_2659_);
return v___x_2661_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__4___boxed(lean_object* v_as_2662_, lean_object* v_sz_2663_, lean_object* v_i_2664_, lean_object* v_bs_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_){
_start:
{
size_t v_sz_boxed_2675_; size_t v_i_boxed_2676_; lean_object* v_res_2677_; 
v_sz_boxed_2675_ = lean_unbox_usize(v_sz_2663_);
lean_dec(v_sz_2663_);
v_i_boxed_2676_ = lean_unbox_usize(v_i_2664_);
lean_dec(v_i_2664_);
v_res_2677_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__4(v_as_2662_, v_sz_boxed_2675_, v_i_boxed_2676_, v_bs_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_, v___y_2673_);
lean_dec(v___y_2673_);
lean_dec_ref(v___y_2672_);
lean_dec(v___y_2671_);
lean_dec_ref(v___y_2670_);
lean_dec(v___y_2669_);
lean_dec_ref(v___y_2668_);
lean_dec(v___y_2667_);
lean_dec_ref(v___y_2666_);
lean_dec_ref(v_as_2662_);
return v_res_2677_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__8(lean_object* v_00_u03b1_2678_, lean_object* v_msg_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_){
_start:
{
lean_object* v___x_2685_; 
v___x_2685_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__8___redArg(v_msg_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_);
return v___x_2685_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__8___boxed(lean_object* v_00_u03b1_2686_, lean_object* v_msg_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_){
_start:
{
lean_object* v_res_2693_; 
v_res_2693_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__8(v_00_u03b1_2686_, v_msg_2687_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_);
lean_dec(v___y_2691_);
lean_dec_ref(v___y_2690_);
lean_dec(v___y_2689_);
lean_dec_ref(v___y_2688_);
return v_res_2693_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10(lean_object* v_00_u03b2_2694_, lean_object* v_x_2695_, lean_object* v_x_2696_, lean_object* v_x_2697_){
_start:
{
lean_object* v___x_2698_; 
v___x_2698_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10___redArg(v_x_2695_, v_x_2696_, v_x_2697_);
return v___x_2698_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14(lean_object* v_00_u03b2_2699_, lean_object* v_x_2700_, size_t v_x_2701_, size_t v_x_2702_, lean_object* v_x_2703_, lean_object* v_x_2704_){
_start:
{
lean_object* v___x_2705_; 
v___x_2705_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14___redArg(v_x_2700_, v_x_2701_, v_x_2702_, v_x_2703_, v_x_2704_);
return v___x_2705_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14___boxed(lean_object* v_00_u03b2_2706_, lean_object* v_x_2707_, lean_object* v_x_2708_, lean_object* v_x_2709_, lean_object* v_x_2710_, lean_object* v_x_2711_){
_start:
{
size_t v_x_22744__boxed_2712_; size_t v_x_22745__boxed_2713_; lean_object* v_res_2714_; 
v_x_22744__boxed_2712_ = lean_unbox_usize(v_x_2708_);
lean_dec(v_x_2708_);
v_x_22745__boxed_2713_ = lean_unbox_usize(v_x_2709_);
lean_dec(v_x_2709_);
v_res_2714_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14(v_00_u03b2_2706_, v_x_2707_, v_x_22744__boxed_2712_, v_x_22745__boxed_2713_, v_x_2710_, v_x_2711_);
return v_res_2714_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14_spec__20(lean_object* v_00_u03b2_2715_, lean_object* v_n_2716_, lean_object* v_k_2717_, lean_object* v_v_2718_){
_start:
{
lean_object* v___x_2719_; 
v___x_2719_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14_spec__20___redArg(v_n_2716_, v_k_2717_, v_v_2718_);
return v___x_2719_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14_spec__21(lean_object* v_00_u03b2_2720_, size_t v_depth_2721_, lean_object* v_keys_2722_, lean_object* v_vals_2723_, lean_object* v_heq_2724_, lean_object* v_i_2725_, lean_object* v_entries_2726_){
_start:
{
lean_object* v___x_2727_; 
v___x_2727_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14_spec__21___redArg(v_depth_2721_, v_keys_2722_, v_vals_2723_, v_i_2725_, v_entries_2726_);
return v___x_2727_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14_spec__21___boxed(lean_object* v_00_u03b2_2728_, lean_object* v_depth_2729_, lean_object* v_keys_2730_, lean_object* v_vals_2731_, lean_object* v_heq_2732_, lean_object* v_i_2733_, lean_object* v_entries_2734_){
_start:
{
size_t v_depth_boxed_2735_; lean_object* v_res_2736_; 
v_depth_boxed_2735_ = lean_unbox_usize(v_depth_2729_);
lean_dec(v_depth_2729_);
v_res_2736_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14_spec__21(v_00_u03b2_2728_, v_depth_boxed_2735_, v_keys_2730_, v_vals_2731_, v_heq_2732_, v_i_2733_, v_entries_2734_);
lean_dec_ref(v_vals_2731_);
lean_dec_ref(v_keys_2730_);
return v_res_2736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19_spec__21(lean_object* v_00_u03b1_2737_, lean_object* v_name_2738_, uint8_t v_bi_2739_, lean_object* v_type_2740_, lean_object* v_k_2741_, uint8_t v_kind_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_){
_start:
{
lean_object* v___x_2752_; 
v___x_2752_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19_spec__21___redArg(v_name_2738_, v_bi_2739_, v_type_2740_, v_k_2741_, v_kind_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_);
return v___x_2752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19_spec__21___boxed(lean_object* v_00_u03b1_2753_, lean_object* v_name_2754_, lean_object* v_bi_2755_, lean_object* v_type_2756_, lean_object* v_k_2757_, lean_object* v_kind_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_){
_start:
{
uint8_t v_bi_boxed_2768_; uint8_t v_kind_boxed_2769_; lean_object* v_res_2770_; 
v_bi_boxed_2768_ = lean_unbox(v_bi_2755_);
v_kind_boxed_2769_ = lean_unbox(v_kind_2758_);
v_res_2770_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19_spec__21(v_00_u03b1_2753_, v_name_2754_, v_bi_boxed_2768_, v_type_2756_, v_k_2757_, v_kind_boxed_2769_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_, v___y_2765_, v___y_2766_);
lean_dec(v___y_2766_);
lean_dec_ref(v___y_2765_);
lean_dec(v___y_2764_);
lean_dec_ref(v___y_2763_);
lean_dec(v___y_2762_);
lean_dec_ref(v___y_2761_);
lean_dec(v___y_2760_);
lean_dec_ref(v___y_2759_);
return v_res_2770_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14_spec__20_spec__22(lean_object* v_00_u03b2_2771_, lean_object* v_x_2772_, lean_object* v_x_2773_, lean_object* v_x_2774_, lean_object* v_x_2775_){
_start:
{
lean_object* v___x_2776_; 
v___x_2776_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14_spec__20_spec__22___redArg(v_x_2772_, v_x_2773_, v_x_2774_, v_x_2775_);
return v___x_2776_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Revert_0__Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1(){
_start:
{
lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; 
v___x_2788_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2789_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__3));
v___x_2790_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Revert_0__Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__3));
v___x_2791_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___boxed), 10, 0);
v___x_2792_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2788_, v___x_2789_, v___x_2790_, v___x_2791_);
return v___x_2792_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Revert_0__Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___boxed(lean_object* v_a_2793_){
_start:
{
lean_object* v_res_2794_; 
v_res_2794_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Revert_0__Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1();
return v_res_2794_;
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
