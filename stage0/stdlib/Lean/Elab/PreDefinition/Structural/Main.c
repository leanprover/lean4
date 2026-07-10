// Lean compiler output
// Module: Lean.Elab.PreDefinition.Structural.Main
// Imports: public import Lean.Elab.PreDefinition.Mutual public import Lean.Elab.PreDefinition.Structural.FindRecArg public import Lean.Elab.PreDefinition.Structural.Preprocess public import Lean.Elab.PreDefinition.Structural.BRecOn public import Lean.Elab.PreDefinition.Structural.IndPred public import Lean.Elab.PreDefinition.Structural.Eqns public import Lean.Elab.PreDefinition.Structural.SmartUnfolding public import Lean.Meta.Tactic.TryThis
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
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Array_instInhabited(lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_FixedParamPerm_buildArgs___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_beta(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Elab_Structural_mkBRecOnMotive(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_FixedParamPerm_instantiateForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
uint8_t lean_bool_not(uint8_t);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
uint8_t l_Lean_Expr_isFVarOf(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_unlockAsync(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Elab_addAsAxiom___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_withEnv___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Lean_enableRealizationsForConst(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_local_ctx_erase(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_Elab_Structural_RecArgInfo_indicesAndRecArgPos(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
lean_object* l_Lean_Elab_FixedParamPerm_instantiateLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Structural_instInhabitedRecArgInfo_default;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isInductiveCore_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Meta_PProdN_mkLambdas___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_InductiveVal_numTypeFormers(lean_object*);
lean_object* l_Array_range(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
uint8_t l_Nat_blt(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInductivePredicate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_zip___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_mkBRecOnApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferArgumentTypesN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
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
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_Positions_numIndices(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_instInhabitedPreDefinition_default;
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_Elab_eraseRecAppSyntaxExpr(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_letToHave(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t l_Lean_getMaxHeight(lean_object*, lean_object*);
lean_object* l_Lean_addDecl(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_setDefHeightOverride(lean_object*, lean_object*, uint32_t);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_mkBRecOnF___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_mkIndPredBRecOnF___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_mkBRecOnConst(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_mkIndPredBRecOnMotive(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_withFunTypes___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Elab_addNonRec(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_findRecArgCandidates___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_Elab_FixedParamPerms_erase(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_tryCandidates___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_TerminationMeasure_delab(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_nil;
lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_addSmartUnfoldingDef(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_DefKind_isTheorem(uint8_t);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_abstractNestedProofs(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_registerEqnsInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_saveEqnAffectingOptions(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_eraseRecAppSyntax(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_preprocess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addAsAxiom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getFixedParamPerms___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addAndCompilePartialRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_applyAttributesOf(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Meta_mapErrorImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__24___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__24___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__24(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__0;
static lean_once_cell_t l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__1;
static lean_once_cell_t l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__2;
static lean_once_cell_t l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___lam__1___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + sizeof(size_t)*1, .m_other = 0, .m_tag = 0}, .m_objs = {(lean_object*)(size_t)(0ULL)}};
LEAN_EXPORT const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___boxed__const__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___boxed__const__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11_spec__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16_spec__29___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16_spec__29___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_f"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(253, 65, 185, 154, 193, 83, 240, 170)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg(lean_object*, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__15(lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__0;
static const lean_closure_object l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__1 = (const lean_object*)&l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__2 = (const lean_object*)&l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__3 = (const lean_object*)&l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__4 = (const lean_object*)&l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__4_value;
static lean_once_cell_t l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__5;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__13(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "Lean.Elab.PreDefinition.Structural.Basic"};
static const lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__0_value;
static const lean_string_object l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Lean.Elab.Structural.Positions.mapMwith"};
static const lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__1_value;
static const lean_string_object l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "assertion violation: positions.size = ys.size\n  "};
static const lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__3;
static const lean_string_object l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "assertion violation: positions.numIndices = xs.size\n  "};
static const lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__4 = (const lean_object*)&l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__5;
static const lean_array_object l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__6 = (const lean_object*)&l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "_inhabitedExprDummy"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 247, 56, 151, 29, 116, 116, 243)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__2;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "packedFArgs: "};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__3 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__3_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__4;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "FArgs: "};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__5 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__5_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__6;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "FTypes: "};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__7 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__7_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__8;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "funTypes: "};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__9 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__9_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__10;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = ", motives: "};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__11 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__11_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__12;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__3(lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__0 = (const lean_object*)&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__0_value;
static lean_once_cell_t l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__1;
static const lean_string_object l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "` is not an inductive type"};
static const lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__2 = (const lean_object*)&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__2_value;
static lean_once_cell_t l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__3;
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__11(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__7___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__7___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__7(lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "Lean.Elab.Structural.Positions.groupAndSort"};
static const lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__0 = (const lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__0_value;
static const lean_string_object l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "assertion violation: Array.range xs.size == positions.flatten.qsort Nat.blt\n  "};
static const lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__1 = (const lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__2;
static const lean_array_object l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__3 = (const lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__20(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__0_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__1_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "structural"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__2 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__1_value),LEAN_SCALAR_PTR_LITERAL(127, 238, 145, 63, 173, 125, 183, 95)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__2_value),LEAN_SCALAR_PTR_LITERAL(117, 73, 239, 7, 229, 151, 237, 199)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__3 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__3_value;
static const lean_closure_object l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__3_value)} };
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__4 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__4_value;
static const lean_closure_object l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_PProdN_mkLambdas___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__5 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__5_value;
static const lean_closure_object l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__6 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__6_value;
static const lean_array_object l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__7 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__7_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "assignments of type formers of "};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__8 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__8_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__9;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " to functions: "};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__10 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__10_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__11;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16_spec__29(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16_spec__29___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__0 = (const lean_object*)&l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__0_value;
static lean_once_cell_t l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__1;
static lean_once_cell_t l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__12(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9_spec__11(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__11(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__14_spec__17_spec__21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__14_spec__17(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__14(lean_object*, lean_object*);
static const lean_string_object l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "#["};
static const lean_object* l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__0 = (const lean_object*)&l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__0_value;
static const lean_string_object l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__1 = (const lean_object*)&l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__1_value;
static const lean_ctor_object l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__1_value)}};
static const lean_object* l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__2 = (const lean_object*)&l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__2_value;
static const lean_ctor_object l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__2_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__3 = (const lean_object*)&l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__3_value;
static const lean_string_object l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__4 = (const lean_object*)&l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__4_value;
static lean_once_cell_t l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__5;
static lean_once_cell_t l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__6;
static const lean_ctor_object l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__0_value)}};
static const lean_object* l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__7 = (const lean_object*)&l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__7_value;
static const lean_ctor_object l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__4_value)}};
static const lean_object* l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__8 = (const lean_object*)&l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__8_value;
static const lean_string_object l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "#[]"};
static const lean_object* l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__9 = (const lean_object*)&l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__9_value;
static const lean_ctor_object l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__9_value)}};
static const lean_object* l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__10 = (const lean_object*)&l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__10_value;
LEAN_EXPORT lean_object* l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__11(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 61, .m_capacity = 61, .m_length = 60, .m_data = "its type is an inductive datatype and the datatype parameter"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "\ndepends on the function parameter"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__3;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 137, .m_capacity = 137, .m_length = 136, .m_data = "\nwhich cannot be fixed as it is an index or depends on an index, and indices cannot be fixed parameters when using structural recursion."};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__4_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__5;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__0;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "New recArgInfos "};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__2;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Reduced fixed params from "};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__3 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__3_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__4;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " to "};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__5 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__5_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__6;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = ", erasing "};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__7 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__7_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__8;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Trying argument set "};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__9 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__9_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__10;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__2(lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__15(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Structural_reportTermMeasure___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Structural_reportTermMeasure___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Structural_reportTermMeasure___closed__0 = (const lean_object*)&l_Lean_Elab_Structural_reportTermMeasure___closed__0_value;
static const lean_string_object l_Lean_Elab_Structural_reportTermMeasure___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Structural_reportTermMeasure___closed__1 = (const lean_object*)&l_Lean_Elab_Structural_reportTermMeasure___closed__1_value;
static const lean_string_object l_Lean_Elab_Structural_reportTermMeasure___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Structural_reportTermMeasure___closed__2 = (const lean_object*)&l_Lean_Elab_Structural_reportTermMeasure___closed__2_value;
static const lean_string_object l_Lean_Elab_Structural_reportTermMeasure___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Termination"};
static const lean_object* l_Lean_Elab_Structural_reportTermMeasure___closed__3 = (const lean_object*)&l_Lean_Elab_Structural_reportTermMeasure___closed__3_value;
static const lean_string_object l_Lean_Elab_Structural_reportTermMeasure___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "terminationBy"};
static const lean_object* l_Lean_Elab_Structural_reportTermMeasure___closed__4 = (const lean_object*)&l_Lean_Elab_Structural_reportTermMeasure___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Structural_reportTermMeasure___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Structural_reportTermMeasure___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Structural_reportTermMeasure___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Structural_reportTermMeasure___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Structural_reportTermMeasure___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Structural_reportTermMeasure___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Structural_reportTermMeasure___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Structural_reportTermMeasure___closed__3_value),LEAN_SCALAR_PTR_LITERAL(128, 225, 226, 49, 186, 161, 212, 105)}};
static const lean_ctor_object l_Lean_Elab_Structural_reportTermMeasure___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Structural_reportTermMeasure___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Structural_reportTermMeasure___closed__4_value),LEAN_SCALAR_PTR_LITERAL(20, 221, 175, 114, 26, 111, 13, 165)}};
static const lean_object* l_Lean_Elab_Structural_reportTermMeasure___closed__5 = (const lean_object*)&l_Lean_Elab_Structural_reportTermMeasure___closed__5_value;
static const lean_string_object l_Lean_Elab_Structural_reportTermMeasure___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Try this:"};
static const lean_object* l_Lean_Elab_Structural_reportTermMeasure___closed__6 = (const lean_object*)&l_Lean_Elab_Structural_reportTermMeasure___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 58, .m_capacity = 58, .m_length = 57, .m_data = "structural recursion failed, produced type incorrect term"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__1;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_structuralRecursion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_structuralRecursion___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___redArg___lam__0(lean_object* v_k_1_, lean_object* v_____r_2_){
_start:
{
lean_inc(v_k_1_);
return v_k_1_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___redArg___lam__0___boxed(lean_object* v_k_3_, lean_object* v_____r_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___redArg___lam__0(v_k_3_, v_____r_4_);
lean_dec(v_k_3_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___redArg___lam__1(lean_object* v_inst_6_, lean_object* v_inst_7_, lean_object* v_inst_8_, lean_object* v___x_9_, lean_object* v_____do__lift_10_){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_11_ = l_Lean_Environment_unlockAsync(v_____do__lift_10_);
v___x_12_ = l_Lean_withEnv___redArg(v_inst_6_, v_inst_7_, v_inst_8_, v___x_11_, v___x_9_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___redArg___lam__2(lean_object* v_inst_13_, lean_object* v_x_14_, lean_object* v___y_15_){
_start:
{
lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_16_ = lean_alloc_closure((void*)(l_Lean_Elab_addAsAxiom___boxed), 6, 1);
lean_closure_set(v___x_16_, 0, v___y_15_);
v___x_17_ = lean_apply_2(v_inst_13_, lean_box(0), v___x_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___redArg(lean_object* v_inst_18_, lean_object* v_inst_19_, lean_object* v_inst_20_, lean_object* v_inst_21_, lean_object* v_preDefs_22_, lean_object* v_k_23_){
_start:
{
lean_object* v_toApplicative_24_; lean_object* v_toBind_25_; lean_object* v___f_26_; lean_object* v___y_28_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; uint8_t v___x_36_; 
v_toApplicative_24_ = lean_ctor_get(v_inst_18_, 0);
v_toBind_25_ = lean_ctor_get(v_inst_18_, 1);
lean_inc(v_toBind_25_);
v___f_26_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_26_, 0, v_k_23_);
v___x_33_ = lean_unsigned_to_nat(0u);
v___x_34_ = lean_array_get_size(v_preDefs_22_);
v___x_35_ = lean_box(0);
v___x_36_ = lean_nat_dec_lt(v___x_33_, v___x_34_);
if (v___x_36_ == 0)
{
lean_object* v_toPure_37_; lean_object* v___x_38_; 
lean_dec_ref(v_preDefs_22_);
lean_dec(v_inst_19_);
v_toPure_37_ = lean_ctor_get(v_toApplicative_24_, 1);
lean_inc(v_toPure_37_);
v___x_38_ = lean_apply_2(v_toPure_37_, lean_box(0), v___x_35_);
v___y_28_ = v___x_38_;
goto v___jp_27_;
}
else
{
lean_object* v___f_39_; uint8_t v___x_40_; 
v___f_39_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___redArg___lam__2), 3, 1);
lean_closure_set(v___f_39_, 0, v_inst_19_);
v___x_40_ = lean_nat_dec_le(v___x_34_, v___x_34_);
if (v___x_40_ == 0)
{
if (v___x_36_ == 0)
{
lean_object* v_toPure_41_; lean_object* v___x_42_; 
lean_dec_ref(v___f_39_);
lean_dec_ref(v_preDefs_22_);
v_toPure_41_ = lean_ctor_get(v_toApplicative_24_, 1);
lean_inc(v_toPure_41_);
v___x_42_ = lean_apply_2(v_toPure_41_, lean_box(0), v___x_35_);
v___y_28_ = v___x_42_;
goto v___jp_27_;
}
else
{
size_t v___x_43_; size_t v___x_44_; lean_object* v___x_45_; 
v___x_43_ = ((size_t)0ULL);
v___x_44_ = lean_usize_of_nat(v___x_34_);
lean_inc_ref(v_inst_18_);
v___x_45_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_18_, v___f_39_, v_preDefs_22_, v___x_43_, v___x_44_, v___x_35_);
v___y_28_ = v___x_45_;
goto v___jp_27_;
}
}
else
{
size_t v___x_46_; size_t v___x_47_; lean_object* v___x_48_; 
v___x_46_ = ((size_t)0ULL);
v___x_47_ = lean_usize_of_nat(v___x_34_);
lean_inc_ref(v_inst_18_);
v___x_48_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_18_, v___f_39_, v_preDefs_22_, v___x_46_, v___x_47_, v___x_35_);
v___y_28_ = v___x_48_;
goto v___jp_27_;
}
}
v___jp_27_:
{
lean_object* v_getEnv_29_; lean_object* v___x_30_; lean_object* v___f_31_; lean_object* v___x_32_; 
v_getEnv_29_ = lean_ctor_get(v_inst_20_, 0);
lean_inc(v_getEnv_29_);
lean_inc(v_toBind_25_);
v___x_30_ = lean_apply_4(v_toBind_25_, lean_box(0), lean_box(0), v___y_28_, v___f_26_);
v___f_31_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___redArg___lam__1), 5, 4);
lean_closure_set(v___f_31_, 0, v_inst_18_);
lean_closure_set(v___f_31_, 1, v_inst_21_);
lean_closure_set(v___f_31_, 2, v_inst_20_);
lean_closure_set(v___f_31_, 3, v___x_30_);
v___x_32_ = lean_apply_4(v_toBind_25_, lean_box(0), lean_box(0), v_getEnv_29_, v___f_31_);
return v___x_32_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms(lean_object* v_n_49_, lean_object* v_00_u03b1_50_, lean_object* v_inst_51_, lean_object* v_inst_52_, lean_object* v_inst_53_, lean_object* v_inst_54_, lean_object* v_preDefs_55_, lean_object* v_k_56_){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___redArg(v_inst_51_, v_inst_52_, v_inst_53_, v_inst_54_, v_preDefs_55_, v_k_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg___lam__0(lean_object* v_k_58_, lean_object* v_b_59_, lean_object* v_c_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_){
_start:
{
lean_object* v___x_66_; 
lean_inc(v___y_64_);
lean_inc_ref(v___y_63_);
lean_inc(v___y_62_);
lean_inc_ref(v___y_61_);
v___x_66_ = lean_apply_7(v_k_58_, v_b_59_, v_c_60_, v___y_61_, v___y_62_, v___y_63_, v___y_64_, lean_box(0));
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg___lam__0___boxed(lean_object* v_k_67_, lean_object* v_b_68_, lean_object* v_c_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg___lam__0(v_k_67_, v_b_68_, v_c_69_, v___y_70_, v___y_71_, v___y_72_, v___y_73_);
lean_dec(v___y_73_);
lean_dec_ref(v___y_72_);
lean_dec(v___y_71_);
lean_dec_ref(v___y_70_);
return v_res_75_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg(lean_object* v_e_76_, lean_object* v_k_77_, uint8_t v_cleanupAnnotations_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_){
_start:
{
lean_object* v___f_84_; uint8_t v___x_85_; uint8_t v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v___f_84_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_84_, 0, v_k_77_);
v___x_85_ = 1;
v___x_86_ = 0;
v___x_87_ = lean_box(0);
v___x_88_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_76_, v___x_85_, v___x_86_, v___x_85_, v___x_86_, v___x_87_, v___f_84_, v_cleanupAnnotations_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_);
if (lean_obj_tag(v___x_88_) == 0)
{
lean_object* v_a_89_; lean_object* v___x_91_; uint8_t v_isShared_92_; uint8_t v_isSharedCheck_96_; 
v_a_89_ = lean_ctor_get(v___x_88_, 0);
v_isSharedCheck_96_ = !lean_is_exclusive(v___x_88_);
if (v_isSharedCheck_96_ == 0)
{
v___x_91_ = v___x_88_;
v_isShared_92_ = v_isSharedCheck_96_;
goto v_resetjp_90_;
}
else
{
lean_inc(v_a_89_);
lean_dec(v___x_88_);
v___x_91_ = lean_box(0);
v_isShared_92_ = v_isSharedCheck_96_;
goto v_resetjp_90_;
}
v_resetjp_90_:
{
lean_object* v___x_94_; 
if (v_isShared_92_ == 0)
{
v___x_94_ = v___x_91_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v_a_89_);
v___x_94_ = v_reuseFailAlloc_95_;
goto v_reusejp_93_;
}
v_reusejp_93_:
{
return v___x_94_;
}
}
}
else
{
lean_object* v_a_97_; lean_object* v___x_99_; uint8_t v_isShared_100_; uint8_t v_isSharedCheck_104_; 
v_a_97_ = lean_ctor_get(v___x_88_, 0);
v_isSharedCheck_104_ = !lean_is_exclusive(v___x_88_);
if (v_isSharedCheck_104_ == 0)
{
v___x_99_ = v___x_88_;
v_isShared_100_ = v_isSharedCheck_104_;
goto v_resetjp_98_;
}
else
{
lean_inc(v_a_97_);
lean_dec(v___x_88_);
v___x_99_ = lean_box(0);
v_isShared_100_ = v_isSharedCheck_104_;
goto v_resetjp_98_;
}
v_resetjp_98_:
{
lean_object* v___x_102_; 
if (v_isShared_100_ == 0)
{
v___x_102_ = v___x_99_;
goto v_reusejp_101_;
}
else
{
lean_object* v_reuseFailAlloc_103_; 
v_reuseFailAlloc_103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_103_, 0, v_a_97_);
v___x_102_ = v_reuseFailAlloc_103_;
goto v_reusejp_101_;
}
v_reusejp_101_:
{
return v___x_102_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg___boxed(lean_object* v_e_105_, lean_object* v_k_106_, lean_object* v_cleanupAnnotations_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_113_; lean_object* v_res_114_; 
v_cleanupAnnotations_boxed_113_ = lean_unbox(v_cleanupAnnotations_107_);
v_res_114_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg(v_e_105_, v_k_106_, v_cleanupAnnotations_boxed_113_, v___y_108_, v___y_109_, v___y_110_, v___y_111_);
lean_dec(v___y_111_);
lean_dec_ref(v___y_110_);
lean_dec(v___y_109_);
lean_dec_ref(v___y_108_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1(lean_object* v_00_u03b1_115_, lean_object* v_e_116_, lean_object* v_k_117_, uint8_t v_cleanupAnnotations_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_){
_start:
{
lean_object* v___x_124_; 
v___x_124_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg(v_e_116_, v_k_117_, v_cleanupAnnotations_118_, v___y_119_, v___y_120_, v___y_121_, v___y_122_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___boxed(lean_object* v_00_u03b1_125_, lean_object* v_e_126_, lean_object* v_k_127_, lean_object* v_cleanupAnnotations_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_134_; lean_object* v_res_135_; 
v_cleanupAnnotations_boxed_134_ = lean_unbox(v_cleanupAnnotations_128_);
v_res_135_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1(v_00_u03b1_125_, v_e_126_, v_k_127_, v_cleanupAnnotations_boxed_134_, v___y_129_, v___y_130_, v___y_131_, v___y_132_);
lean_dec(v___y_132_);
lean_dec_ref(v___y_131_);
lean_dec(v___y_130_);
lean_dec_ref(v___y_129_);
return v_res_135_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0(lean_object* v___x_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_){
_start:
{
lean_object* v_options_145_; uint8_t v_hasTrace_146_; 
v_options_145_ = lean_ctor_get(v___y_142_, 2);
v_hasTrace_146_ = lean_ctor_get_uint8(v_options_145_, sizeof(void*)*1);
if (v_hasTrace_146_ == 0)
{
lean_object* v___x_147_; lean_object* v___x_148_; 
lean_dec(v___x_139_);
v___x_147_ = lean_box(v_hasTrace_146_);
v___x_148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_148_, 0, v___x_147_);
return v___x_148_;
}
else
{
lean_object* v_inheritedTraceOptions_149_; lean_object* v___x_150_; lean_object* v___x_151_; uint8_t v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v_inheritedTraceOptions_149_ = lean_ctor_get(v___y_142_, 13);
v___x_150_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0___closed__1));
v___x_151_ = l_Lean_Name_append(v___x_150_, v___x_139_);
v___x_152_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_149_, v_options_145_, v___x_151_);
lean_dec(v___x_151_);
v___x_153_ = lean_box(v___x_152_);
v___x_154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_154_, 0, v___x_153_);
return v___x_154_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0___boxed(lean_object* v___x_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0(v___x_155_, v___y_156_, v___y_157_, v___y_158_, v___y_159_);
lean_dec(v___y_159_);
lean_dec_ref(v___y_158_);
lean_dec(v___y_157_);
lean_dec_ref(v___y_156_);
return v_res_161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1(lean_object* v_x_162_){
_start:
{
lean_object* v_indIdx_163_; 
v_indIdx_163_ = lean_ctor_get(v_x_162_, 5);
lean_inc(v_indIdx_163_);
return v_indIdx_163_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___boxed(lean_object* v_x_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1(v_x_164_);
lean_dec_ref(v_x_164_);
return v_res_165_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13(lean_object* v_as_166_, size_t v_i_167_, size_t v_stop_168_, lean_object* v_b_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_){
_start:
{
uint8_t v___x_175_; 
v___x_175_ = lean_usize_dec_eq(v_i_167_, v_stop_168_);
if (v___x_175_ == 0)
{
lean_object* v___x_21530__overap_176_; lean_object* v___x_177_; 
v___x_21530__overap_176_ = lean_array_uget_borrowed(v_as_166_, v_i_167_);
lean_inc(v___x_21530__overap_176_);
lean_inc(v___y_173_);
lean_inc_ref(v___y_172_);
lean_inc(v___y_171_);
lean_inc_ref(v___y_170_);
v___x_177_ = lean_apply_5(v___x_21530__overap_176_, v___y_170_, v___y_171_, v___y_172_, v___y_173_, lean_box(0));
if (lean_obj_tag(v___x_177_) == 0)
{
lean_object* v_a_178_; size_t v___x_179_; size_t v___x_180_; 
v_a_178_ = lean_ctor_get(v___x_177_, 0);
lean_inc(v_a_178_);
lean_dec_ref_known(v___x_177_, 1);
v___x_179_ = ((size_t)1ULL);
v___x_180_ = lean_usize_add(v_i_167_, v___x_179_);
v_i_167_ = v___x_180_;
v_b_169_ = v_a_178_;
goto _start;
}
else
{
return v___x_177_;
}
}
else
{
lean_object* v___x_182_; 
v___x_182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_182_, 0, v_b_169_);
return v___x_182_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13___boxed(lean_object* v_as_183_, lean_object* v_i_184_, lean_object* v_stop_185_, lean_object* v_b_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_){
_start:
{
size_t v_i_boxed_192_; size_t v_stop_boxed_193_; lean_object* v_res_194_; 
v_i_boxed_192_ = lean_unbox_usize(v_i_184_);
lean_dec(v_i_184_);
v_stop_boxed_193_ = lean_unbox_usize(v_stop_185_);
lean_dec(v_stop_185_);
v_res_194_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13(v_as_183_, v_i_boxed_192_, v_stop_boxed_193_, v_b_186_, v___y_187_, v___y_188_, v___y_189_, v___y_190_);
lean_dec(v___y_190_);
lean_dec_ref(v___y_189_);
lean_dec(v___y_188_);
lean_dec_ref(v___y_187_);
lean_dec_ref(v_as_183_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__24___redArg(lean_object* v_as_195_, size_t v_i_196_, size_t v_stop_197_, lean_object* v_b_198_, lean_object* v___y_199_, lean_object* v___y_200_){
_start:
{
uint8_t v___x_202_; 
v___x_202_ = lean_usize_dec_eq(v_i_196_, v_stop_197_);
if (v___x_202_ == 0)
{
lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_203_ = lean_array_uget_borrowed(v_as_195_, v_i_196_);
v___x_204_ = l_Lean_Elab_addAsAxiom___redArg(v___x_203_, v___y_199_, v___y_200_);
if (lean_obj_tag(v___x_204_) == 0)
{
lean_object* v_a_205_; size_t v___x_206_; size_t v___x_207_; 
v_a_205_ = lean_ctor_get(v___x_204_, 0);
lean_inc(v_a_205_);
lean_dec_ref_known(v___x_204_, 1);
v___x_206_ = ((size_t)1ULL);
v___x_207_ = lean_usize_add(v_i_196_, v___x_206_);
v_i_196_ = v___x_207_;
v_b_198_ = v_a_205_;
goto _start;
}
else
{
return v___x_204_;
}
}
else
{
lean_object* v___x_209_; 
v___x_209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_209_, 0, v_b_198_);
return v___x_209_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__24___redArg___boxed(lean_object* v_as_210_, lean_object* v_i_211_, lean_object* v_stop_212_, lean_object* v_b_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_){
_start:
{
size_t v_i_boxed_217_; size_t v_stop_boxed_218_; lean_object* v_res_219_; 
v_i_boxed_217_ = lean_unbox_usize(v_i_211_);
lean_dec(v_i_211_);
v_stop_boxed_218_ = lean_unbox_usize(v_stop_212_);
lean_dec(v_stop_212_);
v_res_219_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__24___redArg(v_as_210_, v_i_boxed_217_, v_stop_boxed_218_, v_b_213_, v___y_214_, v___y_215_);
lean_dec(v___y_215_);
lean_dec_ref(v___y_214_);
lean_dec_ref(v_as_210_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__24(lean_object* v_as_220_, size_t v_i_221_, size_t v_stop_222_, lean_object* v_b_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_){
_start:
{
lean_object* v___x_229_; 
v___x_229_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__24___redArg(v_as_220_, v_i_221_, v_stop_222_, v_b_223_, v___y_226_, v___y_227_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__24___boxed(lean_object* v_as_230_, lean_object* v_i_231_, lean_object* v_stop_232_, lean_object* v_b_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_){
_start:
{
size_t v_i_boxed_239_; size_t v_stop_boxed_240_; lean_object* v_res_241_; 
v_i_boxed_239_ = lean_unbox_usize(v_i_231_);
lean_dec(v_i_231_);
v_stop_boxed_240_ = lean_unbox_usize(v_stop_232_);
lean_dec(v_stop_232_);
v_res_241_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__24(v_as_230_, v_i_boxed_239_, v_stop_boxed_240_, v_b_233_, v___y_234_, v___y_235_, v___y_236_, v___y_237_);
lean_dec(v___y_237_);
lean_dec_ref(v___y_236_);
lean_dec(v___y_235_);
lean_dec_ref(v___y_234_);
lean_dec_ref(v_as_230_);
return v_res_241_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__0(void){
_start:
{
lean_object* v___x_242_; 
v___x_242_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_242_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__1(void){
_start:
{
lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_243_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__0, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__0);
v___x_244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_244_, 0, v___x_243_);
return v___x_244_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__2(void){
_start:
{
lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_245_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__1, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__1);
v___x_246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_246_, 0, v___x_245_);
lean_ctor_set(v___x_246_, 1, v___x_245_);
return v___x_246_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__3(void){
_start:
{
lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_247_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__1, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__1);
v___x_248_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_248_, 0, v___x_247_);
lean_ctor_set(v___x_248_, 1, v___x_247_);
lean_ctor_set(v___x_248_, 2, v___x_247_);
lean_ctor_set(v___x_248_, 3, v___x_247_);
lean_ctor_set(v___x_248_, 4, v___x_247_);
lean_ctor_set(v___x_248_, 5, v___x_247_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg(lean_object* v_env_249_, lean_object* v___y_250_, lean_object* v___y_251_){
_start:
{
lean_object* v___x_253_; lean_object* v_nextMacroScope_254_; lean_object* v_ngen_255_; lean_object* v_auxDeclNGen_256_; lean_object* v_traceState_257_; lean_object* v_messages_258_; lean_object* v_infoState_259_; lean_object* v_snapshotTasks_260_; lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_286_; 
v___x_253_ = lean_st_ref_take(v___y_251_);
v_nextMacroScope_254_ = lean_ctor_get(v___x_253_, 1);
v_ngen_255_ = lean_ctor_get(v___x_253_, 2);
v_auxDeclNGen_256_ = lean_ctor_get(v___x_253_, 3);
v_traceState_257_ = lean_ctor_get(v___x_253_, 4);
v_messages_258_ = lean_ctor_get(v___x_253_, 6);
v_infoState_259_ = lean_ctor_get(v___x_253_, 7);
v_snapshotTasks_260_ = lean_ctor_get(v___x_253_, 8);
v_isSharedCheck_286_ = !lean_is_exclusive(v___x_253_);
if (v_isSharedCheck_286_ == 0)
{
lean_object* v_unused_287_; lean_object* v_unused_288_; 
v_unused_287_ = lean_ctor_get(v___x_253_, 5);
lean_dec(v_unused_287_);
v_unused_288_ = lean_ctor_get(v___x_253_, 0);
lean_dec(v_unused_288_);
v___x_262_ = v___x_253_;
v_isShared_263_ = v_isSharedCheck_286_;
goto v_resetjp_261_;
}
else
{
lean_inc(v_snapshotTasks_260_);
lean_inc(v_infoState_259_);
lean_inc(v_messages_258_);
lean_inc(v_traceState_257_);
lean_inc(v_auxDeclNGen_256_);
lean_inc(v_ngen_255_);
lean_inc(v_nextMacroScope_254_);
lean_dec(v___x_253_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_286_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
lean_object* v___x_264_; lean_object* v___x_266_; 
v___x_264_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__2);
if (v_isShared_263_ == 0)
{
lean_ctor_set(v___x_262_, 5, v___x_264_);
lean_ctor_set(v___x_262_, 0, v_env_249_);
v___x_266_ = v___x_262_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v_env_249_);
lean_ctor_set(v_reuseFailAlloc_285_, 1, v_nextMacroScope_254_);
lean_ctor_set(v_reuseFailAlloc_285_, 2, v_ngen_255_);
lean_ctor_set(v_reuseFailAlloc_285_, 3, v_auxDeclNGen_256_);
lean_ctor_set(v_reuseFailAlloc_285_, 4, v_traceState_257_);
lean_ctor_set(v_reuseFailAlloc_285_, 5, v___x_264_);
lean_ctor_set(v_reuseFailAlloc_285_, 6, v_messages_258_);
lean_ctor_set(v_reuseFailAlloc_285_, 7, v_infoState_259_);
lean_ctor_set(v_reuseFailAlloc_285_, 8, v_snapshotTasks_260_);
v___x_266_ = v_reuseFailAlloc_285_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v_mctx_269_; lean_object* v_zetaDeltaFVarIds_270_; lean_object* v_postponed_271_; lean_object* v_diag_272_; lean_object* v___x_274_; uint8_t v_isShared_275_; uint8_t v_isSharedCheck_283_; 
v___x_267_ = lean_st_ref_set(v___y_251_, v___x_266_);
v___x_268_ = lean_st_ref_take(v___y_250_);
v_mctx_269_ = lean_ctor_get(v___x_268_, 0);
v_zetaDeltaFVarIds_270_ = lean_ctor_get(v___x_268_, 2);
v_postponed_271_ = lean_ctor_get(v___x_268_, 3);
v_diag_272_ = lean_ctor_get(v___x_268_, 4);
v_isSharedCheck_283_ = !lean_is_exclusive(v___x_268_);
if (v_isSharedCheck_283_ == 0)
{
lean_object* v_unused_284_; 
v_unused_284_ = lean_ctor_get(v___x_268_, 1);
lean_dec(v_unused_284_);
v___x_274_ = v___x_268_;
v_isShared_275_ = v_isSharedCheck_283_;
goto v_resetjp_273_;
}
else
{
lean_inc(v_diag_272_);
lean_inc(v_postponed_271_);
lean_inc(v_zetaDeltaFVarIds_270_);
lean_inc(v_mctx_269_);
lean_dec(v___x_268_);
v___x_274_ = lean_box(0);
v_isShared_275_ = v_isSharedCheck_283_;
goto v_resetjp_273_;
}
v_resetjp_273_:
{
lean_object* v___x_276_; lean_object* v___x_278_; 
v___x_276_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__3, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__3);
if (v_isShared_275_ == 0)
{
lean_ctor_set(v___x_274_, 1, v___x_276_);
v___x_278_ = v___x_274_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v_mctx_269_);
lean_ctor_set(v_reuseFailAlloc_282_, 1, v___x_276_);
lean_ctor_set(v_reuseFailAlloc_282_, 2, v_zetaDeltaFVarIds_270_);
lean_ctor_set(v_reuseFailAlloc_282_, 3, v_postponed_271_);
lean_ctor_set(v_reuseFailAlloc_282_, 4, v_diag_272_);
v___x_278_ = v_reuseFailAlloc_282_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_279_ = lean_st_ref_set(v___y_250_, v___x_278_);
v___x_280_ = lean_box(0);
v___x_281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_281_, 0, v___x_280_);
return v___x_281_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___boxed(lean_object* v_env_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg(v_env_289_, v___y_290_, v___y_291_);
lean_dec(v___y_291_);
lean_dec(v___y_290_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23___redArg(lean_object* v_env_294_, lean_object* v_x_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_){
_start:
{
lean_object* v___x_301_; lean_object* v_env_302_; lean_object* v_a_304_; lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_301_ = lean_st_ref_get(v___y_299_);
v_env_302_ = lean_ctor_get(v___x_301_, 0);
lean_inc_ref(v_env_302_);
lean_dec(v___x_301_);
v___x_314_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg(v_env_294_, v___y_297_, v___y_299_);
lean_dec_ref(v___x_314_);
lean_inc(v___y_299_);
lean_inc_ref(v___y_298_);
lean_inc(v___y_297_);
lean_inc_ref(v___y_296_);
v___x_315_ = lean_apply_5(v_x_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_, lean_box(0));
if (lean_obj_tag(v___x_315_) == 0)
{
lean_object* v_a_316_; lean_object* v___x_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_324_; 
v_a_316_ = lean_ctor_get(v___x_315_, 0);
lean_inc(v_a_316_);
lean_dec_ref_known(v___x_315_, 1);
v___x_317_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg(v_env_302_, v___y_297_, v___y_299_);
v_isSharedCheck_324_ = !lean_is_exclusive(v___x_317_);
if (v_isSharedCheck_324_ == 0)
{
lean_object* v_unused_325_; 
v_unused_325_ = lean_ctor_get(v___x_317_, 0);
lean_dec(v_unused_325_);
v___x_319_ = v___x_317_;
v_isShared_320_ = v_isSharedCheck_324_;
goto v_resetjp_318_;
}
else
{
lean_dec(v___x_317_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_324_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v___x_322_; 
if (v_isShared_320_ == 0)
{
lean_ctor_set(v___x_319_, 0, v_a_316_);
v___x_322_ = v___x_319_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v_a_316_);
v___x_322_ = v_reuseFailAlloc_323_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
return v___x_322_;
}
}
}
else
{
lean_object* v_a_326_; 
v_a_326_ = lean_ctor_get(v___x_315_, 0);
lean_inc(v_a_326_);
lean_dec_ref_known(v___x_315_, 1);
v_a_304_ = v_a_326_;
goto v___jp_303_;
}
v___jp_303_:
{
lean_object* v___x_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_312_; 
v___x_305_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg(v_env_302_, v___y_297_, v___y_299_);
v_isSharedCheck_312_ = !lean_is_exclusive(v___x_305_);
if (v_isSharedCheck_312_ == 0)
{
lean_object* v_unused_313_; 
v_unused_313_ = lean_ctor_get(v___x_305_, 0);
lean_dec(v_unused_313_);
v___x_307_ = v___x_305_;
v_isShared_308_ = v_isSharedCheck_312_;
goto v_resetjp_306_;
}
else
{
lean_dec(v___x_305_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_312_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v___x_310_; 
if (v_isShared_308_ == 0)
{
lean_ctor_set_tag(v___x_307_, 1);
lean_ctor_set(v___x_307_, 0, v_a_304_);
v___x_310_ = v___x_307_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v_a_304_);
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
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23___redArg___boxed(lean_object* v_env_327_, lean_object* v_x_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23___redArg(v_env_327_, v_x_328_, v___y_329_, v___y_330_, v___y_331_, v___y_332_);
lean_dec(v___y_332_);
lean_dec_ref(v___y_331_);
lean_dec(v___y_330_);
lean_dec_ref(v___y_329_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___lam__1(lean_object* v___x_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_){
_start:
{
lean_object* v___x_341_; 
v___x_341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_341_, 0, v___x_335_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___lam__1___boxed(lean_object* v___x_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___lam__1(v___x_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_);
lean_dec(v___y_346_);
lean_dec_ref(v___y_345_);
lean_dec(v___y_344_);
lean_dec_ref(v___y_343_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___lam__0(lean_object* v___y_349_, lean_object* v_k_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_){
_start:
{
lean_object* v___x_356_; 
lean_inc(v___y_354_);
lean_inc_ref(v___y_353_);
lean_inc(v___y_352_);
lean_inc_ref(v___y_351_);
v___x_356_ = lean_apply_5(v___y_349_, v___y_351_, v___y_352_, v___y_353_, v___y_354_, lean_box(0));
if (lean_obj_tag(v___x_356_) == 0)
{
lean_object* v___x_357_; 
lean_dec_ref_known(v___x_356_, 1);
v___x_357_ = lean_apply_5(v_k_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_, lean_box(0));
return v___x_357_;
}
else
{
lean_object* v_a_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_365_; 
lean_dec(v___y_354_);
lean_dec_ref(v___y_353_);
lean_dec(v___y_352_);
lean_dec_ref(v___y_351_);
lean_dec_ref(v_k_350_);
v_a_358_ = lean_ctor_get(v___x_356_, 0);
v_isSharedCheck_365_ = !lean_is_exclusive(v___x_356_);
if (v_isSharedCheck_365_ == 0)
{
v___x_360_ = v___x_356_;
v_isShared_361_ = v_isSharedCheck_365_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_a_358_);
lean_dec(v___x_356_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_365_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___x_363_; 
if (v_isShared_361_ == 0)
{
v___x_363_ = v___x_360_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v_a_358_);
v___x_363_ = v_reuseFailAlloc_364_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
return v___x_363_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___lam__0___boxed(lean_object* v___y_366_, lean_object* v_k_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___lam__0(v___y_366_, v_k_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(lean_object* v_preDefs_378_, lean_object* v_k_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_){
_start:
{
lean_object* v___y_386_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; uint8_t v___x_395_; 
v___x_392_ = lean_unsigned_to_nat(0u);
v___x_393_ = lean_array_get_size(v_preDefs_378_);
v___x_394_ = lean_box(0);
v___x_395_ = lean_nat_dec_lt(v___x_392_, v___x_393_);
if (v___x_395_ == 0)
{
lean_object* v___f_396_; 
lean_dec_ref(v_preDefs_378_);
v___f_396_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___closed__0));
v___y_386_ = v___f_396_;
goto v___jp_385_;
}
else
{
uint8_t v___x_397_; 
v___x_397_ = lean_nat_dec_le(v___x_393_, v___x_393_);
if (v___x_397_ == 0)
{
if (v___x_395_ == 0)
{
lean_object* v___f_398_; 
lean_dec_ref(v_preDefs_378_);
v___f_398_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___closed__0));
v___y_386_ = v___f_398_;
goto v___jp_385_;
}
else
{
size_t v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_399_ = lean_usize_of_nat(v___x_393_);
v___x_400_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___boxed__const__1));
v___x_401_ = lean_box_usize(v___x_399_);
v___x_402_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__24___boxed), 9, 4);
lean_closure_set(v___x_402_, 0, v_preDefs_378_);
lean_closure_set(v___x_402_, 1, v___x_400_);
lean_closure_set(v___x_402_, 2, v___x_401_);
lean_closure_set(v___x_402_, 3, v___x_394_);
v___y_386_ = v___x_402_;
goto v___jp_385_;
}
}
else
{
size_t v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_403_ = lean_usize_of_nat(v___x_393_);
v___x_404_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___boxed__const__1));
v___x_405_ = lean_box_usize(v___x_403_);
v___x_406_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__24___boxed), 9, 4);
lean_closure_set(v___x_406_, 0, v_preDefs_378_);
lean_closure_set(v___x_406_, 1, v___x_404_);
lean_closure_set(v___x_406_, 2, v___x_405_);
lean_closure_set(v___x_406_, 3, v___x_394_);
v___y_386_ = v___x_406_;
goto v___jp_385_;
}
}
v___jp_385_:
{
lean_object* v___x_387_; lean_object* v_env_388_; lean_object* v___f_389_; lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_387_ = lean_st_ref_get(v___y_383_);
v_env_388_ = lean_ctor_get(v___x_387_, 0);
lean_inc_ref(v_env_388_);
lean_dec(v___x_387_);
v___f_389_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_389_, 0, v___y_386_);
lean_closure_set(v___f_389_, 1, v_k_379_);
v___x_390_ = l_Lean_Environment_unlockAsync(v_env_388_);
v___x_391_ = l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23___redArg(v___x_390_, v___f_389_, v___y_380_, v___y_381_, v___y_382_, v___y_383_);
return v___x_391_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___boxed(lean_object* v_preDefs_407_, lean_object* v_k_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v_preDefs_407_, v_k_408_, v___y_409_, v___y_410_, v___y_411_, v___y_412_);
lean_dec(v___y_412_);
lean_dec_ref(v___y_411_);
lean_dec(v___y_410_);
lean_dec_ref(v___y_409_);
return v_res_414_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg___closed__0(void){
_start:
{
lean_object* v___x_415_; lean_object* v_dummy_416_; 
v___x_415_ = lean_box(0);
v_dummy_416_ = l_Lean_Expr_sort___override(v___x_415_);
return v_dummy_416_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg(uint8_t v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_recArgInfos_420_, lean_object* v___x_421_, lean_object* v_preDefs_422_, lean_object* v_a_423_, size_t v_sz_424_, size_t v_i_425_, lean_object* v_bs_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_){
_start:
{
uint8_t v___x_432_; 
v___x_432_ = lean_usize_dec_lt(v_i_425_, v_sz_424_);
if (v___x_432_ == 0)
{
lean_object* v___x_433_; 
lean_dec_ref(v_a_423_);
lean_dec_ref(v_preDefs_422_);
lean_dec_ref(v___x_421_);
lean_dec_ref(v_recArgInfos_420_);
v___x_433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_433_, 0, v_bs_426_);
return v___x_433_;
}
else
{
lean_object* v___x_434_; lean_object* v_v_435_; lean_object* v___x_436_; lean_object* v_bs_x27_437_; lean_object* v_a_439_; lean_object* v___x_444_; 
v___x_434_ = l_Lean_instInhabitedExpr;
v_v_435_ = lean_array_uget(v_bs_426_, v_i_425_);
v___x_436_ = lean_unsigned_to_nat(0u);
v_bs_x27_437_ = lean_array_uset(v_bs_426_, v_i_425_, v___x_436_);
v___x_444_ = lean_usize_to_nat(v_i_425_);
if (v_a_417_ == 0)
{
lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_445_ = lean_array_get_borrowed(v___x_434_, v_a_418_, v___x_444_);
v___x_446_ = lean_array_get_borrowed(v___x_434_, v_a_419_, v___x_444_);
lean_dec(v___x_444_);
lean_inc(v___x_446_);
lean_inc(v___x_445_);
lean_inc_ref(v___x_421_);
lean_inc_ref(v_recArgInfos_420_);
v___x_447_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnF___boxed), 10, 5);
lean_closure_set(v___x_447_, 0, v_recArgInfos_420_);
lean_closure_set(v___x_447_, 1, v___x_421_);
lean_closure_set(v___x_447_, 2, v_v_435_);
lean_closure_set(v___x_447_, 3, v___x_445_);
lean_closure_set(v___x_447_, 4, v___x_446_);
lean_inc_ref(v_preDefs_422_);
v___x_448_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v_preDefs_422_, v___x_447_, v___y_427_, v___y_428_, v___y_429_, v___y_430_);
if (lean_obj_tag(v___x_448_) == 0)
{
lean_object* v_a_449_; 
v_a_449_ = lean_ctor_get(v___x_448_, 0);
lean_inc(v_a_449_);
lean_dec_ref_known(v___x_448_, 1);
v_a_439_ = v_a_449_;
goto v___jp_438_;
}
else
{
lean_object* v_a_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_457_; 
lean_dec_ref(v_bs_x27_437_);
lean_dec_ref(v_a_423_);
lean_dec_ref(v_preDefs_422_);
lean_dec_ref(v___x_421_);
lean_dec_ref(v_recArgInfos_420_);
v_a_450_ = lean_ctor_get(v___x_448_, 0);
v_isSharedCheck_457_ = !lean_is_exclusive(v___x_448_);
if (v_isSharedCheck_457_ == 0)
{
v___x_452_ = v___x_448_;
v_isShared_453_ = v_isSharedCheck_457_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_a_450_);
lean_dec(v___x_448_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_457_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v___x_455_; 
if (v_isShared_453_ == 0)
{
v___x_455_ = v___x_452_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v_a_450_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
return v___x_455_;
}
}
}
}
else
{
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v_dummy_461_; lean_object* v_nargs_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_458_ = lean_array_get_borrowed(v___x_434_, v_a_418_, v___x_444_);
v___x_459_ = lean_array_get_borrowed(v___x_434_, v_a_419_, v___x_444_);
lean_dec(v___x_444_);
lean_inc_ref(v_a_423_);
v___x_460_ = lean_apply_1(v_a_423_, v___x_436_);
v_dummy_461_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg___closed__0);
v_nargs_462_ = l_Lean_Expr_getAppNumArgs(v___x_460_);
lean_inc(v_nargs_462_);
v___x_463_ = lean_mk_array(v_nargs_462_, v_dummy_461_);
v___x_464_ = lean_unsigned_to_nat(1u);
v___x_465_ = lean_nat_sub(v_nargs_462_, v___x_464_);
lean_dec(v_nargs_462_);
v___x_466_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___x_460_, v___x_463_, v___x_465_);
lean_inc(v___x_459_);
lean_inc(v___x_458_);
lean_inc_ref(v___x_421_);
lean_inc_ref(v_recArgInfos_420_);
v___x_467_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkIndPredBRecOnF___boxed), 11, 6);
lean_closure_set(v___x_467_, 0, v_recArgInfos_420_);
lean_closure_set(v___x_467_, 1, v___x_421_);
lean_closure_set(v___x_467_, 2, v_v_435_);
lean_closure_set(v___x_467_, 3, v___x_458_);
lean_closure_set(v___x_467_, 4, v___x_459_);
lean_closure_set(v___x_467_, 5, v___x_466_);
lean_inc_ref(v_preDefs_422_);
v___x_468_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v_preDefs_422_, v___x_467_, v___y_427_, v___y_428_, v___y_429_, v___y_430_);
if (lean_obj_tag(v___x_468_) == 0)
{
lean_object* v_a_469_; lean_object* v_fst_470_; lean_object* v_snd_471_; lean_object* v___y_473_; lean_object* v___x_482_; uint8_t v___x_483_; 
v_a_469_ = lean_ctor_get(v___x_468_, 0);
lean_inc(v_a_469_);
lean_dec_ref_known(v___x_468_, 1);
v_fst_470_ = lean_ctor_get(v_a_469_, 0);
lean_inc(v_fst_470_);
v_snd_471_ = lean_ctor_get(v_a_469_, 1);
lean_inc(v_snd_471_);
lean_dec(v_a_469_);
v___x_482_ = lean_array_get_size(v_snd_471_);
v___x_483_ = lean_nat_dec_lt(v___x_436_, v___x_482_);
if (v___x_483_ == 0)
{
lean_dec(v_snd_471_);
v_a_439_ = v_fst_470_;
goto v___jp_438_;
}
else
{
lean_object* v___x_484_; uint8_t v___x_485_; 
v___x_484_ = lean_box(0);
v___x_485_ = lean_nat_dec_le(v___x_482_, v___x_482_);
if (v___x_485_ == 0)
{
if (v___x_483_ == 0)
{
lean_dec(v_snd_471_);
v_a_439_ = v_fst_470_;
goto v___jp_438_;
}
else
{
size_t v___x_486_; size_t v___x_487_; lean_object* v___x_488_; 
v___x_486_ = ((size_t)0ULL);
v___x_487_ = lean_usize_of_nat(v___x_482_);
v___x_488_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13(v_snd_471_, v___x_486_, v___x_487_, v___x_484_, v___y_427_, v___y_428_, v___y_429_, v___y_430_);
lean_dec(v_snd_471_);
v___y_473_ = v___x_488_;
goto v___jp_472_;
}
}
else
{
size_t v___x_489_; size_t v___x_490_; lean_object* v___x_491_; 
v___x_489_ = ((size_t)0ULL);
v___x_490_ = lean_usize_of_nat(v___x_482_);
v___x_491_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13(v_snd_471_, v___x_489_, v___x_490_, v___x_484_, v___y_427_, v___y_428_, v___y_429_, v___y_430_);
lean_dec(v_snd_471_);
v___y_473_ = v___x_491_;
goto v___jp_472_;
}
}
v___jp_472_:
{
if (lean_obj_tag(v___y_473_) == 0)
{
lean_dec_ref_known(v___y_473_, 1);
v_a_439_ = v_fst_470_;
goto v___jp_438_;
}
else
{
lean_object* v_a_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_481_; 
lean_dec(v_fst_470_);
lean_dec_ref(v_bs_x27_437_);
lean_dec_ref(v_a_423_);
lean_dec_ref(v_preDefs_422_);
lean_dec_ref(v___x_421_);
lean_dec_ref(v_recArgInfos_420_);
v_a_474_ = lean_ctor_get(v___y_473_, 0);
v_isSharedCheck_481_ = !lean_is_exclusive(v___y_473_);
if (v_isSharedCheck_481_ == 0)
{
v___x_476_ = v___y_473_;
v_isShared_477_ = v_isSharedCheck_481_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_a_474_);
lean_dec(v___y_473_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_481_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v___x_479_; 
if (v_isShared_477_ == 0)
{
v___x_479_ = v___x_476_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v_a_474_);
v___x_479_ = v_reuseFailAlloc_480_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
return v___x_479_;
}
}
}
}
}
else
{
lean_object* v_a_492_; lean_object* v___x_494_; uint8_t v_isShared_495_; uint8_t v_isSharedCheck_499_; 
lean_dec_ref(v_bs_x27_437_);
lean_dec_ref(v_a_423_);
lean_dec_ref(v_preDefs_422_);
lean_dec_ref(v___x_421_);
lean_dec_ref(v_recArgInfos_420_);
v_a_492_ = lean_ctor_get(v___x_468_, 0);
v_isSharedCheck_499_ = !lean_is_exclusive(v___x_468_);
if (v_isSharedCheck_499_ == 0)
{
v___x_494_ = v___x_468_;
v_isShared_495_ = v_isSharedCheck_499_;
goto v_resetjp_493_;
}
else
{
lean_inc(v_a_492_);
lean_dec(v___x_468_);
v___x_494_ = lean_box(0);
v_isShared_495_ = v_isSharedCheck_499_;
goto v_resetjp_493_;
}
v_resetjp_493_:
{
lean_object* v___x_497_; 
if (v_isShared_495_ == 0)
{
v___x_497_ = v___x_494_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v_a_492_);
v___x_497_ = v_reuseFailAlloc_498_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
return v___x_497_;
}
}
}
}
v___jp_438_:
{
size_t v___x_440_; size_t v___x_441_; lean_object* v___x_442_; 
v___x_440_ = ((size_t)1ULL);
v___x_441_ = lean_usize_add(v_i_425_, v___x_440_);
v___x_442_ = lean_array_uset(v_bs_x27_437_, v_i_425_, v_a_439_);
v_i_425_ = v___x_441_;
v_bs_426_ = v___x_442_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg___boxed(lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_recArgInfos_503_, lean_object* v___x_504_, lean_object* v_preDefs_505_, lean_object* v_a_506_, lean_object* v_sz_507_, lean_object* v_i_508_, lean_object* v_bs_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_){
_start:
{
uint8_t v_a_27382__boxed_515_; size_t v_sz_boxed_516_; size_t v_i_boxed_517_; lean_object* v_res_518_; 
v_a_27382__boxed_515_ = lean_unbox(v_a_500_);
v_sz_boxed_516_ = lean_unbox_usize(v_sz_507_);
lean_dec(v_sz_507_);
v_i_boxed_517_ = lean_unbox_usize(v_i_508_);
lean_dec(v_i_508_);
v_res_518_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg(v_a_27382__boxed_515_, v_a_501_, v_a_502_, v_recArgInfos_503_, v___x_504_, v_preDefs_505_, v_a_506_, v_sz_boxed_516_, v_i_boxed_517_, v_bs_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_);
lean_dec(v___y_513_);
lean_dec_ref(v___y_512_);
lean_dec(v___y_511_);
lean_dec_ref(v___y_510_);
lean_dec_ref(v_a_502_);
lean_dec_ref(v_a_501_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11_spec__21(lean_object* v_msgData_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_){
_start:
{
lean_object* v___x_525_; lean_object* v_env_526_; lean_object* v___x_527_; lean_object* v_mctx_528_; lean_object* v_lctx_529_; lean_object* v_options_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_525_ = lean_st_ref_get(v___y_523_);
v_env_526_ = lean_ctor_get(v___x_525_, 0);
lean_inc_ref(v_env_526_);
lean_dec(v___x_525_);
v___x_527_ = lean_st_ref_get(v___y_521_);
v_mctx_528_ = lean_ctor_get(v___x_527_, 0);
lean_inc_ref(v_mctx_528_);
lean_dec(v___x_527_);
v_lctx_529_ = lean_ctor_get(v___y_520_, 2);
v_options_530_ = lean_ctor_get(v___y_522_, 2);
lean_inc_ref(v_options_530_);
lean_inc_ref(v_lctx_529_);
v___x_531_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_531_, 0, v_env_526_);
lean_ctor_set(v___x_531_, 1, v_mctx_528_);
lean_ctor_set(v___x_531_, 2, v_lctx_529_);
lean_ctor_set(v___x_531_, 3, v_options_530_);
v___x_532_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_532_, 0, v___x_531_);
lean_ctor_set(v___x_532_, 1, v_msgData_519_);
v___x_533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_533_, 0, v___x_532_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11_spec__21___boxed(lean_object* v_msgData_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11_spec__21(v_msgData_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_);
lean_dec(v___y_538_);
lean_dec_ref(v___y_537_);
lean_dec(v___y_536_);
lean_dec_ref(v___y_535_);
return v_res_540_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___closed__0(void){
_start:
{
lean_object* v___x_541_; double v___x_542_; 
v___x_541_ = lean_unsigned_to_nat(0u);
v___x_542_ = lean_float_of_nat(v___x_541_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(lean_object* v_cls_546_, lean_object* v_msg_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_){
_start:
{
lean_object* v_ref_553_; lean_object* v___x_554_; lean_object* v_a_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_599_; 
v_ref_553_ = lean_ctor_get(v___y_550_, 5);
v___x_554_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11_spec__21(v_msg_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_);
v_a_555_ = lean_ctor_get(v___x_554_, 0);
v_isSharedCheck_599_ = !lean_is_exclusive(v___x_554_);
if (v_isSharedCheck_599_ == 0)
{
v___x_557_ = v___x_554_;
v_isShared_558_ = v_isSharedCheck_599_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_a_555_);
lean_dec(v___x_554_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_599_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v___x_559_; lean_object* v_traceState_560_; lean_object* v_env_561_; lean_object* v_nextMacroScope_562_; lean_object* v_ngen_563_; lean_object* v_auxDeclNGen_564_; lean_object* v_cache_565_; lean_object* v_messages_566_; lean_object* v_infoState_567_; lean_object* v_snapshotTasks_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_598_; 
v___x_559_ = lean_st_ref_take(v___y_551_);
v_traceState_560_ = lean_ctor_get(v___x_559_, 4);
v_env_561_ = lean_ctor_get(v___x_559_, 0);
v_nextMacroScope_562_ = lean_ctor_get(v___x_559_, 1);
v_ngen_563_ = lean_ctor_get(v___x_559_, 2);
v_auxDeclNGen_564_ = lean_ctor_get(v___x_559_, 3);
v_cache_565_ = lean_ctor_get(v___x_559_, 5);
v_messages_566_ = lean_ctor_get(v___x_559_, 6);
v_infoState_567_ = lean_ctor_get(v___x_559_, 7);
v_snapshotTasks_568_ = lean_ctor_get(v___x_559_, 8);
v_isSharedCheck_598_ = !lean_is_exclusive(v___x_559_);
if (v_isSharedCheck_598_ == 0)
{
v___x_570_ = v___x_559_;
v_isShared_571_ = v_isSharedCheck_598_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_snapshotTasks_568_);
lean_inc(v_infoState_567_);
lean_inc(v_messages_566_);
lean_inc(v_cache_565_);
lean_inc(v_traceState_560_);
lean_inc(v_auxDeclNGen_564_);
lean_inc(v_ngen_563_);
lean_inc(v_nextMacroScope_562_);
lean_inc(v_env_561_);
lean_dec(v___x_559_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_598_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
uint64_t v_tid_572_; lean_object* v_traces_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_597_; 
v_tid_572_ = lean_ctor_get_uint64(v_traceState_560_, sizeof(void*)*1);
v_traces_573_ = lean_ctor_get(v_traceState_560_, 0);
v_isSharedCheck_597_ = !lean_is_exclusive(v_traceState_560_);
if (v_isSharedCheck_597_ == 0)
{
v___x_575_ = v_traceState_560_;
v_isShared_576_ = v_isSharedCheck_597_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_traces_573_);
lean_dec(v_traceState_560_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_597_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v___x_577_; double v___x_578_; uint8_t v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_587_; 
v___x_577_ = lean_box(0);
v___x_578_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___closed__0);
v___x_579_ = 0;
v___x_580_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___closed__1));
v___x_581_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_581_, 0, v_cls_546_);
lean_ctor_set(v___x_581_, 1, v___x_577_);
lean_ctor_set(v___x_581_, 2, v___x_580_);
lean_ctor_set_float(v___x_581_, sizeof(void*)*3, v___x_578_);
lean_ctor_set_float(v___x_581_, sizeof(void*)*3 + 8, v___x_578_);
lean_ctor_set_uint8(v___x_581_, sizeof(void*)*3 + 16, v___x_579_);
v___x_582_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___closed__2));
v___x_583_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_583_, 0, v___x_581_);
lean_ctor_set(v___x_583_, 1, v_a_555_);
lean_ctor_set(v___x_583_, 2, v___x_582_);
lean_inc(v_ref_553_);
v___x_584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_584_, 0, v_ref_553_);
lean_ctor_set(v___x_584_, 1, v___x_583_);
v___x_585_ = l_Lean_PersistentArray_push___redArg(v_traces_573_, v___x_584_);
if (v_isShared_576_ == 0)
{
lean_ctor_set(v___x_575_, 0, v___x_585_);
v___x_587_ = v___x_575_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v___x_585_);
lean_ctor_set_uint64(v_reuseFailAlloc_596_, sizeof(void*)*1, v_tid_572_);
v___x_587_ = v_reuseFailAlloc_596_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
lean_object* v___x_589_; 
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 4, v___x_587_);
v___x_589_ = v___x_570_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v_env_561_);
lean_ctor_set(v_reuseFailAlloc_595_, 1, v_nextMacroScope_562_);
lean_ctor_set(v_reuseFailAlloc_595_, 2, v_ngen_563_);
lean_ctor_set(v_reuseFailAlloc_595_, 3, v_auxDeclNGen_564_);
lean_ctor_set(v_reuseFailAlloc_595_, 4, v___x_587_);
lean_ctor_set(v_reuseFailAlloc_595_, 5, v_cache_565_);
lean_ctor_set(v_reuseFailAlloc_595_, 6, v_messages_566_);
lean_ctor_set(v_reuseFailAlloc_595_, 7, v_infoState_567_);
lean_ctor_set(v_reuseFailAlloc_595_, 8, v_snapshotTasks_568_);
v___x_589_ = v_reuseFailAlloc_595_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_593_; 
v___x_590_ = lean_st_ref_set(v___y_551_, v___x_589_);
v___x_591_ = lean_box(0);
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 0, v___x_591_);
v___x_593_ = v___x_557_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v___x_591_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___boxed(lean_object* v_cls_600_, lean_object* v_msg_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_){
_start:
{
lean_object* v_res_607_; 
v_res_607_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v_cls_600_, v_msg_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_);
lean_dec(v___y_605_);
lean_dec_ref(v___y_604_);
lean_dec(v___y_603_);
lean_dec_ref(v___y_602_);
return v_res_607_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9(lean_object* v_as_608_, lean_object* v_bs_609_, lean_object* v_i_610_, lean_object* v_cs_611_){
_start:
{
lean_object* v___x_612_; uint8_t v___x_613_; 
v___x_612_ = lean_array_get_size(v_as_608_);
v___x_613_ = lean_nat_dec_lt(v_i_610_, v___x_612_);
if (v___x_613_ == 0)
{
lean_dec(v_i_610_);
return v_cs_611_;
}
else
{
lean_object* v___x_614_; uint8_t v___x_615_; 
v___x_614_ = lean_array_get_size(v_bs_609_);
v___x_615_ = lean_nat_dec_lt(v_i_610_, v___x_614_);
if (v___x_615_ == 0)
{
lean_dec(v_i_610_);
return v_cs_611_;
}
else
{
lean_object* v_a_616_; lean_object* v_ref_617_; uint8_t v_kind_618_; lean_object* v_levelParams_619_; lean_object* v_modifiers_620_; lean_object* v_declName_621_; lean_object* v_binders_622_; lean_object* v_numSectionVars_623_; lean_object* v_type_624_; lean_object* v_termination_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_637_; 
v_a_616_ = lean_array_fget(v_as_608_, v_i_610_);
v_ref_617_ = lean_ctor_get(v_a_616_, 0);
v_kind_618_ = lean_ctor_get_uint8(v_a_616_, sizeof(void*)*9);
v_levelParams_619_ = lean_ctor_get(v_a_616_, 1);
v_modifiers_620_ = lean_ctor_get(v_a_616_, 2);
v_declName_621_ = lean_ctor_get(v_a_616_, 3);
v_binders_622_ = lean_ctor_get(v_a_616_, 4);
v_numSectionVars_623_ = lean_ctor_get(v_a_616_, 5);
v_type_624_ = lean_ctor_get(v_a_616_, 6);
v_termination_625_ = lean_ctor_get(v_a_616_, 8);
v_isSharedCheck_637_ = !lean_is_exclusive(v_a_616_);
if (v_isSharedCheck_637_ == 0)
{
lean_object* v_unused_638_; 
v_unused_638_ = lean_ctor_get(v_a_616_, 7);
lean_dec(v_unused_638_);
v___x_627_ = v_a_616_;
v_isShared_628_ = v_isSharedCheck_637_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_termination_625_);
lean_inc(v_type_624_);
lean_inc(v_numSectionVars_623_);
lean_inc(v_binders_622_);
lean_inc(v_declName_621_);
lean_inc(v_modifiers_620_);
lean_inc(v_levelParams_619_);
lean_inc(v_ref_617_);
lean_dec(v_a_616_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_637_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v_b_629_; lean_object* v___x_631_; 
v_b_629_ = lean_array_fget_borrowed(v_bs_609_, v_i_610_);
lean_inc(v_b_629_);
if (v_isShared_628_ == 0)
{
lean_ctor_set(v___x_627_, 7, v_b_629_);
v___x_631_ = v___x_627_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v_ref_617_);
lean_ctor_set(v_reuseFailAlloc_636_, 1, v_levelParams_619_);
lean_ctor_set(v_reuseFailAlloc_636_, 2, v_modifiers_620_);
lean_ctor_set(v_reuseFailAlloc_636_, 3, v_declName_621_);
lean_ctor_set(v_reuseFailAlloc_636_, 4, v_binders_622_);
lean_ctor_set(v_reuseFailAlloc_636_, 5, v_numSectionVars_623_);
lean_ctor_set(v_reuseFailAlloc_636_, 6, v_type_624_);
lean_ctor_set(v_reuseFailAlloc_636_, 7, v_b_629_);
lean_ctor_set(v_reuseFailAlloc_636_, 8, v_termination_625_);
lean_ctor_set_uint8(v_reuseFailAlloc_636_, sizeof(void*)*9, v_kind_618_);
v___x_631_ = v_reuseFailAlloc_636_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_632_ = lean_unsigned_to_nat(1u);
v___x_633_ = lean_nat_add(v_i_610_, v___x_632_);
lean_dec(v_i_610_);
v___x_634_ = lean_array_push(v_cs_611_, v___x_631_);
v_i_610_ = v___x_633_;
v_cs_611_ = v___x_634_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9___boxed(lean_object* v_as_639_, lean_object* v_bs_640_, lean_object* v_i_641_, lean_object* v_cs_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9(v_as_639_, v_bs_640_, v_i_641_, v_cs_642_);
lean_dec_ref(v_bs_640_);
lean_dec_ref(v_as_639_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16_spec__29___redArg(lean_object* v_declName_644_, uint8_t v_s_645_, lean_object* v___y_646_, lean_object* v___y_647_){
_start:
{
lean_object* v___x_649_; lean_object* v_env_650_; lean_object* v_nextMacroScope_651_; lean_object* v_ngen_652_; lean_object* v_auxDeclNGen_653_; lean_object* v_traceState_654_; lean_object* v_messages_655_; lean_object* v_infoState_656_; lean_object* v_snapshotTasks_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_686_; 
v___x_649_ = lean_st_ref_take(v___y_647_);
v_env_650_ = lean_ctor_get(v___x_649_, 0);
v_nextMacroScope_651_ = lean_ctor_get(v___x_649_, 1);
v_ngen_652_ = lean_ctor_get(v___x_649_, 2);
v_auxDeclNGen_653_ = lean_ctor_get(v___x_649_, 3);
v_traceState_654_ = lean_ctor_get(v___x_649_, 4);
v_messages_655_ = lean_ctor_get(v___x_649_, 6);
v_infoState_656_ = lean_ctor_get(v___x_649_, 7);
v_snapshotTasks_657_ = lean_ctor_get(v___x_649_, 8);
v_isSharedCheck_686_ = !lean_is_exclusive(v___x_649_);
if (v_isSharedCheck_686_ == 0)
{
lean_object* v_unused_687_; 
v_unused_687_ = lean_ctor_get(v___x_649_, 5);
lean_dec(v_unused_687_);
v___x_659_ = v___x_649_;
v_isShared_660_ = v_isSharedCheck_686_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_snapshotTasks_657_);
lean_inc(v_infoState_656_);
lean_inc(v_messages_655_);
lean_inc(v_traceState_654_);
lean_inc(v_auxDeclNGen_653_);
lean_inc(v_ngen_652_);
lean_inc(v_nextMacroScope_651_);
lean_inc(v_env_650_);
lean_dec(v___x_649_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_686_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
uint8_t v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_666_; 
v___x_661_ = 0;
v___x_662_ = lean_box(0);
v___x_663_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_650_, v_declName_644_, v_s_645_, v___x_661_, v___x_662_);
v___x_664_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__2);
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 5, v___x_664_);
lean_ctor_set(v___x_659_, 0, v___x_663_);
v___x_666_ = v___x_659_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v___x_663_);
lean_ctor_set(v_reuseFailAlloc_685_, 1, v_nextMacroScope_651_);
lean_ctor_set(v_reuseFailAlloc_685_, 2, v_ngen_652_);
lean_ctor_set(v_reuseFailAlloc_685_, 3, v_auxDeclNGen_653_);
lean_ctor_set(v_reuseFailAlloc_685_, 4, v_traceState_654_);
lean_ctor_set(v_reuseFailAlloc_685_, 5, v___x_664_);
lean_ctor_set(v_reuseFailAlloc_685_, 6, v_messages_655_);
lean_ctor_set(v_reuseFailAlloc_685_, 7, v_infoState_656_);
lean_ctor_set(v_reuseFailAlloc_685_, 8, v_snapshotTasks_657_);
v___x_666_ = v_reuseFailAlloc_685_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v_mctx_669_; lean_object* v_zetaDeltaFVarIds_670_; lean_object* v_postponed_671_; lean_object* v_diag_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_683_; 
v___x_667_ = lean_st_ref_set(v___y_647_, v___x_666_);
v___x_668_ = lean_st_ref_take(v___y_646_);
v_mctx_669_ = lean_ctor_get(v___x_668_, 0);
v_zetaDeltaFVarIds_670_ = lean_ctor_get(v___x_668_, 2);
v_postponed_671_ = lean_ctor_get(v___x_668_, 3);
v_diag_672_ = lean_ctor_get(v___x_668_, 4);
v_isSharedCheck_683_ = !lean_is_exclusive(v___x_668_);
if (v_isSharedCheck_683_ == 0)
{
lean_object* v_unused_684_; 
v_unused_684_ = lean_ctor_get(v___x_668_, 1);
lean_dec(v_unused_684_);
v___x_674_ = v___x_668_;
v_isShared_675_ = v_isSharedCheck_683_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_diag_672_);
lean_inc(v_postponed_671_);
lean_inc(v_zetaDeltaFVarIds_670_);
lean_inc(v_mctx_669_);
lean_dec(v___x_668_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_683_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v___x_676_; lean_object* v___x_678_; 
v___x_676_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__3, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__3);
if (v_isShared_675_ == 0)
{
lean_ctor_set(v___x_674_, 1, v___x_676_);
v___x_678_ = v___x_674_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v_mctx_669_);
lean_ctor_set(v_reuseFailAlloc_682_, 1, v___x_676_);
lean_ctor_set(v_reuseFailAlloc_682_, 2, v_zetaDeltaFVarIds_670_);
lean_ctor_set(v_reuseFailAlloc_682_, 3, v_postponed_671_);
lean_ctor_set(v_reuseFailAlloc_682_, 4, v_diag_672_);
v___x_678_ = v_reuseFailAlloc_682_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_679_ = lean_st_ref_set(v___y_646_, v___x_678_);
v___x_680_ = lean_box(0);
v___x_681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_681_, 0, v___x_680_);
return v___x_681_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16_spec__29___redArg___boxed(lean_object* v_declName_688_, lean_object* v_s_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_){
_start:
{
uint8_t v_s_boxed_693_; lean_object* v_res_694_; 
v_s_boxed_693_ = lean_unbox(v_s_689_);
v_res_694_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16_spec__29___redArg(v_declName_688_, v_s_boxed_693_, v___y_690_, v___y_691_);
lean_dec(v___y_691_);
lean_dec(v___y_690_);
return v_res_694_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16(lean_object* v_declName_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_){
_start:
{
uint8_t v___x_701_; lean_object* v___x_702_; 
v___x_701_ = 0;
v___x_702_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16_spec__29___redArg(v_declName_695_, v___x_701_, v___y_697_, v___y_699_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16___boxed(lean_object* v_declName_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_){
_start:
{
lean_object* v_res_709_; 
v_res_709_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16(v_declName_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_);
lean_dec(v___y_707_);
lean_dec_ref(v___y_706_);
lean_dec(v___y_705_);
lean_dec_ref(v___y_704_);
return v_res_709_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg(lean_object* v_xs_713_, uint8_t v_a_714_, lean_object* v_preDefs_715_, lean_object* v___x_716_, size_t v_sz_717_, size_t v_i_718_, lean_object* v_bs_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_){
_start:
{
uint8_t v___x_725_; 
v___x_725_ = lean_usize_dec_lt(v_i_718_, v_sz_717_);
if (v___x_725_ == 0)
{
lean_object* v___x_726_; 
lean_dec(v___x_716_);
v___x_726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_726_, 0, v_bs_719_);
return v___x_726_;
}
else
{
lean_object* v_v_727_; lean_object* v___x_728_; lean_object* v_bs_x27_729_; lean_object* v_a_731_; lean_object* v___y_737_; uint8_t v___x_747_; lean_object* v___x_748_; 
v_v_727_ = lean_array_uget(v_bs_719_, v_i_718_);
v___x_728_ = lean_unsigned_to_nat(0u);
v_bs_x27_729_ = lean_array_uset(v_bs_719_, v_i_718_, v___x_728_);
v___x_747_ = 1;
v___x_748_ = l_Lean_Meta_mkLambdaFVars(v_xs_713_, v_v_727_, v_a_714_, v___x_725_, v_a_714_, v___x_725_, v___x_747_, v___y_720_, v___y_721_, v___y_722_, v___y_723_);
if (lean_obj_tag(v___x_748_) == 0)
{
lean_object* v_a_749_; lean_object* v___x_750_; 
v_a_749_ = lean_ctor_get(v___x_748_, 0);
lean_inc(v_a_749_);
lean_dec_ref_known(v___x_748_, 1);
v___x_750_ = l_Lean_Elab_eraseRecAppSyntaxExpr(v_a_749_, v___y_722_, v___y_723_);
if (lean_obj_tag(v___x_750_) == 0)
{
lean_object* v_a_751_; lean_object* v___x_752_; 
v_a_751_ = lean_ctor_get(v___x_750_, 0);
lean_inc_n(v_a_751_, 2);
lean_dec_ref_known(v___x_750_, 1);
lean_inc(v___y_723_);
lean_inc_ref(v___y_722_);
lean_inc(v___y_721_);
lean_inc_ref(v___y_720_);
v___x_752_ = lean_infer_type(v_a_751_, v___y_720_, v___y_721_, v___y_722_, v___y_723_);
if (lean_obj_tag(v___x_752_) == 0)
{
lean_object* v_a_753_; lean_object* v___x_754_; 
v_a_753_ = lean_ctor_get(v___x_752_, 0);
lean_inc(v_a_753_);
lean_dec_ref_known(v___x_752_, 1);
v___x_754_ = l_Lean_Meta_letToHave(v_a_753_, v___y_720_, v___y_721_, v___y_722_, v___y_723_);
if (lean_obj_tag(v___x_754_) == 0)
{
lean_object* v_a_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_838_; 
v_a_755_ = lean_ctor_get(v___x_754_, 0);
v_isSharedCheck_838_ = !lean_is_exclusive(v___x_754_);
if (v_isSharedCheck_838_ == 0)
{
v___x_757_ = v___x_754_;
v_isShared_758_ = v_isSharedCheck_838_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_a_755_);
lean_dec(v___x_754_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_838_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v_modifiers_763_; lean_object* v_levelParams_764_; lean_object* v_declName_765_; lean_object* v_env_766_; uint8_t v_isUnsafe_767_; lean_object* v___x_768_; lean_object* v___x_769_; uint32_t v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; uint8_t v___y_774_; 
v___x_759_ = lean_st_ref_get(v___y_723_);
v___x_760_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_761_ = lean_usize_to_nat(v_i_718_);
v___x_762_ = lean_array_get_borrowed(v___x_760_, v_preDefs_715_, v___x_761_);
lean_dec(v___x_761_);
v_modifiers_763_ = lean_ctor_get(v___x_762_, 2);
v_levelParams_764_ = lean_ctor_get(v___x_762_, 1);
v_declName_765_ = lean_ctor_get(v___x_762_, 3);
v_env_766_ = lean_ctor_get(v___x_759_, 0);
lean_inc_ref(v_env_766_);
lean_dec(v___x_759_);
v_isUnsafe_767_ = lean_ctor_get_uint8(v_modifiers_763_, sizeof(void*)*3 + 4);
v___x_768_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg___closed__1));
lean_inc(v_declName_765_);
v___x_769_ = l_Lean_Name_append(v_declName_765_, v___x_768_);
lean_inc(v_a_751_);
v___x_770_ = l_Lean_getMaxHeight(v_env_766_, v_a_751_);
lean_inc(v_levelParams_764_);
lean_inc(v___x_769_);
v___x_771_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_771_, 0, v___x_769_);
lean_ctor_set(v___x_771_, 1, v_levelParams_764_);
lean_ctor_set(v___x_771_, 2, v_a_755_);
v___x_772_ = lean_box(1);
if (v_isUnsafe_767_ == 0)
{
uint8_t v___x_836_; 
v___x_836_ = 1;
v___y_774_ = v___x_836_;
goto v___jp_773_;
}
else
{
uint8_t v___x_837_; 
v___x_837_ = 0;
v___y_774_ = v___x_837_;
goto v___jp_773_;
}
v___jp_773_:
{
lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_779_; 
v___x_775_ = lean_box(0);
lean_inc(v___x_769_);
v___x_776_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_776_, 0, v___x_769_);
lean_ctor_set(v___x_776_, 1, v___x_775_);
v___x_777_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_777_, 0, v___x_771_);
lean_ctor_set(v___x_777_, 1, v_a_751_);
lean_ctor_set(v___x_777_, 2, v___x_772_);
lean_ctor_set(v___x_777_, 3, v___x_776_);
lean_ctor_set_uint8(v___x_777_, sizeof(void*)*4, v___y_774_);
if (v_isShared_758_ == 0)
{
lean_ctor_set_tag(v___x_757_, 1);
lean_ctor_set(v___x_757_, 0, v___x_777_);
v___x_779_ = v___x_757_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v___x_777_);
v___x_779_ = v_reuseFailAlloc_835_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
lean_object* v___x_780_; 
v___x_780_ = l_Lean_addDecl(v___x_779_, v_a_714_, v___y_722_, v___y_723_);
if (lean_obj_tag(v___x_780_) == 0)
{
lean_object* v___x_781_; lean_object* v_env_782_; lean_object* v_nextMacroScope_783_; lean_object* v_ngen_784_; lean_object* v_auxDeclNGen_785_; lean_object* v_traceState_786_; lean_object* v_messages_787_; lean_object* v_infoState_788_; lean_object* v_snapshotTasks_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_825_; 
lean_dec_ref_known(v___x_780_, 1);
v___x_781_ = lean_st_ref_take(v___y_723_);
v_env_782_ = lean_ctor_get(v___x_781_, 0);
v_nextMacroScope_783_ = lean_ctor_get(v___x_781_, 1);
v_ngen_784_ = lean_ctor_get(v___x_781_, 2);
v_auxDeclNGen_785_ = lean_ctor_get(v___x_781_, 3);
v_traceState_786_ = lean_ctor_get(v___x_781_, 4);
v_messages_787_ = lean_ctor_get(v___x_781_, 6);
v_infoState_788_ = lean_ctor_get(v___x_781_, 7);
v_snapshotTasks_789_ = lean_ctor_get(v___x_781_, 8);
v_isSharedCheck_825_ = !lean_is_exclusive(v___x_781_);
if (v_isSharedCheck_825_ == 0)
{
lean_object* v_unused_826_; 
v_unused_826_ = lean_ctor_get(v___x_781_, 5);
lean_dec(v_unused_826_);
v___x_791_ = v___x_781_;
v_isShared_792_ = v_isSharedCheck_825_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_snapshotTasks_789_);
lean_inc(v_infoState_788_);
lean_inc(v_messages_787_);
lean_inc(v_traceState_786_);
lean_inc(v_auxDeclNGen_785_);
lean_inc(v_ngen_784_);
lean_inc(v_nextMacroScope_783_);
lean_inc(v_env_782_);
lean_dec(v___x_781_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_825_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_796_; 
lean_inc(v___x_769_);
v___x_793_ = l_Lean_setDefHeightOverride(v_env_782_, v___x_769_, v___x_770_);
v___x_794_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__2);
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 5, v___x_794_);
lean_ctor_set(v___x_791_, 0, v___x_793_);
v___x_796_ = v___x_791_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v___x_793_);
lean_ctor_set(v_reuseFailAlloc_824_, 1, v_nextMacroScope_783_);
lean_ctor_set(v_reuseFailAlloc_824_, 2, v_ngen_784_);
lean_ctor_set(v_reuseFailAlloc_824_, 3, v_auxDeclNGen_785_);
lean_ctor_set(v_reuseFailAlloc_824_, 4, v_traceState_786_);
lean_ctor_set(v_reuseFailAlloc_824_, 5, v___x_794_);
lean_ctor_set(v_reuseFailAlloc_824_, 6, v_messages_787_);
lean_ctor_set(v_reuseFailAlloc_824_, 7, v_infoState_788_);
lean_ctor_set(v_reuseFailAlloc_824_, 8, v_snapshotTasks_789_);
v___x_796_ = v_reuseFailAlloc_824_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v_mctx_799_; lean_object* v_zetaDeltaFVarIds_800_; lean_object* v_postponed_801_; lean_object* v_diag_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_822_; 
v___x_797_ = lean_st_ref_set(v___y_723_, v___x_796_);
v___x_798_ = lean_st_ref_take(v___y_721_);
v_mctx_799_ = lean_ctor_get(v___x_798_, 0);
v_zetaDeltaFVarIds_800_ = lean_ctor_get(v___x_798_, 2);
v_postponed_801_ = lean_ctor_get(v___x_798_, 3);
v_diag_802_ = lean_ctor_get(v___x_798_, 4);
v_isSharedCheck_822_ = !lean_is_exclusive(v___x_798_);
if (v_isSharedCheck_822_ == 0)
{
lean_object* v_unused_823_; 
v_unused_823_ = lean_ctor_get(v___x_798_, 1);
lean_dec(v_unused_823_);
v___x_804_ = v___x_798_;
v_isShared_805_ = v_isSharedCheck_822_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_diag_802_);
lean_inc(v_postponed_801_);
lean_inc(v_zetaDeltaFVarIds_800_);
lean_inc(v_mctx_799_);
lean_dec(v___x_798_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_822_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v___x_806_; lean_object* v___x_808_; 
v___x_806_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__3, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__3);
if (v_isShared_805_ == 0)
{
lean_ctor_set(v___x_804_, 1, v___x_806_);
v___x_808_ = v___x_804_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_mctx_799_);
lean_ctor_set(v_reuseFailAlloc_821_, 1, v___x_806_);
lean_ctor_set(v_reuseFailAlloc_821_, 2, v_zetaDeltaFVarIds_800_);
lean_ctor_set(v_reuseFailAlloc_821_, 3, v_postponed_801_);
lean_ctor_set(v_reuseFailAlloc_821_, 4, v_diag_802_);
v___x_808_ = v_reuseFailAlloc_821_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_809_ = lean_st_ref_set(v___y_721_, v___x_808_);
lean_inc(v___x_769_);
v___x_810_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16(v___x_769_, v___y_720_, v___y_721_, v___y_722_, v___y_723_);
if (lean_obj_tag(v___x_810_) == 0)
{
lean_object* v___x_811_; lean_object* v___x_812_; 
lean_dec_ref_known(v___x_810_, 1);
lean_inc(v___x_716_);
v___x_811_ = l_Lean_mkConst(v___x_769_, v___x_716_);
v___x_812_ = l_Lean_mkAppN(v___x_811_, v_xs_713_);
v_a_731_ = v___x_812_;
goto v___jp_730_;
}
else
{
lean_object* v_a_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_820_; 
lean_dec(v___x_769_);
lean_dec_ref(v_bs_x27_729_);
lean_dec(v___x_716_);
v_a_813_ = lean_ctor_get(v___x_810_, 0);
v_isSharedCheck_820_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_820_ == 0)
{
v___x_815_ = v___x_810_;
v_isShared_816_ = v_isSharedCheck_820_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_a_813_);
lean_dec(v___x_810_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_820_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v___x_818_; 
if (v_isShared_816_ == 0)
{
v___x_818_ = v___x_815_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v_a_813_);
v___x_818_ = v_reuseFailAlloc_819_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
return v___x_818_;
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
lean_object* v_a_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_834_; 
lean_dec(v___x_769_);
lean_dec_ref(v_bs_x27_729_);
lean_dec(v___x_716_);
v_a_827_ = lean_ctor_get(v___x_780_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v___x_780_);
if (v_isSharedCheck_834_ == 0)
{
v___x_829_ = v___x_780_;
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_a_827_);
lean_dec(v___x_780_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v___x_832_; 
if (v_isShared_830_ == 0)
{
v___x_832_ = v___x_829_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v_a_827_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
return v___x_832_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_751_);
v___y_737_ = v___x_754_;
goto v___jp_736_;
}
}
else
{
lean_dec(v_a_751_);
v___y_737_ = v___x_752_;
goto v___jp_736_;
}
}
else
{
v___y_737_ = v___x_750_;
goto v___jp_736_;
}
}
else
{
v___y_737_ = v___x_748_;
goto v___jp_736_;
}
v___jp_730_:
{
size_t v___x_732_; size_t v___x_733_; lean_object* v___x_734_; 
v___x_732_ = ((size_t)1ULL);
v___x_733_ = lean_usize_add(v_i_718_, v___x_732_);
v___x_734_ = lean_array_uset(v_bs_x27_729_, v_i_718_, v_a_731_);
v_i_718_ = v___x_733_;
v_bs_719_ = v___x_734_;
goto _start;
}
v___jp_736_:
{
if (lean_obj_tag(v___y_737_) == 0)
{
lean_object* v_a_738_; 
v_a_738_ = lean_ctor_get(v___y_737_, 0);
lean_inc(v_a_738_);
lean_dec_ref_known(v___y_737_, 1);
v_a_731_ = v_a_738_;
goto v___jp_730_;
}
else
{
lean_object* v_a_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_746_; 
lean_dec_ref(v_bs_x27_729_);
lean_dec(v___x_716_);
v_a_739_ = lean_ctor_get(v___y_737_, 0);
v_isSharedCheck_746_ = !lean_is_exclusive(v___y_737_);
if (v_isSharedCheck_746_ == 0)
{
v___x_741_ = v___y_737_;
v_isShared_742_ = v_isSharedCheck_746_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_a_739_);
lean_dec(v___y_737_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_746_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v___x_744_; 
if (v_isShared_742_ == 0)
{
v___x_744_ = v___x_741_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_a_739_);
v___x_744_ = v_reuseFailAlloc_745_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
return v___x_744_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg___boxed(lean_object* v_xs_839_, lean_object* v_a_840_, lean_object* v_preDefs_841_, lean_object* v___x_842_, lean_object* v_sz_843_, lean_object* v_i_844_, lean_object* v_bs_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_){
_start:
{
uint8_t v_a_27816__boxed_851_; size_t v_sz_boxed_852_; size_t v_i_boxed_853_; lean_object* v_res_854_; 
v_a_27816__boxed_851_ = lean_unbox(v_a_840_);
v_sz_boxed_852_ = lean_unbox_usize(v_sz_843_);
lean_dec(v_sz_843_);
v_i_boxed_853_ = lean_unbox_usize(v_i_844_);
lean_dec(v_i_844_);
v_res_854_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg(v_xs_839_, v_a_27816__boxed_851_, v_preDefs_841_, v___x_842_, v_sz_boxed_852_, v_i_boxed_853_, v_bs_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_);
lean_dec(v___y_849_);
lean_dec_ref(v___y_848_);
lean_dec(v___y_847_);
lean_dec_ref(v___y_846_);
lean_dec_ref(v_preDefs_841_);
lean_dec_ref(v_xs_839_);
return v_res_854_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___lam__0(lean_object* v_fixedParamPerms_855_, lean_object* v___x_856_, lean_object* v___x_857_, lean_object* v_xs_858_, lean_object* v_snd_859_, uint8_t v___x_860_, lean_object* v_ys_861_, lean_object* v_x_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_){
_start:
{
lean_object* v_perms_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; uint8_t v___x_872_; uint8_t v___x_873_; lean_object* v___x_874_; 
v_perms_868_ = lean_ctor_get(v_fixedParamPerms_855_, 1);
v___x_869_ = lean_array_get_borrowed(v___x_856_, v_perms_868_, v___x_857_);
lean_inc_ref(v_ys_861_);
lean_inc(v___x_869_);
v___x_870_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v___x_869_, v_xs_858_, v_ys_861_);
v___x_871_ = l_Lean_Expr_beta(v_snd_859_, v_ys_861_);
v___x_872_ = 0;
v___x_873_ = 1;
v___x_874_ = l_Lean_Meta_mkLambdaFVars(v___x_870_, v___x_871_, v___x_872_, v___x_860_, v___x_872_, v___x_860_, v___x_873_, v___y_863_, v___y_864_, v___y_865_, v___y_866_);
lean_dec_ref(v___x_870_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___lam__0___boxed(lean_object* v_fixedParamPerms_875_, lean_object* v___x_876_, lean_object* v___x_877_, lean_object* v_xs_878_, lean_object* v_snd_879_, lean_object* v___x_880_, lean_object* v_ys_881_, lean_object* v_x_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_){
_start:
{
uint8_t v___x_28039__boxed_888_; lean_object* v_res_889_; 
v___x_28039__boxed_888_ = lean_unbox(v___x_880_);
v_res_889_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___lam__0(v_fixedParamPerms_875_, v___x_876_, v___x_877_, v_xs_878_, v_snd_879_, v___x_28039__boxed_888_, v_ys_881_, v_x_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_);
lean_dec(v___y_886_);
lean_dec_ref(v___y_885_);
lean_dec(v___y_884_);
lean_dec_ref(v___y_883_);
lean_dec_ref(v_x_882_);
lean_dec_ref(v_xs_878_);
lean_dec(v___x_877_);
lean_dec_ref(v___x_876_);
lean_dec_ref(v_fixedParamPerms_875_);
return v_res_889_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_890_; 
v___x_890_ = l_Array_instInhabited(lean_box(0));
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg(lean_object* v_fixedParamPerms_891_, lean_object* v_xs_892_, size_t v_sz_893_, size_t v_i_894_, lean_object* v_bs_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_){
_start:
{
uint8_t v___x_901_; 
v___x_901_ = lean_usize_dec_lt(v_i_894_, v_sz_893_);
if (v___x_901_ == 0)
{
lean_object* v___x_902_; 
lean_dec_ref(v_xs_892_);
lean_dec_ref(v_fixedParamPerms_891_);
v___x_902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_902_, 0, v_bs_895_);
return v___x_902_;
}
else
{
lean_object* v_v_903_; lean_object* v_fst_904_; lean_object* v_snd_905_; lean_object* v___x_906_; lean_object* v_bs_x27_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___f_911_; uint8_t v___x_912_; lean_object* v___x_913_; 
v_v_903_ = lean_array_uget_borrowed(v_bs_895_, v_i_894_);
v_fst_904_ = lean_ctor_get(v_v_903_, 0);
lean_inc(v_fst_904_);
v_snd_905_ = lean_ctor_get(v_v_903_, 1);
lean_inc(v_snd_905_);
v___x_906_ = lean_unsigned_to_nat(0u);
v_bs_x27_907_ = lean_array_uset(v_bs_895_, v_i_894_, v___x_906_);
v___x_908_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0);
v___x_909_ = lean_usize_to_nat(v_i_894_);
v___x_910_ = lean_box(v___x_901_);
lean_inc_ref(v_xs_892_);
lean_inc_ref(v_fixedParamPerms_891_);
v___f_911_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___lam__0___boxed), 13, 6);
lean_closure_set(v___f_911_, 0, v_fixedParamPerms_891_);
lean_closure_set(v___f_911_, 1, v___x_908_);
lean_closure_set(v___f_911_, 2, v___x_909_);
lean_closure_set(v___f_911_, 3, v_xs_892_);
lean_closure_set(v___f_911_, 4, v_snd_905_);
lean_closure_set(v___f_911_, 5, v___x_910_);
v___x_912_ = 0;
v___x_913_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg(v_fst_904_, v___f_911_, v___x_912_, v___y_896_, v___y_897_, v___y_898_, v___y_899_);
if (lean_obj_tag(v___x_913_) == 0)
{
lean_object* v_a_914_; size_t v___x_915_; size_t v___x_916_; lean_object* v___x_917_; 
v_a_914_ = lean_ctor_get(v___x_913_, 0);
lean_inc(v_a_914_);
lean_dec_ref_known(v___x_913_, 1);
v___x_915_ = ((size_t)1ULL);
v___x_916_ = lean_usize_add(v_i_894_, v___x_915_);
v___x_917_ = lean_array_uset(v_bs_x27_907_, v_i_894_, v_a_914_);
v_i_894_ = v___x_916_;
v_bs_895_ = v___x_917_;
goto _start;
}
else
{
lean_object* v_a_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_926_; 
lean_dec_ref(v_bs_x27_907_);
lean_dec_ref(v_xs_892_);
lean_dec_ref(v_fixedParamPerms_891_);
v_a_919_ = lean_ctor_get(v___x_913_, 0);
v_isSharedCheck_926_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_926_ == 0)
{
v___x_921_ = v___x_913_;
v_isShared_922_ = v_isSharedCheck_926_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_a_919_);
lean_dec(v___x_913_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_926_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v___x_924_; 
if (v_isShared_922_ == 0)
{
v___x_924_ = v___x_921_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v_a_919_);
v___x_924_ = v_reuseFailAlloc_925_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
return v___x_924_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___boxed(lean_object* v_fixedParamPerms_927_, lean_object* v_xs_928_, lean_object* v_sz_929_, lean_object* v_i_930_, lean_object* v_bs_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_){
_start:
{
size_t v_sz_boxed_937_; size_t v_i_boxed_938_; lean_object* v_res_939_; 
v_sz_boxed_937_ = lean_unbox_usize(v_sz_929_);
lean_dec(v_sz_929_);
v_i_boxed_938_ = lean_unbox_usize(v_i_930_);
lean_dec(v_i_930_);
v_res_939_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg(v_fixedParamPerms_927_, v_xs_928_, v_sz_boxed_937_, v_i_boxed_938_, v_bs_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
return v_res_939_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(lean_object* v_a_940_, lean_object* v_a_941_){
_start:
{
if (lean_obj_tag(v_a_940_) == 0)
{
lean_object* v___x_942_; 
v___x_942_ = l_List_reverse___redArg(v_a_941_);
return v___x_942_;
}
else
{
lean_object* v_head_943_; lean_object* v_tail_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_953_; 
v_head_943_ = lean_ctor_get(v_a_940_, 0);
v_tail_944_ = lean_ctor_get(v_a_940_, 1);
v_isSharedCheck_953_ = !lean_is_exclusive(v_a_940_);
if (v_isSharedCheck_953_ == 0)
{
v___x_946_ = v_a_940_;
v_isShared_947_ = v_isSharedCheck_953_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_tail_944_);
lean_inc(v_head_943_);
lean_dec(v_a_940_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_953_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v___x_948_; lean_object* v___x_950_; 
v___x_948_ = l_Lean_MessageData_ofExpr(v_head_943_);
if (v_isShared_947_ == 0)
{
lean_ctor_set(v___x_946_, 1, v_a_941_);
lean_ctor_set(v___x_946_, 0, v___x_948_);
v___x_950_ = v___x_946_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v___x_948_);
lean_ctor_set(v_reuseFailAlloc_952_, 1, v_a_941_);
v___x_950_ = v_reuseFailAlloc_952_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
v_a_940_ = v_tail_944_;
v_a_941_ = v___x_950_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__15(lean_object* v_a_954_, lean_object* v_a_955_){
_start:
{
if (lean_obj_tag(v_a_954_) == 0)
{
lean_object* v___x_956_; 
v___x_956_ = l_List_reverse___redArg(v_a_955_);
return v___x_956_;
}
else
{
lean_object* v_head_957_; lean_object* v_tail_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_967_; 
v_head_957_ = lean_ctor_get(v_a_954_, 0);
v_tail_958_ = lean_ctor_get(v_a_954_, 1);
v_isSharedCheck_967_ = !lean_is_exclusive(v_a_954_);
if (v_isSharedCheck_967_ == 0)
{
v___x_960_ = v_a_954_;
v_isShared_961_ = v_isSharedCheck_967_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_tail_958_);
lean_inc(v_head_957_);
lean_dec(v_a_954_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_967_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v___x_962_; lean_object* v___x_964_; 
v___x_962_ = l_Lean_mkLevelParam(v_head_957_);
if (v_isShared_961_ == 0)
{
lean_ctor_set(v___x_960_, 1, v_a_955_);
lean_ctor_set(v___x_960_, 0, v___x_962_);
v___x_964_ = v___x_960_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v___x_962_);
lean_ctor_set(v_reuseFailAlloc_966_, 1, v_a_955_);
v___x_964_ = v_reuseFailAlloc_966_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
v_a_954_ = v_tail_958_;
v_a_955_ = v___x_964_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__0(void){
_start:
{
lean_object* v___x_968_; 
v___x_968_ = l_instMonadEIO(lean_box(0));
return v___x_968_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__5(void){
_start:
{
lean_object* v___x_973_; 
v___x_973_ = l_Array_instInhabited(lean_box(0));
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg(lean_object* v_msg_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_){
_start:
{
lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v_toApplicative_982_; lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_1043_; 
v___x_980_ = lean_obj_once(&l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__0, &l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__0_once, _init_l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__0);
v___x_981_ = l_StateRefT_x27_instMonad___redArg(v___x_980_);
v_toApplicative_982_ = lean_ctor_get(v___x_981_, 0);
v_isSharedCheck_1043_ = !lean_is_exclusive(v___x_981_);
if (v_isSharedCheck_1043_ == 0)
{
lean_object* v_unused_1044_; 
v_unused_1044_ = lean_ctor_get(v___x_981_, 1);
lean_dec(v_unused_1044_);
v___x_984_ = v___x_981_;
v_isShared_985_ = v_isSharedCheck_1043_;
goto v_resetjp_983_;
}
else
{
lean_inc(v_toApplicative_982_);
lean_dec(v___x_981_);
v___x_984_ = lean_box(0);
v_isShared_985_ = v_isSharedCheck_1043_;
goto v_resetjp_983_;
}
v_resetjp_983_:
{
lean_object* v_toFunctor_986_; lean_object* v_toSeq_987_; lean_object* v_toSeqLeft_988_; lean_object* v_toSeqRight_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_1041_; 
v_toFunctor_986_ = lean_ctor_get(v_toApplicative_982_, 0);
v_toSeq_987_ = lean_ctor_get(v_toApplicative_982_, 2);
v_toSeqLeft_988_ = lean_ctor_get(v_toApplicative_982_, 3);
v_toSeqRight_989_ = lean_ctor_get(v_toApplicative_982_, 4);
v_isSharedCheck_1041_ = !lean_is_exclusive(v_toApplicative_982_);
if (v_isSharedCheck_1041_ == 0)
{
lean_object* v_unused_1042_; 
v_unused_1042_ = lean_ctor_get(v_toApplicative_982_, 1);
lean_dec(v_unused_1042_);
v___x_991_ = v_toApplicative_982_;
v_isShared_992_ = v_isSharedCheck_1041_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_toSeqRight_989_);
lean_inc(v_toSeqLeft_988_);
lean_inc(v_toSeq_987_);
lean_inc(v_toFunctor_986_);
lean_dec(v_toApplicative_982_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_1041_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v___f_993_; lean_object* v___f_994_; lean_object* v___f_995_; lean_object* v___f_996_; lean_object* v___x_997_; lean_object* v___f_998_; lean_object* v___f_999_; lean_object* v___f_1000_; lean_object* v___x_1002_; 
v___f_993_ = ((lean_object*)(l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__1));
v___f_994_ = ((lean_object*)(l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__2));
lean_inc_ref(v_toFunctor_986_);
v___f_995_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_995_, 0, v_toFunctor_986_);
v___f_996_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_996_, 0, v_toFunctor_986_);
v___x_997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_997_, 0, v___f_995_);
lean_ctor_set(v___x_997_, 1, v___f_996_);
v___f_998_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_998_, 0, v_toSeqRight_989_);
v___f_999_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_999_, 0, v_toSeqLeft_988_);
v___f_1000_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1000_, 0, v_toSeq_987_);
if (v_isShared_992_ == 0)
{
lean_ctor_set(v___x_991_, 4, v___f_998_);
lean_ctor_set(v___x_991_, 3, v___f_999_);
lean_ctor_set(v___x_991_, 2, v___f_1000_);
lean_ctor_set(v___x_991_, 1, v___f_993_);
lean_ctor_set(v___x_991_, 0, v___x_997_);
v___x_1002_ = v___x_991_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v___x_997_);
lean_ctor_set(v_reuseFailAlloc_1040_, 1, v___f_993_);
lean_ctor_set(v_reuseFailAlloc_1040_, 2, v___f_1000_);
lean_ctor_set(v_reuseFailAlloc_1040_, 3, v___f_999_);
lean_ctor_set(v_reuseFailAlloc_1040_, 4, v___f_998_);
v___x_1002_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
lean_object* v___x_1004_; 
if (v_isShared_985_ == 0)
{
lean_ctor_set(v___x_984_, 1, v___f_994_);
lean_ctor_set(v___x_984_, 0, v___x_1002_);
v___x_1004_ = v___x_984_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v___x_1002_);
lean_ctor_set(v_reuseFailAlloc_1039_, 1, v___f_994_);
v___x_1004_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
lean_object* v___x_1005_; lean_object* v_toApplicative_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1037_; 
v___x_1005_ = l_StateRefT_x27_instMonad___redArg(v___x_1004_);
v_toApplicative_1006_ = lean_ctor_get(v___x_1005_, 0);
v_isSharedCheck_1037_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1037_ == 0)
{
lean_object* v_unused_1038_; 
v_unused_1038_ = lean_ctor_get(v___x_1005_, 1);
lean_dec(v_unused_1038_);
v___x_1008_ = v___x_1005_;
v_isShared_1009_ = v_isSharedCheck_1037_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_toApplicative_1006_);
lean_dec(v___x_1005_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1037_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v_toFunctor_1010_; lean_object* v_toSeq_1011_; lean_object* v_toSeqLeft_1012_; lean_object* v_toSeqRight_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1035_; 
v_toFunctor_1010_ = lean_ctor_get(v_toApplicative_1006_, 0);
v_toSeq_1011_ = lean_ctor_get(v_toApplicative_1006_, 2);
v_toSeqLeft_1012_ = lean_ctor_get(v_toApplicative_1006_, 3);
v_toSeqRight_1013_ = lean_ctor_get(v_toApplicative_1006_, 4);
v_isSharedCheck_1035_ = !lean_is_exclusive(v_toApplicative_1006_);
if (v_isSharedCheck_1035_ == 0)
{
lean_object* v_unused_1036_; 
v_unused_1036_ = lean_ctor_get(v_toApplicative_1006_, 1);
lean_dec(v_unused_1036_);
v___x_1015_ = v_toApplicative_1006_;
v_isShared_1016_ = v_isSharedCheck_1035_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_toSeqRight_1013_);
lean_inc(v_toSeqLeft_1012_);
lean_inc(v_toSeq_1011_);
lean_inc(v_toFunctor_1010_);
lean_dec(v_toApplicative_1006_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1035_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
lean_object* v___f_1017_; lean_object* v___f_1018_; lean_object* v___f_1019_; lean_object* v___f_1020_; lean_object* v___x_1021_; lean_object* v___f_1022_; lean_object* v___f_1023_; lean_object* v___f_1024_; lean_object* v___x_1026_; 
v___f_1017_ = ((lean_object*)(l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__3));
v___f_1018_ = ((lean_object*)(l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__4));
lean_inc_ref(v_toFunctor_1010_);
v___f_1019_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1019_, 0, v_toFunctor_1010_);
v___f_1020_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1020_, 0, v_toFunctor_1010_);
v___x_1021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1021_, 0, v___f_1019_);
lean_ctor_set(v___x_1021_, 1, v___f_1020_);
v___f_1022_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1022_, 0, v_toSeqRight_1013_);
v___f_1023_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1023_, 0, v_toSeqLeft_1012_);
v___f_1024_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1024_, 0, v_toSeq_1011_);
if (v_isShared_1016_ == 0)
{
lean_ctor_set(v___x_1015_, 4, v___f_1022_);
lean_ctor_set(v___x_1015_, 3, v___f_1023_);
lean_ctor_set(v___x_1015_, 2, v___f_1024_);
lean_ctor_set(v___x_1015_, 1, v___f_1017_);
lean_ctor_set(v___x_1015_, 0, v___x_1021_);
v___x_1026_ = v___x_1015_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v___x_1021_);
lean_ctor_set(v_reuseFailAlloc_1034_, 1, v___f_1017_);
lean_ctor_set(v_reuseFailAlloc_1034_, 2, v___f_1024_);
lean_ctor_set(v_reuseFailAlloc_1034_, 3, v___f_1023_);
lean_ctor_set(v_reuseFailAlloc_1034_, 4, v___f_1022_);
v___x_1026_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
lean_object* v___x_1028_; 
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 1, v___f_1018_);
lean_ctor_set(v___x_1008_, 0, v___x_1026_);
v___x_1028_ = v___x_1008_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v___x_1026_);
lean_ctor_set(v_reuseFailAlloc_1033_, 1, v___f_1018_);
v___x_1028_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_23673__overap_1031_; lean_object* v___x_1032_; 
v___x_1029_ = lean_obj_once(&l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__5, &l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__5_once, _init_l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__5);
v___x_1030_ = l_instInhabitedOfMonad___redArg(v___x_1028_, v___x_1029_);
v___x_23673__overap_1031_ = lean_panic_fn_borrowed(v___x_1030_, v_msg_974_);
lean_dec(v___x_1030_);
lean_inc(v___y_978_);
lean_inc_ref(v___y_977_);
lean_inc(v___y_976_);
lean_inc_ref(v___y_975_);
v___x_1032_ = lean_apply_5(v___x_23673__overap_1031_, v___y_975_, v___y_976_, v___y_977_, v___y_978_, lean_box(0));
return v___x_1032_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___boxed(lean_object* v_msg_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_){
_start:
{
lean_object* v_res_1051_; 
v_res_1051_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg(v_msg_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_);
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
lean_dec(v___y_1047_);
lean_dec_ref(v___y_1046_);
return v_res_1051_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__13(lean_object* v_xs_1052_, size_t v_sz_1053_, size_t v_i_1054_, lean_object* v_bs_1055_){
_start:
{
uint8_t v___x_1056_; 
v___x_1056_ = lean_usize_dec_lt(v_i_1054_, v_sz_1053_);
if (v___x_1056_ == 0)
{
return v_bs_1055_;
}
else
{
lean_object* v___x_1057_; lean_object* v_v_1058_; lean_object* v___x_1059_; lean_object* v_bs_x27_1060_; lean_object* v___x_1061_; size_t v___x_1062_; size_t v___x_1063_; lean_object* v___x_1064_; 
v___x_1057_ = l_Lean_instInhabitedExpr;
v_v_1058_ = lean_array_uget(v_bs_1055_, v_i_1054_);
v___x_1059_ = lean_unsigned_to_nat(0u);
v_bs_x27_1060_ = lean_array_uset(v_bs_1055_, v_i_1054_, v___x_1059_);
v___x_1061_ = lean_array_get_borrowed(v___x_1057_, v_xs_1052_, v_v_1058_);
lean_dec(v_v_1058_);
v___x_1062_ = ((size_t)1ULL);
v___x_1063_ = lean_usize_add(v_i_1054_, v___x_1062_);
lean_inc(v___x_1061_);
v___x_1064_ = lean_array_uset(v_bs_x27_1060_, v_i_1054_, v___x_1061_);
v_i_1054_ = v___x_1063_;
v_bs_1055_ = v___x_1064_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__13___boxed(lean_object* v_xs_1066_, lean_object* v_sz_1067_, lean_object* v_i_1068_, lean_object* v_bs_1069_){
_start:
{
size_t v_sz_boxed_1070_; size_t v_i_boxed_1071_; lean_object* v_res_1072_; 
v_sz_boxed_1070_ = lean_unbox_usize(v_sz_1067_);
lean_dec(v_sz_1067_);
v_i_boxed_1071_ = lean_unbox_usize(v_i_1068_);
lean_dec(v_i_1068_);
v_res_1072_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__13(v_xs_1066_, v_sz_boxed_1070_, v_i_boxed_1071_, v_bs_1069_);
lean_dec_ref(v_xs_1066_);
return v_res_1072_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15___redArg(lean_object* v_xs_1073_, lean_object* v_f_1074_, lean_object* v_as_1075_, lean_object* v_bs_1076_, lean_object* v_i_1077_, lean_object* v_cs_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_){
_start:
{
lean_object* v___x_1084_; uint8_t v___x_1085_; 
v___x_1084_ = lean_array_get_size(v_as_1075_);
v___x_1085_ = lean_nat_dec_lt(v_i_1077_, v___x_1084_);
if (v___x_1085_ == 0)
{
lean_object* v___x_1086_; 
lean_dec(v_i_1077_);
lean_dec_ref(v_f_1074_);
v___x_1086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1086_, 0, v_cs_1078_);
return v___x_1086_;
}
else
{
lean_object* v___x_1087_; uint8_t v___x_1088_; 
v___x_1087_ = lean_array_get_size(v_bs_1076_);
v___x_1088_ = lean_nat_dec_lt(v_i_1077_, v___x_1087_);
if (v___x_1088_ == 0)
{
lean_object* v___x_1089_; 
lean_dec(v_i_1077_);
lean_dec_ref(v_f_1074_);
v___x_1089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1089_, 0, v_cs_1078_);
return v___x_1089_;
}
else
{
lean_object* v_a_1090_; lean_object* v_b_1091_; size_t v_sz_1092_; size_t v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; 
v_a_1090_ = lean_array_fget_borrowed(v_as_1075_, v_i_1077_);
v_b_1091_ = lean_array_fget_borrowed(v_bs_1076_, v_i_1077_);
v_sz_1092_ = lean_array_size(v_b_1091_);
v___x_1093_ = ((size_t)0ULL);
lean_inc(v_b_1091_);
v___x_1094_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__13(v_xs_1073_, v_sz_1092_, v___x_1093_, v_b_1091_);
lean_inc_ref(v_f_1074_);
lean_inc(v___y_1082_);
lean_inc_ref(v___y_1081_);
lean_inc(v___y_1080_);
lean_inc_ref(v___y_1079_);
lean_inc(v_a_1090_);
v___x_1095_ = lean_apply_7(v_f_1074_, v_a_1090_, v___x_1094_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_, lean_box(0));
if (lean_obj_tag(v___x_1095_) == 0)
{
lean_object* v_a_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; 
v_a_1096_ = lean_ctor_get(v___x_1095_, 0);
lean_inc(v_a_1096_);
lean_dec_ref_known(v___x_1095_, 1);
v___x_1097_ = lean_unsigned_to_nat(1u);
v___x_1098_ = lean_nat_add(v_i_1077_, v___x_1097_);
lean_dec(v_i_1077_);
v___x_1099_ = lean_array_push(v_cs_1078_, v_a_1096_);
v_i_1077_ = v___x_1098_;
v_cs_1078_ = v___x_1099_;
goto _start;
}
else
{
lean_object* v_a_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1108_; 
lean_dec_ref(v_cs_1078_);
lean_dec(v_i_1077_);
lean_dec_ref(v_f_1074_);
v_a_1101_ = lean_ctor_get(v___x_1095_, 0);
v_isSharedCheck_1108_ = !lean_is_exclusive(v___x_1095_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_1103_ = v___x_1095_;
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_a_1101_);
lean_dec(v___x_1095_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v___x_1106_; 
if (v_isShared_1104_ == 0)
{
v___x_1106_ = v___x_1103_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v_a_1101_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
return v___x_1106_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15___redArg___boxed(lean_object* v_xs_1109_, lean_object* v_f_1110_, lean_object* v_as_1111_, lean_object* v_bs_1112_, lean_object* v_i_1113_, lean_object* v_cs_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_){
_start:
{
lean_object* v_res_1120_; 
v_res_1120_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15___redArg(v_xs_1109_, v_f_1110_, v_as_1111_, v_bs_1112_, v_i_1113_, v_cs_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_);
lean_dec(v___y_1118_);
lean_dec_ref(v___y_1117_);
lean_dec(v___y_1116_);
lean_dec_ref(v___y_1115_);
lean_dec_ref(v_bs_1112_);
lean_dec_ref(v_as_1111_);
lean_dec_ref(v_xs_1109_);
return v_res_1120_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; 
v___x_1124_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__2));
v___x_1125_ = lean_unsigned_to_nat(2u);
v___x_1126_ = lean_unsigned_to_nat(73u);
v___x_1127_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__1));
v___x_1128_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__0));
v___x_1129_ = l_mkPanicMessageWithDecl(v___x_1128_, v___x_1127_, v___x_1126_, v___x_1125_, v___x_1124_);
return v___x_1129_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1131_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__4));
v___x_1132_ = lean_unsigned_to_nat(2u);
v___x_1133_ = lean_unsigned_to_nat(74u);
v___x_1134_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__1));
v___x_1135_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__0));
v___x_1136_ = l_mkPanicMessageWithDecl(v___x_1135_, v___x_1134_, v___x_1133_, v___x_1132_, v___x_1131_);
return v___x_1136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg(lean_object* v_f_1139_, lean_object* v_positions_1140_, lean_object* v_ys_1141_, lean_object* v_xs_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_){
_start:
{
lean_object* v___x_1148_; lean_object* v___x_1149_; uint8_t v___x_1150_; 
v___x_1148_ = lean_array_get_size(v_positions_1140_);
v___x_1149_ = lean_array_get_size(v_ys_1141_);
v___x_1150_ = lean_nat_dec_eq(v___x_1148_, v___x_1149_);
if (v___x_1150_ == 0)
{
lean_object* v___x_1151_; lean_object* v___x_1152_; 
lean_dec_ref(v_f_1139_);
v___x_1151_ = lean_obj_once(&l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__3, &l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__3_once, _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__3);
v___x_1152_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg(v___x_1151_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_);
return v___x_1152_;
}
else
{
lean_object* v___x_1153_; lean_object* v___x_1154_; uint8_t v___x_1155_; 
v___x_1153_ = l_Lean_Elab_Structural_Positions_numIndices(v_positions_1140_);
v___x_1154_ = lean_array_get_size(v_xs_1142_);
v___x_1155_ = lean_nat_dec_eq(v___x_1153_, v___x_1154_);
lean_dec(v___x_1153_);
if (v___x_1155_ == 0)
{
lean_object* v___x_1156_; lean_object* v___x_1157_; 
lean_dec_ref(v_f_1139_);
v___x_1156_ = lean_obj_once(&l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__5, &l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__5_once, _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__5);
v___x_1157_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg(v___x_1156_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_);
return v___x_1157_;
}
else
{
lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; 
v___x_1158_ = lean_unsigned_to_nat(0u);
v___x_1159_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__6));
v___x_1160_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15___redArg(v_xs_1142_, v_f_1139_, v_ys_1141_, v_positions_1140_, v___x_1158_, v___x_1159_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_);
return v___x_1160_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___boxed(lean_object* v_f_1161_, lean_object* v_positions_1162_, lean_object* v_ys_1163_, lean_object* v_xs_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_){
_start:
{
lean_object* v_res_1170_; 
v_res_1170_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg(v_f_1161_, v_positions_1162_, v_ys_1163_, v_xs_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_);
lean_dec(v___y_1168_);
lean_dec_ref(v___y_1167_);
lean_dec(v___y_1166_);
lean_dec_ref(v___y_1165_);
lean_dec_ref(v_xs_1164_);
lean_dec_ref(v_ys_1163_);
lean_dec_ref(v_positions_1162_);
return v_res_1170_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg(lean_object* v___x_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_funTypes_1174_, size_t v_sz_1175_, size_t v_i_1176_, lean_object* v_bs_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_){
_start:
{
uint8_t v___x_1183_; 
v___x_1183_ = lean_usize_dec_lt(v_i_1176_, v_sz_1175_);
if (v___x_1183_ == 0)
{
lean_object* v___x_1184_; 
lean_dec_ref(v_funTypes_1174_);
lean_dec_ref(v_a_1173_);
lean_dec_ref(v_a_1172_);
lean_dec_ref(v___x_1171_);
v___x_1184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1184_, 0, v_bs_1177_);
return v___x_1184_;
}
else
{
lean_object* v_v_1185_; lean_object* v_fst_1186_; lean_object* v_snd_1187_; lean_object* v___x_1188_; lean_object* v_bs_x27_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; 
v_v_1185_ = lean_array_uget_borrowed(v_bs_1177_, v_i_1176_);
v_fst_1186_ = lean_ctor_get(v_v_1185_, 0);
lean_inc(v_fst_1186_);
v_snd_1187_ = lean_ctor_get(v_v_1185_, 1);
lean_inc(v_snd_1187_);
v___x_1188_ = lean_unsigned_to_nat(0u);
v_bs_x27_1189_ = lean_array_uset(v_bs_1177_, v_i_1176_, v___x_1188_);
v___x_1190_ = lean_usize_to_nat(v_i_1176_);
lean_inc_ref(v_funTypes_1174_);
lean_inc_ref(v_a_1173_);
lean_inc_ref(v_a_1172_);
lean_inc_ref(v___x_1171_);
v___x_1191_ = l_Lean_Elab_Structural_mkBRecOnApp(v___x_1171_, v___x_1190_, v_a_1172_, v_a_1173_, v_funTypes_1174_, v_fst_1186_, v_snd_1187_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_);
if (lean_obj_tag(v___x_1191_) == 0)
{
lean_object* v_a_1192_; size_t v___x_1193_; size_t v___x_1194_; lean_object* v___x_1195_; 
v_a_1192_ = lean_ctor_get(v___x_1191_, 0);
lean_inc(v_a_1192_);
lean_dec_ref_known(v___x_1191_, 1);
v___x_1193_ = ((size_t)1ULL);
v___x_1194_ = lean_usize_add(v_i_1176_, v___x_1193_);
v___x_1195_ = lean_array_uset(v_bs_x27_1189_, v_i_1176_, v_a_1192_);
v_i_1176_ = v___x_1194_;
v_bs_1177_ = v___x_1195_;
goto _start;
}
else
{
lean_object* v_a_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1204_; 
lean_dec_ref(v_bs_x27_1189_);
lean_dec_ref(v_funTypes_1174_);
lean_dec_ref(v_a_1173_);
lean_dec_ref(v_a_1172_);
lean_dec_ref(v___x_1171_);
v_a_1197_ = lean_ctor_get(v___x_1191_, 0);
v_isSharedCheck_1204_ = !lean_is_exclusive(v___x_1191_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1199_ = v___x_1191_;
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_a_1197_);
lean_dec(v___x_1191_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v___x_1202_; 
if (v_isShared_1200_ == 0)
{
v___x_1202_ = v___x_1199_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_a_1197_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
return v___x_1202_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg___boxed(lean_object* v___x_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_, lean_object* v_funTypes_1208_, lean_object* v_sz_1209_, lean_object* v_i_1210_, lean_object* v_bs_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_){
_start:
{
size_t v_sz_boxed_1217_; size_t v_i_boxed_1218_; lean_object* v_res_1219_; 
v_sz_boxed_1217_ = lean_unbox_usize(v_sz_1209_);
lean_dec(v_sz_1209_);
v_i_boxed_1218_ = lean_unbox_usize(v_i_1210_);
lean_dec(v_i_1210_);
v_res_1219_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg(v___x_1205_, v_a_1206_, v_a_1207_, v_funTypes_1208_, v_sz_boxed_1217_, v_i_boxed_1218_, v_bs_1211_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_);
lean_dec(v___y_1215_);
lean_dec_ref(v___y_1214_);
lean_dec(v___y_1213_);
lean_dec_ref(v___y_1212_);
return v_res_1219_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__2(void){
_start:
{
lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; 
v___x_1223_ = lean_box(0);
v___x_1224_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__1));
v___x_1225_ = l_Lean_Expr_const___override(v___x_1224_, v___x_1223_);
return v___x_1225_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__4(void){
_start:
{
lean_object* v___x_1227_; lean_object* v___x_1228_; 
v___x_1227_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__3));
v___x_1228_ = l_Lean_stringToMessageData(v___x_1227_);
return v___x_1228_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__6(void){
_start:
{
lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___x_1230_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__5));
v___x_1231_ = l_Lean_stringToMessageData(v___x_1230_);
return v___x_1231_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__8(void){
_start:
{
lean_object* v___x_1233_; lean_object* v___x_1234_; 
v___x_1233_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__7));
v___x_1234_ = l_Lean_stringToMessageData(v___x_1233_);
return v___x_1234_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__10(void){
_start:
{
lean_object* v___x_1236_; lean_object* v___x_1237_; 
v___x_1236_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__9));
v___x_1237_ = l_Lean_stringToMessageData(v___x_1236_);
return v___x_1237_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__12(void){
_start:
{
lean_object* v___x_1239_; lean_object* v___x_1240_; 
v___x_1239_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__11));
v___x_1240_ = l_Lean_stringToMessageData(v___x_1239_);
return v___x_1240_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2(lean_object* v___f_1241_, lean_object* v_recArgInfos_1242_, lean_object* v_a_1243_, lean_object* v___x_1244_, size_t v___x_1245_, lean_object* v_fixedParamPerms_1246_, lean_object* v_xs_1247_, lean_object* v___x_1248_, lean_object* v_preDefs_1249_, lean_object* v_numIndices_1250_, lean_object* v___f_1251_, lean_object* v___x_1252_, uint8_t v_a_1253_, lean_object* v_funTypes_1254_, lean_object* v_motives_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_){
_start:
{
lean_object* v___y_1262_; lean_object* v___y_1263_; lean_object* v___y_1264_; lean_object* v___y_1265_; lean_object* v___y_1266_; lean_object* v___y_1267_; lean_object* v___y_1302_; lean_object* v_FArgs_1303_; lean_object* v___y_1304_; lean_object* v___y_1305_; lean_object* v___y_1306_; lean_object* v___y_1307_; lean_object* v___y_1358_; lean_object* v___y_1359_; lean_object* v___y_1360_; lean_object* v___y_1361_; lean_object* v___y_1362_; lean_object* v___y_1363_; lean_object* v___y_1381_; lean_object* v___y_1382_; lean_object* v___y_1383_; lean_object* v___y_1384_; lean_object* v___y_1385_; lean_object* v___y_1386_; lean_object* v___y_1425_; lean_object* v___y_1426_; lean_object* v___y_1427_; lean_object* v___y_1428_; lean_object* v___x_1475_; 
lean_inc_ref(v___f_1241_);
lean_inc(v___y_1259_);
lean_inc_ref(v___y_1258_);
lean_inc(v___y_1257_);
lean_inc_ref(v___y_1256_);
v___x_1475_ = lean_apply_5(v___f_1241_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_, lean_box(0));
if (lean_obj_tag(v___x_1475_) == 0)
{
lean_object* v_a_1476_; uint8_t v___x_1477_; 
v_a_1476_ = lean_ctor_get(v___x_1475_, 0);
lean_inc(v_a_1476_);
lean_dec_ref_known(v___x_1475_, 1);
v___x_1477_ = lean_unbox(v_a_1476_);
lean_dec(v_a_1476_);
if (v___x_1477_ == 0)
{
v___y_1425_ = v___y_1256_;
v___y_1426_ = v___y_1257_;
v___y_1427_ = v___y_1258_;
v___y_1428_ = v___y_1259_;
goto v___jp_1424_;
}
else
{
lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; 
v___x_1478_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__10, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__10);
lean_inc_ref(v_funTypes_1254_);
v___x_1479_ = lean_array_to_list(v_funTypes_1254_);
v___x_1480_ = lean_box(0);
v___x_1481_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_1479_, v___x_1480_);
v___x_1482_ = l_Lean_MessageData_ofList(v___x_1481_);
v___x_1483_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1483_, 0, v___x_1478_);
lean_ctor_set(v___x_1483_, 1, v___x_1482_);
v___x_1484_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__12, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__12_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__12);
v___x_1485_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1485_, 0, v___x_1483_);
lean_ctor_set(v___x_1485_, 1, v___x_1484_);
lean_inc_ref(v_motives_1255_);
v___x_1486_ = lean_array_to_list(v_motives_1255_);
v___x_1487_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_1486_, v___x_1480_);
v___x_1488_ = l_Lean_MessageData_ofList(v___x_1487_);
v___x_1489_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1489_, 0, v___x_1485_);
lean_ctor_set(v___x_1489_, 1, v___x_1488_);
lean_inc(v___x_1252_);
v___x_1490_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_1252_, v___x_1489_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_);
if (lean_obj_tag(v___x_1490_) == 0)
{
lean_dec_ref_known(v___x_1490_, 1);
v___y_1425_ = v___y_1256_;
v___y_1426_ = v___y_1257_;
v___y_1427_ = v___y_1258_;
v___y_1428_ = v___y_1259_;
goto v___jp_1424_;
}
else
{
lean_object* v_a_1491_; lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1498_; 
lean_dec_ref(v_motives_1255_);
lean_dec_ref(v_funTypes_1254_);
lean_dec(v___x_1252_);
lean_dec_ref(v___f_1251_);
lean_dec_ref(v_preDefs_1249_);
lean_dec(v___x_1248_);
lean_dec_ref(v_xs_1247_);
lean_dec_ref(v_fixedParamPerms_1246_);
lean_dec_ref(v___x_1244_);
lean_dec_ref(v_recArgInfos_1242_);
lean_dec_ref(v___f_1241_);
v_a_1491_ = lean_ctor_get(v___x_1490_, 0);
v_isSharedCheck_1498_ = !lean_is_exclusive(v___x_1490_);
if (v_isSharedCheck_1498_ == 0)
{
v___x_1493_ = v___x_1490_;
v_isShared_1494_ = v_isSharedCheck_1498_;
goto v_resetjp_1492_;
}
else
{
lean_inc(v_a_1491_);
lean_dec(v___x_1490_);
v___x_1493_ = lean_box(0);
v_isShared_1494_ = v_isSharedCheck_1498_;
goto v_resetjp_1492_;
}
v_resetjp_1492_:
{
lean_object* v___x_1496_; 
if (v_isShared_1494_ == 0)
{
v___x_1496_ = v___x_1493_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v_a_1491_);
v___x_1496_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
return v___x_1496_;
}
}
}
}
}
else
{
lean_object* v_a_1499_; lean_object* v___x_1501_; uint8_t v_isShared_1502_; uint8_t v_isSharedCheck_1506_; 
lean_dec_ref(v_motives_1255_);
lean_dec_ref(v_funTypes_1254_);
lean_dec(v___x_1252_);
lean_dec_ref(v___f_1251_);
lean_dec_ref(v_preDefs_1249_);
lean_dec(v___x_1248_);
lean_dec_ref(v_xs_1247_);
lean_dec_ref(v_fixedParamPerms_1246_);
lean_dec_ref(v___x_1244_);
lean_dec_ref(v_recArgInfos_1242_);
lean_dec_ref(v___f_1241_);
v_a_1499_ = lean_ctor_get(v___x_1475_, 0);
v_isSharedCheck_1506_ = !lean_is_exclusive(v___x_1475_);
if (v_isSharedCheck_1506_ == 0)
{
v___x_1501_ = v___x_1475_;
v_isShared_1502_ = v_isSharedCheck_1506_;
goto v_resetjp_1500_;
}
else
{
lean_inc(v_a_1499_);
lean_dec(v___x_1475_);
v___x_1501_ = lean_box(0);
v_isShared_1502_ = v_isSharedCheck_1506_;
goto v_resetjp_1500_;
}
v_resetjp_1500_:
{
lean_object* v___x_1504_; 
if (v_isShared_1502_ == 0)
{
v___x_1504_ = v___x_1501_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v_a_1499_);
v___x_1504_ = v_reuseFailAlloc_1505_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
return v___x_1504_;
}
}
}
v___jp_1261_:
{
lean_object* v___x_1268_; size_t v_sz_1269_; lean_object* v___x_1270_; 
v___x_1268_ = l_Array_zip___redArg(v_recArgInfos_1242_, v_a_1243_);
lean_dec_ref(v_recArgInfos_1242_);
v_sz_1269_ = lean_array_size(v___x_1268_);
v___x_1270_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg(v___x_1244_, v___y_1262_, v___y_1263_, v_funTypes_1254_, v_sz_1269_, v___x_1245_, v___x_1268_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_);
if (lean_obj_tag(v___x_1270_) == 0)
{
lean_object* v_a_1271_; lean_object* v___x_1272_; size_t v_sz_1273_; lean_object* v___x_1274_; 
v_a_1271_ = lean_ctor_get(v___x_1270_, 0);
lean_inc(v_a_1271_);
lean_dec_ref_known(v___x_1270_, 1);
v___x_1272_ = l_Array_zip___redArg(v_a_1243_, v_a_1271_);
lean_dec(v_a_1271_);
v_sz_1273_ = lean_array_size(v___x_1272_);
v___x_1274_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg(v_fixedParamPerms_1246_, v_xs_1247_, v_sz_1273_, v___x_1245_, v___x_1272_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_);
if (lean_obj_tag(v___x_1274_) == 0)
{
lean_object* v_a_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1284_; 
v_a_1275_ = lean_ctor_get(v___x_1274_, 0);
v_isSharedCheck_1284_ = !lean_is_exclusive(v___x_1274_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1277_ = v___x_1274_;
v_isShared_1278_ = v_isSharedCheck_1284_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_a_1275_);
lean_dec(v___x_1274_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1284_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1282_; 
v___x_1279_ = lean_mk_empty_array_with_capacity(v___x_1248_);
v___x_1280_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9(v_preDefs_1249_, v_a_1275_, v___x_1248_, v___x_1279_);
lean_dec(v_a_1275_);
lean_dec_ref(v_preDefs_1249_);
if (v_isShared_1278_ == 0)
{
lean_ctor_set(v___x_1277_, 0, v___x_1280_);
v___x_1282_ = v___x_1277_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v___x_1280_);
v___x_1282_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
return v___x_1282_;
}
}
}
else
{
lean_object* v_a_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1292_; 
lean_dec_ref(v_preDefs_1249_);
lean_dec(v___x_1248_);
v_a_1285_ = lean_ctor_get(v___x_1274_, 0);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1274_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1287_ = v___x_1274_;
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_a_1285_);
lean_dec(v___x_1274_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v___x_1290_; 
if (v_isShared_1288_ == 0)
{
v___x_1290_ = v___x_1287_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_a_1285_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
}
}
else
{
lean_object* v_a_1293_; lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1300_; 
lean_dec_ref(v_preDefs_1249_);
lean_dec(v___x_1248_);
lean_dec_ref(v_xs_1247_);
lean_dec_ref(v_fixedParamPerms_1246_);
v_a_1293_ = lean_ctor_get(v___x_1270_, 0);
v_isSharedCheck_1300_ = !lean_is_exclusive(v___x_1270_);
if (v_isSharedCheck_1300_ == 0)
{
v___x_1295_ = v___x_1270_;
v_isShared_1296_ = v_isSharedCheck_1300_;
goto v_resetjp_1294_;
}
else
{
lean_inc(v_a_1293_);
lean_dec(v___x_1270_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1300_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
lean_object* v___x_1298_; 
if (v_isShared_1296_ == 0)
{
v___x_1298_ = v___x_1295_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v_a_1293_);
v___x_1298_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
return v___x_1298_;
}
}
}
}
v___jp_1301_:
{
lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; 
lean_inc_ref(v___y_1302_);
lean_inc(v___x_1248_);
v___x_1308_ = lean_apply_1(v___y_1302_, v___x_1248_);
v___x_1309_ = lean_unsigned_to_nat(1u);
v___x_1310_ = lean_nat_add(v_numIndices_1250_, v___x_1309_);
v___x_1311_ = lean_box(0);
v___x_1312_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__2);
v___x_1313_ = lean_mk_array(v___x_1310_, v___x_1312_);
v___x_1314_ = l_Lean_mkAppN(v___x_1308_, v___x_1313_);
lean_dec_ref(v___x_1313_);
v___x_1315_ = lean_array_get_size(v___x_1244_);
v___x_1316_ = l_Lean_Meta_inferArgumentTypesN(v___x_1315_, v___x_1314_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_);
if (lean_obj_tag(v___x_1316_) == 0)
{
lean_object* v_a_1317_; lean_object* v___x_1318_; 
v_a_1317_ = lean_ctor_get(v___x_1316_, 0);
lean_inc(v_a_1317_);
lean_dec_ref_known(v___x_1316_, 1);
v___x_1318_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg(v___f_1251_, v___x_1244_, v_a_1317_, v_FArgs_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_);
lean_dec_ref(v_FArgs_1303_);
lean_dec(v_a_1317_);
if (lean_obj_tag(v___x_1318_) == 0)
{
lean_object* v_options_1319_; uint8_t v_hasTrace_1320_; 
v_options_1319_ = lean_ctor_get(v___y_1306_, 2);
v_hasTrace_1320_ = lean_ctor_get_uint8(v_options_1319_, sizeof(void*)*1);
if (v_hasTrace_1320_ == 0)
{
lean_object* v_a_1321_; 
lean_dec(v___x_1252_);
v_a_1321_ = lean_ctor_get(v___x_1318_, 0);
lean_inc(v_a_1321_);
lean_dec_ref_known(v___x_1318_, 1);
v___y_1262_ = v___y_1302_;
v___y_1263_ = v_a_1321_;
v___y_1264_ = v___y_1304_;
v___y_1265_ = v___y_1305_;
v___y_1266_ = v___y_1306_;
v___y_1267_ = v___y_1307_;
goto v___jp_1261_;
}
else
{
lean_object* v_a_1322_; lean_object* v_inheritedTraceOptions_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; uint8_t v___x_1326_; 
v_a_1322_ = lean_ctor_get(v___x_1318_, 0);
lean_inc(v_a_1322_);
lean_dec_ref_known(v___x_1318_, 1);
v_inheritedTraceOptions_1323_ = lean_ctor_get(v___y_1306_, 13);
v___x_1324_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0___closed__1));
lean_inc(v___x_1252_);
v___x_1325_ = l_Lean_Name_append(v___x_1324_, v___x_1252_);
v___x_1326_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1323_, v_options_1319_, v___x_1325_);
lean_dec(v___x_1325_);
if (v___x_1326_ == 0)
{
lean_dec(v___x_1252_);
v___y_1262_ = v___y_1302_;
v___y_1263_ = v_a_1322_;
v___y_1264_ = v___y_1304_;
v___y_1265_ = v___y_1305_;
v___y_1266_ = v___y_1306_;
v___y_1267_ = v___y_1307_;
goto v___jp_1261_;
}
else
{
lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; 
v___x_1327_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__4);
lean_inc(v_a_1322_);
v___x_1328_ = lean_array_to_list(v_a_1322_);
v___x_1329_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_1328_, v___x_1311_);
v___x_1330_ = l_Lean_MessageData_ofList(v___x_1329_);
v___x_1331_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1331_, 0, v___x_1327_);
lean_ctor_set(v___x_1331_, 1, v___x_1330_);
v___x_1332_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_1252_, v___x_1331_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_);
if (lean_obj_tag(v___x_1332_) == 0)
{
lean_dec_ref_known(v___x_1332_, 1);
v___y_1262_ = v___y_1302_;
v___y_1263_ = v_a_1322_;
v___y_1264_ = v___y_1304_;
v___y_1265_ = v___y_1305_;
v___y_1266_ = v___y_1306_;
v___y_1267_ = v___y_1307_;
goto v___jp_1261_;
}
else
{
lean_object* v_a_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1340_; 
lean_dec(v_a_1322_);
lean_dec_ref(v___y_1302_);
lean_dec_ref(v_funTypes_1254_);
lean_dec_ref(v_preDefs_1249_);
lean_dec(v___x_1248_);
lean_dec_ref(v_xs_1247_);
lean_dec_ref(v_fixedParamPerms_1246_);
lean_dec_ref(v___x_1244_);
lean_dec_ref(v_recArgInfos_1242_);
v_a_1333_ = lean_ctor_get(v___x_1332_, 0);
v_isSharedCheck_1340_ = !lean_is_exclusive(v___x_1332_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1335_ = v___x_1332_;
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_a_1333_);
lean_dec(v___x_1332_);
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
else
{
lean_object* v_a_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1348_; 
lean_dec_ref(v___y_1302_);
lean_dec_ref(v_funTypes_1254_);
lean_dec(v___x_1252_);
lean_dec_ref(v_preDefs_1249_);
lean_dec(v___x_1248_);
lean_dec_ref(v_xs_1247_);
lean_dec_ref(v_fixedParamPerms_1246_);
lean_dec_ref(v___x_1244_);
lean_dec_ref(v_recArgInfos_1242_);
v_a_1341_ = lean_ctor_get(v___x_1318_, 0);
v_isSharedCheck_1348_ = !lean_is_exclusive(v___x_1318_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1343_ = v___x_1318_;
v_isShared_1344_ = v_isSharedCheck_1348_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_a_1341_);
lean_dec(v___x_1318_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1348_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
lean_object* v___x_1346_; 
if (v_isShared_1344_ == 0)
{
v___x_1346_ = v___x_1343_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v_a_1341_);
v___x_1346_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
return v___x_1346_;
}
}
}
}
else
{
lean_object* v_a_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1356_; 
lean_dec_ref(v_FArgs_1303_);
lean_dec_ref(v___y_1302_);
lean_dec_ref(v_funTypes_1254_);
lean_dec(v___x_1252_);
lean_dec_ref(v___f_1251_);
lean_dec_ref(v_preDefs_1249_);
lean_dec(v___x_1248_);
lean_dec_ref(v_xs_1247_);
lean_dec_ref(v_fixedParamPerms_1246_);
lean_dec_ref(v___x_1244_);
lean_dec_ref(v_recArgInfos_1242_);
v_a_1349_ = lean_ctor_get(v___x_1316_, 0);
v_isSharedCheck_1356_ = !lean_is_exclusive(v___x_1316_);
if (v_isSharedCheck_1356_ == 0)
{
v___x_1351_ = v___x_1316_;
v_isShared_1352_ = v_isSharedCheck_1356_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_a_1349_);
lean_dec(v___x_1316_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1356_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
lean_object* v___x_1354_; 
if (v_isShared_1352_ == 0)
{
v___x_1354_ = v___x_1351_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v_a_1349_);
v___x_1354_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
return v___x_1354_;
}
}
}
}
v___jp_1357_:
{
if (v_a_1253_ == 0)
{
lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v_levelParams_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; size_t v_sz_1369_; lean_object* v___x_1370_; 
v___x_1364_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_1365_ = lean_array_get_borrowed(v___x_1364_, v_preDefs_1249_, v___x_1248_);
v_levelParams_1366_ = lean_ctor_get(v___x_1365_, 1);
v___x_1367_ = lean_box(0);
lean_inc(v_levelParams_1366_);
v___x_1368_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__15(v_levelParams_1366_, v___x_1367_);
v_sz_1369_ = lean_array_size(v___y_1359_);
v___x_1370_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg(v_xs_1247_, v_a_1253_, v_preDefs_1249_, v___x_1368_, v_sz_1369_, v___x_1245_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_);
if (lean_obj_tag(v___x_1370_) == 0)
{
lean_object* v_a_1371_; 
v_a_1371_ = lean_ctor_get(v___x_1370_, 0);
lean_inc(v_a_1371_);
lean_dec_ref_known(v___x_1370_, 1);
v___y_1302_ = v___y_1358_;
v_FArgs_1303_ = v_a_1371_;
v___y_1304_ = v___y_1360_;
v___y_1305_ = v___y_1361_;
v___y_1306_ = v___y_1362_;
v___y_1307_ = v___y_1363_;
goto v___jp_1301_;
}
else
{
lean_object* v_a_1372_; lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1379_; 
lean_dec_ref(v___y_1358_);
lean_dec_ref(v_funTypes_1254_);
lean_dec(v___x_1252_);
lean_dec_ref(v___f_1251_);
lean_dec_ref(v_preDefs_1249_);
lean_dec(v___x_1248_);
lean_dec_ref(v_xs_1247_);
lean_dec_ref(v_fixedParamPerms_1246_);
lean_dec_ref(v___x_1244_);
lean_dec_ref(v_recArgInfos_1242_);
v_a_1372_ = lean_ctor_get(v___x_1370_, 0);
v_isSharedCheck_1379_ = !lean_is_exclusive(v___x_1370_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1374_ = v___x_1370_;
v_isShared_1375_ = v_isSharedCheck_1379_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_a_1372_);
lean_dec(v___x_1370_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1379_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v___x_1377_; 
if (v_isShared_1375_ == 0)
{
v___x_1377_ = v___x_1374_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v_a_1372_);
v___x_1377_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
return v___x_1377_;
}
}
}
}
else
{
v___y_1302_ = v___y_1358_;
v_FArgs_1303_ = v___y_1359_;
v___y_1304_ = v___y_1360_;
v___y_1305_ = v___y_1361_;
v___y_1306_ = v___y_1362_;
v___y_1307_ = v___y_1363_;
goto v___jp_1301_;
}
}
v___jp_1380_:
{
size_t v_sz_1387_; lean_object* v___x_1388_; 
v_sz_1387_ = lean_array_size(v_recArgInfos_1242_);
lean_inc_ref(v___y_1382_);
lean_inc_ref(v_preDefs_1249_);
lean_inc_ref(v___x_1244_);
lean_inc_ref_n(v_recArgInfos_1242_, 2);
v___x_1388_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg(v_a_1253_, v_a_1243_, v___y_1381_, v_recArgInfos_1242_, v___x_1244_, v_preDefs_1249_, v___y_1382_, v_sz_1387_, v___x_1245_, v_recArgInfos_1242_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_);
lean_dec_ref(v___y_1381_);
if (lean_obj_tag(v___x_1388_) == 0)
{
lean_object* v_a_1389_; lean_object* v___x_1390_; 
v_a_1389_ = lean_ctor_get(v___x_1388_, 0);
lean_inc(v_a_1389_);
lean_dec_ref_known(v___x_1388_, 1);
lean_inc(v___y_1386_);
lean_inc_ref(v___y_1385_);
lean_inc(v___y_1384_);
lean_inc_ref(v___y_1383_);
v___x_1390_ = lean_apply_5(v___f_1241_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_, lean_box(0));
if (lean_obj_tag(v___x_1390_) == 0)
{
lean_object* v_a_1391_; uint8_t v___x_1392_; 
v_a_1391_ = lean_ctor_get(v___x_1390_, 0);
lean_inc(v_a_1391_);
lean_dec_ref_known(v___x_1390_, 1);
v___x_1392_ = lean_unbox(v_a_1391_);
lean_dec(v_a_1391_);
if (v___x_1392_ == 0)
{
v___y_1358_ = v___y_1382_;
v___y_1359_ = v_a_1389_;
v___y_1360_ = v___y_1383_;
v___y_1361_ = v___y_1384_;
v___y_1362_ = v___y_1385_;
v___y_1363_ = v___y_1386_;
goto v___jp_1357_;
}
else
{
lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; 
v___x_1393_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__6, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__6);
lean_inc(v_a_1389_);
v___x_1394_ = lean_array_to_list(v_a_1389_);
v___x_1395_ = lean_box(0);
v___x_1396_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_1394_, v___x_1395_);
v___x_1397_ = l_Lean_MessageData_ofList(v___x_1396_);
v___x_1398_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1398_, 0, v___x_1393_);
lean_ctor_set(v___x_1398_, 1, v___x_1397_);
lean_inc(v___x_1252_);
v___x_1399_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_1252_, v___x_1398_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_);
if (lean_obj_tag(v___x_1399_) == 0)
{
lean_dec_ref_known(v___x_1399_, 1);
v___y_1358_ = v___y_1382_;
v___y_1359_ = v_a_1389_;
v___y_1360_ = v___y_1383_;
v___y_1361_ = v___y_1384_;
v___y_1362_ = v___y_1385_;
v___y_1363_ = v___y_1386_;
goto v___jp_1357_;
}
else
{
lean_object* v_a_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1407_; 
lean_dec(v_a_1389_);
lean_dec_ref(v___y_1382_);
lean_dec_ref(v_funTypes_1254_);
lean_dec(v___x_1252_);
lean_dec_ref(v___f_1251_);
lean_dec_ref(v_preDefs_1249_);
lean_dec(v___x_1248_);
lean_dec_ref(v_xs_1247_);
lean_dec_ref(v_fixedParamPerms_1246_);
lean_dec_ref(v___x_1244_);
lean_dec_ref(v_recArgInfos_1242_);
v_a_1400_ = lean_ctor_get(v___x_1399_, 0);
v_isSharedCheck_1407_ = !lean_is_exclusive(v___x_1399_);
if (v_isSharedCheck_1407_ == 0)
{
v___x_1402_ = v___x_1399_;
v_isShared_1403_ = v_isSharedCheck_1407_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_a_1400_);
lean_dec(v___x_1399_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1407_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v___x_1405_; 
if (v_isShared_1403_ == 0)
{
v___x_1405_ = v___x_1402_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v_a_1400_);
v___x_1405_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
return v___x_1405_;
}
}
}
}
}
else
{
lean_object* v_a_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1415_; 
lean_dec(v_a_1389_);
lean_dec_ref(v___y_1382_);
lean_dec_ref(v_funTypes_1254_);
lean_dec(v___x_1252_);
lean_dec_ref(v___f_1251_);
lean_dec_ref(v_preDefs_1249_);
lean_dec(v___x_1248_);
lean_dec_ref(v_xs_1247_);
lean_dec_ref(v_fixedParamPerms_1246_);
lean_dec_ref(v___x_1244_);
lean_dec_ref(v_recArgInfos_1242_);
v_a_1408_ = lean_ctor_get(v___x_1390_, 0);
v_isSharedCheck_1415_ = !lean_is_exclusive(v___x_1390_);
if (v_isSharedCheck_1415_ == 0)
{
v___x_1410_ = v___x_1390_;
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_a_1408_);
lean_dec(v___x_1390_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v___x_1413_; 
if (v_isShared_1411_ == 0)
{
v___x_1413_ = v___x_1410_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v_a_1408_);
v___x_1413_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
return v___x_1413_;
}
}
}
}
else
{
lean_object* v_a_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1423_; 
lean_dec_ref(v___y_1382_);
lean_dec_ref(v_funTypes_1254_);
lean_dec(v___x_1252_);
lean_dec_ref(v___f_1251_);
lean_dec_ref(v_preDefs_1249_);
lean_dec(v___x_1248_);
lean_dec_ref(v_xs_1247_);
lean_dec_ref(v_fixedParamPerms_1246_);
lean_dec_ref(v___x_1244_);
lean_dec_ref(v_recArgInfos_1242_);
lean_dec_ref(v___f_1241_);
v_a_1416_ = lean_ctor_get(v___x_1388_, 0);
v_isSharedCheck_1423_ = !lean_is_exclusive(v___x_1388_);
if (v_isSharedCheck_1423_ == 0)
{
v___x_1418_ = v___x_1388_;
v_isShared_1419_ = v_isSharedCheck_1423_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_a_1416_);
lean_dec(v___x_1388_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1423_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___x_1421_; 
if (v_isShared_1419_ == 0)
{
v___x_1421_ = v___x_1418_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v_a_1416_);
v___x_1421_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
return v___x_1421_;
}
}
}
}
v___jp_1424_:
{
lean_object* v___x_1429_; 
v___x_1429_ = l_Lean_Elab_Structural_mkBRecOnConst(v_recArgInfos_1242_, v___x_1244_, v_motives_1255_, v_a_1253_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_);
lean_dec_ref(v_motives_1255_);
if (lean_obj_tag(v___x_1429_) == 0)
{
lean_object* v_a_1430_; lean_object* v___x_1431_; 
v_a_1430_ = lean_ctor_get(v___x_1429_, 0);
lean_inc_n(v_a_1430_, 2);
lean_dec_ref_known(v___x_1429_, 1);
lean_inc_ref(v___x_1244_);
v___x_1431_ = l_Lean_Elab_Structural_inferBRecOnFTypes(v_recArgInfos_1242_, v___x_1244_, v_a_1430_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_);
if (lean_obj_tag(v___x_1431_) == 0)
{
lean_object* v_a_1432_; lean_object* v___x_1433_; 
v_a_1432_ = lean_ctor_get(v___x_1431_, 0);
lean_inc(v_a_1432_);
lean_dec_ref_known(v___x_1431_, 1);
lean_inc_ref(v___f_1241_);
lean_inc(v___y_1428_);
lean_inc_ref(v___y_1427_);
lean_inc(v___y_1426_);
lean_inc_ref(v___y_1425_);
v___x_1433_ = lean_apply_5(v___f_1241_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_, lean_box(0));
if (lean_obj_tag(v___x_1433_) == 0)
{
lean_object* v_a_1434_; uint8_t v___x_1435_; 
v_a_1434_ = lean_ctor_get(v___x_1433_, 0);
lean_inc(v_a_1434_);
lean_dec_ref_known(v___x_1433_, 1);
v___x_1435_ = lean_unbox(v_a_1434_);
lean_dec(v_a_1434_);
if (v___x_1435_ == 0)
{
v___y_1381_ = v_a_1432_;
v___y_1382_ = v_a_1430_;
v___y_1383_ = v___y_1425_;
v___y_1384_ = v___y_1426_;
v___y_1385_ = v___y_1427_;
v___y_1386_ = v___y_1428_;
goto v___jp_1380_;
}
else
{
lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; 
v___x_1436_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__8);
lean_inc(v_a_1432_);
v___x_1437_ = lean_array_to_list(v_a_1432_);
v___x_1438_ = lean_box(0);
v___x_1439_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_1437_, v___x_1438_);
v___x_1440_ = l_Lean_MessageData_ofList(v___x_1439_);
v___x_1441_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1441_, 0, v___x_1436_);
lean_ctor_set(v___x_1441_, 1, v___x_1440_);
lean_inc(v___x_1252_);
v___x_1442_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_1252_, v___x_1441_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_);
if (lean_obj_tag(v___x_1442_) == 0)
{
lean_dec_ref_known(v___x_1442_, 1);
v___y_1381_ = v_a_1432_;
v___y_1382_ = v_a_1430_;
v___y_1383_ = v___y_1425_;
v___y_1384_ = v___y_1426_;
v___y_1385_ = v___y_1427_;
v___y_1386_ = v___y_1428_;
goto v___jp_1380_;
}
else
{
lean_object* v_a_1443_; lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1450_; 
lean_dec(v_a_1432_);
lean_dec(v_a_1430_);
lean_dec_ref(v_funTypes_1254_);
lean_dec(v___x_1252_);
lean_dec_ref(v___f_1251_);
lean_dec_ref(v_preDefs_1249_);
lean_dec(v___x_1248_);
lean_dec_ref(v_xs_1247_);
lean_dec_ref(v_fixedParamPerms_1246_);
lean_dec_ref(v___x_1244_);
lean_dec_ref(v_recArgInfos_1242_);
lean_dec_ref(v___f_1241_);
v_a_1443_ = lean_ctor_get(v___x_1442_, 0);
v_isSharedCheck_1450_ = !lean_is_exclusive(v___x_1442_);
if (v_isSharedCheck_1450_ == 0)
{
v___x_1445_ = v___x_1442_;
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
else
{
lean_inc(v_a_1443_);
lean_dec(v___x_1442_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
lean_object* v___x_1448_; 
if (v_isShared_1446_ == 0)
{
v___x_1448_ = v___x_1445_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v_a_1443_);
v___x_1448_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
return v___x_1448_;
}
}
}
}
}
else
{
lean_object* v_a_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1458_; 
lean_dec(v_a_1432_);
lean_dec(v_a_1430_);
lean_dec_ref(v_funTypes_1254_);
lean_dec(v___x_1252_);
lean_dec_ref(v___f_1251_);
lean_dec_ref(v_preDefs_1249_);
lean_dec(v___x_1248_);
lean_dec_ref(v_xs_1247_);
lean_dec_ref(v_fixedParamPerms_1246_);
lean_dec_ref(v___x_1244_);
lean_dec_ref(v_recArgInfos_1242_);
lean_dec_ref(v___f_1241_);
v_a_1451_ = lean_ctor_get(v___x_1433_, 0);
v_isSharedCheck_1458_ = !lean_is_exclusive(v___x_1433_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1453_ = v___x_1433_;
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_a_1451_);
lean_dec(v___x_1433_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v___x_1456_; 
if (v_isShared_1454_ == 0)
{
v___x_1456_ = v___x_1453_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v_a_1451_);
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
lean_object* v_a_1459_; lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1466_; 
lean_dec(v_a_1430_);
lean_dec_ref(v_funTypes_1254_);
lean_dec(v___x_1252_);
lean_dec_ref(v___f_1251_);
lean_dec_ref(v_preDefs_1249_);
lean_dec(v___x_1248_);
lean_dec_ref(v_xs_1247_);
lean_dec_ref(v_fixedParamPerms_1246_);
lean_dec_ref(v___x_1244_);
lean_dec_ref(v_recArgInfos_1242_);
lean_dec_ref(v___f_1241_);
v_a_1459_ = lean_ctor_get(v___x_1431_, 0);
v_isSharedCheck_1466_ = !lean_is_exclusive(v___x_1431_);
if (v_isSharedCheck_1466_ == 0)
{
v___x_1461_ = v___x_1431_;
v_isShared_1462_ = v_isSharedCheck_1466_;
goto v_resetjp_1460_;
}
else
{
lean_inc(v_a_1459_);
lean_dec(v___x_1431_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1466_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
lean_object* v___x_1464_; 
if (v_isShared_1462_ == 0)
{
v___x_1464_ = v___x_1461_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v_a_1459_);
v___x_1464_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
return v___x_1464_;
}
}
}
}
else
{
lean_object* v_a_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1474_; 
lean_dec_ref(v_funTypes_1254_);
lean_dec(v___x_1252_);
lean_dec_ref(v___f_1251_);
lean_dec_ref(v_preDefs_1249_);
lean_dec(v___x_1248_);
lean_dec_ref(v_xs_1247_);
lean_dec_ref(v_fixedParamPerms_1246_);
lean_dec_ref(v___x_1244_);
lean_dec_ref(v_recArgInfos_1242_);
lean_dec_ref(v___f_1241_);
v_a_1467_ = lean_ctor_get(v___x_1429_, 0);
v_isSharedCheck_1474_ = !lean_is_exclusive(v___x_1429_);
if (v_isSharedCheck_1474_ == 0)
{
v___x_1469_ = v___x_1429_;
v_isShared_1470_ = v_isSharedCheck_1474_;
goto v_resetjp_1468_;
}
else
{
lean_inc(v_a_1467_);
lean_dec(v___x_1429_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___boxed(lean_object** _args){
lean_object* v___f_1507_ = _args[0];
lean_object* v_recArgInfos_1508_ = _args[1];
lean_object* v_a_1509_ = _args[2];
lean_object* v___x_1510_ = _args[3];
lean_object* v___x_1511_ = _args[4];
lean_object* v_fixedParamPerms_1512_ = _args[5];
lean_object* v_xs_1513_ = _args[6];
lean_object* v___x_1514_ = _args[7];
lean_object* v_preDefs_1515_ = _args[8];
lean_object* v_numIndices_1516_ = _args[9];
lean_object* v___f_1517_ = _args[10];
lean_object* v___x_1518_ = _args[11];
lean_object* v_a_1519_ = _args[12];
lean_object* v_funTypes_1520_ = _args[13];
lean_object* v_motives_1521_ = _args[14];
lean_object* v___y_1522_ = _args[15];
lean_object* v___y_1523_ = _args[16];
lean_object* v___y_1524_ = _args[17];
lean_object* v___y_1525_ = _args[18];
lean_object* v___y_1526_ = _args[19];
_start:
{
size_t v___x_28625__boxed_1527_; uint8_t v_a_28629__boxed_1528_; lean_object* v_res_1529_; 
v___x_28625__boxed_1527_ = lean_unbox_usize(v___x_1511_);
lean_dec(v___x_1511_);
v_a_28629__boxed_1528_ = lean_unbox(v_a_1519_);
v_res_1529_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2(v___f_1507_, v_recArgInfos_1508_, v_a_1509_, v___x_1510_, v___x_28625__boxed_1527_, v_fixedParamPerms_1512_, v_xs_1513_, v___x_1514_, v_preDefs_1515_, v_numIndices_1516_, v___f_1517_, v___x_1518_, v_a_28629__boxed_1528_, v_funTypes_1520_, v_motives_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_);
lean_dec(v___y_1525_);
lean_dec_ref(v___y_1524_);
lean_dec(v___y_1523_);
lean_dec_ref(v___y_1522_);
lean_dec(v_numIndices_1516_);
lean_dec_ref(v_a_1509_);
return v_res_1529_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___redArg(lean_object* v_a_1530_, lean_object* v_funTypes_1531_, size_t v_sz_1532_, size_t v_i_1533_, lean_object* v_bs_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_){
_start:
{
uint8_t v___x_1540_; 
v___x_1540_ = lean_usize_dec_lt(v_i_1533_, v_sz_1532_);
if (v___x_1540_ == 0)
{
lean_object* v___x_1541_; 
v___x_1541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1541_, 0, v_bs_1534_);
return v___x_1541_;
}
else
{
lean_object* v___x_1542_; lean_object* v_v_1543_; lean_object* v___x_1544_; lean_object* v_bs_x27_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; 
v___x_1542_ = l_Lean_instInhabitedExpr;
v_v_1543_ = lean_array_uget(v_bs_1534_, v_i_1533_);
v___x_1544_ = lean_unsigned_to_nat(0u);
v_bs_x27_1545_ = lean_array_uset(v_bs_1534_, v_i_1533_, v___x_1544_);
v___x_1546_ = lean_usize_to_nat(v_i_1533_);
v___x_1547_ = lean_array_get_borrowed(v___x_1542_, v_a_1530_, v___x_1546_);
v___x_1548_ = lean_array_get_borrowed(v___x_1542_, v_funTypes_1531_, v___x_1546_);
lean_dec(v___x_1546_);
lean_inc(v___x_1548_);
lean_inc(v___x_1547_);
v___x_1549_ = l_Lean_Elab_Structural_mkIndPredBRecOnMotive(v_v_1543_, v___x_1547_, v___x_1548_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
if (lean_obj_tag(v___x_1549_) == 0)
{
lean_object* v_a_1550_; size_t v___x_1551_; size_t v___x_1552_; lean_object* v___x_1553_; 
v_a_1550_ = lean_ctor_get(v___x_1549_, 0);
lean_inc(v_a_1550_);
lean_dec_ref_known(v___x_1549_, 1);
v___x_1551_ = ((size_t)1ULL);
v___x_1552_ = lean_usize_add(v_i_1533_, v___x_1551_);
v___x_1553_ = lean_array_uset(v_bs_x27_1545_, v_i_1533_, v_a_1550_);
v_i_1533_ = v___x_1552_;
v_bs_1534_ = v___x_1553_;
goto _start;
}
else
{
lean_object* v_a_1555_; lean_object* v___x_1557_; uint8_t v_isShared_1558_; uint8_t v_isSharedCheck_1562_; 
lean_dec_ref(v_bs_x27_1545_);
v_a_1555_ = lean_ctor_get(v___x_1549_, 0);
v_isSharedCheck_1562_ = !lean_is_exclusive(v___x_1549_);
if (v_isSharedCheck_1562_ == 0)
{
v___x_1557_ = v___x_1549_;
v_isShared_1558_ = v_isSharedCheck_1562_;
goto v_resetjp_1556_;
}
else
{
lean_inc(v_a_1555_);
lean_dec(v___x_1549_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___redArg___boxed(lean_object* v_a_1563_, lean_object* v_funTypes_1564_, lean_object* v_sz_1565_, lean_object* v_i_1566_, lean_object* v_bs_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_){
_start:
{
size_t v_sz_boxed_1573_; size_t v_i_boxed_1574_; lean_object* v_res_1575_; 
v_sz_boxed_1573_ = lean_unbox_usize(v_sz_1565_);
lean_dec(v_sz_1565_);
v_i_boxed_1574_ = lean_unbox_usize(v_i_1566_);
lean_dec(v_i_1566_);
v_res_1575_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___redArg(v_a_1563_, v_funTypes_1564_, v_sz_boxed_1573_, v_i_boxed_1574_, v_bs_1567_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_);
lean_dec(v___y_1571_);
lean_dec_ref(v___y_1570_);
lean_dec(v___y_1569_);
lean_dec_ref(v___y_1568_);
lean_dec_ref(v_funTypes_1564_);
lean_dec_ref(v_a_1563_);
return v_res_1575_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__3(lean_object* v_recArgInfos_1576_, lean_object* v_a_1577_, size_t v___x_1578_, lean_object* v___f_1579_, lean_object* v_funTypes_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_){
_start:
{
size_t v_sz_1586_; lean_object* v___x_1587_; 
v_sz_1586_ = lean_array_size(v_recArgInfos_1576_);
v___x_1587_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___redArg(v_a_1577_, v_funTypes_1580_, v_sz_1586_, v___x_1578_, v_recArgInfos_1576_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_);
if (lean_obj_tag(v___x_1587_) == 0)
{
lean_object* v_a_1588_; lean_object* v___x_1589_; 
v_a_1588_ = lean_ctor_get(v___x_1587_, 0);
lean_inc(v_a_1588_);
lean_dec_ref_known(v___x_1587_, 1);
lean_inc(v___y_1584_);
lean_inc_ref(v___y_1583_);
lean_inc(v___y_1582_);
lean_inc_ref(v___y_1581_);
v___x_1589_ = lean_apply_7(v___f_1579_, v_funTypes_1580_, v_a_1588_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_, lean_box(0));
return v___x_1589_;
}
else
{
lean_object* v_a_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1597_; 
lean_dec_ref(v_funTypes_1580_);
lean_dec_ref(v___f_1579_);
v_a_1590_ = lean_ctor_get(v___x_1587_, 0);
v_isSharedCheck_1597_ = !lean_is_exclusive(v___x_1587_);
if (v_isSharedCheck_1597_ == 0)
{
v___x_1592_ = v___x_1587_;
v_isShared_1593_ = v_isSharedCheck_1597_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_a_1590_);
lean_dec(v___x_1587_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1597_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v___x_1595_; 
if (v_isShared_1593_ == 0)
{
v___x_1595_ = v___x_1592_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v_a_1590_);
v___x_1595_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
return v___x_1595_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__3___boxed(lean_object* v_recArgInfos_1598_, lean_object* v_a_1599_, lean_object* v___x_1600_, lean_object* v___f_1601_, lean_object* v_funTypes_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_){
_start:
{
size_t v___x_29221__boxed_1608_; lean_object* v_res_1609_; 
v___x_29221__boxed_1608_ = lean_unbox_usize(v___x_1600_);
lean_dec(v___x_1600_);
v_res_1609_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__3(v_recArgInfos_1598_, v_a_1599_, v___x_29221__boxed_1608_, v___f_1601_, v_funTypes_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_);
lean_dec(v___y_1606_);
lean_dec_ref(v___y_1605_);
lean_dec(v___y_1604_);
lean_dec_ref(v___y_1603_);
lean_dec_ref(v_a_1599_);
return v_res_1609_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___redArg(lean_object* v_a_1610_, lean_object* v_a_1611_, size_t v_sz_1612_, size_t v_i_1613_, lean_object* v_bs_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_){
_start:
{
uint8_t v___x_1620_; 
v___x_1620_ = lean_usize_dec_lt(v_i_1613_, v_sz_1612_);
if (v___x_1620_ == 0)
{
lean_object* v___x_1621_; 
v___x_1621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1621_, 0, v_bs_1614_);
return v___x_1621_;
}
else
{
lean_object* v___x_1622_; lean_object* v_v_1623_; lean_object* v___x_1624_; lean_object* v_bs_x27_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; 
v___x_1622_ = l_Lean_instInhabitedExpr;
v_v_1623_ = lean_array_uget(v_bs_1614_, v_i_1613_);
v___x_1624_ = lean_unsigned_to_nat(0u);
v_bs_x27_1625_ = lean_array_uset(v_bs_1614_, v_i_1613_, v___x_1624_);
v___x_1626_ = lean_usize_to_nat(v_i_1613_);
v___x_1627_ = lean_array_get_borrowed(v___x_1622_, v_a_1610_, v___x_1626_);
v___x_1628_ = lean_array_get_borrowed(v___x_1622_, v_a_1611_, v___x_1626_);
lean_dec(v___x_1626_);
lean_inc(v___x_1628_);
lean_inc(v___x_1627_);
v___x_1629_ = l_Lean_Elab_Structural_mkBRecOnMotive(v_v_1623_, v___x_1627_, v___x_1628_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_);
if (lean_obj_tag(v___x_1629_) == 0)
{
lean_object* v_a_1630_; size_t v___x_1631_; size_t v___x_1632_; lean_object* v___x_1633_; 
v_a_1630_ = lean_ctor_get(v___x_1629_, 0);
lean_inc(v_a_1630_);
lean_dec_ref_known(v___x_1629_, 1);
v___x_1631_ = ((size_t)1ULL);
v___x_1632_ = lean_usize_add(v_i_1613_, v___x_1631_);
v___x_1633_ = lean_array_uset(v_bs_x27_1625_, v_i_1613_, v_a_1630_);
v_i_1613_ = v___x_1632_;
v_bs_1614_ = v___x_1633_;
goto _start;
}
else
{
lean_object* v_a_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1642_; 
lean_dec_ref(v_bs_x27_1625_);
v_a_1635_ = lean_ctor_get(v___x_1629_, 0);
v_isSharedCheck_1642_ = !lean_is_exclusive(v___x_1629_);
if (v_isSharedCheck_1642_ == 0)
{
v___x_1637_ = v___x_1629_;
v_isShared_1638_ = v_isSharedCheck_1642_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_a_1635_);
lean_dec(v___x_1629_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1642_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
lean_object* v___x_1640_; 
if (v_isShared_1638_ == 0)
{
v___x_1640_ = v___x_1637_;
goto v_reusejp_1639_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v_a_1635_);
v___x_1640_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1639_;
}
v_reusejp_1639_:
{
return v___x_1640_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___redArg___boxed(lean_object* v_a_1643_, lean_object* v_a_1644_, lean_object* v_sz_1645_, lean_object* v_i_1646_, lean_object* v_bs_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_){
_start:
{
size_t v_sz_boxed_1653_; size_t v_i_boxed_1654_; lean_object* v_res_1655_; 
v_sz_boxed_1653_ = lean_unbox_usize(v_sz_1645_);
lean_dec(v_sz_1645_);
v_i_boxed_1654_ = lean_unbox_usize(v_i_1646_);
lean_dec(v_i_1646_);
v_res_1655_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___redArg(v_a_1643_, v_a_1644_, v_sz_boxed_1653_, v_i_boxed_1654_, v_bs_1647_, v___y_1648_, v___y_1649_, v___y_1650_, v___y_1651_);
lean_dec(v___y_1651_);
lean_dec_ref(v___y_1650_);
lean_dec(v___y_1649_);
lean_dec_ref(v___y_1648_);
lean_dec_ref(v_a_1644_);
lean_dec_ref(v_a_1643_);
return v_res_1655_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg(lean_object* v_msg_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_){
_start:
{
lean_object* v_ref_1662_; lean_object* v___x_1663_; lean_object* v_a_1664_; lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1672_; 
v_ref_1662_ = lean_ctor_get(v___y_1659_, 5);
v___x_1663_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11_spec__21(v_msg_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_);
v_a_1664_ = lean_ctor_get(v___x_1663_, 0);
v_isSharedCheck_1672_ = !lean_is_exclusive(v___x_1663_);
if (v_isSharedCheck_1672_ == 0)
{
v___x_1666_ = v___x_1663_;
v_isShared_1667_ = v_isSharedCheck_1672_;
goto v_resetjp_1665_;
}
else
{
lean_inc(v_a_1664_);
lean_dec(v___x_1663_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1672_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
lean_object* v___x_1668_; lean_object* v___x_1670_; 
lean_inc(v_ref_1662_);
v___x_1668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1668_, 0, v_ref_1662_);
lean_ctor_set(v___x_1668_, 1, v_a_1664_);
if (v_isShared_1667_ == 0)
{
lean_ctor_set_tag(v___x_1666_, 1);
lean_ctor_set(v___x_1666_, 0, v___x_1668_);
v___x_1670_ = v___x_1666_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v___x_1668_);
v___x_1670_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
return v___x_1670_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg___boxed(lean_object* v_msg_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_){
_start:
{
lean_object* v_res_1679_; 
v_res_1679_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg(v_msg_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_);
lean_dec(v___y_1677_);
lean_dec_ref(v___y_1676_);
lean_dec(v___y_1675_);
lean_dec_ref(v___y_1674_);
return v_res_1679_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1681_; lean_object* v___x_1682_; 
v___x_1681_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__0));
v___x_1682_ = l_Lean_stringToMessageData(v___x_1681_);
return v___x_1682_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__3(void){
_start:
{
lean_object* v___x_1684_; lean_object* v___x_1685_; 
v___x_1684_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__2));
v___x_1685_ = l_Lean_stringToMessageData(v___x_1684_);
return v___x_1685_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4(lean_object* v_constName_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_){
_start:
{
lean_object* v___x_1692_; lean_object* v_env_1693_; lean_object* v___x_1694_; 
v___x_1692_ = lean_st_ref_get(v___y_1690_);
v_env_1693_ = lean_ctor_get(v___x_1692_, 0);
lean_inc_ref(v_env_1693_);
lean_dec(v___x_1692_);
lean_inc(v_constName_1686_);
v___x_1694_ = l_Lean_isInductiveCore_x3f(v_env_1693_, v_constName_1686_);
if (lean_obj_tag(v___x_1694_) == 0)
{
lean_object* v___x_1695_; uint8_t v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; 
v___x_1695_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__1, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__1);
v___x_1696_ = 0;
v___x_1697_ = l_Lean_MessageData_ofConstName(v_constName_1686_, v___x_1696_);
v___x_1698_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1698_, 0, v___x_1695_);
lean_ctor_set(v___x_1698_, 1, v___x_1697_);
v___x_1699_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__3, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__3_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__3);
v___x_1700_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1700_, 0, v___x_1698_);
lean_ctor_set(v___x_1700_, 1, v___x_1699_);
v___x_1701_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg(v___x_1700_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_);
return v___x_1701_;
}
else
{
lean_object* v_val_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1709_; 
lean_dec(v_constName_1686_);
v_val_1702_ = lean_ctor_get(v___x_1694_, 0);
v_isSharedCheck_1709_ = !lean_is_exclusive(v___x_1694_);
if (v_isSharedCheck_1709_ == 0)
{
v___x_1704_ = v___x_1694_;
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_val_1702_);
lean_dec(v___x_1694_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
lean_object* v___x_1707_; 
if (v_isShared_1705_ == 0)
{
lean_ctor_set_tag(v___x_1704_, 0);
v___x_1707_ = v___x_1704_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v_val_1702_);
v___x_1707_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
return v___x_1707_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___boxed(lean_object* v_constName_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_){
_start:
{
lean_object* v_res_1716_; 
v_res_1716_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4(v_constName_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
lean_dec(v___y_1714_);
lean_dec_ref(v___y_1713_);
lean_dec(v___y_1712_);
lean_dec_ref(v___y_1711_);
return v_res_1716_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___redArg(lean_object* v_fixedParamPerms_1717_, lean_object* v_xs_1718_, size_t v_sz_1719_, size_t v_i_1720_, lean_object* v_bs_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_){
_start:
{
uint8_t v___x_1727_; 
v___x_1727_ = lean_usize_dec_lt(v_i_1720_, v_sz_1719_);
if (v___x_1727_ == 0)
{
lean_object* v___x_1728_; 
lean_dec_ref(v_xs_1718_);
v___x_1728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1728_, 0, v_bs_1721_);
return v___x_1728_;
}
else
{
lean_object* v_v_1729_; lean_object* v_perms_1730_; lean_object* v_type_1731_; lean_object* v___x_1732_; lean_object* v_bs_x27_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; 
v_v_1729_ = lean_array_uget_borrowed(v_bs_1721_, v_i_1720_);
v_perms_1730_ = lean_ctor_get(v_fixedParamPerms_1717_, 1);
v_type_1731_ = lean_ctor_get(v_v_1729_, 6);
lean_inc_ref(v_type_1731_);
v___x_1732_ = lean_unsigned_to_nat(0u);
v_bs_x27_1733_ = lean_array_uset(v_bs_1721_, v_i_1720_, v___x_1732_);
v___x_1734_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0);
v___x_1735_ = lean_usize_to_nat(v_i_1720_);
v___x_1736_ = lean_array_get_borrowed(v___x_1734_, v_perms_1730_, v___x_1735_);
lean_dec(v___x_1735_);
lean_inc_ref(v_xs_1718_);
lean_inc(v___x_1736_);
v___x_1737_ = l_Lean_Elab_FixedParamPerm_instantiateForall(v___x_1736_, v_type_1731_, v_xs_1718_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_);
if (lean_obj_tag(v___x_1737_) == 0)
{
lean_object* v_a_1738_; size_t v___x_1739_; size_t v___x_1740_; lean_object* v___x_1741_; 
v_a_1738_ = lean_ctor_get(v___x_1737_, 0);
lean_inc(v_a_1738_);
lean_dec_ref_known(v___x_1737_, 1);
v___x_1739_ = ((size_t)1ULL);
v___x_1740_ = lean_usize_add(v_i_1720_, v___x_1739_);
v___x_1741_ = lean_array_uset(v_bs_x27_1733_, v_i_1720_, v_a_1738_);
v_i_1720_ = v___x_1740_;
v_bs_1721_ = v___x_1741_;
goto _start;
}
else
{
lean_object* v_a_1743_; lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_1750_; 
lean_dec_ref(v_bs_x27_1733_);
lean_dec_ref(v_xs_1718_);
v_a_1743_ = lean_ctor_get(v___x_1737_, 0);
v_isSharedCheck_1750_ = !lean_is_exclusive(v___x_1737_);
if (v_isSharedCheck_1750_ == 0)
{
v___x_1745_ = v___x_1737_;
v_isShared_1746_ = v_isSharedCheck_1750_;
goto v_resetjp_1744_;
}
else
{
lean_inc(v_a_1743_);
lean_dec(v___x_1737_);
v___x_1745_ = lean_box(0);
v_isShared_1746_ = v_isSharedCheck_1750_;
goto v_resetjp_1744_;
}
v_resetjp_1744_:
{
lean_object* v___x_1748_; 
if (v_isShared_1746_ == 0)
{
v___x_1748_ = v___x_1745_;
goto v_reusejp_1747_;
}
else
{
lean_object* v_reuseFailAlloc_1749_; 
v_reuseFailAlloc_1749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1749_, 0, v_a_1743_);
v___x_1748_ = v_reuseFailAlloc_1749_;
goto v_reusejp_1747_;
}
v_reusejp_1747_:
{
return v___x_1748_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___redArg___boxed(lean_object* v_fixedParamPerms_1751_, lean_object* v_xs_1752_, lean_object* v_sz_1753_, lean_object* v_i_1754_, lean_object* v_bs_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_){
_start:
{
size_t v_sz_boxed_1761_; size_t v_i_boxed_1762_; lean_object* v_res_1763_; 
v_sz_boxed_1761_ = lean_unbox_usize(v_sz_1753_);
lean_dec(v_sz_1753_);
v_i_boxed_1762_ = lean_unbox_usize(v_i_1754_);
lean_dec(v_i_1754_);
v_res_1763_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___redArg(v_fixedParamPerms_1751_, v_xs_1752_, v_sz_boxed_1761_, v_i_boxed_1762_, v_bs_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_);
lean_dec(v___y_1759_);
lean_dec_ref(v___y_1758_);
lean_dec(v___y_1757_);
lean_dec_ref(v___y_1756_);
lean_dec_ref(v_fixedParamPerms_1751_);
return v_res_1763_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___redArg(lean_object* v_fixedParamPerms_1764_, lean_object* v_xs_1765_, size_t v_sz_1766_, size_t v_i_1767_, lean_object* v_bs_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_){
_start:
{
uint8_t v___x_1774_; 
v___x_1774_ = lean_usize_dec_lt(v_i_1767_, v_sz_1766_);
if (v___x_1774_ == 0)
{
lean_object* v___x_1775_; 
lean_dec_ref(v_xs_1765_);
v___x_1775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1775_, 0, v_bs_1768_);
return v___x_1775_;
}
else
{
lean_object* v_v_1776_; lean_object* v_perms_1777_; lean_object* v_value_1778_; lean_object* v___x_1779_; lean_object* v_bs_x27_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; 
v_v_1776_ = lean_array_uget_borrowed(v_bs_1768_, v_i_1767_);
v_perms_1777_ = lean_ctor_get(v_fixedParamPerms_1764_, 1);
v_value_1778_ = lean_ctor_get(v_v_1776_, 7);
lean_inc_ref(v_value_1778_);
v___x_1779_ = lean_unsigned_to_nat(0u);
v_bs_x27_1780_ = lean_array_uset(v_bs_1768_, v_i_1767_, v___x_1779_);
v___x_1781_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0);
v___x_1782_ = lean_usize_to_nat(v_i_1767_);
v___x_1783_ = lean_array_get_borrowed(v___x_1781_, v_perms_1777_, v___x_1782_);
lean_dec(v___x_1782_);
lean_inc_ref(v_xs_1765_);
lean_inc(v___x_1783_);
v___x_1784_ = l_Lean_Elab_FixedParamPerm_instantiateLambda(v___x_1783_, v_value_1778_, v_xs_1765_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_);
if (lean_obj_tag(v___x_1784_) == 0)
{
lean_object* v_a_1785_; size_t v___x_1786_; size_t v___x_1787_; lean_object* v___x_1788_; 
v_a_1785_ = lean_ctor_get(v___x_1784_, 0);
lean_inc(v_a_1785_);
lean_dec_ref_known(v___x_1784_, 1);
v___x_1786_ = ((size_t)1ULL);
v___x_1787_ = lean_usize_add(v_i_1767_, v___x_1786_);
v___x_1788_ = lean_array_uset(v_bs_x27_1780_, v_i_1767_, v_a_1785_);
v_i_1767_ = v___x_1787_;
v_bs_1768_ = v___x_1788_;
goto _start;
}
else
{
lean_object* v_a_1790_; lean_object* v___x_1792_; uint8_t v_isShared_1793_; uint8_t v_isSharedCheck_1797_; 
lean_dec_ref(v_bs_x27_1780_);
lean_dec_ref(v_xs_1765_);
v_a_1790_ = lean_ctor_get(v___x_1784_, 0);
v_isSharedCheck_1797_ = !lean_is_exclusive(v___x_1784_);
if (v_isSharedCheck_1797_ == 0)
{
v___x_1792_ = v___x_1784_;
v_isShared_1793_ = v_isSharedCheck_1797_;
goto v_resetjp_1791_;
}
else
{
lean_inc(v_a_1790_);
lean_dec(v___x_1784_);
v___x_1792_ = lean_box(0);
v_isShared_1793_ = v_isSharedCheck_1797_;
goto v_resetjp_1791_;
}
v_resetjp_1791_:
{
lean_object* v___x_1795_; 
if (v_isShared_1793_ == 0)
{
v___x_1795_ = v___x_1792_;
goto v_reusejp_1794_;
}
else
{
lean_object* v_reuseFailAlloc_1796_; 
v_reuseFailAlloc_1796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1796_, 0, v_a_1790_);
v___x_1795_ = v_reuseFailAlloc_1796_;
goto v_reusejp_1794_;
}
v_reusejp_1794_:
{
return v___x_1795_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___redArg___boxed(lean_object* v_fixedParamPerms_1798_, lean_object* v_xs_1799_, lean_object* v_sz_1800_, lean_object* v_i_1801_, lean_object* v_bs_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_){
_start:
{
size_t v_sz_boxed_1808_; size_t v_i_boxed_1809_; lean_object* v_res_1810_; 
v_sz_boxed_1808_ = lean_unbox_usize(v_sz_1800_);
lean_dec(v_sz_1800_);
v_i_boxed_1809_ = lean_unbox_usize(v_i_1801_);
lean_dec(v_i_1801_);
v_res_1810_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___redArg(v_fixedParamPerms_1798_, v_xs_1799_, v_sz_boxed_1808_, v_i_boxed_1809_, v_bs_1802_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_);
lean_dec(v___y_1806_);
lean_dec_ref(v___y_1805_);
lean_dec(v___y_1804_);
lean_dec_ref(v___y_1803_);
lean_dec_ref(v_fixedParamPerms_1798_);
return v_res_1810_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11___redArg(lean_object* v_hi_1811_, lean_object* v_pivot_1812_, lean_object* v_as_1813_, lean_object* v_i_1814_, lean_object* v_k_1815_){
_start:
{
uint8_t v___x_1816_; 
v___x_1816_ = lean_nat_dec_lt(v_k_1815_, v_hi_1811_);
if (v___x_1816_ == 0)
{
lean_object* v___x_1817_; lean_object* v___x_1818_; 
lean_dec(v_k_1815_);
v___x_1817_ = lean_array_fswap(v_as_1813_, v_i_1814_, v_hi_1811_);
v___x_1818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1818_, 0, v_i_1814_);
lean_ctor_set(v___x_1818_, 1, v___x_1817_);
return v___x_1818_;
}
else
{
lean_object* v___x_1819_; uint8_t v___x_1820_; 
v___x_1819_ = lean_array_fget_borrowed(v_as_1813_, v_k_1815_);
v___x_1820_ = l_Nat_blt(v___x_1819_, v_pivot_1812_);
if (v___x_1820_ == 0)
{
lean_object* v___x_1821_; lean_object* v___x_1822_; 
v___x_1821_ = lean_unsigned_to_nat(1u);
v___x_1822_ = lean_nat_add(v_k_1815_, v___x_1821_);
lean_dec(v_k_1815_);
v_k_1815_ = v___x_1822_;
goto _start;
}
else
{
lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; 
v___x_1824_ = lean_array_fswap(v_as_1813_, v_i_1814_, v_k_1815_);
v___x_1825_ = lean_unsigned_to_nat(1u);
v___x_1826_ = lean_nat_add(v_i_1814_, v___x_1825_);
lean_dec(v_i_1814_);
v___x_1827_ = lean_nat_add(v_k_1815_, v___x_1825_);
lean_dec(v_k_1815_);
v_as_1813_ = v___x_1824_;
v_i_1814_ = v___x_1826_;
v_k_1815_ = v___x_1827_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11___redArg___boxed(lean_object* v_hi_1829_, lean_object* v_pivot_1830_, lean_object* v_as_1831_, lean_object* v_i_1832_, lean_object* v_k_1833_){
_start:
{
lean_object* v_res_1834_; 
v_res_1834_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11___redArg(v_hi_1829_, v_pivot_1830_, v_as_1831_, v_i_1832_, v_k_1833_);
lean_dec(v_pivot_1830_);
lean_dec(v_hi_1829_);
return v_res_1834_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg(lean_object* v_n_1835_, lean_object* v_as_1836_, lean_object* v_lo_1837_, lean_object* v_hi_1838_){
_start:
{
lean_object* v___y_1840_; uint8_t v___x_1850_; 
v___x_1850_ = lean_nat_dec_lt(v_lo_1837_, v_hi_1838_);
if (v___x_1850_ == 0)
{
lean_dec(v_lo_1837_);
return v_as_1836_;
}
else
{
lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v_mid_1853_; lean_object* v___y_1855_; lean_object* v___y_1861_; lean_object* v___x_1866_; lean_object* v___x_1867_; uint8_t v___x_1868_; 
v___x_1851_ = lean_nat_add(v_lo_1837_, v_hi_1838_);
v___x_1852_ = lean_unsigned_to_nat(1u);
v_mid_1853_ = lean_nat_shiftr(v___x_1851_, v___x_1852_);
lean_dec(v___x_1851_);
v___x_1866_ = lean_array_fget_borrowed(v_as_1836_, v_mid_1853_);
v___x_1867_ = lean_array_fget_borrowed(v_as_1836_, v_lo_1837_);
v___x_1868_ = l_Nat_blt(v___x_1866_, v___x_1867_);
if (v___x_1868_ == 0)
{
v___y_1861_ = v_as_1836_;
goto v___jp_1860_;
}
else
{
lean_object* v___x_1869_; 
v___x_1869_ = lean_array_fswap(v_as_1836_, v_lo_1837_, v_mid_1853_);
v___y_1861_ = v___x_1869_;
goto v___jp_1860_;
}
v___jp_1854_:
{
lean_object* v___x_1856_; lean_object* v___x_1857_; uint8_t v___x_1858_; 
v___x_1856_ = lean_array_fget_borrowed(v___y_1855_, v_mid_1853_);
v___x_1857_ = lean_array_fget_borrowed(v___y_1855_, v_hi_1838_);
v___x_1858_ = l_Nat_blt(v___x_1856_, v___x_1857_);
if (v___x_1858_ == 0)
{
lean_dec(v_mid_1853_);
v___y_1840_ = v___y_1855_;
goto v___jp_1839_;
}
else
{
lean_object* v___x_1859_; 
v___x_1859_ = lean_array_fswap(v___y_1855_, v_mid_1853_, v_hi_1838_);
lean_dec(v_mid_1853_);
v___y_1840_ = v___x_1859_;
goto v___jp_1839_;
}
}
v___jp_1860_:
{
lean_object* v___x_1862_; lean_object* v___x_1863_; uint8_t v___x_1864_; 
v___x_1862_ = lean_array_fget_borrowed(v___y_1861_, v_hi_1838_);
v___x_1863_ = lean_array_fget_borrowed(v___y_1861_, v_lo_1837_);
v___x_1864_ = l_Nat_blt(v___x_1862_, v___x_1863_);
if (v___x_1864_ == 0)
{
v___y_1855_ = v___y_1861_;
goto v___jp_1854_;
}
else
{
lean_object* v___x_1865_; 
v___x_1865_ = lean_array_fswap(v___y_1861_, v_lo_1837_, v_hi_1838_);
v___y_1855_ = v___x_1865_;
goto v___jp_1854_;
}
}
}
v___jp_1839_:
{
lean_object* v_pivot_1841_; lean_object* v___x_1842_; lean_object* v_fst_1843_; lean_object* v_snd_1844_; uint8_t v___x_1845_; 
v_pivot_1841_ = lean_array_fget(v___y_1840_, v_hi_1838_);
lean_inc_n(v_lo_1837_, 2);
v___x_1842_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11___redArg(v_hi_1838_, v_pivot_1841_, v___y_1840_, v_lo_1837_, v_lo_1837_);
lean_dec(v_pivot_1841_);
v_fst_1843_ = lean_ctor_get(v___x_1842_, 0);
lean_inc(v_fst_1843_);
v_snd_1844_ = lean_ctor_get(v___x_1842_, 1);
lean_inc(v_snd_1844_);
lean_dec_ref(v___x_1842_);
v___x_1845_ = lean_nat_dec_le(v_hi_1838_, v_fst_1843_);
if (v___x_1845_ == 0)
{
lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; 
v___x_1846_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg(v_n_1835_, v_snd_1844_, v_lo_1837_, v_fst_1843_);
v___x_1847_ = lean_unsigned_to_nat(1u);
v___x_1848_ = lean_nat_add(v_fst_1843_, v___x_1847_);
lean_dec(v_fst_1843_);
v_as_1836_ = v___x_1846_;
v_lo_1837_ = v___x_1848_;
goto _start;
}
else
{
lean_dec(v_fst_1843_);
lean_dec(v_lo_1837_);
return v_snd_1844_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg___boxed(lean_object* v_n_1870_, lean_object* v_as_1871_, lean_object* v_lo_1872_, lean_object* v_hi_1873_){
_start:
{
lean_object* v_res_1874_; 
v_res_1874_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg(v_n_1870_, v_as_1871_, v_lo_1872_, v_hi_1873_);
lean_dec(v_hi_1873_);
lean_dec(v_n_1870_);
return v_res_1874_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__6(lean_object* v_xs_1875_, lean_object* v_f_1876_, lean_object* v_x_1877_, lean_object* v_as_1878_, size_t v_i_1879_, size_t v_stop_1880_, lean_object* v_b_1881_){
_start:
{
lean_object* v___y_1883_; uint8_t v___x_1887_; 
v___x_1887_ = lean_usize_dec_eq(v_i_1879_, v_stop_1880_);
if (v___x_1887_ == 0)
{
lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; uint8_t v___x_1892_; 
v___x_1888_ = l_Lean_Elab_Structural_instInhabitedRecArgInfo_default;
v___x_1889_ = lean_array_uget_borrowed(v_as_1878_, v_i_1879_);
v___x_1890_ = lean_array_get_borrowed(v___x_1888_, v_xs_1875_, v___x_1889_);
lean_inc_ref(v_f_1876_);
lean_inc(v___x_1890_);
v___x_1891_ = lean_apply_1(v_f_1876_, v___x_1890_);
v___x_1892_ = lean_nat_dec_eq(v___x_1891_, v_x_1877_);
lean_dec(v___x_1891_);
if (v___x_1892_ == 0)
{
v___y_1883_ = v_b_1881_;
goto v___jp_1882_;
}
else
{
lean_object* v___x_1893_; 
lean_inc(v___x_1889_);
v___x_1893_ = lean_array_push(v_b_1881_, v___x_1889_);
v___y_1883_ = v___x_1893_;
goto v___jp_1882_;
}
}
else
{
lean_dec_ref(v_f_1876_);
return v_b_1881_;
}
v___jp_1882_:
{
size_t v___x_1884_; size_t v___x_1885_; 
v___x_1884_ = ((size_t)1ULL);
v___x_1885_ = lean_usize_add(v_i_1879_, v___x_1884_);
v_i_1879_ = v___x_1885_;
v_b_1881_ = v___y_1883_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__6___boxed(lean_object* v_xs_1894_, lean_object* v_f_1895_, lean_object* v_x_1896_, lean_object* v_as_1897_, lean_object* v_i_1898_, lean_object* v_stop_1899_, lean_object* v_b_1900_){
_start:
{
size_t v_i_boxed_1901_; size_t v_stop_boxed_1902_; lean_object* v_res_1903_; 
v_i_boxed_1901_ = lean_unbox_usize(v_i_1898_);
lean_dec(v_i_1898_);
v_stop_boxed_1902_ = lean_unbox_usize(v_stop_1899_);
lean_dec(v_stop_1899_);
v_res_1903_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__6(v_xs_1894_, v_f_1895_, v_x_1896_, v_as_1897_, v_i_boxed_1901_, v_stop_boxed_1902_, v_b_1900_);
lean_dec_ref(v_as_1897_);
lean_dec(v_x_1896_);
lean_dec_ref(v_xs_1894_);
return v_res_1903_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8(lean_object* v_xs_1906_, lean_object* v_f_1907_, size_t v_sz_1908_, size_t v_i_1909_, lean_object* v_bs_1910_){
_start:
{
uint8_t v___x_1911_; 
v___x_1911_ = lean_usize_dec_lt(v_i_1909_, v_sz_1908_);
if (v___x_1911_ == 0)
{
lean_dec_ref(v_f_1907_);
return v_bs_1910_;
}
else
{
lean_object* v_v_1912_; lean_object* v___x_1913_; lean_object* v_bs_x27_1914_; lean_object* v___y_1916_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; uint8_t v___x_1925_; 
v_v_1912_ = lean_array_uget(v_bs_1910_, v_i_1909_);
v___x_1913_ = lean_unsigned_to_nat(0u);
v_bs_x27_1914_ = lean_array_uset(v_bs_1910_, v_i_1909_, v___x_1913_);
v___x_1921_ = lean_array_get_size(v_xs_1906_);
v___x_1922_ = l_Array_range(v___x_1921_);
v___x_1923_ = lean_array_get_size(v___x_1922_);
v___x_1924_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8___closed__0));
v___x_1925_ = lean_nat_dec_lt(v___x_1913_, v___x_1923_);
if (v___x_1925_ == 0)
{
lean_dec_ref(v___x_1922_);
lean_dec(v_v_1912_);
v___y_1916_ = v___x_1924_;
goto v___jp_1915_;
}
else
{
uint8_t v___x_1926_; 
v___x_1926_ = lean_nat_dec_le(v___x_1923_, v___x_1923_);
if (v___x_1926_ == 0)
{
if (v___x_1925_ == 0)
{
lean_dec_ref(v___x_1922_);
lean_dec(v_v_1912_);
v___y_1916_ = v___x_1924_;
goto v___jp_1915_;
}
else
{
size_t v___x_1927_; size_t v___x_1928_; lean_object* v___x_1929_; 
v___x_1927_ = ((size_t)0ULL);
v___x_1928_ = lean_usize_of_nat(v___x_1923_);
lean_inc_ref(v_f_1907_);
v___x_1929_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__6(v_xs_1906_, v_f_1907_, v_v_1912_, v___x_1922_, v___x_1927_, v___x_1928_, v___x_1924_);
lean_dec_ref(v___x_1922_);
lean_dec(v_v_1912_);
v___y_1916_ = v___x_1929_;
goto v___jp_1915_;
}
}
else
{
size_t v___x_1930_; size_t v___x_1931_; lean_object* v___x_1932_; 
v___x_1930_ = ((size_t)0ULL);
v___x_1931_ = lean_usize_of_nat(v___x_1923_);
lean_inc_ref(v_f_1907_);
v___x_1932_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__6(v_xs_1906_, v_f_1907_, v_v_1912_, v___x_1922_, v___x_1930_, v___x_1931_, v___x_1924_);
lean_dec_ref(v___x_1922_);
lean_dec(v_v_1912_);
v___y_1916_ = v___x_1932_;
goto v___jp_1915_;
}
}
v___jp_1915_:
{
size_t v___x_1917_; size_t v___x_1918_; lean_object* v___x_1919_; 
v___x_1917_ = ((size_t)1ULL);
v___x_1918_ = lean_usize_add(v_i_1909_, v___x_1917_);
v___x_1919_ = lean_array_uset(v_bs_x27_1914_, v_i_1909_, v___y_1916_);
v_i_1909_ = v___x_1918_;
v_bs_1910_ = v___x_1919_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8___boxed(lean_object* v_xs_1933_, lean_object* v_f_1934_, lean_object* v_sz_1935_, lean_object* v_i_1936_, lean_object* v_bs_1937_){
_start:
{
size_t v_sz_boxed_1938_; size_t v_i_boxed_1939_; lean_object* v_res_1940_; 
v_sz_boxed_1938_ = lean_unbox_usize(v_sz_1935_);
lean_dec(v_sz_1935_);
v_i_boxed_1939_ = lean_unbox_usize(v_i_1936_);
lean_dec(v_i_1936_);
v_res_1940_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8(v_xs_1933_, v_f_1934_, v_sz_boxed_1938_, v_i_boxed_1939_, v_bs_1937_);
lean_dec_ref(v_xs_1933_);
return v_res_1940_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__11(lean_object* v_as_1941_, size_t v_i_1942_, size_t v_stop_1943_, lean_object* v_b_1944_){
_start:
{
uint8_t v___x_1945_; 
v___x_1945_ = lean_usize_dec_eq(v_i_1942_, v_stop_1943_);
if (v___x_1945_ == 0)
{
lean_object* v___x_1946_; lean_object* v___x_1947_; size_t v___x_1948_; size_t v___x_1949_; 
v___x_1946_ = lean_array_uget_borrowed(v_as_1941_, v_i_1942_);
v___x_1947_ = l_Array_append___redArg(v_b_1944_, v___x_1946_);
v___x_1948_ = ((size_t)1ULL);
v___x_1949_ = lean_usize_add(v_i_1942_, v___x_1948_);
v_i_1942_ = v___x_1949_;
v_b_1944_ = v___x_1947_;
goto _start;
}
else
{
return v_b_1944_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__11___boxed(lean_object* v_as_1951_, lean_object* v_i_1952_, lean_object* v_stop_1953_, lean_object* v_b_1954_){
_start:
{
size_t v_i_boxed_1955_; size_t v_stop_boxed_1956_; lean_object* v_res_1957_; 
v_i_boxed_1955_ = lean_unbox_usize(v_i_1952_);
lean_dec(v_i_1952_);
v_stop_boxed_1956_ = lean_unbox_usize(v_stop_1953_);
lean_dec(v_stop_1953_);
v_res_1957_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__11(v_as_1951_, v_i_boxed_1955_, v_stop_boxed_1956_, v_b_1954_);
lean_dec_ref(v_as_1951_);
return v_res_1957_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__7___closed__0(void){
_start:
{
lean_object* v___x_1958_; 
v___x_1958_ = l_Array_instInhabited(lean_box(0));
return v___x_1958_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__7(lean_object* v_msg_1959_){
_start:
{
lean_object* v___x_1960_; lean_object* v___x_1961_; 
v___x_1960_ = lean_obj_once(&l_panic___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__7___closed__0, &l_panic___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__7___closed__0_once, _init_l_panic___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__7___closed__0);
v___x_1961_ = lean_panic_fn_borrowed(v___x_1960_, v_msg_1959_);
return v___x_1961_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9___redArg(lean_object* v_xs_1962_, lean_object* v_ys_1963_, lean_object* v_x_1964_){
_start:
{
lean_object* v_zero_1965_; uint8_t v_isZero_1966_; 
v_zero_1965_ = lean_unsigned_to_nat(0u);
v_isZero_1966_ = lean_nat_dec_eq(v_x_1964_, v_zero_1965_);
if (v_isZero_1966_ == 1)
{
lean_dec(v_x_1964_);
return v_isZero_1966_;
}
else
{
lean_object* v_one_1967_; lean_object* v_n_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; uint8_t v___x_1971_; 
v_one_1967_ = lean_unsigned_to_nat(1u);
v_n_1968_ = lean_nat_sub(v_x_1964_, v_one_1967_);
lean_dec(v_x_1964_);
v___x_1969_ = lean_array_fget_borrowed(v_xs_1962_, v_n_1968_);
v___x_1970_ = lean_array_fget_borrowed(v_ys_1963_, v_n_1968_);
v___x_1971_ = lean_nat_dec_eq(v___x_1969_, v___x_1970_);
if (v___x_1971_ == 0)
{
lean_dec(v_n_1968_);
return v___x_1971_;
}
else
{
v_x_1964_ = v_n_1968_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9___redArg___boxed(lean_object* v_xs_1973_, lean_object* v_ys_1974_, lean_object* v_x_1975_){
_start:
{
uint8_t v_res_1976_; lean_object* v_r_1977_; 
v_res_1976_ = l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9___redArg(v_xs_1973_, v_ys_1974_, v_x_1975_);
lean_dec_ref(v_ys_1974_);
lean_dec_ref(v_xs_1973_);
v_r_1977_ = lean_box(v_res_1976_);
return v_r_1977_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__2(void){
_start:
{
lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; 
v___x_1980_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__1));
v___x_1981_ = lean_unsigned_to_nat(2u);
v___x_1982_ = lean_unsigned_to_nat(63u);
v___x_1983_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__0));
v___x_1984_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__0));
v___x_1985_ = l_mkPanicMessageWithDecl(v___x_1984_, v___x_1983_, v___x_1982_, v___x_1981_, v___x_1980_);
return v___x_1985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5(lean_object* v_f_1988_, lean_object* v_xs_1989_, lean_object* v_ys_1990_){
_start:
{
size_t v_sz_1994_; size_t v___x_1995_; lean_object* v_positions_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___y_2000_; lean_object* v___y_2006_; lean_object* v___y_2007_; lean_object* v___y_2008_; lean_object* v___y_2009_; lean_object* v___y_2012_; lean_object* v___y_2013_; lean_object* v___y_2014_; lean_object* v___y_2015_; lean_object* v___y_2018_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; uint8_t v___x_2028_; 
v_sz_1994_ = lean_array_size(v_ys_1990_);
v___x_1995_ = ((size_t)0ULL);
v_positions_1996_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8(v_xs_1989_, v_f_1988_, v_sz_1994_, v___x_1995_, v_ys_1990_);
v___x_1997_ = lean_array_get_size(v_xs_1989_);
v___x_1998_ = l_Array_range(v___x_1997_);
v___x_2025_ = lean_unsigned_to_nat(0u);
v___x_2026_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__3));
v___x_2027_ = lean_array_get_size(v_positions_1996_);
v___x_2028_ = lean_nat_dec_lt(v___x_2025_, v___x_2027_);
if (v___x_2028_ == 0)
{
v___y_2018_ = v___x_2026_;
goto v___jp_2017_;
}
else
{
uint8_t v___x_2029_; 
v___x_2029_ = lean_nat_dec_le(v___x_2027_, v___x_2027_);
if (v___x_2029_ == 0)
{
if (v___x_2028_ == 0)
{
v___y_2018_ = v___x_2026_;
goto v___jp_2017_;
}
else
{
size_t v___x_2030_; lean_object* v___x_2031_; 
v___x_2030_ = lean_usize_of_nat(v___x_2027_);
v___x_2031_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__11(v_positions_1996_, v___x_1995_, v___x_2030_, v___x_2026_);
v___y_2018_ = v___x_2031_;
goto v___jp_2017_;
}
}
else
{
size_t v___x_2032_; lean_object* v___x_2033_; 
v___x_2032_ = lean_usize_of_nat(v___x_2027_);
v___x_2033_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__11(v_positions_1996_, v___x_1995_, v___x_2032_, v___x_2026_);
v___y_2018_ = v___x_2033_;
goto v___jp_2017_;
}
}
v___jp_1991_:
{
lean_object* v___x_1992_; lean_object* v___x_1993_; 
v___x_1992_ = lean_obj_once(&l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__2, &l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__2_once, _init_l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__2);
v___x_1993_ = l_panic___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__7(v___x_1992_);
return v___x_1993_;
}
v___jp_1999_:
{
lean_object* v___x_2001_; lean_object* v___x_2002_; uint8_t v___x_2003_; 
v___x_2001_ = lean_array_get_size(v___x_1998_);
v___x_2002_ = lean_array_get_size(v___y_2000_);
v___x_2003_ = lean_nat_dec_eq(v___x_2001_, v___x_2002_);
if (v___x_2003_ == 0)
{
lean_dec_ref(v___y_2000_);
lean_dec_ref(v___x_1998_);
lean_dec_ref(v_positions_1996_);
goto v___jp_1991_;
}
else
{
uint8_t v___x_2004_; 
v___x_2004_ = l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9___redArg(v___x_1998_, v___y_2000_, v___x_2001_);
lean_dec_ref(v___y_2000_);
lean_dec_ref(v___x_1998_);
if (v___x_2004_ == 0)
{
lean_dec_ref(v_positions_1996_);
goto v___jp_1991_;
}
else
{
return v_positions_1996_;
}
}
}
v___jp_2005_:
{
lean_object* v___x_2010_; 
v___x_2010_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg(v___y_2006_, v___y_2008_, v___y_2007_, v___y_2009_);
lean_dec(v___y_2009_);
lean_dec(v___y_2006_);
v___y_2000_ = v___x_2010_;
goto v___jp_1999_;
}
v___jp_2011_:
{
uint8_t v___x_2016_; 
v___x_2016_ = lean_nat_dec_le(v___y_2015_, v___y_2012_);
if (v___x_2016_ == 0)
{
lean_dec(v___y_2012_);
lean_inc(v___y_2015_);
v___y_2006_ = v___y_2013_;
v___y_2007_ = v___y_2015_;
v___y_2008_ = v___y_2014_;
v___y_2009_ = v___y_2015_;
goto v___jp_2005_;
}
else
{
v___y_2006_ = v___y_2013_;
v___y_2007_ = v___y_2015_;
v___y_2008_ = v___y_2014_;
v___y_2009_ = v___y_2012_;
goto v___jp_2005_;
}
}
v___jp_2017_:
{
lean_object* v___x_2019_; lean_object* v___x_2020_; uint8_t v___x_2021_; 
v___x_2019_ = lean_array_get_size(v___y_2018_);
v___x_2020_ = lean_unsigned_to_nat(0u);
v___x_2021_ = lean_nat_dec_eq(v___x_2019_, v___x_2020_);
if (v___x_2021_ == 0)
{
lean_object* v___x_2022_; lean_object* v___x_2023_; uint8_t v___x_2024_; 
v___x_2022_ = lean_unsigned_to_nat(1u);
v___x_2023_ = lean_nat_sub(v___x_2019_, v___x_2022_);
v___x_2024_ = lean_nat_dec_le(v___x_2020_, v___x_2023_);
if (v___x_2024_ == 0)
{
lean_inc(v___x_2023_);
v___y_2012_ = v___x_2023_;
v___y_2013_ = v___x_2019_;
v___y_2014_ = v___y_2018_;
v___y_2015_ = v___x_2023_;
goto v___jp_2011_;
}
else
{
v___y_2012_ = v___x_2023_;
v___y_2013_ = v___x_2019_;
v___y_2014_ = v___y_2018_;
v___y_2015_ = v___x_2020_;
goto v___jp_2011_;
}
}
else
{
v___y_2000_ = v___y_2018_;
goto v___jp_1999_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___boxed(lean_object* v_f_2034_, lean_object* v_xs_2035_, lean_object* v_ys_2036_){
_start:
{
lean_object* v_res_2037_; 
v_res_2037_ = l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5(v_f_2034_, v_xs_2035_, v_ys_2036_);
lean_dec_ref(v_xs_2035_);
return v_res_2037_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__0(lean_object* v_a_2038_, lean_object* v_a_2039_){
_start:
{
if (lean_obj_tag(v_a_2038_) == 0)
{
lean_object* v___x_2040_; 
v___x_2040_ = l_List_reverse___redArg(v_a_2039_);
return v___x_2040_;
}
else
{
lean_object* v_head_2041_; lean_object* v_tail_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2053_; 
v_head_2041_ = lean_ctor_get(v_a_2038_, 0);
v_tail_2042_ = lean_ctor_get(v_a_2038_, 1);
v_isSharedCheck_2053_ = !lean_is_exclusive(v_a_2038_);
if (v_isSharedCheck_2053_ == 0)
{
v___x_2044_ = v_a_2038_;
v_isShared_2045_ = v_isSharedCheck_2053_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_tail_2042_);
lean_inc(v_head_2041_);
lean_dec(v_a_2038_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2053_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2050_; 
v___x_2046_ = l_Nat_reprFast(v_head_2041_);
v___x_2047_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2047_, 0, v___x_2046_);
v___x_2048_ = l_Lean_MessageData_ofFormat(v___x_2047_);
if (v_isShared_2045_ == 0)
{
lean_ctor_set(v___x_2044_, 1, v_a_2039_);
lean_ctor_set(v___x_2044_, 0, v___x_2048_);
v___x_2050_ = v___x_2044_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v___x_2048_);
lean_ctor_set(v_reuseFailAlloc_2052_, 1, v_a_2039_);
v___x_2050_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
v_a_2038_ = v_tail_2042_;
v_a_2039_ = v___x_2050_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__20(lean_object* v_a_2054_, lean_object* v_a_2055_){
_start:
{
if (lean_obj_tag(v_a_2054_) == 0)
{
lean_object* v___x_2056_; 
v___x_2056_ = l_List_reverse___redArg(v_a_2055_);
return v___x_2056_;
}
else
{
lean_object* v_head_2057_; lean_object* v_tail_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2070_; 
v_head_2057_ = lean_ctor_get(v_a_2054_, 0);
v_tail_2058_ = lean_ctor_get(v_a_2054_, 1);
v_isSharedCheck_2070_ = !lean_is_exclusive(v_a_2054_);
if (v_isSharedCheck_2070_ == 0)
{
v___x_2060_ = v_a_2054_;
v_isShared_2061_ = v_isSharedCheck_2070_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_tail_2058_);
lean_inc(v_head_2057_);
lean_dec(v_a_2054_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2070_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2067_; 
v___x_2062_ = lean_array_to_list(v_head_2057_);
v___x_2063_ = lean_box(0);
v___x_2064_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__0(v___x_2062_, v___x_2063_);
v___x_2065_ = l_Lean_MessageData_ofList(v___x_2064_);
if (v_isShared_2061_ == 0)
{
lean_ctor_set(v___x_2060_, 1, v_a_2055_);
lean_ctor_set(v___x_2060_, 0, v___x_2065_);
v___x_2067_ = v___x_2060_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v___x_2065_);
lean_ctor_set(v_reuseFailAlloc_2069_, 1, v_a_2055_);
v___x_2067_ = v_reuseFailAlloc_2069_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
v_a_2054_ = v_tail_2058_;
v_a_2055_ = v___x_2067_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__9(void){
_start:
{
lean_object* v___x_2085_; lean_object* v___x_2086_; 
v___x_2085_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__8));
v___x_2086_ = l_Lean_stringToMessageData(v___x_2085_);
return v___x_2086_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__11(void){
_start:
{
lean_object* v___x_2088_; lean_object* v___x_2089_; 
v___x_2088_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__10));
v___x_2089_ = l_Lean_stringToMessageData(v___x_2088_);
return v___x_2089_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion(lean_object* v_preDefs_2090_, lean_object* v_fixedParamPerms_2091_, lean_object* v_xs_2092_, lean_object* v_recArgInfos_2093_, lean_object* v_a_2094_, lean_object* v_a_2095_, lean_object* v_a_2096_, lean_object* v_a_2097_){
_start:
{
size_t v_sz_2099_; size_t v___x_2100_; lean_object* v___x_2101_; 
v_sz_2099_ = lean_array_size(v_preDefs_2090_);
v___x_2100_ = ((size_t)0ULL);
lean_inc_ref(v_preDefs_2090_);
lean_inc_ref(v_xs_2092_);
v___x_2101_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___redArg(v_fixedParamPerms_2091_, v_xs_2092_, v_sz_2099_, v___x_2100_, v_preDefs_2090_, v_a_2094_, v_a_2095_, v_a_2096_, v_a_2097_);
if (lean_obj_tag(v___x_2101_) == 0)
{
lean_object* v_a_2102_; lean_object* v___x_2103_; 
v_a_2102_ = lean_ctor_get(v___x_2101_, 0);
lean_inc(v_a_2102_);
lean_dec_ref_known(v___x_2101_, 1);
lean_inc_ref(v_preDefs_2090_);
lean_inc_ref(v_xs_2092_);
v___x_2103_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___redArg(v_fixedParamPerms_2091_, v_xs_2092_, v_sz_2099_, v___x_2100_, v_preDefs_2090_, v_a_2094_, v_a_2095_, v_a_2096_, v_a_2097_);
if (lean_obj_tag(v___x_2103_) == 0)
{
lean_object* v_a_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v_indGroupInst_2108_; lean_object* v_toIndGroupInfo_2109_; lean_object* v_all_2110_; lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2197_; 
v_a_2104_ = lean_ctor_get(v___x_2103_, 0);
lean_inc(v_a_2104_);
lean_dec_ref_known(v___x_2103_, 1);
v___x_2105_ = l_Lean_Elab_Structural_instInhabitedRecArgInfo_default;
v___x_2106_ = lean_unsigned_to_nat(0u);
v___x_2107_ = lean_array_get_borrowed(v___x_2105_, v_recArgInfos_2093_, v___x_2106_);
v_indGroupInst_2108_ = lean_ctor_get(v___x_2107_, 4);
v_toIndGroupInfo_2109_ = lean_ctor_get(v_indGroupInst_2108_, 0);
lean_inc_ref(v_toIndGroupInfo_2109_);
v_all_2110_ = lean_ctor_get(v_toIndGroupInfo_2109_, 0);
v_isSharedCheck_2197_ = !lean_is_exclusive(v_toIndGroupInfo_2109_);
if (v_isSharedCheck_2197_ == 0)
{
lean_object* v_unused_2198_; 
v_unused_2198_ = lean_ctor_get(v_toIndGroupInfo_2109_, 1);
lean_dec(v_unused_2198_);
v___x_2112_ = v_toIndGroupInfo_2109_;
v_isShared_2113_ = v_isSharedCheck_2197_;
goto v_resetjp_2111_;
}
else
{
lean_inc(v_all_2110_);
lean_dec(v_toIndGroupInfo_2109_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2197_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; 
v___x_2114_ = lean_box(0);
v___x_2115_ = lean_array_get(v___x_2114_, v_all_2110_, v___x_2106_);
lean_dec_ref(v_all_2110_);
v___x_2116_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4(v___x_2115_, v_a_2094_, v_a_2095_, v_a_2096_, v_a_2097_);
if (lean_obj_tag(v___x_2116_) == 0)
{
lean_object* v_a_2117_; lean_object* v___x_2118_; lean_object* v___f_2119_; lean_object* v___x_2120_; lean_object* v_a_2121_; lean_object* v___f_2122_; lean_object* v___f_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___y_2128_; lean_object* v___y_2129_; lean_object* v___y_2130_; lean_object* v___y_2131_; uint8_t v___x_2165_; 
v_a_2117_ = lean_ctor_get(v___x_2116_, 0);
lean_inc(v_a_2117_);
lean_dec_ref_known(v___x_2116_, 1);
v___x_2118_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__3));
v___f_2119_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__4));
v___x_2120_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0(v___x_2118_, v_a_2094_, v_a_2095_, v_a_2096_, v_a_2097_);
v_a_2121_ = lean_ctor_get(v___x_2120_, 0);
lean_inc(v_a_2121_);
lean_dec_ref(v___x_2120_);
v___f_2122_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__5));
v___f_2123_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__6));
v___x_2124_ = l_Lean_InductiveVal_numTypeFormers(v_a_2117_);
v___x_2125_ = l_Array_range(v___x_2124_);
v___x_2126_ = l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5(v___f_2123_, v_recArgInfos_2093_, v___x_2125_);
v___x_2165_ = lean_unbox(v_a_2121_);
lean_dec(v_a_2121_);
if (v___x_2165_ == 0)
{
lean_del_object(v___x_2112_);
v___y_2128_ = v_a_2094_;
v___y_2129_ = v_a_2095_;
v___y_2130_ = v_a_2096_;
v___y_2131_ = v_a_2097_;
goto v___jp_2127_;
}
else
{
lean_object* v_toConstantVal_2166_; lean_object* v_name_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2171_; 
v_toConstantVal_2166_ = lean_ctor_get(v_a_2117_, 0);
v_name_2167_ = lean_ctor_get(v_toConstantVal_2166_, 0);
v___x_2168_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__9, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__9_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__9);
lean_inc(v_name_2167_);
v___x_2169_ = l_Lean_MessageData_ofName(v_name_2167_);
if (v_isShared_2113_ == 0)
{
lean_ctor_set_tag(v___x_2112_, 7);
lean_ctor_set(v___x_2112_, 1, v___x_2169_);
lean_ctor_set(v___x_2112_, 0, v___x_2168_);
v___x_2171_ = v___x_2112_;
goto v_reusejp_2170_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v___x_2168_);
lean_ctor_set(v_reuseFailAlloc_2188_, 1, v___x_2169_);
v___x_2171_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2170_;
}
v_reusejp_2170_:
{
lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; 
v___x_2172_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__11, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__11_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__11);
v___x_2173_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2173_, 0, v___x_2171_);
lean_ctor_set(v___x_2173_, 1, v___x_2172_);
lean_inc_ref(v___x_2126_);
v___x_2174_ = lean_array_to_list(v___x_2126_);
v___x_2175_ = lean_box(0);
v___x_2176_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__20(v___x_2174_, v___x_2175_);
v___x_2177_ = l_Lean_MessageData_ofList(v___x_2176_);
v___x_2178_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2178_, 0, v___x_2173_);
lean_ctor_set(v___x_2178_, 1, v___x_2177_);
v___x_2179_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_2118_, v___x_2178_, v_a_2094_, v_a_2095_, v_a_2096_, v_a_2097_);
if (lean_obj_tag(v___x_2179_) == 0)
{
lean_dec_ref_known(v___x_2179_, 1);
v___y_2128_ = v_a_2094_;
v___y_2129_ = v_a_2095_;
v___y_2130_ = v_a_2096_;
v___y_2131_ = v_a_2097_;
goto v___jp_2127_;
}
else
{
lean_object* v_a_2180_; lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2187_; 
lean_dec_ref(v___x_2126_);
lean_dec(v_a_2117_);
lean_dec(v_a_2104_);
lean_dec(v_a_2102_);
lean_dec_ref(v_recArgInfos_2093_);
lean_dec_ref(v_xs_2092_);
lean_dec_ref(v_fixedParamPerms_2091_);
lean_dec_ref(v_preDefs_2090_);
v_a_2180_ = lean_ctor_get(v___x_2179_, 0);
v_isSharedCheck_2187_ = !lean_is_exclusive(v___x_2179_);
if (v_isSharedCheck_2187_ == 0)
{
v___x_2182_ = v___x_2179_;
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
else
{
lean_inc(v_a_2180_);
lean_dec(v___x_2179_);
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
}
v___jp_2127_:
{
lean_object* v_toConstantVal_2132_; lean_object* v_numIndices_2133_; lean_object* v_name_2134_; lean_object* v___x_2135_; 
v_toConstantVal_2132_ = lean_ctor_get(v_a_2117_, 0);
lean_inc_ref(v_toConstantVal_2132_);
v_numIndices_2133_ = lean_ctor_get(v_a_2117_, 2);
lean_inc(v_numIndices_2133_);
lean_dec(v_a_2117_);
v_name_2134_ = lean_ctor_get(v_toConstantVal_2132_, 0);
lean_inc(v_name_2134_);
lean_dec_ref(v_toConstantVal_2132_);
v___x_2135_ = l_Lean_Meta_isInductivePredicate(v_name_2134_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_);
if (lean_obj_tag(v___x_2135_) == 0)
{
lean_object* v_a_2136_; lean_object* v___x_2137_; lean_object* v___f_2138_; uint8_t v___x_2139_; 
v_a_2136_ = lean_ctor_get(v___x_2135_, 0);
lean_inc_n(v_a_2136_, 2);
lean_dec_ref_known(v___x_2135_, 1);
v___x_2137_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___boxed__const__1));
lean_inc(v_numIndices_2133_);
lean_inc_ref(v_preDefs_2090_);
lean_inc_ref(v_xs_2092_);
lean_inc_ref(v_fixedParamPerms_2091_);
lean_inc_ref(v___x_2126_);
lean_inc(v_a_2102_);
lean_inc_ref(v_recArgInfos_2093_);
v___f_2138_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___boxed), 20, 13);
lean_closure_set(v___f_2138_, 0, v___f_2119_);
lean_closure_set(v___f_2138_, 1, v_recArgInfos_2093_);
lean_closure_set(v___f_2138_, 2, v_a_2102_);
lean_closure_set(v___f_2138_, 3, v___x_2126_);
lean_closure_set(v___f_2138_, 4, v___x_2137_);
lean_closure_set(v___f_2138_, 5, v_fixedParamPerms_2091_);
lean_closure_set(v___f_2138_, 6, v_xs_2092_);
lean_closure_set(v___f_2138_, 7, v___x_2106_);
lean_closure_set(v___f_2138_, 8, v_preDefs_2090_);
lean_closure_set(v___f_2138_, 9, v_numIndices_2133_);
lean_closure_set(v___f_2138_, 10, v___f_2122_);
lean_closure_set(v___f_2138_, 11, v___x_2118_);
lean_closure_set(v___f_2138_, 12, v_a_2136_);
v___x_2139_ = lean_unbox(v_a_2136_);
if (v___x_2139_ == 0)
{
size_t v_sz_2140_; lean_object* v___x_2141_; 
lean_dec_ref(v___f_2138_);
v_sz_2140_ = lean_array_size(v_recArgInfos_2093_);
lean_inc_ref(v_recArgInfos_2093_);
v___x_2141_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___redArg(v_a_2102_, v_a_2104_, v_sz_2140_, v___x_2100_, v_recArgInfos_2093_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_);
lean_dec(v_a_2104_);
if (lean_obj_tag(v___x_2141_) == 0)
{
lean_object* v_a_2142_; lean_object* v___x_2143_; uint8_t v___x_2144_; lean_object* v___x_2145_; 
v_a_2142_ = lean_ctor_get(v___x_2141_, 0);
lean_inc(v_a_2142_);
lean_dec_ref_known(v___x_2141_, 1);
v___x_2143_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__7));
v___x_2144_ = lean_unbox(v_a_2136_);
lean_dec(v_a_2136_);
v___x_2145_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2(v___f_2119_, v_recArgInfos_2093_, v_a_2102_, v___x_2126_, v___x_2100_, v_fixedParamPerms_2091_, v_xs_2092_, v___x_2106_, v_preDefs_2090_, v_numIndices_2133_, v___f_2122_, v___x_2118_, v___x_2144_, v___x_2143_, v_a_2142_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_);
lean_dec(v_numIndices_2133_);
lean_dec(v_a_2102_);
return v___x_2145_;
}
else
{
lean_object* v_a_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2153_; 
lean_dec(v_a_2136_);
lean_dec(v_numIndices_2133_);
lean_dec_ref(v___x_2126_);
lean_dec(v_a_2102_);
lean_dec_ref(v_recArgInfos_2093_);
lean_dec_ref(v_xs_2092_);
lean_dec_ref(v_fixedParamPerms_2091_);
lean_dec_ref(v_preDefs_2090_);
v_a_2146_ = lean_ctor_get(v___x_2141_, 0);
v_isSharedCheck_2153_ = !lean_is_exclusive(v___x_2141_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2148_ = v___x_2141_;
v_isShared_2149_ = v_isSharedCheck_2153_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_a_2146_);
lean_dec(v___x_2141_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2153_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
lean_object* v___x_2151_; 
if (v_isShared_2149_ == 0)
{
v___x_2151_ = v___x_2148_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v_a_2146_);
v___x_2151_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
return v___x_2151_;
}
}
}
}
else
{
lean_object* v___x_2154_; lean_object* v___f_2155_; lean_object* v___x_2156_; 
lean_dec(v_a_2136_);
lean_dec(v_numIndices_2133_);
lean_dec_ref(v___x_2126_);
lean_dec(v_a_2104_);
lean_dec_ref(v_xs_2092_);
lean_dec_ref(v_fixedParamPerms_2091_);
lean_dec_ref(v_preDefs_2090_);
v___x_2154_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___boxed__const__1));
lean_inc(v_a_2102_);
v___f_2155_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__3___boxed), 10, 4);
lean_closure_set(v___f_2155_, 0, v_recArgInfos_2093_);
lean_closure_set(v___f_2155_, 1, v_a_2102_);
lean_closure_set(v___f_2155_, 2, v___x_2154_);
lean_closure_set(v___f_2155_, 3, v___f_2138_);
v___x_2156_ = l_Lean_Elab_Structural_withFunTypes___redArg(v_a_2102_, v___f_2155_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_);
return v___x_2156_;
}
}
else
{
lean_object* v_a_2157_; lean_object* v___x_2159_; uint8_t v_isShared_2160_; uint8_t v_isSharedCheck_2164_; 
lean_dec(v_numIndices_2133_);
lean_dec_ref(v___x_2126_);
lean_dec(v_a_2104_);
lean_dec(v_a_2102_);
lean_dec_ref(v_recArgInfos_2093_);
lean_dec_ref(v_xs_2092_);
lean_dec_ref(v_fixedParamPerms_2091_);
lean_dec_ref(v_preDefs_2090_);
v_a_2157_ = lean_ctor_get(v___x_2135_, 0);
v_isSharedCheck_2164_ = !lean_is_exclusive(v___x_2135_);
if (v_isSharedCheck_2164_ == 0)
{
v___x_2159_ = v___x_2135_;
v_isShared_2160_ = v_isSharedCheck_2164_;
goto v_resetjp_2158_;
}
else
{
lean_inc(v_a_2157_);
lean_dec(v___x_2135_);
v___x_2159_ = lean_box(0);
v_isShared_2160_ = v_isSharedCheck_2164_;
goto v_resetjp_2158_;
}
v_resetjp_2158_:
{
lean_object* v___x_2162_; 
if (v_isShared_2160_ == 0)
{
v___x_2162_ = v___x_2159_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v_a_2157_);
v___x_2162_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
return v___x_2162_;
}
}
}
}
}
else
{
lean_object* v_a_2189_; lean_object* v___x_2191_; uint8_t v_isShared_2192_; uint8_t v_isSharedCheck_2196_; 
lean_del_object(v___x_2112_);
lean_dec(v_a_2104_);
lean_dec(v_a_2102_);
lean_dec_ref(v_recArgInfos_2093_);
lean_dec_ref(v_xs_2092_);
lean_dec_ref(v_fixedParamPerms_2091_);
lean_dec_ref(v_preDefs_2090_);
v_a_2189_ = lean_ctor_get(v___x_2116_, 0);
v_isSharedCheck_2196_ = !lean_is_exclusive(v___x_2116_);
if (v_isSharedCheck_2196_ == 0)
{
v___x_2191_ = v___x_2116_;
v_isShared_2192_ = v_isSharedCheck_2196_;
goto v_resetjp_2190_;
}
else
{
lean_inc(v_a_2189_);
lean_dec(v___x_2116_);
v___x_2191_ = lean_box(0);
v_isShared_2192_ = v_isSharedCheck_2196_;
goto v_resetjp_2190_;
}
v_resetjp_2190_:
{
lean_object* v___x_2194_; 
if (v_isShared_2192_ == 0)
{
v___x_2194_ = v___x_2191_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v_a_2189_);
v___x_2194_ = v_reuseFailAlloc_2195_;
goto v_reusejp_2193_;
}
v_reusejp_2193_:
{
return v___x_2194_;
}
}
}
}
}
else
{
lean_object* v_a_2199_; lean_object* v___x_2201_; uint8_t v_isShared_2202_; uint8_t v_isSharedCheck_2206_; 
lean_dec(v_a_2102_);
lean_dec_ref(v_recArgInfos_2093_);
lean_dec_ref(v_xs_2092_);
lean_dec_ref(v_fixedParamPerms_2091_);
lean_dec_ref(v_preDefs_2090_);
v_a_2199_ = lean_ctor_get(v___x_2103_, 0);
v_isSharedCheck_2206_ = !lean_is_exclusive(v___x_2103_);
if (v_isSharedCheck_2206_ == 0)
{
v___x_2201_ = v___x_2103_;
v_isShared_2202_ = v_isSharedCheck_2206_;
goto v_resetjp_2200_;
}
else
{
lean_inc(v_a_2199_);
lean_dec(v___x_2103_);
v___x_2201_ = lean_box(0);
v_isShared_2202_ = v_isSharedCheck_2206_;
goto v_resetjp_2200_;
}
v_resetjp_2200_:
{
lean_object* v___x_2204_; 
if (v_isShared_2202_ == 0)
{
v___x_2204_ = v___x_2201_;
goto v_reusejp_2203_;
}
else
{
lean_object* v_reuseFailAlloc_2205_; 
v_reuseFailAlloc_2205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2205_, 0, v_a_2199_);
v___x_2204_ = v_reuseFailAlloc_2205_;
goto v_reusejp_2203_;
}
v_reusejp_2203_:
{
return v___x_2204_;
}
}
}
}
else
{
lean_object* v_a_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2214_; 
lean_dec_ref(v_recArgInfos_2093_);
lean_dec_ref(v_xs_2092_);
lean_dec_ref(v_fixedParamPerms_2091_);
lean_dec_ref(v_preDefs_2090_);
v_a_2207_ = lean_ctor_get(v___x_2101_, 0);
v_isSharedCheck_2214_ = !lean_is_exclusive(v___x_2101_);
if (v_isSharedCheck_2214_ == 0)
{
v___x_2209_ = v___x_2101_;
v_isShared_2210_ = v_isSharedCheck_2214_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_a_2207_);
lean_dec(v___x_2101_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2214_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
lean_object* v___x_2212_; 
if (v_isShared_2210_ == 0)
{
v___x_2212_ = v___x_2209_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v_a_2207_);
v___x_2212_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
return v___x_2212_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___boxed(lean_object* v_preDefs_2215_, lean_object* v_fixedParamPerms_2216_, lean_object* v_xs_2217_, lean_object* v_recArgInfos_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_){
_start:
{
lean_object* v_res_2224_; 
v_res_2224_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion(v_preDefs_2215_, v_fixedParamPerms_2216_, v_xs_2217_, v_recArgInfos_2218_, v_a_2219_, v_a_2220_, v_a_2221_, v_a_2222_);
lean_dec(v_a_2222_);
lean_dec_ref(v_a_2221_);
lean_dec(v_a_2220_);
lean_dec_ref(v_a_2219_);
return v_res_2224_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2(lean_object* v_fixedParamPerms_2225_, lean_object* v_xs_2226_, lean_object* v_as_2227_, size_t v_sz_2228_, size_t v_i_2229_, lean_object* v_bs_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_){
_start:
{
lean_object* v___x_2236_; 
v___x_2236_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___redArg(v_fixedParamPerms_2225_, v_xs_2226_, v_sz_2228_, v_i_2229_, v_bs_2230_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_);
return v___x_2236_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___boxed(lean_object* v_fixedParamPerms_2237_, lean_object* v_xs_2238_, lean_object* v_as_2239_, lean_object* v_sz_2240_, lean_object* v_i_2241_, lean_object* v_bs_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_){
_start:
{
size_t v_sz_boxed_2248_; size_t v_i_boxed_2249_; lean_object* v_res_2250_; 
v_sz_boxed_2248_ = lean_unbox_usize(v_sz_2240_);
lean_dec(v_sz_2240_);
v_i_boxed_2249_ = lean_unbox_usize(v_i_2241_);
lean_dec(v_i_2241_);
v_res_2250_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2(v_fixedParamPerms_2237_, v_xs_2238_, v_as_2239_, v_sz_boxed_2248_, v_i_boxed_2249_, v_bs_2242_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_);
lean_dec(v___y_2246_);
lean_dec_ref(v___y_2245_);
lean_dec(v___y_2244_);
lean_dec_ref(v___y_2243_);
lean_dec_ref(v_as_2239_);
lean_dec_ref(v_fixedParamPerms_2237_);
return v_res_2250_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3(lean_object* v_fixedParamPerms_2251_, lean_object* v_xs_2252_, lean_object* v_as_2253_, size_t v_sz_2254_, size_t v_i_2255_, lean_object* v_bs_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_){
_start:
{
lean_object* v___x_2262_; 
v___x_2262_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___redArg(v_fixedParamPerms_2251_, v_xs_2252_, v_sz_2254_, v_i_2255_, v_bs_2256_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_);
return v___x_2262_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___boxed(lean_object* v_fixedParamPerms_2263_, lean_object* v_xs_2264_, lean_object* v_as_2265_, lean_object* v_sz_2266_, lean_object* v_i_2267_, lean_object* v_bs_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_){
_start:
{
size_t v_sz_boxed_2274_; size_t v_i_boxed_2275_; lean_object* v_res_2276_; 
v_sz_boxed_2274_ = lean_unbox_usize(v_sz_2266_);
lean_dec(v_sz_2266_);
v_i_boxed_2275_ = lean_unbox_usize(v_i_2267_);
lean_dec(v_i_2267_);
v_res_2276_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3(v_fixedParamPerms_2263_, v_xs_2264_, v_as_2265_, v_sz_boxed_2274_, v_i_boxed_2275_, v_bs_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_);
lean_dec(v___y_2272_);
lean_dec_ref(v___y_2271_);
lean_dec(v___y_2270_);
lean_dec_ref(v___y_2269_);
lean_dec_ref(v_as_2265_);
lean_dec_ref(v_fixedParamPerms_2263_);
return v_res_2276_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14(lean_object* v_00_u03b3_2277_, lean_object* v_msg_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_){
_start:
{
lean_object* v___x_2284_; 
v___x_2284_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg(v_msg_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_);
return v___x_2284_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___boxed(lean_object* v_00_u03b3_2285_, lean_object* v_msg_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_){
_start:
{
lean_object* v_res_2292_; 
v_res_2292_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14(v_00_u03b3_2285_, v_msg_2286_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_);
lean_dec(v___y_2290_);
lean_dec_ref(v___y_2289_);
lean_dec(v___y_2288_);
lean_dec_ref(v___y_2287_);
return v_res_2292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6(lean_object* v_00_u03b3_2293_, lean_object* v_00_u03b1_2294_, lean_object* v_f_2295_, lean_object* v_positions_2296_, lean_object* v_ys_2297_, lean_object* v_xs_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_){
_start:
{
lean_object* v___x_2304_; 
v___x_2304_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg(v_f_2295_, v_positions_2296_, v_ys_2297_, v_xs_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_);
return v___x_2304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___boxed(lean_object* v_00_u03b3_2305_, lean_object* v_00_u03b1_2306_, lean_object* v_f_2307_, lean_object* v_positions_2308_, lean_object* v_ys_2309_, lean_object* v_xs_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_){
_start:
{
lean_object* v_res_2316_; 
v_res_2316_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6(v_00_u03b3_2305_, v_00_u03b1_2306_, v_f_2307_, v_positions_2308_, v_ys_2309_, v_xs_2310_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_);
lean_dec(v___y_2314_);
lean_dec_ref(v___y_2313_);
lean_dec(v___y_2312_);
lean_dec_ref(v___y_2311_);
lean_dec_ref(v_xs_2310_);
lean_dec_ref(v_ys_2309_);
lean_dec_ref(v_positions_2308_);
return v_res_2316_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7(lean_object* v___x_2317_, lean_object* v_a_2318_, lean_object* v_a_2319_, lean_object* v_funTypes_2320_, lean_object* v_as_2321_, size_t v_sz_2322_, size_t v_i_2323_, lean_object* v_bs_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_){
_start:
{
lean_object* v___x_2330_; 
v___x_2330_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg(v___x_2317_, v_a_2318_, v_a_2319_, v_funTypes_2320_, v_sz_2322_, v_i_2323_, v_bs_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_);
return v___x_2330_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___boxed(lean_object* v___x_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_, lean_object* v_funTypes_2334_, lean_object* v_as_2335_, lean_object* v_sz_2336_, lean_object* v_i_2337_, lean_object* v_bs_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_){
_start:
{
size_t v_sz_boxed_2344_; size_t v_i_boxed_2345_; lean_object* v_res_2346_; 
v_sz_boxed_2344_ = lean_unbox_usize(v_sz_2336_);
lean_dec(v_sz_2336_);
v_i_boxed_2345_ = lean_unbox_usize(v_i_2337_);
lean_dec(v_i_2337_);
v_res_2346_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7(v___x_2331_, v_a_2332_, v_a_2333_, v_funTypes_2334_, v_as_2335_, v_sz_boxed_2344_, v_i_boxed_2345_, v_bs_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_);
lean_dec(v___y_2342_);
lean_dec_ref(v___y_2341_);
lean_dec(v___y_2340_);
lean_dec_ref(v___y_2339_);
lean_dec_ref(v_as_2335_);
return v_res_2346_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8(lean_object* v_fixedParamPerms_2347_, lean_object* v_xs_2348_, lean_object* v_as_2349_, size_t v_sz_2350_, size_t v_i_2351_, lean_object* v_bs_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_){
_start:
{
lean_object* v___x_2358_; 
v___x_2358_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg(v_fixedParamPerms_2347_, v_xs_2348_, v_sz_2350_, v_i_2351_, v_bs_2352_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_);
return v___x_2358_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___boxed(lean_object* v_fixedParamPerms_2359_, lean_object* v_xs_2360_, lean_object* v_as_2361_, lean_object* v_sz_2362_, lean_object* v_i_2363_, lean_object* v_bs_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_){
_start:
{
size_t v_sz_boxed_2370_; size_t v_i_boxed_2371_; lean_object* v_res_2372_; 
v_sz_boxed_2370_ = lean_unbox_usize(v_sz_2362_);
lean_dec(v_sz_2362_);
v_i_boxed_2371_ = lean_unbox_usize(v_i_2363_);
lean_dec(v_i_2363_);
v_res_2372_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8(v_fixedParamPerms_2359_, v_xs_2360_, v_as_2361_, v_sz_boxed_2370_, v_i_boxed_2371_, v_bs_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_);
lean_dec(v___y_2368_);
lean_dec_ref(v___y_2367_);
lean_dec(v___y_2366_);
lean_dec_ref(v___y_2365_);
lean_dec_ref(v_as_2361_);
return v_res_2372_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12(lean_object* v_00_u03b1_2373_, lean_object* v_preDefs_2374_, lean_object* v_k_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_){
_start:
{
lean_object* v___x_2381_; 
v___x_2381_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v_preDefs_2374_, v_k_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_);
return v___x_2381_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___boxed(lean_object* v_00_u03b1_2382_, lean_object* v_preDefs_2383_, lean_object* v_k_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_){
_start:
{
lean_object* v_res_2390_; 
v_res_2390_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12(v_00_u03b1_2382_, v_preDefs_2383_, v_k_2384_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_);
lean_dec(v___y_2388_);
lean_dec_ref(v___y_2387_);
lean_dec(v___y_2386_);
lean_dec_ref(v___y_2385_);
return v_res_2390_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14(uint8_t v_a_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_recArgInfos_2394_, lean_object* v___x_2395_, lean_object* v_preDefs_2396_, lean_object* v_a_2397_, lean_object* v_as_2398_, size_t v_sz_2399_, size_t v_i_2400_, lean_object* v_bs_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_){
_start:
{
lean_object* v___x_2407_; 
v___x_2407_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg(v_a_2391_, v_a_2392_, v_a_2393_, v_recArgInfos_2394_, v___x_2395_, v_preDefs_2396_, v_a_2397_, v_sz_2399_, v_i_2400_, v_bs_2401_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_);
return v___x_2407_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___boxed(lean_object* v_a_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_, lean_object* v_recArgInfos_2411_, lean_object* v___x_2412_, lean_object* v_preDefs_2413_, lean_object* v_a_2414_, lean_object* v_as_2415_, lean_object* v_sz_2416_, lean_object* v_i_2417_, lean_object* v_bs_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_){
_start:
{
uint8_t v_a_30318__boxed_2424_; size_t v_sz_boxed_2425_; size_t v_i_boxed_2426_; lean_object* v_res_2427_; 
v_a_30318__boxed_2424_ = lean_unbox(v_a_2408_);
v_sz_boxed_2425_ = lean_unbox_usize(v_sz_2416_);
lean_dec(v_sz_2416_);
v_i_boxed_2426_ = lean_unbox_usize(v_i_2417_);
lean_dec(v_i_2417_);
v_res_2427_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14(v_a_30318__boxed_2424_, v_a_2409_, v_a_2410_, v_recArgInfos_2411_, v___x_2412_, v_preDefs_2413_, v_a_2414_, v_as_2415_, v_sz_boxed_2425_, v_i_boxed_2426_, v_bs_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_);
lean_dec(v___y_2422_);
lean_dec_ref(v___y_2421_);
lean_dec(v___y_2420_);
lean_dec_ref(v___y_2419_);
lean_dec_ref(v_as_2415_);
lean_dec_ref(v_a_2410_);
lean_dec_ref(v_a_2409_);
return v_res_2427_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16_spec__29(lean_object* v_declName_2428_, uint8_t v_s_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_){
_start:
{
lean_object* v___x_2435_; 
v___x_2435_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16_spec__29___redArg(v_declName_2428_, v_s_2429_, v___y_2431_, v___y_2433_);
return v___x_2435_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16_spec__29___boxed(lean_object* v_declName_2436_, lean_object* v_s_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_){
_start:
{
uint8_t v_s_boxed_2443_; lean_object* v_res_2444_; 
v_s_boxed_2443_ = lean_unbox(v_s_2437_);
v_res_2444_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16_spec__29(v_declName_2436_, v_s_boxed_2443_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_);
lean_dec(v___y_2441_);
lean_dec_ref(v___y_2440_);
lean_dec(v___y_2439_);
lean_dec_ref(v___y_2438_);
return v_res_2444_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17(lean_object* v_xs_2445_, uint8_t v_a_2446_, lean_object* v_preDefs_2447_, lean_object* v___x_2448_, lean_object* v_as_2449_, size_t v_sz_2450_, size_t v_i_2451_, lean_object* v_bs_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_){
_start:
{
lean_object* v___x_2458_; 
v___x_2458_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg(v_xs_2445_, v_a_2446_, v_preDefs_2447_, v___x_2448_, v_sz_2450_, v_i_2451_, v_bs_2452_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_);
return v___x_2458_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___boxed(lean_object* v_xs_2459_, lean_object* v_a_2460_, lean_object* v_preDefs_2461_, lean_object* v___x_2462_, lean_object* v_as_2463_, lean_object* v_sz_2464_, lean_object* v_i_2465_, lean_object* v_bs_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_){
_start:
{
uint8_t v_a_30367__boxed_2472_; size_t v_sz_boxed_2473_; size_t v_i_boxed_2474_; lean_object* v_res_2475_; 
v_a_30367__boxed_2472_ = lean_unbox(v_a_2460_);
v_sz_boxed_2473_ = lean_unbox_usize(v_sz_2464_);
lean_dec(v_sz_2464_);
v_i_boxed_2474_ = lean_unbox_usize(v_i_2465_);
lean_dec(v_i_2465_);
v_res_2475_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17(v_xs_2459_, v_a_30367__boxed_2472_, v_preDefs_2461_, v___x_2462_, v_as_2463_, v_sz_boxed_2473_, v_i_boxed_2474_, v_bs_2466_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_);
lean_dec(v___y_2470_);
lean_dec_ref(v___y_2469_);
lean_dec(v___y_2468_);
lean_dec_ref(v___y_2467_);
lean_dec_ref(v_as_2463_);
lean_dec_ref(v_preDefs_2461_);
lean_dec_ref(v_xs_2459_);
return v_res_2475_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18(lean_object* v_a_2476_, lean_object* v_funTypes_2477_, lean_object* v_as_2478_, size_t v_sz_2479_, size_t v_i_2480_, lean_object* v_bs_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_){
_start:
{
lean_object* v___x_2487_; 
v___x_2487_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___redArg(v_a_2476_, v_funTypes_2477_, v_sz_2479_, v_i_2480_, v_bs_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_);
return v___x_2487_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___boxed(lean_object* v_a_2488_, lean_object* v_funTypes_2489_, lean_object* v_as_2490_, lean_object* v_sz_2491_, lean_object* v_i_2492_, lean_object* v_bs_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_){
_start:
{
size_t v_sz_boxed_2499_; size_t v_i_boxed_2500_; lean_object* v_res_2501_; 
v_sz_boxed_2499_ = lean_unbox_usize(v_sz_2491_);
lean_dec(v_sz_2491_);
v_i_boxed_2500_ = lean_unbox_usize(v_i_2492_);
lean_dec(v_i_2492_);
v_res_2501_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18(v_a_2488_, v_funTypes_2489_, v_as_2490_, v_sz_boxed_2499_, v_i_boxed_2500_, v_bs_2493_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_);
lean_dec(v___y_2497_);
lean_dec_ref(v___y_2496_);
lean_dec(v___y_2495_);
lean_dec_ref(v___y_2494_);
lean_dec_ref(v_as_2490_);
lean_dec_ref(v_funTypes_2489_);
lean_dec_ref(v_a_2488_);
return v_res_2501_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19(lean_object* v_a_2502_, lean_object* v_a_2503_, lean_object* v_as_2504_, size_t v_sz_2505_, size_t v_i_2506_, lean_object* v_bs_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_){
_start:
{
lean_object* v___x_2513_; 
v___x_2513_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___redArg(v_a_2502_, v_a_2503_, v_sz_2505_, v_i_2506_, v_bs_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_);
return v___x_2513_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___boxed(lean_object* v_a_2514_, lean_object* v_a_2515_, lean_object* v_as_2516_, lean_object* v_sz_2517_, lean_object* v_i_2518_, lean_object* v_bs_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_){
_start:
{
size_t v_sz_boxed_2525_; size_t v_i_boxed_2526_; lean_object* v_res_2527_; 
v_sz_boxed_2525_ = lean_unbox_usize(v_sz_2517_);
lean_dec(v_sz_2517_);
v_i_boxed_2526_ = lean_unbox_usize(v_i_2518_);
lean_dec(v_i_2518_);
v_res_2527_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19(v_a_2514_, v_a_2515_, v_as_2516_, v_sz_boxed_2525_, v_i_boxed_2526_, v_bs_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_);
lean_dec(v___y_2523_);
lean_dec_ref(v___y_2522_);
lean_dec(v___y_2521_);
lean_dec_ref(v___y_2520_);
lean_dec_ref(v_as_2516_);
lean_dec_ref(v_a_2515_);
lean_dec_ref(v_a_2514_);
return v_res_2527_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4(lean_object* v_00_u03b1_2528_, lean_object* v_msg_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_){
_start:
{
lean_object* v___x_2535_; 
v___x_2535_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg(v_msg_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_);
return v___x_2535_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___boxed(lean_object* v_00_u03b1_2536_, lean_object* v_msg_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_){
_start:
{
lean_object* v_res_2543_; 
v_res_2543_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4(v_00_u03b1_2536_, v_msg_2537_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_);
lean_dec(v___y_2541_);
lean_dec_ref(v___y_2540_);
lean_dec(v___y_2539_);
lean_dec_ref(v___y_2538_);
return v_res_2543_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9(lean_object* v_xs_2544_, lean_object* v_ys_2545_, lean_object* v_hsz_2546_, lean_object* v_x_2547_, lean_object* v_x_2548_){
_start:
{
uint8_t v___x_2549_; 
v___x_2549_ = l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9___redArg(v_xs_2544_, v_ys_2545_, v_x_2547_);
return v___x_2549_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9___boxed(lean_object* v_xs_2550_, lean_object* v_ys_2551_, lean_object* v_hsz_2552_, lean_object* v_x_2553_, lean_object* v_x_2554_){
_start:
{
uint8_t v_res_2555_; lean_object* v_r_2556_; 
v_res_2555_ = l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9(v_xs_2550_, v_ys_2551_, v_hsz_2552_, v_x_2553_, v_x_2554_);
lean_dec_ref(v_ys_2551_);
lean_dec_ref(v_xs_2550_);
v_r_2556_ = lean_box(v_res_2555_);
return v_r_2556_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10(lean_object* v_n_2557_, lean_object* v_as_2558_, lean_object* v_lo_2559_, lean_object* v_hi_2560_, lean_object* v_w_2561_, lean_object* v_hlo_2562_, lean_object* v_hhi_2563_){
_start:
{
lean_object* v___x_2564_; 
v___x_2564_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg(v_n_2557_, v_as_2558_, v_lo_2559_, v_hi_2560_);
return v___x_2564_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___boxed(lean_object* v_n_2565_, lean_object* v_as_2566_, lean_object* v_lo_2567_, lean_object* v_hi_2568_, lean_object* v_w_2569_, lean_object* v_hlo_2570_, lean_object* v_hhi_2571_){
_start:
{
lean_object* v_res_2572_; 
v_res_2572_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10(v_n_2565_, v_as_2566_, v_lo_2567_, v_hi_2568_, v_w_2569_, v_hlo_2570_, v_hhi_2571_);
lean_dec(v_hi_2568_);
lean_dec(v_n_2565_);
return v_res_2572_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15(lean_object* v_00_u03b1_2573_, lean_object* v_00_u03b3_2574_, lean_object* v_xs_2575_, lean_object* v_f_2576_, lean_object* v_as_2577_, lean_object* v_bs_2578_, lean_object* v_i_2579_, lean_object* v_cs_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_){
_start:
{
lean_object* v___x_2586_; 
v___x_2586_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15___redArg(v_xs_2575_, v_f_2576_, v_as_2577_, v_bs_2578_, v_i_2579_, v_cs_2580_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_);
return v___x_2586_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15___boxed(lean_object* v_00_u03b1_2587_, lean_object* v_00_u03b3_2588_, lean_object* v_xs_2589_, lean_object* v_f_2590_, lean_object* v_as_2591_, lean_object* v_bs_2592_, lean_object* v_i_2593_, lean_object* v_cs_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_){
_start:
{
lean_object* v_res_2600_; 
v_res_2600_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15(v_00_u03b1_2587_, v_00_u03b3_2588_, v_xs_2589_, v_f_2590_, v_as_2591_, v_bs_2592_, v_i_2593_, v_cs_2594_, v___y_2595_, v___y_2596_, v___y_2597_, v___y_2598_);
lean_dec(v___y_2598_);
lean_dec_ref(v___y_2597_);
lean_dec(v___y_2596_);
lean_dec_ref(v___y_2595_);
lean_dec_ref(v_bs_2592_);
lean_dec_ref(v_as_2591_);
lean_dec_ref(v_xs_2589_);
return v_res_2600_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25(lean_object* v_env_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_){
_start:
{
lean_object* v___x_2607_; 
v___x_2607_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg(v_env_2601_, v___y_2603_, v___y_2605_);
return v___x_2607_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___boxed(lean_object* v_env_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_){
_start:
{
lean_object* v_res_2614_; 
v_res_2614_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25(v_env_2608_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_);
lean_dec(v___y_2612_);
lean_dec_ref(v___y_2611_);
lean_dec(v___y_2610_);
lean_dec_ref(v___y_2609_);
return v_res_2614_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23(lean_object* v_00_u03b1_2615_, lean_object* v_env_2616_, lean_object* v_x_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_){
_start:
{
lean_object* v___x_2623_; 
v___x_2623_ = l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23___redArg(v_env_2616_, v_x_2617_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_);
return v___x_2623_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23___boxed(lean_object* v_00_u03b1_2624_, lean_object* v_env_2625_, lean_object* v_x_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_){
_start:
{
lean_object* v_res_2632_; 
v_res_2632_ = l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23(v_00_u03b1_2624_, v_env_2625_, v_x_2626_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_);
lean_dec(v___y_2630_);
lean_dec_ref(v___y_2629_);
lean_dec(v___y_2628_);
lean_dec_ref(v___y_2627_);
return v_res_2632_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11(lean_object* v_n_2633_, lean_object* v_lo_2634_, lean_object* v_hi_2635_, lean_object* v_hhi_2636_, lean_object* v_pivot_2637_, lean_object* v_as_2638_, lean_object* v_i_2639_, lean_object* v_k_2640_, lean_object* v_ilo_2641_, lean_object* v_ik_2642_, lean_object* v_w_2643_){
_start:
{
lean_object* v___x_2644_; 
v___x_2644_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11___redArg(v_hi_2635_, v_pivot_2637_, v_as_2638_, v_i_2639_, v_k_2640_);
return v___x_2644_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11___boxed(lean_object* v_n_2645_, lean_object* v_lo_2646_, lean_object* v_hi_2647_, lean_object* v_hhi_2648_, lean_object* v_pivot_2649_, lean_object* v_as_2650_, lean_object* v_i_2651_, lean_object* v_k_2652_, lean_object* v_ilo_2653_, lean_object* v_ik_2654_, lean_object* v_w_2655_){
_start:
{
lean_object* v_res_2656_; 
v_res_2656_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11(v_n_2645_, v_lo_2646_, v_hi_2647_, v_hhi_2648_, v_pivot_2649_, v_as_2650_, v_i_2651_, v_k_2652_, v_ilo_2653_, v_ik_2654_, v_w_2655_);
lean_dec(v_pivot_2649_);
lean_dec(v_hi_2647_);
lean_dec(v_lo_2646_);
lean_dec(v_n_2645_);
return v_res_2656_;
}
}
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___lam__0(lean_object* v_x_2657_){
_start:
{
uint8_t v___x_2658_; 
v___x_2658_ = 0;
return v___x_2658_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___lam__0___boxed(lean_object* v_x_2659_){
_start:
{
uint8_t v_res_2660_; lean_object* v_r_2661_; 
v_res_2660_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___lam__0(v_x_2659_);
lean_dec(v_x_2659_);
v_r_2661_ = lean_box(v_res_2660_);
return v_r_2661_;
}
}
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___lam__1(lean_object* v_fvarId_2662_, lean_object* v_x_2663_){
_start:
{
uint8_t v___x_2664_; 
v___x_2664_ = l_Lean_instBEqFVarId_beq(v_fvarId_2662_, v_x_2663_);
return v___x_2664_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___lam__1___boxed(lean_object* v_fvarId_2665_, lean_object* v_x_2666_){
_start:
{
uint8_t v_res_2667_; lean_object* v_r_2668_; 
v_res_2667_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___lam__1(v_fvarId_2665_, v_x_2666_);
lean_dec(v_x_2666_);
lean_dec(v_fvarId_2665_);
v_r_2668_ = lean_box(v_res_2667_);
return v_r_2668_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; 
v___x_2670_ = lean_box(0);
v___x_2671_ = lean_unsigned_to_nat(16u);
v___x_2672_ = lean_mk_array(v___x_2671_, v___x_2670_);
return v___x_2672_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; 
v___x_2673_ = lean_obj_once(&l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__1, &l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__1_once, _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__1);
v___x_2674_ = lean_unsigned_to_nat(0u);
v___x_2675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2675_, 0, v___x_2674_);
lean_ctor_set(v___x_2675_, 1, v___x_2673_);
return v___x_2675_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg(lean_object* v_e_2676_, lean_object* v_fvarId_2677_, lean_object* v___y_2678_){
_start:
{
lean_object* v___x_2680_; uint8_t v_fst_2682_; lean_object* v_mctx_2683_; lean_object* v_mctx_2700_; lean_object* v___f_2701_; lean_object* v___f_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; uint8_t v___y_2706_; uint8_t v___x_2713_; uint8_t v___x_2714_; 
v___x_2680_ = lean_st_ref_get(v___y_2678_);
v_mctx_2700_ = lean_ctor_get(v___x_2680_, 0);
lean_inc_ref_n(v_mctx_2700_, 2);
lean_dec(v___x_2680_);
v___f_2701_ = ((lean_object*)(l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__0));
v___f_2702_ = lean_alloc_closure((void*)(l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_2702_, 0, v_fvarId_2677_);
v___x_2703_ = lean_obj_once(&l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__2, &l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__2_once, _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__2);
v___x_2704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2704_, 0, v___x_2703_);
lean_ctor_set(v___x_2704_, 1, v_mctx_2700_);
v___x_2713_ = l_Lean_Expr_hasFVar(v_e_2676_);
v___x_2714_ = lean_bool_not(v___x_2713_);
if (v___x_2714_ == 0)
{
v___y_2706_ = v___x_2714_;
goto v___jp_2705_;
}
else
{
uint8_t v___x_2715_; uint8_t v___x_2716_; 
v___x_2715_ = l_Lean_Expr_hasMVar(v_e_2676_);
v___x_2716_ = lean_bool_not(v___x_2715_);
v___y_2706_ = v___x_2716_;
goto v___jp_2705_;
}
v___jp_2681_:
{
lean_object* v___x_2684_; lean_object* v_cache_2685_; lean_object* v_zetaDeltaFVarIds_2686_; lean_object* v_postponed_2687_; lean_object* v_diag_2688_; lean_object* v___x_2690_; uint8_t v_isShared_2691_; uint8_t v_isSharedCheck_2698_; 
v___x_2684_ = lean_st_ref_take(v___y_2678_);
v_cache_2685_ = lean_ctor_get(v___x_2684_, 1);
v_zetaDeltaFVarIds_2686_ = lean_ctor_get(v___x_2684_, 2);
v_postponed_2687_ = lean_ctor_get(v___x_2684_, 3);
v_diag_2688_ = lean_ctor_get(v___x_2684_, 4);
v_isSharedCheck_2698_ = !lean_is_exclusive(v___x_2684_);
if (v_isSharedCheck_2698_ == 0)
{
lean_object* v_unused_2699_; 
v_unused_2699_ = lean_ctor_get(v___x_2684_, 0);
lean_dec(v_unused_2699_);
v___x_2690_ = v___x_2684_;
v_isShared_2691_ = v_isSharedCheck_2698_;
goto v_resetjp_2689_;
}
else
{
lean_inc(v_diag_2688_);
lean_inc(v_postponed_2687_);
lean_inc(v_zetaDeltaFVarIds_2686_);
lean_inc(v_cache_2685_);
lean_dec(v___x_2684_);
v___x_2690_ = lean_box(0);
v_isShared_2691_ = v_isSharedCheck_2698_;
goto v_resetjp_2689_;
}
v_resetjp_2689_:
{
lean_object* v___x_2693_; 
if (v_isShared_2691_ == 0)
{
lean_ctor_set(v___x_2690_, 0, v_mctx_2683_);
v___x_2693_ = v___x_2690_;
goto v_reusejp_2692_;
}
else
{
lean_object* v_reuseFailAlloc_2697_; 
v_reuseFailAlloc_2697_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2697_, 0, v_mctx_2683_);
lean_ctor_set(v_reuseFailAlloc_2697_, 1, v_cache_2685_);
lean_ctor_set(v_reuseFailAlloc_2697_, 2, v_zetaDeltaFVarIds_2686_);
lean_ctor_set(v_reuseFailAlloc_2697_, 3, v_postponed_2687_);
lean_ctor_set(v_reuseFailAlloc_2697_, 4, v_diag_2688_);
v___x_2693_ = v_reuseFailAlloc_2697_;
goto v_reusejp_2692_;
}
v_reusejp_2692_:
{
lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; 
v___x_2694_ = lean_st_ref_set(v___y_2678_, v___x_2693_);
v___x_2695_ = lean_box(v_fst_2682_);
v___x_2696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2696_, 0, v___x_2695_);
return v___x_2696_;
}
}
}
v___jp_2705_:
{
if (v___y_2706_ == 0)
{
lean_object* v___x_2707_; lean_object* v_snd_2708_; lean_object* v_fst_2709_; lean_object* v_mctx_2710_; uint8_t v___x_2711_; 
lean_dec_ref(v_mctx_2700_);
v___x_2707_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2702_, v___f_2701_, v_e_2676_, v___x_2704_);
v_snd_2708_ = lean_ctor_get(v___x_2707_, 1);
lean_inc(v_snd_2708_);
v_fst_2709_ = lean_ctor_get(v___x_2707_, 0);
lean_inc(v_fst_2709_);
lean_dec_ref(v___x_2707_);
v_mctx_2710_ = lean_ctor_get(v_snd_2708_, 1);
lean_inc_ref(v_mctx_2710_);
lean_dec(v_snd_2708_);
v___x_2711_ = lean_unbox(v_fst_2709_);
lean_dec(v_fst_2709_);
v_fst_2682_ = v___x_2711_;
v_mctx_2683_ = v_mctx_2710_;
goto v___jp_2681_;
}
else
{
uint8_t v___x_2712_; 
lean_dec_ref_known(v___x_2704_, 2);
lean_dec_ref(v___f_2702_);
lean_dec_ref(v_e_2676_);
v___x_2712_ = 0;
v_fst_2682_ = v___x_2712_;
v_mctx_2683_ = v_mctx_2700_;
goto v___jp_2681_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___boxed(lean_object* v_e_2717_, lean_object* v_fvarId_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_){
_start:
{
lean_object* v_res_2721_; 
v_res_2721_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg(v_e_2717_, v_fvarId_2718_, v___y_2719_);
lean_dec(v___y_2719_);
return v_res_2721_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5(lean_object* v_e_2722_, lean_object* v_fvarId_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_){
_start:
{
lean_object* v___x_2729_; 
v___x_2729_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg(v_e_2722_, v_fvarId_2723_, v___y_2725_);
return v___x_2729_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___boxed(lean_object* v_e_2730_, lean_object* v_fvarId_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_){
_start:
{
lean_object* v_res_2737_; 
v_res_2737_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5(v_e_2730_, v_fvarId_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_);
lean_dec(v___y_2735_);
lean_dec_ref(v___y_2734_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
return v_res_2737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg___lam__0(lean_object* v_k_2738_, lean_object* v_b_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_){
_start:
{
lean_object* v___x_2745_; 
lean_inc(v___y_2743_);
lean_inc_ref(v___y_2742_);
lean_inc(v___y_2741_);
lean_inc_ref(v___y_2740_);
v___x_2745_ = lean_apply_6(v_k_2738_, v_b_2739_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_, lean_box(0));
return v___x_2745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg___lam__0___boxed(lean_object* v_k_2746_, lean_object* v_b_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_){
_start:
{
lean_object* v_res_2753_; 
v_res_2753_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg___lam__0(v_k_2746_, v_b_2747_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_);
lean_dec(v___y_2751_);
lean_dec_ref(v___y_2750_);
lean_dec(v___y_2749_);
lean_dec_ref(v___y_2748_);
return v_res_2753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg(lean_object* v_perm_2754_, lean_object* v_type_2755_, lean_object* v_k_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_){
_start:
{
lean_object* v___f_2762_; lean_object* v___x_2763_; 
v___f_2762_ = lean_alloc_closure((void*)(l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2762_, 0, v_k_2756_);
v___x_2763_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl(lean_box(0), v_perm_2754_, v_type_2755_, v___f_2762_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_);
if (lean_obj_tag(v___x_2763_) == 0)
{
lean_object* v_a_2764_; lean_object* v___x_2766_; uint8_t v_isShared_2767_; uint8_t v_isSharedCheck_2771_; 
v_a_2764_ = lean_ctor_get(v___x_2763_, 0);
v_isSharedCheck_2771_ = !lean_is_exclusive(v___x_2763_);
if (v_isSharedCheck_2771_ == 0)
{
v___x_2766_ = v___x_2763_;
v_isShared_2767_ = v_isSharedCheck_2771_;
goto v_resetjp_2765_;
}
else
{
lean_inc(v_a_2764_);
lean_dec(v___x_2763_);
v___x_2766_ = lean_box(0);
v_isShared_2767_ = v_isSharedCheck_2771_;
goto v_resetjp_2765_;
}
v_resetjp_2765_:
{
lean_object* v___x_2769_; 
if (v_isShared_2767_ == 0)
{
v___x_2769_ = v___x_2766_;
goto v_reusejp_2768_;
}
else
{
lean_object* v_reuseFailAlloc_2770_; 
v_reuseFailAlloc_2770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2770_, 0, v_a_2764_);
v___x_2769_ = v_reuseFailAlloc_2770_;
goto v_reusejp_2768_;
}
v_reusejp_2768_:
{
return v___x_2769_;
}
}
}
else
{
lean_object* v_a_2772_; lean_object* v___x_2774_; uint8_t v_isShared_2775_; uint8_t v_isSharedCheck_2779_; 
v_a_2772_ = lean_ctor_get(v___x_2763_, 0);
v_isSharedCheck_2779_ = !lean_is_exclusive(v___x_2763_);
if (v_isSharedCheck_2779_ == 0)
{
v___x_2774_ = v___x_2763_;
v_isShared_2775_ = v_isSharedCheck_2779_;
goto v_resetjp_2773_;
}
else
{
lean_inc(v_a_2772_);
lean_dec(v___x_2763_);
v___x_2774_ = lean_box(0);
v_isShared_2775_ = v_isSharedCheck_2779_;
goto v_resetjp_2773_;
}
v_resetjp_2773_:
{
lean_object* v___x_2777_; 
if (v_isShared_2775_ == 0)
{
v___x_2777_ = v___x_2774_;
goto v_reusejp_2776_;
}
else
{
lean_object* v_reuseFailAlloc_2778_; 
v_reuseFailAlloc_2778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2778_, 0, v_a_2772_);
v___x_2777_ = v_reuseFailAlloc_2778_;
goto v_reusejp_2776_;
}
v_reusejp_2776_:
{
return v___x_2777_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg___boxed(lean_object* v_perm_2780_, lean_object* v_type_2781_, lean_object* v_k_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_){
_start:
{
lean_object* v_res_2788_; 
v_res_2788_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg(v_perm_2780_, v_type_2781_, v_k_2782_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_);
lean_dec(v___y_2786_);
lean_dec_ref(v___y_2785_);
lean_dec(v___y_2784_);
lean_dec_ref(v___y_2783_);
return v_res_2788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13(lean_object* v_00_u03b1_2789_, lean_object* v_perm_2790_, lean_object* v_type_2791_, lean_object* v_k_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_){
_start:
{
lean_object* v___x_2798_; 
v___x_2798_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg(v_perm_2790_, v_type_2791_, v_k_2792_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_);
return v___x_2798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___boxed(lean_object* v_00_u03b1_2799_, lean_object* v_perm_2800_, lean_object* v_type_2801_, lean_object* v_k_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_){
_start:
{
lean_object* v_res_2808_; 
v_res_2808_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13(v_00_u03b1_2799_, v_perm_2800_, v_type_2801_, v_k_2802_, v___y_2803_, v___y_2804_, v___y_2805_, v___y_2806_);
lean_dec(v___y_2806_);
lean_dec_ref(v___y_2805_);
lean_dec(v___y_2804_);
lean_dec_ref(v___y_2803_);
return v_res_2808_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1(lean_object* v_a_2809_, lean_object* v_fst_2810_, lean_object* v_fst_2811_, lean_object* v___x_2812_, lean_object* v___x_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_){
_start:
{
lean_object* v___x_2819_; 
lean_inc_ref(v_fst_2810_);
v___x_2819_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion(v_a_2809_, v_fst_2810_, v_fst_2811_, v___x_2812_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_);
if (lean_obj_tag(v___x_2819_) == 0)
{
lean_object* v_a_2820_; lean_object* v___x_2822_; uint8_t v_isShared_2823_; uint8_t v_isSharedCheck_2829_; 
v_a_2820_ = lean_ctor_get(v___x_2819_, 0);
v_isSharedCheck_2829_ = !lean_is_exclusive(v___x_2819_);
if (v_isSharedCheck_2829_ == 0)
{
v___x_2822_ = v___x_2819_;
v_isShared_2823_ = v_isSharedCheck_2829_;
goto v_resetjp_2821_;
}
else
{
lean_inc(v_a_2820_);
lean_dec(v___x_2819_);
v___x_2822_ = lean_box(0);
v_isShared_2823_ = v_isSharedCheck_2829_;
goto v_resetjp_2821_;
}
v_resetjp_2821_:
{
lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2827_; 
v___x_2824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2824_, 0, v_a_2820_);
lean_ctor_set(v___x_2824_, 1, v_fst_2810_);
v___x_2825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2825_, 0, v___x_2813_);
lean_ctor_set(v___x_2825_, 1, v___x_2824_);
if (v_isShared_2823_ == 0)
{
lean_ctor_set(v___x_2822_, 0, v___x_2825_);
v___x_2827_ = v___x_2822_;
goto v_reusejp_2826_;
}
else
{
lean_object* v_reuseFailAlloc_2828_; 
v_reuseFailAlloc_2828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2828_, 0, v___x_2825_);
v___x_2827_ = v_reuseFailAlloc_2828_;
goto v_reusejp_2826_;
}
v_reusejp_2826_:
{
return v___x_2827_;
}
}
}
else
{
lean_object* v_a_2830_; lean_object* v___x_2832_; uint8_t v_isShared_2833_; uint8_t v_isSharedCheck_2837_; 
lean_dec_ref(v___x_2813_);
lean_dec_ref(v_fst_2810_);
v_a_2830_ = lean_ctor_get(v___x_2819_, 0);
v_isSharedCheck_2837_ = !lean_is_exclusive(v___x_2819_);
if (v_isSharedCheck_2837_ == 0)
{
v___x_2832_ = v___x_2819_;
v_isShared_2833_ = v_isSharedCheck_2837_;
goto v_resetjp_2831_;
}
else
{
lean_inc(v_a_2830_);
lean_dec(v___x_2819_);
v___x_2832_ = lean_box(0);
v_isShared_2833_ = v_isSharedCheck_2837_;
goto v_resetjp_2831_;
}
v_resetjp_2831_:
{
lean_object* v___x_2835_; 
if (v_isShared_2833_ == 0)
{
v___x_2835_ = v___x_2832_;
goto v_reusejp_2834_;
}
else
{
lean_object* v_reuseFailAlloc_2836_; 
v_reuseFailAlloc_2836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2836_, 0, v_a_2830_);
v___x_2835_ = v_reuseFailAlloc_2836_;
goto v_reusejp_2834_;
}
v_reusejp_2834_:
{
return v___x_2835_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___boxed(lean_object* v_a_2838_, lean_object* v_fst_2839_, lean_object* v_fst_2840_, lean_object* v___x_2841_, lean_object* v___x_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_){
_start:
{
lean_object* v_res_2848_; 
v_res_2848_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1(v_a_2838_, v_fst_2839_, v_fst_2840_, v___x_2841_, v___x_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_);
lean_dec(v___y_2846_);
lean_dec_ref(v___y_2845_);
lean_dec(v___y_2844_);
lean_dec_ref(v___y_2843_);
return v_res_2848_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__3(size_t v_sz_2849_, size_t v_i_2850_, lean_object* v_bs_2851_){
_start:
{
uint8_t v___x_2852_; 
v___x_2852_ = lean_usize_dec_lt(v_i_2850_, v_sz_2849_);
if (v___x_2852_ == 0)
{
return v_bs_2851_;
}
else
{
lean_object* v_v_2853_; lean_object* v___x_2854_; lean_object* v_bs_x27_2855_; lean_object* v___x_2856_; size_t v___x_2857_; size_t v___x_2858_; lean_object* v___x_2859_; 
v_v_2853_ = lean_array_uget(v_bs_2851_, v_i_2850_);
v___x_2854_ = lean_unsigned_to_nat(0u);
v_bs_x27_2855_ = lean_array_uset(v_bs_2851_, v_i_2850_, v___x_2854_);
v___x_2856_ = l_Lean_Elab_Structural_RecArgInfo_indicesAndRecArgPos(v_v_2853_);
v___x_2857_ = ((size_t)1ULL);
v___x_2858_ = lean_usize_add(v_i_2850_, v___x_2857_);
v___x_2859_ = lean_array_uset(v_bs_x27_2855_, v_i_2850_, v___x_2856_);
v_i_2850_ = v___x_2858_;
v_bs_2851_ = v___x_2859_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__3___boxed(lean_object* v_sz_2861_, lean_object* v_i_2862_, lean_object* v_bs_2863_){
_start:
{
size_t v_sz_boxed_2864_; size_t v_i_boxed_2865_; lean_object* v_res_2866_; 
v_sz_boxed_2864_ = lean_unbox_usize(v_sz_2861_);
lean_dec(v_sz_2861_);
v_i_boxed_2865_ = lean_unbox_usize(v_i_2862_);
lean_dec(v_i_2862_);
v_res_2866_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__3(v_sz_boxed_2864_, v_i_boxed_2865_, v_bs_2863_);
return v_res_2866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___redArg(lean_object* v_lctx_2867_, lean_object* v_localInsts_2868_, lean_object* v_x_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_){
_start:
{
lean_object* v___x_2875_; 
v___x_2875_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_2867_, v_localInsts_2868_, v_x_2869_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_);
if (lean_obj_tag(v___x_2875_) == 0)
{
lean_object* v_a_2876_; lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2883_; 
v_a_2876_ = lean_ctor_get(v___x_2875_, 0);
v_isSharedCheck_2883_ = !lean_is_exclusive(v___x_2875_);
if (v_isSharedCheck_2883_ == 0)
{
v___x_2878_ = v___x_2875_;
v_isShared_2879_ = v_isSharedCheck_2883_;
goto v_resetjp_2877_;
}
else
{
lean_inc(v_a_2876_);
lean_dec(v___x_2875_);
v___x_2878_ = lean_box(0);
v_isShared_2879_ = v_isSharedCheck_2883_;
goto v_resetjp_2877_;
}
v_resetjp_2877_:
{
lean_object* v___x_2881_; 
if (v_isShared_2879_ == 0)
{
v___x_2881_ = v___x_2878_;
goto v_reusejp_2880_;
}
else
{
lean_object* v_reuseFailAlloc_2882_; 
v_reuseFailAlloc_2882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2882_, 0, v_a_2876_);
v___x_2881_ = v_reuseFailAlloc_2882_;
goto v_reusejp_2880_;
}
v_reusejp_2880_:
{
return v___x_2881_;
}
}
}
else
{
lean_object* v_a_2884_; lean_object* v___x_2886_; uint8_t v_isShared_2887_; uint8_t v_isSharedCheck_2891_; 
v_a_2884_ = lean_ctor_get(v___x_2875_, 0);
v_isSharedCheck_2891_ = !lean_is_exclusive(v___x_2875_);
if (v_isSharedCheck_2891_ == 0)
{
v___x_2886_ = v___x_2875_;
v_isShared_2887_ = v_isSharedCheck_2891_;
goto v_resetjp_2885_;
}
else
{
lean_inc(v_a_2884_);
lean_dec(v___x_2875_);
v___x_2886_ = lean_box(0);
v_isShared_2887_ = v_isSharedCheck_2891_;
goto v_resetjp_2885_;
}
v_resetjp_2885_:
{
lean_object* v___x_2889_; 
if (v_isShared_2887_ == 0)
{
v___x_2889_ = v___x_2886_;
goto v_reusejp_2888_;
}
else
{
lean_object* v_reuseFailAlloc_2890_; 
v_reuseFailAlloc_2890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2890_, 0, v_a_2884_);
v___x_2889_ = v_reuseFailAlloc_2890_;
goto v_reusejp_2888_;
}
v_reusejp_2888_:
{
return v___x_2889_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___redArg___boxed(lean_object* v_lctx_2892_, lean_object* v_localInsts_2893_, lean_object* v_x_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_){
_start:
{
lean_object* v_res_2900_; 
v_res_2900_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___redArg(v_lctx_2892_, v_localInsts_2893_, v_x_2894_, v___y_2895_, v___y_2896_, v___y_2897_, v___y_2898_);
lean_dec(v___y_2898_);
lean_dec_ref(v___y_2897_);
lean_dec(v___y_2896_);
lean_dec_ref(v___y_2895_);
return v_res_2900_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__12(lean_object* v_as_2901_, size_t v_i_2902_, size_t v_stop_2903_, lean_object* v_b_2904_){
_start:
{
uint8_t v___x_2905_; 
v___x_2905_ = lean_usize_dec_eq(v_i_2902_, v_stop_2903_);
if (v___x_2905_ == 0)
{
lean_object* v___x_2906_; lean_object* v___x_2907_; size_t v___x_2908_; size_t v___x_2909_; 
v___x_2906_ = lean_array_uget_borrowed(v_as_2901_, v_i_2902_);
lean_inc(v___x_2906_);
v___x_2907_ = lean_local_ctx_erase(v_b_2904_, v___x_2906_);
v___x_2908_ = ((size_t)1ULL);
v___x_2909_ = lean_usize_add(v_i_2902_, v___x_2908_);
v_i_2902_ = v___x_2909_;
v_b_2904_ = v___x_2907_;
goto _start;
}
else
{
return v_b_2904_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__12___boxed(lean_object* v_as_2911_, lean_object* v_i_2912_, lean_object* v_stop_2913_, lean_object* v_b_2914_){
_start:
{
size_t v_i_boxed_2915_; size_t v_stop_boxed_2916_; lean_object* v_res_2917_; 
v_i_boxed_2915_ = lean_unbox_usize(v_i_2912_);
lean_dec(v_i_2912_);
v_stop_boxed_2916_ = lean_unbox_usize(v_stop_2913_);
lean_dec(v_stop_2913_);
v_res_2917_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__12(v_as_2911_, v_i_boxed_2915_, v_stop_boxed_2916_, v_b_2914_);
lean_dec_ref(v_as_2911_);
return v_res_2917_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9_spec__11(lean_object* v_a_2918_, lean_object* v_as_2919_, size_t v_i_2920_, size_t v_stop_2921_){
_start:
{
uint8_t v___x_2922_; 
v___x_2922_ = lean_usize_dec_eq(v_i_2920_, v_stop_2921_);
if (v___x_2922_ == 0)
{
lean_object* v___x_2923_; uint8_t v___x_2924_; 
v___x_2923_ = lean_array_uget_borrowed(v_as_2919_, v_i_2920_);
v___x_2924_ = l_Lean_instBEqFVarId_beq(v_a_2918_, v___x_2923_);
if (v___x_2924_ == 0)
{
size_t v___x_2925_; size_t v___x_2926_; 
v___x_2925_ = ((size_t)1ULL);
v___x_2926_ = lean_usize_add(v_i_2920_, v___x_2925_);
v_i_2920_ = v___x_2926_;
goto _start;
}
else
{
return v___x_2924_;
}
}
else
{
uint8_t v___x_2928_; 
v___x_2928_ = 0;
return v___x_2928_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9_spec__11___boxed(lean_object* v_a_2929_, lean_object* v_as_2930_, lean_object* v_i_2931_, lean_object* v_stop_2932_){
_start:
{
size_t v_i_boxed_2933_; size_t v_stop_boxed_2934_; uint8_t v_res_2935_; lean_object* v_r_2936_; 
v_i_boxed_2933_ = lean_unbox_usize(v_i_2931_);
lean_dec(v_i_2931_);
v_stop_boxed_2934_ = lean_unbox_usize(v_stop_2932_);
lean_dec(v_stop_2932_);
v_res_2935_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9_spec__11(v_a_2929_, v_as_2930_, v_i_boxed_2933_, v_stop_boxed_2934_);
lean_dec_ref(v_as_2930_);
lean_dec(v_a_2929_);
v_r_2936_ = lean_box(v_res_2935_);
return v_r_2936_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9(lean_object* v_as_2937_, lean_object* v_a_2938_){
_start:
{
lean_object* v___x_2939_; lean_object* v___x_2940_; uint8_t v___x_2941_; 
v___x_2939_ = lean_unsigned_to_nat(0u);
v___x_2940_ = lean_array_get_size(v_as_2937_);
v___x_2941_ = lean_nat_dec_lt(v___x_2939_, v___x_2940_);
if (v___x_2941_ == 0)
{
return v___x_2941_;
}
else
{
if (v___x_2941_ == 0)
{
return v___x_2941_;
}
else
{
size_t v___x_2942_; size_t v___x_2943_; uint8_t v___x_2944_; 
v___x_2942_ = ((size_t)0ULL);
v___x_2943_ = lean_usize_of_nat(v___x_2940_);
v___x_2944_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9_spec__11(v_a_2938_, v_as_2937_, v___x_2942_, v___x_2943_);
return v___x_2944_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9___boxed(lean_object* v_as_2945_, lean_object* v_a_2946_){
_start:
{
uint8_t v_res_2947_; lean_object* v_r_2948_; 
v_res_2947_ = l_Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9(v_as_2945_, v_a_2946_);
lean_dec(v_a_2946_);
lean_dec_ref(v_as_2945_);
v_r_2948_ = lean_box(v_res_2947_);
return v_r_2948_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__11(lean_object* v_fvarIds_2949_, lean_object* v_as_2950_, size_t v_i_2951_, size_t v_stop_2952_, lean_object* v_b_2953_){
_start:
{
lean_object* v___y_2955_; uint8_t v___x_2959_; 
v___x_2959_ = lean_usize_dec_eq(v_i_2951_, v_stop_2952_);
if (v___x_2959_ == 0)
{
lean_object* v___x_2960_; lean_object* v_fvar_2961_; lean_object* v___x_2962_; uint8_t v___x_2963_; uint8_t v___x_2964_; 
v___x_2960_ = lean_array_uget_borrowed(v_as_2950_, v_i_2951_);
v_fvar_2961_ = lean_ctor_get(v___x_2960_, 1);
v___x_2962_ = l_Lean_Expr_fvarId_x21(v_fvar_2961_);
v___x_2963_ = l_Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9(v_fvarIds_2949_, v___x_2962_);
lean_dec(v___x_2962_);
v___x_2964_ = lean_bool_not(v___x_2963_);
if (v___x_2964_ == 0)
{
v___y_2955_ = v_b_2953_;
goto v___jp_2954_;
}
else
{
lean_object* v___x_2965_; 
lean_inc(v___x_2960_);
v___x_2965_ = lean_array_push(v_b_2953_, v___x_2960_);
v___y_2955_ = v___x_2965_;
goto v___jp_2954_;
}
}
else
{
return v_b_2953_;
}
v___jp_2954_:
{
size_t v___x_2956_; size_t v___x_2957_; 
v___x_2956_ = ((size_t)1ULL);
v___x_2957_ = lean_usize_add(v_i_2951_, v___x_2956_);
v_i_2951_ = v___x_2957_;
v_b_2953_ = v___y_2955_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__11___boxed(lean_object* v_fvarIds_2966_, lean_object* v_as_2967_, lean_object* v_i_2968_, lean_object* v_stop_2969_, lean_object* v_b_2970_){
_start:
{
size_t v_i_boxed_2971_; size_t v_stop_boxed_2972_; lean_object* v_res_2973_; 
v_i_boxed_2971_ = lean_unbox_usize(v_i_2968_);
lean_dec(v_i_2968_);
v_stop_boxed_2972_ = lean_unbox_usize(v_stop_2969_);
lean_dec(v_stop_2969_);
v_res_2973_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__11(v_fvarIds_2966_, v_as_2967_, v_i_boxed_2971_, v_stop_boxed_2972_, v_b_2970_);
lean_dec_ref(v_as_2967_);
lean_dec_ref(v_fvarIds_2966_);
return v_res_2973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___redArg(lean_object* v_fvarIds_2976_, lean_object* v_k_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_){
_start:
{
lean_object* v_lctx_2983_; lean_object* v_localInstances_2984_; lean_object* v___x_2985_; lean_object* v___y_2987_; lean_object* v___x_3002_; uint8_t v___x_3003_; 
v_lctx_2983_ = lean_ctor_get(v___y_2978_, 2);
v_localInstances_2984_ = lean_ctor_get(v___y_2978_, 3);
v___x_2985_ = lean_unsigned_to_nat(0u);
v___x_3002_ = lean_array_get_size(v_fvarIds_2976_);
v___x_3003_ = lean_nat_dec_lt(v___x_2985_, v___x_3002_);
if (v___x_3003_ == 0)
{
lean_inc_ref(v_lctx_2983_);
v___y_2987_ = v_lctx_2983_;
goto v___jp_2986_;
}
else
{
uint8_t v___x_3004_; 
v___x_3004_ = lean_nat_dec_le(v___x_3002_, v___x_3002_);
if (v___x_3004_ == 0)
{
if (v___x_3003_ == 0)
{
lean_inc_ref(v_lctx_2983_);
v___y_2987_ = v_lctx_2983_;
goto v___jp_2986_;
}
else
{
size_t v___x_3005_; size_t v___x_3006_; lean_object* v___x_3007_; 
v___x_3005_ = ((size_t)0ULL);
v___x_3006_ = lean_usize_of_nat(v___x_3002_);
lean_inc_ref(v_lctx_2983_);
v___x_3007_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__12(v_fvarIds_2976_, v___x_3005_, v___x_3006_, v_lctx_2983_);
v___y_2987_ = v___x_3007_;
goto v___jp_2986_;
}
}
else
{
size_t v___x_3008_; size_t v___x_3009_; lean_object* v___x_3010_; 
v___x_3008_ = ((size_t)0ULL);
v___x_3009_ = lean_usize_of_nat(v___x_3002_);
lean_inc_ref(v_lctx_2983_);
v___x_3010_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__12(v_fvarIds_2976_, v___x_3008_, v___x_3009_, v_lctx_2983_);
v___y_2987_ = v___x_3010_;
goto v___jp_2986_;
}
}
v___jp_2986_:
{
lean_object* v___x_2988_; lean_object* v___x_2989_; uint8_t v___x_2990_; 
v___x_2988_ = lean_array_get_size(v_localInstances_2984_);
v___x_2989_ = ((lean_object*)(l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___redArg___closed__0));
v___x_2990_ = lean_nat_dec_lt(v___x_2985_, v___x_2988_);
if (v___x_2990_ == 0)
{
lean_object* v___x_2991_; 
v___x_2991_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___redArg(v___y_2987_, v___x_2989_, v_k_2977_, v___y_2978_, v___y_2979_, v___y_2980_, v___y_2981_);
return v___x_2991_;
}
else
{
uint8_t v___x_2992_; 
v___x_2992_ = lean_nat_dec_le(v___x_2988_, v___x_2988_);
if (v___x_2992_ == 0)
{
if (v___x_2990_ == 0)
{
lean_object* v___x_2993_; 
v___x_2993_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___redArg(v___y_2987_, v___x_2989_, v_k_2977_, v___y_2978_, v___y_2979_, v___y_2980_, v___y_2981_);
return v___x_2993_;
}
else
{
size_t v___x_2994_; size_t v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; 
v___x_2994_ = ((size_t)0ULL);
v___x_2995_ = lean_usize_of_nat(v___x_2988_);
v___x_2996_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__11(v_fvarIds_2976_, v_localInstances_2984_, v___x_2994_, v___x_2995_, v___x_2989_);
v___x_2997_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___redArg(v___y_2987_, v___x_2996_, v_k_2977_, v___y_2978_, v___y_2979_, v___y_2980_, v___y_2981_);
return v___x_2997_;
}
}
else
{
size_t v___x_2998_; size_t v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; 
v___x_2998_ = ((size_t)0ULL);
v___x_2999_ = lean_usize_of_nat(v___x_2988_);
v___x_3000_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__11(v_fvarIds_2976_, v_localInstances_2984_, v___x_2998_, v___x_2999_, v___x_2989_);
v___x_3001_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___redArg(v___y_2987_, v___x_3000_, v_k_2977_, v___y_2978_, v___y_2979_, v___y_2980_, v___y_2981_);
return v___x_3001_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___redArg___boxed(lean_object* v_fvarIds_3011_, lean_object* v_k_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_){
_start:
{
lean_object* v_res_3018_; 
v_res_3018_ = l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___redArg(v_fvarIds_3011_, v_k_3012_, v___y_3013_, v___y_3014_, v___y_3015_, v___y_3016_);
lean_dec(v___y_3016_);
lean_dec_ref(v___y_3015_);
lean_dec(v___y_3014_);
lean_dec_ref(v___y_3013_);
lean_dec_ref(v_fvarIds_3011_);
return v_res_3018_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__14_spec__17_spec__21(lean_object* v_x_3019_, lean_object* v_x_3020_, lean_object* v_x_3021_){
_start:
{
if (lean_obj_tag(v_x_3021_) == 0)
{
lean_dec(v_x_3019_);
return v_x_3020_;
}
else
{
lean_object* v_head_3022_; lean_object* v_tail_3023_; lean_object* v___x_3025_; uint8_t v_isShared_3026_; uint8_t v_isSharedCheck_3033_; 
v_head_3022_ = lean_ctor_get(v_x_3021_, 0);
v_tail_3023_ = lean_ctor_get(v_x_3021_, 1);
v_isSharedCheck_3033_ = !lean_is_exclusive(v_x_3021_);
if (v_isSharedCheck_3033_ == 0)
{
v___x_3025_ = v_x_3021_;
v_isShared_3026_ = v_isSharedCheck_3033_;
goto v_resetjp_3024_;
}
else
{
lean_inc(v_tail_3023_);
lean_inc(v_head_3022_);
lean_dec(v_x_3021_);
v___x_3025_ = lean_box(0);
v_isShared_3026_ = v_isSharedCheck_3033_;
goto v_resetjp_3024_;
}
v_resetjp_3024_:
{
lean_object* v___x_3028_; 
lean_inc(v_x_3019_);
if (v_isShared_3026_ == 0)
{
lean_ctor_set_tag(v___x_3025_, 5);
lean_ctor_set(v___x_3025_, 1, v_x_3019_);
lean_ctor_set(v___x_3025_, 0, v_x_3020_);
v___x_3028_ = v___x_3025_;
goto v_reusejp_3027_;
}
else
{
lean_object* v_reuseFailAlloc_3032_; 
v_reuseFailAlloc_3032_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3032_, 0, v_x_3020_);
lean_ctor_set(v_reuseFailAlloc_3032_, 1, v_x_3019_);
v___x_3028_ = v_reuseFailAlloc_3032_;
goto v_reusejp_3027_;
}
v_reusejp_3027_:
{
lean_object* v___x_3029_; lean_object* v___x_3030_; 
v___x_3029_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(v_head_3022_);
v___x_3030_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3030_, 0, v___x_3028_);
lean_ctor_set(v___x_3030_, 1, v___x_3029_);
v_x_3020_ = v___x_3030_;
v_x_3021_ = v_tail_3023_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__14_spec__17(lean_object* v_x_3034_, lean_object* v_x_3035_, lean_object* v_x_3036_){
_start:
{
if (lean_obj_tag(v_x_3036_) == 0)
{
lean_dec(v_x_3034_);
return v_x_3035_;
}
else
{
lean_object* v_head_3037_; lean_object* v_tail_3038_; lean_object* v___x_3040_; uint8_t v_isShared_3041_; uint8_t v_isSharedCheck_3048_; 
v_head_3037_ = lean_ctor_get(v_x_3036_, 0);
v_tail_3038_ = lean_ctor_get(v_x_3036_, 1);
v_isSharedCheck_3048_ = !lean_is_exclusive(v_x_3036_);
if (v_isSharedCheck_3048_ == 0)
{
v___x_3040_ = v_x_3036_;
v_isShared_3041_ = v_isSharedCheck_3048_;
goto v_resetjp_3039_;
}
else
{
lean_inc(v_tail_3038_);
lean_inc(v_head_3037_);
lean_dec(v_x_3036_);
v___x_3040_ = lean_box(0);
v_isShared_3041_ = v_isSharedCheck_3048_;
goto v_resetjp_3039_;
}
v_resetjp_3039_:
{
lean_object* v___x_3043_; 
lean_inc(v_x_3034_);
if (v_isShared_3041_ == 0)
{
lean_ctor_set_tag(v___x_3040_, 5);
lean_ctor_set(v___x_3040_, 1, v_x_3034_);
lean_ctor_set(v___x_3040_, 0, v_x_3035_);
v___x_3043_ = v___x_3040_;
goto v_reusejp_3042_;
}
else
{
lean_object* v_reuseFailAlloc_3047_; 
v_reuseFailAlloc_3047_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3047_, 0, v_x_3035_);
lean_ctor_set(v_reuseFailAlloc_3047_, 1, v_x_3034_);
v___x_3043_ = v_reuseFailAlloc_3047_;
goto v_reusejp_3042_;
}
v_reusejp_3042_:
{
lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; 
v___x_3044_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(v_head_3037_);
v___x_3045_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3045_, 0, v___x_3043_);
lean_ctor_set(v___x_3045_, 1, v___x_3044_);
v___x_3046_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__14_spec__17_spec__21(v_x_3034_, v___x_3045_, v_tail_3038_);
return v___x_3046_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__14(lean_object* v_x_3049_, lean_object* v_x_3050_){
_start:
{
if (lean_obj_tag(v_x_3049_) == 0)
{
lean_object* v___x_3051_; 
lean_dec(v_x_3050_);
v___x_3051_ = lean_box(0);
return v___x_3051_;
}
else
{
lean_object* v_tail_3052_; 
v_tail_3052_ = lean_ctor_get(v_x_3049_, 1);
if (lean_obj_tag(v_tail_3052_) == 0)
{
lean_object* v_head_3053_; lean_object* v___x_3054_; 
lean_dec(v_x_3050_);
v_head_3053_ = lean_ctor_get(v_x_3049_, 0);
lean_inc(v_head_3053_);
lean_dec_ref_known(v_x_3049_, 2);
v___x_3054_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(v_head_3053_);
return v___x_3054_;
}
else
{
lean_object* v_head_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; 
lean_inc(v_tail_3052_);
v_head_3055_ = lean_ctor_get(v_x_3049_, 0);
lean_inc(v_head_3055_);
lean_dec_ref_known(v_x_3049_, 2);
v___x_3056_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(v_head_3055_);
v___x_3057_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__14_spec__17(v_x_3050_, v___x_3056_, v_tail_3052_);
return v___x_3057_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__5(void){
_start:
{
lean_object* v___x_3066_; lean_object* v___x_3067_; 
v___x_3066_ = ((lean_object*)(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__0));
v___x_3067_ = lean_string_length(v___x_3066_);
return v___x_3067_;
}
}
static lean_object* _init_l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__6(void){
_start:
{
lean_object* v___x_3068_; lean_object* v___x_3069_; 
v___x_3068_ = lean_obj_once(&l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__5, &l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__5_once, _init_l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__5);
v___x_3069_ = lean_nat_to_int(v___x_3068_);
return v___x_3069_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10(lean_object* v_xs_3077_){
_start:
{
lean_object* v___x_3078_; lean_object* v___x_3079_; uint8_t v___x_3080_; 
v___x_3078_ = lean_array_get_size(v_xs_3077_);
v___x_3079_ = lean_unsigned_to_nat(0u);
v___x_3080_ = lean_nat_dec_eq(v___x_3078_, v___x_3079_);
if (v___x_3080_ == 0)
{
lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; 
v___x_3081_ = lean_array_to_list(v_xs_3077_);
v___x_3082_ = ((lean_object*)(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__3));
v___x_3083_ = l_Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__14(v___x_3081_, v___x_3082_);
v___x_3084_ = lean_obj_once(&l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__6, &l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__6_once, _init_l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__6);
v___x_3085_ = ((lean_object*)(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__7));
v___x_3086_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3086_, 0, v___x_3085_);
lean_ctor_set(v___x_3086_, 1, v___x_3083_);
v___x_3087_ = ((lean_object*)(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__8));
v___x_3088_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3088_, 0, v___x_3086_);
lean_ctor_set(v___x_3088_, 1, v___x_3087_);
v___x_3089_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3089_, 0, v___x_3084_);
lean_ctor_set(v___x_3089_, 1, v___x_3088_);
v___x_3090_ = l_Std_Format_fill(v___x_3089_);
return v___x_3090_;
}
else
{
lean_object* v___x_3091_; 
lean_dec_ref(v_xs_3077_);
v___x_3091_ = ((lean_object*)(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__10));
return v___x_3091_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__11(size_t v_sz_3092_, size_t v_i_3093_, lean_object* v_bs_3094_){
_start:
{
uint8_t v___x_3095_; 
v___x_3095_ = lean_usize_dec_lt(v_i_3093_, v_sz_3092_);
if (v___x_3095_ == 0)
{
return v_bs_3094_;
}
else
{
lean_object* v_v_3096_; lean_object* v___x_3097_; lean_object* v_bs_x27_3098_; lean_object* v___x_3099_; size_t v___x_3100_; size_t v___x_3101_; lean_object* v___x_3102_; 
v_v_3096_ = lean_array_uget(v_bs_3094_, v_i_3093_);
v___x_3097_ = lean_unsigned_to_nat(0u);
v_bs_x27_3098_ = lean_array_uset(v_bs_3094_, v_i_3093_, v___x_3097_);
v___x_3099_ = l_Lean_mkFVar(v_v_3096_);
v___x_3100_ = ((size_t)1ULL);
v___x_3101_ = lean_usize_add(v_i_3093_, v___x_3100_);
v___x_3102_ = lean_array_uset(v_bs_x27_3098_, v_i_3093_, v___x_3099_);
v_i_3093_ = v___x_3101_;
v_bs_3094_ = v___x_3102_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__11___boxed(lean_object* v_sz_3104_, lean_object* v_i_3105_, lean_object* v_bs_3106_){
_start:
{
size_t v_sz_boxed_3107_; size_t v_i_boxed_3108_; lean_object* v_res_3109_; 
v_sz_boxed_3107_ = lean_unbox_usize(v_sz_3104_);
lean_dec(v_sz_3104_);
v_i_boxed_3108_ = lean_unbox_usize(v_i_3105_);
lean_dec(v_i_3105_);
v_res_3109_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__11(v_sz_boxed_3107_, v_i_boxed_3108_, v_bs_3106_);
return v_res_3109_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__2(size_t v_sz_3110_, size_t v_i_3111_, lean_object* v_bs_3112_){
_start:
{
uint8_t v___x_3113_; 
v___x_3113_ = lean_usize_dec_lt(v_i_3111_, v_sz_3110_);
if (v___x_3113_ == 0)
{
return v_bs_3112_;
}
else
{
lean_object* v_v_3114_; lean_object* v_recArgPos_3115_; lean_object* v___x_3116_; lean_object* v_bs_x27_3117_; size_t v___x_3118_; size_t v___x_3119_; lean_object* v___x_3120_; 
v_v_3114_ = lean_array_uget_borrowed(v_bs_3112_, v_i_3111_);
v_recArgPos_3115_ = lean_ctor_get(v_v_3114_, 2);
lean_inc(v_recArgPos_3115_);
v___x_3116_ = lean_unsigned_to_nat(0u);
v_bs_x27_3117_ = lean_array_uset(v_bs_3112_, v_i_3111_, v___x_3116_);
v___x_3118_ = ((size_t)1ULL);
v___x_3119_ = lean_usize_add(v_i_3111_, v___x_3118_);
v___x_3120_ = lean_array_uset(v_bs_x27_3117_, v_i_3111_, v_recArgPos_3115_);
v_i_3111_ = v___x_3119_;
v_bs_3112_ = v___x_3120_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__2___boxed(lean_object* v_sz_3122_, lean_object* v_i_3123_, lean_object* v_bs_3124_){
_start:
{
size_t v_sz_boxed_3125_; size_t v_i_boxed_3126_; lean_object* v_res_3127_; 
v_sz_boxed_3125_ = lean_unbox_usize(v_sz_3122_);
lean_dec(v_sz_3122_);
v_i_boxed_3126_ = lean_unbox_usize(v_i_3123_);
lean_dec(v_i_3123_);
v_res_3127_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__2(v_sz_boxed_3125_, v_i_boxed_3126_, v_bs_3124_);
return v_res_3127_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg(lean_object* v_fst_3128_, size_t v_sz_3129_, size_t v_i_3130_, lean_object* v_bs_3131_){
_start:
{
uint8_t v___x_3132_; 
v___x_3132_ = lean_usize_dec_lt(v_i_3130_, v_sz_3129_);
if (v___x_3132_ == 0)
{
return v_bs_3131_;
}
else
{
lean_object* v_v_3133_; lean_object* v_fnName_3134_; lean_object* v_recArgPos_3135_; lean_object* v_indicesPos_3136_; lean_object* v_indGroupInst_3137_; lean_object* v_indIdx_3138_; lean_object* v___x_3140_; uint8_t v_isShared_3141_; uint8_t v_isSharedCheck_3155_; 
v_v_3133_ = lean_array_uget(v_bs_3131_, v_i_3130_);
v_fnName_3134_ = lean_ctor_get(v_v_3133_, 0);
v_recArgPos_3135_ = lean_ctor_get(v_v_3133_, 2);
v_indicesPos_3136_ = lean_ctor_get(v_v_3133_, 3);
v_indGroupInst_3137_ = lean_ctor_get(v_v_3133_, 4);
v_indIdx_3138_ = lean_ctor_get(v_v_3133_, 5);
v_isSharedCheck_3155_ = !lean_is_exclusive(v_v_3133_);
if (v_isSharedCheck_3155_ == 0)
{
lean_object* v_unused_3156_; 
v_unused_3156_ = lean_ctor_get(v_v_3133_, 1);
lean_dec(v_unused_3156_);
v___x_3140_ = v_v_3133_;
v_isShared_3141_ = v_isSharedCheck_3155_;
goto v_resetjp_3139_;
}
else
{
lean_inc(v_indIdx_3138_);
lean_inc(v_indGroupInst_3137_);
lean_inc(v_indicesPos_3136_);
lean_inc(v_recArgPos_3135_);
lean_inc(v_fnName_3134_);
lean_dec(v_v_3133_);
v___x_3140_ = lean_box(0);
v_isShared_3141_ = v_isSharedCheck_3155_;
goto v_resetjp_3139_;
}
v_resetjp_3139_:
{
lean_object* v_perms_3142_; lean_object* v___x_3143_; lean_object* v_bs_x27_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3149_; 
v_perms_3142_ = lean_ctor_get(v_fst_3128_, 1);
v___x_3143_ = lean_unsigned_to_nat(0u);
v_bs_x27_3144_ = lean_array_uset(v_bs_3131_, v_i_3130_, v___x_3143_);
v___x_3145_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0);
v___x_3146_ = lean_usize_to_nat(v_i_3130_);
v___x_3147_ = lean_array_get_borrowed(v___x_3145_, v_perms_3142_, v___x_3146_);
lean_dec(v___x_3146_);
lean_inc(v___x_3147_);
if (v_isShared_3141_ == 0)
{
lean_ctor_set(v___x_3140_, 1, v___x_3147_);
v___x_3149_ = v___x_3140_;
goto v_reusejp_3148_;
}
else
{
lean_object* v_reuseFailAlloc_3154_; 
v_reuseFailAlloc_3154_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3154_, 0, v_fnName_3134_);
lean_ctor_set(v_reuseFailAlloc_3154_, 1, v___x_3147_);
lean_ctor_set(v_reuseFailAlloc_3154_, 2, v_recArgPos_3135_);
lean_ctor_set(v_reuseFailAlloc_3154_, 3, v_indicesPos_3136_);
lean_ctor_set(v_reuseFailAlloc_3154_, 4, v_indGroupInst_3137_);
lean_ctor_set(v_reuseFailAlloc_3154_, 5, v_indIdx_3138_);
v___x_3149_ = v_reuseFailAlloc_3154_;
goto v_reusejp_3148_;
}
v_reusejp_3148_:
{
size_t v___x_3150_; size_t v___x_3151_; lean_object* v___x_3152_; 
v___x_3150_ = ((size_t)1ULL);
v___x_3151_ = lean_usize_add(v_i_3130_, v___x_3150_);
v___x_3152_ = lean_array_uset(v_bs_x27_3144_, v_i_3130_, v___x_3149_);
v_i_3130_ = v___x_3151_;
v_bs_3131_ = v___x_3152_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg___boxed(lean_object* v_fst_3157_, lean_object* v_sz_3158_, lean_object* v_i_3159_, lean_object* v_bs_3160_){
_start:
{
size_t v_sz_boxed_3161_; size_t v_i_boxed_3162_; lean_object* v_res_3163_; 
v_sz_boxed_3161_ = lean_unbox_usize(v_sz_3158_);
lean_dec(v_sz_3158_);
v_i_boxed_3162_ = lean_unbox_usize(v_i_3159_);
lean_dec(v_i_3159_);
v_res_3163_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg(v_fst_3157_, v_sz_boxed_3161_, v_i_boxed_3162_, v_bs_3160_);
lean_dec_ref(v_fst_3157_);
return v_res_3163_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__1(void){
_start:
{
lean_object* v___x_3165_; lean_object* v___x_3166_; 
v___x_3165_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__0));
v___x_3166_ = l_Lean_stringToMessageData(v___x_3165_);
return v___x_3166_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__3(void){
_start:
{
lean_object* v___x_3168_; lean_object* v___x_3169_; 
v___x_3168_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__2));
v___x_3169_ = l_Lean_stringToMessageData(v___x_3168_);
return v___x_3169_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__5(void){
_start:
{
lean_object* v___x_3171_; lean_object* v___x_3172_; 
v___x_3171_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__4));
v___x_3172_ = l_Lean_stringToMessageData(v___x_3171_);
return v___x_3172_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6(lean_object* v_a_3173_, lean_object* v_as_3174_, size_t v_sz_3175_, size_t v_i_3176_, lean_object* v_b_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_){
_start:
{
lean_object* v_a_3184_; uint8_t v___x_3188_; 
v___x_3188_ = lean_usize_dec_lt(v_i_3176_, v_sz_3175_);
if (v___x_3188_ == 0)
{
lean_object* v___x_3189_; 
lean_dec_ref(v_a_3173_);
v___x_3189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3189_, 0, v_b_3177_);
return v___x_3189_;
}
else
{
lean_object* v_a_3190_; lean_object* v___x_3191_; 
v_a_3190_ = lean_array_uget_borrowed(v_as_3174_, v_i_3176_);
lean_inc(v_a_3190_);
lean_inc_ref(v_a_3173_);
v___x_3191_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg(v_a_3173_, v_a_3190_, v___y_3179_);
if (lean_obj_tag(v___x_3191_) == 0)
{
lean_object* v_a_3192_; lean_object* v___x_3193_; uint8_t v___x_3194_; 
v_a_3192_ = lean_ctor_get(v___x_3191_, 0);
lean_inc(v_a_3192_);
lean_dec_ref_known(v___x_3191_, 1);
v___x_3193_ = lean_box(0);
v___x_3194_ = lean_unbox(v_a_3192_);
lean_dec(v_a_3192_);
if (v___x_3194_ == 0)
{
v_a_3184_ = v___x_3193_;
goto v___jp_3183_;
}
else
{
uint8_t v___x_3195_; 
v___x_3195_ = l_Lean_Expr_isFVarOf(v_a_3173_, v_a_3190_);
if (v___x_3195_ == 0)
{
lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; 
v___x_3196_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__1);
lean_inc_ref(v_a_3173_);
v___x_3197_ = l_Lean_indentExpr(v_a_3173_);
v___x_3198_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3198_, 0, v___x_3196_);
lean_ctor_set(v___x_3198_, 1, v___x_3197_);
v___x_3199_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__3);
v___x_3200_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3200_, 0, v___x_3198_);
lean_ctor_set(v___x_3200_, 1, v___x_3199_);
lean_inc(v_a_3190_);
v___x_3201_ = l_Lean_mkFVar(v_a_3190_);
v___x_3202_ = l_Lean_indentExpr(v___x_3201_);
v___x_3203_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3203_, 0, v___x_3200_);
lean_ctor_set(v___x_3203_, 1, v___x_3202_);
v___x_3204_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__5);
v___x_3205_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3205_, 0, v___x_3203_);
lean_ctor_set(v___x_3205_, 1, v___x_3204_);
v___x_3206_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg(v___x_3205_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_);
if (lean_obj_tag(v___x_3206_) == 0)
{
lean_dec_ref_known(v___x_3206_, 1);
v_a_3184_ = v___x_3193_;
goto v___jp_3183_;
}
else
{
lean_dec_ref(v_a_3173_);
return v___x_3206_;
}
}
else
{
lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; 
v___x_3207_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__1);
lean_inc_ref(v_a_3173_);
v___x_3208_ = l_Lean_indentExpr(v_a_3173_);
v___x_3209_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3209_, 0, v___x_3207_);
lean_ctor_set(v___x_3209_, 1, v___x_3208_);
v___x_3210_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__5);
v___x_3211_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3211_, 0, v___x_3209_);
lean_ctor_set(v___x_3211_, 1, v___x_3210_);
v___x_3212_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg(v___x_3211_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_);
if (lean_obj_tag(v___x_3212_) == 0)
{
lean_dec_ref_known(v___x_3212_, 1);
v_a_3184_ = v___x_3193_;
goto v___jp_3183_;
}
else
{
lean_dec_ref(v_a_3173_);
return v___x_3212_;
}
}
}
}
else
{
lean_object* v_a_3213_; lean_object* v___x_3215_; uint8_t v_isShared_3216_; uint8_t v_isSharedCheck_3220_; 
lean_dec_ref(v_a_3173_);
v_a_3213_ = lean_ctor_get(v___x_3191_, 0);
v_isSharedCheck_3220_ = !lean_is_exclusive(v___x_3191_);
if (v_isSharedCheck_3220_ == 0)
{
v___x_3215_ = v___x_3191_;
v_isShared_3216_ = v_isSharedCheck_3220_;
goto v_resetjp_3214_;
}
else
{
lean_inc(v_a_3213_);
lean_dec(v___x_3191_);
v___x_3215_ = lean_box(0);
v_isShared_3216_ = v_isSharedCheck_3220_;
goto v_resetjp_3214_;
}
v_resetjp_3214_:
{
lean_object* v___x_3218_; 
if (v_isShared_3216_ == 0)
{
v___x_3218_ = v___x_3215_;
goto v_reusejp_3217_;
}
else
{
lean_object* v_reuseFailAlloc_3219_; 
v_reuseFailAlloc_3219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3219_, 0, v_a_3213_);
v___x_3218_ = v_reuseFailAlloc_3219_;
goto v_reusejp_3217_;
}
v_reusejp_3217_:
{
return v___x_3218_;
}
}
}
}
v___jp_3183_:
{
size_t v___x_3185_; size_t v___x_3186_; 
v___x_3185_ = ((size_t)1ULL);
v___x_3186_ = lean_usize_add(v_i_3176_, v___x_3185_);
v_i_3176_ = v___x_3186_;
v_b_3177_ = v_a_3184_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___boxed(lean_object* v_a_3221_, lean_object* v_as_3222_, lean_object* v_sz_3223_, lean_object* v_i_3224_, lean_object* v_b_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_){
_start:
{
size_t v_sz_boxed_3231_; size_t v_i_boxed_3232_; lean_object* v_res_3233_; 
v_sz_boxed_3231_ = lean_unbox_usize(v_sz_3223_);
lean_dec(v_sz_3223_);
v_i_boxed_3232_ = lean_unbox_usize(v_i_3224_);
lean_dec(v_i_3224_);
v_res_3233_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6(v_a_3221_, v_as_3222_, v_sz_boxed_3231_, v_i_boxed_3232_, v_b_3225_, v___y_3226_, v___y_3227_, v___y_3228_, v___y_3229_);
lean_dec(v___y_3229_);
lean_dec_ref(v___y_3228_);
lean_dec(v___y_3227_);
lean_dec_ref(v___y_3226_);
lean_dec_ref(v_as_3222_);
return v_res_3233_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7(lean_object* v_snd_3234_, lean_object* v_as_3235_, size_t v_sz_3236_, size_t v_i_3237_, lean_object* v_b_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_){
_start:
{
uint8_t v___x_3244_; 
v___x_3244_ = lean_usize_dec_lt(v_i_3237_, v_sz_3236_);
if (v___x_3244_ == 0)
{
lean_object* v___x_3245_; 
v___x_3245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3245_, 0, v_b_3238_);
return v___x_3245_;
}
else
{
lean_object* v___x_3246_; lean_object* v_a_3247_; size_t v_sz_3248_; size_t v___x_3249_; lean_object* v___x_3250_; 
v___x_3246_ = lean_box(0);
v_a_3247_ = lean_array_uget_borrowed(v_as_3235_, v_i_3237_);
v_sz_3248_ = lean_array_size(v_snd_3234_);
v___x_3249_ = ((size_t)0ULL);
lean_inc(v_a_3247_);
v___x_3250_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6(v_a_3247_, v_snd_3234_, v_sz_3248_, v___x_3249_, v___x_3246_, v___y_3239_, v___y_3240_, v___y_3241_, v___y_3242_);
if (lean_obj_tag(v___x_3250_) == 0)
{
size_t v___x_3251_; size_t v___x_3252_; 
lean_dec_ref_known(v___x_3250_, 1);
v___x_3251_ = ((size_t)1ULL);
v___x_3252_ = lean_usize_add(v_i_3237_, v___x_3251_);
v_i_3237_ = v___x_3252_;
v_b_3238_ = v___x_3246_;
goto _start;
}
else
{
return v___x_3250_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7___boxed(lean_object* v_snd_3254_, lean_object* v_as_3255_, lean_object* v_sz_3256_, lean_object* v_i_3257_, lean_object* v_b_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_){
_start:
{
size_t v_sz_boxed_3264_; size_t v_i_boxed_3265_; lean_object* v_res_3266_; 
v_sz_boxed_3264_ = lean_unbox_usize(v_sz_3256_);
lean_dec(v_sz_3256_);
v_i_boxed_3265_ = lean_unbox_usize(v_i_3257_);
lean_dec(v_i_3257_);
v_res_3266_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7(v_snd_3254_, v_as_3255_, v_sz_boxed_3264_, v_i_boxed_3265_, v_b_3258_, v___y_3259_, v___y_3260_, v___y_3261_, v___y_3262_);
lean_dec(v___y_3262_);
lean_dec_ref(v___y_3261_);
lean_dec(v___y_3260_);
lean_dec_ref(v___y_3259_);
lean_dec_ref(v_as_3255_);
lean_dec_ref(v_snd_3254_);
return v_res_3266_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8(lean_object* v_snd_3267_, lean_object* v_as_3268_, size_t v_sz_3269_, size_t v_i_3270_, lean_object* v_b_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_){
_start:
{
uint8_t v___x_3277_; 
v___x_3277_ = lean_usize_dec_lt(v_i_3270_, v_sz_3269_);
if (v___x_3277_ == 0)
{
lean_object* v___x_3278_; 
v___x_3278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3278_, 0, v_b_3271_);
return v___x_3278_;
}
else
{
lean_object* v_a_3279_; lean_object* v_indGroupInst_3280_; lean_object* v_params_3281_; lean_object* v___x_3282_; size_t v_sz_3283_; size_t v___x_3284_; lean_object* v___x_3285_; 
v_a_3279_ = lean_array_uget_borrowed(v_as_3268_, v_i_3270_);
v_indGroupInst_3280_ = lean_ctor_get(v_a_3279_, 4);
v_params_3281_ = lean_ctor_get(v_indGroupInst_3280_, 2);
v___x_3282_ = lean_box(0);
v_sz_3283_ = lean_array_size(v_params_3281_);
v___x_3284_ = ((size_t)0ULL);
v___x_3285_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7(v_snd_3267_, v_params_3281_, v_sz_3283_, v___x_3284_, v___x_3282_, v___y_3272_, v___y_3273_, v___y_3274_, v___y_3275_);
if (lean_obj_tag(v___x_3285_) == 0)
{
size_t v___x_3286_; size_t v___x_3287_; 
lean_dec_ref_known(v___x_3285_, 1);
v___x_3286_ = ((size_t)1ULL);
v___x_3287_ = lean_usize_add(v_i_3270_, v___x_3286_);
v_i_3270_ = v___x_3287_;
v_b_3271_ = v___x_3282_;
goto _start;
}
else
{
return v___x_3285_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8___boxed(lean_object* v_snd_3289_, lean_object* v_as_3290_, lean_object* v_sz_3291_, lean_object* v_i_3292_, lean_object* v_b_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_){
_start:
{
size_t v_sz_boxed_3299_; size_t v_i_boxed_3300_; lean_object* v_res_3301_; 
v_sz_boxed_3299_ = lean_unbox_usize(v_sz_3291_);
lean_dec(v_sz_3291_);
v_i_boxed_3300_ = lean_unbox_usize(v_i_3292_);
lean_dec(v_i_3292_);
v_res_3301_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8(v_snd_3289_, v_as_3290_, v_sz_boxed_3299_, v_i_boxed_3300_, v_b_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_);
lean_dec(v___y_3297_);
lean_dec_ref(v___y_3296_);
lean_dec(v___y_3295_);
lean_dec_ref(v___y_3294_);
lean_dec_ref(v_as_3290_);
lean_dec_ref(v_snd_3289_);
return v_res_3301_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__0(void){
_start:
{
lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; 
v___x_3302_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__3));
v___x_3303_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0___closed__1));
v___x_3304_ = l_Lean_Name_append(v___x_3303_, v___x_3302_);
return v___x_3304_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3306_; lean_object* v___x_3307_; 
v___x_3306_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__1));
v___x_3307_ = l_Lean_stringToMessageData(v___x_3306_);
return v___x_3307_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__4(void){
_start:
{
lean_object* v___x_3309_; lean_object* v___x_3310_; 
v___x_3309_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__3));
v___x_3310_ = l_Lean_stringToMessageData(v___x_3309_);
return v___x_3310_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__6(void){
_start:
{
lean_object* v___x_3312_; lean_object* v___x_3313_; 
v___x_3312_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__5));
v___x_3313_ = l_Lean_stringToMessageData(v___x_3312_);
return v___x_3313_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__8(void){
_start:
{
lean_object* v___x_3315_; lean_object* v___x_3316_; 
v___x_3315_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__7));
v___x_3316_ = l_Lean_stringToMessageData(v___x_3315_);
return v___x_3316_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__10(void){
_start:
{
lean_object* v___x_3318_; lean_object* v___x_3319_; 
v___x_3318_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__9));
v___x_3319_ = l_Lean_stringToMessageData(v___x_3318_);
return v___x_3319_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0(size_t v___x_3320_, lean_object* v_a_3321_, lean_object* v_xs_3322_, lean_object* v_a_3323_, lean_object* v_recArgInfos_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_){
_start:
{
lean_object* v___y_3331_; lean_object* v___y_3332_; lean_object* v___y_3333_; lean_object* v___y_3334_; lean_object* v___y_3335_; lean_object* v___y_3336_; lean_object* v___y_3337_; lean_object* v___x_3350_; lean_object* v___y_3352_; lean_object* v___y_3353_; lean_object* v___y_3354_; lean_object* v___y_3355_; lean_object* v___y_3356_; lean_object* v___y_3357_; lean_object* v___y_3358_; lean_object* v___x_3377_; lean_object* v_a_3378_; size_t v_sz_3379_; lean_object* v___x_3380_; lean_object* v___y_3382_; lean_object* v___y_3383_; lean_object* v___y_3384_; lean_object* v___y_3385_; uint8_t v___x_3443_; 
v___x_3350_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__3));
v___x_3377_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0(v___x_3350_, v___y_3325_, v___y_3326_, v___y_3327_, v___y_3328_);
v_a_3378_ = lean_ctor_get(v___x_3377_, 0);
lean_inc(v_a_3378_);
lean_dec_ref(v___x_3377_);
v_sz_3379_ = lean_array_size(v_recArgInfos_3324_);
lean_inc_ref(v_recArgInfos_3324_);
v___x_3380_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__2(v_sz_3379_, v___x_3320_, v_recArgInfos_3324_);
v___x_3443_ = lean_unbox(v_a_3378_);
lean_dec(v_a_3378_);
if (v___x_3443_ == 0)
{
v___y_3382_ = v___y_3325_;
v___y_3383_ = v___y_3326_;
v___y_3384_ = v___y_3327_;
v___y_3385_ = v___y_3328_;
goto v___jp_3381_;
}
else
{
lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; 
v___x_3444_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__10, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__10);
lean_inc_ref(v___x_3380_);
v___x_3445_ = lean_array_to_list(v___x_3380_);
v___x_3446_ = lean_box(0);
v___x_3447_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__0(v___x_3445_, v___x_3446_);
v___x_3448_ = l_Lean_MessageData_ofList(v___x_3447_);
v___x_3449_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3449_, 0, v___x_3444_);
lean_ctor_set(v___x_3449_, 1, v___x_3448_);
v___x_3450_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_3350_, v___x_3449_, v___y_3325_, v___y_3326_, v___y_3327_, v___y_3328_);
if (lean_obj_tag(v___x_3450_) == 0)
{
lean_dec_ref_known(v___x_3450_, 1);
v___y_3382_ = v___y_3325_;
v___y_3383_ = v___y_3326_;
v___y_3384_ = v___y_3327_;
v___y_3385_ = v___y_3328_;
goto v___jp_3381_;
}
else
{
lean_object* v_a_3451_; lean_object* v___x_3453_; uint8_t v_isShared_3454_; uint8_t v_isSharedCheck_3458_; 
lean_dec_ref(v___x_3380_);
lean_dec_ref(v_recArgInfos_3324_);
lean_dec_ref(v_a_3323_);
lean_dec_ref(v_xs_3322_);
lean_dec_ref(v_a_3321_);
v_a_3451_ = lean_ctor_get(v___x_3450_, 0);
v_isSharedCheck_3458_ = !lean_is_exclusive(v___x_3450_);
if (v_isSharedCheck_3458_ == 0)
{
v___x_3453_ = v___x_3450_;
v_isShared_3454_ = v_isSharedCheck_3458_;
goto v_resetjp_3452_;
}
else
{
lean_inc(v_a_3451_);
lean_dec(v___x_3450_);
v___x_3453_ = lean_box(0);
v_isShared_3454_ = v_isSharedCheck_3458_;
goto v_resetjp_3452_;
}
v_resetjp_3452_:
{
lean_object* v___x_3456_; 
if (v_isShared_3454_ == 0)
{
v___x_3456_ = v___x_3453_;
goto v_reusejp_3455_;
}
else
{
lean_object* v_reuseFailAlloc_3457_; 
v_reuseFailAlloc_3457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3457_, 0, v_a_3451_);
v___x_3456_ = v_reuseFailAlloc_3457_;
goto v_reusejp_3455_;
}
v_reusejp_3455_:
{
return v___x_3456_;
}
}
}
}
v___jp_3330_:
{
lean_object* v___x_3338_; size_t v_sz_3339_; lean_object* v___x_3340_; 
v___x_3338_ = lean_box(0);
v_sz_3339_ = lean_array_size(v___y_3332_);
v___x_3340_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8(v___y_3333_, v___y_3332_, v_sz_3339_, v___x_3320_, v___x_3338_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_);
lean_dec_ref(v___y_3332_);
if (lean_obj_tag(v___x_3340_) == 0)
{
lean_object* v___x_3341_; 
lean_dec_ref_known(v___x_3340_, 1);
v___x_3341_ = l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___redArg(v___y_3333_, v___y_3331_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_);
lean_dec_ref(v___y_3333_);
return v___x_3341_;
}
else
{
lean_object* v_a_3342_; lean_object* v___x_3344_; uint8_t v_isShared_3345_; uint8_t v_isSharedCheck_3349_; 
lean_dec_ref(v___y_3333_);
lean_dec_ref(v___y_3331_);
v_a_3342_ = lean_ctor_get(v___x_3340_, 0);
v_isSharedCheck_3349_ = !lean_is_exclusive(v___x_3340_);
if (v_isSharedCheck_3349_ == 0)
{
v___x_3344_ = v___x_3340_;
v_isShared_3345_ = v_isSharedCheck_3349_;
goto v_resetjp_3343_;
}
else
{
lean_inc(v_a_3342_);
lean_dec(v___x_3340_);
v___x_3344_ = lean_box(0);
v_isShared_3345_ = v_isSharedCheck_3349_;
goto v_resetjp_3343_;
}
v_resetjp_3343_:
{
lean_object* v___x_3347_; 
if (v_isShared_3345_ == 0)
{
v___x_3347_ = v___x_3344_;
goto v_reusejp_3346_;
}
else
{
lean_object* v_reuseFailAlloc_3348_; 
v_reuseFailAlloc_3348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3348_, 0, v_a_3342_);
v___x_3347_ = v_reuseFailAlloc_3348_;
goto v_reusejp_3346_;
}
v_reusejp_3346_:
{
return v___x_3347_;
}
}
}
}
v___jp_3351_:
{
lean_object* v_options_3359_; uint8_t v_hasTrace_3360_; 
v_options_3359_ = lean_ctor_get(v___y_3357_, 2);
v_hasTrace_3360_ = lean_ctor_get_uint8(v_options_3359_, sizeof(void*)*1);
if (v_hasTrace_3360_ == 0)
{
v___y_3331_ = v___y_3352_;
v___y_3332_ = v___y_3353_;
v___y_3333_ = v___y_3354_;
v___y_3334_ = v___y_3355_;
v___y_3335_ = v___y_3356_;
v___y_3336_ = v___y_3357_;
v___y_3337_ = v___y_3358_;
goto v___jp_3330_;
}
else
{
lean_object* v_inheritedTraceOptions_3361_; lean_object* v___x_3362_; uint8_t v___x_3363_; 
v_inheritedTraceOptions_3361_ = lean_ctor_get(v___y_3357_, 13);
v___x_3362_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__0);
v___x_3363_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3361_, v_options_3359_, v___x_3362_);
if (v___x_3363_ == 0)
{
v___y_3331_ = v___y_3352_;
v___y_3332_ = v___y_3353_;
v___y_3333_ = v___y_3354_;
v___y_3334_ = v___y_3355_;
v___y_3335_ = v___y_3356_;
v___y_3336_ = v___y_3357_;
v___y_3337_ = v___y_3358_;
goto v___jp_3330_;
}
else
{
lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; 
v___x_3364_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__2);
lean_inc_ref(v___y_3353_);
v___x_3365_ = l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10(v___y_3353_);
v___x_3366_ = l_Lean_MessageData_ofFormat(v___x_3365_);
v___x_3367_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3367_, 0, v___x_3364_);
lean_ctor_set(v___x_3367_, 1, v___x_3366_);
v___x_3368_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_3350_, v___x_3367_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_);
if (lean_obj_tag(v___x_3368_) == 0)
{
lean_dec_ref_known(v___x_3368_, 1);
v___y_3331_ = v___y_3352_;
v___y_3332_ = v___y_3353_;
v___y_3333_ = v___y_3354_;
v___y_3334_ = v___y_3355_;
v___y_3335_ = v___y_3356_;
v___y_3336_ = v___y_3357_;
v___y_3337_ = v___y_3358_;
goto v___jp_3330_;
}
else
{
lean_object* v_a_3369_; lean_object* v___x_3371_; uint8_t v_isShared_3372_; uint8_t v_isSharedCheck_3376_; 
lean_dec_ref(v___y_3354_);
lean_dec_ref(v___y_3353_);
lean_dec_ref(v___y_3352_);
v_a_3369_ = lean_ctor_get(v___x_3368_, 0);
v_isSharedCheck_3376_ = !lean_is_exclusive(v___x_3368_);
if (v_isSharedCheck_3376_ == 0)
{
v___x_3371_ = v___x_3368_;
v_isShared_3372_ = v_isSharedCheck_3376_;
goto v_resetjp_3370_;
}
else
{
lean_inc(v_a_3369_);
lean_dec(v___x_3368_);
v___x_3371_ = lean_box(0);
v_isShared_3372_ = v_isSharedCheck_3376_;
goto v_resetjp_3370_;
}
v_resetjp_3370_:
{
lean_object* v___x_3374_; 
if (v_isShared_3372_ == 0)
{
v___x_3374_ = v___x_3371_;
goto v_reusejp_3373_;
}
else
{
lean_object* v_reuseFailAlloc_3375_; 
v_reuseFailAlloc_3375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3375_, 0, v_a_3369_);
v___x_3374_ = v_reuseFailAlloc_3375_;
goto v_reusejp_3373_;
}
v_reusejp_3373_:
{
return v___x_3374_;
}
}
}
}
}
}
v___jp_3381_:
{
lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v_snd_3388_; lean_object* v_fst_3389_; lean_object* v___x_3391_; uint8_t v_isShared_3392_; uint8_t v_isSharedCheck_3442_; 
lean_inc_ref(v_recArgInfos_3324_);
v___x_3386_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__3(v_sz_3379_, v___x_3320_, v_recArgInfos_3324_);
lean_inc_ref(v_xs_3322_);
v___x_3387_ = l_Lean_Elab_FixedParamPerms_erase(v_a_3321_, v_xs_3322_, v___x_3386_);
v_snd_3388_ = lean_ctor_get(v___x_3387_, 1);
v_fst_3389_ = lean_ctor_get(v___x_3387_, 0);
v_isSharedCheck_3442_ = !lean_is_exclusive(v___x_3387_);
if (v_isSharedCheck_3442_ == 0)
{
v___x_3391_ = v___x_3387_;
v_isShared_3392_ = v_isSharedCheck_3442_;
goto v_resetjp_3390_;
}
else
{
lean_inc(v_snd_3388_);
lean_inc(v_fst_3389_);
lean_dec(v___x_3387_);
v___x_3391_ = lean_box(0);
v_isShared_3392_ = v_isSharedCheck_3442_;
goto v_resetjp_3390_;
}
v_resetjp_3390_:
{
lean_object* v_fst_3393_; lean_object* v_snd_3394_; lean_object* v___x_3396_; uint8_t v_isShared_3397_; uint8_t v_isSharedCheck_3441_; 
v_fst_3393_ = lean_ctor_get(v_snd_3388_, 0);
v_snd_3394_ = lean_ctor_get(v_snd_3388_, 1);
v_isSharedCheck_3441_ = !lean_is_exclusive(v_snd_3388_);
if (v_isSharedCheck_3441_ == 0)
{
v___x_3396_ = v_snd_3388_;
v_isShared_3397_ = v_isSharedCheck_3441_;
goto v_resetjp_3395_;
}
else
{
lean_inc(v_snd_3394_);
lean_inc(v_fst_3393_);
lean_dec(v_snd_3388_);
v___x_3396_ = lean_box(0);
v_isShared_3397_ = v_isSharedCheck_3441_;
goto v_resetjp_3395_;
}
v_resetjp_3395_:
{
lean_object* v___x_3398_; lean_object* v___f_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; uint8_t v___x_3402_; uint8_t v___x_3403_; 
v___x_3398_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg(v_fst_3389_, v_sz_3379_, v___x_3320_, v_recArgInfos_3324_);
lean_inc_ref(v___x_3398_);
lean_inc(v_fst_3393_);
v___f_3399_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___boxed), 10, 5);
lean_closure_set(v___f_3399_, 0, v_a_3323_);
lean_closure_set(v___f_3399_, 1, v_fst_3389_);
lean_closure_set(v___f_3399_, 2, v_fst_3393_);
lean_closure_set(v___f_3399_, 3, v___x_3398_);
lean_closure_set(v___f_3399_, 4, v___x_3380_);
v___x_3400_ = lean_array_get_size(v_fst_3393_);
v___x_3401_ = lean_array_get_size(v_xs_3322_);
v___x_3402_ = lean_nat_dec_eq(v___x_3400_, v___x_3401_);
v___x_3403_ = lean_bool_not(v___x_3402_);
if (v___x_3403_ == 0)
{
lean_object* v___x_3404_; 
lean_dec_ref(v___x_3398_);
lean_del_object(v___x_3396_);
lean_dec(v_fst_3393_);
lean_del_object(v___x_3391_);
lean_dec_ref(v_xs_3322_);
v___x_3404_ = l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___redArg(v_snd_3394_, v___f_3399_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_);
lean_dec(v_snd_3394_);
return v___x_3404_;
}
else
{
lean_object* v___x_3405_; lean_object* v_a_3406_; uint8_t v___x_3407_; 
v___x_3405_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0(v___x_3350_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_);
v_a_3406_ = lean_ctor_get(v___x_3405_, 0);
lean_inc(v_a_3406_);
lean_dec_ref(v___x_3405_);
v___x_3407_ = lean_unbox(v_a_3406_);
lean_dec(v_a_3406_);
if (v___x_3407_ == 0)
{
lean_del_object(v___x_3396_);
lean_dec(v_fst_3393_);
lean_del_object(v___x_3391_);
lean_dec_ref(v_xs_3322_);
v___y_3352_ = v___f_3399_;
v___y_3353_ = v___x_3398_;
v___y_3354_ = v_snd_3394_;
v___y_3355_ = v___y_3382_;
v___y_3356_ = v___y_3383_;
v___y_3357_ = v___y_3384_;
v___y_3358_ = v___y_3385_;
goto v___jp_3351_;
}
else
{
lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3414_; 
v___x_3408_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__4);
v___x_3409_ = lean_array_to_list(v_xs_3322_);
v___x_3410_ = lean_box(0);
v___x_3411_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_3409_, v___x_3410_);
v___x_3412_ = l_Lean_MessageData_ofList(v___x_3411_);
if (v_isShared_3397_ == 0)
{
lean_ctor_set_tag(v___x_3396_, 7);
lean_ctor_set(v___x_3396_, 1, v___x_3412_);
lean_ctor_set(v___x_3396_, 0, v___x_3408_);
v___x_3414_ = v___x_3396_;
goto v_reusejp_3413_;
}
else
{
lean_object* v_reuseFailAlloc_3440_; 
v_reuseFailAlloc_3440_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3440_, 0, v___x_3408_);
lean_ctor_set(v_reuseFailAlloc_3440_, 1, v___x_3412_);
v___x_3414_ = v_reuseFailAlloc_3440_;
goto v_reusejp_3413_;
}
v_reusejp_3413_:
{
lean_object* v___x_3415_; lean_object* v___x_3417_; 
v___x_3415_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__6, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__6);
if (v_isShared_3392_ == 0)
{
lean_ctor_set_tag(v___x_3391_, 7);
lean_ctor_set(v___x_3391_, 1, v___x_3415_);
lean_ctor_set(v___x_3391_, 0, v___x_3414_);
v___x_3417_ = v___x_3391_;
goto v_reusejp_3416_;
}
else
{
lean_object* v_reuseFailAlloc_3439_; 
v_reuseFailAlloc_3439_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3439_, 0, v___x_3414_);
lean_ctor_set(v_reuseFailAlloc_3439_, 1, v___x_3415_);
v___x_3417_ = v_reuseFailAlloc_3439_;
goto v_reusejp_3416_;
}
v_reusejp_3416_:
{
lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; size_t v_sz_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; 
v___x_3418_ = lean_array_to_list(v_fst_3393_);
v___x_3419_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_3418_, v___x_3410_);
v___x_3420_ = l_Lean_MessageData_ofList(v___x_3419_);
v___x_3421_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3421_, 0, v___x_3417_);
lean_ctor_set(v___x_3421_, 1, v___x_3420_);
v___x_3422_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__8);
v___x_3423_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3423_, 0, v___x_3421_);
lean_ctor_set(v___x_3423_, 1, v___x_3422_);
v_sz_3424_ = lean_array_size(v_snd_3394_);
lean_inc(v_snd_3394_);
v___x_3425_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__11(v_sz_3424_, v___x_3320_, v_snd_3394_);
v___x_3426_ = lean_array_to_list(v___x_3425_);
v___x_3427_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_3426_, v___x_3410_);
v___x_3428_ = l_Lean_MessageData_ofList(v___x_3427_);
v___x_3429_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3429_, 0, v___x_3423_);
lean_ctor_set(v___x_3429_, 1, v___x_3428_);
v___x_3430_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_3350_, v___x_3429_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_);
if (lean_obj_tag(v___x_3430_) == 0)
{
lean_dec_ref_known(v___x_3430_, 1);
v___y_3352_ = v___f_3399_;
v___y_3353_ = v___x_3398_;
v___y_3354_ = v_snd_3394_;
v___y_3355_ = v___y_3382_;
v___y_3356_ = v___y_3383_;
v___y_3357_ = v___y_3384_;
v___y_3358_ = v___y_3385_;
goto v___jp_3351_;
}
else
{
lean_object* v_a_3431_; lean_object* v___x_3433_; uint8_t v_isShared_3434_; uint8_t v_isSharedCheck_3438_; 
lean_dec_ref(v___f_3399_);
lean_dec_ref(v___x_3398_);
lean_dec(v_snd_3394_);
v_a_3431_ = lean_ctor_get(v___x_3430_, 0);
v_isSharedCheck_3438_ = !lean_is_exclusive(v___x_3430_);
if (v_isSharedCheck_3438_ == 0)
{
v___x_3433_ = v___x_3430_;
v_isShared_3434_ = v_isSharedCheck_3438_;
goto v_resetjp_3432_;
}
else
{
lean_inc(v_a_3431_);
lean_dec(v___x_3430_);
v___x_3433_ = lean_box(0);
v_isShared_3434_ = v_isSharedCheck_3438_;
goto v_resetjp_3432_;
}
v_resetjp_3432_:
{
lean_object* v___x_3436_; 
if (v_isShared_3434_ == 0)
{
v___x_3436_ = v___x_3433_;
goto v_reusejp_3435_;
}
else
{
lean_object* v_reuseFailAlloc_3437_; 
v_reuseFailAlloc_3437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3437_, 0, v_a_3431_);
v___x_3436_ = v_reuseFailAlloc_3437_;
goto v_reusejp_3435_;
}
v_reusejp_3435_:
{
return v___x_3436_;
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___boxed(lean_object* v___x_3459_, lean_object* v_a_3460_, lean_object* v_xs_3461_, lean_object* v_a_3462_, lean_object* v_recArgInfos_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_){
_start:
{
size_t v___x_15318__boxed_3469_; lean_object* v_res_3470_; 
v___x_15318__boxed_3469_ = lean_unbox_usize(v___x_3459_);
lean_dec(v___x_3459_);
v_res_3470_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0(v___x_15318__boxed_3469_, v_a_3460_, v_xs_3461_, v_a_3462_, v_recArgInfos_3463_, v___y_3464_, v___y_3465_, v___y_3466_, v___y_3467_);
lean_dec(v___y_3467_);
lean_dec_ref(v___y_3466_);
lean_dec(v___y_3465_);
lean_dec_ref(v___y_3464_);
return v_res_3470_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg(lean_object* v___x_3471_, lean_object* v_xs_3472_, size_t v_sz_3473_, size_t v_i_3474_, lean_object* v_bs_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_){
_start:
{
uint8_t v___x_3481_; 
v___x_3481_ = lean_usize_dec_lt(v_i_3474_, v_sz_3473_);
if (v___x_3481_ == 0)
{
lean_object* v___x_3482_; 
lean_dec_ref(v_xs_3472_);
v___x_3482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3482_, 0, v_bs_3475_);
return v___x_3482_;
}
else
{
lean_object* v_v_3483_; lean_object* v_value_3484_; lean_object* v___x_3485_; lean_object* v_bs_x27_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; 
v_v_3483_ = lean_array_uget_borrowed(v_bs_3475_, v_i_3474_);
v_value_3484_ = lean_ctor_get(v_v_3483_, 7);
lean_inc_ref(v_value_3484_);
v___x_3485_ = lean_unsigned_to_nat(0u);
v_bs_x27_3486_ = lean_array_uset(v_bs_3475_, v_i_3474_, v___x_3485_);
v___x_3487_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0);
v___x_3488_ = lean_usize_to_nat(v_i_3474_);
v___x_3489_ = lean_array_get_borrowed(v___x_3487_, v___x_3471_, v___x_3488_);
lean_dec(v___x_3488_);
lean_inc_ref(v_xs_3472_);
lean_inc(v___x_3489_);
v___x_3490_ = l_Lean_Elab_FixedParamPerm_instantiateLambda(v___x_3489_, v_value_3484_, v_xs_3472_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_);
if (lean_obj_tag(v___x_3490_) == 0)
{
lean_object* v_a_3491_; size_t v___x_3492_; size_t v___x_3493_; lean_object* v___x_3494_; 
v_a_3491_ = lean_ctor_get(v___x_3490_, 0);
lean_inc(v_a_3491_);
lean_dec_ref_known(v___x_3490_, 1);
v___x_3492_ = ((size_t)1ULL);
v___x_3493_ = lean_usize_add(v_i_3474_, v___x_3492_);
v___x_3494_ = lean_array_uset(v_bs_x27_3486_, v_i_3474_, v_a_3491_);
v_i_3474_ = v___x_3493_;
v_bs_3475_ = v___x_3494_;
goto _start;
}
else
{
lean_object* v_a_3496_; lean_object* v___x_3498_; uint8_t v_isShared_3499_; uint8_t v_isSharedCheck_3503_; 
lean_dec_ref(v_bs_x27_3486_);
lean_dec_ref(v_xs_3472_);
v_a_3496_ = lean_ctor_get(v___x_3490_, 0);
v_isSharedCheck_3503_ = !lean_is_exclusive(v___x_3490_);
if (v_isSharedCheck_3503_ == 0)
{
v___x_3498_ = v___x_3490_;
v_isShared_3499_ = v_isSharedCheck_3503_;
goto v_resetjp_3497_;
}
else
{
lean_inc(v_a_3496_);
lean_dec(v___x_3490_);
v___x_3498_ = lean_box(0);
v_isShared_3499_ = v_isSharedCheck_3503_;
goto v_resetjp_3497_;
}
v_resetjp_3497_:
{
lean_object* v___x_3501_; 
if (v_isShared_3499_ == 0)
{
v___x_3501_ = v___x_3498_;
goto v_reusejp_3500_;
}
else
{
lean_object* v_reuseFailAlloc_3502_; 
v_reuseFailAlloc_3502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3502_, 0, v_a_3496_);
v___x_3501_ = v_reuseFailAlloc_3502_;
goto v_reusejp_3500_;
}
v_reusejp_3500_:
{
return v___x_3501_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg___boxed(lean_object* v___x_3504_, lean_object* v_xs_3505_, lean_object* v_sz_3506_, lean_object* v_i_3507_, lean_object* v_bs_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_){
_start:
{
size_t v_sz_boxed_3514_; size_t v_i_boxed_3515_; lean_object* v_res_3516_; 
v_sz_boxed_3514_ = lean_unbox_usize(v_sz_3506_);
lean_dec(v_sz_3506_);
v_i_boxed_3515_ = lean_unbox_usize(v_i_3507_);
lean_dec(v_i_3507_);
v_res_3516_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg(v___x_3504_, v_xs_3505_, v_sz_boxed_3514_, v_i_boxed_3515_, v_bs_3508_, v___y_3509_, v___y_3510_, v___y_3511_, v___y_3512_);
lean_dec(v___y_3512_);
lean_dec_ref(v___y_3511_);
lean_dec(v___y_3510_);
lean_dec_ref(v___y_3509_);
lean_dec_ref(v___x_3504_);
return v_res_3516_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__2(lean_object* v_a_3517_, lean_object* v_perms_3518_, size_t v___x_3519_, lean_object* v_fnNames_3520_, lean_object* v_a_3521_, lean_object* v_termMeasure_x3fs_3522_, lean_object* v_xs_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_){
_start:
{
size_t v_sz_3529_; lean_object* v___x_3530_; 
v_sz_3529_ = lean_array_size(v_a_3517_);
lean_inc_ref(v_a_3517_);
lean_inc_ref(v_xs_3523_);
v___x_3530_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg(v_perms_3518_, v_xs_3523_, v_sz_3529_, v___x_3519_, v_a_3517_, v___y_3524_, v___y_3525_, v___y_3526_, v___y_3527_);
if (lean_obj_tag(v___x_3530_) == 0)
{
lean_object* v_a_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; 
v_a_3531_ = lean_ctor_get(v___x_3530_, 0);
lean_inc_n(v_a_3531_, 2);
lean_dec_ref_known(v___x_3530_, 1);
lean_inc_ref(v_xs_3523_);
lean_inc_ref(v_a_3521_);
lean_inc_ref(v_fnNames_3520_);
v___x_3532_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_findRecArgCandidates___boxed), 10, 5);
lean_closure_set(v___x_3532_, 0, v_fnNames_3520_);
lean_closure_set(v___x_3532_, 1, v_a_3521_);
lean_closure_set(v___x_3532_, 2, v_xs_3523_);
lean_closure_set(v___x_3532_, 3, v_a_3531_);
lean_closure_set(v___x_3532_, 4, v_termMeasure_x3fs_3522_);
lean_inc_ref(v_a_3517_);
v___x_3533_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v_a_3517_, v___x_3532_, v___y_3524_, v___y_3525_, v___y_3526_, v___y_3527_);
if (lean_obj_tag(v___x_3533_) == 0)
{
lean_object* v_a_3534_; lean_object* v___x_3535_; lean_object* v___f_3536_; lean_object* v___x_3537_; 
v_a_3534_ = lean_ctor_get(v___x_3533_, 0);
lean_inc(v_a_3534_);
lean_dec_ref_known(v___x_3533_, 1);
v___x_3535_ = lean_box_usize(v___x_3519_);
lean_inc_ref(v_xs_3523_);
v___f_3536_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___boxed), 10, 4);
lean_closure_set(v___f_3536_, 0, v___x_3535_);
lean_closure_set(v___f_3536_, 1, v_a_3521_);
lean_closure_set(v___f_3536_, 2, v_xs_3523_);
lean_closure_set(v___f_3536_, 3, v_a_3517_);
v___x_3537_ = l_Lean_Elab_Structural_tryCandidates___redArg(v_fnNames_3520_, v_xs_3523_, v_a_3531_, v_a_3534_, v___f_3536_, v___y_3524_, v___y_3525_, v___y_3526_, v___y_3527_);
lean_dec_ref(v_fnNames_3520_);
return v___x_3537_;
}
else
{
lean_object* v_a_3538_; lean_object* v___x_3540_; uint8_t v_isShared_3541_; uint8_t v_isSharedCheck_3545_; 
lean_dec(v_a_3531_);
lean_dec_ref(v_xs_3523_);
lean_dec_ref(v_a_3521_);
lean_dec_ref(v_fnNames_3520_);
lean_dec_ref(v_a_3517_);
v_a_3538_ = lean_ctor_get(v___x_3533_, 0);
v_isSharedCheck_3545_ = !lean_is_exclusive(v___x_3533_);
if (v_isSharedCheck_3545_ == 0)
{
v___x_3540_ = v___x_3533_;
v_isShared_3541_ = v_isSharedCheck_3545_;
goto v_resetjp_3539_;
}
else
{
lean_inc(v_a_3538_);
lean_dec(v___x_3533_);
v___x_3540_ = lean_box(0);
v_isShared_3541_ = v_isSharedCheck_3545_;
goto v_resetjp_3539_;
}
v_resetjp_3539_:
{
lean_object* v___x_3543_; 
if (v_isShared_3541_ == 0)
{
v___x_3543_ = v___x_3540_;
goto v_reusejp_3542_;
}
else
{
lean_object* v_reuseFailAlloc_3544_; 
v_reuseFailAlloc_3544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3544_, 0, v_a_3538_);
v___x_3543_ = v_reuseFailAlloc_3544_;
goto v_reusejp_3542_;
}
v_reusejp_3542_:
{
return v___x_3543_;
}
}
}
}
else
{
lean_object* v_a_3546_; lean_object* v___x_3548_; uint8_t v_isShared_3549_; uint8_t v_isSharedCheck_3553_; 
lean_dec_ref(v_xs_3523_);
lean_dec_ref(v_termMeasure_x3fs_3522_);
lean_dec_ref(v_a_3521_);
lean_dec_ref(v_fnNames_3520_);
lean_dec_ref(v_a_3517_);
v_a_3546_ = lean_ctor_get(v___x_3530_, 0);
v_isSharedCheck_3553_ = !lean_is_exclusive(v___x_3530_);
if (v_isSharedCheck_3553_ == 0)
{
v___x_3548_ = v___x_3530_;
v_isShared_3549_ = v_isSharedCheck_3553_;
goto v_resetjp_3547_;
}
else
{
lean_inc(v_a_3546_);
lean_dec(v___x_3530_);
v___x_3548_ = lean_box(0);
v_isShared_3549_ = v_isSharedCheck_3553_;
goto v_resetjp_3547_;
}
v_resetjp_3547_:
{
lean_object* v___x_3551_; 
if (v_isShared_3549_ == 0)
{
v___x_3551_ = v___x_3548_;
goto v_reusejp_3550_;
}
else
{
lean_object* v_reuseFailAlloc_3552_; 
v_reuseFailAlloc_3552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3552_, 0, v_a_3546_);
v___x_3551_ = v_reuseFailAlloc_3552_;
goto v_reusejp_3550_;
}
v_reusejp_3550_:
{
return v___x_3551_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__2___boxed(lean_object* v_a_3554_, lean_object* v_perms_3555_, lean_object* v___x_3556_, lean_object* v_fnNames_3557_, lean_object* v_a_3558_, lean_object* v_termMeasure_x3fs_3559_, lean_object* v_xs_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_){
_start:
{
size_t v___x_15672__boxed_3566_; lean_object* v_res_3567_; 
v___x_15672__boxed_3566_ = lean_unbox_usize(v___x_3556_);
lean_dec(v___x_3556_);
v_res_3567_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__2(v_a_3554_, v_perms_3555_, v___x_15672__boxed_3566_, v_fnNames_3557_, v_a_3558_, v_termMeasure_x3fs_3559_, v_xs_3560_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_);
lean_dec(v___y_3564_);
lean_dec_ref(v___y_3563_);
lean_dec(v___y_3562_);
lean_dec_ref(v___y_3561_);
lean_dec_ref(v_perms_3555_);
return v_res_3567_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0(size_t v_sz_3568_, size_t v_i_3569_, lean_object* v_bs_3570_){
_start:
{
uint8_t v___x_3571_; 
v___x_3571_ = lean_usize_dec_lt(v_i_3569_, v_sz_3568_);
if (v___x_3571_ == 0)
{
return v_bs_3570_;
}
else
{
lean_object* v_v_3572_; lean_object* v_declName_3573_; lean_object* v___x_3574_; lean_object* v_bs_x27_3575_; size_t v___x_3576_; size_t v___x_3577_; lean_object* v___x_3578_; 
v_v_3572_ = lean_array_uget_borrowed(v_bs_3570_, v_i_3569_);
v_declName_3573_ = lean_ctor_get(v_v_3572_, 3);
lean_inc(v_declName_3573_);
v___x_3574_ = lean_unsigned_to_nat(0u);
v_bs_x27_3575_ = lean_array_uset(v_bs_3570_, v_i_3569_, v___x_3574_);
v___x_3576_ = ((size_t)1ULL);
v___x_3577_ = lean_usize_add(v_i_3569_, v___x_3576_);
v___x_3578_ = lean_array_uset(v_bs_x27_3575_, v_i_3569_, v_declName_3573_);
v_i_3569_ = v___x_3577_;
v_bs_3570_ = v___x_3578_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0___boxed(lean_object* v_sz_3580_, lean_object* v_i_3581_, lean_object* v_bs_3582_){
_start:
{
size_t v_sz_boxed_3583_; size_t v_i_boxed_3584_; lean_object* v_res_3585_; 
v_sz_boxed_3583_ = lean_unbox_usize(v_sz_3580_);
lean_dec(v_sz_3580_);
v_i_boxed_3584_ = lean_unbox_usize(v_i_3581_);
lean_dec(v_i_3581_);
v_res_3585_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0(v_sz_boxed_3583_, v_i_boxed_3584_, v_bs_3582_);
return v_res_3585_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1___redArg(lean_object* v_fnNames_3586_, lean_object* v_numSectionVars_3587_, size_t v_sz_3588_, size_t v_i_3589_, lean_object* v_bs_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_){
_start:
{
uint8_t v___x_3594_; 
v___x_3594_ = lean_usize_dec_lt(v_i_3589_, v_sz_3588_);
if (v___x_3594_ == 0)
{
lean_object* v___x_3595_; 
lean_dec(v_numSectionVars_3587_);
lean_dec_ref(v_fnNames_3586_);
v___x_3595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3595_, 0, v_bs_3590_);
return v___x_3595_;
}
else
{
lean_object* v_v_3596_; lean_object* v_ref_3597_; uint8_t v_kind_3598_; lean_object* v_levelParams_3599_; lean_object* v_modifiers_3600_; lean_object* v_declName_3601_; lean_object* v_binders_3602_; lean_object* v_numSectionVars_3603_; lean_object* v_type_3604_; lean_object* v_value_3605_; lean_object* v_termination_3606_; lean_object* v___x_3608_; uint8_t v_isShared_3609_; uint8_t v_isSharedCheck_3629_; 
v_v_3596_ = lean_array_uget(v_bs_3590_, v_i_3589_);
v_ref_3597_ = lean_ctor_get(v_v_3596_, 0);
v_kind_3598_ = lean_ctor_get_uint8(v_v_3596_, sizeof(void*)*9);
v_levelParams_3599_ = lean_ctor_get(v_v_3596_, 1);
v_modifiers_3600_ = lean_ctor_get(v_v_3596_, 2);
v_declName_3601_ = lean_ctor_get(v_v_3596_, 3);
v_binders_3602_ = lean_ctor_get(v_v_3596_, 4);
v_numSectionVars_3603_ = lean_ctor_get(v_v_3596_, 5);
v_type_3604_ = lean_ctor_get(v_v_3596_, 6);
v_value_3605_ = lean_ctor_get(v_v_3596_, 7);
v_termination_3606_ = lean_ctor_get(v_v_3596_, 8);
v_isSharedCheck_3629_ = !lean_is_exclusive(v_v_3596_);
if (v_isSharedCheck_3629_ == 0)
{
v___x_3608_ = v_v_3596_;
v_isShared_3609_ = v_isSharedCheck_3629_;
goto v_resetjp_3607_;
}
else
{
lean_inc(v_termination_3606_);
lean_inc(v_value_3605_);
lean_inc(v_type_3604_);
lean_inc(v_numSectionVars_3603_);
lean_inc(v_binders_3602_);
lean_inc(v_declName_3601_);
lean_inc(v_modifiers_3600_);
lean_inc(v_levelParams_3599_);
lean_inc(v_ref_3597_);
lean_dec(v_v_3596_);
v___x_3608_ = lean_box(0);
v_isShared_3609_ = v_isSharedCheck_3629_;
goto v_resetjp_3607_;
}
v_resetjp_3607_:
{
lean_object* v___x_3610_; 
lean_inc(v_numSectionVars_3587_);
lean_inc_ref(v_fnNames_3586_);
v___x_3610_ = l_Lean_Elab_Structural_preprocess(v_value_3605_, v_fnNames_3586_, v_numSectionVars_3587_, v___y_3591_, v___y_3592_);
if (lean_obj_tag(v___x_3610_) == 0)
{
lean_object* v_a_3611_; lean_object* v___x_3612_; lean_object* v_bs_x27_3613_; lean_object* v___x_3615_; 
v_a_3611_ = lean_ctor_get(v___x_3610_, 0);
lean_inc(v_a_3611_);
lean_dec_ref_known(v___x_3610_, 1);
v___x_3612_ = lean_unsigned_to_nat(0u);
v_bs_x27_3613_ = lean_array_uset(v_bs_3590_, v_i_3589_, v___x_3612_);
if (v_isShared_3609_ == 0)
{
lean_ctor_set(v___x_3608_, 7, v_a_3611_);
v___x_3615_ = v___x_3608_;
goto v_reusejp_3614_;
}
else
{
lean_object* v_reuseFailAlloc_3620_; 
v_reuseFailAlloc_3620_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_3620_, 0, v_ref_3597_);
lean_ctor_set(v_reuseFailAlloc_3620_, 1, v_levelParams_3599_);
lean_ctor_set(v_reuseFailAlloc_3620_, 2, v_modifiers_3600_);
lean_ctor_set(v_reuseFailAlloc_3620_, 3, v_declName_3601_);
lean_ctor_set(v_reuseFailAlloc_3620_, 4, v_binders_3602_);
lean_ctor_set(v_reuseFailAlloc_3620_, 5, v_numSectionVars_3603_);
lean_ctor_set(v_reuseFailAlloc_3620_, 6, v_type_3604_);
lean_ctor_set(v_reuseFailAlloc_3620_, 7, v_a_3611_);
lean_ctor_set(v_reuseFailAlloc_3620_, 8, v_termination_3606_);
lean_ctor_set_uint8(v_reuseFailAlloc_3620_, sizeof(void*)*9, v_kind_3598_);
v___x_3615_ = v_reuseFailAlloc_3620_;
goto v_reusejp_3614_;
}
v_reusejp_3614_:
{
size_t v___x_3616_; size_t v___x_3617_; lean_object* v___x_3618_; 
v___x_3616_ = ((size_t)1ULL);
v___x_3617_ = lean_usize_add(v_i_3589_, v___x_3616_);
v___x_3618_ = lean_array_uset(v_bs_x27_3613_, v_i_3589_, v___x_3615_);
v_i_3589_ = v___x_3617_;
v_bs_3590_ = v___x_3618_;
goto _start;
}
}
else
{
lean_object* v_a_3621_; lean_object* v___x_3623_; uint8_t v_isShared_3624_; uint8_t v_isSharedCheck_3628_; 
lean_del_object(v___x_3608_);
lean_dec_ref(v_termination_3606_);
lean_dec_ref(v_type_3604_);
lean_dec(v_numSectionVars_3603_);
lean_dec(v_binders_3602_);
lean_dec(v_declName_3601_);
lean_dec_ref(v_modifiers_3600_);
lean_dec(v_levelParams_3599_);
lean_dec(v_ref_3597_);
lean_dec_ref(v_bs_3590_);
lean_dec(v_numSectionVars_3587_);
lean_dec_ref(v_fnNames_3586_);
v_a_3621_ = lean_ctor_get(v___x_3610_, 0);
v_isSharedCheck_3628_ = !lean_is_exclusive(v___x_3610_);
if (v_isSharedCheck_3628_ == 0)
{
v___x_3623_ = v___x_3610_;
v_isShared_3624_ = v_isSharedCheck_3628_;
goto v_resetjp_3622_;
}
else
{
lean_inc(v_a_3621_);
lean_dec(v___x_3610_);
v___x_3623_ = lean_box(0);
v_isShared_3624_ = v_isSharedCheck_3628_;
goto v_resetjp_3622_;
}
v_resetjp_3622_:
{
lean_object* v___x_3626_; 
if (v_isShared_3624_ == 0)
{
v___x_3626_ = v___x_3623_;
goto v_reusejp_3625_;
}
else
{
lean_object* v_reuseFailAlloc_3627_; 
v_reuseFailAlloc_3627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3627_, 0, v_a_3621_);
v___x_3626_ = v_reuseFailAlloc_3627_;
goto v_reusejp_3625_;
}
v_reusejp_3625_:
{
return v___x_3626_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1___redArg___boxed(lean_object* v_fnNames_3630_, lean_object* v_numSectionVars_3631_, lean_object* v_sz_3632_, lean_object* v_i_3633_, lean_object* v_bs_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_){
_start:
{
size_t v_sz_boxed_3638_; size_t v_i_boxed_3639_; lean_object* v_res_3640_; 
v_sz_boxed_3638_ = lean_unbox_usize(v_sz_3632_);
lean_dec(v_sz_3632_);
v_i_boxed_3639_ = lean_unbox_usize(v_i_3633_);
lean_dec(v_i_3633_);
v_res_3640_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1___redArg(v_fnNames_3630_, v_numSectionVars_3631_, v_sz_boxed_3638_, v_i_boxed_3639_, v_bs_3634_, v___y_3635_, v___y_3636_);
lean_dec(v___y_3636_);
lean_dec_ref(v___y_3635_);
return v_res_3640_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1(lean_object* v_fnNames_3641_, lean_object* v_numSectionVars_3642_, size_t v_sz_3643_, size_t v_i_3644_, lean_object* v_bs_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_){
_start:
{
lean_object* v___x_3651_; 
v___x_3651_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1___redArg(v_fnNames_3641_, v_numSectionVars_3642_, v_sz_3643_, v_i_3644_, v_bs_3645_, v___y_3648_, v___y_3649_);
return v___x_3651_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1___boxed(lean_object* v_fnNames_3652_, lean_object* v_numSectionVars_3653_, lean_object* v_sz_3654_, lean_object* v_i_3655_, lean_object* v_bs_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_){
_start:
{
size_t v_sz_boxed_3662_; size_t v_i_boxed_3663_; lean_object* v_res_3664_; 
v_sz_boxed_3662_ = lean_unbox_usize(v_sz_3654_);
lean_dec(v_sz_3654_);
v_i_boxed_3663_ = lean_unbox_usize(v_i_3655_);
lean_dec(v_i_3655_);
v_res_3664_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1(v_fnNames_3652_, v_numSectionVars_3653_, v_sz_boxed_3662_, v_i_boxed_3663_, v_bs_3656_, v___y_3657_, v___y_3658_, v___y_3659_, v___y_3660_);
lean_dec(v___y_3660_);
lean_dec_ref(v___y_3659_);
lean_dec(v___y_3658_);
lean_dec_ref(v___y_3657_);
return v_res_3664_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos(lean_object* v_preDefs_3665_, lean_object* v_termMeasure_x3fs_3666_, lean_object* v_a_3667_, lean_object* v_a_3668_, lean_object* v_a_3669_, lean_object* v_a_3670_){
_start:
{
lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v_numSectionVars_3675_; size_t v_sz_3676_; size_t v___x_3677_; lean_object* v_fnNames_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; 
v___x_3672_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_3673_ = lean_unsigned_to_nat(0u);
v___x_3674_ = lean_array_get_borrowed(v___x_3672_, v_preDefs_3665_, v___x_3673_);
v_numSectionVars_3675_ = lean_ctor_get(v___x_3674_, 5);
v_sz_3676_ = lean_array_size(v_preDefs_3665_);
v___x_3677_ = ((size_t)0ULL);
lean_inc_ref_n(v_preDefs_3665_, 2);
v_fnNames_3678_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0(v_sz_3676_, v___x_3677_, v_preDefs_3665_);
v___x_3679_ = lean_box_usize(v_sz_3676_);
v___x_3680_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___boxed__const__1));
lean_inc(v_numSectionVars_3675_);
lean_inc_ref(v_fnNames_3678_);
v___x_3681_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1___boxed), 10, 5);
lean_closure_set(v___x_3681_, 0, v_fnNames_3678_);
lean_closure_set(v___x_3681_, 1, v_numSectionVars_3675_);
lean_closure_set(v___x_3681_, 2, v___x_3679_);
lean_closure_set(v___x_3681_, 3, v___x_3680_);
lean_closure_set(v___x_3681_, 4, v_preDefs_3665_);
v___x_3682_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v_preDefs_3665_, v___x_3681_, v_a_3667_, v_a_3668_, v_a_3669_, v_a_3670_);
if (lean_obj_tag(v___x_3682_) == 0)
{
lean_object* v_a_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; 
v_a_3683_ = lean_ctor_get(v___x_3682_, 0);
lean_inc_n(v_a_3683_, 3);
lean_dec_ref_known(v___x_3682_, 1);
v___x_3684_ = lean_alloc_closure((void*)(l_Lean_Elab_getFixedParamPerms___boxed), 6, 1);
lean_closure_set(v___x_3684_, 0, v_a_3683_);
v___x_3685_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v_a_3683_, v___x_3684_, v_a_3667_, v_a_3668_, v_a_3669_, v_a_3670_);
if (lean_obj_tag(v___x_3685_) == 0)
{
lean_object* v_a_3686_; lean_object* v_perms_3687_; lean_object* v___x_3688_; lean_object* v_type_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___f_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; 
v_a_3686_ = lean_ctor_get(v___x_3685_, 0);
lean_inc(v_a_3686_);
lean_dec_ref_known(v___x_3685_, 1);
v_perms_3687_ = lean_ctor_get(v_a_3686_, 1);
lean_inc_ref_n(v_perms_3687_, 2);
v___x_3688_ = lean_array_get_borrowed(v___x_3672_, v_a_3683_, v___x_3673_);
v_type_3689_ = lean_ctor_get(v___x_3688_, 6);
lean_inc_ref(v_type_3689_);
v___x_3690_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0);
v___x_3691_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___boxed__const__1));
v___f_3692_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__2___boxed), 12, 6);
lean_closure_set(v___f_3692_, 0, v_a_3683_);
lean_closure_set(v___f_3692_, 1, v_perms_3687_);
lean_closure_set(v___f_3692_, 2, v___x_3691_);
lean_closure_set(v___f_3692_, 3, v_fnNames_3678_);
lean_closure_set(v___f_3692_, 4, v_a_3686_);
lean_closure_set(v___f_3692_, 5, v_termMeasure_x3fs_3666_);
v___x_3693_ = lean_array_get(v___x_3690_, v_perms_3687_, v___x_3673_);
lean_dec_ref(v_perms_3687_);
v___x_3694_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg(v___x_3693_, v_type_3689_, v___f_3692_, v_a_3667_, v_a_3668_, v_a_3669_, v_a_3670_);
return v___x_3694_;
}
else
{
lean_object* v_a_3695_; lean_object* v___x_3697_; uint8_t v_isShared_3698_; uint8_t v_isSharedCheck_3702_; 
lean_dec(v_a_3683_);
lean_dec_ref(v_fnNames_3678_);
lean_dec_ref(v_termMeasure_x3fs_3666_);
v_a_3695_ = lean_ctor_get(v___x_3685_, 0);
v_isSharedCheck_3702_ = !lean_is_exclusive(v___x_3685_);
if (v_isSharedCheck_3702_ == 0)
{
v___x_3697_ = v___x_3685_;
v_isShared_3698_ = v_isSharedCheck_3702_;
goto v_resetjp_3696_;
}
else
{
lean_inc(v_a_3695_);
lean_dec(v___x_3685_);
v___x_3697_ = lean_box(0);
v_isShared_3698_ = v_isSharedCheck_3702_;
goto v_resetjp_3696_;
}
v_resetjp_3696_:
{
lean_object* v___x_3700_; 
if (v_isShared_3698_ == 0)
{
v___x_3700_ = v___x_3697_;
goto v_reusejp_3699_;
}
else
{
lean_object* v_reuseFailAlloc_3701_; 
v_reuseFailAlloc_3701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3701_, 0, v_a_3695_);
v___x_3700_ = v_reuseFailAlloc_3701_;
goto v_reusejp_3699_;
}
v_reusejp_3699_:
{
return v___x_3700_;
}
}
}
}
else
{
lean_object* v_a_3703_; lean_object* v___x_3705_; uint8_t v_isShared_3706_; uint8_t v_isSharedCheck_3710_; 
lean_dec_ref(v_fnNames_3678_);
lean_dec_ref(v_termMeasure_x3fs_3666_);
v_a_3703_ = lean_ctor_get(v___x_3682_, 0);
v_isSharedCheck_3710_ = !lean_is_exclusive(v___x_3682_);
if (v_isSharedCheck_3710_ == 0)
{
v___x_3705_ = v___x_3682_;
v_isShared_3706_ = v_isSharedCheck_3710_;
goto v_resetjp_3704_;
}
else
{
lean_inc(v_a_3703_);
lean_dec(v___x_3682_);
v___x_3705_ = lean_box(0);
v_isShared_3706_ = v_isSharedCheck_3710_;
goto v_resetjp_3704_;
}
v_resetjp_3704_:
{
lean_object* v___x_3708_; 
if (v_isShared_3706_ == 0)
{
v___x_3708_ = v___x_3705_;
goto v_reusejp_3707_;
}
else
{
lean_object* v_reuseFailAlloc_3709_; 
v_reuseFailAlloc_3709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3709_, 0, v_a_3703_);
v___x_3708_ = v_reuseFailAlloc_3709_;
goto v_reusejp_3707_;
}
v_reusejp_3707_:
{
return v___x_3708_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___boxed(lean_object* v_preDefs_3711_, lean_object* v_termMeasure_x3fs_3712_, lean_object* v_a_3713_, lean_object* v_a_3714_, lean_object* v_a_3715_, lean_object* v_a_3716_, lean_object* v_a_3717_){
_start:
{
lean_object* v_res_3718_; 
v_res_3718_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos(v_preDefs_3711_, v_termMeasure_x3fs_3712_, v_a_3713_, v_a_3714_, v_a_3715_, v_a_3716_);
lean_dec(v_a_3716_);
lean_dec_ref(v_a_3715_);
lean_dec(v_a_3714_);
lean_dec_ref(v_a_3713_);
return v_res_3718_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4(lean_object* v_fst_3719_, lean_object* v_as_3720_, size_t v_sz_3721_, size_t v_i_3722_, lean_object* v_bs_3723_){
_start:
{
lean_object* v___x_3724_; 
v___x_3724_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg(v_fst_3719_, v_sz_3721_, v_i_3722_, v_bs_3723_);
return v___x_3724_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___boxed(lean_object* v_fst_3725_, lean_object* v_as_3726_, lean_object* v_sz_3727_, lean_object* v_i_3728_, lean_object* v_bs_3729_){
_start:
{
size_t v_sz_boxed_3730_; size_t v_i_boxed_3731_; lean_object* v_res_3732_; 
v_sz_boxed_3730_ = lean_unbox_usize(v_sz_3727_);
lean_dec(v_sz_3727_);
v_i_boxed_3731_ = lean_unbox_usize(v_i_3728_);
lean_dec(v_i_3728_);
v_res_3732_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4(v_fst_3725_, v_as_3726_, v_sz_boxed_3730_, v_i_boxed_3731_, v_bs_3729_);
lean_dec_ref(v_as_3726_);
lean_dec_ref(v_fst_3725_);
return v_res_3732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10(lean_object* v_00_u03b1_3733_, lean_object* v_lctx_3734_, lean_object* v_localInsts_3735_, lean_object* v_x_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_){
_start:
{
lean_object* v___x_3742_; 
v___x_3742_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___redArg(v_lctx_3734_, v_localInsts_3735_, v_x_3736_, v___y_3737_, v___y_3738_, v___y_3739_, v___y_3740_);
return v___x_3742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___boxed(lean_object* v_00_u03b1_3743_, lean_object* v_lctx_3744_, lean_object* v_localInsts_3745_, lean_object* v_x_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_){
_start:
{
lean_object* v_res_3752_; 
v_res_3752_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10(v_00_u03b1_3743_, v_lctx_3744_, v_localInsts_3745_, v_x_3746_, v___y_3747_, v___y_3748_, v___y_3749_, v___y_3750_);
lean_dec(v___y_3750_);
lean_dec_ref(v___y_3749_);
lean_dec(v___y_3748_);
lean_dec_ref(v___y_3747_);
return v_res_3752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9(lean_object* v_00_u03b1_3753_, lean_object* v_fvarIds_3754_, lean_object* v_k_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_){
_start:
{
lean_object* v___x_3761_; 
v___x_3761_ = l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___redArg(v_fvarIds_3754_, v_k_3755_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_);
return v___x_3761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___boxed(lean_object* v_00_u03b1_3762_, lean_object* v_fvarIds_3763_, lean_object* v_k_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_){
_start:
{
lean_object* v_res_3770_; 
v_res_3770_ = l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9(v_00_u03b1_3762_, v_fvarIds_3763_, v_k_3764_, v___y_3765_, v___y_3766_, v___y_3767_, v___y_3768_);
lean_dec(v___y_3768_);
lean_dec_ref(v___y_3767_);
lean_dec(v___y_3766_);
lean_dec_ref(v___y_3765_);
lean_dec_ref(v_fvarIds_3763_);
return v_res_3770_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__15(lean_object* v_a_3771_){
_start:
{
lean_object* v___x_3772_; 
v___x_3772_ = lean_nat_to_int(v_a_3771_);
return v___x_3772_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12(lean_object* v___x_3773_, lean_object* v_xs_3774_, lean_object* v_as_3775_, size_t v_sz_3776_, size_t v_i_3777_, lean_object* v_bs_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_){
_start:
{
lean_object* v___x_3784_; 
v___x_3784_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg(v___x_3773_, v_xs_3774_, v_sz_3776_, v_i_3777_, v_bs_3778_, v___y_3779_, v___y_3780_, v___y_3781_, v___y_3782_);
return v___x_3784_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___boxed(lean_object* v___x_3785_, lean_object* v_xs_3786_, lean_object* v_as_3787_, lean_object* v_sz_3788_, lean_object* v_i_3789_, lean_object* v_bs_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_){
_start:
{
size_t v_sz_boxed_3796_; size_t v_i_boxed_3797_; lean_object* v_res_3798_; 
v_sz_boxed_3796_ = lean_unbox_usize(v_sz_3788_);
lean_dec(v_sz_3788_);
v_i_boxed_3797_ = lean_unbox_usize(v_i_3789_);
lean_dec(v_i_3789_);
v_res_3798_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12(v___x_3785_, v_xs_3786_, v_as_3787_, v_sz_boxed_3796_, v_i_boxed_3797_, v_bs_3790_, v___y_3791_, v___y_3792_, v___y_3793_, v___y_3794_);
lean_dec(v___y_3794_);
lean_dec_ref(v___y_3793_);
lean_dec(v___y_3792_);
lean_dec_ref(v___y_3791_);
lean_dec_ref(v_as_3787_);
lean_dec_ref(v___x_3785_);
return v_res_3798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure___lam__0(lean_object* v___x_3799_, lean_object* v_recArgPos_3800_, lean_object* v_xs_3801_, lean_object* v_x_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_){
_start:
{
lean_object* v___x_3808_; uint8_t v___x_3809_; uint8_t v___x_3810_; uint8_t v___x_3811_; lean_object* v___x_3812_; 
v___x_3808_ = lean_array_get_borrowed(v___x_3799_, v_xs_3801_, v_recArgPos_3800_);
v___x_3809_ = 0;
v___x_3810_ = 1;
v___x_3811_ = 1;
lean_inc(v___x_3808_);
v___x_3812_ = l_Lean_Meta_mkLambdaFVars(v_xs_3801_, v___x_3808_, v___x_3809_, v___x_3810_, v___x_3809_, v___x_3810_, v___x_3811_, v___y_3803_, v___y_3804_, v___y_3805_, v___y_3806_);
return v___x_3812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure___lam__0___boxed(lean_object* v___x_3813_, lean_object* v_recArgPos_3814_, lean_object* v_xs_3815_, lean_object* v_x_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_){
_start:
{
lean_object* v_res_3822_; 
v_res_3822_ = l_Lean_Elab_Structural_reportTermMeasure___lam__0(v___x_3813_, v_recArgPos_3814_, v_xs_3815_, v_x_3816_, v___y_3817_, v___y_3818_, v___y_3819_, v___y_3820_);
lean_dec(v___y_3820_);
lean_dec_ref(v___y_3819_);
lean_dec(v___y_3818_);
lean_dec_ref(v___y_3817_);
lean_dec_ref(v_x_3816_);
lean_dec_ref(v_xs_3815_);
lean_dec(v_recArgPos_3814_);
lean_dec_ref(v___x_3813_);
return v_res_3822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure___lam__1(lean_object* v_xs_3823_, lean_object* v_x_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_){
_start:
{
lean_object* v___x_3830_; lean_object* v___x_3831_; 
v___x_3830_ = lean_array_get_size(v_xs_3823_);
v___x_3831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3831_, 0, v___x_3830_);
return v___x_3831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure___lam__1___boxed(lean_object* v_xs_3832_, lean_object* v_x_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_){
_start:
{
lean_object* v_res_3839_; 
v_res_3839_ = l_Lean_Elab_Structural_reportTermMeasure___lam__1(v_xs_3832_, v_x_3833_, v___y_3834_, v___y_3835_, v___y_3836_, v___y_3837_);
lean_dec(v___y_3837_);
lean_dec_ref(v___y_3836_);
lean_dec(v___y_3835_);
lean_dec_ref(v___y_3834_);
lean_dec_ref(v_x_3833_);
lean_dec_ref(v_xs_3832_);
return v_res_3839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure(lean_object* v_preDef_3851_, lean_object* v_recArgPos_3852_, lean_object* v_a_3853_, lean_object* v_a_3854_, lean_object* v_a_3855_, lean_object* v_a_3856_){
_start:
{
lean_object* v_termination_3858_; lean_object* v_terminationBy_x3f_x3f_3859_; 
v_termination_3858_ = lean_ctor_get(v_preDef_3851_, 8);
lean_inc_ref(v_termination_3858_);
v_terminationBy_x3f_x3f_3859_ = lean_ctor_get(v_termination_3858_, 1);
lean_inc(v_terminationBy_x3f_x3f_3859_);
if (lean_obj_tag(v_terminationBy_x3f_x3f_3859_) == 1)
{
lean_object* v_value_3860_; lean_object* v_extraParams_3861_; lean_object* v___x_3863_; uint8_t v_isShared_3864_; uint8_t v_isSharedCheck_3913_; 
v_value_3860_ = lean_ctor_get(v_preDef_3851_, 7);
lean_inc_ref(v_value_3860_);
lean_dec_ref(v_preDef_3851_);
v_extraParams_3861_ = lean_ctor_get(v_termination_3858_, 5);
v_isSharedCheck_3913_ = !lean_is_exclusive(v_termination_3858_);
if (v_isSharedCheck_3913_ == 0)
{
lean_object* v_unused_3914_; lean_object* v_unused_3915_; lean_object* v_unused_3916_; lean_object* v_unused_3917_; lean_object* v_unused_3918_; 
v_unused_3914_ = lean_ctor_get(v_termination_3858_, 4);
lean_dec(v_unused_3914_);
v_unused_3915_ = lean_ctor_get(v_termination_3858_, 3);
lean_dec(v_unused_3915_);
v_unused_3916_ = lean_ctor_get(v_termination_3858_, 2);
lean_dec(v_unused_3916_);
v_unused_3917_ = lean_ctor_get(v_termination_3858_, 1);
lean_dec(v_unused_3917_);
v_unused_3918_ = lean_ctor_get(v_termination_3858_, 0);
lean_dec(v_unused_3918_);
v___x_3863_ = v_termination_3858_;
v_isShared_3864_ = v_isSharedCheck_3913_;
goto v_resetjp_3862_;
}
else
{
lean_inc(v_extraParams_3861_);
lean_dec(v_termination_3858_);
v___x_3863_ = lean_box(0);
v_isShared_3864_ = v_isSharedCheck_3913_;
goto v_resetjp_3862_;
}
v_resetjp_3862_:
{
lean_object* v_val_3865_; lean_object* v___x_3866_; lean_object* v___f_3867_; uint8_t v___x_3868_; lean_object* v___x_3869_; 
v_val_3865_ = lean_ctor_get(v_terminationBy_x3f_x3f_3859_, 0);
lean_inc(v_val_3865_);
lean_dec_ref_known(v_terminationBy_x3f_x3f_3859_, 1);
v___x_3866_ = l_Lean_instInhabitedExpr;
v___f_3867_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_reportTermMeasure___lam__0___boxed), 9, 2);
lean_closure_set(v___f_3867_, 0, v___x_3866_);
lean_closure_set(v___f_3867_, 1, v_recArgPos_3852_);
v___x_3868_ = 0;
lean_inc_ref(v_value_3860_);
v___x_3869_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg(v_value_3860_, v___f_3867_, v___x_3868_, v_a_3853_, v_a_3854_, v_a_3855_, v_a_3856_);
if (lean_obj_tag(v___x_3869_) == 0)
{
lean_object* v_a_3870_; lean_object* v___f_3871_; lean_object* v___x_3872_; 
v_a_3870_ = lean_ctor_get(v___x_3869_, 0);
lean_inc(v_a_3870_);
lean_dec_ref_known(v___x_3869_, 1);
v___f_3871_ = ((lean_object*)(l_Lean_Elab_Structural_reportTermMeasure___closed__0));
v___x_3872_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg(v_value_3860_, v___f_3871_, v___x_3868_, v_a_3853_, v_a_3854_, v_a_3855_, v_a_3856_);
if (lean_obj_tag(v___x_3872_) == 0)
{
lean_object* v_a_3873_; lean_object* v___x_3874_; uint8_t v___x_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; 
v_a_3873_ = lean_ctor_get(v___x_3872_, 0);
lean_inc(v_a_3873_);
lean_dec_ref_known(v___x_3872_, 1);
v___x_3874_ = lean_box(0);
v___x_3875_ = 1;
v___x_3876_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3876_, 0, v___x_3874_);
lean_ctor_set(v___x_3876_, 1, v_a_3870_);
lean_ctor_set_uint8(v___x_3876_, sizeof(void*)*2, v___x_3875_);
v___x_3877_ = l_Lean_Elab_TerminationMeasure_delab(v_a_3873_, v_extraParams_3861_, v___x_3876_, v_a_3853_, v_a_3854_, v_a_3855_, v_a_3856_);
lean_dec(v_a_3873_);
if (lean_obj_tag(v___x_3877_) == 0)
{
lean_object* v_a_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3883_; 
v_a_3878_ = lean_ctor_get(v___x_3877_, 0);
lean_inc(v_a_3878_);
lean_dec_ref_known(v___x_3877_, 1);
v___x_3879_ = ((lean_object*)(l_Lean_Elab_Structural_reportTermMeasure___closed__5));
v___x_3880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3880_, 0, v___x_3879_);
lean_ctor_set(v___x_3880_, 1, v_a_3878_);
v___x_3881_ = lean_box(0);
if (v_isShared_3864_ == 0)
{
lean_ctor_set(v___x_3863_, 5, v___x_3881_);
lean_ctor_set(v___x_3863_, 4, v___x_3881_);
lean_ctor_set(v___x_3863_, 3, v___x_3881_);
lean_ctor_set(v___x_3863_, 2, v___x_3881_);
lean_ctor_set(v___x_3863_, 1, v___x_3881_);
lean_ctor_set(v___x_3863_, 0, v___x_3880_);
v___x_3883_ = v___x_3863_;
goto v_reusejp_3882_;
}
else
{
lean_object* v_reuseFailAlloc_3888_; 
v_reuseFailAlloc_3888_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3888_, 0, v___x_3880_);
lean_ctor_set(v_reuseFailAlloc_3888_, 1, v___x_3881_);
lean_ctor_set(v_reuseFailAlloc_3888_, 2, v___x_3881_);
lean_ctor_set(v_reuseFailAlloc_3888_, 3, v___x_3881_);
lean_ctor_set(v_reuseFailAlloc_3888_, 4, v___x_3881_);
lean_ctor_set(v_reuseFailAlloc_3888_, 5, v___x_3881_);
v___x_3883_ = v_reuseFailAlloc_3888_;
goto v_reusejp_3882_;
}
v_reusejp_3882_:
{
lean_object* v___x_3884_; uint8_t v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; 
v___x_3884_ = ((lean_object*)(l_Lean_Elab_Structural_reportTermMeasure___closed__6));
v___x_3885_ = 4;
v___x_3886_ = l_Lean_MessageData_nil;
v___x_3887_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_val_3865_, v___x_3883_, v___x_3881_, v___x_3884_, v___x_3881_, v___x_3885_, v___x_3886_, v_a_3855_, v_a_3856_);
return v___x_3887_;
}
}
else
{
lean_object* v_a_3889_; lean_object* v___x_3891_; uint8_t v_isShared_3892_; uint8_t v_isSharedCheck_3896_; 
lean_dec(v_val_3865_);
lean_del_object(v___x_3863_);
v_a_3889_ = lean_ctor_get(v___x_3877_, 0);
v_isSharedCheck_3896_ = !lean_is_exclusive(v___x_3877_);
if (v_isSharedCheck_3896_ == 0)
{
v___x_3891_ = v___x_3877_;
v_isShared_3892_ = v_isSharedCheck_3896_;
goto v_resetjp_3890_;
}
else
{
lean_inc(v_a_3889_);
lean_dec(v___x_3877_);
v___x_3891_ = lean_box(0);
v_isShared_3892_ = v_isSharedCheck_3896_;
goto v_resetjp_3890_;
}
v_resetjp_3890_:
{
lean_object* v___x_3894_; 
if (v_isShared_3892_ == 0)
{
v___x_3894_ = v___x_3891_;
goto v_reusejp_3893_;
}
else
{
lean_object* v_reuseFailAlloc_3895_; 
v_reuseFailAlloc_3895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3895_, 0, v_a_3889_);
v___x_3894_ = v_reuseFailAlloc_3895_;
goto v_reusejp_3893_;
}
v_reusejp_3893_:
{
return v___x_3894_;
}
}
}
}
else
{
lean_object* v_a_3897_; lean_object* v___x_3899_; uint8_t v_isShared_3900_; uint8_t v_isSharedCheck_3904_; 
lean_dec(v_a_3870_);
lean_dec(v_val_3865_);
lean_del_object(v___x_3863_);
lean_dec(v_extraParams_3861_);
v_a_3897_ = lean_ctor_get(v___x_3872_, 0);
v_isSharedCheck_3904_ = !lean_is_exclusive(v___x_3872_);
if (v_isSharedCheck_3904_ == 0)
{
v___x_3899_ = v___x_3872_;
v_isShared_3900_ = v_isSharedCheck_3904_;
goto v_resetjp_3898_;
}
else
{
lean_inc(v_a_3897_);
lean_dec(v___x_3872_);
v___x_3899_ = lean_box(0);
v_isShared_3900_ = v_isSharedCheck_3904_;
goto v_resetjp_3898_;
}
v_resetjp_3898_:
{
lean_object* v___x_3902_; 
if (v_isShared_3900_ == 0)
{
v___x_3902_ = v___x_3899_;
goto v_reusejp_3901_;
}
else
{
lean_object* v_reuseFailAlloc_3903_; 
v_reuseFailAlloc_3903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3903_, 0, v_a_3897_);
v___x_3902_ = v_reuseFailAlloc_3903_;
goto v_reusejp_3901_;
}
v_reusejp_3901_:
{
return v___x_3902_;
}
}
}
}
else
{
lean_object* v_a_3905_; lean_object* v___x_3907_; uint8_t v_isShared_3908_; uint8_t v_isSharedCheck_3912_; 
lean_dec(v_val_3865_);
lean_del_object(v___x_3863_);
lean_dec(v_extraParams_3861_);
lean_dec_ref(v_value_3860_);
v_a_3905_ = lean_ctor_get(v___x_3869_, 0);
v_isSharedCheck_3912_ = !lean_is_exclusive(v___x_3869_);
if (v_isSharedCheck_3912_ == 0)
{
v___x_3907_ = v___x_3869_;
v_isShared_3908_ = v_isSharedCheck_3912_;
goto v_resetjp_3906_;
}
else
{
lean_inc(v_a_3905_);
lean_dec(v___x_3869_);
v___x_3907_ = lean_box(0);
v_isShared_3908_ = v_isSharedCheck_3912_;
goto v_resetjp_3906_;
}
v_resetjp_3906_:
{
lean_object* v___x_3910_; 
if (v_isShared_3908_ == 0)
{
v___x_3910_ = v___x_3907_;
goto v_reusejp_3909_;
}
else
{
lean_object* v_reuseFailAlloc_3911_; 
v_reuseFailAlloc_3911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3911_, 0, v_a_3905_);
v___x_3910_ = v_reuseFailAlloc_3911_;
goto v_reusejp_3909_;
}
v_reusejp_3909_:
{
return v___x_3910_;
}
}
}
}
}
else
{
lean_object* v___x_3919_; lean_object* v___x_3920_; 
lean_dec(v_terminationBy_x3f_x3f_3859_);
lean_dec_ref(v_termination_3858_);
lean_dec(v_recArgPos_3852_);
lean_dec_ref(v_preDef_3851_);
v___x_3919_ = lean_box(0);
v___x_3920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3920_, 0, v___x_3919_);
return v___x_3920_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure___boxed(lean_object* v_preDef_3921_, lean_object* v_recArgPos_3922_, lean_object* v_a_3923_, lean_object* v_a_3924_, lean_object* v_a_3925_, lean_object* v_a_3926_, lean_object* v_a_3927_){
_start:
{
lean_object* v_res_3928_; 
v_res_3928_ = l_Lean_Elab_Structural_reportTermMeasure(v_preDef_3921_, v_recArgPos_3922_, v_a_3923_, v_a_3924_, v_a_3925_, v_a_3926_);
lean_dec(v_a_3926_);
lean_dec_ref(v_a_3925_);
lean_dec(v_a_3924_);
lean_dec_ref(v_a_3923_);
return v_res_3928_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___redArg(lean_object* v_as_3929_, size_t v_sz_3930_, size_t v_i_3931_, lean_object* v_b_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_){
_start:
{
uint8_t v___x_3938_; 
v___x_3938_ = lean_usize_dec_lt(v_i_3931_, v_sz_3930_);
if (v___x_3938_ == 0)
{
lean_object* v___x_3939_; 
v___x_3939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3939_, 0, v_b_3932_);
return v___x_3939_;
}
else
{
lean_object* v_a_3940_; lean_object* v_declName_3941_; lean_object* v___x_3942_; 
v_a_3940_ = lean_array_uget_borrowed(v_as_3929_, v_i_3931_);
v_declName_3941_ = lean_ctor_get(v_a_3940_, 3);
lean_inc(v_declName_3941_);
v___x_3942_ = l_Lean_Meta_saveEqnAffectingOptions(v_declName_3941_, v___y_3933_, v___y_3934_, v___y_3935_, v___y_3936_);
if (lean_obj_tag(v___x_3942_) == 0)
{
lean_object* v___x_3943_; size_t v___x_3944_; size_t v___x_3945_; 
lean_dec_ref_known(v___x_3942_, 1);
v___x_3943_ = lean_box(0);
v___x_3944_ = ((size_t)1ULL);
v___x_3945_ = lean_usize_add(v_i_3931_, v___x_3944_);
v_i_3931_ = v___x_3945_;
v_b_3932_ = v___x_3943_;
goto _start;
}
else
{
return v___x_3942_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___redArg___boxed(lean_object* v_as_3947_, lean_object* v_sz_3948_, lean_object* v_i_3949_, lean_object* v_b_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_){
_start:
{
size_t v_sz_boxed_3956_; size_t v_i_boxed_3957_; lean_object* v_res_3958_; 
v_sz_boxed_3956_ = lean_unbox_usize(v_sz_3948_);
lean_dec(v_sz_3948_);
v_i_boxed_3957_ = lean_unbox_usize(v_i_3949_);
lean_dec(v_i_3949_);
v_res_3958_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___redArg(v_as_3947_, v_sz_boxed_3956_, v_i_boxed_3957_, v_b_3950_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_);
lean_dec(v___y_3954_);
lean_dec_ref(v___y_3953_);
lean_dec(v___y_3952_);
lean_dec_ref(v___y_3951_);
lean_dec_ref(v_as_3947_);
return v_res_3958_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__1(lean_object* v_docCtx_3959_, lean_object* v_a_3960_, lean_object* v_snd_3961_, lean_object* v_as_3962_, size_t v_sz_3963_, size_t v_i_3964_, lean_object* v_b_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_){
_start:
{
uint8_t v___x_3973_; 
v___x_3973_ = lean_usize_dec_lt(v_i_3964_, v_sz_3963_);
if (v___x_3973_ == 0)
{
lean_object* v___x_3974_; 
lean_dec_ref(v_snd_3961_);
lean_dec_ref(v_a_3960_);
lean_dec_ref(v_docCtx_3959_);
v___x_3974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3974_, 0, v_b_3965_);
return v___x_3974_;
}
else
{
lean_object* v_array_3975_; lean_object* v_start_3976_; lean_object* v_stop_3977_; uint8_t v___x_3978_; 
v_array_3975_ = lean_ctor_get(v_b_3965_, 0);
v_start_3976_ = lean_ctor_get(v_b_3965_, 1);
v_stop_3977_ = lean_ctor_get(v_b_3965_, 2);
v___x_3978_ = lean_nat_dec_lt(v_start_3976_, v_stop_3977_);
if (v___x_3978_ == 0)
{
lean_object* v___x_3979_; 
lean_dec_ref(v_snd_3961_);
lean_dec_ref(v_a_3960_);
lean_dec_ref(v_docCtx_3959_);
v___x_3979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3979_, 0, v_b_3965_);
return v___x_3979_;
}
else
{
lean_object* v___x_3981_; uint8_t v_isShared_3982_; uint8_t v_isSharedCheck_4046_; 
lean_inc(v_stop_3977_);
lean_inc(v_start_3976_);
lean_inc_ref(v_array_3975_);
v_isSharedCheck_4046_ = !lean_is_exclusive(v_b_3965_);
if (v_isSharedCheck_4046_ == 0)
{
lean_object* v_unused_4047_; lean_object* v_unused_4048_; lean_object* v_unused_4049_; 
v_unused_4047_ = lean_ctor_get(v_b_3965_, 2);
lean_dec(v_unused_4047_);
v_unused_4048_ = lean_ctor_get(v_b_3965_, 1);
lean_dec(v_unused_4048_);
v_unused_4049_ = lean_ctor_get(v_b_3965_, 0);
lean_dec(v_unused_4049_);
v___x_3981_ = v_b_3965_;
v_isShared_3982_ = v_isSharedCheck_4046_;
goto v_resetjp_3980_;
}
else
{
lean_dec(v_b_3965_);
v___x_3981_ = lean_box(0);
v_isShared_3982_ = v_isSharedCheck_4046_;
goto v_resetjp_3980_;
}
v_resetjp_3980_:
{
lean_object* v_a_3983_; uint8_t v_kind_3984_; lean_object* v_type_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3990_; 
v_a_3983_ = lean_array_uget_borrowed(v_as_3962_, v_i_3964_);
v_kind_3984_ = lean_ctor_get_uint8(v_a_3983_, sizeof(void*)*9);
v_type_3985_ = lean_ctor_get(v_a_3983_, 6);
v___x_3986_ = lean_array_fget(v_array_3975_, v_start_3976_);
v___x_3987_ = lean_unsigned_to_nat(1u);
v___x_3988_ = lean_nat_add(v_start_3976_, v___x_3987_);
lean_dec(v_start_3976_);
if (v_isShared_3982_ == 0)
{
lean_ctor_set(v___x_3981_, 1, v___x_3988_);
v___x_3990_ = v___x_3981_;
goto v_reusejp_3989_;
}
else
{
lean_object* v_reuseFailAlloc_4045_; 
v_reuseFailAlloc_4045_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4045_, 0, v_array_3975_);
lean_ctor_set(v_reuseFailAlloc_4045_, 1, v___x_3988_);
lean_ctor_set(v_reuseFailAlloc_4045_, 2, v_stop_3977_);
v___x_3990_ = v_reuseFailAlloc_4045_;
goto v_reusejp_3989_;
}
v_reusejp_3989_:
{
lean_object* v_preDef_3992_; lean_object* v___y_3993_; lean_object* v___y_3994_; lean_object* v___y_3995_; lean_object* v___y_3996_; lean_object* v___y_3997_; lean_object* v___y_3998_; uint8_t v___x_4011_; 
v___x_4011_ = l_Lean_Elab_DefKind_isTheorem(v_kind_3984_);
if (v___x_4011_ == 0)
{
lean_object* v___x_4012_; 
lean_inc_ref(v_type_3985_);
v___x_4012_ = l_Lean_Meta_isProp(v_type_3985_, v___y_3968_, v___y_3969_, v___y_3970_, v___y_3971_);
if (lean_obj_tag(v___x_4012_) == 0)
{
lean_object* v_a_4013_; uint8_t v___x_4014_; 
v_a_4013_ = lean_ctor_get(v___x_4012_, 0);
lean_inc(v_a_4013_);
lean_dec_ref_known(v___x_4012_, 1);
v___x_4014_ = lean_unbox(v_a_4013_);
lean_dec(v_a_4013_);
if (v___x_4014_ == 0)
{
lean_object* v___x_4015_; 
lean_inc(v_a_3983_);
v___x_4015_ = l_Lean_Elab_abstractNestedProofs(v_a_3983_, v___x_3978_, v___y_3968_, v___y_3969_, v___y_3970_, v___y_3971_);
if (lean_obj_tag(v___x_4015_) == 0)
{
lean_object* v_a_4016_; size_t v_sz_4017_; size_t v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; 
v_a_4016_ = lean_ctor_get(v___x_4015_, 0);
lean_inc_n(v_a_4016_, 2);
lean_dec_ref_known(v___x_4015_, 1);
v_sz_4017_ = lean_array_size(v_a_3960_);
v___x_4018_ = ((size_t)0ULL);
lean_inc_ref(v_a_3960_);
v___x_4019_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0(v_sz_4017_, v___x_4018_, v_a_3960_);
lean_inc_ref(v_snd_3961_);
lean_inc(v___x_3986_);
v___x_4020_ = l_Lean_Elab_Structural_registerEqnsInfo(v_a_4016_, v___x_4019_, v___x_3986_, v_snd_3961_, v___y_3970_, v___y_3971_);
if (lean_obj_tag(v___x_4020_) == 0)
{
lean_dec_ref_known(v___x_4020_, 1);
v_preDef_3992_ = v_a_4016_;
v___y_3993_ = v___y_3966_;
v___y_3994_ = v___y_3967_;
v___y_3995_ = v___y_3968_;
v___y_3996_ = v___y_3969_;
v___y_3997_ = v___y_3970_;
v___y_3998_ = v___y_3971_;
goto v___jp_3991_;
}
else
{
lean_object* v_a_4021_; lean_object* v___x_4023_; uint8_t v_isShared_4024_; uint8_t v_isSharedCheck_4028_; 
lean_dec(v_a_4016_);
lean_dec_ref(v___x_3990_);
lean_dec(v___x_3986_);
lean_dec_ref(v_snd_3961_);
lean_dec_ref(v_a_3960_);
lean_dec_ref(v_docCtx_3959_);
v_a_4021_ = lean_ctor_get(v___x_4020_, 0);
v_isSharedCheck_4028_ = !lean_is_exclusive(v___x_4020_);
if (v_isSharedCheck_4028_ == 0)
{
v___x_4023_ = v___x_4020_;
v_isShared_4024_ = v_isSharedCheck_4028_;
goto v_resetjp_4022_;
}
else
{
lean_inc(v_a_4021_);
lean_dec(v___x_4020_);
v___x_4023_ = lean_box(0);
v_isShared_4024_ = v_isSharedCheck_4028_;
goto v_resetjp_4022_;
}
v_resetjp_4022_:
{
lean_object* v___x_4026_; 
if (v_isShared_4024_ == 0)
{
v___x_4026_ = v___x_4023_;
goto v_reusejp_4025_;
}
else
{
lean_object* v_reuseFailAlloc_4027_; 
v_reuseFailAlloc_4027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4027_, 0, v_a_4021_);
v___x_4026_ = v_reuseFailAlloc_4027_;
goto v_reusejp_4025_;
}
v_reusejp_4025_:
{
return v___x_4026_;
}
}
}
}
else
{
lean_object* v_a_4029_; lean_object* v___x_4031_; uint8_t v_isShared_4032_; uint8_t v_isSharedCheck_4036_; 
lean_dec_ref(v___x_3990_);
lean_dec(v___x_3986_);
lean_dec_ref(v_snd_3961_);
lean_dec_ref(v_a_3960_);
lean_dec_ref(v_docCtx_3959_);
v_a_4029_ = lean_ctor_get(v___x_4015_, 0);
v_isSharedCheck_4036_ = !lean_is_exclusive(v___x_4015_);
if (v_isSharedCheck_4036_ == 0)
{
v___x_4031_ = v___x_4015_;
v_isShared_4032_ = v_isSharedCheck_4036_;
goto v_resetjp_4030_;
}
else
{
lean_inc(v_a_4029_);
lean_dec(v___x_4015_);
v___x_4031_ = lean_box(0);
v_isShared_4032_ = v_isSharedCheck_4036_;
goto v_resetjp_4030_;
}
v_resetjp_4030_:
{
lean_object* v___x_4034_; 
if (v_isShared_4032_ == 0)
{
v___x_4034_ = v___x_4031_;
goto v_reusejp_4033_;
}
else
{
lean_object* v_reuseFailAlloc_4035_; 
v_reuseFailAlloc_4035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4035_, 0, v_a_4029_);
v___x_4034_ = v_reuseFailAlloc_4035_;
goto v_reusejp_4033_;
}
v_reusejp_4033_:
{
return v___x_4034_;
}
}
}
}
else
{
lean_inc(v_a_3983_);
v_preDef_3992_ = v_a_3983_;
v___y_3993_ = v___y_3966_;
v___y_3994_ = v___y_3967_;
v___y_3995_ = v___y_3968_;
v___y_3996_ = v___y_3969_;
v___y_3997_ = v___y_3970_;
v___y_3998_ = v___y_3971_;
goto v___jp_3991_;
}
}
else
{
lean_object* v_a_4037_; lean_object* v___x_4039_; uint8_t v_isShared_4040_; uint8_t v_isSharedCheck_4044_; 
lean_dec_ref(v___x_3990_);
lean_dec(v___x_3986_);
lean_dec_ref(v_snd_3961_);
lean_dec_ref(v_a_3960_);
lean_dec_ref(v_docCtx_3959_);
v_a_4037_ = lean_ctor_get(v___x_4012_, 0);
v_isSharedCheck_4044_ = !lean_is_exclusive(v___x_4012_);
if (v_isSharedCheck_4044_ == 0)
{
v___x_4039_ = v___x_4012_;
v_isShared_4040_ = v_isSharedCheck_4044_;
goto v_resetjp_4038_;
}
else
{
lean_inc(v_a_4037_);
lean_dec(v___x_4012_);
v___x_4039_ = lean_box(0);
v_isShared_4040_ = v_isSharedCheck_4044_;
goto v_resetjp_4038_;
}
v_resetjp_4038_:
{
lean_object* v___x_4042_; 
if (v_isShared_4040_ == 0)
{
v___x_4042_ = v___x_4039_;
goto v_reusejp_4041_;
}
else
{
lean_object* v_reuseFailAlloc_4043_; 
v_reuseFailAlloc_4043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4043_, 0, v_a_4037_);
v___x_4042_ = v_reuseFailAlloc_4043_;
goto v_reusejp_4041_;
}
v_reusejp_4041_:
{
return v___x_4042_;
}
}
}
}
else
{
lean_inc(v_a_3983_);
v_preDef_3992_ = v_a_3983_;
v___y_3993_ = v___y_3966_;
v___y_3994_ = v___y_3967_;
v___y_3995_ = v___y_3968_;
v___y_3996_ = v___y_3969_;
v___y_3997_ = v___y_3970_;
v___y_3998_ = v___y_3971_;
goto v___jp_3991_;
}
v___jp_3991_:
{
lean_object* v___x_3999_; 
lean_inc_ref(v_docCtx_3959_);
v___x_3999_ = l_Lean_Elab_Structural_addSmartUnfoldingDef(v_docCtx_3959_, v_preDef_3992_, v___x_3986_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_, v___y_3997_, v___y_3998_);
if (lean_obj_tag(v___x_3999_) == 0)
{
size_t v___x_4000_; size_t v___x_4001_; 
lean_dec_ref_known(v___x_3999_, 1);
v___x_4000_ = ((size_t)1ULL);
v___x_4001_ = lean_usize_add(v_i_3964_, v___x_4000_);
v_i_3964_ = v___x_4001_;
v_b_3965_ = v___x_3990_;
goto _start;
}
else
{
lean_object* v_a_4003_; lean_object* v___x_4005_; uint8_t v_isShared_4006_; uint8_t v_isSharedCheck_4010_; 
lean_dec_ref(v___x_3990_);
lean_dec_ref(v_snd_3961_);
lean_dec_ref(v_a_3960_);
lean_dec_ref(v_docCtx_3959_);
v_a_4003_ = lean_ctor_get(v___x_3999_, 0);
v_isSharedCheck_4010_ = !lean_is_exclusive(v___x_3999_);
if (v_isSharedCheck_4010_ == 0)
{
v___x_4005_ = v___x_3999_;
v_isShared_4006_ = v_isSharedCheck_4010_;
goto v_resetjp_4004_;
}
else
{
lean_inc(v_a_4003_);
lean_dec(v___x_3999_);
v___x_4005_ = lean_box(0);
v_isShared_4006_ = v_isSharedCheck_4010_;
goto v_resetjp_4004_;
}
v_resetjp_4004_:
{
lean_object* v___x_4008_; 
if (v_isShared_4006_ == 0)
{
v___x_4008_ = v___x_4005_;
goto v_reusejp_4007_;
}
else
{
lean_object* v_reuseFailAlloc_4009_; 
v_reuseFailAlloc_4009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4009_, 0, v_a_4003_);
v___x_4008_ = v_reuseFailAlloc_4009_;
goto v_reusejp_4007_;
}
v_reusejp_4007_:
{
return v___x_4008_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__1___boxed(lean_object* v_docCtx_4050_, lean_object* v_a_4051_, lean_object* v_snd_4052_, lean_object* v_as_4053_, lean_object* v_sz_4054_, lean_object* v_i_4055_, lean_object* v_b_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_){
_start:
{
size_t v_sz_boxed_4064_; size_t v_i_boxed_4065_; lean_object* v_res_4066_; 
v_sz_boxed_4064_ = lean_unbox_usize(v_sz_4054_);
lean_dec(v_sz_4054_);
v_i_boxed_4065_ = lean_unbox_usize(v_i_4055_);
lean_dec(v_i_4055_);
v_res_4066_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__1(v_docCtx_4050_, v_a_4051_, v_snd_4052_, v_as_4053_, v_sz_boxed_4064_, v_i_boxed_4065_, v_b_4056_, v___y_4057_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_);
lean_dec(v___y_4062_);
lean_dec_ref(v___y_4061_);
lean_dec(v___y_4060_);
lean_dec_ref(v___y_4059_);
lean_dec(v___y_4058_);
lean_dec_ref(v___y_4057_);
lean_dec_ref(v_as_4053_);
return v_res_4066_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___lam__0(lean_object* v___x_4067_, lean_object* v_e_4068_){
_start:
{
lean_object* v___x_4069_; lean_object* v___x_4070_; 
v___x_4069_ = l_Lean_indentD(v_e_4068_);
v___x_4070_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4070_, 0, v___x_4067_);
lean_ctor_set(v___x_4070_, 1, v___x_4069_);
return v___x_4070_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___lam__1(lean_object* v_docCtx_4071_, lean_object* v_a_4072_, uint8_t v___x_4073_, lean_object* v___x_4074_, uint8_t v___x_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_){
_start:
{
lean_object* v___x_4083_; 
v___x_4083_ = l_Lean_Elab_addNonRec(v_docCtx_4071_, v_a_4072_, v___x_4073_, v___x_4074_, v___x_4075_, v___x_4073_, v___x_4075_, v___y_4076_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_, v___y_4081_);
return v___x_4083_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___lam__1___boxed(lean_object* v_docCtx_4084_, lean_object* v_a_4085_, lean_object* v___x_4086_, lean_object* v___x_4087_, lean_object* v___x_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_){
_start:
{
uint8_t v___x_9560__boxed_4096_; uint8_t v___x_9562__boxed_4097_; lean_object* v_res_4098_; 
v___x_9560__boxed_4096_ = lean_unbox(v___x_4086_);
v___x_9562__boxed_4097_ = lean_unbox(v___x_4088_);
v_res_4098_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___lam__1(v_docCtx_4084_, v_a_4085_, v___x_9560__boxed_4096_, v___x_4087_, v___x_9562__boxed_4097_, v___y_4089_, v___y_4090_, v___y_4091_, v___y_4092_, v___y_4093_, v___y_4094_);
lean_dec(v___y_4094_);
lean_dec_ref(v___y_4093_);
lean_dec(v___y_4092_);
lean_dec_ref(v___y_4091_);
lean_dec(v___y_4090_);
lean_dec_ref(v___y_4089_);
return v_res_4098_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__1(void){
_start:
{
lean_object* v___x_4100_; lean_object* v___x_4101_; 
v___x_4100_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__0));
v___x_4101_ = l_Lean_stringToMessageData(v___x_4100_);
return v___x_4101_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__2(void){
_start:
{
lean_object* v___x_4102_; lean_object* v___f_4103_; 
v___x_4102_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__1);
v___f_4103_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___lam__0), 2, 1);
lean_closure_set(v___f_4103_, 0, v___x_4102_);
return v___f_4103_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5(lean_object* v_names_4104_, lean_object* v_docCtx_4105_, lean_object* v_as_4106_, size_t v_i_4107_, size_t v_stop_4108_, lean_object* v_b_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_){
_start:
{
uint8_t v___x_4117_; 
v___x_4117_ = lean_usize_dec_eq(v_i_4107_, v_stop_4108_);
if (v___x_4117_ == 0)
{
lean_object* v___x_4118_; lean_object* v___x_4119_; 
v___x_4118_ = lean_array_uget_borrowed(v_as_4106_, v_i_4107_);
lean_inc(v___x_4118_);
v___x_4119_ = l_Lean_Elab_eraseRecAppSyntax(v___x_4118_, v___y_4114_, v___y_4115_);
if (lean_obj_tag(v___x_4119_) == 0)
{
lean_object* v_a_4120_; lean_object* v___f_4121_; lean_object* v___x_4122_; uint8_t v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___f_4126_; lean_object* v___x_4127_; 
v_a_4120_ = lean_ctor_get(v___x_4119_, 0);
lean_inc(v_a_4120_);
lean_dec_ref_known(v___x_4119_, 1);
v___f_4121_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__2);
lean_inc_ref(v_names_4104_);
v___x_4122_ = lean_array_to_list(v_names_4104_);
v___x_4123_ = 1;
v___x_4124_ = lean_box(v___x_4117_);
v___x_4125_ = lean_box(v___x_4123_);
lean_inc(v___y_4111_);
lean_inc_ref(v___y_4110_);
lean_inc_ref(v_docCtx_4105_);
v___f_4126_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___lam__1___boxed), 12, 7);
lean_closure_set(v___f_4126_, 0, v_docCtx_4105_);
lean_closure_set(v___f_4126_, 1, v_a_4120_);
lean_closure_set(v___f_4126_, 2, v___x_4124_);
lean_closure_set(v___f_4126_, 3, v___x_4122_);
lean_closure_set(v___f_4126_, 4, v___x_4125_);
lean_closure_set(v___f_4126_, 5, v___y_4110_);
lean_closure_set(v___f_4126_, 6, v___y_4111_);
v___x_4127_ = l_Lean_Meta_mapErrorImp___redArg(v___f_4126_, v___f_4121_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_);
if (lean_obj_tag(v___x_4127_) == 0)
{
if (lean_obj_tag(v___x_4127_) == 0)
{
lean_object* v_a_4128_; size_t v___x_4129_; size_t v___x_4130_; 
v_a_4128_ = lean_ctor_get(v___x_4127_, 0);
lean_inc(v_a_4128_);
lean_dec_ref_known(v___x_4127_, 1);
v___x_4129_ = ((size_t)1ULL);
v___x_4130_ = lean_usize_add(v_i_4107_, v___x_4129_);
v_i_4107_ = v___x_4130_;
v_b_4109_ = v_a_4128_;
goto _start;
}
else
{
lean_dec_ref(v_docCtx_4105_);
lean_dec_ref(v_names_4104_);
return v___x_4127_;
}
}
else
{
lean_object* v_a_4132_; lean_object* v___x_4134_; uint8_t v_isShared_4135_; uint8_t v_isSharedCheck_4139_; 
lean_dec_ref(v_docCtx_4105_);
lean_dec_ref(v_names_4104_);
v_a_4132_ = lean_ctor_get(v___x_4127_, 0);
v_isSharedCheck_4139_ = !lean_is_exclusive(v___x_4127_);
if (v_isSharedCheck_4139_ == 0)
{
v___x_4134_ = v___x_4127_;
v_isShared_4135_ = v_isSharedCheck_4139_;
goto v_resetjp_4133_;
}
else
{
lean_inc(v_a_4132_);
lean_dec(v___x_4127_);
v___x_4134_ = lean_box(0);
v_isShared_4135_ = v_isSharedCheck_4139_;
goto v_resetjp_4133_;
}
v_resetjp_4133_:
{
lean_object* v___x_4137_; 
if (v_isShared_4135_ == 0)
{
v___x_4137_ = v___x_4134_;
goto v_reusejp_4136_;
}
else
{
lean_object* v_reuseFailAlloc_4138_; 
v_reuseFailAlloc_4138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4138_, 0, v_a_4132_);
v___x_4137_ = v_reuseFailAlloc_4138_;
goto v_reusejp_4136_;
}
v_reusejp_4136_:
{
return v___x_4137_;
}
}
}
}
else
{
lean_object* v_a_4140_; lean_object* v___x_4142_; uint8_t v_isShared_4143_; uint8_t v_isSharedCheck_4147_; 
lean_dec_ref(v_docCtx_4105_);
lean_dec_ref(v_names_4104_);
v_a_4140_ = lean_ctor_get(v___x_4119_, 0);
v_isSharedCheck_4147_ = !lean_is_exclusive(v___x_4119_);
if (v_isSharedCheck_4147_ == 0)
{
v___x_4142_ = v___x_4119_;
v_isShared_4143_ = v_isSharedCheck_4147_;
goto v_resetjp_4141_;
}
else
{
lean_inc(v_a_4140_);
lean_dec(v___x_4119_);
v___x_4142_ = lean_box(0);
v_isShared_4143_ = v_isSharedCheck_4147_;
goto v_resetjp_4141_;
}
v_resetjp_4141_:
{
lean_object* v___x_4145_; 
if (v_isShared_4143_ == 0)
{
v___x_4145_ = v___x_4142_;
goto v_reusejp_4144_;
}
else
{
lean_object* v_reuseFailAlloc_4146_; 
v_reuseFailAlloc_4146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4146_, 0, v_a_4140_);
v___x_4145_ = v_reuseFailAlloc_4146_;
goto v_reusejp_4144_;
}
v_reusejp_4144_:
{
return v___x_4145_;
}
}
}
}
else
{
lean_object* v___x_4148_; 
lean_dec_ref(v_docCtx_4105_);
lean_dec_ref(v_names_4104_);
v___x_4148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4148_, 0, v_b_4109_);
return v___x_4148_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___boxed(lean_object* v_names_4149_, lean_object* v_docCtx_4150_, lean_object* v_as_4151_, lean_object* v_i_4152_, lean_object* v_stop_4153_, lean_object* v_b_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_){
_start:
{
size_t v_i_boxed_4162_; size_t v_stop_boxed_4163_; lean_object* v_res_4164_; 
v_i_boxed_4162_ = lean_unbox_usize(v_i_4152_);
lean_dec(v_i_4152_);
v_stop_boxed_4163_ = lean_unbox_usize(v_stop_4153_);
lean_dec(v_stop_4153_);
v_res_4164_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5(v_names_4149_, v_docCtx_4150_, v_as_4151_, v_i_boxed_4162_, v_stop_boxed_4163_, v_b_4154_, v___y_4155_, v___y_4156_, v___y_4157_, v___y_4158_, v___y_4159_, v___y_4160_);
lean_dec(v___y_4160_);
lean_dec_ref(v___y_4159_);
lean_dec(v___y_4158_);
lean_dec_ref(v___y_4157_);
lean_dec(v___y_4156_);
lean_dec_ref(v___y_4155_);
lean_dec_ref(v_as_4151_);
return v_res_4164_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4___redArg(lean_object* v_as_4165_, size_t v_sz_4166_, size_t v_i_4167_, lean_object* v_b_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_){
_start:
{
uint8_t v___x_4174_; 
v___x_4174_ = lean_usize_dec_lt(v_i_4167_, v_sz_4166_);
if (v___x_4174_ == 0)
{
lean_object* v___x_4175_; 
v___x_4175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4175_, 0, v_b_4168_);
return v___x_4175_;
}
else
{
lean_object* v_array_4176_; lean_object* v_start_4177_; lean_object* v_stop_4178_; uint8_t v___x_4179_; 
v_array_4176_ = lean_ctor_get(v_b_4168_, 0);
v_start_4177_ = lean_ctor_get(v_b_4168_, 1);
v_stop_4178_ = lean_ctor_get(v_b_4168_, 2);
v___x_4179_ = lean_nat_dec_lt(v_start_4177_, v_stop_4178_);
if (v___x_4179_ == 0)
{
lean_object* v___x_4180_; 
v___x_4180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4180_, 0, v_b_4168_);
return v___x_4180_;
}
else
{
lean_object* v___x_4182_; uint8_t v_isShared_4183_; uint8_t v_isSharedCheck_4203_; 
lean_inc(v_stop_4178_);
lean_inc(v_start_4177_);
lean_inc_ref(v_array_4176_);
v_isSharedCheck_4203_ = !lean_is_exclusive(v_b_4168_);
if (v_isSharedCheck_4203_ == 0)
{
lean_object* v_unused_4204_; lean_object* v_unused_4205_; lean_object* v_unused_4206_; 
v_unused_4204_ = lean_ctor_get(v_b_4168_, 2);
lean_dec(v_unused_4204_);
v_unused_4205_ = lean_ctor_get(v_b_4168_, 1);
lean_dec(v_unused_4205_);
v_unused_4206_ = lean_ctor_get(v_b_4168_, 0);
lean_dec(v_unused_4206_);
v___x_4182_ = v_b_4168_;
v_isShared_4183_ = v_isSharedCheck_4203_;
goto v_resetjp_4181_;
}
else
{
lean_dec(v_b_4168_);
v___x_4182_ = lean_box(0);
v_isShared_4183_ = v_isSharedCheck_4203_;
goto v_resetjp_4181_;
}
v_resetjp_4181_:
{
lean_object* v_a_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; 
v_a_4184_ = lean_array_uget_borrowed(v_as_4165_, v_i_4167_);
v___x_4185_ = lean_array_fget_borrowed(v_array_4176_, v_start_4177_);
lean_inc(v_a_4184_);
lean_inc(v___x_4185_);
v___x_4186_ = l_Lean_Elab_Structural_reportTermMeasure(v___x_4185_, v_a_4184_, v___y_4169_, v___y_4170_, v___y_4171_, v___y_4172_);
if (lean_obj_tag(v___x_4186_) == 0)
{
lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4190_; 
lean_dec_ref_known(v___x_4186_, 1);
v___x_4187_ = lean_unsigned_to_nat(1u);
v___x_4188_ = lean_nat_add(v_start_4177_, v___x_4187_);
lean_dec(v_start_4177_);
if (v_isShared_4183_ == 0)
{
lean_ctor_set(v___x_4182_, 1, v___x_4188_);
v___x_4190_ = v___x_4182_;
goto v_reusejp_4189_;
}
else
{
lean_object* v_reuseFailAlloc_4194_; 
v_reuseFailAlloc_4194_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4194_, 0, v_array_4176_);
lean_ctor_set(v_reuseFailAlloc_4194_, 1, v___x_4188_);
lean_ctor_set(v_reuseFailAlloc_4194_, 2, v_stop_4178_);
v___x_4190_ = v_reuseFailAlloc_4194_;
goto v_reusejp_4189_;
}
v_reusejp_4189_:
{
size_t v___x_4191_; size_t v___x_4192_; 
v___x_4191_ = ((size_t)1ULL);
v___x_4192_ = lean_usize_add(v_i_4167_, v___x_4191_);
v_i_4167_ = v___x_4192_;
v_b_4168_ = v___x_4190_;
goto _start;
}
}
else
{
lean_object* v_a_4195_; lean_object* v___x_4197_; uint8_t v_isShared_4198_; uint8_t v_isSharedCheck_4202_; 
lean_del_object(v___x_4182_);
lean_dec(v_stop_4178_);
lean_dec(v_start_4177_);
lean_dec_ref(v_array_4176_);
v_a_4195_ = lean_ctor_get(v___x_4186_, 0);
v_isSharedCheck_4202_ = !lean_is_exclusive(v___x_4186_);
if (v_isSharedCheck_4202_ == 0)
{
v___x_4197_ = v___x_4186_;
v_isShared_4198_ = v_isSharedCheck_4202_;
goto v_resetjp_4196_;
}
else
{
lean_inc(v_a_4195_);
lean_dec(v___x_4186_);
v___x_4197_ = lean_box(0);
v_isShared_4198_ = v_isSharedCheck_4202_;
goto v_resetjp_4196_;
}
v_resetjp_4196_:
{
lean_object* v___x_4200_; 
if (v_isShared_4198_ == 0)
{
v___x_4200_ = v___x_4197_;
goto v_reusejp_4199_;
}
else
{
lean_object* v_reuseFailAlloc_4201_; 
v_reuseFailAlloc_4201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4201_, 0, v_a_4195_);
v___x_4200_ = v_reuseFailAlloc_4201_;
goto v_reusejp_4199_;
}
v_reusejp_4199_:
{
return v___x_4200_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4___redArg___boxed(lean_object* v_as_4207_, lean_object* v_sz_4208_, lean_object* v_i_4209_, lean_object* v_b_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_){
_start:
{
size_t v_sz_boxed_4216_; size_t v_i_boxed_4217_; lean_object* v_res_4218_; 
v_sz_boxed_4216_ = lean_unbox_usize(v_sz_4208_);
lean_dec(v_sz_4208_);
v_i_boxed_4217_ = lean_unbox_usize(v_i_4209_);
lean_dec(v_i_4209_);
v_res_4218_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4___redArg(v_as_4207_, v_sz_boxed_4216_, v_i_boxed_4217_, v_b_4210_, v___y_4211_, v___y_4212_, v___y_4213_, v___y_4214_);
lean_dec(v___y_4214_);
lean_dec_ref(v___y_4213_);
lean_dec(v___y_4212_);
lean_dec_ref(v___y_4211_);
lean_dec_ref(v_as_4207_);
return v_res_4218_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___redArg(size_t v_sz_4219_, size_t v_i_4220_, lean_object* v_bs_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_){
_start:
{
uint8_t v___x_4225_; 
v___x_4225_ = lean_usize_dec_lt(v_i_4220_, v_sz_4219_);
if (v___x_4225_ == 0)
{
lean_object* v___x_4226_; 
v___x_4226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4226_, 0, v_bs_4221_);
return v___x_4226_;
}
else
{
lean_object* v_v_4227_; lean_object* v___x_4228_; 
v_v_4227_ = lean_array_uget_borrowed(v_bs_4221_, v_i_4220_);
lean_inc(v_v_4227_);
v___x_4228_ = l_Lean_Elab_eraseRecAppSyntax(v_v_4227_, v___y_4222_, v___y_4223_);
if (lean_obj_tag(v___x_4228_) == 0)
{
lean_object* v_a_4229_; lean_object* v___x_4230_; lean_object* v_bs_x27_4231_; size_t v___x_4232_; size_t v___x_4233_; lean_object* v___x_4234_; 
v_a_4229_ = lean_ctor_get(v___x_4228_, 0);
lean_inc(v_a_4229_);
lean_dec_ref_known(v___x_4228_, 1);
v___x_4230_ = lean_unsigned_to_nat(0u);
v_bs_x27_4231_ = lean_array_uset(v_bs_4221_, v_i_4220_, v___x_4230_);
v___x_4232_ = ((size_t)1ULL);
v___x_4233_ = lean_usize_add(v_i_4220_, v___x_4232_);
v___x_4234_ = lean_array_uset(v_bs_x27_4231_, v_i_4220_, v_a_4229_);
v_i_4220_ = v___x_4233_;
v_bs_4221_ = v___x_4234_;
goto _start;
}
else
{
lean_object* v_a_4236_; lean_object* v___x_4238_; uint8_t v_isShared_4239_; uint8_t v_isSharedCheck_4243_; 
lean_dec_ref(v_bs_4221_);
v_a_4236_ = lean_ctor_get(v___x_4228_, 0);
v_isSharedCheck_4243_ = !lean_is_exclusive(v___x_4228_);
if (v_isSharedCheck_4243_ == 0)
{
v___x_4238_ = v___x_4228_;
v_isShared_4239_ = v_isSharedCheck_4243_;
goto v_resetjp_4237_;
}
else
{
lean_inc(v_a_4236_);
lean_dec(v___x_4228_);
v___x_4238_ = lean_box(0);
v_isShared_4239_ = v_isSharedCheck_4243_;
goto v_resetjp_4237_;
}
v_resetjp_4237_:
{
lean_object* v___x_4241_; 
if (v_isShared_4239_ == 0)
{
v___x_4241_ = v___x_4238_;
goto v_reusejp_4240_;
}
else
{
lean_object* v_reuseFailAlloc_4242_; 
v_reuseFailAlloc_4242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4242_, 0, v_a_4236_);
v___x_4241_ = v_reuseFailAlloc_4242_;
goto v_reusejp_4240_;
}
v_reusejp_4240_:
{
return v___x_4241_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___redArg___boxed(lean_object* v_sz_4244_, lean_object* v_i_4245_, lean_object* v_bs_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_, lean_object* v___y_4249_){
_start:
{
size_t v_sz_boxed_4250_; size_t v_i_boxed_4251_; lean_object* v_res_4252_; 
v_sz_boxed_4250_ = lean_unbox_usize(v_sz_4244_);
lean_dec(v_sz_4244_);
v_i_boxed_4251_ = lean_unbox_usize(v_i_4245_);
lean_dec(v_i_4245_);
v_res_4252_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___redArg(v_sz_boxed_4250_, v_i_boxed_4251_, v_bs_4246_, v___y_4247_, v___y_4248_);
lean_dec(v___y_4248_);
lean_dec_ref(v___y_4247_);
return v_res_4252_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___redArg(lean_object* v_as_4253_, size_t v_sz_4254_, size_t v_i_4255_, lean_object* v_b_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_){
_start:
{
uint8_t v___x_4260_; 
v___x_4260_ = lean_usize_dec_lt(v_i_4255_, v_sz_4254_);
if (v___x_4260_ == 0)
{
lean_object* v___x_4261_; 
v___x_4261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4261_, 0, v_b_4256_);
return v___x_4261_;
}
else
{
lean_object* v_a_4262_; lean_object* v_declName_4263_; lean_object* v___x_4264_; 
v_a_4262_ = lean_array_uget_borrowed(v_as_4253_, v_i_4255_);
v_declName_4263_ = lean_ctor_get(v_a_4262_, 3);
lean_inc(v_declName_4263_);
v___x_4264_ = l_Lean_enableRealizationsForConst(v_declName_4263_, v___y_4257_, v___y_4258_);
if (lean_obj_tag(v___x_4264_) == 0)
{
lean_object* v___x_4265_; size_t v___x_4266_; size_t v___x_4267_; 
lean_dec_ref_known(v___x_4264_, 1);
v___x_4265_ = lean_box(0);
v___x_4266_ = ((size_t)1ULL);
v___x_4267_ = lean_usize_add(v_i_4255_, v___x_4266_);
v_i_4255_ = v___x_4267_;
v_b_4256_ = v___x_4265_;
goto _start;
}
else
{
return v___x_4264_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___redArg___boxed(lean_object* v_as_4269_, lean_object* v_sz_4270_, lean_object* v_i_4271_, lean_object* v_b_4272_, lean_object* v___y_4273_, lean_object* v___y_4274_, lean_object* v___y_4275_){
_start:
{
size_t v_sz_boxed_4276_; size_t v_i_boxed_4277_; lean_object* v_res_4278_; 
v_sz_boxed_4276_ = lean_unbox_usize(v_sz_4270_);
lean_dec(v_sz_4270_);
v_i_boxed_4277_ = lean_unbox_usize(v_i_4271_);
lean_dec(v_i_4271_);
v_res_4278_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___redArg(v_as_4269_, v_sz_boxed_4276_, v_i_boxed_4277_, v_b_4272_, v___y_4273_, v___y_4274_);
lean_dec(v___y_4274_);
lean_dec_ref(v___y_4273_);
lean_dec_ref(v_as_4269_);
return v_res_4278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_structuralRecursion(lean_object* v_docCtx_4279_, lean_object* v_preDefs_4280_, lean_object* v_termMeasure_x3fs_4281_, lean_object* v_a_4282_, lean_object* v_a_4283_, lean_object* v_a_4284_, lean_object* v_a_4285_, lean_object* v_a_4286_, lean_object* v_a_4287_){
_start:
{
size_t v_sz_4289_; size_t v___x_4290_; lean_object* v_names_4291_; lean_object* v___x_4292_; 
v_sz_4289_ = lean_array_size(v_preDefs_4280_);
v___x_4290_ = ((size_t)0ULL);
lean_inc_ref_n(v_preDefs_4280_, 2);
v_names_4291_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0(v_sz_4289_, v___x_4290_, v_preDefs_4280_);
v___x_4292_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos(v_preDefs_4280_, v_termMeasure_x3fs_4281_, v_a_4284_, v_a_4285_, v_a_4286_, v_a_4287_);
if (lean_obj_tag(v___x_4292_) == 0)
{
lean_object* v_a_4293_; lean_object* v_snd_4294_; lean_object* v_fst_4295_; lean_object* v_fst_4296_; lean_object* v_snd_4297_; lean_object* v___y_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; size_t v_sz_4333_; lean_object* v___x_4334_; 
v_a_4293_ = lean_ctor_get(v___x_4292_, 0);
lean_inc(v_a_4293_);
lean_dec_ref_known(v___x_4292_, 1);
v_snd_4294_ = lean_ctor_get(v_a_4293_, 1);
lean_inc(v_snd_4294_);
v_fst_4295_ = lean_ctor_get(v_a_4293_, 0);
lean_inc(v_fst_4295_);
lean_dec(v_a_4293_);
v_fst_4296_ = lean_ctor_get(v_snd_4294_, 0);
lean_inc(v_fst_4296_);
v_snd_4297_ = lean_ctor_get(v_snd_4294_, 1);
lean_inc(v_snd_4297_);
lean_dec(v_snd_4294_);
v___x_4330_ = lean_unsigned_to_nat(0u);
v___x_4331_ = lean_array_get_size(v_preDefs_4280_);
lean_inc_ref(v_preDefs_4280_);
v___x_4332_ = l_Array_toSubarray___redArg(v_preDefs_4280_, v___x_4330_, v___x_4331_);
v_sz_4333_ = lean_array_size(v_fst_4295_);
v___x_4334_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4___redArg(v_fst_4295_, v_sz_4333_, v___x_4290_, v___x_4332_, v_a_4284_, v_a_4285_, v_a_4286_, v_a_4287_);
if (lean_obj_tag(v___x_4334_) == 0)
{
lean_object* v___x_4335_; uint8_t v___x_4336_; 
lean_dec_ref_known(v___x_4334_, 1);
v___x_4335_ = lean_array_get_size(v_fst_4296_);
v___x_4336_ = lean_nat_dec_lt(v___x_4330_, v___x_4335_);
if (v___x_4336_ == 0)
{
lean_dec_ref(v_names_4291_);
goto v___jp_4298_;
}
else
{
lean_object* v___x_4337_; uint8_t v___x_4338_; 
v___x_4337_ = lean_box(0);
v___x_4338_ = lean_nat_dec_le(v___x_4335_, v___x_4335_);
if (v___x_4338_ == 0)
{
if (v___x_4336_ == 0)
{
lean_dec_ref(v_names_4291_);
goto v___jp_4298_;
}
else
{
size_t v___x_4339_; lean_object* v___x_4340_; 
v___x_4339_ = lean_usize_of_nat(v___x_4335_);
lean_inc_ref(v_docCtx_4279_);
v___x_4340_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5(v_names_4291_, v_docCtx_4279_, v_fst_4296_, v___x_4290_, v___x_4339_, v___x_4337_, v_a_4282_, v_a_4283_, v_a_4284_, v_a_4285_, v_a_4286_, v_a_4287_);
v___y_4329_ = v___x_4340_;
goto v___jp_4328_;
}
}
else
{
size_t v___x_4341_; lean_object* v___x_4342_; 
v___x_4341_ = lean_usize_of_nat(v___x_4335_);
lean_inc_ref(v_docCtx_4279_);
v___x_4342_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5(v_names_4291_, v_docCtx_4279_, v_fst_4296_, v___x_4290_, v___x_4341_, v___x_4337_, v_a_4282_, v_a_4283_, v_a_4284_, v_a_4285_, v_a_4286_, v_a_4287_);
v___y_4329_ = v___x_4342_;
goto v___jp_4328_;
}
}
}
else
{
lean_object* v_a_4343_; lean_object* v___x_4345_; uint8_t v_isShared_4346_; uint8_t v_isSharedCheck_4350_; 
lean_dec(v_snd_4297_);
lean_dec(v_fst_4296_);
lean_dec(v_fst_4295_);
lean_dec_ref(v_names_4291_);
lean_dec_ref(v_preDefs_4280_);
lean_dec_ref(v_docCtx_4279_);
v_a_4343_ = lean_ctor_get(v___x_4334_, 0);
v_isSharedCheck_4350_ = !lean_is_exclusive(v___x_4334_);
if (v_isSharedCheck_4350_ == 0)
{
v___x_4345_ = v___x_4334_;
v_isShared_4346_ = v_isSharedCheck_4350_;
goto v_resetjp_4344_;
}
else
{
lean_inc(v_a_4343_);
lean_dec(v___x_4334_);
v___x_4345_ = lean_box(0);
v_isShared_4346_ = v_isSharedCheck_4350_;
goto v_resetjp_4344_;
}
v_resetjp_4344_:
{
lean_object* v___x_4348_; 
if (v_isShared_4346_ == 0)
{
v___x_4348_ = v___x_4345_;
goto v_reusejp_4347_;
}
else
{
lean_object* v_reuseFailAlloc_4349_; 
v_reuseFailAlloc_4349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4349_, 0, v_a_4343_);
v___x_4348_ = v_reuseFailAlloc_4349_;
goto v_reusejp_4347_;
}
v_reusejp_4347_:
{
return v___x_4348_;
}
}
}
v___jp_4298_:
{
lean_object* v___x_4299_; 
v___x_4299_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___redArg(v_sz_4289_, v___x_4290_, v_preDefs_4280_, v_a_4286_, v_a_4287_);
if (lean_obj_tag(v___x_4299_) == 0)
{
lean_object* v_a_4300_; lean_object* v___x_4301_; 
v_a_4300_ = lean_ctor_get(v___x_4299_, 0);
lean_inc_n(v_a_4300_, 2);
lean_dec_ref_known(v___x_4299_, 1);
lean_inc_ref(v_docCtx_4279_);
v___x_4301_ = l_Lean_Elab_addAndCompilePartialRec(v_docCtx_4279_, v_a_4300_, v_a_4282_, v_a_4283_, v_a_4284_, v_a_4285_, v_a_4286_, v_a_4287_);
if (lean_obj_tag(v___x_4301_) == 0)
{
lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; size_t v_sz_4305_; lean_object* v___x_4306_; 
lean_dec_ref_known(v___x_4301_, 1);
v___x_4302_ = lean_unsigned_to_nat(0u);
v___x_4303_ = lean_array_get_size(v_fst_4295_);
v___x_4304_ = l_Array_toSubarray___redArg(v_fst_4295_, v___x_4302_, v___x_4303_);
v_sz_4305_ = lean_array_size(v_a_4300_);
lean_inc(v_a_4300_);
v___x_4306_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__1(v_docCtx_4279_, v_a_4300_, v_snd_4297_, v_a_4300_, v_sz_4305_, v___x_4290_, v___x_4304_, v_a_4282_, v_a_4283_, v_a_4284_, v_a_4285_, v_a_4286_, v_a_4287_);
if (lean_obj_tag(v___x_4306_) == 0)
{
lean_object* v___x_4307_; lean_object* v___x_4308_; 
lean_dec_ref_known(v___x_4306_, 1);
v___x_4307_ = lean_box(0);
v___x_4308_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___redArg(v_a_4300_, v_sz_4305_, v___x_4290_, v___x_4307_, v_a_4284_, v_a_4285_, v_a_4286_, v_a_4287_);
if (lean_obj_tag(v___x_4308_) == 0)
{
lean_object* v___x_4309_; 
lean_dec_ref_known(v___x_4308_, 1);
v___x_4309_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___redArg(v_a_4300_, v_sz_4305_, v___x_4290_, v___x_4307_, v_a_4286_, v_a_4287_);
lean_dec(v_a_4300_);
if (lean_obj_tag(v___x_4309_) == 0)
{
uint8_t v___x_4310_; lean_object* v___x_4311_; 
lean_dec_ref_known(v___x_4309_, 1);
v___x_4310_ = 1;
v___x_4311_ = l_Lean_Elab_applyAttributesOf(v_fst_4296_, v___x_4310_, v_a_4282_, v_a_4283_, v_a_4284_, v_a_4285_, v_a_4286_, v_a_4287_);
lean_dec(v_fst_4296_);
return v___x_4311_;
}
else
{
lean_dec(v_fst_4296_);
return v___x_4309_;
}
}
else
{
lean_dec(v_a_4300_);
lean_dec(v_fst_4296_);
return v___x_4308_;
}
}
else
{
lean_object* v_a_4312_; lean_object* v___x_4314_; uint8_t v_isShared_4315_; uint8_t v_isSharedCheck_4319_; 
lean_dec(v_a_4300_);
lean_dec(v_fst_4296_);
v_a_4312_ = lean_ctor_get(v___x_4306_, 0);
v_isSharedCheck_4319_ = !lean_is_exclusive(v___x_4306_);
if (v_isSharedCheck_4319_ == 0)
{
v___x_4314_ = v___x_4306_;
v_isShared_4315_ = v_isSharedCheck_4319_;
goto v_resetjp_4313_;
}
else
{
lean_inc(v_a_4312_);
lean_dec(v___x_4306_);
v___x_4314_ = lean_box(0);
v_isShared_4315_ = v_isSharedCheck_4319_;
goto v_resetjp_4313_;
}
v_resetjp_4313_:
{
lean_object* v___x_4317_; 
if (v_isShared_4315_ == 0)
{
v___x_4317_ = v___x_4314_;
goto v_reusejp_4316_;
}
else
{
lean_object* v_reuseFailAlloc_4318_; 
v_reuseFailAlloc_4318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4318_, 0, v_a_4312_);
v___x_4317_ = v_reuseFailAlloc_4318_;
goto v_reusejp_4316_;
}
v_reusejp_4316_:
{
return v___x_4317_;
}
}
}
}
else
{
lean_dec(v_a_4300_);
lean_dec(v_snd_4297_);
lean_dec(v_fst_4296_);
lean_dec(v_fst_4295_);
lean_dec_ref(v_docCtx_4279_);
return v___x_4301_;
}
}
else
{
lean_object* v_a_4320_; lean_object* v___x_4322_; uint8_t v_isShared_4323_; uint8_t v_isSharedCheck_4327_; 
lean_dec(v_snd_4297_);
lean_dec(v_fst_4296_);
lean_dec(v_fst_4295_);
lean_dec_ref(v_docCtx_4279_);
v_a_4320_ = lean_ctor_get(v___x_4299_, 0);
v_isSharedCheck_4327_ = !lean_is_exclusive(v___x_4299_);
if (v_isSharedCheck_4327_ == 0)
{
v___x_4322_ = v___x_4299_;
v_isShared_4323_ = v_isSharedCheck_4327_;
goto v_resetjp_4321_;
}
else
{
lean_inc(v_a_4320_);
lean_dec(v___x_4299_);
v___x_4322_ = lean_box(0);
v_isShared_4323_ = v_isSharedCheck_4327_;
goto v_resetjp_4321_;
}
v_resetjp_4321_:
{
lean_object* v___x_4325_; 
if (v_isShared_4323_ == 0)
{
v___x_4325_ = v___x_4322_;
goto v_reusejp_4324_;
}
else
{
lean_object* v_reuseFailAlloc_4326_; 
v_reuseFailAlloc_4326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4326_, 0, v_a_4320_);
v___x_4325_ = v_reuseFailAlloc_4326_;
goto v_reusejp_4324_;
}
v_reusejp_4324_:
{
return v___x_4325_;
}
}
}
}
v___jp_4328_:
{
if (lean_obj_tag(v___y_4329_) == 0)
{
lean_dec_ref_known(v___y_4329_, 1);
goto v___jp_4298_;
}
else
{
lean_dec(v_snd_4297_);
lean_dec(v_fst_4296_);
lean_dec(v_fst_4295_);
lean_dec_ref(v_preDefs_4280_);
lean_dec_ref(v_docCtx_4279_);
return v___y_4329_;
}
}
}
else
{
lean_object* v_a_4351_; lean_object* v___x_4353_; uint8_t v_isShared_4354_; uint8_t v_isSharedCheck_4358_; 
lean_dec_ref(v_names_4291_);
lean_dec_ref(v_preDefs_4280_);
lean_dec_ref(v_docCtx_4279_);
v_a_4351_ = lean_ctor_get(v___x_4292_, 0);
v_isSharedCheck_4358_ = !lean_is_exclusive(v___x_4292_);
if (v_isSharedCheck_4358_ == 0)
{
v___x_4353_ = v___x_4292_;
v_isShared_4354_ = v_isSharedCheck_4358_;
goto v_resetjp_4352_;
}
else
{
lean_inc(v_a_4351_);
lean_dec(v___x_4292_);
v___x_4353_ = lean_box(0);
v_isShared_4354_ = v_isSharedCheck_4358_;
goto v_resetjp_4352_;
}
v_resetjp_4352_:
{
lean_object* v___x_4356_; 
if (v_isShared_4354_ == 0)
{
v___x_4356_ = v___x_4353_;
goto v_reusejp_4355_;
}
else
{
lean_object* v_reuseFailAlloc_4357_; 
v_reuseFailAlloc_4357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4357_, 0, v_a_4351_);
v___x_4356_ = v_reuseFailAlloc_4357_;
goto v_reusejp_4355_;
}
v_reusejp_4355_:
{
return v___x_4356_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_structuralRecursion___boxed(lean_object* v_docCtx_4359_, lean_object* v_preDefs_4360_, lean_object* v_termMeasure_x3fs_4361_, lean_object* v_a_4362_, lean_object* v_a_4363_, lean_object* v_a_4364_, lean_object* v_a_4365_, lean_object* v_a_4366_, lean_object* v_a_4367_, lean_object* v_a_4368_){
_start:
{
lean_object* v_res_4369_; 
v_res_4369_ = l_Lean_Elab_Structural_structuralRecursion(v_docCtx_4359_, v_preDefs_4360_, v_termMeasure_x3fs_4361_, v_a_4362_, v_a_4363_, v_a_4364_, v_a_4365_, v_a_4366_, v_a_4367_);
lean_dec(v_a_4367_);
lean_dec_ref(v_a_4366_);
lean_dec(v_a_4365_);
lean_dec_ref(v_a_4364_);
lean_dec(v_a_4363_);
lean_dec_ref(v_a_4362_);
return v_res_4369_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0(size_t v_sz_4370_, size_t v_i_4371_, lean_object* v_bs_4372_, lean_object* v___y_4373_, lean_object* v___y_4374_, lean_object* v___y_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_, lean_object* v___y_4378_){
_start:
{
lean_object* v___x_4380_; 
v___x_4380_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___redArg(v_sz_4370_, v_i_4371_, v_bs_4372_, v___y_4377_, v___y_4378_);
return v___x_4380_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___boxed(lean_object* v_sz_4381_, lean_object* v_i_4382_, lean_object* v_bs_4383_, lean_object* v___y_4384_, lean_object* v___y_4385_, lean_object* v___y_4386_, lean_object* v___y_4387_, lean_object* v___y_4388_, lean_object* v___y_4389_, lean_object* v___y_4390_){
_start:
{
size_t v_sz_boxed_4391_; size_t v_i_boxed_4392_; lean_object* v_res_4393_; 
v_sz_boxed_4391_ = lean_unbox_usize(v_sz_4381_);
lean_dec(v_sz_4381_);
v_i_boxed_4392_ = lean_unbox_usize(v_i_4382_);
lean_dec(v_i_4382_);
v_res_4393_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0(v_sz_boxed_4391_, v_i_boxed_4392_, v_bs_4383_, v___y_4384_, v___y_4385_, v___y_4386_, v___y_4387_, v___y_4388_, v___y_4389_);
lean_dec(v___y_4389_);
lean_dec_ref(v___y_4388_);
lean_dec(v___y_4387_);
lean_dec_ref(v___y_4386_);
lean_dec(v___y_4385_);
lean_dec_ref(v___y_4384_);
return v_res_4393_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2(lean_object* v_as_4394_, size_t v_sz_4395_, size_t v_i_4396_, lean_object* v_b_4397_, lean_object* v___y_4398_, lean_object* v___y_4399_, lean_object* v___y_4400_, lean_object* v___y_4401_, lean_object* v___y_4402_, lean_object* v___y_4403_){
_start:
{
lean_object* v___x_4405_; 
v___x_4405_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___redArg(v_as_4394_, v_sz_4395_, v_i_4396_, v_b_4397_, v___y_4400_, v___y_4401_, v___y_4402_, v___y_4403_);
return v___x_4405_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___boxed(lean_object* v_as_4406_, lean_object* v_sz_4407_, lean_object* v_i_4408_, lean_object* v_b_4409_, lean_object* v___y_4410_, lean_object* v___y_4411_, lean_object* v___y_4412_, lean_object* v___y_4413_, lean_object* v___y_4414_, lean_object* v___y_4415_, lean_object* v___y_4416_){
_start:
{
size_t v_sz_boxed_4417_; size_t v_i_boxed_4418_; lean_object* v_res_4419_; 
v_sz_boxed_4417_ = lean_unbox_usize(v_sz_4407_);
lean_dec(v_sz_4407_);
v_i_boxed_4418_ = lean_unbox_usize(v_i_4408_);
lean_dec(v_i_4408_);
v_res_4419_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2(v_as_4406_, v_sz_boxed_4417_, v_i_boxed_4418_, v_b_4409_, v___y_4410_, v___y_4411_, v___y_4412_, v___y_4413_, v___y_4414_, v___y_4415_);
lean_dec(v___y_4415_);
lean_dec_ref(v___y_4414_);
lean_dec(v___y_4413_);
lean_dec_ref(v___y_4412_);
lean_dec(v___y_4411_);
lean_dec_ref(v___y_4410_);
lean_dec_ref(v_as_4406_);
return v_res_4419_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3(lean_object* v_as_4420_, size_t v_sz_4421_, size_t v_i_4422_, lean_object* v_b_4423_, lean_object* v___y_4424_, lean_object* v___y_4425_, lean_object* v___y_4426_, lean_object* v___y_4427_, lean_object* v___y_4428_, lean_object* v___y_4429_){
_start:
{
lean_object* v___x_4431_; 
v___x_4431_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___redArg(v_as_4420_, v_sz_4421_, v_i_4422_, v_b_4423_, v___y_4428_, v___y_4429_);
return v___x_4431_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___boxed(lean_object* v_as_4432_, lean_object* v_sz_4433_, lean_object* v_i_4434_, lean_object* v_b_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_, lean_object* v___y_4441_, lean_object* v___y_4442_){
_start:
{
size_t v_sz_boxed_4443_; size_t v_i_boxed_4444_; lean_object* v_res_4445_; 
v_sz_boxed_4443_ = lean_unbox_usize(v_sz_4433_);
lean_dec(v_sz_4433_);
v_i_boxed_4444_ = lean_unbox_usize(v_i_4434_);
lean_dec(v_i_4434_);
v_res_4445_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3(v_as_4432_, v_sz_boxed_4443_, v_i_boxed_4444_, v_b_4435_, v___y_4436_, v___y_4437_, v___y_4438_, v___y_4439_, v___y_4440_, v___y_4441_);
lean_dec(v___y_4441_);
lean_dec_ref(v___y_4440_);
lean_dec(v___y_4439_);
lean_dec_ref(v___y_4438_);
lean_dec(v___y_4437_);
lean_dec_ref(v___y_4436_);
lean_dec_ref(v_as_4432_);
return v_res_4445_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4(lean_object* v_as_4446_, size_t v_sz_4447_, size_t v_i_4448_, lean_object* v_b_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_, lean_object* v___y_4452_, lean_object* v___y_4453_, lean_object* v___y_4454_, lean_object* v___y_4455_){
_start:
{
lean_object* v___x_4457_; 
v___x_4457_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4___redArg(v_as_4446_, v_sz_4447_, v_i_4448_, v_b_4449_, v___y_4452_, v___y_4453_, v___y_4454_, v___y_4455_);
return v___x_4457_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4___boxed(lean_object* v_as_4458_, lean_object* v_sz_4459_, lean_object* v_i_4460_, lean_object* v_b_4461_, lean_object* v___y_4462_, lean_object* v___y_4463_, lean_object* v___y_4464_, lean_object* v___y_4465_, lean_object* v___y_4466_, lean_object* v___y_4467_, lean_object* v___y_4468_){
_start:
{
size_t v_sz_boxed_4469_; size_t v_i_boxed_4470_; lean_object* v_res_4471_; 
v_sz_boxed_4469_ = lean_unbox_usize(v_sz_4459_);
lean_dec(v_sz_4459_);
v_i_boxed_4470_ = lean_unbox_usize(v_i_4460_);
lean_dec(v_i_4460_);
v_res_4471_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4(v_as_4458_, v_sz_boxed_4469_, v_i_boxed_4470_, v_b_4461_, v___y_4462_, v___y_4463_, v___y_4464_, v___y_4465_, v___y_4466_, v___y_4467_);
lean_dec(v___y_4467_);
lean_dec_ref(v___y_4466_);
lean_dec(v___y_4465_);
lean_dec_ref(v___y_4464_);
lean_dec(v___y_4463_);
lean_dec_ref(v___y_4462_);
lean_dec_ref(v_as_4458_);
return v_res_4471_;
}
}
lean_object* runtime_initialize_Lean_Elab_PreDefinition_Mutual(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_PreDefinition_Structural_FindRecArg(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_PreDefinition_Structural_Preprocess(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_PreDefinition_Structural_BRecOn(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_PreDefinition_Structural_IndPred(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_PreDefinition_Structural_Eqns(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_PreDefinition_Structural_SmartUnfolding(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_TryThis(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_PreDefinition_Structural_Main(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_PreDefinition_Mutual(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_PreDefinition_Structural_FindRecArg(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_PreDefinition_Structural_Preprocess(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_PreDefinition_Structural_BRecOn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_PreDefinition_Structural_IndPred(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_PreDefinition_Structural_Eqns(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_PreDefinition_Structural_SmartUnfolding(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_TryThis(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_PreDefinition_Structural_Main(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_PreDefinition_Mutual(uint8_t builtin);
lean_object* initialize_Lean_Elab_PreDefinition_Structural_FindRecArg(uint8_t builtin);
lean_object* initialize_Lean_Elab_PreDefinition_Structural_Preprocess(uint8_t builtin);
lean_object* initialize_Lean_Elab_PreDefinition_Structural_BRecOn(uint8_t builtin);
lean_object* initialize_Lean_Elab_PreDefinition_Structural_IndPred(uint8_t builtin);
lean_object* initialize_Lean_Elab_PreDefinition_Structural_Eqns(uint8_t builtin);
lean_object* initialize_Lean_Elab_PreDefinition_Structural_SmartUnfolding(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_TryThis(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_PreDefinition_Structural_Main(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_PreDefinition_Mutual(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_Structural_FindRecArg(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_Structural_Preprocess(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_Structural_BRecOn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_Structural_IndPred(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_Structural_Eqns(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_Structural_SmartUnfolding(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_TryThis(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_PreDefinition_Structural_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_PreDefinition_Structural_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_PreDefinition_Structural_Main(builtin);
}
#ifdef __cplusplus
}
#endif
