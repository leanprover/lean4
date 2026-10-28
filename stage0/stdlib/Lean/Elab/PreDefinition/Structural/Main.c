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
lean_object* l_Array_instInhabited___redArg();
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_FixedParamPerm_buildArgs___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_beta(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Elab_Structural_mkIndPredBRecOnMotive(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_FixedParamPerm_instantiateForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVarOf(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_Environment_unlockAsync(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Elab_addAsAxiom___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_PProdN_mkLambdas___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_withEnv___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_enableRealizationsForConst(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Structural_instInhabitedRecArgInfo_default;
extern lean_object* l_Lean_Elab_instInhabitedPreDefinition_default;
lean_object* l_Lean_Elab_FixedParamPerm_instantiateLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isInductiveCore_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_InductiveVal_numTypeFormers(lean_object*);
lean_object* l_Array_range(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
uint8_t l_Nat_blt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInductivePredicate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_zip___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_mkBRecOnApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferArgumentTypesN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_Positions_numIndices(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_Elab_eraseRecAppSyntaxExpr(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_ensureNoRecFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Elab_Structural_mkBRecOnMotive(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_withFunTypes___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_LocalContext_erase(lean_object*, lean_object*);
lean_object* l_Lean_Elab_addNonRec(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
lean_object* l_Lean_Elab_Structural_RecArgInfo_indicesAndRecArgPos(lean_object*);
lean_object* l_Lean_Elab_FixedParamPerms_erase(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_findRecArgCandidates___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0___boxed(lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17_spec__30___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17_spec__30___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_f"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(253, 65, 185, 154, 193, 83, 240, 170)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___redArg(lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2(lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__3(lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__21(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__20___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_PProdN_mkLambdas___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__0_value;
static const lean_closure_object l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__1_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__2 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__2_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__3 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__3_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "structural"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__4 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__2_value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__3_value),LEAN_SCALAR_PTR_LITERAL(127, 238, 145, 63, 173, 125, 183, 95)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__4_value),LEAN_SCALAR_PTR_LITERAL(117, 73, 239, 7, 229, 151, 237, 199)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__5 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__5_value;
static const lean_closure_object l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__5_value)} };
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
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17_spec__30(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17_spec__30___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__20(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg___closed__0 = (const lean_object*)&l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg___closed__0_value;
static lean_once_cell_t l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg___closed__1;
static lean_once_cell_t l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__11(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__8_spec__10(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__8_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__8___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__10(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 61, .m_capacity = 61, .m_length = 60, .m_data = "its type is an inductive datatype and the datatype parameter"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "\ndepends on the function parameter"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___closed__3;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 137, .m_capacity = 137, .m_length = 136, .m_data = "\nwhich cannot be fixed as it is an index or depends on an index, and indices cannot be fixed parameters when using structural recursion."};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___closed__4_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___closed__5;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__3___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__13_spec__16_spec__20(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__13_spec__16(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__13(lean_object*, lean_object*);
static const lean_string_object l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "#["};
static const lean_object* l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___closed__0 = (const lean_object*)&l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___closed__0_value;
static const lean_string_object l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___closed__1 = (const lean_object*)&l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___closed__1_value;
static const lean_ctor_object l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___closed__1_value)}};
static const lean_object* l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___closed__2 = (const lean_object*)&l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___closed__2_value;
static const lean_ctor_object l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___closed__2_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___closed__3 = (const lean_object*)&l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___closed__3_value;
static const lean_string_object l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___closed__4 = (const lean_object*)&l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___closed__4_value;
static lean_once_cell_t l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___closed__5;
static lean_once_cell_t l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___closed__6;
static const lean_ctor_object l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___closed__0_value)}};
static const lean_object* l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___closed__7 = (const lean_object*)&l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___closed__7_value;
static const lean_ctor_object l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___closed__4_value)}};
static const lean_object* l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___closed__8 = (const lean_object*)&l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___closed__8_value;
static const lean_string_object l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "#[]"};
static const lean_object* l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___closed__9 = (const lean_object*)&l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___closed__9_value;
static const lean_ctor_object l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___closed__9_value)}};
static const lean_object* l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___closed__10 = (const lean_object*)&l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___closed__10_value;
LEAN_EXPORT lean_object* l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__2___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__11___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__2(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__14(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__11(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Structural_reportTermMeasure___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Structural_reportTermMeasure___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v_toApplicative_24_; lean_object* v_toBind_25_; lean_object* v_toPure_26_; lean_object* v___f_27_; lean_object* v___y_29_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; uint8_t v___x_37_; 
v_toApplicative_24_ = lean_ctor_get(v_inst_18_, 0);
v_toBind_25_ = lean_ctor_get(v_inst_18_, 1);
lean_inc(v_toBind_25_);
v_toPure_26_ = lean_ctor_get(v_toApplicative_24_, 1);
v___f_27_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_27_, 0, v_k_23_);
v___x_34_ = lean_unsigned_to_nat(0u);
v___x_35_ = lean_array_get_size(v_preDefs_22_);
v___x_36_ = lean_box(0);
v___x_37_ = lean_nat_dec_lt(v___x_34_, v___x_35_);
if (v___x_37_ == 0)
{
lean_object* v___x_38_; 
lean_dec_ref(v_preDefs_22_);
lean_dec(v_inst_19_);
lean_inc(v_toPure_26_);
v___x_38_ = lean_apply_2(v_toPure_26_, lean_box(0), v___x_36_);
v___y_29_ = v___x_38_;
goto v___jp_28_;
}
else
{
lean_object* v___f_39_; size_t v___x_40_; size_t v___x_41_; lean_object* v___x_42_; 
v___f_39_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___redArg___lam__2), 3, 1);
lean_closure_set(v___f_39_, 0, v_inst_19_);
v___x_40_ = ((size_t)0ULL);
v___x_41_ = lean_usize_of_nat(v___x_35_);
lean_inc_ref(v_inst_18_);
v___x_42_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_18_, v___f_39_, v_preDefs_22_, v___x_40_, v___x_41_, v___x_36_);
v___y_29_ = v___x_42_;
goto v___jp_28_;
}
v___jp_28_:
{
lean_object* v_getEnv_30_; lean_object* v___x_31_; lean_object* v___f_32_; lean_object* v___x_33_; 
v_getEnv_30_ = lean_ctor_get(v_inst_20_, 0);
lean_inc(v_getEnv_30_);
lean_inc(v_toBind_25_);
v___x_31_ = lean_apply_4(v_toBind_25_, lean_box(0), lean_box(0), v___y_29_, v___f_27_);
v___f_32_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___redArg___lam__1), 5, 4);
lean_closure_set(v___f_32_, 0, v_inst_18_);
lean_closure_set(v___f_32_, 1, v_inst_21_);
lean_closure_set(v___f_32_, 2, v_inst_20_);
lean_closure_set(v___f_32_, 3, v___x_31_);
v___x_33_ = lean_apply_4(v_toBind_25_, lean_box(0), lean_box(0), v_getEnv_30_, v___f_32_);
return v___x_33_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms(lean_object* v_n_43_, lean_object* v_00_u03b1_44_, lean_object* v_inst_45_, lean_object* v_inst_46_, lean_object* v_inst_47_, lean_object* v_inst_48_, lean_object* v_preDefs_49_, lean_object* v_k_50_){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___redArg(v_inst_45_, v_inst_46_, v_inst_47_, v_inst_48_, v_preDefs_49_, v_k_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg___lam__0(lean_object* v_k_52_, lean_object* v_b_53_, lean_object* v_c_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_){
_start:
{
lean_object* v___x_60_; 
lean_inc(v___y_58_);
lean_inc_ref(v___y_57_);
lean_inc(v___y_56_);
lean_inc_ref(v___y_55_);
v___x_60_ = lean_apply_7(v_k_52_, v_b_53_, v_c_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, lean_box(0));
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg___lam__0___boxed(lean_object* v_k_61_, lean_object* v_b_62_, lean_object* v_c_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg___lam__0(v_k_61_, v_b_62_, v_c_63_, v___y_64_, v___y_65_, v___y_66_, v___y_67_);
lean_dec(v___y_67_);
lean_dec_ref(v___y_66_);
lean_dec(v___y_65_);
lean_dec_ref(v___y_64_);
return v_res_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg(lean_object* v_e_70_, lean_object* v_k_71_, uint8_t v_cleanupAnnotations_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_){
_start:
{
lean_object* v___f_78_; uint8_t v___x_79_; uint8_t v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v___f_78_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_78_, 0, v_k_71_);
v___x_79_ = 1;
v___x_80_ = 0;
v___x_81_ = lean_box(0);
v___x_82_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_70_, v___x_79_, v___x_80_, v___x_79_, v___x_80_, v___x_81_, v___f_78_, v_cleanupAnnotations_72_, v___y_73_, v___y_74_, v___y_75_, v___y_76_);
if (lean_obj_tag(v___x_82_) == 0)
{
lean_object* v_a_83_; lean_object* v___x_85_; uint8_t v_isShared_86_; uint8_t v_isSharedCheck_90_; 
v_a_83_ = lean_ctor_get(v___x_82_, 0);
v_isSharedCheck_90_ = !lean_is_exclusive(v___x_82_);
if (v_isSharedCheck_90_ == 0)
{
v___x_85_ = v___x_82_;
v_isShared_86_ = v_isSharedCheck_90_;
goto v_resetjp_84_;
}
else
{
lean_inc(v_a_83_);
lean_dec(v___x_82_);
v___x_85_ = lean_box(0);
v_isShared_86_ = v_isSharedCheck_90_;
goto v_resetjp_84_;
}
v_resetjp_84_:
{
lean_object* v___x_88_; 
if (v_isShared_86_ == 0)
{
v___x_88_ = v___x_85_;
goto v_reusejp_87_;
}
else
{
lean_object* v_reuseFailAlloc_89_; 
v_reuseFailAlloc_89_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_89_, 0, v_a_83_);
v___x_88_ = v_reuseFailAlloc_89_;
goto v_reusejp_87_;
}
v_reusejp_87_:
{
return v___x_88_;
}
}
}
else
{
lean_object* v_a_91_; lean_object* v___x_93_; uint8_t v_isShared_94_; uint8_t v_isSharedCheck_98_; 
v_a_91_ = lean_ctor_get(v___x_82_, 0);
v_isSharedCheck_98_ = !lean_is_exclusive(v___x_82_);
if (v_isSharedCheck_98_ == 0)
{
v___x_93_ = v___x_82_;
v_isShared_94_ = v_isSharedCheck_98_;
goto v_resetjp_92_;
}
else
{
lean_inc(v_a_91_);
lean_dec(v___x_82_);
v___x_93_ = lean_box(0);
v_isShared_94_ = v_isSharedCheck_98_;
goto v_resetjp_92_;
}
v_resetjp_92_:
{
lean_object* v___x_96_; 
if (v_isShared_94_ == 0)
{
v___x_96_ = v___x_93_;
goto v_reusejp_95_;
}
else
{
lean_object* v_reuseFailAlloc_97_; 
v_reuseFailAlloc_97_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_97_, 0, v_a_91_);
v___x_96_ = v_reuseFailAlloc_97_;
goto v_reusejp_95_;
}
v_reusejp_95_:
{
return v___x_96_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg___boxed(lean_object* v_e_99_, lean_object* v_k_100_, lean_object* v_cleanupAnnotations_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_107_; lean_object* v_res_108_; 
v_cleanupAnnotations_boxed_107_ = lean_unbox(v_cleanupAnnotations_101_);
v_res_108_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg(v_e_99_, v_k_100_, v_cleanupAnnotations_boxed_107_, v___y_102_, v___y_103_, v___y_104_, v___y_105_);
lean_dec(v___y_105_);
lean_dec_ref(v___y_104_);
lean_dec(v___y_103_);
lean_dec_ref(v___y_102_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1(lean_object* v_00_u03b1_109_, lean_object* v_e_110_, lean_object* v_k_111_, uint8_t v_cleanupAnnotations_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_){
_start:
{
lean_object* v___x_118_; 
v___x_118_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg(v_e_110_, v_k_111_, v_cleanupAnnotations_112_, v___y_113_, v___y_114_, v___y_115_, v___y_116_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___boxed(lean_object* v_00_u03b1_119_, lean_object* v_e_120_, lean_object* v_k_121_, lean_object* v_cleanupAnnotations_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_128_; lean_object* v_res_129_; 
v_cleanupAnnotations_boxed_128_ = lean_unbox(v_cleanupAnnotations_122_);
v_res_129_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1(v_00_u03b1_119_, v_e_120_, v_k_121_, v_cleanupAnnotations_boxed_128_, v___y_123_, v___y_124_, v___y_125_, v___y_126_);
lean_dec(v___y_126_);
lean_dec_ref(v___y_125_);
lean_dec(v___y_124_);
lean_dec_ref(v___y_123_);
return v_res_129_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0(lean_object* v_x_130_){
_start:
{
lean_object* v_indIdx_131_; 
v_indIdx_131_ = lean_ctor_get(v_x_130_, 5);
lean_inc(v_indIdx_131_);
return v_indIdx_131_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0___boxed(lean_object* v_x_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0(v_x_132_);
lean_dec_ref(v_x_132_);
return v_res_133_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1(lean_object* v___x_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_){
_start:
{
lean_object* v_toCold_143_; lean_object* v_options_144_; uint8_t v_hasTrace_145_; 
v_toCold_143_ = lean_ctor_get(v___y_140_, 0);
v_options_144_ = lean_ctor_get(v_toCold_143_, 2);
v_hasTrace_145_ = lean_ctor_get_uint8(v_options_144_, sizeof(void*)*1);
if (v_hasTrace_145_ == 0)
{
lean_object* v___x_146_; lean_object* v___x_147_; 
lean_dec(v___x_137_);
v___x_146_ = lean_box(v_hasTrace_145_);
v___x_147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_147_, 0, v___x_146_);
return v___x_147_;
}
else
{
lean_object* v_inheritedTraceOptions_148_; lean_object* v___x_149_; lean_object* v___x_150_; uint8_t v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; 
v_inheritedTraceOptions_148_ = lean_ctor_get(v_toCold_143_, 11);
v___x_149_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___closed__1));
v___x_150_ = l_Lean_Name_append(v___x_149_, v___x_137_);
v___x_151_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_148_, v_options_144_, v___x_150_);
lean_dec(v___x_150_);
v___x_152_ = lean_box(v___x_151_);
v___x_153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_153_, 0, v___x_152_);
return v___x_153_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___boxed(lean_object* v___x_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1(v___x_154_, v___y_155_, v___y_156_, v___y_157_, v___y_158_);
lean_dec(v___y_158_);
lean_dec_ref(v___y_157_);
lean_dec(v___y_156_);
lean_dec_ref(v___y_155_);
return v_res_160_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13(lean_object* v_as_161_, size_t v_i_162_, size_t v_stop_163_, lean_object* v_b_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_){
_start:
{
uint8_t v___x_170_; 
v___x_170_ = lean_usize_dec_eq(v_i_162_, v_stop_163_);
if (v___x_170_ == 0)
{
lean_object* v___x_20122__overap_171_; lean_object* v___x_172_; 
v___x_20122__overap_171_ = lean_array_uget_borrowed(v_as_161_, v_i_162_);
lean_inc(v___x_20122__overap_171_);
lean_inc(v___y_168_);
lean_inc_ref(v___y_167_);
lean_inc(v___y_166_);
lean_inc_ref(v___y_165_);
v___x_172_ = lean_apply_5(v___x_20122__overap_171_, v___y_165_, v___y_166_, v___y_167_, v___y_168_, lean_box(0));
if (lean_obj_tag(v___x_172_) == 0)
{
lean_object* v_a_173_; size_t v___x_174_; size_t v___x_175_; 
v_a_173_ = lean_ctor_get(v___x_172_, 0);
lean_inc(v_a_173_);
lean_dec_ref_known(v___x_172_, 1);
v___x_174_ = ((size_t)1ULL);
v___x_175_ = lean_usize_add(v_i_162_, v___x_174_);
v_i_162_ = v___x_175_;
v_b_164_ = v_a_173_;
goto _start;
}
else
{
return v___x_172_;
}
}
else
{
lean_object* v___x_177_; 
v___x_177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_177_, 0, v_b_164_);
return v___x_177_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13___boxed(lean_object* v_as_178_, lean_object* v_i_179_, lean_object* v_stop_180_, lean_object* v_b_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_){
_start:
{
size_t v_i_boxed_187_; size_t v_stop_boxed_188_; lean_object* v_res_189_; 
v_i_boxed_187_ = lean_unbox_usize(v_i_179_);
lean_dec(v_i_179_);
v_stop_boxed_188_ = lean_unbox_usize(v_stop_180_);
lean_dec(v_stop_180_);
v_res_189_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13(v_as_178_, v_i_boxed_187_, v_stop_boxed_188_, v_b_181_, v___y_182_, v___y_183_, v___y_184_, v___y_185_);
lean_dec(v___y_185_);
lean_dec_ref(v___y_184_);
lean_dec(v___y_183_);
lean_dec_ref(v___y_182_);
lean_dec_ref(v_as_178_);
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__24___redArg(lean_object* v_as_190_, size_t v_i_191_, size_t v_stop_192_, lean_object* v_b_193_, lean_object* v___y_194_, lean_object* v___y_195_){
_start:
{
uint8_t v___x_197_; 
v___x_197_ = lean_usize_dec_eq(v_i_191_, v_stop_192_);
if (v___x_197_ == 0)
{
lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_198_ = lean_array_uget_borrowed(v_as_190_, v_i_191_);
lean_inc(v___x_198_);
v___x_199_ = l_Lean_Elab_addAsAxiom___redArg(v___x_198_, v___y_194_, v___y_195_);
if (lean_obj_tag(v___x_199_) == 0)
{
lean_object* v_a_200_; size_t v___x_201_; size_t v___x_202_; 
v_a_200_ = lean_ctor_get(v___x_199_, 0);
lean_inc(v_a_200_);
lean_dec_ref_known(v___x_199_, 1);
v___x_201_ = ((size_t)1ULL);
v___x_202_ = lean_usize_add(v_i_191_, v___x_201_);
v_i_191_ = v___x_202_;
v_b_193_ = v_a_200_;
goto _start;
}
else
{
return v___x_199_;
}
}
else
{
lean_object* v___x_204_; 
v___x_204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_204_, 0, v_b_193_);
return v___x_204_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__24___redArg___boxed(lean_object* v_as_205_, lean_object* v_i_206_, lean_object* v_stop_207_, lean_object* v_b_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_){
_start:
{
size_t v_i_boxed_212_; size_t v_stop_boxed_213_; lean_object* v_res_214_; 
v_i_boxed_212_ = lean_unbox_usize(v_i_206_);
lean_dec(v_i_206_);
v_stop_boxed_213_ = lean_unbox_usize(v_stop_207_);
lean_dec(v_stop_207_);
v_res_214_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__24___redArg(v_as_205_, v_i_boxed_212_, v_stop_boxed_213_, v_b_208_, v___y_209_, v___y_210_);
lean_dec(v___y_210_);
lean_dec_ref(v___y_209_);
lean_dec_ref(v_as_205_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__24(lean_object* v_as_215_, size_t v_i_216_, size_t v_stop_217_, lean_object* v_b_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_){
_start:
{
lean_object* v___x_224_; 
v___x_224_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__24___redArg(v_as_215_, v_i_216_, v_stop_217_, v_b_218_, v___y_221_, v___y_222_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__24___boxed(lean_object* v_as_225_, lean_object* v_i_226_, lean_object* v_stop_227_, lean_object* v_b_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_){
_start:
{
size_t v_i_boxed_234_; size_t v_stop_boxed_235_; lean_object* v_res_236_; 
v_i_boxed_234_ = lean_unbox_usize(v_i_226_);
lean_dec(v_i_226_);
v_stop_boxed_235_ = lean_unbox_usize(v_stop_227_);
lean_dec(v_stop_227_);
v_res_236_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__24(v_as_225_, v_i_boxed_234_, v_stop_boxed_235_, v_b_228_, v___y_229_, v___y_230_, v___y_231_, v___y_232_);
lean_dec(v___y_232_);
lean_dec_ref(v___y_231_);
lean_dec(v___y_230_);
lean_dec_ref(v___y_229_);
lean_dec_ref(v_as_225_);
return v_res_236_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__0(void){
_start:
{
lean_object* v___x_237_; 
v___x_237_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_237_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__1(void){
_start:
{
lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_238_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__0, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__0);
v___x_239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_239_, 0, v___x_238_);
return v___x_239_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__2(void){
_start:
{
lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_240_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__1, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__1);
v___x_241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_241_, 0, v___x_240_);
lean_ctor_set(v___x_241_, 1, v___x_240_);
return v___x_241_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__3(void){
_start:
{
lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_242_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__1, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__1);
v___x_243_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_243_, 0, v___x_242_);
lean_ctor_set(v___x_243_, 1, v___x_242_);
lean_ctor_set(v___x_243_, 2, v___x_242_);
lean_ctor_set(v___x_243_, 3, v___x_242_);
lean_ctor_set(v___x_243_, 4, v___x_242_);
lean_ctor_set(v___x_243_, 5, v___x_242_);
lean_ctor_set(v___x_243_, 6, v___x_242_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg(lean_object* v_env_244_, lean_object* v___y_245_, lean_object* v___y_246_){
_start:
{
lean_object* v___x_248_; lean_object* v_nextMacroScope_249_; lean_object* v_ngen_250_; lean_object* v_auxDeclNGen_251_; lean_object* v_traceState_252_; lean_object* v_recordedDeps_253_; lean_object* v_messages_254_; lean_object* v_infoState_255_; lean_object* v_snapshotTasks_256_; lean_object* v___x_258_; uint8_t v_isShared_259_; uint8_t v_isSharedCheck_282_; 
v___x_248_ = lean_st_ref_take(v___y_246_);
v_nextMacroScope_249_ = lean_ctor_get(v___x_248_, 1);
v_ngen_250_ = lean_ctor_get(v___x_248_, 2);
v_auxDeclNGen_251_ = lean_ctor_get(v___x_248_, 3);
v_traceState_252_ = lean_ctor_get(v___x_248_, 4);
v_recordedDeps_253_ = lean_ctor_get(v___x_248_, 6);
v_messages_254_ = lean_ctor_get(v___x_248_, 7);
v_infoState_255_ = lean_ctor_get(v___x_248_, 8);
v_snapshotTasks_256_ = lean_ctor_get(v___x_248_, 9);
v_isSharedCheck_282_ = !lean_is_exclusive(v___x_248_);
if (v_isSharedCheck_282_ == 0)
{
lean_object* v_unused_283_; lean_object* v_unused_284_; 
v_unused_283_ = lean_ctor_get(v___x_248_, 5);
lean_dec(v_unused_283_);
v_unused_284_ = lean_ctor_get(v___x_248_, 0);
lean_dec(v_unused_284_);
v___x_258_ = v___x_248_;
v_isShared_259_ = v_isSharedCheck_282_;
goto v_resetjp_257_;
}
else
{
lean_inc(v_snapshotTasks_256_);
lean_inc(v_infoState_255_);
lean_inc(v_messages_254_);
lean_inc(v_recordedDeps_253_);
lean_inc(v_traceState_252_);
lean_inc(v_auxDeclNGen_251_);
lean_inc(v_ngen_250_);
lean_inc(v_nextMacroScope_249_);
lean_dec(v___x_248_);
v___x_258_ = lean_box(0);
v_isShared_259_ = v_isSharedCheck_282_;
goto v_resetjp_257_;
}
v_resetjp_257_:
{
lean_object* v___x_260_; lean_object* v___x_262_; 
v___x_260_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__2);
if (v_isShared_259_ == 0)
{
lean_ctor_set(v___x_258_, 5, v___x_260_);
lean_ctor_set(v___x_258_, 0, v_env_244_);
v___x_262_ = v___x_258_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v_env_244_);
lean_ctor_set(v_reuseFailAlloc_281_, 1, v_nextMacroScope_249_);
lean_ctor_set(v_reuseFailAlloc_281_, 2, v_ngen_250_);
lean_ctor_set(v_reuseFailAlloc_281_, 3, v_auxDeclNGen_251_);
lean_ctor_set(v_reuseFailAlloc_281_, 4, v_traceState_252_);
lean_ctor_set(v_reuseFailAlloc_281_, 5, v___x_260_);
lean_ctor_set(v_reuseFailAlloc_281_, 6, v_recordedDeps_253_);
lean_ctor_set(v_reuseFailAlloc_281_, 7, v_messages_254_);
lean_ctor_set(v_reuseFailAlloc_281_, 8, v_infoState_255_);
lean_ctor_set(v_reuseFailAlloc_281_, 9, v_snapshotTasks_256_);
v___x_262_ = v_reuseFailAlloc_281_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v_mctx_265_; lean_object* v_zetaDeltaFVarIds_266_; lean_object* v_postponed_267_; lean_object* v_diag_268_; lean_object* v___x_270_; uint8_t v_isShared_271_; uint8_t v_isSharedCheck_279_; 
v___x_263_ = lean_st_ref_put(v___y_246_, v___x_262_);
v___x_264_ = lean_st_ref_take(v___y_245_);
v_mctx_265_ = lean_ctor_get(v___x_264_, 0);
v_zetaDeltaFVarIds_266_ = lean_ctor_get(v___x_264_, 2);
v_postponed_267_ = lean_ctor_get(v___x_264_, 3);
v_diag_268_ = lean_ctor_get(v___x_264_, 4);
v_isSharedCheck_279_ = !lean_is_exclusive(v___x_264_);
if (v_isSharedCheck_279_ == 0)
{
lean_object* v_unused_280_; 
v_unused_280_ = lean_ctor_get(v___x_264_, 1);
lean_dec(v_unused_280_);
v___x_270_ = v___x_264_;
v_isShared_271_ = v_isSharedCheck_279_;
goto v_resetjp_269_;
}
else
{
lean_inc(v_diag_268_);
lean_inc(v_postponed_267_);
lean_inc(v_zetaDeltaFVarIds_266_);
lean_inc(v_mctx_265_);
lean_dec(v___x_264_);
v___x_270_ = lean_box(0);
v_isShared_271_ = v_isSharedCheck_279_;
goto v_resetjp_269_;
}
v_resetjp_269_:
{
lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_275_; 
v___x_272_ = lean_box(0);
v___x_273_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__3, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__3);
if (v_isShared_271_ == 0)
{
lean_ctor_set(v___x_270_, 1, v___x_273_);
v___x_275_ = v___x_270_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v_mctx_265_);
lean_ctor_set(v_reuseFailAlloc_278_, 1, v___x_273_);
lean_ctor_set(v_reuseFailAlloc_278_, 2, v_zetaDeltaFVarIds_266_);
lean_ctor_set(v_reuseFailAlloc_278_, 3, v_postponed_267_);
lean_ctor_set(v_reuseFailAlloc_278_, 4, v_diag_268_);
v___x_275_ = v_reuseFailAlloc_278_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_276_ = lean_st_ref_put(v___y_245_, v___x_275_);
v___x_277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_277_, 0, v___x_272_);
return v___x_277_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___boxed(lean_object* v_env_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg(v_env_285_, v___y_286_, v___y_287_);
lean_dec(v___y_287_);
lean_dec(v___y_286_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23___redArg(lean_object* v_env_290_, lean_object* v_x_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_){
_start:
{
lean_object* v___x_297_; lean_object* v_env_298_; lean_object* v_a_300_; lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_297_ = lean_st_ref_get(v___y_295_);
v_env_298_ = lean_ctor_get(v___x_297_, 0);
lean_inc_ref(v_env_298_);
lean_dec(v___x_297_);
v___x_310_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg(v_env_290_, v___y_293_, v___y_295_);
lean_dec_ref(v___x_310_);
lean_inc(v___y_295_);
lean_inc_ref(v___y_294_);
lean_inc(v___y_293_);
lean_inc_ref(v___y_292_);
v___x_311_ = lean_apply_5(v_x_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_, lean_box(0));
if (lean_obj_tag(v___x_311_) == 0)
{
lean_object* v_a_312_; lean_object* v___x_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_320_; 
v_a_312_ = lean_ctor_get(v___x_311_, 0);
lean_inc(v_a_312_);
lean_dec_ref_known(v___x_311_, 1);
v___x_313_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg(v_env_298_, v___y_293_, v___y_295_);
v_isSharedCheck_320_ = !lean_is_exclusive(v___x_313_);
if (v_isSharedCheck_320_ == 0)
{
lean_object* v_unused_321_; 
v_unused_321_ = lean_ctor_get(v___x_313_, 0);
lean_dec(v_unused_321_);
v___x_315_ = v___x_313_;
v_isShared_316_ = v_isSharedCheck_320_;
goto v_resetjp_314_;
}
else
{
lean_dec(v___x_313_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_320_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v___x_318_; 
if (v_isShared_316_ == 0)
{
lean_ctor_set(v___x_315_, 0, v_a_312_);
v___x_318_ = v___x_315_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v_a_312_);
v___x_318_ = v_reuseFailAlloc_319_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
return v___x_318_;
}
}
}
else
{
lean_object* v_a_322_; 
v_a_322_ = lean_ctor_get(v___x_311_, 0);
lean_inc(v_a_322_);
lean_dec_ref_known(v___x_311_, 1);
v_a_300_ = v_a_322_;
goto v___jp_299_;
}
v___jp_299_:
{
lean_object* v___x_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_308_; 
v___x_301_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg(v_env_298_, v___y_293_, v___y_295_);
v_isSharedCheck_308_ = !lean_is_exclusive(v___x_301_);
if (v_isSharedCheck_308_ == 0)
{
lean_object* v_unused_309_; 
v_unused_309_ = lean_ctor_get(v___x_301_, 0);
lean_dec(v_unused_309_);
v___x_303_ = v___x_301_;
v_isShared_304_ = v_isSharedCheck_308_;
goto v_resetjp_302_;
}
else
{
lean_dec(v___x_301_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_308_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v___x_306_; 
if (v_isShared_304_ == 0)
{
lean_ctor_set_tag(v___x_303_, 1);
lean_ctor_set(v___x_303_, 0, v_a_300_);
v___x_306_ = v___x_303_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v_a_300_);
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
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23___redArg___boxed(lean_object* v_env_323_, lean_object* v_x_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23___redArg(v_env_323_, v_x_324_, v___y_325_, v___y_326_, v___y_327_, v___y_328_);
lean_dec(v___y_328_);
lean_dec_ref(v___y_327_);
lean_dec(v___y_326_);
lean_dec_ref(v___y_325_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___lam__1(lean_object* v___x_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_){
_start:
{
lean_object* v___x_337_; 
v___x_337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_337_, 0, v___x_331_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___lam__1___boxed(lean_object* v___x_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___lam__1(v___x_338_, v___y_339_, v___y_340_, v___y_341_, v___y_342_);
lean_dec(v___y_342_);
lean_dec_ref(v___y_341_);
lean_dec(v___y_340_);
lean_dec_ref(v___y_339_);
return v_res_344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___lam__0(lean_object* v___y_345_, lean_object* v_k_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_){
_start:
{
lean_object* v___x_352_; 
lean_inc(v___y_350_);
lean_inc_ref(v___y_349_);
lean_inc(v___y_348_);
lean_inc_ref(v___y_347_);
v___x_352_ = lean_apply_5(v___y_345_, v___y_347_, v___y_348_, v___y_349_, v___y_350_, lean_box(0));
if (lean_obj_tag(v___x_352_) == 0)
{
lean_object* v___x_353_; 
lean_dec_ref_known(v___x_352_, 1);
v___x_353_ = lean_apply_5(v_k_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_, lean_box(0));
return v___x_353_;
}
else
{
lean_object* v_a_354_; lean_object* v___x_356_; uint8_t v_isShared_357_; uint8_t v_isSharedCheck_361_; 
lean_dec(v___y_350_);
lean_dec_ref(v___y_349_);
lean_dec(v___y_348_);
lean_dec_ref(v___y_347_);
lean_dec_ref(v_k_346_);
v_a_354_ = lean_ctor_get(v___x_352_, 0);
v_isSharedCheck_361_ = !lean_is_exclusive(v___x_352_);
if (v_isSharedCheck_361_ == 0)
{
v___x_356_ = v___x_352_;
v_isShared_357_ = v_isSharedCheck_361_;
goto v_resetjp_355_;
}
else
{
lean_inc(v_a_354_);
lean_dec(v___x_352_);
v___x_356_ = lean_box(0);
v_isShared_357_ = v_isSharedCheck_361_;
goto v_resetjp_355_;
}
v_resetjp_355_:
{
lean_object* v___x_359_; 
if (v_isShared_357_ == 0)
{
v___x_359_ = v___x_356_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v_a_354_);
v___x_359_ = v_reuseFailAlloc_360_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
return v___x_359_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___lam__0___boxed(lean_object* v___y_362_, lean_object* v_k_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___lam__0(v___y_362_, v_k_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_);
return v_res_369_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(lean_object* v_preDefs_374_, lean_object* v_k_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_){
_start:
{
lean_object* v___y_382_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; uint8_t v___x_391_; 
v___x_388_ = lean_unsigned_to_nat(0u);
v___x_389_ = lean_array_get_size(v_preDefs_374_);
v___x_390_ = lean_box(0);
v___x_391_ = lean_nat_dec_lt(v___x_388_, v___x_389_);
if (v___x_391_ == 0)
{
lean_object* v___f_392_; 
lean_dec_ref(v_preDefs_374_);
v___f_392_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___closed__0));
v___y_382_ = v___f_392_;
goto v___jp_381_;
}
else
{
size_t v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_393_ = lean_usize_of_nat(v___x_389_);
v___x_394_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___boxed__const__1));
v___x_395_ = lean_box_usize(v___x_393_);
v___x_396_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__24___boxed), 9, 4);
lean_closure_set(v___x_396_, 0, v_preDefs_374_);
lean_closure_set(v___x_396_, 1, v___x_394_);
lean_closure_set(v___x_396_, 2, v___x_395_);
lean_closure_set(v___x_396_, 3, v___x_390_);
v___y_382_ = v___x_396_;
goto v___jp_381_;
}
v___jp_381_:
{
lean_object* v___f_383_; lean_object* v___x_384_; lean_object* v_env_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v___f_383_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_383_, 0, v___y_382_);
lean_closure_set(v___f_383_, 1, v_k_375_);
v___x_384_ = lean_st_ref_get(v___y_379_);
v_env_385_ = lean_ctor_get(v___x_384_, 0);
lean_inc_ref(v_env_385_);
lean_dec(v___x_384_);
v___x_386_ = l_Lean_Environment_unlockAsync(v_env_385_);
v___x_387_ = l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23___redArg(v___x_386_, v___f_383_, v___y_376_, v___y_377_, v___y_378_, v___y_379_);
return v___x_387_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___boxed(lean_object* v_preDefs_397_, lean_object* v_k_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v_preDefs_397_, v_k_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_);
lean_dec(v___y_402_);
lean_dec_ref(v___y_401_);
lean_dec(v___y_400_);
lean_dec_ref(v___y_399_);
return v_res_404_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg___closed__0(void){
_start:
{
lean_object* v___x_405_; lean_object* v_dummy_406_; 
v___x_405_ = lean_box(0);
v_dummy_406_ = l_Lean_Expr_sort___override(v___x_405_);
return v_dummy_406_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg(uint8_t v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_recArgInfos_410_, lean_object* v___x_411_, lean_object* v_preDefs_412_, lean_object* v_a_413_, size_t v_sz_414_, size_t v_i_415_, lean_object* v_bs_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_){
_start:
{
uint8_t v___x_422_; 
v___x_422_ = lean_usize_dec_lt(v_i_415_, v_sz_414_);
if (v___x_422_ == 0)
{
lean_object* v___x_423_; 
lean_dec_ref(v_a_413_);
lean_dec_ref(v_preDefs_412_);
lean_dec_ref(v___x_411_);
lean_dec_ref(v_recArgInfos_410_);
v___x_423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_423_, 0, v_bs_416_);
return v___x_423_;
}
else
{
lean_object* v___x_424_; lean_object* v_v_425_; lean_object* v___x_426_; lean_object* v_bs_x27_427_; lean_object* v_a_429_; lean_object* v___x_434_; 
v___x_424_ = l_Lean_instInhabitedExpr;
v_v_425_ = lean_array_uget(v_bs_416_, v_i_415_);
v___x_426_ = lean_unsigned_to_nat(0u);
v_bs_x27_427_ = lean_array_uset(v_bs_416_, v_i_415_, v___x_426_);
v___x_434_ = lean_usize_to_nat(v_i_415_);
if (v_a_407_ == 0)
{
lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_435_ = lean_array_get_borrowed(v___x_424_, v_a_408_, v___x_434_);
v___x_436_ = lean_array_get_borrowed(v___x_424_, v_a_409_, v___x_434_);
lean_dec(v___x_434_);
lean_inc(v___x_436_);
lean_inc(v___x_435_);
lean_inc_ref(v___x_411_);
lean_inc_ref(v_recArgInfos_410_);
v___x_437_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnF___boxed), 10, 5);
lean_closure_set(v___x_437_, 0, v_recArgInfos_410_);
lean_closure_set(v___x_437_, 1, v___x_411_);
lean_closure_set(v___x_437_, 2, v_v_425_);
lean_closure_set(v___x_437_, 3, v___x_435_);
lean_closure_set(v___x_437_, 4, v___x_436_);
lean_inc_ref(v_preDefs_412_);
v___x_438_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v_preDefs_412_, v___x_437_, v___y_417_, v___y_418_, v___y_419_, v___y_420_);
if (lean_obj_tag(v___x_438_) == 0)
{
lean_object* v_a_439_; 
v_a_439_ = lean_ctor_get(v___x_438_, 0);
lean_inc(v_a_439_);
lean_dec_ref_known(v___x_438_, 1);
v_a_429_ = v_a_439_;
goto v___jp_428_;
}
else
{
lean_object* v_a_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_447_; 
lean_dec_ref(v_bs_x27_427_);
lean_dec_ref(v_a_413_);
lean_dec_ref(v_preDefs_412_);
lean_dec_ref(v___x_411_);
lean_dec_ref(v_recArgInfos_410_);
v_a_440_ = lean_ctor_get(v___x_438_, 0);
v_isSharedCheck_447_ = !lean_is_exclusive(v___x_438_);
if (v_isSharedCheck_447_ == 0)
{
v___x_442_ = v___x_438_;
v_isShared_443_ = v_isSharedCheck_447_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_a_440_);
lean_dec(v___x_438_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_447_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v___x_445_; 
if (v_isShared_443_ == 0)
{
v___x_445_ = v___x_442_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v_a_440_);
v___x_445_ = v_reuseFailAlloc_446_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
return v___x_445_;
}
}
}
}
else
{
lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v_dummy_451_; lean_object* v_nargs_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_448_ = lean_array_get_borrowed(v___x_424_, v_a_408_, v___x_434_);
v___x_449_ = lean_array_get_borrowed(v___x_424_, v_a_409_, v___x_434_);
lean_dec(v___x_434_);
lean_inc_ref(v_a_413_);
v___x_450_ = lean_apply_1(v_a_413_, v___x_426_);
v_dummy_451_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg___closed__0);
v_nargs_452_ = l_Lean_Expr_getAppNumArgs(v___x_450_);
lean_inc(v_nargs_452_);
v___x_453_ = lean_mk_array(v_nargs_452_, v_dummy_451_);
v___x_454_ = lean_unsigned_to_nat(1u);
v___x_455_ = lean_nat_sub(v_nargs_452_, v___x_454_);
lean_dec(v_nargs_452_);
v___x_456_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___x_450_, v___x_453_, v___x_455_);
lean_inc(v___x_449_);
lean_inc(v___x_448_);
lean_inc_ref(v___x_411_);
lean_inc_ref(v_recArgInfos_410_);
v___x_457_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkIndPredBRecOnF___boxed), 11, 6);
lean_closure_set(v___x_457_, 0, v_recArgInfos_410_);
lean_closure_set(v___x_457_, 1, v___x_411_);
lean_closure_set(v___x_457_, 2, v_v_425_);
lean_closure_set(v___x_457_, 3, v___x_448_);
lean_closure_set(v___x_457_, 4, v___x_449_);
lean_closure_set(v___x_457_, 5, v___x_456_);
lean_inc_ref(v_preDefs_412_);
v___x_458_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v_preDefs_412_, v___x_457_, v___y_417_, v___y_418_, v___y_419_, v___y_420_);
if (lean_obj_tag(v___x_458_) == 0)
{
lean_object* v_a_459_; lean_object* v_fst_460_; lean_object* v_snd_461_; lean_object* v___x_462_; uint8_t v___x_463_; 
v_a_459_ = lean_ctor_get(v___x_458_, 0);
lean_inc(v_a_459_);
lean_dec_ref_known(v___x_458_, 1);
v_fst_460_ = lean_ctor_get(v_a_459_, 0);
lean_inc(v_fst_460_);
v_snd_461_ = lean_ctor_get(v_a_459_, 1);
lean_inc(v_snd_461_);
lean_dec(v_a_459_);
v___x_462_ = lean_array_get_size(v_snd_461_);
v___x_463_ = lean_nat_dec_lt(v___x_426_, v___x_462_);
if (v___x_463_ == 0)
{
lean_dec(v_snd_461_);
v_a_429_ = v_fst_460_;
goto v___jp_428_;
}
else
{
lean_object* v___x_464_; size_t v___x_465_; size_t v___x_466_; lean_object* v___x_467_; 
v___x_464_ = lean_box(0);
v___x_465_ = ((size_t)0ULL);
v___x_466_ = lean_usize_of_nat(v___x_462_);
v___x_467_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13(v_snd_461_, v___x_465_, v___x_466_, v___x_464_, v___y_417_, v___y_418_, v___y_419_, v___y_420_);
lean_dec(v_snd_461_);
if (lean_obj_tag(v___x_467_) == 0)
{
lean_dec_ref_known(v___x_467_, 1);
v_a_429_ = v_fst_460_;
goto v___jp_428_;
}
else
{
lean_object* v_a_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_475_; 
lean_dec(v_fst_460_);
lean_dec_ref(v_bs_x27_427_);
lean_dec_ref(v_a_413_);
lean_dec_ref(v_preDefs_412_);
lean_dec_ref(v___x_411_);
lean_dec_ref(v_recArgInfos_410_);
v_a_468_ = lean_ctor_get(v___x_467_, 0);
v_isSharedCheck_475_ = !lean_is_exclusive(v___x_467_);
if (v_isSharedCheck_475_ == 0)
{
v___x_470_ = v___x_467_;
v_isShared_471_ = v_isSharedCheck_475_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_a_468_);
lean_dec(v___x_467_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_475_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
lean_object* v___x_473_; 
if (v_isShared_471_ == 0)
{
v___x_473_ = v___x_470_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v_a_468_);
v___x_473_ = v_reuseFailAlloc_474_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
return v___x_473_;
}
}
}
}
}
else
{
lean_object* v_a_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_483_; 
lean_dec_ref(v_bs_x27_427_);
lean_dec_ref(v_a_413_);
lean_dec_ref(v_preDefs_412_);
lean_dec_ref(v___x_411_);
lean_dec_ref(v_recArgInfos_410_);
v_a_476_ = lean_ctor_get(v___x_458_, 0);
v_isSharedCheck_483_ = !lean_is_exclusive(v___x_458_);
if (v_isSharedCheck_483_ == 0)
{
v___x_478_ = v___x_458_;
v_isShared_479_ = v_isSharedCheck_483_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_a_476_);
lean_dec(v___x_458_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_483_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v___x_481_; 
if (v_isShared_479_ == 0)
{
v___x_481_ = v___x_478_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v_a_476_);
v___x_481_ = v_reuseFailAlloc_482_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
return v___x_481_;
}
}
}
}
v___jp_428_:
{
size_t v___x_430_; size_t v___x_431_; lean_object* v___x_432_; 
v___x_430_ = ((size_t)1ULL);
v___x_431_ = lean_usize_add(v_i_415_, v___x_430_);
v___x_432_ = lean_array_uset(v_bs_x27_427_, v_i_415_, v_a_429_);
v_i_415_ = v___x_431_;
v_bs_416_ = v___x_432_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg___boxed(lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_recArgInfos_487_, lean_object* v___x_488_, lean_object* v_preDefs_489_, lean_object* v_a_490_, lean_object* v_sz_491_, lean_object* v_i_492_, lean_object* v_bs_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_){
_start:
{
uint8_t v_a_26200__boxed_499_; size_t v_sz_boxed_500_; size_t v_i_boxed_501_; lean_object* v_res_502_; 
v_a_26200__boxed_499_ = lean_unbox(v_a_484_);
v_sz_boxed_500_ = lean_unbox_usize(v_sz_491_);
lean_dec(v_sz_491_);
v_i_boxed_501_ = lean_unbox_usize(v_i_492_);
lean_dec(v_i_492_);
v_res_502_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg(v_a_26200__boxed_499_, v_a_485_, v_a_486_, v_recArgInfos_487_, v___x_488_, v_preDefs_489_, v_a_490_, v_sz_boxed_500_, v_i_boxed_501_, v_bs_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_);
lean_dec(v___y_497_);
lean_dec_ref(v___y_496_);
lean_dec(v___y_495_);
lean_dec_ref(v___y_494_);
lean_dec_ref(v_a_486_);
lean_dec_ref(v_a_485_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11_spec__21(lean_object* v_msgData_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_){
_start:
{
lean_object* v___x_509_; lean_object* v_env_510_; uint8_t v___x_511_; lean_object* v_env_512_; lean_object* v___x_513_; lean_object* v_toCold_514_; lean_object* v_mctx_515_; lean_object* v_lctx_516_; lean_object* v_options_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_509_ = lean_st_ref_get(v___y_507_);
v_env_510_ = lean_ctor_get(v___x_509_, 0);
lean_inc_ref(v_env_510_);
lean_dec(v___x_509_);
v___x_511_ = 0;
v_env_512_ = l_Lean_Environment_setRecordingDeps(v_env_510_, v___x_511_);
v___x_513_ = lean_st_ref_get(v___y_505_);
v_toCold_514_ = lean_ctor_get(v___y_506_, 0);
v_mctx_515_ = lean_ctor_get(v___x_513_, 0);
lean_inc_ref(v_mctx_515_);
lean_dec(v___x_513_);
v_lctx_516_ = lean_ctor_get(v___y_504_, 2);
v_options_517_ = lean_ctor_get(v_toCold_514_, 2);
lean_inc_ref(v_options_517_);
lean_inc_ref(v_lctx_516_);
v___x_518_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_518_, 0, v_env_512_);
lean_ctor_set(v___x_518_, 1, v_mctx_515_);
lean_ctor_set(v___x_518_, 2, v_lctx_516_);
lean_ctor_set(v___x_518_, 3, v_options_517_);
v___x_519_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_519_, 0, v___x_518_);
lean_ctor_set(v___x_519_, 1, v_msgData_503_);
v___x_520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_520_, 0, v___x_519_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11_spec__21___boxed(lean_object* v_msgData_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11_spec__21(v_msgData_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_);
lean_dec(v___y_525_);
lean_dec_ref(v___y_524_);
lean_dec(v___y_523_);
lean_dec_ref(v___y_522_);
return v_res_527_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___closed__0(void){
_start:
{
lean_object* v___x_528_; double v___x_529_; 
v___x_528_ = lean_unsigned_to_nat(0u);
v___x_529_ = lean_float_of_nat(v___x_528_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(lean_object* v_cls_533_, lean_object* v_msg_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_){
_start:
{
lean_object* v_ref_540_; lean_object* v___x_541_; lean_object* v_a_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_587_; 
v_ref_540_ = lean_ctor_get(v___y_537_, 2);
v___x_541_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11_spec__21(v_msg_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_);
v_a_542_ = lean_ctor_get(v___x_541_, 0);
v_isSharedCheck_587_ = !lean_is_exclusive(v___x_541_);
if (v_isSharedCheck_587_ == 0)
{
v___x_544_ = v___x_541_;
v_isShared_545_ = v_isSharedCheck_587_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_a_542_);
lean_dec(v___x_541_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_587_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v___x_546_; lean_object* v_traceState_547_; lean_object* v_env_548_; lean_object* v_nextMacroScope_549_; lean_object* v_ngen_550_; lean_object* v_auxDeclNGen_551_; lean_object* v_cache_552_; lean_object* v_recordedDeps_553_; lean_object* v_messages_554_; lean_object* v_infoState_555_; lean_object* v_snapshotTasks_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_586_; 
v___x_546_ = lean_st_ref_take(v___y_538_);
v_traceState_547_ = lean_ctor_get(v___x_546_, 4);
v_env_548_ = lean_ctor_get(v___x_546_, 0);
v_nextMacroScope_549_ = lean_ctor_get(v___x_546_, 1);
v_ngen_550_ = lean_ctor_get(v___x_546_, 2);
v_auxDeclNGen_551_ = lean_ctor_get(v___x_546_, 3);
v_cache_552_ = lean_ctor_get(v___x_546_, 5);
v_recordedDeps_553_ = lean_ctor_get(v___x_546_, 6);
v_messages_554_ = lean_ctor_get(v___x_546_, 7);
v_infoState_555_ = lean_ctor_get(v___x_546_, 8);
v_snapshotTasks_556_ = lean_ctor_get(v___x_546_, 9);
v_isSharedCheck_586_ = !lean_is_exclusive(v___x_546_);
if (v_isSharedCheck_586_ == 0)
{
v___x_558_ = v___x_546_;
v_isShared_559_ = v_isSharedCheck_586_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_snapshotTasks_556_);
lean_inc(v_infoState_555_);
lean_inc(v_messages_554_);
lean_inc(v_recordedDeps_553_);
lean_inc(v_cache_552_);
lean_inc(v_traceState_547_);
lean_inc(v_auxDeclNGen_551_);
lean_inc(v_ngen_550_);
lean_inc(v_nextMacroScope_549_);
lean_inc(v_env_548_);
lean_dec(v___x_546_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_586_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
uint64_t v_tid_560_; lean_object* v_traces_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_585_; 
v_tid_560_ = lean_ctor_get_uint64(v_traceState_547_, sizeof(void*)*1);
v_traces_561_ = lean_ctor_get(v_traceState_547_, 0);
v_isSharedCheck_585_ = !lean_is_exclusive(v_traceState_547_);
if (v_isSharedCheck_585_ == 0)
{
v___x_563_ = v_traceState_547_;
v_isShared_564_ = v_isSharedCheck_585_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_traces_561_);
lean_dec(v_traceState_547_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_585_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v___x_565_; lean_object* v___x_566_; double v___x_567_; uint8_t v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_576_; 
v___x_565_ = lean_box(0);
v___x_566_ = lean_box(0);
v___x_567_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___closed__0);
v___x_568_ = 0;
v___x_569_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___closed__1));
v___x_570_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_570_, 0, v_cls_533_);
lean_ctor_set(v___x_570_, 1, v___x_566_);
lean_ctor_set(v___x_570_, 2, v___x_569_);
lean_ctor_set_float(v___x_570_, sizeof(void*)*3, v___x_567_);
lean_ctor_set_float(v___x_570_, sizeof(void*)*3 + 8, v___x_567_);
lean_ctor_set_uint8(v___x_570_, sizeof(void*)*3 + 16, v___x_568_);
v___x_571_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___closed__2));
v___x_572_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_572_, 0, v___x_570_);
lean_ctor_set(v___x_572_, 1, v_a_542_);
lean_ctor_set(v___x_572_, 2, v___x_571_);
lean_inc(v_ref_540_);
v___x_573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_573_, 0, v_ref_540_);
lean_ctor_set(v___x_573_, 1, v___x_572_);
v___x_574_ = l_Lean_PersistentArray_push___redArg(v_traces_561_, v___x_573_);
if (v_isShared_564_ == 0)
{
lean_ctor_set(v___x_563_, 0, v___x_574_);
v___x_576_ = v___x_563_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v___x_574_);
lean_ctor_set_uint64(v_reuseFailAlloc_584_, sizeof(void*)*1, v_tid_560_);
v___x_576_ = v_reuseFailAlloc_584_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
lean_object* v___x_578_; 
if (v_isShared_559_ == 0)
{
lean_ctor_set(v___x_558_, 4, v___x_576_);
v___x_578_ = v___x_558_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v_env_548_);
lean_ctor_set(v_reuseFailAlloc_583_, 1, v_nextMacroScope_549_);
lean_ctor_set(v_reuseFailAlloc_583_, 2, v_ngen_550_);
lean_ctor_set(v_reuseFailAlloc_583_, 3, v_auxDeclNGen_551_);
lean_ctor_set(v_reuseFailAlloc_583_, 4, v___x_576_);
lean_ctor_set(v_reuseFailAlloc_583_, 5, v_cache_552_);
lean_ctor_set(v_reuseFailAlloc_583_, 6, v_recordedDeps_553_);
lean_ctor_set(v_reuseFailAlloc_583_, 7, v_messages_554_);
lean_ctor_set(v_reuseFailAlloc_583_, 8, v_infoState_555_);
lean_ctor_set(v_reuseFailAlloc_583_, 9, v_snapshotTasks_556_);
v___x_578_ = v_reuseFailAlloc_583_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
lean_object* v___x_579_; lean_object* v___x_581_; 
v___x_579_ = lean_st_ref_put(v___y_538_, v___x_578_);
if (v_isShared_545_ == 0)
{
lean_ctor_set(v___x_544_, 0, v___x_565_);
v___x_581_ = v___x_544_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v___x_565_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___boxed(lean_object* v_cls_588_, lean_object* v_msg_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v_cls_588_, v_msg_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_);
lean_dec(v___y_593_);
lean_dec_ref(v___y_592_);
lean_dec(v___y_591_);
lean_dec_ref(v___y_590_);
return v_res_595_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9(lean_object* v_as_596_, lean_object* v_bs_597_, lean_object* v_i_598_, lean_object* v_cs_599_){
_start:
{
lean_object* v___x_600_; uint8_t v___x_601_; 
v___x_600_ = lean_array_get_size(v_as_596_);
v___x_601_ = lean_nat_dec_lt(v_i_598_, v___x_600_);
if (v___x_601_ == 0)
{
lean_dec(v_i_598_);
return v_cs_599_;
}
else
{
lean_object* v___x_602_; uint8_t v___x_603_; 
v___x_602_ = lean_array_get_size(v_bs_597_);
v___x_603_ = lean_nat_dec_lt(v_i_598_, v___x_602_);
if (v___x_603_ == 0)
{
lean_dec(v_i_598_);
return v_cs_599_;
}
else
{
lean_object* v_a_604_; lean_object* v_ref_605_; uint8_t v_kind_606_; lean_object* v_levelParams_607_; lean_object* v_modifiers_608_; lean_object* v_declName_609_; lean_object* v_binders_610_; lean_object* v_numSectionVars_611_; lean_object* v_type_612_; lean_object* v_termination_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_625_; 
v_a_604_ = lean_array_fget(v_as_596_, v_i_598_);
v_ref_605_ = lean_ctor_get(v_a_604_, 0);
v_kind_606_ = lean_ctor_get_uint8(v_a_604_, sizeof(void*)*9);
v_levelParams_607_ = lean_ctor_get(v_a_604_, 1);
v_modifiers_608_ = lean_ctor_get(v_a_604_, 2);
v_declName_609_ = lean_ctor_get(v_a_604_, 3);
v_binders_610_ = lean_ctor_get(v_a_604_, 4);
v_numSectionVars_611_ = lean_ctor_get(v_a_604_, 5);
v_type_612_ = lean_ctor_get(v_a_604_, 6);
v_termination_613_ = lean_ctor_get(v_a_604_, 8);
v_isSharedCheck_625_ = !lean_is_exclusive(v_a_604_);
if (v_isSharedCheck_625_ == 0)
{
lean_object* v_unused_626_; 
v_unused_626_ = lean_ctor_get(v_a_604_, 7);
lean_dec(v_unused_626_);
v___x_615_ = v_a_604_;
v_isShared_616_ = v_isSharedCheck_625_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_termination_613_);
lean_inc(v_type_612_);
lean_inc(v_numSectionVars_611_);
lean_inc(v_binders_610_);
lean_inc(v_declName_609_);
lean_inc(v_modifiers_608_);
lean_inc(v_levelParams_607_);
lean_inc(v_ref_605_);
lean_dec(v_a_604_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_625_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
lean_object* v_b_617_; lean_object* v___x_619_; 
v_b_617_ = lean_array_fget_borrowed(v_bs_597_, v_i_598_);
lean_inc(v_b_617_);
if (v_isShared_616_ == 0)
{
lean_ctor_set(v___x_615_, 7, v_b_617_);
v___x_619_ = v___x_615_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_ref_605_);
lean_ctor_set(v_reuseFailAlloc_624_, 1, v_levelParams_607_);
lean_ctor_set(v_reuseFailAlloc_624_, 2, v_modifiers_608_);
lean_ctor_set(v_reuseFailAlloc_624_, 3, v_declName_609_);
lean_ctor_set(v_reuseFailAlloc_624_, 4, v_binders_610_);
lean_ctor_set(v_reuseFailAlloc_624_, 5, v_numSectionVars_611_);
lean_ctor_set(v_reuseFailAlloc_624_, 6, v_type_612_);
lean_ctor_set(v_reuseFailAlloc_624_, 7, v_b_617_);
lean_ctor_set(v_reuseFailAlloc_624_, 8, v_termination_613_);
lean_ctor_set_uint8(v_reuseFailAlloc_624_, sizeof(void*)*9, v_kind_606_);
v___x_619_ = v_reuseFailAlloc_624_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_620_ = lean_unsigned_to_nat(1u);
v___x_621_ = lean_nat_add(v_i_598_, v___x_620_);
lean_dec(v_i_598_);
v___x_622_ = lean_array_push(v_cs_599_, v___x_619_);
v_i_598_ = v___x_621_;
v_cs_599_ = v___x_622_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9___boxed(lean_object* v_as_627_, lean_object* v_bs_628_, lean_object* v_i_629_, lean_object* v_cs_630_){
_start:
{
lean_object* v_res_631_; 
v_res_631_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9(v_as_627_, v_bs_628_, v_i_629_, v_cs_630_);
lean_dec_ref(v_bs_628_);
lean_dec_ref(v_as_627_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17_spec__30___redArg(lean_object* v_declName_632_, uint8_t v_s_633_, lean_object* v___y_634_, lean_object* v___y_635_){
_start:
{
lean_object* v___x_637_; lean_object* v_env_638_; lean_object* v_nextMacroScope_639_; lean_object* v_ngen_640_; lean_object* v_auxDeclNGen_641_; lean_object* v_traceState_642_; lean_object* v_recordedDeps_643_; lean_object* v_messages_644_; lean_object* v_infoState_645_; lean_object* v_snapshotTasks_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_675_; 
v___x_637_ = lean_st_ref_take(v___y_635_);
v_env_638_ = lean_ctor_get(v___x_637_, 0);
v_nextMacroScope_639_ = lean_ctor_get(v___x_637_, 1);
v_ngen_640_ = lean_ctor_get(v___x_637_, 2);
v_auxDeclNGen_641_ = lean_ctor_get(v___x_637_, 3);
v_traceState_642_ = lean_ctor_get(v___x_637_, 4);
v_recordedDeps_643_ = lean_ctor_get(v___x_637_, 6);
v_messages_644_ = lean_ctor_get(v___x_637_, 7);
v_infoState_645_ = lean_ctor_get(v___x_637_, 8);
v_snapshotTasks_646_ = lean_ctor_get(v___x_637_, 9);
v_isSharedCheck_675_ = !lean_is_exclusive(v___x_637_);
if (v_isSharedCheck_675_ == 0)
{
lean_object* v_unused_676_; 
v_unused_676_ = lean_ctor_get(v___x_637_, 5);
lean_dec(v_unused_676_);
v___x_648_ = v___x_637_;
v_isShared_649_ = v_isSharedCheck_675_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_snapshotTasks_646_);
lean_inc(v_infoState_645_);
lean_inc(v_messages_644_);
lean_inc(v_recordedDeps_643_);
lean_inc(v_traceState_642_);
lean_inc(v_auxDeclNGen_641_);
lean_inc(v_ngen_640_);
lean_inc(v_nextMacroScope_639_);
lean_inc(v_env_638_);
lean_dec(v___x_637_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_675_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
uint8_t v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_655_; 
v___x_650_ = 0;
v___x_651_ = lean_box(0);
v___x_652_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_638_, v_declName_632_, v_s_633_, v___x_650_, v___x_651_);
v___x_653_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__2);
if (v_isShared_649_ == 0)
{
lean_ctor_set(v___x_648_, 5, v___x_653_);
lean_ctor_set(v___x_648_, 0, v___x_652_);
v___x_655_ = v___x_648_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v___x_652_);
lean_ctor_set(v_reuseFailAlloc_674_, 1, v_nextMacroScope_639_);
lean_ctor_set(v_reuseFailAlloc_674_, 2, v_ngen_640_);
lean_ctor_set(v_reuseFailAlloc_674_, 3, v_auxDeclNGen_641_);
lean_ctor_set(v_reuseFailAlloc_674_, 4, v_traceState_642_);
lean_ctor_set(v_reuseFailAlloc_674_, 5, v___x_653_);
lean_ctor_set(v_reuseFailAlloc_674_, 6, v_recordedDeps_643_);
lean_ctor_set(v_reuseFailAlloc_674_, 7, v_messages_644_);
lean_ctor_set(v_reuseFailAlloc_674_, 8, v_infoState_645_);
lean_ctor_set(v_reuseFailAlloc_674_, 9, v_snapshotTasks_646_);
v___x_655_ = v_reuseFailAlloc_674_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v_mctx_658_; lean_object* v_zetaDeltaFVarIds_659_; lean_object* v_postponed_660_; lean_object* v_diag_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_672_; 
v___x_656_ = lean_st_ref_put(v___y_635_, v___x_655_);
v___x_657_ = lean_st_ref_take(v___y_634_);
v_mctx_658_ = lean_ctor_get(v___x_657_, 0);
v_zetaDeltaFVarIds_659_ = lean_ctor_get(v___x_657_, 2);
v_postponed_660_ = lean_ctor_get(v___x_657_, 3);
v_diag_661_ = lean_ctor_get(v___x_657_, 4);
v_isSharedCheck_672_ = !lean_is_exclusive(v___x_657_);
if (v_isSharedCheck_672_ == 0)
{
lean_object* v_unused_673_; 
v_unused_673_ = lean_ctor_get(v___x_657_, 1);
lean_dec(v_unused_673_);
v___x_663_ = v___x_657_;
v_isShared_664_ = v_isSharedCheck_672_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_diag_661_);
lean_inc(v_postponed_660_);
lean_inc(v_zetaDeltaFVarIds_659_);
lean_inc(v_mctx_658_);
lean_dec(v___x_657_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_672_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_668_; 
v___x_665_ = lean_box(0);
v___x_666_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__3, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__3);
if (v_isShared_664_ == 0)
{
lean_ctor_set(v___x_663_, 1, v___x_666_);
v___x_668_ = v___x_663_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_mctx_658_);
lean_ctor_set(v_reuseFailAlloc_671_, 1, v___x_666_);
lean_ctor_set(v_reuseFailAlloc_671_, 2, v_zetaDeltaFVarIds_659_);
lean_ctor_set(v_reuseFailAlloc_671_, 3, v_postponed_660_);
lean_ctor_set(v_reuseFailAlloc_671_, 4, v_diag_661_);
v___x_668_ = v_reuseFailAlloc_671_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_669_ = lean_st_ref_put(v___y_634_, v___x_668_);
v___x_670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_670_, 0, v___x_665_);
return v___x_670_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17_spec__30___redArg___boxed(lean_object* v_declName_677_, lean_object* v_s_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_){
_start:
{
uint8_t v_s_boxed_682_; lean_object* v_res_683_; 
v_s_boxed_682_ = lean_unbox(v_s_678_);
v_res_683_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17_spec__30___redArg(v_declName_677_, v_s_boxed_682_, v___y_679_, v___y_680_);
lean_dec(v___y_680_);
lean_dec(v___y_679_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17(lean_object* v_declName_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_){
_start:
{
uint8_t v___x_690_; lean_object* v___x_691_; 
v___x_690_ = 0;
v___x_691_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17_spec__30___redArg(v_declName_684_, v___x_690_, v___y_686_, v___y_688_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___boxed(lean_object* v_declName_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_){
_start:
{
lean_object* v_res_698_; 
v_res_698_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17(v_declName_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_);
lean_dec(v___y_696_);
lean_dec_ref(v___y_695_);
lean_dec(v___y_694_);
lean_dec_ref(v___y_693_);
return v_res_698_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16(size_t v_sz_699_, size_t v_i_700_, lean_object* v_bs_701_){
_start:
{
uint8_t v___x_702_; 
v___x_702_ = lean_usize_dec_lt(v_i_700_, v_sz_699_);
if (v___x_702_ == 0)
{
return v_bs_701_;
}
else
{
lean_object* v_v_703_; lean_object* v_declName_704_; lean_object* v___x_705_; lean_object* v_bs_x27_706_; size_t v___x_707_; size_t v___x_708_; lean_object* v___x_709_; 
v_v_703_ = lean_array_uget_borrowed(v_bs_701_, v_i_700_);
v_declName_704_ = lean_ctor_get(v_v_703_, 3);
lean_inc(v_declName_704_);
v___x_705_ = lean_unsigned_to_nat(0u);
v_bs_x27_706_ = lean_array_uset(v_bs_701_, v_i_700_, v___x_705_);
v___x_707_ = ((size_t)1ULL);
v___x_708_ = lean_usize_add(v_i_700_, v___x_707_);
v___x_709_ = lean_array_uset(v_bs_x27_706_, v_i_700_, v_declName_704_);
v_i_700_ = v___x_708_;
v_bs_701_ = v___x_709_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16___boxed(lean_object* v_sz_711_, lean_object* v_i_712_, lean_object* v_bs_713_){
_start:
{
size_t v_sz_boxed_714_; size_t v_i_boxed_715_; lean_object* v_res_716_; 
v_sz_boxed_714_ = lean_unbox_usize(v_sz_711_);
lean_dec(v_sz_711_);
v_i_boxed_715_ = lean_unbox_usize(v_i_712_);
lean_dec(v_i_712_);
v_res_716_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16(v_sz_boxed_714_, v_i_boxed_715_, v_bs_713_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___redArg(lean_object* v_preDefs_720_, lean_object* v_xs_721_, uint8_t v_a_722_, lean_object* v___x_723_, size_t v_sz_724_, size_t v_i_725_, lean_object* v_bs_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_){
_start:
{
uint8_t v___x_732_; 
v___x_732_ = lean_usize_dec_lt(v_i_725_, v_sz_724_);
if (v___x_732_ == 0)
{
lean_object* v___x_733_; 
lean_dec(v___x_723_);
lean_dec_ref(v_preDefs_720_);
v___x_733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_733_, 0, v_bs_726_);
return v___x_733_;
}
else
{
lean_object* v___x_734_; lean_object* v_v_735_; lean_object* v___x_736_; lean_object* v_bs_x27_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v_levelParams_740_; lean_object* v_modifiers_741_; lean_object* v_declName_742_; lean_object* v___x_743_; lean_object* v___x_744_; uint8_t v___x_745_; lean_object* v___x_746_; 
v___x_734_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v_v_735_ = lean_array_uget(v_bs_726_, v_i_725_);
v___x_736_ = lean_unsigned_to_nat(0u);
v_bs_x27_737_ = lean_array_uset(v_bs_726_, v_i_725_, v___x_736_);
v___x_738_ = lean_usize_to_nat(v_i_725_);
v___x_739_ = lean_array_get_borrowed(v___x_734_, v_preDefs_720_, v___x_738_);
lean_dec(v___x_738_);
v_levelParams_740_ = lean_ctor_get(v___x_739_, 1);
v_modifiers_741_ = lean_ctor_get(v___x_739_, 2);
v_declName_742_ = lean_ctor_get(v___x_739_, 3);
v___x_743_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___redArg___closed__1));
lean_inc(v_declName_742_);
v___x_744_ = l_Lean_Name_append(v_declName_742_, v___x_743_);
v___x_745_ = 1;
v___x_746_ = l_Lean_Meta_mkLambdaFVars(v_xs_721_, v_v_735_, v_a_722_, v___x_732_, v_a_722_, v___x_732_, v___x_745_, v___y_727_, v___y_728_, v___y_729_, v___y_730_);
if (lean_obj_tag(v___x_746_) == 0)
{
lean_object* v_a_747_; lean_object* v___x_748_; 
v_a_747_ = lean_ctor_get(v___x_746_, 0);
lean_inc(v_a_747_);
lean_dec_ref_known(v___x_746_, 1);
v___x_748_ = l_Lean_Elab_eraseRecAppSyntaxExpr(v_a_747_, v___y_729_, v___y_730_);
if (lean_obj_tag(v___x_748_) == 0)
{
lean_object* v_a_749_; size_t v_sz_750_; size_t v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; 
v_a_749_ = lean_ctor_get(v___x_748_, 0);
lean_inc_n(v_a_749_, 2);
lean_dec_ref_known(v___x_748_, 1);
v_sz_750_ = lean_array_size(v_preDefs_720_);
v___x_751_ = ((size_t)0ULL);
lean_inc_ref(v_preDefs_720_);
v___x_752_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16(v_sz_750_, v___x_751_, v_preDefs_720_);
v___x_753_ = l_Lean_Elab_ensureNoRecFn(v___x_752_, v_a_749_, v___y_727_, v___y_728_, v___y_729_, v___y_730_);
if (lean_obj_tag(v___x_753_) == 0)
{
lean_object* v___x_754_; 
lean_dec_ref_known(v___x_753_, 1);
lean_inc(v___y_730_);
lean_inc_ref(v___y_729_);
lean_inc(v___y_728_);
lean_inc_ref(v___y_727_);
lean_inc(v_a_749_);
v___x_754_ = lean_infer_type(v_a_749_, v___y_727_, v___y_728_, v___y_729_, v___y_730_);
if (lean_obj_tag(v___x_754_) == 0)
{
lean_object* v_a_755_; lean_object* v___x_756_; 
v_a_755_ = lean_ctor_get(v___x_754_, 0);
lean_inc(v_a_755_);
lean_dec_ref_known(v___x_754_, 1);
v___x_756_ = l_Lean_Meta_letToHave(v_a_755_, v___y_727_, v___y_728_, v___y_729_, v___y_730_);
if (lean_obj_tag(v___x_756_) == 0)
{
lean_object* v_a_757_; lean_object* v___x_758_; lean_object* v_env_759_; uint8_t v_isUnsafe_760_; uint32_t v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; uint8_t v___y_765_; 
v_a_757_ = lean_ctor_get(v___x_756_, 0);
lean_inc(v_a_757_);
lean_dec_ref_known(v___x_756_, 1);
v___x_758_ = lean_st_ref_get(v___y_730_);
v_env_759_ = lean_ctor_get(v___x_758_, 0);
lean_inc_ref(v_env_759_);
lean_dec(v___x_758_);
v_isUnsafe_760_ = lean_ctor_get_uint8(v_modifiers_741_, sizeof(void*)*3 + 4);
lean_inc(v_a_749_);
v___x_761_ = l_Lean_getMaxHeight(v_env_759_, v_a_749_);
lean_inc(v_levelParams_740_);
lean_inc(v___x_744_);
v___x_762_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_762_, 0, v___x_744_);
lean_ctor_set(v___x_762_, 1, v_levelParams_740_);
lean_ctor_set(v___x_762_, 2, v_a_757_);
v___x_763_ = lean_box(1);
if (v_isUnsafe_760_ == 0)
{
uint8_t v___x_830_; 
v___x_830_ = 1;
v___y_765_ = v___x_830_;
goto v___jp_764_;
}
else
{
uint8_t v___x_831_; 
v___x_831_ = 0;
v___y_765_ = v___x_831_;
goto v___jp_764_;
}
v___jp_764_:
{
lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_766_ = lean_box(0);
lean_inc(v___x_744_);
v___x_767_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_767_, 0, v___x_744_);
lean_ctor_set(v___x_767_, 1, v___x_766_);
v___x_768_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_768_, 0, v___x_762_);
lean_ctor_set(v___x_768_, 1, v_a_749_);
lean_ctor_set(v___x_768_, 2, v___x_763_);
lean_ctor_set(v___x_768_, 3, v___x_767_);
lean_ctor_set_uint8(v___x_768_, sizeof(void*)*4, v___y_765_);
v___x_769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_769_, 0, v___x_768_);
v___x_770_ = l_Lean_addDecl(v___x_769_, v_a_722_, v___y_729_, v___y_730_);
if (lean_obj_tag(v___x_770_) == 0)
{
lean_object* v___x_771_; lean_object* v_env_772_; lean_object* v_nextMacroScope_773_; lean_object* v_ngen_774_; lean_object* v_auxDeclNGen_775_; lean_object* v_traceState_776_; lean_object* v_recordedDeps_777_; lean_object* v_messages_778_; lean_object* v_infoState_779_; lean_object* v_snapshotTasks_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_820_; 
lean_dec_ref_known(v___x_770_, 1);
v___x_771_ = lean_st_ref_take(v___y_730_);
v_env_772_ = lean_ctor_get(v___x_771_, 0);
v_nextMacroScope_773_ = lean_ctor_get(v___x_771_, 1);
v_ngen_774_ = lean_ctor_get(v___x_771_, 2);
v_auxDeclNGen_775_ = lean_ctor_get(v___x_771_, 3);
v_traceState_776_ = lean_ctor_get(v___x_771_, 4);
v_recordedDeps_777_ = lean_ctor_get(v___x_771_, 6);
v_messages_778_ = lean_ctor_get(v___x_771_, 7);
v_infoState_779_ = lean_ctor_get(v___x_771_, 8);
v_snapshotTasks_780_ = lean_ctor_get(v___x_771_, 9);
v_isSharedCheck_820_ = !lean_is_exclusive(v___x_771_);
if (v_isSharedCheck_820_ == 0)
{
lean_object* v_unused_821_; 
v_unused_821_ = lean_ctor_get(v___x_771_, 5);
lean_dec(v_unused_821_);
v___x_782_ = v___x_771_;
v_isShared_783_ = v_isSharedCheck_820_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_snapshotTasks_780_);
lean_inc(v_infoState_779_);
lean_inc(v_messages_778_);
lean_inc(v_recordedDeps_777_);
lean_inc(v_traceState_776_);
lean_inc(v_auxDeclNGen_775_);
lean_inc(v_ngen_774_);
lean_inc(v_nextMacroScope_773_);
lean_inc(v_env_772_);
lean_dec(v___x_771_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_820_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_787_; 
lean_inc(v___x_744_);
v___x_784_ = l_Lean_setDefHeightOverride(v_env_772_, v___x_744_, v___x_761_);
v___x_785_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__2);
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 5, v___x_785_);
lean_ctor_set(v___x_782_, 0, v___x_784_);
v___x_787_ = v___x_782_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v___x_784_);
lean_ctor_set(v_reuseFailAlloc_819_, 1, v_nextMacroScope_773_);
lean_ctor_set(v_reuseFailAlloc_819_, 2, v_ngen_774_);
lean_ctor_set(v_reuseFailAlloc_819_, 3, v_auxDeclNGen_775_);
lean_ctor_set(v_reuseFailAlloc_819_, 4, v_traceState_776_);
lean_ctor_set(v_reuseFailAlloc_819_, 5, v___x_785_);
lean_ctor_set(v_reuseFailAlloc_819_, 6, v_recordedDeps_777_);
lean_ctor_set(v_reuseFailAlloc_819_, 7, v_messages_778_);
lean_ctor_set(v_reuseFailAlloc_819_, 8, v_infoState_779_);
lean_ctor_set(v_reuseFailAlloc_819_, 9, v_snapshotTasks_780_);
v___x_787_ = v_reuseFailAlloc_819_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v_mctx_790_; lean_object* v_zetaDeltaFVarIds_791_; lean_object* v_postponed_792_; lean_object* v_diag_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_817_; 
v___x_788_ = lean_st_ref_put(v___y_730_, v___x_787_);
v___x_789_ = lean_st_ref_take(v___y_728_);
v_mctx_790_ = lean_ctor_get(v___x_789_, 0);
v_zetaDeltaFVarIds_791_ = lean_ctor_get(v___x_789_, 2);
v_postponed_792_ = lean_ctor_get(v___x_789_, 3);
v_diag_793_ = lean_ctor_get(v___x_789_, 4);
v_isSharedCheck_817_ = !lean_is_exclusive(v___x_789_);
if (v_isSharedCheck_817_ == 0)
{
lean_object* v_unused_818_; 
v_unused_818_ = lean_ctor_get(v___x_789_, 1);
lean_dec(v_unused_818_);
v___x_795_ = v___x_789_;
v_isShared_796_ = v_isSharedCheck_817_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_diag_793_);
lean_inc(v_postponed_792_);
lean_inc(v_zetaDeltaFVarIds_791_);
lean_inc(v_mctx_790_);
lean_dec(v___x_789_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_817_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_797_; lean_object* v___x_799_; 
v___x_797_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__3, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__3);
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 1, v___x_797_);
v___x_799_ = v___x_795_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_mctx_790_);
lean_ctor_set(v_reuseFailAlloc_816_, 1, v___x_797_);
lean_ctor_set(v_reuseFailAlloc_816_, 2, v_zetaDeltaFVarIds_791_);
lean_ctor_set(v_reuseFailAlloc_816_, 3, v_postponed_792_);
lean_ctor_set(v_reuseFailAlloc_816_, 4, v_diag_793_);
v___x_799_ = v_reuseFailAlloc_816_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
lean_object* v___x_800_; lean_object* v___x_801_; 
v___x_800_ = lean_st_ref_put(v___y_728_, v___x_799_);
lean_inc(v___x_744_);
v___x_801_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17(v___x_744_, v___y_727_, v___y_728_, v___y_729_, v___y_730_);
if (lean_obj_tag(v___x_801_) == 0)
{
lean_object* v___x_802_; lean_object* v___x_803_; size_t v___x_804_; size_t v___x_805_; lean_object* v___x_806_; 
lean_dec_ref_known(v___x_801_, 1);
lean_inc(v___x_723_);
v___x_802_ = l_Lean_mkConst(v___x_744_, v___x_723_);
v___x_803_ = l_Lean_mkAppN(v___x_802_, v_xs_721_);
v___x_804_ = ((size_t)1ULL);
v___x_805_ = lean_usize_add(v_i_725_, v___x_804_);
v___x_806_ = lean_array_uset(v_bs_x27_737_, v_i_725_, v___x_803_);
v_i_725_ = v___x_805_;
v_bs_726_ = v___x_806_;
goto _start;
}
else
{
lean_object* v_a_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_815_; 
lean_dec(v___x_744_);
lean_dec_ref(v_bs_x27_737_);
lean_dec(v___x_723_);
lean_dec_ref(v_preDefs_720_);
v_a_808_ = lean_ctor_get(v___x_801_, 0);
v_isSharedCheck_815_ = !lean_is_exclusive(v___x_801_);
if (v_isSharedCheck_815_ == 0)
{
v___x_810_ = v___x_801_;
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_a_808_);
lean_dec(v___x_801_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
lean_object* v___x_813_; 
if (v_isShared_811_ == 0)
{
v___x_813_ = v___x_810_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v_a_808_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
return v___x_813_;
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
lean_object* v_a_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_829_; 
lean_dec(v___x_744_);
lean_dec_ref(v_bs_x27_737_);
lean_dec(v___x_723_);
lean_dec_ref(v_preDefs_720_);
v_a_822_ = lean_ctor_get(v___x_770_, 0);
v_isSharedCheck_829_ = !lean_is_exclusive(v___x_770_);
if (v_isSharedCheck_829_ == 0)
{
v___x_824_ = v___x_770_;
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_a_822_);
lean_dec(v___x_770_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v___x_827_; 
if (v_isShared_825_ == 0)
{
v___x_827_ = v___x_824_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v_a_822_);
v___x_827_ = v_reuseFailAlloc_828_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
return v___x_827_;
}
}
}
}
}
else
{
lean_object* v_a_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_839_; 
lean_dec(v_a_749_);
lean_dec(v___x_744_);
lean_dec_ref(v_bs_x27_737_);
lean_dec(v___x_723_);
lean_dec_ref(v_preDefs_720_);
v_a_832_ = lean_ctor_get(v___x_756_, 0);
v_isSharedCheck_839_ = !lean_is_exclusive(v___x_756_);
if (v_isSharedCheck_839_ == 0)
{
v___x_834_ = v___x_756_;
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_a_832_);
lean_dec(v___x_756_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v___x_837_; 
if (v_isShared_835_ == 0)
{
v___x_837_ = v___x_834_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v_a_832_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
}
}
}
}
else
{
lean_object* v_a_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_847_; 
lean_dec(v_a_749_);
lean_dec(v___x_744_);
lean_dec_ref(v_bs_x27_737_);
lean_dec(v___x_723_);
lean_dec_ref(v_preDefs_720_);
v_a_840_ = lean_ctor_get(v___x_754_, 0);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_754_);
if (v_isSharedCheck_847_ == 0)
{
v___x_842_ = v___x_754_;
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_a_840_);
lean_dec(v___x_754_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_845_; 
if (v_isShared_843_ == 0)
{
v___x_845_ = v___x_842_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_a_840_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
}
}
else
{
lean_object* v_a_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_855_; 
lean_dec(v_a_749_);
lean_dec(v___x_744_);
lean_dec_ref(v_bs_x27_737_);
lean_dec(v___x_723_);
lean_dec_ref(v_preDefs_720_);
v_a_848_ = lean_ctor_get(v___x_753_, 0);
v_isSharedCheck_855_ = !lean_is_exclusive(v___x_753_);
if (v_isSharedCheck_855_ == 0)
{
v___x_850_ = v___x_753_;
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_a_848_);
lean_dec(v___x_753_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v___x_853_; 
if (v_isShared_851_ == 0)
{
v___x_853_ = v___x_850_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v_a_848_);
v___x_853_ = v_reuseFailAlloc_854_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
return v___x_853_;
}
}
}
}
else
{
lean_object* v_a_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_863_; 
lean_dec(v___x_744_);
lean_dec_ref(v_bs_x27_737_);
lean_dec(v___x_723_);
lean_dec_ref(v_preDefs_720_);
v_a_856_ = lean_ctor_get(v___x_748_, 0);
v_isSharedCheck_863_ = !lean_is_exclusive(v___x_748_);
if (v_isSharedCheck_863_ == 0)
{
v___x_858_ = v___x_748_;
v_isShared_859_ = v_isSharedCheck_863_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_a_856_);
lean_dec(v___x_748_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_863_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v___x_861_; 
if (v_isShared_859_ == 0)
{
v___x_861_ = v___x_858_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v_a_856_);
v___x_861_ = v_reuseFailAlloc_862_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
return v___x_861_;
}
}
}
}
else
{
lean_object* v_a_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_871_; 
lean_dec(v___x_744_);
lean_dec_ref(v_bs_x27_737_);
lean_dec(v___x_723_);
lean_dec_ref(v_preDefs_720_);
v_a_864_ = lean_ctor_get(v___x_746_, 0);
v_isSharedCheck_871_ = !lean_is_exclusive(v___x_746_);
if (v_isSharedCheck_871_ == 0)
{
v___x_866_ = v___x_746_;
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_a_864_);
lean_dec(v___x_746_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v___x_869_; 
if (v_isShared_867_ == 0)
{
v___x_869_ = v___x_866_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v_a_864_);
v___x_869_ = v_reuseFailAlloc_870_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
return v___x_869_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___redArg___boxed(lean_object* v_preDefs_872_, lean_object* v_xs_873_, lean_object* v_a_874_, lean_object* v___x_875_, lean_object* v_sz_876_, lean_object* v_i_877_, lean_object* v_bs_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_){
_start:
{
uint8_t v_a_26638__boxed_884_; size_t v_sz_boxed_885_; size_t v_i_boxed_886_; lean_object* v_res_887_; 
v_a_26638__boxed_884_ = lean_unbox(v_a_874_);
v_sz_boxed_885_ = lean_unbox_usize(v_sz_876_);
lean_dec(v_sz_876_);
v_i_boxed_886_ = lean_unbox_usize(v_i_877_);
lean_dec(v_i_877_);
v_res_887_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___redArg(v_preDefs_872_, v_xs_873_, v_a_26638__boxed_884_, v___x_875_, v_sz_boxed_885_, v_i_boxed_886_, v_bs_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_);
lean_dec(v___y_882_);
lean_dec_ref(v___y_881_);
lean_dec(v___y_880_);
lean_dec_ref(v___y_879_);
lean_dec_ref(v_xs_873_);
return v_res_887_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___lam__0(lean_object* v_fixedParamPerms_888_, lean_object* v___x_889_, lean_object* v___x_890_, lean_object* v_xs_891_, lean_object* v_snd_892_, uint8_t v___x_893_, lean_object* v_ys_894_, lean_object* v_x_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_){
_start:
{
lean_object* v_perms_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; uint8_t v___x_905_; uint8_t v___x_906_; lean_object* v___x_907_; 
v_perms_901_ = lean_ctor_get(v_fixedParamPerms_888_, 1);
v___x_902_ = lean_array_get_borrowed(v___x_889_, v_perms_901_, v___x_890_);
lean_inc_ref(v_ys_894_);
lean_inc(v___x_902_);
v___x_903_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v___x_902_, v_xs_891_, v_ys_894_);
v___x_904_ = l_Lean_Expr_beta(v_snd_892_, v_ys_894_);
v___x_905_ = 0;
v___x_906_ = 1;
v___x_907_ = l_Lean_Meta_mkLambdaFVars(v___x_903_, v___x_904_, v___x_905_, v___x_893_, v___x_905_, v___x_893_, v___x_906_, v___y_896_, v___y_897_, v___y_898_, v___y_899_);
lean_dec_ref(v___x_903_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___lam__0___boxed(lean_object* v_fixedParamPerms_908_, lean_object* v___x_909_, lean_object* v___x_910_, lean_object* v_xs_911_, lean_object* v_snd_912_, lean_object* v___x_913_, lean_object* v_ys_914_, lean_object* v_x_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_){
_start:
{
uint8_t v___x_26906__boxed_921_; lean_object* v_res_922_; 
v___x_26906__boxed_921_ = lean_unbox(v___x_913_);
v_res_922_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___lam__0(v_fixedParamPerms_908_, v___x_909_, v___x_910_, v_xs_911_, v_snd_912_, v___x_26906__boxed_921_, v_ys_914_, v_x_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_);
lean_dec(v___y_919_);
lean_dec_ref(v___y_918_);
lean_dec(v___y_917_);
lean_dec_ref(v___y_916_);
lean_dec_ref(v_x_915_);
lean_dec_ref(v_xs_911_);
lean_dec(v___x_910_);
lean_dec_ref(v___x_909_);
lean_dec_ref(v_fixedParamPerms_908_);
return v_res_922_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_923_; 
v___x_923_ = l_Array_instInhabited___redArg();
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg(lean_object* v_fixedParamPerms_924_, lean_object* v_xs_925_, size_t v_sz_926_, size_t v_i_927_, lean_object* v_bs_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_){
_start:
{
uint8_t v___x_934_; 
v___x_934_ = lean_usize_dec_lt(v_i_927_, v_sz_926_);
if (v___x_934_ == 0)
{
lean_object* v___x_935_; 
lean_dec_ref(v_xs_925_);
lean_dec_ref(v_fixedParamPerms_924_);
v___x_935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_935_, 0, v_bs_928_);
return v___x_935_;
}
else
{
lean_object* v_v_936_; lean_object* v_fst_937_; lean_object* v_snd_938_; lean_object* v___x_939_; lean_object* v_bs_x27_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___f_944_; uint8_t v___x_945_; lean_object* v___x_946_; 
v_v_936_ = lean_array_uget_borrowed(v_bs_928_, v_i_927_);
v_fst_937_ = lean_ctor_get(v_v_936_, 0);
lean_inc(v_fst_937_);
v_snd_938_ = lean_ctor_get(v_v_936_, 1);
lean_inc(v_snd_938_);
v___x_939_ = lean_unsigned_to_nat(0u);
v_bs_x27_940_ = lean_array_uset(v_bs_928_, v_i_927_, v___x_939_);
v___x_941_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0);
v___x_942_ = lean_usize_to_nat(v_i_927_);
v___x_943_ = lean_box(v___x_934_);
lean_inc_ref(v_xs_925_);
lean_inc_ref(v_fixedParamPerms_924_);
v___f_944_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___lam__0___boxed), 13, 6);
lean_closure_set(v___f_944_, 0, v_fixedParamPerms_924_);
lean_closure_set(v___f_944_, 1, v___x_941_);
lean_closure_set(v___f_944_, 2, v___x_942_);
lean_closure_set(v___f_944_, 3, v_xs_925_);
lean_closure_set(v___f_944_, 4, v_snd_938_);
lean_closure_set(v___f_944_, 5, v___x_943_);
v___x_945_ = 0;
v___x_946_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg(v_fst_937_, v___f_944_, v___x_945_, v___y_929_, v___y_930_, v___y_931_, v___y_932_);
if (lean_obj_tag(v___x_946_) == 0)
{
lean_object* v_a_947_; size_t v___x_948_; size_t v___x_949_; lean_object* v___x_950_; 
v_a_947_ = lean_ctor_get(v___x_946_, 0);
lean_inc(v_a_947_);
lean_dec_ref_known(v___x_946_, 1);
v___x_948_ = ((size_t)1ULL);
v___x_949_ = lean_usize_add(v_i_927_, v___x_948_);
v___x_950_ = lean_array_uset(v_bs_x27_940_, v_i_927_, v_a_947_);
v_i_927_ = v___x_949_;
v_bs_928_ = v___x_950_;
goto _start;
}
else
{
lean_object* v_a_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_959_; 
lean_dec_ref(v_bs_x27_940_);
lean_dec_ref(v_xs_925_);
lean_dec_ref(v_fixedParamPerms_924_);
v_a_952_ = lean_ctor_get(v___x_946_, 0);
v_isSharedCheck_959_ = !lean_is_exclusive(v___x_946_);
if (v_isSharedCheck_959_ == 0)
{
v___x_954_ = v___x_946_;
v_isShared_955_ = v_isSharedCheck_959_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_a_952_);
lean_dec(v___x_946_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_959_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v___x_957_; 
if (v_isShared_955_ == 0)
{
v___x_957_ = v___x_954_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v_a_952_);
v___x_957_ = v_reuseFailAlloc_958_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
return v___x_957_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___boxed(lean_object* v_fixedParamPerms_960_, lean_object* v_xs_961_, lean_object* v_sz_962_, lean_object* v_i_963_, lean_object* v_bs_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_){
_start:
{
size_t v_sz_boxed_970_; size_t v_i_boxed_971_; lean_object* v_res_972_; 
v_sz_boxed_970_ = lean_unbox_usize(v_sz_962_);
lean_dec(v_sz_962_);
v_i_boxed_971_ = lean_unbox_usize(v_i_963_);
lean_dec(v_i_963_);
v_res_972_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg(v_fixedParamPerms_960_, v_xs_961_, v_sz_boxed_970_, v_i_boxed_971_, v_bs_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_);
lean_dec(v___y_968_);
lean_dec_ref(v___y_967_);
lean_dec(v___y_966_);
lean_dec_ref(v___y_965_);
return v_res_972_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(lean_object* v_a_973_, lean_object* v_a_974_){
_start:
{
if (lean_obj_tag(v_a_973_) == 0)
{
lean_object* v___x_975_; 
v___x_975_ = l_List_reverse___redArg(v_a_974_);
return v___x_975_;
}
else
{
lean_object* v_head_976_; lean_object* v_tail_977_; lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_986_; 
v_head_976_ = lean_ctor_get(v_a_973_, 0);
v_tail_977_ = lean_ctor_get(v_a_973_, 1);
v_isSharedCheck_986_ = !lean_is_exclusive(v_a_973_);
if (v_isSharedCheck_986_ == 0)
{
v___x_979_ = v_a_973_;
v_isShared_980_ = v_isSharedCheck_986_;
goto v_resetjp_978_;
}
else
{
lean_inc(v_tail_977_);
lean_inc(v_head_976_);
lean_dec(v_a_973_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_986_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v___x_981_; lean_object* v___x_983_; 
v___x_981_ = l_Lean_MessageData_ofExpr(v_head_976_);
if (v_isShared_980_ == 0)
{
lean_ctor_set(v___x_979_, 1, v_a_974_);
lean_ctor_set(v___x_979_, 0, v___x_981_);
v___x_983_ = v___x_979_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v___x_981_);
lean_ctor_set(v_reuseFailAlloc_985_, 1, v_a_974_);
v___x_983_ = v_reuseFailAlloc_985_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
v_a_973_ = v_tail_977_;
v_a_974_ = v___x_983_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__15(lean_object* v_a_987_, lean_object* v_a_988_){
_start:
{
if (lean_obj_tag(v_a_987_) == 0)
{
lean_object* v___x_989_; 
v___x_989_ = l_List_reverse___redArg(v_a_988_);
return v___x_989_;
}
else
{
lean_object* v_head_990_; lean_object* v_tail_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_1000_; 
v_head_990_ = lean_ctor_get(v_a_987_, 0);
v_tail_991_ = lean_ctor_get(v_a_987_, 1);
v_isSharedCheck_1000_ = !lean_is_exclusive(v_a_987_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_993_ = v_a_987_;
v_isShared_994_ = v_isSharedCheck_1000_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_tail_991_);
lean_inc(v_head_990_);
lean_dec(v_a_987_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_1000_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_995_; lean_object* v___x_997_; 
v___x_995_ = l_Lean_mkLevelParam(v_head_990_);
if (v_isShared_994_ == 0)
{
lean_ctor_set(v___x_993_, 1, v_a_988_);
lean_ctor_set(v___x_993_, 0, v___x_995_);
v___x_997_ = v___x_993_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v___x_995_);
lean_ctor_set(v_reuseFailAlloc_999_, 1, v_a_988_);
v___x_997_ = v_reuseFailAlloc_999_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
v_a_987_ = v_tail_991_;
v_a_988_ = v___x_997_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__0(void){
_start:
{
lean_object* v___x_1001_; 
v___x_1001_ = l_instMonadEIO___redArg();
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg(lean_object* v_msg_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_){
_start:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v_toApplicative_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1075_; 
v___x_1012_ = lean_obj_once(&l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__0, &l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__0_once, _init_l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__0);
v___x_1013_ = l_StateRefT_x27_instMonad___redArg(v___x_1012_);
v_toApplicative_1014_ = lean_ctor_get(v___x_1013_, 0);
v_isSharedCheck_1075_ = !lean_is_exclusive(v___x_1013_);
if (v_isSharedCheck_1075_ == 0)
{
lean_object* v_unused_1076_; 
v_unused_1076_ = lean_ctor_get(v___x_1013_, 1);
lean_dec(v_unused_1076_);
v___x_1016_ = v___x_1013_;
v_isShared_1017_ = v_isSharedCheck_1075_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_toApplicative_1014_);
lean_dec(v___x_1013_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1075_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v_toFunctor_1018_; lean_object* v_toSeq_1019_; lean_object* v_toSeqLeft_1020_; lean_object* v_toSeqRight_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1073_; 
v_toFunctor_1018_ = lean_ctor_get(v_toApplicative_1014_, 0);
v_toSeq_1019_ = lean_ctor_get(v_toApplicative_1014_, 2);
v_toSeqLeft_1020_ = lean_ctor_get(v_toApplicative_1014_, 3);
v_toSeqRight_1021_ = lean_ctor_get(v_toApplicative_1014_, 4);
v_isSharedCheck_1073_ = !lean_is_exclusive(v_toApplicative_1014_);
if (v_isSharedCheck_1073_ == 0)
{
lean_object* v_unused_1074_; 
v_unused_1074_ = lean_ctor_get(v_toApplicative_1014_, 1);
lean_dec(v_unused_1074_);
v___x_1023_ = v_toApplicative_1014_;
v_isShared_1024_ = v_isSharedCheck_1073_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_toSeqRight_1021_);
lean_inc(v_toSeqLeft_1020_);
lean_inc(v_toSeq_1019_);
lean_inc(v_toFunctor_1018_);
lean_dec(v_toApplicative_1014_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1073_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v___f_1025_; lean_object* v___f_1026_; lean_object* v___f_1027_; lean_object* v___f_1028_; lean_object* v___x_1029_; lean_object* v___f_1030_; lean_object* v___f_1031_; lean_object* v___f_1032_; lean_object* v___x_1034_; 
v___f_1025_ = ((lean_object*)(l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__1));
v___f_1026_ = ((lean_object*)(l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__2));
lean_inc_ref(v_toFunctor_1018_);
v___f_1027_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1027_, 0, v_toFunctor_1018_);
v___f_1028_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1028_, 0, v_toFunctor_1018_);
v___x_1029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1029_, 0, v___f_1027_);
lean_ctor_set(v___x_1029_, 1, v___f_1028_);
v___f_1030_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1030_, 0, v_toSeqRight_1021_);
v___f_1031_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1031_, 0, v_toSeqLeft_1020_);
v___f_1032_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1032_, 0, v_toSeq_1019_);
if (v_isShared_1024_ == 0)
{
lean_ctor_set(v___x_1023_, 4, v___f_1030_);
lean_ctor_set(v___x_1023_, 3, v___f_1031_);
lean_ctor_set(v___x_1023_, 2, v___f_1032_);
lean_ctor_set(v___x_1023_, 1, v___f_1025_);
lean_ctor_set(v___x_1023_, 0, v___x_1029_);
v___x_1034_ = v___x_1023_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v___x_1029_);
lean_ctor_set(v_reuseFailAlloc_1072_, 1, v___f_1025_);
lean_ctor_set(v_reuseFailAlloc_1072_, 2, v___f_1032_);
lean_ctor_set(v_reuseFailAlloc_1072_, 3, v___f_1031_);
lean_ctor_set(v_reuseFailAlloc_1072_, 4, v___f_1030_);
v___x_1034_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
lean_object* v___x_1036_; 
if (v_isShared_1017_ == 0)
{
lean_ctor_set(v___x_1016_, 1, v___f_1026_);
lean_ctor_set(v___x_1016_, 0, v___x_1034_);
v___x_1036_ = v___x_1016_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v___x_1034_);
lean_ctor_set(v_reuseFailAlloc_1071_, 1, v___f_1026_);
v___x_1036_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
lean_object* v___x_1037_; lean_object* v_toApplicative_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1069_; 
v___x_1037_ = l_StateRefT_x27_instMonad___redArg(v___x_1036_);
v_toApplicative_1038_ = lean_ctor_get(v___x_1037_, 0);
v_isSharedCheck_1069_ = !lean_is_exclusive(v___x_1037_);
if (v_isSharedCheck_1069_ == 0)
{
lean_object* v_unused_1070_; 
v_unused_1070_ = lean_ctor_get(v___x_1037_, 1);
lean_dec(v_unused_1070_);
v___x_1040_ = v___x_1037_;
v_isShared_1041_ = v_isSharedCheck_1069_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_toApplicative_1038_);
lean_dec(v___x_1037_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1069_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v_toFunctor_1042_; lean_object* v_toSeq_1043_; lean_object* v_toSeqLeft_1044_; lean_object* v_toSeqRight_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1067_; 
v_toFunctor_1042_ = lean_ctor_get(v_toApplicative_1038_, 0);
v_toSeq_1043_ = lean_ctor_get(v_toApplicative_1038_, 2);
v_toSeqLeft_1044_ = lean_ctor_get(v_toApplicative_1038_, 3);
v_toSeqRight_1045_ = lean_ctor_get(v_toApplicative_1038_, 4);
v_isSharedCheck_1067_ = !lean_is_exclusive(v_toApplicative_1038_);
if (v_isSharedCheck_1067_ == 0)
{
lean_object* v_unused_1068_; 
v_unused_1068_ = lean_ctor_get(v_toApplicative_1038_, 1);
lean_dec(v_unused_1068_);
v___x_1047_ = v_toApplicative_1038_;
v_isShared_1048_ = v_isSharedCheck_1067_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_toSeqRight_1045_);
lean_inc(v_toSeqLeft_1044_);
lean_inc(v_toSeq_1043_);
lean_inc(v_toFunctor_1042_);
lean_dec(v_toApplicative_1038_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1067_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___f_1049_; lean_object* v___f_1050_; lean_object* v___f_1051_; lean_object* v___f_1052_; lean_object* v___x_1053_; lean_object* v___f_1054_; lean_object* v___f_1055_; lean_object* v___f_1056_; lean_object* v___x_1058_; 
v___f_1049_ = ((lean_object*)(l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__3));
v___f_1050_ = ((lean_object*)(l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__4));
lean_inc_ref(v_toFunctor_1042_);
v___f_1051_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1051_, 0, v_toFunctor_1042_);
v___f_1052_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1052_, 0, v_toFunctor_1042_);
v___x_1053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1053_, 0, v___f_1051_);
lean_ctor_set(v___x_1053_, 1, v___f_1052_);
v___f_1054_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1054_, 0, v_toSeqRight_1045_);
v___f_1055_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1055_, 0, v_toSeqLeft_1044_);
v___f_1056_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1056_, 0, v_toSeq_1043_);
if (v_isShared_1048_ == 0)
{
lean_ctor_set(v___x_1047_, 4, v___f_1054_);
lean_ctor_set(v___x_1047_, 3, v___f_1055_);
lean_ctor_set(v___x_1047_, 2, v___f_1056_);
lean_ctor_set(v___x_1047_, 1, v___f_1049_);
lean_ctor_set(v___x_1047_, 0, v___x_1053_);
v___x_1058_ = v___x_1047_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v___x_1053_);
lean_ctor_set(v_reuseFailAlloc_1066_, 1, v___f_1049_);
lean_ctor_set(v_reuseFailAlloc_1066_, 2, v___f_1056_);
lean_ctor_set(v_reuseFailAlloc_1066_, 3, v___f_1055_);
lean_ctor_set(v_reuseFailAlloc_1066_, 4, v___f_1054_);
v___x_1058_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
lean_object* v___x_1060_; 
if (v_isShared_1041_ == 0)
{
lean_ctor_set(v___x_1040_, 1, v___f_1050_);
lean_ctor_set(v___x_1040_, 0, v___x_1058_);
v___x_1060_ = v___x_1040_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v___x_1058_);
lean_ctor_set(v_reuseFailAlloc_1065_, 1, v___f_1050_);
v___x_1060_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_22378__overap_1063_; lean_object* v___x_1064_; 
v___x_1061_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0);
v___x_1062_ = l_instInhabitedOfMonad___redArg(v___x_1060_, v___x_1061_);
v___x_22378__overap_1063_ = lean_panic_fn_borrowed(v___x_1062_, v_msg_1006_);
lean_dec(v___x_1062_);
lean_inc(v___y_1010_);
lean_inc_ref(v___y_1009_);
lean_inc(v___y_1008_);
lean_inc_ref(v___y_1007_);
v___x_1064_ = lean_apply_5(v___x_22378__overap_1063_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_, lean_box(0));
return v___x_1064_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___boxed(lean_object* v_msg_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_){
_start:
{
lean_object* v_res_1083_; 
v_res_1083_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg(v_msg_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_);
lean_dec(v___y_1081_);
lean_dec_ref(v___y_1080_);
lean_dec(v___y_1079_);
lean_dec_ref(v___y_1078_);
return v_res_1083_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__13(lean_object* v_xs_1084_, size_t v_sz_1085_, size_t v_i_1086_, lean_object* v_bs_1087_){
_start:
{
uint8_t v___x_1088_; 
v___x_1088_ = lean_usize_dec_lt(v_i_1086_, v_sz_1085_);
if (v___x_1088_ == 0)
{
return v_bs_1087_;
}
else
{
lean_object* v___x_1089_; lean_object* v_v_1090_; lean_object* v___x_1091_; lean_object* v_bs_x27_1092_; lean_object* v___x_1093_; size_t v___x_1094_; size_t v___x_1095_; lean_object* v___x_1096_; 
v___x_1089_ = l_Lean_instInhabitedExpr;
v_v_1090_ = lean_array_uget(v_bs_1087_, v_i_1086_);
v___x_1091_ = lean_unsigned_to_nat(0u);
v_bs_x27_1092_ = lean_array_uset(v_bs_1087_, v_i_1086_, v___x_1091_);
v___x_1093_ = lean_array_get_borrowed(v___x_1089_, v_xs_1084_, v_v_1090_);
lean_dec(v_v_1090_);
v___x_1094_ = ((size_t)1ULL);
v___x_1095_ = lean_usize_add(v_i_1086_, v___x_1094_);
lean_inc(v___x_1093_);
v___x_1096_ = lean_array_uset(v_bs_x27_1092_, v_i_1086_, v___x_1093_);
v_i_1086_ = v___x_1095_;
v_bs_1087_ = v___x_1096_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__13___boxed(lean_object* v_xs_1098_, lean_object* v_sz_1099_, lean_object* v_i_1100_, lean_object* v_bs_1101_){
_start:
{
size_t v_sz_boxed_1102_; size_t v_i_boxed_1103_; lean_object* v_res_1104_; 
v_sz_boxed_1102_ = lean_unbox_usize(v_sz_1099_);
lean_dec(v_sz_1099_);
v_i_boxed_1103_ = lean_unbox_usize(v_i_1100_);
lean_dec(v_i_1100_);
v_res_1104_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__13(v_xs_1098_, v_sz_boxed_1102_, v_i_boxed_1103_, v_bs_1101_);
lean_dec_ref(v_xs_1098_);
return v_res_1104_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15___redArg(lean_object* v_xs_1105_, lean_object* v_f_1106_, lean_object* v_as_1107_, lean_object* v_bs_1108_, lean_object* v_i_1109_, lean_object* v_cs_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_){
_start:
{
lean_object* v___x_1116_; uint8_t v___x_1117_; 
v___x_1116_ = lean_array_get_size(v_as_1107_);
v___x_1117_ = lean_nat_dec_lt(v_i_1109_, v___x_1116_);
if (v___x_1117_ == 0)
{
lean_object* v___x_1118_; 
lean_dec(v_i_1109_);
lean_dec_ref(v_f_1106_);
v___x_1118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1118_, 0, v_cs_1110_);
return v___x_1118_;
}
else
{
lean_object* v___x_1119_; uint8_t v___x_1120_; 
v___x_1119_ = lean_array_get_size(v_bs_1108_);
v___x_1120_ = lean_nat_dec_lt(v_i_1109_, v___x_1119_);
if (v___x_1120_ == 0)
{
lean_object* v___x_1121_; 
lean_dec(v_i_1109_);
lean_dec_ref(v_f_1106_);
v___x_1121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1121_, 0, v_cs_1110_);
return v___x_1121_;
}
else
{
lean_object* v_a_1122_; lean_object* v_b_1123_; size_t v_sz_1124_; size_t v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; 
v_a_1122_ = lean_array_fget_borrowed(v_as_1107_, v_i_1109_);
v_b_1123_ = lean_array_fget_borrowed(v_bs_1108_, v_i_1109_);
v_sz_1124_ = lean_array_size(v_b_1123_);
v___x_1125_ = ((size_t)0ULL);
lean_inc(v_b_1123_);
v___x_1126_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__13(v_xs_1105_, v_sz_1124_, v___x_1125_, v_b_1123_);
lean_inc_ref(v_f_1106_);
lean_inc(v___y_1114_);
lean_inc_ref(v___y_1113_);
lean_inc(v___y_1112_);
lean_inc_ref(v___y_1111_);
lean_inc(v_a_1122_);
v___x_1127_ = lean_apply_7(v_f_1106_, v_a_1122_, v___x_1126_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, lean_box(0));
if (lean_obj_tag(v___x_1127_) == 0)
{
lean_object* v_a_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; 
v_a_1128_ = lean_ctor_get(v___x_1127_, 0);
lean_inc(v_a_1128_);
lean_dec_ref_known(v___x_1127_, 1);
v___x_1129_ = lean_unsigned_to_nat(1u);
v___x_1130_ = lean_nat_add(v_i_1109_, v___x_1129_);
lean_dec(v_i_1109_);
v___x_1131_ = lean_array_push(v_cs_1110_, v_a_1128_);
v_i_1109_ = v___x_1130_;
v_cs_1110_ = v___x_1131_;
goto _start;
}
else
{
lean_object* v_a_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1140_; 
lean_dec_ref(v_cs_1110_);
lean_dec(v_i_1109_);
lean_dec_ref(v_f_1106_);
v_a_1133_ = lean_ctor_get(v___x_1127_, 0);
v_isSharedCheck_1140_ = !lean_is_exclusive(v___x_1127_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1135_ = v___x_1127_;
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_a_1133_);
lean_dec(v___x_1127_);
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
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15___redArg___boxed(lean_object* v_xs_1141_, lean_object* v_f_1142_, lean_object* v_as_1143_, lean_object* v_bs_1144_, lean_object* v_i_1145_, lean_object* v_cs_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_){
_start:
{
lean_object* v_res_1152_; 
v_res_1152_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15___redArg(v_xs_1141_, v_f_1142_, v_as_1143_, v_bs_1144_, v_i_1145_, v_cs_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_);
lean_dec(v___y_1150_);
lean_dec_ref(v___y_1149_);
lean_dec(v___y_1148_);
lean_dec_ref(v___y_1147_);
lean_dec_ref(v_bs_1144_);
lean_dec_ref(v_as_1143_);
lean_dec_ref(v_xs_1141_);
return v_res_1152_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; 
v___x_1156_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__2));
v___x_1157_ = lean_unsigned_to_nat(2u);
v___x_1158_ = lean_unsigned_to_nat(73u);
v___x_1159_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__1));
v___x_1160_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__0));
v___x_1161_ = l_mkPanicMessageWithDecl(v___x_1160_, v___x_1159_, v___x_1158_, v___x_1157_, v___x_1156_);
return v___x_1161_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; 
v___x_1163_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__4));
v___x_1164_ = lean_unsigned_to_nat(2u);
v___x_1165_ = lean_unsigned_to_nat(74u);
v___x_1166_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__1));
v___x_1167_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__0));
v___x_1168_ = l_mkPanicMessageWithDecl(v___x_1167_, v___x_1166_, v___x_1165_, v___x_1164_, v___x_1163_);
return v___x_1168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg(lean_object* v_f_1171_, lean_object* v_positions_1172_, lean_object* v_ys_1173_, lean_object* v_xs_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_){
_start:
{
lean_object* v___x_1180_; lean_object* v___x_1181_; uint8_t v___x_1182_; 
v___x_1180_ = lean_array_get_size(v_positions_1172_);
v___x_1181_ = lean_array_get_size(v_ys_1173_);
v___x_1182_ = lean_nat_dec_eq(v___x_1180_, v___x_1181_);
if (v___x_1182_ == 0)
{
lean_object* v___x_1183_; lean_object* v___x_1184_; 
lean_dec_ref(v_f_1171_);
v___x_1183_ = lean_obj_once(&l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__3, &l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__3_once, _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__3);
v___x_1184_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg(v___x_1183_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_);
return v___x_1184_;
}
else
{
lean_object* v___x_1185_; lean_object* v___x_1186_; uint8_t v___x_1187_; 
v___x_1185_ = l_Lean_Elab_Structural_Positions_numIndices(v_positions_1172_);
v___x_1186_ = lean_array_get_size(v_xs_1174_);
v___x_1187_ = lean_nat_dec_eq(v___x_1185_, v___x_1186_);
lean_dec(v___x_1185_);
if (v___x_1187_ == 0)
{
lean_object* v___x_1188_; lean_object* v___x_1189_; 
lean_dec_ref(v_f_1171_);
v___x_1188_ = lean_obj_once(&l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__5, &l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__5_once, _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__5);
v___x_1189_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg(v___x_1188_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_);
return v___x_1189_;
}
else
{
lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; 
v___x_1190_ = lean_unsigned_to_nat(0u);
v___x_1191_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__6));
v___x_1192_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15___redArg(v_xs_1174_, v_f_1171_, v_ys_1173_, v_positions_1172_, v___x_1190_, v___x_1191_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_);
return v___x_1192_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___boxed(lean_object* v_f_1193_, lean_object* v_positions_1194_, lean_object* v_ys_1195_, lean_object* v_xs_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_){
_start:
{
lean_object* v_res_1202_; 
v_res_1202_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg(v_f_1193_, v_positions_1194_, v_ys_1195_, v_xs_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_);
lean_dec(v___y_1200_);
lean_dec_ref(v___y_1199_);
lean_dec(v___y_1198_);
lean_dec_ref(v___y_1197_);
lean_dec_ref(v_xs_1196_);
lean_dec_ref(v_ys_1195_);
lean_dec_ref(v_positions_1194_);
return v_res_1202_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg(lean_object* v___x_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_funTypes_1206_, size_t v_sz_1207_, size_t v_i_1208_, lean_object* v_bs_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_){
_start:
{
uint8_t v___x_1215_; 
v___x_1215_ = lean_usize_dec_lt(v_i_1208_, v_sz_1207_);
if (v___x_1215_ == 0)
{
lean_object* v___x_1216_; 
lean_dec_ref(v_funTypes_1206_);
lean_dec_ref(v_a_1205_);
lean_dec_ref(v_a_1204_);
lean_dec_ref(v___x_1203_);
v___x_1216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1216_, 0, v_bs_1209_);
return v___x_1216_;
}
else
{
lean_object* v_v_1217_; lean_object* v_fst_1218_; lean_object* v_snd_1219_; lean_object* v___x_1220_; lean_object* v_bs_x27_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; 
v_v_1217_ = lean_array_uget_borrowed(v_bs_1209_, v_i_1208_);
v_fst_1218_ = lean_ctor_get(v_v_1217_, 0);
lean_inc(v_fst_1218_);
v_snd_1219_ = lean_ctor_get(v_v_1217_, 1);
lean_inc(v_snd_1219_);
v___x_1220_ = lean_unsigned_to_nat(0u);
v_bs_x27_1221_ = lean_array_uset(v_bs_1209_, v_i_1208_, v___x_1220_);
v___x_1222_ = lean_usize_to_nat(v_i_1208_);
lean_inc_ref(v_funTypes_1206_);
lean_inc_ref(v_a_1205_);
lean_inc_ref(v_a_1204_);
lean_inc_ref(v___x_1203_);
v___x_1223_ = l_Lean_Elab_Structural_mkBRecOnApp(v___x_1203_, v___x_1222_, v_a_1204_, v_a_1205_, v_funTypes_1206_, v_fst_1218_, v_snd_1219_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_);
if (lean_obj_tag(v___x_1223_) == 0)
{
lean_object* v_a_1224_; size_t v___x_1225_; size_t v___x_1226_; lean_object* v___x_1227_; 
v_a_1224_ = lean_ctor_get(v___x_1223_, 0);
lean_inc(v_a_1224_);
lean_dec_ref_known(v___x_1223_, 1);
v___x_1225_ = ((size_t)1ULL);
v___x_1226_ = lean_usize_add(v_i_1208_, v___x_1225_);
v___x_1227_ = lean_array_uset(v_bs_x27_1221_, v_i_1208_, v_a_1224_);
v_i_1208_ = v___x_1226_;
v_bs_1209_ = v___x_1227_;
goto _start;
}
else
{
lean_object* v_a_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1236_; 
lean_dec_ref(v_bs_x27_1221_);
lean_dec_ref(v_funTypes_1206_);
lean_dec_ref(v_a_1205_);
lean_dec_ref(v_a_1204_);
lean_dec_ref(v___x_1203_);
v_a_1229_ = lean_ctor_get(v___x_1223_, 0);
v_isSharedCheck_1236_ = !lean_is_exclusive(v___x_1223_);
if (v_isSharedCheck_1236_ == 0)
{
v___x_1231_ = v___x_1223_;
v_isShared_1232_ = v_isSharedCheck_1236_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_a_1229_);
lean_dec(v___x_1223_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1236_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v___x_1234_; 
if (v_isShared_1232_ == 0)
{
v___x_1234_ = v___x_1231_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v_a_1229_);
v___x_1234_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
return v___x_1234_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg___boxed(lean_object* v___x_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_funTypes_1240_, lean_object* v_sz_1241_, lean_object* v_i_1242_, lean_object* v_bs_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_){
_start:
{
size_t v_sz_boxed_1249_; size_t v_i_boxed_1250_; lean_object* v_res_1251_; 
v_sz_boxed_1249_ = lean_unbox_usize(v_sz_1241_);
lean_dec(v_sz_1241_);
v_i_boxed_1250_ = lean_unbox_usize(v_i_1242_);
lean_dec(v_i_1242_);
v_res_1251_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg(v___x_1237_, v_a_1238_, v_a_1239_, v_funTypes_1240_, v_sz_boxed_1249_, v_i_boxed_1250_, v_bs_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_);
lean_dec(v___y_1247_);
lean_dec_ref(v___y_1246_);
lean_dec(v___y_1245_);
lean_dec_ref(v___y_1244_);
return v_res_1251_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__2(void){
_start:
{
lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; 
v___x_1255_ = lean_box(0);
v___x_1256_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__1));
v___x_1257_ = l_Lean_Expr_const___override(v___x_1256_, v___x_1255_);
return v___x_1257_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__4(void){
_start:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; 
v___x_1259_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__3));
v___x_1260_ = l_Lean_stringToMessageData(v___x_1259_);
return v___x_1260_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__6(void){
_start:
{
lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___x_1262_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__5));
v___x_1263_ = l_Lean_stringToMessageData(v___x_1262_);
return v___x_1263_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__8(void){
_start:
{
lean_object* v___x_1265_; lean_object* v___x_1266_; 
v___x_1265_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__7));
v___x_1266_ = l_Lean_stringToMessageData(v___x_1265_);
return v___x_1266_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__10(void){
_start:
{
lean_object* v___x_1268_; lean_object* v___x_1269_; 
v___x_1268_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__9));
v___x_1269_ = l_Lean_stringToMessageData(v___x_1268_);
return v___x_1269_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__12(void){
_start:
{
lean_object* v___x_1271_; lean_object* v___x_1272_; 
v___x_1271_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__11));
v___x_1272_ = l_Lean_stringToMessageData(v___x_1271_);
return v___x_1272_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2(lean_object* v_recArgInfos_1273_, lean_object* v_a_1274_, lean_object* v___x_1275_, size_t v___x_1276_, lean_object* v_fixedParamPerms_1277_, lean_object* v_xs_1278_, lean_object* v___x_1279_, lean_object* v_preDefs_1280_, lean_object* v_numIndices_1281_, lean_object* v___f_1282_, lean_object* v___x_1283_, uint8_t v_a_1284_, lean_object* v___x_1285_, lean_object* v___f_1286_, lean_object* v_funTypes_1287_, lean_object* v_motives_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_){
_start:
{
lean_object* v___y_1295_; lean_object* v___y_1296_; lean_object* v___y_1297_; lean_object* v___y_1298_; lean_object* v___y_1299_; lean_object* v___y_1300_; lean_object* v___y_1335_; lean_object* v_FArgs_1336_; lean_object* v___y_1337_; lean_object* v___y_1338_; lean_object* v___y_1339_; lean_object* v___y_1340_; lean_object* v___y_1392_; lean_object* v___y_1393_; lean_object* v___y_1394_; lean_object* v___y_1395_; lean_object* v___y_1396_; lean_object* v___y_1397_; lean_object* v___y_1414_; lean_object* v___y_1415_; lean_object* v___y_1416_; lean_object* v___y_1417_; lean_object* v___y_1418_; lean_object* v___y_1419_; lean_object* v___x_1504_; 
lean_inc_ref(v___f_1286_);
lean_inc(v___y_1292_);
lean_inc_ref(v___y_1291_);
lean_inc(v___y_1290_);
lean_inc_ref(v___y_1289_);
v___x_1504_ = lean_apply_5(v___f_1286_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, lean_box(0));
if (lean_obj_tag(v___x_1504_) == 0)
{
lean_object* v_a_1505_; uint8_t v___x_1506_; 
v_a_1505_ = lean_ctor_get(v___x_1504_, 0);
lean_inc(v_a_1505_);
lean_dec_ref_known(v___x_1504_, 1);
v___x_1506_ = lean_unbox(v_a_1505_);
lean_dec(v_a_1505_);
if (v___x_1506_ == 0)
{
goto v___jp_1457_;
}
else
{
lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; 
v___x_1507_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__10, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__10);
lean_inc_ref(v_funTypes_1287_);
v___x_1508_ = lean_array_to_list(v_funTypes_1287_);
v___x_1509_ = lean_box(0);
v___x_1510_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_1508_, v___x_1509_);
v___x_1511_ = l_Lean_MessageData_ofList(v___x_1510_);
v___x_1512_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1512_, 0, v___x_1507_);
lean_ctor_set(v___x_1512_, 1, v___x_1511_);
v___x_1513_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__12, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__12_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__12);
v___x_1514_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1514_, 0, v___x_1512_);
lean_ctor_set(v___x_1514_, 1, v___x_1513_);
lean_inc_ref(v_motives_1288_);
v___x_1515_ = lean_array_to_list(v_motives_1288_);
v___x_1516_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_1515_, v___x_1509_);
v___x_1517_ = l_Lean_MessageData_ofList(v___x_1516_);
v___x_1518_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1518_, 0, v___x_1514_);
lean_ctor_set(v___x_1518_, 1, v___x_1517_);
lean_inc(v___x_1283_);
v___x_1519_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_1283_, v___x_1518_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_);
if (lean_obj_tag(v___x_1519_) == 0)
{
lean_dec_ref_known(v___x_1519_, 1);
goto v___jp_1457_;
}
else
{
lean_object* v_a_1520_; lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1527_; 
lean_dec_ref(v_motives_1288_);
lean_dec_ref(v_funTypes_1287_);
lean_dec_ref(v___f_1286_);
lean_dec(v___x_1283_);
lean_dec_ref(v___f_1282_);
lean_dec_ref(v_preDefs_1280_);
lean_dec(v___x_1279_);
lean_dec_ref(v_xs_1278_);
lean_dec_ref(v_fixedParamPerms_1277_);
lean_dec_ref(v___x_1275_);
lean_dec_ref(v_recArgInfos_1273_);
v_a_1520_ = lean_ctor_get(v___x_1519_, 0);
v_isSharedCheck_1527_ = !lean_is_exclusive(v___x_1519_);
if (v_isSharedCheck_1527_ == 0)
{
v___x_1522_ = v___x_1519_;
v_isShared_1523_ = v_isSharedCheck_1527_;
goto v_resetjp_1521_;
}
else
{
lean_inc(v_a_1520_);
lean_dec(v___x_1519_);
v___x_1522_ = lean_box(0);
v_isShared_1523_ = v_isSharedCheck_1527_;
goto v_resetjp_1521_;
}
v_resetjp_1521_:
{
lean_object* v___x_1525_; 
if (v_isShared_1523_ == 0)
{
v___x_1525_ = v___x_1522_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v_a_1520_);
v___x_1525_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
return v___x_1525_;
}
}
}
}
}
else
{
lean_object* v_a_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1535_; 
lean_dec_ref(v_motives_1288_);
lean_dec_ref(v_funTypes_1287_);
lean_dec_ref(v___f_1286_);
lean_dec(v___x_1283_);
lean_dec_ref(v___f_1282_);
lean_dec_ref(v_preDefs_1280_);
lean_dec(v___x_1279_);
lean_dec_ref(v_xs_1278_);
lean_dec_ref(v_fixedParamPerms_1277_);
lean_dec_ref(v___x_1275_);
lean_dec_ref(v_recArgInfos_1273_);
v_a_1528_ = lean_ctor_get(v___x_1504_, 0);
v_isSharedCheck_1535_ = !lean_is_exclusive(v___x_1504_);
if (v_isSharedCheck_1535_ == 0)
{
v___x_1530_ = v___x_1504_;
v_isShared_1531_ = v_isSharedCheck_1535_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_a_1528_);
lean_dec(v___x_1504_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1535_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
lean_object* v___x_1533_; 
if (v_isShared_1531_ == 0)
{
v___x_1533_ = v___x_1530_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v_a_1528_);
v___x_1533_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
return v___x_1533_;
}
}
}
v___jp_1294_:
{
lean_object* v___x_1301_; size_t v_sz_1302_; lean_object* v___x_1303_; 
v___x_1301_ = l_Array_zip___redArg(v_recArgInfos_1273_, v_a_1274_);
lean_dec_ref(v_recArgInfos_1273_);
v_sz_1302_ = lean_array_size(v___x_1301_);
v___x_1303_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg(v___x_1275_, v___y_1295_, v___y_1296_, v_funTypes_1287_, v_sz_1302_, v___x_1276_, v___x_1301_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_);
if (lean_obj_tag(v___x_1303_) == 0)
{
lean_object* v_a_1304_; lean_object* v___x_1305_; size_t v_sz_1306_; lean_object* v___x_1307_; 
v_a_1304_ = lean_ctor_get(v___x_1303_, 0);
lean_inc(v_a_1304_);
lean_dec_ref_known(v___x_1303_, 1);
v___x_1305_ = l_Array_zip___redArg(v_a_1274_, v_a_1304_);
lean_dec(v_a_1304_);
v_sz_1306_ = lean_array_size(v___x_1305_);
v___x_1307_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg(v_fixedParamPerms_1277_, v_xs_1278_, v_sz_1306_, v___x_1276_, v___x_1305_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_);
if (lean_obj_tag(v___x_1307_) == 0)
{
lean_object* v_a_1308_; lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1317_; 
v_a_1308_ = lean_ctor_get(v___x_1307_, 0);
v_isSharedCheck_1317_ = !lean_is_exclusive(v___x_1307_);
if (v_isSharedCheck_1317_ == 0)
{
v___x_1310_ = v___x_1307_;
v_isShared_1311_ = v_isSharedCheck_1317_;
goto v_resetjp_1309_;
}
else
{
lean_inc(v_a_1308_);
lean_dec(v___x_1307_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1317_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1315_; 
v___x_1312_ = lean_mk_empty_array_with_capacity(v___x_1279_);
v___x_1313_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9(v_preDefs_1280_, v_a_1308_, v___x_1279_, v___x_1312_);
lean_dec(v_a_1308_);
lean_dec_ref(v_preDefs_1280_);
if (v_isShared_1311_ == 0)
{
lean_ctor_set(v___x_1310_, 0, v___x_1313_);
v___x_1315_ = v___x_1310_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v___x_1313_);
v___x_1315_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
return v___x_1315_;
}
}
}
else
{
lean_object* v_a_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1325_; 
lean_dec_ref(v_preDefs_1280_);
lean_dec(v___x_1279_);
v_a_1318_ = lean_ctor_get(v___x_1307_, 0);
v_isSharedCheck_1325_ = !lean_is_exclusive(v___x_1307_);
if (v_isSharedCheck_1325_ == 0)
{
v___x_1320_ = v___x_1307_;
v_isShared_1321_ = v_isSharedCheck_1325_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_a_1318_);
lean_dec(v___x_1307_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1325_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
lean_object* v___x_1323_; 
if (v_isShared_1321_ == 0)
{
v___x_1323_ = v___x_1320_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v_a_1318_);
v___x_1323_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
return v___x_1323_;
}
}
}
}
else
{
lean_object* v_a_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1333_; 
lean_dec_ref(v_preDefs_1280_);
lean_dec(v___x_1279_);
lean_dec_ref(v_xs_1278_);
lean_dec_ref(v_fixedParamPerms_1277_);
v_a_1326_ = lean_ctor_get(v___x_1303_, 0);
v_isSharedCheck_1333_ = !lean_is_exclusive(v___x_1303_);
if (v_isSharedCheck_1333_ == 0)
{
v___x_1328_ = v___x_1303_;
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_a_1326_);
lean_dec(v___x_1303_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v___x_1331_; 
if (v_isShared_1329_ == 0)
{
v___x_1331_ = v___x_1328_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v_a_1326_);
v___x_1331_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
return v___x_1331_;
}
}
}
}
v___jp_1334_:
{
lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; 
lean_inc_ref(v___y_1335_);
lean_inc(v___x_1279_);
v___x_1341_ = lean_apply_1(v___y_1335_, v___x_1279_);
v___x_1342_ = lean_unsigned_to_nat(1u);
v___x_1343_ = lean_nat_add(v_numIndices_1281_, v___x_1342_);
v___x_1344_ = lean_box(0);
v___x_1345_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__2);
v___x_1346_ = lean_mk_array(v___x_1343_, v___x_1345_);
v___x_1347_ = l_Lean_mkAppN(v___x_1341_, v___x_1346_);
lean_dec_ref(v___x_1346_);
v___x_1348_ = lean_array_get_size(v___x_1275_);
v___x_1349_ = l_Lean_Meta_inferArgumentTypesN(v___x_1348_, v___x_1347_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_);
if (lean_obj_tag(v___x_1349_) == 0)
{
lean_object* v_a_1350_; lean_object* v___x_1351_; 
v_a_1350_ = lean_ctor_get(v___x_1349_, 0);
lean_inc(v_a_1350_);
lean_dec_ref_known(v___x_1349_, 1);
v___x_1351_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg(v___f_1282_, v___x_1275_, v_a_1350_, v_FArgs_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_);
lean_dec_ref(v_FArgs_1336_);
lean_dec(v_a_1350_);
if (lean_obj_tag(v___x_1351_) == 0)
{
lean_object* v_toCold_1352_; lean_object* v_options_1353_; uint8_t v_hasTrace_1354_; 
v_toCold_1352_ = lean_ctor_get(v___y_1339_, 0);
v_options_1353_ = lean_ctor_get(v_toCold_1352_, 2);
v_hasTrace_1354_ = lean_ctor_get_uint8(v_options_1353_, sizeof(void*)*1);
if (v_hasTrace_1354_ == 0)
{
lean_object* v_a_1355_; 
lean_dec(v___x_1283_);
v_a_1355_ = lean_ctor_get(v___x_1351_, 0);
lean_inc(v_a_1355_);
lean_dec_ref_known(v___x_1351_, 1);
v___y_1295_ = v___y_1335_;
v___y_1296_ = v_a_1355_;
v___y_1297_ = v___y_1337_;
v___y_1298_ = v___y_1338_;
v___y_1299_ = v___y_1339_;
v___y_1300_ = v___y_1340_;
goto v___jp_1294_;
}
else
{
lean_object* v_a_1356_; lean_object* v_inheritedTraceOptions_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; uint8_t v___x_1360_; 
v_a_1356_ = lean_ctor_get(v___x_1351_, 0);
lean_inc(v_a_1356_);
lean_dec_ref_known(v___x_1351_, 1);
v_inheritedTraceOptions_1357_ = lean_ctor_get(v_toCold_1352_, 11);
v___x_1358_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___closed__1));
lean_inc(v___x_1283_);
v___x_1359_ = l_Lean_Name_append(v___x_1358_, v___x_1283_);
v___x_1360_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1357_, v_options_1353_, v___x_1359_);
lean_dec(v___x_1359_);
if (v___x_1360_ == 0)
{
lean_dec(v___x_1283_);
v___y_1295_ = v___y_1335_;
v___y_1296_ = v_a_1356_;
v___y_1297_ = v___y_1337_;
v___y_1298_ = v___y_1338_;
v___y_1299_ = v___y_1339_;
v___y_1300_ = v___y_1340_;
goto v___jp_1294_;
}
else
{
lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; 
v___x_1361_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__4);
lean_inc(v_a_1356_);
v___x_1362_ = lean_array_to_list(v_a_1356_);
v___x_1363_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_1362_, v___x_1344_);
v___x_1364_ = l_Lean_MessageData_ofList(v___x_1363_);
v___x_1365_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1365_, 0, v___x_1361_);
lean_ctor_set(v___x_1365_, 1, v___x_1364_);
v___x_1366_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_1283_, v___x_1365_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_);
if (lean_obj_tag(v___x_1366_) == 0)
{
lean_dec_ref_known(v___x_1366_, 1);
v___y_1295_ = v___y_1335_;
v___y_1296_ = v_a_1356_;
v___y_1297_ = v___y_1337_;
v___y_1298_ = v___y_1338_;
v___y_1299_ = v___y_1339_;
v___y_1300_ = v___y_1340_;
goto v___jp_1294_;
}
else
{
lean_object* v_a_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1374_; 
lean_dec(v_a_1356_);
lean_dec_ref(v___y_1335_);
lean_dec_ref(v_funTypes_1287_);
lean_dec_ref(v_preDefs_1280_);
lean_dec(v___x_1279_);
lean_dec_ref(v_xs_1278_);
lean_dec_ref(v_fixedParamPerms_1277_);
lean_dec_ref(v___x_1275_);
lean_dec_ref(v_recArgInfos_1273_);
v_a_1367_ = lean_ctor_get(v___x_1366_, 0);
v_isSharedCheck_1374_ = !lean_is_exclusive(v___x_1366_);
if (v_isSharedCheck_1374_ == 0)
{
v___x_1369_ = v___x_1366_;
v_isShared_1370_ = v_isSharedCheck_1374_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_a_1367_);
lean_dec(v___x_1366_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1374_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v___x_1372_; 
if (v_isShared_1370_ == 0)
{
v___x_1372_ = v___x_1369_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v_a_1367_);
v___x_1372_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
return v___x_1372_;
}
}
}
}
}
}
else
{
lean_object* v_a_1375_; lean_object* v___x_1377_; uint8_t v_isShared_1378_; uint8_t v_isSharedCheck_1382_; 
lean_dec_ref(v___y_1335_);
lean_dec_ref(v_funTypes_1287_);
lean_dec(v___x_1283_);
lean_dec_ref(v_preDefs_1280_);
lean_dec(v___x_1279_);
lean_dec_ref(v_xs_1278_);
lean_dec_ref(v_fixedParamPerms_1277_);
lean_dec_ref(v___x_1275_);
lean_dec_ref(v_recArgInfos_1273_);
v_a_1375_ = lean_ctor_get(v___x_1351_, 0);
v_isSharedCheck_1382_ = !lean_is_exclusive(v___x_1351_);
if (v_isSharedCheck_1382_ == 0)
{
v___x_1377_ = v___x_1351_;
v_isShared_1378_ = v_isSharedCheck_1382_;
goto v_resetjp_1376_;
}
else
{
lean_inc(v_a_1375_);
lean_dec(v___x_1351_);
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
else
{
lean_object* v_a_1383_; lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1390_; 
lean_dec_ref(v_FArgs_1336_);
lean_dec_ref(v___y_1335_);
lean_dec_ref(v_funTypes_1287_);
lean_dec(v___x_1283_);
lean_dec_ref(v___f_1282_);
lean_dec_ref(v_preDefs_1280_);
lean_dec(v___x_1279_);
lean_dec_ref(v_xs_1278_);
lean_dec_ref(v_fixedParamPerms_1277_);
lean_dec_ref(v___x_1275_);
lean_dec_ref(v_recArgInfos_1273_);
v_a_1383_ = lean_ctor_get(v___x_1349_, 0);
v_isSharedCheck_1390_ = !lean_is_exclusive(v___x_1349_);
if (v_isSharedCheck_1390_ == 0)
{
v___x_1385_ = v___x_1349_;
v_isShared_1386_ = v_isSharedCheck_1390_;
goto v_resetjp_1384_;
}
else
{
lean_inc(v_a_1383_);
lean_dec(v___x_1349_);
v___x_1385_ = lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1390_;
goto v_resetjp_1384_;
}
v_resetjp_1384_:
{
lean_object* v___x_1388_; 
if (v_isShared_1386_ == 0)
{
v___x_1388_ = v___x_1385_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v_a_1383_);
v___x_1388_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
return v___x_1388_;
}
}
}
}
v___jp_1391_:
{
if (v_a_1284_ == 0)
{
lean_object* v___x_1398_; lean_object* v_levelParams_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; size_t v_sz_1402_; lean_object* v___x_1403_; 
v___x_1398_ = lean_array_get_borrowed(v___x_1285_, v_preDefs_1280_, v___x_1279_);
v_levelParams_1399_ = lean_ctor_get(v___x_1398_, 1);
v___x_1400_ = lean_box(0);
lean_inc(v_levelParams_1399_);
v___x_1401_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__15(v_levelParams_1399_, v___x_1400_);
v_sz_1402_ = lean_array_size(v___y_1393_);
lean_inc_ref(v_preDefs_1280_);
v___x_1403_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___redArg(v_preDefs_1280_, v_xs_1278_, v_a_1284_, v___x_1401_, v_sz_1402_, v___x_1276_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_);
if (lean_obj_tag(v___x_1403_) == 0)
{
lean_object* v_a_1404_; 
v_a_1404_ = lean_ctor_get(v___x_1403_, 0);
lean_inc(v_a_1404_);
lean_dec_ref_known(v___x_1403_, 1);
v___y_1335_ = v___y_1392_;
v_FArgs_1336_ = v_a_1404_;
v___y_1337_ = v___y_1394_;
v___y_1338_ = v___y_1395_;
v___y_1339_ = v___y_1396_;
v___y_1340_ = v___y_1397_;
goto v___jp_1334_;
}
else
{
lean_object* v_a_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1412_; 
lean_dec_ref(v___y_1392_);
lean_dec_ref(v_funTypes_1287_);
lean_dec(v___x_1283_);
lean_dec_ref(v___f_1282_);
lean_dec_ref(v_preDefs_1280_);
lean_dec(v___x_1279_);
lean_dec_ref(v_xs_1278_);
lean_dec_ref(v_fixedParamPerms_1277_);
lean_dec_ref(v___x_1275_);
lean_dec_ref(v_recArgInfos_1273_);
v_a_1405_ = lean_ctor_get(v___x_1403_, 0);
v_isSharedCheck_1412_ = !lean_is_exclusive(v___x_1403_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1407_ = v___x_1403_;
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_a_1405_);
lean_dec(v___x_1403_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v___x_1410_; 
if (v_isShared_1408_ == 0)
{
v___x_1410_ = v___x_1407_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v_a_1405_);
v___x_1410_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
return v___x_1410_;
}
}
}
}
else
{
v___y_1335_ = v___y_1392_;
v_FArgs_1336_ = v___y_1393_;
v___y_1337_ = v___y_1394_;
v___y_1338_ = v___y_1395_;
v___y_1339_ = v___y_1396_;
v___y_1340_ = v___y_1397_;
goto v___jp_1334_;
}
}
v___jp_1413_:
{
size_t v_sz_1420_; lean_object* v___x_1421_; 
v_sz_1420_ = lean_array_size(v_recArgInfos_1273_);
lean_inc_ref(v___y_1414_);
lean_inc_ref(v_preDefs_1280_);
lean_inc_ref(v___x_1275_);
lean_inc_ref_n(v_recArgInfos_1273_, 2);
v___x_1421_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg(v_a_1284_, v_a_1274_, v___y_1415_, v_recArgInfos_1273_, v___x_1275_, v_preDefs_1280_, v___y_1414_, v_sz_1420_, v___x_1276_, v_recArgInfos_1273_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_);
lean_dec_ref(v___y_1415_);
if (lean_obj_tag(v___x_1421_) == 0)
{
lean_object* v_a_1422_; lean_object* v___x_1423_; 
v_a_1422_ = lean_ctor_get(v___x_1421_, 0);
lean_inc(v_a_1422_);
lean_dec_ref_known(v___x_1421_, 1);
lean_inc(v___y_1419_);
lean_inc_ref(v___y_1418_);
lean_inc(v___y_1417_);
lean_inc_ref(v___y_1416_);
v___x_1423_ = lean_apply_5(v___f_1286_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_, lean_box(0));
if (lean_obj_tag(v___x_1423_) == 0)
{
lean_object* v_a_1424_; uint8_t v___x_1425_; 
v_a_1424_ = lean_ctor_get(v___x_1423_, 0);
lean_inc(v_a_1424_);
lean_dec_ref_known(v___x_1423_, 1);
v___x_1425_ = lean_unbox(v_a_1424_);
lean_dec(v_a_1424_);
if (v___x_1425_ == 0)
{
v___y_1392_ = v___y_1414_;
v___y_1393_ = v_a_1422_;
v___y_1394_ = v___y_1416_;
v___y_1395_ = v___y_1417_;
v___y_1396_ = v___y_1418_;
v___y_1397_ = v___y_1419_;
goto v___jp_1391_;
}
else
{
lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; 
v___x_1426_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__6, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__6);
lean_inc(v_a_1422_);
v___x_1427_ = lean_array_to_list(v_a_1422_);
v___x_1428_ = lean_box(0);
v___x_1429_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_1427_, v___x_1428_);
v___x_1430_ = l_Lean_MessageData_ofList(v___x_1429_);
v___x_1431_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1431_, 0, v___x_1426_);
lean_ctor_set(v___x_1431_, 1, v___x_1430_);
lean_inc(v___x_1283_);
v___x_1432_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_1283_, v___x_1431_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_);
if (lean_obj_tag(v___x_1432_) == 0)
{
lean_dec_ref_known(v___x_1432_, 1);
v___y_1392_ = v___y_1414_;
v___y_1393_ = v_a_1422_;
v___y_1394_ = v___y_1416_;
v___y_1395_ = v___y_1417_;
v___y_1396_ = v___y_1418_;
v___y_1397_ = v___y_1419_;
goto v___jp_1391_;
}
else
{
lean_object* v_a_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1440_; 
lean_dec(v_a_1422_);
lean_dec_ref(v___y_1414_);
lean_dec_ref(v_funTypes_1287_);
lean_dec(v___x_1283_);
lean_dec_ref(v___f_1282_);
lean_dec_ref(v_preDefs_1280_);
lean_dec(v___x_1279_);
lean_dec_ref(v_xs_1278_);
lean_dec_ref(v_fixedParamPerms_1277_);
lean_dec_ref(v___x_1275_);
lean_dec_ref(v_recArgInfos_1273_);
v_a_1433_ = lean_ctor_get(v___x_1432_, 0);
v_isSharedCheck_1440_ = !lean_is_exclusive(v___x_1432_);
if (v_isSharedCheck_1440_ == 0)
{
v___x_1435_ = v___x_1432_;
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_a_1433_);
lean_dec(v___x_1432_);
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
lean_object* v_a_1441_; lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1448_; 
lean_dec(v_a_1422_);
lean_dec_ref(v___y_1414_);
lean_dec_ref(v_funTypes_1287_);
lean_dec(v___x_1283_);
lean_dec_ref(v___f_1282_);
lean_dec_ref(v_preDefs_1280_);
lean_dec(v___x_1279_);
lean_dec_ref(v_xs_1278_);
lean_dec_ref(v_fixedParamPerms_1277_);
lean_dec_ref(v___x_1275_);
lean_dec_ref(v_recArgInfos_1273_);
v_a_1441_ = lean_ctor_get(v___x_1423_, 0);
v_isSharedCheck_1448_ = !lean_is_exclusive(v___x_1423_);
if (v_isSharedCheck_1448_ == 0)
{
v___x_1443_ = v___x_1423_;
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
else
{
lean_inc(v_a_1441_);
lean_dec(v___x_1423_);
v___x_1443_ = lean_box(0);
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
v_resetjp_1442_:
{
lean_object* v___x_1446_; 
if (v_isShared_1444_ == 0)
{
v___x_1446_ = v___x_1443_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v_a_1441_);
v___x_1446_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
return v___x_1446_;
}
}
}
}
else
{
lean_object* v_a_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1456_; 
lean_dec_ref(v___y_1414_);
lean_dec_ref(v_funTypes_1287_);
lean_dec_ref(v___f_1286_);
lean_dec(v___x_1283_);
lean_dec_ref(v___f_1282_);
lean_dec_ref(v_preDefs_1280_);
lean_dec(v___x_1279_);
lean_dec_ref(v_xs_1278_);
lean_dec_ref(v_fixedParamPerms_1277_);
lean_dec_ref(v___x_1275_);
lean_dec_ref(v_recArgInfos_1273_);
v_a_1449_ = lean_ctor_get(v___x_1421_, 0);
v_isSharedCheck_1456_ = !lean_is_exclusive(v___x_1421_);
if (v_isSharedCheck_1456_ == 0)
{
v___x_1451_ = v___x_1421_;
v_isShared_1452_ = v_isSharedCheck_1456_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_a_1449_);
lean_dec(v___x_1421_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1456_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v___x_1454_; 
if (v_isShared_1452_ == 0)
{
v___x_1454_ = v___x_1451_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v_a_1449_);
v___x_1454_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
return v___x_1454_;
}
}
}
}
v___jp_1457_:
{
lean_object* v___x_1458_; 
v___x_1458_ = l_Lean_Elab_Structural_mkBRecOnConst(v_recArgInfos_1273_, v___x_1275_, v_motives_1288_, v_a_1284_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_);
lean_dec_ref(v_motives_1288_);
if (lean_obj_tag(v___x_1458_) == 0)
{
lean_object* v_a_1459_; lean_object* v___x_1460_; 
v_a_1459_ = lean_ctor_get(v___x_1458_, 0);
lean_inc_n(v_a_1459_, 2);
lean_dec_ref_known(v___x_1458_, 1);
lean_inc_ref(v___x_1275_);
v___x_1460_ = l_Lean_Elab_Structural_inferBRecOnFTypes(v_recArgInfos_1273_, v___x_1275_, v_a_1459_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_);
if (lean_obj_tag(v___x_1460_) == 0)
{
lean_object* v_a_1461_; lean_object* v___x_1462_; 
v_a_1461_ = lean_ctor_get(v___x_1460_, 0);
lean_inc(v_a_1461_);
lean_dec_ref_known(v___x_1460_, 1);
lean_inc_ref(v___f_1286_);
lean_inc(v___y_1292_);
lean_inc_ref(v___y_1291_);
lean_inc(v___y_1290_);
lean_inc_ref(v___y_1289_);
v___x_1462_ = lean_apply_5(v___f_1286_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, lean_box(0));
if (lean_obj_tag(v___x_1462_) == 0)
{
lean_object* v_a_1463_; uint8_t v___x_1464_; 
v_a_1463_ = lean_ctor_get(v___x_1462_, 0);
lean_inc(v_a_1463_);
lean_dec_ref_known(v___x_1462_, 1);
v___x_1464_ = lean_unbox(v_a_1463_);
lean_dec(v_a_1463_);
if (v___x_1464_ == 0)
{
v___y_1414_ = v_a_1459_;
v___y_1415_ = v_a_1461_;
v___y_1416_ = v___y_1289_;
v___y_1417_ = v___y_1290_;
v___y_1418_ = v___y_1291_;
v___y_1419_ = v___y_1292_;
goto v___jp_1413_;
}
else
{
lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; 
v___x_1465_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__8);
lean_inc(v_a_1461_);
v___x_1466_ = lean_array_to_list(v_a_1461_);
v___x_1467_ = lean_box(0);
v___x_1468_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_1466_, v___x_1467_);
v___x_1469_ = l_Lean_MessageData_ofList(v___x_1468_);
v___x_1470_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1470_, 0, v___x_1465_);
lean_ctor_set(v___x_1470_, 1, v___x_1469_);
lean_inc(v___x_1283_);
v___x_1471_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_1283_, v___x_1470_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_);
if (lean_obj_tag(v___x_1471_) == 0)
{
lean_dec_ref_known(v___x_1471_, 1);
v___y_1414_ = v_a_1459_;
v___y_1415_ = v_a_1461_;
v___y_1416_ = v___y_1289_;
v___y_1417_ = v___y_1290_;
v___y_1418_ = v___y_1291_;
v___y_1419_ = v___y_1292_;
goto v___jp_1413_;
}
else
{
lean_object* v_a_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1479_; 
lean_dec(v_a_1461_);
lean_dec(v_a_1459_);
lean_dec_ref(v_funTypes_1287_);
lean_dec_ref(v___f_1286_);
lean_dec(v___x_1283_);
lean_dec_ref(v___f_1282_);
lean_dec_ref(v_preDefs_1280_);
lean_dec(v___x_1279_);
lean_dec_ref(v_xs_1278_);
lean_dec_ref(v_fixedParamPerms_1277_);
lean_dec_ref(v___x_1275_);
lean_dec_ref(v_recArgInfos_1273_);
v_a_1472_ = lean_ctor_get(v___x_1471_, 0);
v_isSharedCheck_1479_ = !lean_is_exclusive(v___x_1471_);
if (v_isSharedCheck_1479_ == 0)
{
v___x_1474_ = v___x_1471_;
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_a_1472_);
lean_dec(v___x_1471_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
lean_object* v___x_1477_; 
if (v_isShared_1475_ == 0)
{
v___x_1477_ = v___x_1474_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v_a_1472_);
v___x_1477_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
return v___x_1477_;
}
}
}
}
}
else
{
lean_object* v_a_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1487_; 
lean_dec(v_a_1461_);
lean_dec(v_a_1459_);
lean_dec_ref(v_funTypes_1287_);
lean_dec_ref(v___f_1286_);
lean_dec(v___x_1283_);
lean_dec_ref(v___f_1282_);
lean_dec_ref(v_preDefs_1280_);
lean_dec(v___x_1279_);
lean_dec_ref(v_xs_1278_);
lean_dec_ref(v_fixedParamPerms_1277_);
lean_dec_ref(v___x_1275_);
lean_dec_ref(v_recArgInfos_1273_);
v_a_1480_ = lean_ctor_get(v___x_1462_, 0);
v_isSharedCheck_1487_ = !lean_is_exclusive(v___x_1462_);
if (v_isSharedCheck_1487_ == 0)
{
v___x_1482_ = v___x_1462_;
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_a_1480_);
lean_dec(v___x_1462_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v___x_1485_; 
if (v_isShared_1483_ == 0)
{
v___x_1485_ = v___x_1482_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v_a_1480_);
v___x_1485_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
return v___x_1485_;
}
}
}
}
else
{
lean_object* v_a_1488_; lean_object* v___x_1490_; uint8_t v_isShared_1491_; uint8_t v_isSharedCheck_1495_; 
lean_dec(v_a_1459_);
lean_dec_ref(v_funTypes_1287_);
lean_dec_ref(v___f_1286_);
lean_dec(v___x_1283_);
lean_dec_ref(v___f_1282_);
lean_dec_ref(v_preDefs_1280_);
lean_dec(v___x_1279_);
lean_dec_ref(v_xs_1278_);
lean_dec_ref(v_fixedParamPerms_1277_);
lean_dec_ref(v___x_1275_);
lean_dec_ref(v_recArgInfos_1273_);
v_a_1488_ = lean_ctor_get(v___x_1460_, 0);
v_isSharedCheck_1495_ = !lean_is_exclusive(v___x_1460_);
if (v_isSharedCheck_1495_ == 0)
{
v___x_1490_ = v___x_1460_;
v_isShared_1491_ = v_isSharedCheck_1495_;
goto v_resetjp_1489_;
}
else
{
lean_inc(v_a_1488_);
lean_dec(v___x_1460_);
v___x_1490_ = lean_box(0);
v_isShared_1491_ = v_isSharedCheck_1495_;
goto v_resetjp_1489_;
}
v_resetjp_1489_:
{
lean_object* v___x_1493_; 
if (v_isShared_1491_ == 0)
{
v___x_1493_ = v___x_1490_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v_a_1488_);
v___x_1493_ = v_reuseFailAlloc_1494_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
return v___x_1493_;
}
}
}
}
else
{
lean_object* v_a_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1503_; 
lean_dec_ref(v_funTypes_1287_);
lean_dec_ref(v___f_1286_);
lean_dec(v___x_1283_);
lean_dec_ref(v___f_1282_);
lean_dec_ref(v_preDefs_1280_);
lean_dec(v___x_1279_);
lean_dec_ref(v_xs_1278_);
lean_dec_ref(v_fixedParamPerms_1277_);
lean_dec_ref(v___x_1275_);
lean_dec_ref(v_recArgInfos_1273_);
v_a_1496_ = lean_ctor_get(v___x_1458_, 0);
v_isSharedCheck_1503_ = !lean_is_exclusive(v___x_1458_);
if (v_isSharedCheck_1503_ == 0)
{
v___x_1498_ = v___x_1458_;
v_isShared_1499_ = v_isSharedCheck_1503_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_a_1496_);
lean_dec(v___x_1458_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1503_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
lean_object* v___x_1501_; 
if (v_isShared_1499_ == 0)
{
v___x_1501_ = v___x_1498_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v_a_1496_);
v___x_1501_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
return v___x_1501_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___boxed(lean_object** _args){
lean_object* v_recArgInfos_1536_ = _args[0];
lean_object* v_a_1537_ = _args[1];
lean_object* v___x_1538_ = _args[2];
lean_object* v___x_1539_ = _args[3];
lean_object* v_fixedParamPerms_1540_ = _args[4];
lean_object* v_xs_1541_ = _args[5];
lean_object* v___x_1542_ = _args[6];
lean_object* v_preDefs_1543_ = _args[7];
lean_object* v_numIndices_1544_ = _args[8];
lean_object* v___f_1545_ = _args[9];
lean_object* v___x_1546_ = _args[10];
lean_object* v_a_1547_ = _args[11];
lean_object* v___x_1548_ = _args[12];
lean_object* v___f_1549_ = _args[13];
lean_object* v_funTypes_1550_ = _args[14];
lean_object* v_motives_1551_ = _args[15];
lean_object* v___y_1552_ = _args[16];
lean_object* v___y_1553_ = _args[17];
lean_object* v___y_1554_ = _args[18];
lean_object* v___y_1555_ = _args[19];
lean_object* v___y_1556_ = _args[20];
_start:
{
size_t v___x_27489__boxed_1557_; uint8_t v_a_27493__boxed_1558_; lean_object* v_res_1559_; 
v___x_27489__boxed_1557_ = lean_unbox_usize(v___x_1539_);
lean_dec(v___x_1539_);
v_a_27493__boxed_1558_ = lean_unbox(v_a_1547_);
v_res_1559_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2(v_recArgInfos_1536_, v_a_1537_, v___x_1538_, v___x_27489__boxed_1557_, v_fixedParamPerms_1540_, v_xs_1541_, v___x_1542_, v_preDefs_1543_, v_numIndices_1544_, v___f_1545_, v___x_1546_, v_a_27493__boxed_1558_, v___x_1548_, v___f_1549_, v_funTypes_1550_, v_motives_1551_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_);
lean_dec(v___y_1555_);
lean_dec_ref(v___y_1554_);
lean_dec(v___y_1553_);
lean_dec_ref(v___y_1552_);
lean_dec_ref(v___x_1548_);
lean_dec(v_numIndices_1544_);
lean_dec_ref(v_a_1537_);
return v_res_1559_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___redArg(lean_object* v_a_1560_, lean_object* v_funTypes_1561_, size_t v_sz_1562_, size_t v_i_1563_, lean_object* v_bs_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_){
_start:
{
uint8_t v___x_1570_; 
v___x_1570_ = lean_usize_dec_lt(v_i_1563_, v_sz_1562_);
if (v___x_1570_ == 0)
{
lean_object* v___x_1571_; 
v___x_1571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1571_, 0, v_bs_1564_);
return v___x_1571_;
}
else
{
lean_object* v___x_1572_; lean_object* v_v_1573_; lean_object* v___x_1574_; lean_object* v_bs_x27_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; 
v___x_1572_ = l_Lean_instInhabitedExpr;
v_v_1573_ = lean_array_uget(v_bs_1564_, v_i_1563_);
v___x_1574_ = lean_unsigned_to_nat(0u);
v_bs_x27_1575_ = lean_array_uset(v_bs_1564_, v_i_1563_, v___x_1574_);
v___x_1576_ = lean_usize_to_nat(v_i_1563_);
v___x_1577_ = lean_array_get_borrowed(v___x_1572_, v_a_1560_, v___x_1576_);
v___x_1578_ = lean_array_get_borrowed(v___x_1572_, v_funTypes_1561_, v___x_1576_);
lean_dec(v___x_1576_);
lean_inc(v___x_1578_);
lean_inc(v___x_1577_);
v___x_1579_ = l_Lean_Elab_Structural_mkIndPredBRecOnMotive(v_v_1573_, v___x_1577_, v___x_1578_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_);
if (lean_obj_tag(v___x_1579_) == 0)
{
lean_object* v_a_1580_; size_t v___x_1581_; size_t v___x_1582_; lean_object* v___x_1583_; 
v_a_1580_ = lean_ctor_get(v___x_1579_, 0);
lean_inc(v_a_1580_);
lean_dec_ref_known(v___x_1579_, 1);
v___x_1581_ = ((size_t)1ULL);
v___x_1582_ = lean_usize_add(v_i_1563_, v___x_1581_);
v___x_1583_ = lean_array_uset(v_bs_x27_1575_, v_i_1563_, v_a_1580_);
v_i_1563_ = v___x_1582_;
v_bs_1564_ = v___x_1583_;
goto _start;
}
else
{
lean_object* v_a_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1592_; 
lean_dec_ref(v_bs_x27_1575_);
v_a_1585_ = lean_ctor_get(v___x_1579_, 0);
v_isSharedCheck_1592_ = !lean_is_exclusive(v___x_1579_);
if (v_isSharedCheck_1592_ == 0)
{
v___x_1587_ = v___x_1579_;
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_a_1585_);
lean_dec(v___x_1579_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
lean_object* v___x_1590_; 
if (v_isShared_1588_ == 0)
{
v___x_1590_ = v___x_1587_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v_a_1585_);
v___x_1590_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
return v___x_1590_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___redArg___boxed(lean_object* v_a_1593_, lean_object* v_funTypes_1594_, lean_object* v_sz_1595_, lean_object* v_i_1596_, lean_object* v_bs_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_){
_start:
{
size_t v_sz_boxed_1603_; size_t v_i_boxed_1604_; lean_object* v_res_1605_; 
v_sz_boxed_1603_ = lean_unbox_usize(v_sz_1595_);
lean_dec(v_sz_1595_);
v_i_boxed_1604_ = lean_unbox_usize(v_i_1596_);
lean_dec(v_i_1596_);
v_res_1605_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___redArg(v_a_1593_, v_funTypes_1594_, v_sz_boxed_1603_, v_i_boxed_1604_, v_bs_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_);
lean_dec(v___y_1601_);
lean_dec_ref(v___y_1600_);
lean_dec(v___y_1599_);
lean_dec_ref(v___y_1598_);
lean_dec_ref(v_funTypes_1594_);
lean_dec_ref(v_a_1593_);
return v_res_1605_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__3(lean_object* v_recArgInfos_1606_, lean_object* v_a_1607_, size_t v___x_1608_, lean_object* v___f_1609_, lean_object* v_funTypes_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_){
_start:
{
size_t v_sz_1616_; lean_object* v___x_1617_; 
v_sz_1616_ = lean_array_size(v_recArgInfos_1606_);
v___x_1617_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___redArg(v_a_1607_, v_funTypes_1610_, v_sz_1616_, v___x_1608_, v_recArgInfos_1606_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_);
if (lean_obj_tag(v___x_1617_) == 0)
{
lean_object* v_a_1618_; lean_object* v___x_1619_; 
v_a_1618_ = lean_ctor_get(v___x_1617_, 0);
lean_inc(v_a_1618_);
lean_dec_ref_known(v___x_1617_, 1);
lean_inc(v___y_1614_);
lean_inc_ref(v___y_1613_);
lean_inc(v___y_1612_);
lean_inc_ref(v___y_1611_);
v___x_1619_ = lean_apply_7(v___f_1609_, v_funTypes_1610_, v_a_1618_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, lean_box(0));
return v___x_1619_;
}
else
{
lean_object* v_a_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1627_; 
lean_dec_ref(v_funTypes_1610_);
lean_dec_ref(v___f_1609_);
v_a_1620_ = lean_ctor_get(v___x_1617_, 0);
v_isSharedCheck_1627_ = !lean_is_exclusive(v___x_1617_);
if (v_isSharedCheck_1627_ == 0)
{
v___x_1622_ = v___x_1617_;
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_a_1620_);
lean_dec(v___x_1617_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v___x_1625_; 
if (v_isShared_1623_ == 0)
{
v___x_1625_ = v___x_1622_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v_a_1620_);
v___x_1625_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
return v___x_1625_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__3___boxed(lean_object* v_recArgInfos_1628_, lean_object* v_a_1629_, lean_object* v___x_1630_, lean_object* v___f_1631_, lean_object* v_funTypes_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_){
_start:
{
size_t v___x_28079__boxed_1638_; lean_object* v_res_1639_; 
v___x_28079__boxed_1638_ = lean_unbox_usize(v___x_1630_);
lean_dec(v___x_1630_);
v_res_1639_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__3(v_recArgInfos_1628_, v_a_1629_, v___x_28079__boxed_1638_, v___f_1631_, v_funTypes_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
lean_dec(v___y_1636_);
lean_dec_ref(v___y_1635_);
lean_dec(v___y_1634_);
lean_dec_ref(v___y_1633_);
lean_dec_ref(v_a_1629_);
return v_res_1639_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__0(lean_object* v_a_1640_, lean_object* v_a_1641_){
_start:
{
if (lean_obj_tag(v_a_1640_) == 0)
{
lean_object* v___x_1642_; 
v___x_1642_ = l_List_reverse___redArg(v_a_1641_);
return v___x_1642_;
}
else
{
lean_object* v_head_1643_; lean_object* v_tail_1644_; lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1655_; 
v_head_1643_ = lean_ctor_get(v_a_1640_, 0);
v_tail_1644_ = lean_ctor_get(v_a_1640_, 1);
v_isSharedCheck_1655_ = !lean_is_exclusive(v_a_1640_);
if (v_isSharedCheck_1655_ == 0)
{
v___x_1646_ = v_a_1640_;
v_isShared_1647_ = v_isSharedCheck_1655_;
goto v_resetjp_1645_;
}
else
{
lean_inc(v_tail_1644_);
lean_inc(v_head_1643_);
lean_dec(v_a_1640_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1655_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1652_; 
v___x_1648_ = l_Nat_reprFast(v_head_1643_);
v___x_1649_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1649_, 0, v___x_1648_);
v___x_1650_ = l_Lean_MessageData_ofFormat(v___x_1649_);
if (v_isShared_1647_ == 0)
{
lean_ctor_set(v___x_1646_, 1, v_a_1641_);
lean_ctor_set(v___x_1646_, 0, v___x_1650_);
v___x_1652_ = v___x_1646_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v___x_1650_);
lean_ctor_set(v_reuseFailAlloc_1654_, 1, v_a_1641_);
v___x_1652_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
v_a_1640_ = v_tail_1644_;
v_a_1641_ = v___x_1652_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__21(lean_object* v_a_1656_, lean_object* v_a_1657_){
_start:
{
if (lean_obj_tag(v_a_1656_) == 0)
{
lean_object* v___x_1658_; 
v___x_1658_ = l_List_reverse___redArg(v_a_1657_);
return v___x_1658_;
}
else
{
lean_object* v_head_1659_; lean_object* v_tail_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1672_; 
v_head_1659_ = lean_ctor_get(v_a_1656_, 0);
v_tail_1660_ = lean_ctor_get(v_a_1656_, 1);
v_isSharedCheck_1672_ = !lean_is_exclusive(v_a_1656_);
if (v_isSharedCheck_1672_ == 0)
{
v___x_1662_ = v_a_1656_;
v_isShared_1663_ = v_isSharedCheck_1672_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_tail_1660_);
lean_inc(v_head_1659_);
lean_dec(v_a_1656_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1672_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1669_; 
v___x_1664_ = lean_array_to_list(v_head_1659_);
v___x_1665_ = lean_box(0);
v___x_1666_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__0(v___x_1664_, v___x_1665_);
v___x_1667_ = l_Lean_MessageData_ofList(v___x_1666_);
if (v_isShared_1663_ == 0)
{
lean_ctor_set(v___x_1662_, 1, v_a_1657_);
lean_ctor_set(v___x_1662_, 0, v___x_1667_);
v___x_1669_ = v___x_1662_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v___x_1667_);
lean_ctor_set(v_reuseFailAlloc_1671_, 1, v_a_1657_);
v___x_1669_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
v_a_1656_ = v_tail_1660_;
v_a_1657_ = v___x_1669_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg(lean_object* v_msg_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_){
_start:
{
lean_object* v_ref_1679_; lean_object* v___x_1680_; lean_object* v_a_1681_; lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1689_; 
v_ref_1679_ = lean_ctor_get(v___y_1676_, 2);
v___x_1680_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11_spec__21(v_msg_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_);
v_a_1681_ = lean_ctor_get(v___x_1680_, 0);
v_isSharedCheck_1689_ = !lean_is_exclusive(v___x_1680_);
if (v_isSharedCheck_1689_ == 0)
{
v___x_1683_ = v___x_1680_;
v_isShared_1684_ = v_isSharedCheck_1689_;
goto v_resetjp_1682_;
}
else
{
lean_inc(v_a_1681_);
lean_dec(v___x_1680_);
v___x_1683_ = lean_box(0);
v_isShared_1684_ = v_isSharedCheck_1689_;
goto v_resetjp_1682_;
}
v_resetjp_1682_:
{
lean_object* v___x_1685_; lean_object* v___x_1687_; 
lean_inc(v_ref_1679_);
v___x_1685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1685_, 0, v_ref_1679_);
lean_ctor_set(v___x_1685_, 1, v_a_1681_);
if (v_isShared_1684_ == 0)
{
lean_ctor_set_tag(v___x_1683_, 1);
lean_ctor_set(v___x_1683_, 0, v___x_1685_);
v___x_1687_ = v___x_1683_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v___x_1685_);
v___x_1687_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
return v___x_1687_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg___boxed(lean_object* v_msg_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_){
_start:
{
lean_object* v_res_1696_; 
v_res_1696_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg(v_msg_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_);
lean_dec(v___y_1694_);
lean_dec_ref(v___y_1693_);
lean_dec(v___y_1692_);
lean_dec_ref(v___y_1691_);
return v_res_1696_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1698_; lean_object* v___x_1699_; 
v___x_1698_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__0));
v___x_1699_ = l_Lean_stringToMessageData(v___x_1698_);
return v___x_1699_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__3(void){
_start:
{
lean_object* v___x_1701_; lean_object* v___x_1702_; 
v___x_1701_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__2));
v___x_1702_ = l_Lean_stringToMessageData(v___x_1701_);
return v___x_1702_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4(lean_object* v_constName_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_){
_start:
{
lean_object* v___x_1709_; lean_object* v_env_1710_; lean_object* v___x_1711_; 
v___x_1709_ = lean_st_ref_get(v___y_1707_);
v_env_1710_ = lean_ctor_get(v___x_1709_, 0);
lean_inc_ref(v_env_1710_);
lean_dec(v___x_1709_);
lean_inc(v_constName_1703_);
v___x_1711_ = l_Lean_isInductiveCore_x3f(v_env_1710_, v_constName_1703_);
if (lean_obj_tag(v___x_1711_) == 0)
{
lean_object* v___x_1712_; uint8_t v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; 
v___x_1712_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__1, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__1);
v___x_1713_ = 0;
v___x_1714_ = l_Lean_MessageData_ofConstName(v_constName_1703_, v___x_1713_);
v___x_1715_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1715_, 0, v___x_1712_);
lean_ctor_set(v___x_1715_, 1, v___x_1714_);
v___x_1716_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__3, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__3_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__3);
v___x_1717_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1717_, 0, v___x_1715_);
lean_ctor_set(v___x_1717_, 1, v___x_1716_);
v___x_1718_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg(v___x_1717_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_);
return v___x_1718_;
}
else
{
lean_object* v_val_1719_; lean_object* v___x_1721_; uint8_t v_isShared_1722_; uint8_t v_isSharedCheck_1726_; 
lean_dec(v_constName_1703_);
v_val_1719_ = lean_ctor_get(v___x_1711_, 0);
v_isSharedCheck_1726_ = !lean_is_exclusive(v___x_1711_);
if (v_isSharedCheck_1726_ == 0)
{
v___x_1721_ = v___x_1711_;
v_isShared_1722_ = v_isSharedCheck_1726_;
goto v_resetjp_1720_;
}
else
{
lean_inc(v_val_1719_);
lean_dec(v___x_1711_);
v___x_1721_ = lean_box(0);
v_isShared_1722_ = v_isSharedCheck_1726_;
goto v_resetjp_1720_;
}
v_resetjp_1720_:
{
lean_object* v___x_1724_; 
if (v_isShared_1722_ == 0)
{
lean_ctor_set_tag(v___x_1721_, 0);
v___x_1724_ = v___x_1721_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v_val_1719_);
v___x_1724_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
return v___x_1724_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___boxed(lean_object* v_constName_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_){
_start:
{
lean_object* v_res_1733_; 
v_res_1733_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4(v_constName_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_);
lean_dec(v___y_1731_);
lean_dec_ref(v___y_1730_);
lean_dec(v___y_1729_);
lean_dec_ref(v___y_1728_);
return v_res_1733_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___redArg(lean_object* v_fixedParamPerms_1734_, lean_object* v_xs_1735_, size_t v_sz_1736_, size_t v_i_1737_, lean_object* v_bs_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_){
_start:
{
uint8_t v___x_1744_; 
v___x_1744_ = lean_usize_dec_lt(v_i_1737_, v_sz_1736_);
if (v___x_1744_ == 0)
{
lean_object* v___x_1745_; 
lean_dec_ref(v_xs_1735_);
v___x_1745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1745_, 0, v_bs_1738_);
return v___x_1745_;
}
else
{
lean_object* v_v_1746_; lean_object* v_perms_1747_; lean_object* v_type_1748_; lean_object* v___x_1749_; lean_object* v_bs_x27_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; 
v_v_1746_ = lean_array_uget_borrowed(v_bs_1738_, v_i_1737_);
v_perms_1747_ = lean_ctor_get(v_fixedParamPerms_1734_, 1);
v_type_1748_ = lean_ctor_get(v_v_1746_, 6);
lean_inc_ref(v_type_1748_);
v___x_1749_ = lean_unsigned_to_nat(0u);
v_bs_x27_1750_ = lean_array_uset(v_bs_1738_, v_i_1737_, v___x_1749_);
v___x_1751_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0);
v___x_1752_ = lean_usize_to_nat(v_i_1737_);
v___x_1753_ = lean_array_get_borrowed(v___x_1751_, v_perms_1747_, v___x_1752_);
lean_dec(v___x_1752_);
lean_inc_ref(v_xs_1735_);
lean_inc(v___x_1753_);
v___x_1754_ = l_Lean_Elab_FixedParamPerm_instantiateForall(v___x_1753_, v_type_1748_, v_xs_1735_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_);
if (lean_obj_tag(v___x_1754_) == 0)
{
lean_object* v_a_1755_; size_t v___x_1756_; size_t v___x_1757_; lean_object* v___x_1758_; 
v_a_1755_ = lean_ctor_get(v___x_1754_, 0);
lean_inc(v_a_1755_);
lean_dec_ref_known(v___x_1754_, 1);
v___x_1756_ = ((size_t)1ULL);
v___x_1757_ = lean_usize_add(v_i_1737_, v___x_1756_);
v___x_1758_ = lean_array_uset(v_bs_x27_1750_, v_i_1737_, v_a_1755_);
v_i_1737_ = v___x_1757_;
v_bs_1738_ = v___x_1758_;
goto _start;
}
else
{
lean_object* v_a_1760_; lean_object* v___x_1762_; uint8_t v_isShared_1763_; uint8_t v_isSharedCheck_1767_; 
lean_dec_ref(v_bs_x27_1750_);
lean_dec_ref(v_xs_1735_);
v_a_1760_ = lean_ctor_get(v___x_1754_, 0);
v_isSharedCheck_1767_ = !lean_is_exclusive(v___x_1754_);
if (v_isSharedCheck_1767_ == 0)
{
v___x_1762_ = v___x_1754_;
v_isShared_1763_ = v_isSharedCheck_1767_;
goto v_resetjp_1761_;
}
else
{
lean_inc(v_a_1760_);
lean_dec(v___x_1754_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___redArg___boxed(lean_object* v_fixedParamPerms_1768_, lean_object* v_xs_1769_, lean_object* v_sz_1770_, lean_object* v_i_1771_, lean_object* v_bs_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_){
_start:
{
size_t v_sz_boxed_1778_; size_t v_i_boxed_1779_; lean_object* v_res_1780_; 
v_sz_boxed_1778_ = lean_unbox_usize(v_sz_1770_);
lean_dec(v_sz_1770_);
v_i_boxed_1779_ = lean_unbox_usize(v_i_1771_);
lean_dec(v_i_1771_);
v_res_1780_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___redArg(v_fixedParamPerms_1768_, v_xs_1769_, v_sz_boxed_1778_, v_i_boxed_1779_, v_bs_1772_, v___y_1773_, v___y_1774_, v___y_1775_, v___y_1776_);
lean_dec(v___y_1776_);
lean_dec_ref(v___y_1775_);
lean_dec(v___y_1774_);
lean_dec_ref(v___y_1773_);
lean_dec_ref(v_fixedParamPerms_1768_);
return v_res_1780_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__20___redArg(lean_object* v_a_1781_, lean_object* v_a_1782_, size_t v_sz_1783_, size_t v_i_1784_, lean_object* v_bs_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_){
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
lean_object* v___x_1793_; lean_object* v_v_1794_; lean_object* v___x_1795_; lean_object* v_bs_x27_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; 
v___x_1793_ = l_Lean_instInhabitedExpr;
v_v_1794_ = lean_array_uget(v_bs_1785_, v_i_1784_);
v___x_1795_ = lean_unsigned_to_nat(0u);
v_bs_x27_1796_ = lean_array_uset(v_bs_1785_, v_i_1784_, v___x_1795_);
v___x_1797_ = lean_usize_to_nat(v_i_1784_);
v___x_1798_ = lean_array_get_borrowed(v___x_1793_, v_a_1781_, v___x_1797_);
v___x_1799_ = lean_array_get_borrowed(v___x_1793_, v_a_1782_, v___x_1797_);
lean_dec(v___x_1797_);
lean_inc(v___x_1799_);
lean_inc(v___x_1798_);
v___x_1800_ = l_Lean_Elab_Structural_mkBRecOnMotive(v_v_1794_, v___x_1798_, v___x_1799_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_);
if (lean_obj_tag(v___x_1800_) == 0)
{
lean_object* v_a_1801_; size_t v___x_1802_; size_t v___x_1803_; lean_object* v___x_1804_; 
v_a_1801_ = lean_ctor_get(v___x_1800_, 0);
lean_inc(v_a_1801_);
lean_dec_ref_known(v___x_1800_, 1);
v___x_1802_ = ((size_t)1ULL);
v___x_1803_ = lean_usize_add(v_i_1784_, v___x_1802_);
v___x_1804_ = lean_array_uset(v_bs_x27_1796_, v_i_1784_, v_a_1801_);
v_i_1784_ = v___x_1803_;
v_bs_1785_ = v___x_1804_;
goto _start;
}
else
{
lean_object* v_a_1806_; lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1813_; 
lean_dec_ref(v_bs_x27_1796_);
v_a_1806_ = lean_ctor_get(v___x_1800_, 0);
v_isSharedCheck_1813_ = !lean_is_exclusive(v___x_1800_);
if (v_isSharedCheck_1813_ == 0)
{
v___x_1808_ = v___x_1800_;
v_isShared_1809_ = v_isSharedCheck_1813_;
goto v_resetjp_1807_;
}
else
{
lean_inc(v_a_1806_);
lean_dec(v___x_1800_);
v___x_1808_ = lean_box(0);
v_isShared_1809_ = v_isSharedCheck_1813_;
goto v_resetjp_1807_;
}
v_resetjp_1807_:
{
lean_object* v___x_1811_; 
if (v_isShared_1809_ == 0)
{
v___x_1811_ = v___x_1808_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v_a_1806_);
v___x_1811_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
return v___x_1811_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__20___redArg___boxed(lean_object* v_a_1814_, lean_object* v_a_1815_, lean_object* v_sz_1816_, lean_object* v_i_1817_, lean_object* v_bs_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_){
_start:
{
size_t v_sz_boxed_1824_; size_t v_i_boxed_1825_; lean_object* v_res_1826_; 
v_sz_boxed_1824_ = lean_unbox_usize(v_sz_1816_);
lean_dec(v_sz_1816_);
v_i_boxed_1825_ = lean_unbox_usize(v_i_1817_);
lean_dec(v_i_1817_);
v_res_1826_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__20___redArg(v_a_1814_, v_a_1815_, v_sz_boxed_1824_, v_i_boxed_1825_, v_bs_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_);
lean_dec(v___y_1822_);
lean_dec_ref(v___y_1821_);
lean_dec(v___y_1820_);
lean_dec_ref(v___y_1819_);
lean_dec_ref(v_a_1815_);
lean_dec_ref(v_a_1814_);
return v_res_1826_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___redArg(lean_object* v_fixedParamPerms_1827_, lean_object* v_xs_1828_, size_t v_sz_1829_, size_t v_i_1830_, lean_object* v_bs_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_){
_start:
{
uint8_t v___x_1837_; 
v___x_1837_ = lean_usize_dec_lt(v_i_1830_, v_sz_1829_);
if (v___x_1837_ == 0)
{
lean_object* v___x_1838_; 
lean_dec_ref(v_xs_1828_);
v___x_1838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1838_, 0, v_bs_1831_);
return v___x_1838_;
}
else
{
lean_object* v_v_1839_; lean_object* v_perms_1840_; lean_object* v_value_1841_; lean_object* v___x_1842_; lean_object* v_bs_x27_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; 
v_v_1839_ = lean_array_uget_borrowed(v_bs_1831_, v_i_1830_);
v_perms_1840_ = lean_ctor_get(v_fixedParamPerms_1827_, 1);
v_value_1841_ = lean_ctor_get(v_v_1839_, 7);
lean_inc_ref(v_value_1841_);
v___x_1842_ = lean_unsigned_to_nat(0u);
v_bs_x27_1843_ = lean_array_uset(v_bs_1831_, v_i_1830_, v___x_1842_);
v___x_1844_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0);
v___x_1845_ = lean_usize_to_nat(v_i_1830_);
v___x_1846_ = lean_array_get_borrowed(v___x_1844_, v_perms_1840_, v___x_1845_);
lean_dec(v___x_1845_);
lean_inc_ref(v_xs_1828_);
lean_inc(v___x_1846_);
v___x_1847_ = l_Lean_Elab_FixedParamPerm_instantiateLambda(v___x_1846_, v_value_1841_, v_xs_1828_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_);
if (lean_obj_tag(v___x_1847_) == 0)
{
lean_object* v_a_1848_; size_t v___x_1849_; size_t v___x_1850_; lean_object* v___x_1851_; 
v_a_1848_ = lean_ctor_get(v___x_1847_, 0);
lean_inc(v_a_1848_);
lean_dec_ref_known(v___x_1847_, 1);
v___x_1849_ = ((size_t)1ULL);
v___x_1850_ = lean_usize_add(v_i_1830_, v___x_1849_);
v___x_1851_ = lean_array_uset(v_bs_x27_1843_, v_i_1830_, v_a_1848_);
v_i_1830_ = v___x_1850_;
v_bs_1831_ = v___x_1851_;
goto _start;
}
else
{
lean_object* v_a_1853_; lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_1860_; 
lean_dec_ref(v_bs_x27_1843_);
lean_dec_ref(v_xs_1828_);
v_a_1853_ = lean_ctor_get(v___x_1847_, 0);
v_isSharedCheck_1860_ = !lean_is_exclusive(v___x_1847_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1855_ = v___x_1847_;
v_isShared_1856_ = v_isSharedCheck_1860_;
goto v_resetjp_1854_;
}
else
{
lean_inc(v_a_1853_);
lean_dec(v___x_1847_);
v___x_1855_ = lean_box(0);
v_isShared_1856_ = v_isSharedCheck_1860_;
goto v_resetjp_1854_;
}
v_resetjp_1854_:
{
lean_object* v___x_1858_; 
if (v_isShared_1856_ == 0)
{
v___x_1858_ = v___x_1855_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v_a_1853_);
v___x_1858_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
return v___x_1858_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___redArg___boxed(lean_object* v_fixedParamPerms_1861_, lean_object* v_xs_1862_, lean_object* v_sz_1863_, lean_object* v_i_1864_, lean_object* v_bs_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_){
_start:
{
size_t v_sz_boxed_1871_; size_t v_i_boxed_1872_; lean_object* v_res_1873_; 
v_sz_boxed_1871_ = lean_unbox_usize(v_sz_1863_);
lean_dec(v_sz_1863_);
v_i_boxed_1872_ = lean_unbox_usize(v_i_1864_);
lean_dec(v_i_1864_);
v_res_1873_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___redArg(v_fixedParamPerms_1861_, v_xs_1862_, v_sz_boxed_1871_, v_i_boxed_1872_, v_bs_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_);
lean_dec(v___y_1869_);
lean_dec_ref(v___y_1868_);
lean_dec(v___y_1867_);
lean_dec_ref(v___y_1866_);
lean_dec_ref(v_fixedParamPerms_1861_);
return v_res_1873_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11___redArg(lean_object* v_hi_1874_, lean_object* v_pivot_1875_, lean_object* v_as_1876_, lean_object* v_i_1877_, lean_object* v_k_1878_){
_start:
{
uint8_t v___x_1879_; 
v___x_1879_ = lean_nat_dec_lt(v_k_1878_, v_hi_1874_);
if (v___x_1879_ == 0)
{
lean_object* v___x_1880_; lean_object* v___x_1881_; 
lean_dec(v_k_1878_);
v___x_1880_ = lean_array_fswap(v_as_1876_, v_i_1877_, v_hi_1874_);
v___x_1881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1881_, 0, v_i_1877_);
lean_ctor_set(v___x_1881_, 1, v___x_1880_);
return v___x_1881_;
}
else
{
lean_object* v___x_1882_; uint8_t v___x_1883_; 
v___x_1882_ = lean_array_fget_borrowed(v_as_1876_, v_k_1878_);
v___x_1883_ = l_Nat_blt(v___x_1882_, v_pivot_1875_);
if (v___x_1883_ == 0)
{
lean_object* v___x_1884_; lean_object* v___x_1885_; 
v___x_1884_ = lean_unsigned_to_nat(1u);
v___x_1885_ = lean_nat_add(v_k_1878_, v___x_1884_);
lean_dec(v_k_1878_);
v_k_1878_ = v___x_1885_;
goto _start;
}
else
{
lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; 
v___x_1887_ = lean_array_fswap(v_as_1876_, v_i_1877_, v_k_1878_);
v___x_1888_ = lean_unsigned_to_nat(1u);
v___x_1889_ = lean_nat_add(v_i_1877_, v___x_1888_);
lean_dec(v_i_1877_);
v___x_1890_ = lean_nat_add(v_k_1878_, v___x_1888_);
lean_dec(v_k_1878_);
v_as_1876_ = v___x_1887_;
v_i_1877_ = v___x_1889_;
v_k_1878_ = v___x_1890_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11___redArg___boxed(lean_object* v_hi_1892_, lean_object* v_pivot_1893_, lean_object* v_as_1894_, lean_object* v_i_1895_, lean_object* v_k_1896_){
_start:
{
lean_object* v_res_1897_; 
v_res_1897_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11___redArg(v_hi_1892_, v_pivot_1893_, v_as_1894_, v_i_1895_, v_k_1896_);
lean_dec(v_pivot_1893_);
lean_dec(v_hi_1892_);
return v_res_1897_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg(lean_object* v_n_1898_, lean_object* v_as_1899_, lean_object* v_lo_1900_, lean_object* v_hi_1901_){
_start:
{
lean_object* v___y_1903_; uint8_t v___x_1913_; 
v___x_1913_ = lean_nat_dec_lt(v_lo_1900_, v_hi_1901_);
if (v___x_1913_ == 0)
{
lean_dec(v_lo_1900_);
return v_as_1899_;
}
else
{
lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v_mid_1916_; lean_object* v___y_1918_; lean_object* v___y_1924_; lean_object* v___x_1929_; lean_object* v___x_1930_; uint8_t v___x_1931_; 
v___x_1914_ = lean_nat_add(v_lo_1900_, v_hi_1901_);
v___x_1915_ = lean_unsigned_to_nat(1u);
v_mid_1916_ = lean_nat_shiftr(v___x_1914_, v___x_1915_);
lean_dec(v___x_1914_);
v___x_1929_ = lean_array_fget_borrowed(v_as_1899_, v_mid_1916_);
v___x_1930_ = lean_array_fget_borrowed(v_as_1899_, v_lo_1900_);
v___x_1931_ = l_Nat_blt(v___x_1929_, v___x_1930_);
if (v___x_1931_ == 0)
{
v___y_1924_ = v_as_1899_;
goto v___jp_1923_;
}
else
{
lean_object* v___x_1932_; 
v___x_1932_ = lean_array_fswap(v_as_1899_, v_lo_1900_, v_mid_1916_);
v___y_1924_ = v___x_1932_;
goto v___jp_1923_;
}
v___jp_1917_:
{
lean_object* v___x_1919_; lean_object* v___x_1920_; uint8_t v___x_1921_; 
v___x_1919_ = lean_array_fget_borrowed(v___y_1918_, v_mid_1916_);
v___x_1920_ = lean_array_fget_borrowed(v___y_1918_, v_hi_1901_);
v___x_1921_ = l_Nat_blt(v___x_1919_, v___x_1920_);
if (v___x_1921_ == 0)
{
lean_dec(v_mid_1916_);
v___y_1903_ = v___y_1918_;
goto v___jp_1902_;
}
else
{
lean_object* v___x_1922_; 
v___x_1922_ = lean_array_fswap(v___y_1918_, v_mid_1916_, v_hi_1901_);
lean_dec(v_mid_1916_);
v___y_1903_ = v___x_1922_;
goto v___jp_1902_;
}
}
v___jp_1923_:
{
lean_object* v___x_1925_; lean_object* v___x_1926_; uint8_t v___x_1927_; 
v___x_1925_ = lean_array_fget_borrowed(v___y_1924_, v_hi_1901_);
v___x_1926_ = lean_array_fget_borrowed(v___y_1924_, v_lo_1900_);
v___x_1927_ = l_Nat_blt(v___x_1925_, v___x_1926_);
if (v___x_1927_ == 0)
{
v___y_1918_ = v___y_1924_;
goto v___jp_1917_;
}
else
{
lean_object* v___x_1928_; 
v___x_1928_ = lean_array_fswap(v___y_1924_, v_lo_1900_, v_hi_1901_);
v___y_1918_ = v___x_1928_;
goto v___jp_1917_;
}
}
}
v___jp_1902_:
{
lean_object* v_pivot_1904_; lean_object* v___x_1905_; lean_object* v_fst_1906_; lean_object* v_snd_1907_; uint8_t v___x_1908_; 
v_pivot_1904_ = lean_array_fget(v___y_1903_, v_hi_1901_);
lean_inc_n(v_lo_1900_, 2);
v___x_1905_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11___redArg(v_hi_1901_, v_pivot_1904_, v___y_1903_, v_lo_1900_, v_lo_1900_);
lean_dec(v_pivot_1904_);
v_fst_1906_ = lean_ctor_get(v___x_1905_, 0);
lean_inc(v_fst_1906_);
v_snd_1907_ = lean_ctor_get(v___x_1905_, 1);
lean_inc(v_snd_1907_);
lean_dec_ref(v___x_1905_);
v___x_1908_ = lean_nat_dec_le(v_hi_1901_, v_fst_1906_);
if (v___x_1908_ == 0)
{
lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; 
v___x_1909_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg(v_n_1898_, v_snd_1907_, v_lo_1900_, v_fst_1906_);
v___x_1910_ = lean_unsigned_to_nat(1u);
v___x_1911_ = lean_nat_add(v_fst_1906_, v___x_1910_);
lean_dec(v_fst_1906_);
v_as_1899_ = v___x_1909_;
v_lo_1900_ = v___x_1911_;
goto _start;
}
else
{
lean_dec(v_fst_1906_);
lean_dec(v_lo_1900_);
return v_snd_1907_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg___boxed(lean_object* v_n_1933_, lean_object* v_as_1934_, lean_object* v_lo_1935_, lean_object* v_hi_1936_){
_start:
{
lean_object* v_res_1937_; 
v_res_1937_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg(v_n_1933_, v_as_1934_, v_lo_1935_, v_hi_1936_);
lean_dec(v_hi_1936_);
lean_dec(v_n_1933_);
return v_res_1937_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__6(lean_object* v_xs_1938_, lean_object* v_f_1939_, lean_object* v_x_1940_, lean_object* v_as_1941_, size_t v_i_1942_, size_t v_stop_1943_, lean_object* v_b_1944_){
_start:
{
lean_object* v___y_1946_; uint8_t v___x_1950_; 
v___x_1950_ = lean_usize_dec_eq(v_i_1942_, v_stop_1943_);
if (v___x_1950_ == 0)
{
lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; uint8_t v___x_1955_; 
v___x_1951_ = l_Lean_Elab_Structural_instInhabitedRecArgInfo_default;
v___x_1952_ = lean_array_uget_borrowed(v_as_1941_, v_i_1942_);
v___x_1953_ = lean_array_get_borrowed(v___x_1951_, v_xs_1938_, v___x_1952_);
lean_inc_ref(v_f_1939_);
lean_inc(v___x_1953_);
v___x_1954_ = lean_apply_1(v_f_1939_, v___x_1953_);
v___x_1955_ = lean_nat_dec_eq(v___x_1954_, v_x_1940_);
lean_dec(v___x_1954_);
if (v___x_1955_ == 0)
{
v___y_1946_ = v_b_1944_;
goto v___jp_1945_;
}
else
{
lean_object* v___x_1956_; 
lean_inc(v___x_1952_);
v___x_1956_ = lean_array_push(v_b_1944_, v___x_1952_);
v___y_1946_ = v___x_1956_;
goto v___jp_1945_;
}
}
else
{
lean_dec_ref(v_f_1939_);
return v_b_1944_;
}
v___jp_1945_:
{
size_t v___x_1947_; size_t v___x_1948_; 
v___x_1947_ = ((size_t)1ULL);
v___x_1948_ = lean_usize_add(v_i_1942_, v___x_1947_);
v_i_1942_ = v___x_1948_;
v_b_1944_ = v___y_1946_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__6___boxed(lean_object* v_xs_1957_, lean_object* v_f_1958_, lean_object* v_x_1959_, lean_object* v_as_1960_, lean_object* v_i_1961_, lean_object* v_stop_1962_, lean_object* v_b_1963_){
_start:
{
size_t v_i_boxed_1964_; size_t v_stop_boxed_1965_; lean_object* v_res_1966_; 
v_i_boxed_1964_ = lean_unbox_usize(v_i_1961_);
lean_dec(v_i_1961_);
v_stop_boxed_1965_ = lean_unbox_usize(v_stop_1962_);
lean_dec(v_stop_1962_);
v_res_1966_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__6(v_xs_1957_, v_f_1958_, v_x_1959_, v_as_1960_, v_i_boxed_1964_, v_stop_boxed_1965_, v_b_1963_);
lean_dec_ref(v_as_1960_);
lean_dec(v_x_1959_);
lean_dec_ref(v_xs_1957_);
return v_res_1966_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8(lean_object* v_xs_1969_, lean_object* v_f_1970_, size_t v_sz_1971_, size_t v_i_1972_, lean_object* v_bs_1973_){
_start:
{
uint8_t v___x_1974_; 
v___x_1974_ = lean_usize_dec_lt(v_i_1972_, v_sz_1971_);
if (v___x_1974_ == 0)
{
lean_dec_ref(v_f_1970_);
return v_bs_1973_;
}
else
{
lean_object* v_v_1975_; lean_object* v___x_1976_; lean_object* v_bs_x27_1977_; lean_object* v___y_1979_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; uint8_t v___x_1988_; 
v_v_1975_ = lean_array_uget(v_bs_1973_, v_i_1972_);
v___x_1976_ = lean_unsigned_to_nat(0u);
v_bs_x27_1977_ = lean_array_uset(v_bs_1973_, v_i_1972_, v___x_1976_);
v___x_1984_ = lean_array_get_size(v_xs_1969_);
v___x_1985_ = l_Array_range(v___x_1984_);
v___x_1986_ = lean_array_get_size(v___x_1985_);
v___x_1987_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8___closed__0));
v___x_1988_ = lean_nat_dec_lt(v___x_1976_, v___x_1986_);
if (v___x_1988_ == 0)
{
lean_dec_ref(v___x_1985_);
lean_dec(v_v_1975_);
v___y_1979_ = v___x_1987_;
goto v___jp_1978_;
}
else
{
size_t v___x_1989_; size_t v___x_1990_; lean_object* v___x_1991_; 
v___x_1989_ = ((size_t)0ULL);
v___x_1990_ = lean_usize_of_nat(v___x_1986_);
lean_inc_ref(v_f_1970_);
v___x_1991_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__6(v_xs_1969_, v_f_1970_, v_v_1975_, v___x_1985_, v___x_1989_, v___x_1990_, v___x_1987_);
lean_dec_ref(v___x_1985_);
lean_dec(v_v_1975_);
v___y_1979_ = v___x_1991_;
goto v___jp_1978_;
}
v___jp_1978_:
{
size_t v___x_1980_; size_t v___x_1981_; lean_object* v___x_1982_; 
v___x_1980_ = ((size_t)1ULL);
v___x_1981_ = lean_usize_add(v_i_1972_, v___x_1980_);
v___x_1982_ = lean_array_uset(v_bs_x27_1977_, v_i_1972_, v___y_1979_);
v_i_1972_ = v___x_1981_;
v_bs_1973_ = v___x_1982_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8___boxed(lean_object* v_xs_1992_, lean_object* v_f_1993_, lean_object* v_sz_1994_, lean_object* v_i_1995_, lean_object* v_bs_1996_){
_start:
{
size_t v_sz_boxed_1997_; size_t v_i_boxed_1998_; lean_object* v_res_1999_; 
v_sz_boxed_1997_ = lean_unbox_usize(v_sz_1994_);
lean_dec(v_sz_1994_);
v_i_boxed_1998_ = lean_unbox_usize(v_i_1995_);
lean_dec(v_i_1995_);
v_res_1999_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8(v_xs_1992_, v_f_1993_, v_sz_boxed_1997_, v_i_boxed_1998_, v_bs_1996_);
lean_dec_ref(v_xs_1992_);
return v_res_1999_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__11(lean_object* v_as_2000_, size_t v_i_2001_, size_t v_stop_2002_, lean_object* v_b_2003_){
_start:
{
uint8_t v___x_2004_; 
v___x_2004_ = lean_usize_dec_eq(v_i_2001_, v_stop_2002_);
if (v___x_2004_ == 0)
{
lean_object* v___x_2005_; lean_object* v___x_2006_; size_t v___x_2007_; size_t v___x_2008_; 
v___x_2005_ = lean_array_uget_borrowed(v_as_2000_, v_i_2001_);
v___x_2006_ = l_Array_append___redArg(v_b_2003_, v___x_2005_);
v___x_2007_ = ((size_t)1ULL);
v___x_2008_ = lean_usize_add(v_i_2001_, v___x_2007_);
v_i_2001_ = v___x_2008_;
v_b_2003_ = v___x_2006_;
goto _start;
}
else
{
return v_b_2003_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__11___boxed(lean_object* v_as_2010_, lean_object* v_i_2011_, lean_object* v_stop_2012_, lean_object* v_b_2013_){
_start:
{
size_t v_i_boxed_2014_; size_t v_stop_boxed_2015_; lean_object* v_res_2016_; 
v_i_boxed_2014_ = lean_unbox_usize(v_i_2011_);
lean_dec(v_i_2011_);
v_stop_boxed_2015_ = lean_unbox_usize(v_stop_2012_);
lean_dec(v_stop_2012_);
v_res_2016_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__11(v_as_2010_, v_i_boxed_2014_, v_stop_boxed_2015_, v_b_2013_);
lean_dec_ref(v_as_2010_);
return v_res_2016_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__7(lean_object* v_msg_2017_){
_start:
{
lean_object* v___x_2018_; lean_object* v___x_2019_; 
v___x_2018_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0);
v___x_2019_ = lean_panic_fn_borrowed(v___x_2018_, v_msg_2017_);
return v___x_2019_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9___redArg(lean_object* v_xs_2020_, lean_object* v_ys_2021_, lean_object* v_x_2022_){
_start:
{
lean_object* v_zero_2023_; uint8_t v_isZero_2024_; 
v_zero_2023_ = lean_unsigned_to_nat(0u);
v_isZero_2024_ = lean_nat_dec_eq(v_x_2022_, v_zero_2023_);
if (v_isZero_2024_ == 1)
{
lean_dec(v_x_2022_);
return v_isZero_2024_;
}
else
{
lean_object* v_one_2025_; lean_object* v_n_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; uint8_t v___x_2029_; 
v_one_2025_ = lean_unsigned_to_nat(1u);
v_n_2026_ = lean_nat_sub(v_x_2022_, v_one_2025_);
lean_dec(v_x_2022_);
v___x_2027_ = lean_array_fget_borrowed(v_xs_2020_, v_n_2026_);
v___x_2028_ = lean_array_fget_borrowed(v_ys_2021_, v_n_2026_);
v___x_2029_ = lean_nat_dec_eq(v___x_2027_, v___x_2028_);
if (v___x_2029_ == 0)
{
lean_dec(v_n_2026_);
return v___x_2029_;
}
else
{
v_x_2022_ = v_n_2026_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9___redArg___boxed(lean_object* v_xs_2031_, lean_object* v_ys_2032_, lean_object* v_x_2033_){
_start:
{
uint8_t v_res_2034_; lean_object* v_r_2035_; 
v_res_2034_ = l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9___redArg(v_xs_2031_, v_ys_2032_, v_x_2033_);
lean_dec_ref(v_ys_2032_);
lean_dec_ref(v_xs_2031_);
v_r_2035_ = lean_box(v_res_2034_);
return v_r_2035_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__2(void){
_start:
{
lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; 
v___x_2038_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__1));
v___x_2039_ = lean_unsigned_to_nat(2u);
v___x_2040_ = lean_unsigned_to_nat(63u);
v___x_2041_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__0));
v___x_2042_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__0));
v___x_2043_ = l_mkPanicMessageWithDecl(v___x_2042_, v___x_2041_, v___x_2040_, v___x_2039_, v___x_2038_);
return v___x_2043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5(lean_object* v_f_2046_, lean_object* v_xs_2047_, lean_object* v_ys_2048_){
_start:
{
size_t v_sz_2052_; size_t v___x_2053_; lean_object* v_positions_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___y_2058_; lean_object* v___y_2064_; lean_object* v___y_2065_; lean_object* v___y_2066_; lean_object* v___y_2067_; lean_object* v___y_2070_; lean_object* v___y_2071_; lean_object* v___y_2072_; lean_object* v___y_2073_; lean_object* v___y_2076_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; uint8_t v___x_2086_; 
v_sz_2052_ = lean_array_size(v_ys_2048_);
v___x_2053_ = ((size_t)0ULL);
v_positions_2054_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8(v_xs_2047_, v_f_2046_, v_sz_2052_, v___x_2053_, v_ys_2048_);
v___x_2055_ = lean_array_get_size(v_xs_2047_);
v___x_2056_ = l_Array_range(v___x_2055_);
v___x_2083_ = lean_unsigned_to_nat(0u);
v___x_2084_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__3));
v___x_2085_ = lean_array_get_size(v_positions_2054_);
v___x_2086_ = lean_nat_dec_lt(v___x_2083_, v___x_2085_);
if (v___x_2086_ == 0)
{
v___y_2076_ = v___x_2084_;
goto v___jp_2075_;
}
else
{
size_t v___x_2087_; lean_object* v___x_2088_; 
v___x_2087_ = lean_usize_of_nat(v___x_2085_);
v___x_2088_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__11(v_positions_2054_, v___x_2053_, v___x_2087_, v___x_2084_);
v___y_2076_ = v___x_2088_;
goto v___jp_2075_;
}
v___jp_2049_:
{
lean_object* v___x_2050_; lean_object* v___x_2051_; 
v___x_2050_ = lean_obj_once(&l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__2, &l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__2_once, _init_l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__2);
v___x_2051_ = l_panic___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__7(v___x_2050_);
return v___x_2051_;
}
v___jp_2057_:
{
lean_object* v___x_2059_; lean_object* v___x_2060_; uint8_t v___x_2061_; 
v___x_2059_ = lean_array_get_size(v___x_2056_);
v___x_2060_ = lean_array_get_size(v___y_2058_);
v___x_2061_ = lean_nat_dec_eq(v___x_2059_, v___x_2060_);
if (v___x_2061_ == 0)
{
lean_dec_ref(v___y_2058_);
lean_dec_ref(v___x_2056_);
lean_dec_ref(v_positions_2054_);
goto v___jp_2049_;
}
else
{
uint8_t v___x_2062_; 
v___x_2062_ = l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9___redArg(v___x_2056_, v___y_2058_, v___x_2059_);
lean_dec_ref(v___y_2058_);
lean_dec_ref(v___x_2056_);
if (v___x_2062_ == 0)
{
lean_dec_ref(v_positions_2054_);
goto v___jp_2049_;
}
else
{
return v_positions_2054_;
}
}
}
v___jp_2063_:
{
lean_object* v___x_2068_; 
v___x_2068_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg(v___y_2066_, v___y_2065_, v___y_2064_, v___y_2067_);
lean_dec(v___y_2067_);
lean_dec(v___y_2066_);
v___y_2058_ = v___x_2068_;
goto v___jp_2057_;
}
v___jp_2069_:
{
uint8_t v___x_2074_; 
v___x_2074_ = lean_nat_dec_le(v___y_2073_, v___y_2070_);
if (v___x_2074_ == 0)
{
lean_dec(v___y_2070_);
lean_inc(v___y_2073_);
v___y_2064_ = v___y_2073_;
v___y_2065_ = v___y_2071_;
v___y_2066_ = v___y_2072_;
v___y_2067_ = v___y_2073_;
goto v___jp_2063_;
}
else
{
v___y_2064_ = v___y_2073_;
v___y_2065_ = v___y_2071_;
v___y_2066_ = v___y_2072_;
v___y_2067_ = v___y_2070_;
goto v___jp_2063_;
}
}
v___jp_2075_:
{
lean_object* v___x_2077_; lean_object* v___x_2078_; uint8_t v___x_2079_; 
v___x_2077_ = lean_array_get_size(v___y_2076_);
v___x_2078_ = lean_unsigned_to_nat(0u);
v___x_2079_ = lean_nat_dec_eq(v___x_2077_, v___x_2078_);
if (v___x_2079_ == 0)
{
lean_object* v___x_2080_; lean_object* v___x_2081_; uint8_t v___x_2082_; 
v___x_2080_ = lean_unsigned_to_nat(1u);
v___x_2081_ = lean_nat_sub(v___x_2077_, v___x_2080_);
v___x_2082_ = lean_nat_dec_le(v___x_2078_, v___x_2081_);
if (v___x_2082_ == 0)
{
lean_inc(v___x_2081_);
v___y_2070_ = v___x_2081_;
v___y_2071_ = v___y_2076_;
v___y_2072_ = v___x_2077_;
v___y_2073_ = v___x_2081_;
goto v___jp_2069_;
}
else
{
v___y_2070_ = v___x_2081_;
v___y_2071_ = v___y_2076_;
v___y_2072_ = v___x_2077_;
v___y_2073_ = v___x_2078_;
goto v___jp_2069_;
}
}
else
{
v___y_2058_ = v___y_2076_;
goto v___jp_2057_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___boxed(lean_object* v_f_2089_, lean_object* v_xs_2090_, lean_object* v_ys_2091_){
_start:
{
lean_object* v_res_2092_; 
v_res_2092_ = l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5(v_f_2089_, v_xs_2090_, v_ys_2091_);
lean_dec_ref(v_xs_2090_);
return v_res_2092_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__9(void){
_start:
{
lean_object* v___x_2107_; lean_object* v___x_2108_; 
v___x_2107_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__8));
v___x_2108_ = l_Lean_stringToMessageData(v___x_2107_);
return v___x_2108_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__11(void){
_start:
{
lean_object* v___x_2110_; lean_object* v___x_2111_; 
v___x_2110_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__10));
v___x_2111_ = l_Lean_stringToMessageData(v___x_2110_);
return v___x_2111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion(lean_object* v_preDefs_2112_, lean_object* v_fixedParamPerms_2113_, lean_object* v_xs_2114_, lean_object* v_recArgInfos_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_){
_start:
{
lean_object* v___f_2121_; lean_object* v___f_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; size_t v_sz_2126_; size_t v___x_2127_; lean_object* v___x_2128_; 
v___f_2121_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__0));
v___f_2122_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__1));
v___x_2123_ = lean_box(0);
v___x_2124_ = l_Lean_Elab_Structural_instInhabitedRecArgInfo_default;
v___x_2125_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v_sz_2126_ = lean_array_size(v_preDefs_2112_);
v___x_2127_ = ((size_t)0ULL);
lean_inc_ref(v_preDefs_2112_);
lean_inc_ref(v_xs_2114_);
v___x_2128_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___redArg(v_fixedParamPerms_2113_, v_xs_2114_, v_sz_2126_, v___x_2127_, v_preDefs_2112_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_);
if (lean_obj_tag(v___x_2128_) == 0)
{
lean_object* v_a_2129_; lean_object* v___x_2130_; 
v_a_2129_ = lean_ctor_get(v___x_2128_, 0);
lean_inc(v_a_2129_);
lean_dec_ref_known(v___x_2128_, 1);
lean_inc_ref(v_preDefs_2112_);
lean_inc_ref(v_xs_2114_);
v___x_2130_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___redArg(v_fixedParamPerms_2113_, v_xs_2114_, v_sz_2126_, v___x_2127_, v_preDefs_2112_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_);
if (lean_obj_tag(v___x_2130_) == 0)
{
lean_object* v_a_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v_indGroupInst_2134_; lean_object* v_toIndGroupInfo_2135_; lean_object* v_all_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2220_; 
v_a_2131_ = lean_ctor_get(v___x_2130_, 0);
lean_inc(v_a_2131_);
lean_dec_ref_known(v___x_2130_, 1);
v___x_2132_ = lean_unsigned_to_nat(0u);
v___x_2133_ = lean_array_get_borrowed(v___x_2124_, v_recArgInfos_2115_, v___x_2132_);
v_indGroupInst_2134_ = lean_ctor_get(v___x_2133_, 4);
v_toIndGroupInfo_2135_ = lean_ctor_get(v_indGroupInst_2134_, 0);
lean_inc_ref(v_toIndGroupInfo_2135_);
v_all_2136_ = lean_ctor_get(v_toIndGroupInfo_2135_, 0);
v_isSharedCheck_2220_ = !lean_is_exclusive(v_toIndGroupInfo_2135_);
if (v_isSharedCheck_2220_ == 0)
{
lean_object* v_unused_2221_; 
v_unused_2221_ = lean_ctor_get(v_toIndGroupInfo_2135_, 1);
lean_dec(v_unused_2221_);
v___x_2138_ = v_toIndGroupInfo_2135_;
v_isShared_2139_ = v_isSharedCheck_2220_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_all_2136_);
lean_dec(v_toIndGroupInfo_2135_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2220_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v___x_2140_; lean_object* v___x_2141_; 
v___x_2140_ = lean_array_get(v___x_2123_, v_all_2136_, v___x_2132_);
lean_dec_ref(v_all_2136_);
v___x_2141_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4(v___x_2140_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_);
if (lean_obj_tag(v___x_2141_) == 0)
{
lean_object* v_a_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___f_2147_; lean_object* v___y_2149_; lean_object* v___y_2150_; lean_object* v___y_2151_; lean_object* v___y_2152_; lean_object* v___x_2186_; lean_object* v_a_2187_; uint8_t v___x_2188_; 
v_a_2142_ = lean_ctor_get(v___x_2141_, 0);
lean_inc(v_a_2142_);
lean_dec_ref_known(v___x_2141_, 1);
v___x_2143_ = l_Lean_InductiveVal_numTypeFormers(v_a_2142_);
v___x_2144_ = l_Array_range(v___x_2143_);
v___x_2145_ = l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5(v___f_2122_, v_recArgInfos_2115_, v___x_2144_);
v___x_2146_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__5));
v___f_2147_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__6));
v___x_2186_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1(v___x_2146_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_);
v_a_2187_ = lean_ctor_get(v___x_2186_, 0);
lean_inc(v_a_2187_);
lean_dec_ref(v___x_2186_);
v___x_2188_ = lean_unbox(v_a_2187_);
lean_dec(v_a_2187_);
if (v___x_2188_ == 0)
{
lean_del_object(v___x_2138_);
v___y_2149_ = v_a_2116_;
v___y_2150_ = v_a_2117_;
v___y_2151_ = v_a_2118_;
v___y_2152_ = v_a_2119_;
goto v___jp_2148_;
}
else
{
lean_object* v_toConstantVal_2189_; lean_object* v_name_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2194_; 
v_toConstantVal_2189_ = lean_ctor_get(v_a_2142_, 0);
v_name_2190_ = lean_ctor_get(v_toConstantVal_2189_, 0);
v___x_2191_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__9, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__9_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__9);
lean_inc(v_name_2190_);
v___x_2192_ = l_Lean_MessageData_ofName(v_name_2190_);
if (v_isShared_2139_ == 0)
{
lean_ctor_set_tag(v___x_2138_, 7);
lean_ctor_set(v___x_2138_, 1, v___x_2192_);
lean_ctor_set(v___x_2138_, 0, v___x_2191_);
v___x_2194_ = v___x_2138_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v___x_2191_);
lean_ctor_set(v_reuseFailAlloc_2211_, 1, v___x_2192_);
v___x_2194_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2193_;
}
v_reusejp_2193_:
{
lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; 
v___x_2195_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__11, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__11_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__11);
v___x_2196_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2196_, 0, v___x_2194_);
lean_ctor_set(v___x_2196_, 1, v___x_2195_);
lean_inc_ref(v___x_2145_);
v___x_2197_ = lean_array_to_list(v___x_2145_);
v___x_2198_ = lean_box(0);
v___x_2199_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__21(v___x_2197_, v___x_2198_);
v___x_2200_ = l_Lean_MessageData_ofList(v___x_2199_);
v___x_2201_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2201_, 0, v___x_2196_);
lean_ctor_set(v___x_2201_, 1, v___x_2200_);
v___x_2202_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_2146_, v___x_2201_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_);
if (lean_obj_tag(v___x_2202_) == 0)
{
lean_dec_ref_known(v___x_2202_, 1);
v___y_2149_ = v_a_2116_;
v___y_2150_ = v_a_2117_;
v___y_2151_ = v_a_2118_;
v___y_2152_ = v_a_2119_;
goto v___jp_2148_;
}
else
{
lean_object* v_a_2203_; lean_object* v___x_2205_; uint8_t v_isShared_2206_; uint8_t v_isSharedCheck_2210_; 
lean_dec_ref(v___x_2145_);
lean_dec(v_a_2142_);
lean_dec(v_a_2131_);
lean_dec(v_a_2129_);
lean_dec_ref(v_recArgInfos_2115_);
lean_dec_ref(v_xs_2114_);
lean_dec_ref(v_fixedParamPerms_2113_);
lean_dec_ref(v_preDefs_2112_);
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
}
}
v___jp_2148_:
{
lean_object* v_toConstantVal_2153_; lean_object* v_numIndices_2154_; lean_object* v_name_2155_; lean_object* v___x_2156_; 
v_toConstantVal_2153_ = lean_ctor_get(v_a_2142_, 0);
lean_inc_ref(v_toConstantVal_2153_);
v_numIndices_2154_ = lean_ctor_get(v_a_2142_, 2);
lean_inc(v_numIndices_2154_);
lean_dec(v_a_2142_);
v_name_2155_ = lean_ctor_get(v_toConstantVal_2153_, 0);
lean_inc(v_name_2155_);
lean_dec_ref(v_toConstantVal_2153_);
v___x_2156_ = l_Lean_Meta_isInductivePredicate(v_name_2155_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_);
if (lean_obj_tag(v___x_2156_) == 0)
{
lean_object* v_a_2157_; lean_object* v___x_2158_; lean_object* v___f_2159_; uint8_t v___x_2160_; 
v_a_2157_ = lean_ctor_get(v___x_2156_, 0);
lean_inc_n(v_a_2157_, 2);
lean_dec_ref_known(v___x_2156_, 1);
v___x_2158_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___boxed__const__1));
lean_inc(v_numIndices_2154_);
lean_inc_ref(v_preDefs_2112_);
lean_inc_ref(v_xs_2114_);
lean_inc_ref(v_fixedParamPerms_2113_);
lean_inc_ref(v___x_2145_);
lean_inc(v_a_2129_);
lean_inc_ref(v_recArgInfos_2115_);
v___f_2159_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___boxed), 21, 14);
lean_closure_set(v___f_2159_, 0, v_recArgInfos_2115_);
lean_closure_set(v___f_2159_, 1, v_a_2129_);
lean_closure_set(v___f_2159_, 2, v___x_2145_);
lean_closure_set(v___f_2159_, 3, v___x_2158_);
lean_closure_set(v___f_2159_, 4, v_fixedParamPerms_2113_);
lean_closure_set(v___f_2159_, 5, v_xs_2114_);
lean_closure_set(v___f_2159_, 6, v___x_2132_);
lean_closure_set(v___f_2159_, 7, v_preDefs_2112_);
lean_closure_set(v___f_2159_, 8, v_numIndices_2154_);
lean_closure_set(v___f_2159_, 9, v___f_2121_);
lean_closure_set(v___f_2159_, 10, v___x_2146_);
lean_closure_set(v___f_2159_, 11, v_a_2157_);
lean_closure_set(v___f_2159_, 12, v___x_2125_);
lean_closure_set(v___f_2159_, 13, v___f_2147_);
v___x_2160_ = lean_unbox(v_a_2157_);
if (v___x_2160_ == 0)
{
size_t v_sz_2161_; lean_object* v___x_2162_; 
lean_dec_ref(v___f_2159_);
v_sz_2161_ = lean_array_size(v_recArgInfos_2115_);
lean_inc_ref(v_recArgInfos_2115_);
v___x_2162_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__20___redArg(v_a_2129_, v_a_2131_, v_sz_2161_, v___x_2127_, v_recArgInfos_2115_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_);
lean_dec(v_a_2131_);
if (lean_obj_tag(v___x_2162_) == 0)
{
lean_object* v_a_2163_; lean_object* v___x_2164_; uint8_t v___x_2165_; lean_object* v___x_2166_; 
v_a_2163_ = lean_ctor_get(v___x_2162_, 0);
lean_inc(v_a_2163_);
lean_dec_ref_known(v___x_2162_, 1);
v___x_2164_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__7));
v___x_2165_ = lean_unbox(v_a_2157_);
lean_dec(v_a_2157_);
v___x_2166_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2(v_recArgInfos_2115_, v_a_2129_, v___x_2145_, v___x_2127_, v_fixedParamPerms_2113_, v_xs_2114_, v___x_2132_, v_preDefs_2112_, v_numIndices_2154_, v___f_2121_, v___x_2146_, v___x_2165_, v___x_2125_, v___f_2147_, v___x_2164_, v_a_2163_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_);
lean_dec(v_numIndices_2154_);
lean_dec(v_a_2129_);
return v___x_2166_;
}
else
{
lean_object* v_a_2167_; lean_object* v___x_2169_; uint8_t v_isShared_2170_; uint8_t v_isSharedCheck_2174_; 
lean_dec(v_a_2157_);
lean_dec(v_numIndices_2154_);
lean_dec_ref(v___x_2145_);
lean_dec(v_a_2129_);
lean_dec_ref(v_recArgInfos_2115_);
lean_dec_ref(v_xs_2114_);
lean_dec_ref(v_fixedParamPerms_2113_);
lean_dec_ref(v_preDefs_2112_);
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
lean_object* v___x_2175_; lean_object* v___f_2176_; lean_object* v___x_2177_; 
lean_dec(v_a_2157_);
lean_dec(v_numIndices_2154_);
lean_dec_ref(v___x_2145_);
lean_dec(v_a_2131_);
lean_dec_ref(v_xs_2114_);
lean_dec_ref(v_fixedParamPerms_2113_);
lean_dec_ref(v_preDefs_2112_);
v___x_2175_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___boxed__const__1));
lean_inc(v_a_2129_);
v___f_2176_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__3___boxed), 10, 4);
lean_closure_set(v___f_2176_, 0, v_recArgInfos_2115_);
lean_closure_set(v___f_2176_, 1, v_a_2129_);
lean_closure_set(v___f_2176_, 2, v___x_2175_);
lean_closure_set(v___f_2176_, 3, v___f_2159_);
v___x_2177_ = l_Lean_Elab_Structural_withFunTypes___redArg(v_a_2129_, v___f_2176_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_);
return v___x_2177_;
}
}
else
{
lean_object* v_a_2178_; lean_object* v___x_2180_; uint8_t v_isShared_2181_; uint8_t v_isSharedCheck_2185_; 
lean_dec(v_numIndices_2154_);
lean_dec_ref(v___x_2145_);
lean_dec(v_a_2131_);
lean_dec(v_a_2129_);
lean_dec_ref(v_recArgInfos_2115_);
lean_dec_ref(v_xs_2114_);
lean_dec_ref(v_fixedParamPerms_2113_);
lean_dec_ref(v_preDefs_2112_);
v_a_2178_ = lean_ctor_get(v___x_2156_, 0);
v_isSharedCheck_2185_ = !lean_is_exclusive(v___x_2156_);
if (v_isSharedCheck_2185_ == 0)
{
v___x_2180_ = v___x_2156_;
v_isShared_2181_ = v_isSharedCheck_2185_;
goto v_resetjp_2179_;
}
else
{
lean_inc(v_a_2178_);
lean_dec(v___x_2156_);
v___x_2180_ = lean_box(0);
v_isShared_2181_ = v_isSharedCheck_2185_;
goto v_resetjp_2179_;
}
v_resetjp_2179_:
{
lean_object* v___x_2183_; 
if (v_isShared_2181_ == 0)
{
v___x_2183_ = v___x_2180_;
goto v_reusejp_2182_;
}
else
{
lean_object* v_reuseFailAlloc_2184_; 
v_reuseFailAlloc_2184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2184_, 0, v_a_2178_);
v___x_2183_ = v_reuseFailAlloc_2184_;
goto v_reusejp_2182_;
}
v_reusejp_2182_:
{
return v___x_2183_;
}
}
}
}
}
else
{
lean_object* v_a_2212_; lean_object* v___x_2214_; uint8_t v_isShared_2215_; uint8_t v_isSharedCheck_2219_; 
lean_del_object(v___x_2138_);
lean_dec(v_a_2131_);
lean_dec(v_a_2129_);
lean_dec_ref(v_recArgInfos_2115_);
lean_dec_ref(v_xs_2114_);
lean_dec_ref(v_fixedParamPerms_2113_);
lean_dec_ref(v_preDefs_2112_);
v_a_2212_ = lean_ctor_get(v___x_2141_, 0);
v_isSharedCheck_2219_ = !lean_is_exclusive(v___x_2141_);
if (v_isSharedCheck_2219_ == 0)
{
v___x_2214_ = v___x_2141_;
v_isShared_2215_ = v_isSharedCheck_2219_;
goto v_resetjp_2213_;
}
else
{
lean_inc(v_a_2212_);
lean_dec(v___x_2141_);
v___x_2214_ = lean_box(0);
v_isShared_2215_ = v_isSharedCheck_2219_;
goto v_resetjp_2213_;
}
v_resetjp_2213_:
{
lean_object* v___x_2217_; 
if (v_isShared_2215_ == 0)
{
v___x_2217_ = v___x_2214_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v_a_2212_);
v___x_2217_ = v_reuseFailAlloc_2218_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
return v___x_2217_;
}
}
}
}
}
else
{
lean_object* v_a_2222_; lean_object* v___x_2224_; uint8_t v_isShared_2225_; uint8_t v_isSharedCheck_2229_; 
lean_dec(v_a_2129_);
lean_dec_ref(v_recArgInfos_2115_);
lean_dec_ref(v_xs_2114_);
lean_dec_ref(v_fixedParamPerms_2113_);
lean_dec_ref(v_preDefs_2112_);
v_a_2222_ = lean_ctor_get(v___x_2130_, 0);
v_isSharedCheck_2229_ = !lean_is_exclusive(v___x_2130_);
if (v_isSharedCheck_2229_ == 0)
{
v___x_2224_ = v___x_2130_;
v_isShared_2225_ = v_isSharedCheck_2229_;
goto v_resetjp_2223_;
}
else
{
lean_inc(v_a_2222_);
lean_dec(v___x_2130_);
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
lean_dec_ref(v_recArgInfos_2115_);
lean_dec_ref(v_xs_2114_);
lean_dec_ref(v_fixedParamPerms_2113_);
lean_dec_ref(v_preDefs_2112_);
v_a_2230_ = lean_ctor_get(v___x_2128_, 0);
v_isSharedCheck_2237_ = !lean_is_exclusive(v___x_2128_);
if (v_isSharedCheck_2237_ == 0)
{
v___x_2232_ = v___x_2128_;
v_isShared_2233_ = v_isSharedCheck_2237_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_a_2230_);
lean_dec(v___x_2128_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___boxed(lean_object* v_preDefs_2238_, lean_object* v_fixedParamPerms_2239_, lean_object* v_xs_2240_, lean_object* v_recArgInfos_2241_, lean_object* v_a_2242_, lean_object* v_a_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_, lean_object* v_a_2246_){
_start:
{
lean_object* v_res_2247_; 
v_res_2247_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion(v_preDefs_2238_, v_fixedParamPerms_2239_, v_xs_2240_, v_recArgInfos_2241_, v_a_2242_, v_a_2243_, v_a_2244_, v_a_2245_);
lean_dec(v_a_2245_);
lean_dec_ref(v_a_2244_);
lean_dec(v_a_2243_);
lean_dec_ref(v_a_2242_);
return v_res_2247_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2(lean_object* v_fixedParamPerms_2248_, lean_object* v_xs_2249_, lean_object* v_as_2250_, size_t v_sz_2251_, size_t v_i_2252_, lean_object* v_bs_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_){
_start:
{
lean_object* v___x_2259_; 
v___x_2259_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___redArg(v_fixedParamPerms_2248_, v_xs_2249_, v_sz_2251_, v_i_2252_, v_bs_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_);
return v___x_2259_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___boxed(lean_object* v_fixedParamPerms_2260_, lean_object* v_xs_2261_, lean_object* v_as_2262_, lean_object* v_sz_2263_, lean_object* v_i_2264_, lean_object* v_bs_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_){
_start:
{
size_t v_sz_boxed_2271_; size_t v_i_boxed_2272_; lean_object* v_res_2273_; 
v_sz_boxed_2271_ = lean_unbox_usize(v_sz_2263_);
lean_dec(v_sz_2263_);
v_i_boxed_2272_ = lean_unbox_usize(v_i_2264_);
lean_dec(v_i_2264_);
v_res_2273_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2(v_fixedParamPerms_2260_, v_xs_2261_, v_as_2262_, v_sz_boxed_2271_, v_i_boxed_2272_, v_bs_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_);
lean_dec(v___y_2269_);
lean_dec_ref(v___y_2268_);
lean_dec(v___y_2267_);
lean_dec_ref(v___y_2266_);
lean_dec_ref(v_as_2262_);
lean_dec_ref(v_fixedParamPerms_2260_);
return v_res_2273_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3(lean_object* v_fixedParamPerms_2274_, lean_object* v_xs_2275_, lean_object* v_as_2276_, size_t v_sz_2277_, size_t v_i_2278_, lean_object* v_bs_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_){
_start:
{
lean_object* v___x_2285_; 
v___x_2285_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___redArg(v_fixedParamPerms_2274_, v_xs_2275_, v_sz_2277_, v_i_2278_, v_bs_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_);
return v___x_2285_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___boxed(lean_object* v_fixedParamPerms_2286_, lean_object* v_xs_2287_, lean_object* v_as_2288_, lean_object* v_sz_2289_, lean_object* v_i_2290_, lean_object* v_bs_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_){
_start:
{
size_t v_sz_boxed_2297_; size_t v_i_boxed_2298_; lean_object* v_res_2299_; 
v_sz_boxed_2297_ = lean_unbox_usize(v_sz_2289_);
lean_dec(v_sz_2289_);
v_i_boxed_2298_ = lean_unbox_usize(v_i_2290_);
lean_dec(v_i_2290_);
v_res_2299_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3(v_fixedParamPerms_2286_, v_xs_2287_, v_as_2288_, v_sz_boxed_2297_, v_i_boxed_2298_, v_bs_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_);
lean_dec(v___y_2295_);
lean_dec_ref(v___y_2294_);
lean_dec(v___y_2293_);
lean_dec_ref(v___y_2292_);
lean_dec_ref(v_as_2288_);
lean_dec_ref(v_fixedParamPerms_2286_);
return v_res_2299_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14(lean_object* v_00_u03b3_2300_, lean_object* v_msg_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_){
_start:
{
lean_object* v___x_2307_; 
v___x_2307_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg(v_msg_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_);
return v___x_2307_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___boxed(lean_object* v_00_u03b3_2308_, lean_object* v_msg_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_){
_start:
{
lean_object* v_res_2315_; 
v_res_2315_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14(v_00_u03b3_2308_, v_msg_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_);
lean_dec(v___y_2313_);
lean_dec_ref(v___y_2312_);
lean_dec(v___y_2311_);
lean_dec_ref(v___y_2310_);
return v_res_2315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6(lean_object* v_00_u03b3_2316_, lean_object* v_00_u03b1_2317_, lean_object* v_f_2318_, lean_object* v_positions_2319_, lean_object* v_ys_2320_, lean_object* v_xs_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_){
_start:
{
lean_object* v___x_2327_; 
v___x_2327_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg(v_f_2318_, v_positions_2319_, v_ys_2320_, v_xs_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_);
return v___x_2327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___boxed(lean_object* v_00_u03b3_2328_, lean_object* v_00_u03b1_2329_, lean_object* v_f_2330_, lean_object* v_positions_2331_, lean_object* v_ys_2332_, lean_object* v_xs_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_){
_start:
{
lean_object* v_res_2339_; 
v_res_2339_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6(v_00_u03b3_2328_, v_00_u03b1_2329_, v_f_2330_, v_positions_2331_, v_ys_2332_, v_xs_2333_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_);
lean_dec(v___y_2337_);
lean_dec_ref(v___y_2336_);
lean_dec(v___y_2335_);
lean_dec_ref(v___y_2334_);
lean_dec_ref(v_xs_2333_);
lean_dec_ref(v_ys_2332_);
lean_dec_ref(v_positions_2331_);
return v_res_2339_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7(lean_object* v___x_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_, lean_object* v_funTypes_2343_, lean_object* v_as_2344_, size_t v_sz_2345_, size_t v_i_2346_, lean_object* v_bs_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_){
_start:
{
lean_object* v___x_2353_; 
v___x_2353_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg(v___x_2340_, v_a_2341_, v_a_2342_, v_funTypes_2343_, v_sz_2345_, v_i_2346_, v_bs_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_);
return v___x_2353_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___boxed(lean_object* v___x_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_, lean_object* v_funTypes_2357_, lean_object* v_as_2358_, lean_object* v_sz_2359_, lean_object* v_i_2360_, lean_object* v_bs_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_){
_start:
{
size_t v_sz_boxed_2367_; size_t v_i_boxed_2368_; lean_object* v_res_2369_; 
v_sz_boxed_2367_ = lean_unbox_usize(v_sz_2359_);
lean_dec(v_sz_2359_);
v_i_boxed_2368_ = lean_unbox_usize(v_i_2360_);
lean_dec(v_i_2360_);
v_res_2369_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7(v___x_2354_, v_a_2355_, v_a_2356_, v_funTypes_2357_, v_as_2358_, v_sz_boxed_2367_, v_i_boxed_2368_, v_bs_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_);
lean_dec(v___y_2365_);
lean_dec_ref(v___y_2364_);
lean_dec(v___y_2363_);
lean_dec_ref(v___y_2362_);
lean_dec_ref(v_as_2358_);
return v_res_2369_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8(lean_object* v_fixedParamPerms_2370_, lean_object* v_xs_2371_, lean_object* v_as_2372_, size_t v_sz_2373_, size_t v_i_2374_, lean_object* v_bs_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_){
_start:
{
lean_object* v___x_2381_; 
v___x_2381_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg(v_fixedParamPerms_2370_, v_xs_2371_, v_sz_2373_, v_i_2374_, v_bs_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_);
return v___x_2381_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___boxed(lean_object* v_fixedParamPerms_2382_, lean_object* v_xs_2383_, lean_object* v_as_2384_, lean_object* v_sz_2385_, lean_object* v_i_2386_, lean_object* v_bs_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_){
_start:
{
size_t v_sz_boxed_2393_; size_t v_i_boxed_2394_; lean_object* v_res_2395_; 
v_sz_boxed_2393_ = lean_unbox_usize(v_sz_2385_);
lean_dec(v_sz_2385_);
v_i_boxed_2394_ = lean_unbox_usize(v_i_2386_);
lean_dec(v_i_2386_);
v_res_2395_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8(v_fixedParamPerms_2382_, v_xs_2383_, v_as_2384_, v_sz_boxed_2393_, v_i_boxed_2394_, v_bs_2387_, v___y_2388_, v___y_2389_, v___y_2390_, v___y_2391_);
lean_dec(v___y_2391_);
lean_dec_ref(v___y_2390_);
lean_dec(v___y_2389_);
lean_dec_ref(v___y_2388_);
lean_dec_ref(v_as_2384_);
return v_res_2395_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12(lean_object* v_00_u03b1_2396_, lean_object* v_preDefs_2397_, lean_object* v_k_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_){
_start:
{
lean_object* v___x_2404_; 
v___x_2404_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v_preDefs_2397_, v_k_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_);
return v___x_2404_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___boxed(lean_object* v_00_u03b1_2405_, lean_object* v_preDefs_2406_, lean_object* v_k_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_){
_start:
{
lean_object* v_res_2413_; 
v_res_2413_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12(v_00_u03b1_2405_, v_preDefs_2406_, v_k_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_);
lean_dec(v___y_2411_);
lean_dec_ref(v___y_2410_);
lean_dec(v___y_2409_);
lean_dec_ref(v___y_2408_);
return v_res_2413_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14(uint8_t v_a_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_, lean_object* v_recArgInfos_2417_, lean_object* v___x_2418_, lean_object* v_preDefs_2419_, lean_object* v_a_2420_, lean_object* v_as_2421_, size_t v_sz_2422_, size_t v_i_2423_, lean_object* v_bs_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_){
_start:
{
lean_object* v___x_2430_; 
v___x_2430_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg(v_a_2414_, v_a_2415_, v_a_2416_, v_recArgInfos_2417_, v___x_2418_, v_preDefs_2419_, v_a_2420_, v_sz_2422_, v_i_2423_, v_bs_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_);
return v___x_2430_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___boxed(lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_recArgInfos_2434_, lean_object* v___x_2435_, lean_object* v_preDefs_2436_, lean_object* v_a_2437_, lean_object* v_as_2438_, lean_object* v_sz_2439_, lean_object* v_i_2440_, lean_object* v_bs_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_){
_start:
{
uint8_t v_a_29162__boxed_2447_; size_t v_sz_boxed_2448_; size_t v_i_boxed_2449_; lean_object* v_res_2450_; 
v_a_29162__boxed_2447_ = lean_unbox(v_a_2431_);
v_sz_boxed_2448_ = lean_unbox_usize(v_sz_2439_);
lean_dec(v_sz_2439_);
v_i_boxed_2449_ = lean_unbox_usize(v_i_2440_);
lean_dec(v_i_2440_);
v_res_2450_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14(v_a_29162__boxed_2447_, v_a_2432_, v_a_2433_, v_recArgInfos_2434_, v___x_2435_, v_preDefs_2436_, v_a_2437_, v_as_2438_, v_sz_boxed_2448_, v_i_boxed_2449_, v_bs_2441_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_);
lean_dec(v___y_2445_);
lean_dec_ref(v___y_2444_);
lean_dec(v___y_2443_);
lean_dec_ref(v___y_2442_);
lean_dec_ref(v_as_2438_);
lean_dec_ref(v_a_2433_);
lean_dec_ref(v_a_2432_);
return v_res_2450_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17_spec__30(lean_object* v_declName_2451_, uint8_t v_s_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_){
_start:
{
lean_object* v___x_2458_; 
v___x_2458_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17_spec__30___redArg(v_declName_2451_, v_s_2452_, v___y_2454_, v___y_2456_);
return v___x_2458_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17_spec__30___boxed(lean_object* v_declName_2459_, lean_object* v_s_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_){
_start:
{
uint8_t v_s_boxed_2466_; lean_object* v_res_2467_; 
v_s_boxed_2466_ = lean_unbox(v_s_2460_);
v_res_2467_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17_spec__30(v_declName_2459_, v_s_boxed_2466_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_);
lean_dec(v___y_2464_);
lean_dec_ref(v___y_2463_);
lean_dec(v___y_2462_);
lean_dec_ref(v___y_2461_);
return v_res_2467_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18(lean_object* v_preDefs_2468_, lean_object* v_xs_2469_, uint8_t v_a_2470_, lean_object* v___x_2471_, lean_object* v_as_2472_, size_t v_sz_2473_, size_t v_i_2474_, lean_object* v_bs_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_){
_start:
{
lean_object* v___x_2481_; 
v___x_2481_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___redArg(v_preDefs_2468_, v_xs_2469_, v_a_2470_, v___x_2471_, v_sz_2473_, v_i_2474_, v_bs_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_);
return v___x_2481_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___boxed(lean_object* v_preDefs_2482_, lean_object* v_xs_2483_, lean_object* v_a_2484_, lean_object* v___x_2485_, lean_object* v_as_2486_, lean_object* v_sz_2487_, lean_object* v_i_2488_, lean_object* v_bs_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_){
_start:
{
uint8_t v_a_29211__boxed_2495_; size_t v_sz_boxed_2496_; size_t v_i_boxed_2497_; lean_object* v_res_2498_; 
v_a_29211__boxed_2495_ = lean_unbox(v_a_2484_);
v_sz_boxed_2496_ = lean_unbox_usize(v_sz_2487_);
lean_dec(v_sz_2487_);
v_i_boxed_2497_ = lean_unbox_usize(v_i_2488_);
lean_dec(v_i_2488_);
v_res_2498_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18(v_preDefs_2482_, v_xs_2483_, v_a_29211__boxed_2495_, v___x_2485_, v_as_2486_, v_sz_boxed_2496_, v_i_boxed_2497_, v_bs_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_);
lean_dec(v___y_2493_);
lean_dec_ref(v___y_2492_);
lean_dec(v___y_2491_);
lean_dec_ref(v___y_2490_);
lean_dec_ref(v_as_2486_);
lean_dec_ref(v_xs_2483_);
return v_res_2498_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19(lean_object* v_a_2499_, lean_object* v_funTypes_2500_, lean_object* v_as_2501_, size_t v_sz_2502_, size_t v_i_2503_, lean_object* v_bs_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_){
_start:
{
lean_object* v___x_2510_; 
v___x_2510_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___redArg(v_a_2499_, v_funTypes_2500_, v_sz_2502_, v_i_2503_, v_bs_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_);
return v___x_2510_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___boxed(lean_object* v_a_2511_, lean_object* v_funTypes_2512_, lean_object* v_as_2513_, lean_object* v_sz_2514_, lean_object* v_i_2515_, lean_object* v_bs_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_){
_start:
{
size_t v_sz_boxed_2522_; size_t v_i_boxed_2523_; lean_object* v_res_2524_; 
v_sz_boxed_2522_ = lean_unbox_usize(v_sz_2514_);
lean_dec(v_sz_2514_);
v_i_boxed_2523_ = lean_unbox_usize(v_i_2515_);
lean_dec(v_i_2515_);
v_res_2524_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19(v_a_2511_, v_funTypes_2512_, v_as_2513_, v_sz_boxed_2522_, v_i_boxed_2523_, v_bs_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_);
lean_dec(v___y_2520_);
lean_dec_ref(v___y_2519_);
lean_dec(v___y_2518_);
lean_dec_ref(v___y_2517_);
lean_dec_ref(v_as_2513_);
lean_dec_ref(v_funTypes_2512_);
lean_dec_ref(v_a_2511_);
return v_res_2524_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__20(lean_object* v_a_2525_, lean_object* v_a_2526_, lean_object* v_as_2527_, size_t v_sz_2528_, size_t v_i_2529_, lean_object* v_bs_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_){
_start:
{
lean_object* v___x_2536_; 
v___x_2536_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__20___redArg(v_a_2525_, v_a_2526_, v_sz_2528_, v_i_2529_, v_bs_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_);
return v___x_2536_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__20___boxed(lean_object* v_a_2537_, lean_object* v_a_2538_, lean_object* v_as_2539_, lean_object* v_sz_2540_, lean_object* v_i_2541_, lean_object* v_bs_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_){
_start:
{
size_t v_sz_boxed_2548_; size_t v_i_boxed_2549_; lean_object* v_res_2550_; 
v_sz_boxed_2548_ = lean_unbox_usize(v_sz_2540_);
lean_dec(v_sz_2540_);
v_i_boxed_2549_ = lean_unbox_usize(v_i_2541_);
lean_dec(v_i_2541_);
v_res_2550_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__20(v_a_2537_, v_a_2538_, v_as_2539_, v_sz_boxed_2548_, v_i_boxed_2549_, v_bs_2542_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_);
lean_dec(v___y_2546_);
lean_dec_ref(v___y_2545_);
lean_dec(v___y_2544_);
lean_dec_ref(v___y_2543_);
lean_dec_ref(v_as_2539_);
lean_dec_ref(v_a_2538_);
lean_dec_ref(v_a_2537_);
return v_res_2550_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4(lean_object* v_00_u03b1_2551_, lean_object* v_msg_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_){
_start:
{
lean_object* v___x_2558_; 
v___x_2558_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg(v_msg_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_);
return v___x_2558_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___boxed(lean_object* v_00_u03b1_2559_, lean_object* v_msg_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_){
_start:
{
lean_object* v_res_2566_; 
v_res_2566_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4(v_00_u03b1_2559_, v_msg_2560_, v___y_2561_, v___y_2562_, v___y_2563_, v___y_2564_);
lean_dec(v___y_2564_);
lean_dec_ref(v___y_2563_);
lean_dec(v___y_2562_);
lean_dec_ref(v___y_2561_);
return v_res_2566_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9(lean_object* v_xs_2567_, lean_object* v_ys_2568_, lean_object* v_hsz_2569_, lean_object* v_x_2570_, lean_object* v_x_2571_){
_start:
{
uint8_t v___x_2572_; 
v___x_2572_ = l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9___redArg(v_xs_2567_, v_ys_2568_, v_x_2570_);
return v___x_2572_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9___boxed(lean_object* v_xs_2573_, lean_object* v_ys_2574_, lean_object* v_hsz_2575_, lean_object* v_x_2576_, lean_object* v_x_2577_){
_start:
{
uint8_t v_res_2578_; lean_object* v_r_2579_; 
v_res_2578_ = l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9(v_xs_2573_, v_ys_2574_, v_hsz_2575_, v_x_2576_, v_x_2577_);
lean_dec_ref(v_ys_2574_);
lean_dec_ref(v_xs_2573_);
v_r_2579_ = lean_box(v_res_2578_);
return v_r_2579_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10(lean_object* v_n_2580_, lean_object* v_as_2581_, lean_object* v_lo_2582_, lean_object* v_hi_2583_, lean_object* v_w_2584_, lean_object* v_hlo_2585_, lean_object* v_hhi_2586_){
_start:
{
lean_object* v___x_2587_; 
v___x_2587_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg(v_n_2580_, v_as_2581_, v_lo_2582_, v_hi_2583_);
return v___x_2587_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___boxed(lean_object* v_n_2588_, lean_object* v_as_2589_, lean_object* v_lo_2590_, lean_object* v_hi_2591_, lean_object* v_w_2592_, lean_object* v_hlo_2593_, lean_object* v_hhi_2594_){
_start:
{
lean_object* v_res_2595_; 
v_res_2595_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10(v_n_2588_, v_as_2589_, v_lo_2590_, v_hi_2591_, v_w_2592_, v_hlo_2593_, v_hhi_2594_);
lean_dec(v_hi_2591_);
lean_dec(v_n_2588_);
return v_res_2595_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15(lean_object* v_00_u03b1_2596_, lean_object* v_00_u03b3_2597_, lean_object* v_xs_2598_, lean_object* v_f_2599_, lean_object* v_as_2600_, lean_object* v_bs_2601_, lean_object* v_i_2602_, lean_object* v_cs_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_){
_start:
{
lean_object* v___x_2609_; 
v___x_2609_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15___redArg(v_xs_2598_, v_f_2599_, v_as_2600_, v_bs_2601_, v_i_2602_, v_cs_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_);
return v___x_2609_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15___boxed(lean_object* v_00_u03b1_2610_, lean_object* v_00_u03b3_2611_, lean_object* v_xs_2612_, lean_object* v_f_2613_, lean_object* v_as_2614_, lean_object* v_bs_2615_, lean_object* v_i_2616_, lean_object* v_cs_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_){
_start:
{
lean_object* v_res_2623_; 
v_res_2623_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15(v_00_u03b1_2610_, v_00_u03b3_2611_, v_xs_2612_, v_f_2613_, v_as_2614_, v_bs_2615_, v_i_2616_, v_cs_2617_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_);
lean_dec(v___y_2621_);
lean_dec_ref(v___y_2620_);
lean_dec(v___y_2619_);
lean_dec_ref(v___y_2618_);
lean_dec_ref(v_bs_2615_);
lean_dec_ref(v_as_2614_);
lean_dec_ref(v_xs_2612_);
return v_res_2623_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25(lean_object* v_env_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_){
_start:
{
lean_object* v___x_2630_; 
v___x_2630_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg(v_env_2624_, v___y_2626_, v___y_2628_);
return v___x_2630_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___boxed(lean_object* v_env_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_){
_start:
{
lean_object* v_res_2637_; 
v_res_2637_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25(v_env_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_);
lean_dec(v___y_2635_);
lean_dec_ref(v___y_2634_);
lean_dec(v___y_2633_);
lean_dec_ref(v___y_2632_);
return v_res_2637_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23(lean_object* v_00_u03b1_2638_, lean_object* v_env_2639_, lean_object* v_x_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_){
_start:
{
lean_object* v___x_2646_; 
v___x_2646_ = l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23___redArg(v_env_2639_, v_x_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_);
return v___x_2646_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23___boxed(lean_object* v_00_u03b1_2647_, lean_object* v_env_2648_, lean_object* v_x_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_){
_start:
{
lean_object* v_res_2655_; 
v_res_2655_ = l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23(v_00_u03b1_2647_, v_env_2648_, v_x_2649_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_);
lean_dec(v___y_2653_);
lean_dec_ref(v___y_2652_);
lean_dec(v___y_2651_);
lean_dec_ref(v___y_2650_);
return v_res_2655_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11(lean_object* v_n_2656_, lean_object* v_lo_2657_, lean_object* v_hi_2658_, lean_object* v_hhi_2659_, lean_object* v_pivot_2660_, lean_object* v_as_2661_, lean_object* v_i_2662_, lean_object* v_k_2663_, lean_object* v_ilo_2664_, lean_object* v_ik_2665_, lean_object* v_w_2666_){
_start:
{
lean_object* v___x_2667_; 
v___x_2667_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11___redArg(v_hi_2658_, v_pivot_2660_, v_as_2661_, v_i_2662_, v_k_2663_);
return v___x_2667_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11___boxed(lean_object* v_n_2668_, lean_object* v_lo_2669_, lean_object* v_hi_2670_, lean_object* v_hhi_2671_, lean_object* v_pivot_2672_, lean_object* v_as_2673_, lean_object* v_i_2674_, lean_object* v_k_2675_, lean_object* v_ilo_2676_, lean_object* v_ik_2677_, lean_object* v_w_2678_){
_start:
{
lean_object* v_res_2679_; 
v_res_2679_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11(v_n_2668_, v_lo_2669_, v_hi_2670_, v_hhi_2671_, v_pivot_2672_, v_as_2673_, v_i_2674_, v_k_2675_, v_ilo_2676_, v_ik_2677_, v_w_2678_);
lean_dec(v_pivot_2672_);
lean_dec(v_hi_2670_);
lean_dec(v_lo_2669_);
lean_dec(v_n_2668_);
return v_res_2679_;
}
}
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg___lam__0(lean_object* v_x_2680_){
_start:
{
uint8_t v___x_2681_; 
v___x_2681_ = 0;
return v___x_2681_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg___lam__0___boxed(lean_object* v_x_2682_){
_start:
{
uint8_t v_res_2683_; lean_object* v_r_2684_; 
v_res_2683_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg___lam__0(v_x_2682_);
lean_dec(v_x_2682_);
v_r_2684_ = lean_box(v_res_2683_);
return v_r_2684_;
}
}
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg___lam__1(lean_object* v_fvarId_2685_, lean_object* v_x_2686_){
_start:
{
uint8_t v___x_2687_; 
v___x_2687_ = l_Lean_instBEqFVarId_beq(v_fvarId_2685_, v_x_2686_);
return v___x_2687_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg___lam__1___boxed(lean_object* v_fvarId_2688_, lean_object* v_x_2689_){
_start:
{
uint8_t v_res_2690_; lean_object* v_r_2691_; 
v_res_2690_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg___lam__1(v_fvarId_2688_, v_x_2689_);
lean_dec(v_x_2689_);
lean_dec(v_fvarId_2688_);
v_r_2691_ = lean_box(v_res_2690_);
return v_r_2691_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; 
v___x_2693_ = lean_box(0);
v___x_2694_ = lean_unsigned_to_nat(16u);
v___x_2695_ = lean_mk_array(v___x_2694_, v___x_2693_);
return v___x_2695_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; 
v___x_2696_ = lean_obj_once(&l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg___closed__1, &l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg___closed__1_once, _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg___closed__1);
v___x_2697_ = lean_unsigned_to_nat(0u);
v___x_2698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2698_, 0, v___x_2697_);
lean_ctor_set(v___x_2698_, 1, v___x_2696_);
return v___x_2698_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg(lean_object* v_e_2699_, lean_object* v_fvarId_2700_, lean_object* v___y_2701_){
_start:
{
lean_object* v___f_2703_; lean_object* v___f_2704_; lean_object* v___x_2705_; uint8_t v_fst_2707_; lean_object* v_mctx_2708_; lean_object* v___y_2726_; lean_object* v_mctx_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; uint8_t v___x_2734_; 
v___f_2703_ = ((lean_object*)(l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg___closed__0));
v___f_2704_ = lean_alloc_closure((void*)(l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_2704_, 0, v_fvarId_2700_);
v___x_2705_ = lean_st_ref_get(v___y_2701_);
v_mctx_2731_ = lean_ctor_get(v___x_2705_, 0);
lean_inc_ref_n(v_mctx_2731_, 2);
lean_dec(v___x_2705_);
v___x_2732_ = lean_obj_once(&l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg___closed__2, &l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg___closed__2_once, _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg___closed__2);
v___x_2733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2733_, 0, v___x_2732_);
lean_ctor_set(v___x_2733_, 1, v_mctx_2731_);
v___x_2734_ = l_Lean_Expr_hasFVar(v_e_2699_);
if (v___x_2734_ == 0)
{
uint8_t v___x_2735_; 
v___x_2735_ = l_Lean_Expr_hasMVar(v_e_2699_);
if (v___x_2735_ == 0)
{
lean_dec_ref_known(v___x_2733_, 2);
lean_dec_ref(v___f_2704_);
lean_dec_ref(v_e_2699_);
v_fst_2707_ = v___x_2735_;
v_mctx_2708_ = v_mctx_2731_;
goto v___jp_2706_;
}
else
{
lean_object* v___x_2736_; 
lean_dec_ref(v_mctx_2731_);
v___x_2736_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2704_, v___f_2703_, v_e_2699_, v___x_2733_);
v___y_2726_ = v___x_2736_;
goto v___jp_2725_;
}
}
else
{
lean_object* v___x_2737_; 
lean_dec_ref(v_mctx_2731_);
v___x_2737_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2704_, v___f_2703_, v_e_2699_, v___x_2733_);
v___y_2726_ = v___x_2737_;
goto v___jp_2725_;
}
v___jp_2706_:
{
lean_object* v___x_2709_; lean_object* v_cache_2710_; lean_object* v_zetaDeltaFVarIds_2711_; lean_object* v_postponed_2712_; lean_object* v_diag_2713_; lean_object* v___x_2715_; uint8_t v_isShared_2716_; uint8_t v_isSharedCheck_2723_; 
v___x_2709_ = lean_st_ref_take(v___y_2701_);
v_cache_2710_ = lean_ctor_get(v___x_2709_, 1);
v_zetaDeltaFVarIds_2711_ = lean_ctor_get(v___x_2709_, 2);
v_postponed_2712_ = lean_ctor_get(v___x_2709_, 3);
v_diag_2713_ = lean_ctor_get(v___x_2709_, 4);
v_isSharedCheck_2723_ = !lean_is_exclusive(v___x_2709_);
if (v_isSharedCheck_2723_ == 0)
{
lean_object* v_unused_2724_; 
v_unused_2724_ = lean_ctor_get(v___x_2709_, 0);
lean_dec(v_unused_2724_);
v___x_2715_ = v___x_2709_;
v_isShared_2716_ = v_isSharedCheck_2723_;
goto v_resetjp_2714_;
}
else
{
lean_inc(v_diag_2713_);
lean_inc(v_postponed_2712_);
lean_inc(v_zetaDeltaFVarIds_2711_);
lean_inc(v_cache_2710_);
lean_dec(v___x_2709_);
v___x_2715_ = lean_box(0);
v_isShared_2716_ = v_isSharedCheck_2723_;
goto v_resetjp_2714_;
}
v_resetjp_2714_:
{
lean_object* v___x_2718_; 
if (v_isShared_2716_ == 0)
{
lean_ctor_set(v___x_2715_, 0, v_mctx_2708_);
v___x_2718_ = v___x_2715_;
goto v_reusejp_2717_;
}
else
{
lean_object* v_reuseFailAlloc_2722_; 
v_reuseFailAlloc_2722_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2722_, 0, v_mctx_2708_);
lean_ctor_set(v_reuseFailAlloc_2722_, 1, v_cache_2710_);
lean_ctor_set(v_reuseFailAlloc_2722_, 2, v_zetaDeltaFVarIds_2711_);
lean_ctor_set(v_reuseFailAlloc_2722_, 3, v_postponed_2712_);
lean_ctor_set(v_reuseFailAlloc_2722_, 4, v_diag_2713_);
v___x_2718_ = v_reuseFailAlloc_2722_;
goto v_reusejp_2717_;
}
v_reusejp_2717_:
{
lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; 
v___x_2719_ = lean_st_ref_put(v___y_2701_, v___x_2718_);
v___x_2720_ = lean_box(v_fst_2707_);
v___x_2721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2721_, 0, v___x_2720_);
return v___x_2721_;
}
}
}
v___jp_2725_:
{
lean_object* v_snd_2727_; lean_object* v_fst_2728_; lean_object* v_mctx_2729_; uint8_t v___x_2730_; 
v_snd_2727_ = lean_ctor_get(v___y_2726_, 1);
lean_inc(v_snd_2727_);
v_fst_2728_ = lean_ctor_get(v___y_2726_, 0);
lean_inc(v_fst_2728_);
lean_dec_ref(v___y_2726_);
v_mctx_2729_ = lean_ctor_get(v_snd_2727_, 1);
lean_inc_ref(v_mctx_2729_);
lean_dec(v_snd_2727_);
v___x_2730_ = lean_unbox(v_fst_2728_);
lean_dec(v_fst_2728_);
v_fst_2707_ = v___x_2730_;
v_mctx_2708_ = v_mctx_2729_;
goto v___jp_2706_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg___boxed(lean_object* v_e_2738_, lean_object* v_fvarId_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_){
_start:
{
lean_object* v_res_2742_; 
v_res_2742_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg(v_e_2738_, v_fvarId_2739_, v___y_2740_);
lean_dec(v___y_2740_);
return v_res_2742_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4(lean_object* v_e_2743_, lean_object* v_fvarId_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_){
_start:
{
lean_object* v___x_2750_; 
v___x_2750_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg(v_e_2743_, v_fvarId_2744_, v___y_2746_);
return v___x_2750_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___boxed(lean_object* v_e_2751_, lean_object* v_fvarId_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_){
_start:
{
lean_object* v_res_2758_; 
v_res_2758_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4(v_e_2751_, v_fvarId_2752_, v___y_2753_, v___y_2754_, v___y_2755_, v___y_2756_);
lean_dec(v___y_2756_);
lean_dec_ref(v___y_2755_);
lean_dec(v___y_2754_);
lean_dec_ref(v___y_2753_);
return v_res_2758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg___lam__0(lean_object* v_k_2759_, lean_object* v_b_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_){
_start:
{
lean_object* v___x_2766_; 
lean_inc(v___y_2764_);
lean_inc_ref(v___y_2763_);
lean_inc(v___y_2762_);
lean_inc_ref(v___y_2761_);
v___x_2766_ = lean_apply_6(v_k_2759_, v_b_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_, lean_box(0));
return v___x_2766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg___lam__0___boxed(lean_object* v_k_2767_, lean_object* v_b_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_){
_start:
{
lean_object* v_res_2774_; 
v_res_2774_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg___lam__0(v_k_2767_, v_b_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_);
lean_dec(v___y_2772_);
lean_dec_ref(v___y_2771_);
lean_dec(v___y_2770_);
lean_dec_ref(v___y_2769_);
return v_res_2774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg(lean_object* v_perm_2775_, lean_object* v_type_2776_, lean_object* v_k_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_){
_start:
{
lean_object* v___f_2783_; lean_object* v___x_2784_; 
v___f_2783_ = lean_alloc_closure((void*)(l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2783_, 0, v_k_2777_);
v___x_2784_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl(lean_box(0), v_perm_2775_, v_type_2776_, v___f_2783_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_);
if (lean_obj_tag(v___x_2784_) == 0)
{
lean_object* v_a_2785_; lean_object* v___x_2787_; uint8_t v_isShared_2788_; uint8_t v_isSharedCheck_2792_; 
v_a_2785_ = lean_ctor_get(v___x_2784_, 0);
v_isSharedCheck_2792_ = !lean_is_exclusive(v___x_2784_);
if (v_isSharedCheck_2792_ == 0)
{
v___x_2787_ = v___x_2784_;
v_isShared_2788_ = v_isSharedCheck_2792_;
goto v_resetjp_2786_;
}
else
{
lean_inc(v_a_2785_);
lean_dec(v___x_2784_);
v___x_2787_ = lean_box(0);
v_isShared_2788_ = v_isSharedCheck_2792_;
goto v_resetjp_2786_;
}
v_resetjp_2786_:
{
lean_object* v___x_2790_; 
if (v_isShared_2788_ == 0)
{
v___x_2790_ = v___x_2787_;
goto v_reusejp_2789_;
}
else
{
lean_object* v_reuseFailAlloc_2791_; 
v_reuseFailAlloc_2791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2791_, 0, v_a_2785_);
v___x_2790_ = v_reuseFailAlloc_2791_;
goto v_reusejp_2789_;
}
v_reusejp_2789_:
{
return v___x_2790_;
}
}
}
else
{
lean_object* v_a_2793_; lean_object* v___x_2795_; uint8_t v_isShared_2796_; uint8_t v_isSharedCheck_2800_; 
v_a_2793_ = lean_ctor_get(v___x_2784_, 0);
v_isSharedCheck_2800_ = !lean_is_exclusive(v___x_2784_);
if (v_isSharedCheck_2800_ == 0)
{
v___x_2795_ = v___x_2784_;
v_isShared_2796_ = v_isSharedCheck_2800_;
goto v_resetjp_2794_;
}
else
{
lean_inc(v_a_2793_);
lean_dec(v___x_2784_);
v___x_2795_ = lean_box(0);
v_isShared_2796_ = v_isSharedCheck_2800_;
goto v_resetjp_2794_;
}
v_resetjp_2794_:
{
lean_object* v___x_2798_; 
if (v_isShared_2796_ == 0)
{
v___x_2798_ = v___x_2795_;
goto v_reusejp_2797_;
}
else
{
lean_object* v_reuseFailAlloc_2799_; 
v_reuseFailAlloc_2799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2799_, 0, v_a_2793_);
v___x_2798_ = v_reuseFailAlloc_2799_;
goto v_reusejp_2797_;
}
v_reusejp_2797_:
{
return v___x_2798_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg___boxed(lean_object* v_perm_2801_, lean_object* v_type_2802_, lean_object* v_k_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_){
_start:
{
lean_object* v_res_2809_; 
v_res_2809_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg(v_perm_2801_, v_type_2802_, v_k_2803_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_);
lean_dec(v___y_2807_);
lean_dec_ref(v___y_2806_);
lean_dec(v___y_2805_);
lean_dec_ref(v___y_2804_);
return v_res_2809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12(lean_object* v_00_u03b1_2810_, lean_object* v_perm_2811_, lean_object* v_type_2812_, lean_object* v_k_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_){
_start:
{
lean_object* v___x_2819_; 
v___x_2819_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg(v_perm_2811_, v_type_2812_, v_k_2813_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_);
return v___x_2819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___boxed(lean_object* v_00_u03b1_2820_, lean_object* v_perm_2821_, lean_object* v_type_2822_, lean_object* v_k_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_){
_start:
{
lean_object* v_res_2829_; 
v_res_2829_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12(v_00_u03b1_2820_, v_perm_2821_, v_type_2822_, v_k_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_);
lean_dec(v___y_2827_);
lean_dec_ref(v___y_2826_);
lean_dec(v___y_2825_);
lean_dec_ref(v___y_2824_);
return v_res_2829_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1(lean_object* v_a_2830_, lean_object* v_fst_2831_, lean_object* v_fst_2832_, lean_object* v___x_2833_, lean_object* v___x_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_){
_start:
{
lean_object* v___x_2840_; 
lean_inc_ref(v_fst_2831_);
v___x_2840_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion(v_a_2830_, v_fst_2831_, v_fst_2832_, v___x_2833_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_);
if (lean_obj_tag(v___x_2840_) == 0)
{
lean_object* v_a_2841_; lean_object* v___x_2843_; uint8_t v_isShared_2844_; uint8_t v_isSharedCheck_2850_; 
v_a_2841_ = lean_ctor_get(v___x_2840_, 0);
v_isSharedCheck_2850_ = !lean_is_exclusive(v___x_2840_);
if (v_isSharedCheck_2850_ == 0)
{
v___x_2843_ = v___x_2840_;
v_isShared_2844_ = v_isSharedCheck_2850_;
goto v_resetjp_2842_;
}
else
{
lean_inc(v_a_2841_);
lean_dec(v___x_2840_);
v___x_2843_ = lean_box(0);
v_isShared_2844_ = v_isSharedCheck_2850_;
goto v_resetjp_2842_;
}
v_resetjp_2842_:
{
lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2848_; 
v___x_2845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2845_, 0, v_a_2841_);
lean_ctor_set(v___x_2845_, 1, v_fst_2831_);
v___x_2846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2846_, 0, v___x_2834_);
lean_ctor_set(v___x_2846_, 1, v___x_2845_);
if (v_isShared_2844_ == 0)
{
lean_ctor_set(v___x_2843_, 0, v___x_2846_);
v___x_2848_ = v___x_2843_;
goto v_reusejp_2847_;
}
else
{
lean_object* v_reuseFailAlloc_2849_; 
v_reuseFailAlloc_2849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2849_, 0, v___x_2846_);
v___x_2848_ = v_reuseFailAlloc_2849_;
goto v_reusejp_2847_;
}
v_reusejp_2847_:
{
return v___x_2848_;
}
}
}
else
{
lean_object* v_a_2851_; lean_object* v___x_2853_; uint8_t v_isShared_2854_; uint8_t v_isSharedCheck_2858_; 
lean_dec_ref(v___x_2834_);
lean_dec_ref(v_fst_2831_);
v_a_2851_ = lean_ctor_get(v___x_2840_, 0);
v_isSharedCheck_2858_ = !lean_is_exclusive(v___x_2840_);
if (v_isSharedCheck_2858_ == 0)
{
v___x_2853_ = v___x_2840_;
v_isShared_2854_ = v_isSharedCheck_2858_;
goto v_resetjp_2852_;
}
else
{
lean_inc(v_a_2851_);
lean_dec(v___x_2840_);
v___x_2853_ = lean_box(0);
v_isShared_2854_ = v_isSharedCheck_2858_;
goto v_resetjp_2852_;
}
v_resetjp_2852_:
{
lean_object* v___x_2856_; 
if (v_isShared_2854_ == 0)
{
v___x_2856_ = v___x_2853_;
goto v_reusejp_2855_;
}
else
{
lean_object* v_reuseFailAlloc_2857_; 
v_reuseFailAlloc_2857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2857_, 0, v_a_2851_);
v___x_2856_ = v_reuseFailAlloc_2857_;
goto v_reusejp_2855_;
}
v_reusejp_2855_:
{
return v___x_2856_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___boxed(lean_object* v_a_2859_, lean_object* v_fst_2860_, lean_object* v_fst_2861_, lean_object* v___x_2862_, lean_object* v___x_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_){
_start:
{
lean_object* v_res_2869_; 
v_res_2869_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1(v_a_2859_, v_fst_2860_, v_fst_2861_, v___x_2862_, v___x_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_);
lean_dec(v___y_2867_);
lean_dec_ref(v___y_2866_);
lean_dec(v___y_2865_);
lean_dec_ref(v___y_2864_);
return v_res_2869_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1(size_t v_sz_2870_, size_t v_i_2871_, lean_object* v_bs_2872_){
_start:
{
uint8_t v___x_2873_; 
v___x_2873_ = lean_usize_dec_lt(v_i_2871_, v_sz_2870_);
if (v___x_2873_ == 0)
{
return v_bs_2872_;
}
else
{
lean_object* v_v_2874_; lean_object* v_recArgPos_2875_; lean_object* v___x_2876_; lean_object* v_bs_x27_2877_; size_t v___x_2878_; size_t v___x_2879_; lean_object* v___x_2880_; 
v_v_2874_ = lean_array_uget_borrowed(v_bs_2872_, v_i_2871_);
v_recArgPos_2875_ = lean_ctor_get(v_v_2874_, 2);
lean_inc(v_recArgPos_2875_);
v___x_2876_ = lean_unsigned_to_nat(0u);
v_bs_x27_2877_ = lean_array_uset(v_bs_2872_, v_i_2871_, v___x_2876_);
v___x_2878_ = ((size_t)1ULL);
v___x_2879_ = lean_usize_add(v_i_2871_, v___x_2878_);
v___x_2880_ = lean_array_uset(v_bs_x27_2877_, v_i_2871_, v_recArgPos_2875_);
v_i_2871_ = v___x_2879_;
v_bs_2872_ = v___x_2880_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1___boxed(lean_object* v_sz_2882_, lean_object* v_i_2883_, lean_object* v_bs_2884_){
_start:
{
size_t v_sz_boxed_2885_; size_t v_i_boxed_2886_; lean_object* v_res_2887_; 
v_sz_boxed_2885_ = lean_unbox_usize(v_sz_2882_);
lean_dec(v_sz_2882_);
v_i_boxed_2886_ = lean_unbox_usize(v_i_2883_);
lean_dec(v_i_2883_);
v_res_2887_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1(v_sz_boxed_2885_, v_i_boxed_2886_, v_bs_2884_);
return v_res_2887_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__11(lean_object* v_as_2888_, size_t v_i_2889_, size_t v_stop_2890_, lean_object* v_b_2891_){
_start:
{
uint8_t v___x_2892_; 
v___x_2892_ = lean_usize_dec_eq(v_i_2889_, v_stop_2890_);
if (v___x_2892_ == 0)
{
lean_object* v___x_2893_; lean_object* v___x_2894_; size_t v___x_2895_; size_t v___x_2896_; 
v___x_2893_ = lean_array_uget_borrowed(v_as_2888_, v_i_2889_);
v___x_2894_ = l_Lean_LocalContext_erase(v_b_2891_, v___x_2893_);
v___x_2895_ = ((size_t)1ULL);
v___x_2896_ = lean_usize_add(v_i_2889_, v___x_2895_);
v_i_2889_ = v___x_2896_;
v_b_2891_ = v___x_2894_;
goto _start;
}
else
{
return v_b_2891_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__11___boxed(lean_object* v_as_2898_, lean_object* v_i_2899_, lean_object* v_stop_2900_, lean_object* v_b_2901_){
_start:
{
size_t v_i_boxed_2902_; size_t v_stop_boxed_2903_; lean_object* v_res_2904_; 
v_i_boxed_2902_ = lean_unbox_usize(v_i_2899_);
lean_dec(v_i_2899_);
v_stop_boxed_2903_ = lean_unbox_usize(v_stop_2900_);
lean_dec(v_stop_2900_);
v_res_2904_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__11(v_as_2898_, v_i_boxed_2902_, v_stop_boxed_2903_, v_b_2901_);
lean_dec_ref(v_as_2898_);
return v_res_2904_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__8_spec__10(lean_object* v_a_2905_, lean_object* v_as_2906_, size_t v_i_2907_, size_t v_stop_2908_){
_start:
{
uint8_t v___x_2909_; 
v___x_2909_ = lean_usize_dec_eq(v_i_2907_, v_stop_2908_);
if (v___x_2909_ == 0)
{
lean_object* v___x_2910_; uint8_t v___x_2911_; 
v___x_2910_ = lean_array_uget_borrowed(v_as_2906_, v_i_2907_);
v___x_2911_ = l_Lean_instBEqFVarId_beq(v_a_2905_, v___x_2910_);
if (v___x_2911_ == 0)
{
size_t v___x_2912_; size_t v___x_2913_; 
v___x_2912_ = ((size_t)1ULL);
v___x_2913_ = lean_usize_add(v_i_2907_, v___x_2912_);
v_i_2907_ = v___x_2913_;
goto _start;
}
else
{
return v___x_2911_;
}
}
else
{
uint8_t v___x_2915_; 
v___x_2915_ = 0;
return v___x_2915_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__8_spec__10___boxed(lean_object* v_a_2916_, lean_object* v_as_2917_, lean_object* v_i_2918_, lean_object* v_stop_2919_){
_start:
{
size_t v_i_boxed_2920_; size_t v_stop_boxed_2921_; uint8_t v_res_2922_; lean_object* v_r_2923_; 
v_i_boxed_2920_ = lean_unbox_usize(v_i_2918_);
lean_dec(v_i_2918_);
v_stop_boxed_2921_ = lean_unbox_usize(v_stop_2919_);
lean_dec(v_stop_2919_);
v_res_2922_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__8_spec__10(v_a_2916_, v_as_2917_, v_i_boxed_2920_, v_stop_boxed_2921_);
lean_dec_ref(v_as_2917_);
lean_dec(v_a_2916_);
v_r_2923_ = lean_box(v_res_2922_);
return v_r_2923_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__8(lean_object* v_as_2924_, lean_object* v_a_2925_){
_start:
{
lean_object* v___x_2926_; lean_object* v___x_2927_; uint8_t v___x_2928_; 
v___x_2926_ = lean_unsigned_to_nat(0u);
v___x_2927_ = lean_array_get_size(v_as_2924_);
v___x_2928_ = lean_nat_dec_lt(v___x_2926_, v___x_2927_);
if (v___x_2928_ == 0)
{
return v___x_2928_;
}
else
{
size_t v___x_2929_; size_t v___x_2930_; uint8_t v___x_2931_; 
v___x_2929_ = ((size_t)0ULL);
v___x_2930_ = lean_usize_of_nat(v___x_2927_);
v___x_2931_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__8_spec__10(v_a_2925_, v_as_2924_, v___x_2929_, v___x_2930_);
return v___x_2931_;
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__8___boxed(lean_object* v_as_2932_, lean_object* v_a_2933_){
_start:
{
uint8_t v_res_2934_; lean_object* v_r_2935_; 
v_res_2934_ = l_Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__8(v_as_2932_, v_a_2933_);
lean_dec(v_a_2933_);
lean_dec_ref(v_as_2932_);
v_r_2935_ = lean_box(v_res_2934_);
return v_r_2935_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__10(lean_object* v_fvarIds_2936_, lean_object* v_as_2937_, size_t v_i_2938_, size_t v_stop_2939_, lean_object* v_b_2940_){
_start:
{
lean_object* v___y_2942_; uint8_t v___x_2946_; 
v___x_2946_ = lean_usize_dec_eq(v_i_2938_, v_stop_2939_);
if (v___x_2946_ == 0)
{
lean_object* v___x_2947_; lean_object* v_fvar_2948_; 
v___x_2947_ = lean_array_uget_borrowed(v_as_2937_, v_i_2938_);
v_fvar_2948_ = lean_ctor_get(v___x_2947_, 1);
if (lean_obj_tag(v_fvar_2948_) == 1)
{
lean_object* v_fvarId_2949_; uint8_t v___x_2950_; 
v_fvarId_2949_ = lean_ctor_get(v_fvar_2948_, 0);
v___x_2950_ = l_Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__8(v_fvarIds_2936_, v_fvarId_2949_);
if (v___x_2950_ == 0)
{
lean_object* v___x_2951_; 
lean_inc(v___x_2947_);
v___x_2951_ = lean_array_push(v_b_2940_, v___x_2947_);
v___y_2942_ = v___x_2951_;
goto v___jp_2941_;
}
else
{
v___y_2942_ = v_b_2940_;
goto v___jp_2941_;
}
}
else
{
lean_object* v___x_2952_; 
lean_inc(v___x_2947_);
v___x_2952_ = lean_array_push(v_b_2940_, v___x_2947_);
v___y_2942_ = v___x_2952_;
goto v___jp_2941_;
}
}
else
{
return v_b_2940_;
}
v___jp_2941_:
{
size_t v___x_2943_; size_t v___x_2944_; 
v___x_2943_ = ((size_t)1ULL);
v___x_2944_ = lean_usize_add(v_i_2938_, v___x_2943_);
v_i_2938_ = v___x_2944_;
v_b_2940_ = v___y_2942_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__10___boxed(lean_object* v_fvarIds_2953_, lean_object* v_as_2954_, lean_object* v_i_2955_, lean_object* v_stop_2956_, lean_object* v_b_2957_){
_start:
{
size_t v_i_boxed_2958_; size_t v_stop_boxed_2959_; lean_object* v_res_2960_; 
v_i_boxed_2958_ = lean_unbox_usize(v_i_2955_);
lean_dec(v_i_2955_);
v_stop_boxed_2959_ = lean_unbox_usize(v_stop_2956_);
lean_dec(v_stop_2956_);
v_res_2960_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__10(v_fvarIds_2953_, v_as_2954_, v_i_boxed_2958_, v_stop_boxed_2959_, v_b_2957_);
lean_dec_ref(v_as_2954_);
lean_dec_ref(v_fvarIds_2953_);
return v_res_2960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__9___redArg(lean_object* v_lctx_2961_, lean_object* v_localInsts_2962_, lean_object* v_x_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_){
_start:
{
lean_object* v___x_2969_; 
v___x_2969_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_2961_, v_localInsts_2962_, v_x_2963_, v___y_2964_, v___y_2965_, v___y_2966_, v___y_2967_);
if (lean_obj_tag(v___x_2969_) == 0)
{
lean_object* v_a_2970_; lean_object* v___x_2972_; uint8_t v_isShared_2973_; uint8_t v_isSharedCheck_2977_; 
v_a_2970_ = lean_ctor_get(v___x_2969_, 0);
v_isSharedCheck_2977_ = !lean_is_exclusive(v___x_2969_);
if (v_isSharedCheck_2977_ == 0)
{
v___x_2972_ = v___x_2969_;
v_isShared_2973_ = v_isSharedCheck_2977_;
goto v_resetjp_2971_;
}
else
{
lean_inc(v_a_2970_);
lean_dec(v___x_2969_);
v___x_2972_ = lean_box(0);
v_isShared_2973_ = v_isSharedCheck_2977_;
goto v_resetjp_2971_;
}
v_resetjp_2971_:
{
lean_object* v___x_2975_; 
if (v_isShared_2973_ == 0)
{
v___x_2975_ = v___x_2972_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v_a_2970_);
v___x_2975_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
return v___x_2975_;
}
}
}
else
{
lean_object* v_a_2978_; lean_object* v___x_2980_; uint8_t v_isShared_2981_; uint8_t v_isSharedCheck_2985_; 
v_a_2978_ = lean_ctor_get(v___x_2969_, 0);
v_isSharedCheck_2985_ = !lean_is_exclusive(v___x_2969_);
if (v_isSharedCheck_2985_ == 0)
{
v___x_2980_ = v___x_2969_;
v_isShared_2981_ = v_isSharedCheck_2985_;
goto v_resetjp_2979_;
}
else
{
lean_inc(v_a_2978_);
lean_dec(v___x_2969_);
v___x_2980_ = lean_box(0);
v_isShared_2981_ = v_isSharedCheck_2985_;
goto v_resetjp_2979_;
}
v_resetjp_2979_:
{
lean_object* v___x_2983_; 
if (v_isShared_2981_ == 0)
{
v___x_2983_ = v___x_2980_;
goto v_reusejp_2982_;
}
else
{
lean_object* v_reuseFailAlloc_2984_; 
v_reuseFailAlloc_2984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2984_, 0, v_a_2978_);
v___x_2983_ = v_reuseFailAlloc_2984_;
goto v_reusejp_2982_;
}
v_reusejp_2982_:
{
return v___x_2983_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__9___redArg___boxed(lean_object* v_lctx_2986_, lean_object* v_localInsts_2987_, lean_object* v_x_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_){
_start:
{
lean_object* v_res_2994_; 
v_res_2994_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__9___redArg(v_lctx_2986_, v_localInsts_2987_, v_x_2988_, v___y_2989_, v___y_2990_, v___y_2991_, v___y_2992_);
lean_dec(v___y_2992_);
lean_dec_ref(v___y_2991_);
lean_dec(v___y_2990_);
lean_dec_ref(v___y_2989_);
return v_res_2994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8___redArg(lean_object* v_fvarIds_2997_, lean_object* v_k_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_){
_start:
{
lean_object* v_lctx_3004_; lean_object* v_localInstances_3005_; lean_object* v___y_3007_; lean_object* v___x_3017_; lean_object* v___x_3018_; uint8_t v___x_3019_; 
v_lctx_3004_ = lean_ctor_get(v___y_2999_, 2);
v_localInstances_3005_ = lean_ctor_get(v___y_2999_, 3);
v___x_3017_ = lean_unsigned_to_nat(0u);
v___x_3018_ = lean_array_get_size(v_fvarIds_2997_);
v___x_3019_ = lean_nat_dec_lt(v___x_3017_, v___x_3018_);
if (v___x_3019_ == 0)
{
lean_inc_ref(v_lctx_3004_);
v___y_3007_ = v_lctx_3004_;
goto v___jp_3006_;
}
else
{
size_t v___x_3020_; size_t v___x_3021_; lean_object* v___x_3022_; 
v___x_3020_ = ((size_t)0ULL);
v___x_3021_ = lean_usize_of_nat(v___x_3018_);
lean_inc_ref(v_lctx_3004_);
v___x_3022_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__11(v_fvarIds_2997_, v___x_3020_, v___x_3021_, v_lctx_3004_);
v___y_3007_ = v___x_3022_;
goto v___jp_3006_;
}
v___jp_3006_:
{
lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; uint8_t v___x_3011_; 
v___x_3008_ = lean_unsigned_to_nat(0u);
v___x_3009_ = lean_array_get_size(v_localInstances_3005_);
v___x_3010_ = ((lean_object*)(l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8___redArg___closed__0));
v___x_3011_ = lean_nat_dec_lt(v___x_3008_, v___x_3009_);
if (v___x_3011_ == 0)
{
lean_object* v___x_3012_; 
v___x_3012_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__9___redArg(v___y_3007_, v___x_3010_, v_k_2998_, v___y_2999_, v___y_3000_, v___y_3001_, v___y_3002_);
return v___x_3012_;
}
else
{
size_t v___x_3013_; size_t v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; 
v___x_3013_ = ((size_t)0ULL);
v___x_3014_ = lean_usize_of_nat(v___x_3009_);
v___x_3015_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__10(v_fvarIds_2997_, v_localInstances_3005_, v___x_3013_, v___x_3014_, v___x_3010_);
v___x_3016_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__9___redArg(v___y_3007_, v___x_3015_, v_k_2998_, v___y_2999_, v___y_3000_, v___y_3001_, v___y_3002_);
return v___x_3016_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8___redArg___boxed(lean_object* v_fvarIds_3023_, lean_object* v_k_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_){
_start:
{
lean_object* v_res_3030_; 
v_res_3030_ = l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8___redArg(v_fvarIds_3023_, v_k_3024_, v___y_3025_, v___y_3026_, v___y_3027_, v___y_3028_);
lean_dec(v___y_3028_);
lean_dec_ref(v___y_3027_);
lean_dec(v___y_3026_);
lean_dec_ref(v___y_3025_);
lean_dec_ref(v_fvarIds_3023_);
return v_res_3030_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___closed__1(void){
_start:
{
lean_object* v___x_3032_; lean_object* v___x_3033_; 
v___x_3032_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___closed__0));
v___x_3033_ = l_Lean_stringToMessageData(v___x_3032_);
return v___x_3033_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___closed__3(void){
_start:
{
lean_object* v___x_3035_; lean_object* v___x_3036_; 
v___x_3035_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___closed__2));
v___x_3036_ = l_Lean_stringToMessageData(v___x_3035_);
return v___x_3036_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___closed__5(void){
_start:
{
lean_object* v___x_3038_; lean_object* v___x_3039_; 
v___x_3038_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___closed__4));
v___x_3039_ = l_Lean_stringToMessageData(v___x_3038_);
return v___x_3039_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5(lean_object* v_a_3040_, lean_object* v_as_3041_, size_t v_sz_3042_, size_t v_i_3043_, lean_object* v_b_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_){
_start:
{
lean_object* v_a_3051_; uint8_t v___x_3055_; 
v___x_3055_ = lean_usize_dec_lt(v_i_3043_, v_sz_3042_);
if (v___x_3055_ == 0)
{
lean_object* v___x_3056_; 
lean_dec_ref(v_a_3040_);
v___x_3056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3056_, 0, v_b_3044_);
return v___x_3056_;
}
else
{
lean_object* v___x_3057_; lean_object* v_a_3058_; lean_object* v___x_3059_; 
v___x_3057_ = lean_box(0);
v_a_3058_ = lean_array_uget_borrowed(v_as_3041_, v_i_3043_);
lean_inc(v_a_3058_);
lean_inc_ref(v_a_3040_);
v___x_3059_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg(v_a_3040_, v_a_3058_, v___y_3046_);
if (lean_obj_tag(v___x_3059_) == 0)
{
lean_object* v_a_3060_; uint8_t v___x_3061_; 
v_a_3060_ = lean_ctor_get(v___x_3059_, 0);
lean_inc(v_a_3060_);
lean_dec_ref_known(v___x_3059_, 1);
v___x_3061_ = lean_unbox(v_a_3060_);
lean_dec(v_a_3060_);
if (v___x_3061_ == 0)
{
v_a_3051_ = v___x_3057_;
goto v___jp_3050_;
}
else
{
uint8_t v___x_3062_; 
v___x_3062_ = l_Lean_Expr_isFVarOf(v_a_3040_, v_a_3058_);
if (v___x_3062_ == 0)
{
lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; 
v___x_3063_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___closed__1);
lean_inc_ref(v_a_3040_);
v___x_3064_ = l_Lean_indentExpr(v_a_3040_);
v___x_3065_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3065_, 0, v___x_3063_);
lean_ctor_set(v___x_3065_, 1, v___x_3064_);
v___x_3066_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___closed__3);
v___x_3067_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3067_, 0, v___x_3065_);
lean_ctor_set(v___x_3067_, 1, v___x_3066_);
lean_inc(v_a_3058_);
v___x_3068_ = l_Lean_mkFVar(v_a_3058_);
v___x_3069_ = l_Lean_indentExpr(v___x_3068_);
v___x_3070_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3070_, 0, v___x_3067_);
lean_ctor_set(v___x_3070_, 1, v___x_3069_);
v___x_3071_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___closed__5);
v___x_3072_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3072_, 0, v___x_3070_);
lean_ctor_set(v___x_3072_, 1, v___x_3071_);
v___x_3073_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg(v___x_3072_, v___y_3045_, v___y_3046_, v___y_3047_, v___y_3048_);
if (lean_obj_tag(v___x_3073_) == 0)
{
lean_dec_ref_known(v___x_3073_, 1);
v_a_3051_ = v___x_3057_;
goto v___jp_3050_;
}
else
{
lean_dec_ref(v_a_3040_);
return v___x_3073_;
}
}
else
{
lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; 
v___x_3074_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___closed__1);
lean_inc_ref(v_a_3040_);
v___x_3075_ = l_Lean_indentExpr(v_a_3040_);
v___x_3076_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3076_, 0, v___x_3074_);
lean_ctor_set(v___x_3076_, 1, v___x_3075_);
v___x_3077_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___closed__5);
v___x_3078_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3078_, 0, v___x_3076_);
lean_ctor_set(v___x_3078_, 1, v___x_3077_);
v___x_3079_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg(v___x_3078_, v___y_3045_, v___y_3046_, v___y_3047_, v___y_3048_);
if (lean_obj_tag(v___x_3079_) == 0)
{
lean_dec_ref_known(v___x_3079_, 1);
v_a_3051_ = v___x_3057_;
goto v___jp_3050_;
}
else
{
lean_dec_ref(v_a_3040_);
return v___x_3079_;
}
}
}
}
else
{
lean_object* v_a_3080_; lean_object* v___x_3082_; uint8_t v_isShared_3083_; uint8_t v_isSharedCheck_3087_; 
lean_dec_ref(v_a_3040_);
v_a_3080_ = lean_ctor_get(v___x_3059_, 0);
v_isSharedCheck_3087_ = !lean_is_exclusive(v___x_3059_);
if (v_isSharedCheck_3087_ == 0)
{
v___x_3082_ = v___x_3059_;
v_isShared_3083_ = v_isSharedCheck_3087_;
goto v_resetjp_3081_;
}
else
{
lean_inc(v_a_3080_);
lean_dec(v___x_3059_);
v___x_3082_ = lean_box(0);
v_isShared_3083_ = v_isSharedCheck_3087_;
goto v_resetjp_3081_;
}
v_resetjp_3081_:
{
lean_object* v___x_3085_; 
if (v_isShared_3083_ == 0)
{
v___x_3085_ = v___x_3082_;
goto v_reusejp_3084_;
}
else
{
lean_object* v_reuseFailAlloc_3086_; 
v_reuseFailAlloc_3086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3086_, 0, v_a_3080_);
v___x_3085_ = v_reuseFailAlloc_3086_;
goto v_reusejp_3084_;
}
v_reusejp_3084_:
{
return v___x_3085_;
}
}
}
}
v___jp_3050_:
{
size_t v___x_3052_; size_t v___x_3053_; 
v___x_3052_ = ((size_t)1ULL);
v___x_3053_ = lean_usize_add(v_i_3043_, v___x_3052_);
v_i_3043_ = v___x_3053_;
v_b_3044_ = v_a_3051_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___boxed(lean_object* v_a_3088_, lean_object* v_as_3089_, lean_object* v_sz_3090_, lean_object* v_i_3091_, lean_object* v_b_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_){
_start:
{
size_t v_sz_boxed_3098_; size_t v_i_boxed_3099_; lean_object* v_res_3100_; 
v_sz_boxed_3098_ = lean_unbox_usize(v_sz_3090_);
lean_dec(v_sz_3090_);
v_i_boxed_3099_ = lean_unbox_usize(v_i_3091_);
lean_dec(v_i_3091_);
v_res_3100_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5(v_a_3088_, v_as_3089_, v_sz_boxed_3098_, v_i_boxed_3099_, v_b_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_);
lean_dec(v___y_3096_);
lean_dec_ref(v___y_3095_);
lean_dec(v___y_3094_);
lean_dec_ref(v___y_3093_);
lean_dec_ref(v_as_3089_);
return v_res_3100_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6(lean_object* v_snd_3101_, lean_object* v_as_3102_, size_t v_sz_3103_, size_t v_i_3104_, lean_object* v_b_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_){
_start:
{
uint8_t v___x_3111_; 
v___x_3111_ = lean_usize_dec_lt(v_i_3104_, v_sz_3103_);
if (v___x_3111_ == 0)
{
lean_object* v___x_3112_; 
v___x_3112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3112_, 0, v_b_3105_);
return v___x_3112_;
}
else
{
lean_object* v___x_3113_; lean_object* v_a_3114_; size_t v_sz_3115_; size_t v___x_3116_; lean_object* v___x_3117_; 
v___x_3113_ = lean_box(0);
v_a_3114_ = lean_array_uget_borrowed(v_as_3102_, v_i_3104_);
v_sz_3115_ = lean_array_size(v_snd_3101_);
v___x_3116_ = ((size_t)0ULL);
lean_inc(v_a_3114_);
v___x_3117_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5(v_a_3114_, v_snd_3101_, v_sz_3115_, v___x_3116_, v___x_3113_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_);
if (lean_obj_tag(v___x_3117_) == 0)
{
size_t v___x_3118_; size_t v___x_3119_; 
lean_dec_ref_known(v___x_3117_, 1);
v___x_3118_ = ((size_t)1ULL);
v___x_3119_ = lean_usize_add(v_i_3104_, v___x_3118_);
v_i_3104_ = v___x_3119_;
v_b_3105_ = v___x_3113_;
goto _start;
}
else
{
return v___x_3117_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___boxed(lean_object* v_snd_3121_, lean_object* v_as_3122_, lean_object* v_sz_3123_, lean_object* v_i_3124_, lean_object* v_b_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_){
_start:
{
size_t v_sz_boxed_3131_; size_t v_i_boxed_3132_; lean_object* v_res_3133_; 
v_sz_boxed_3131_ = lean_unbox_usize(v_sz_3123_);
lean_dec(v_sz_3123_);
v_i_boxed_3132_ = lean_unbox_usize(v_i_3124_);
lean_dec(v_i_3124_);
v_res_3133_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6(v_snd_3121_, v_as_3122_, v_sz_boxed_3131_, v_i_boxed_3132_, v_b_3125_, v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_);
lean_dec(v___y_3129_);
lean_dec_ref(v___y_3128_);
lean_dec(v___y_3127_);
lean_dec_ref(v___y_3126_);
lean_dec_ref(v_as_3122_);
lean_dec_ref(v_snd_3121_);
return v_res_3133_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7(lean_object* v_snd_3134_, lean_object* v_as_3135_, size_t v_sz_3136_, size_t v_i_3137_, lean_object* v_b_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_){
_start:
{
uint8_t v___x_3144_; 
v___x_3144_ = lean_usize_dec_lt(v_i_3137_, v_sz_3136_);
if (v___x_3144_ == 0)
{
lean_object* v___x_3145_; 
v___x_3145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3145_, 0, v_b_3138_);
return v___x_3145_;
}
else
{
lean_object* v_a_3146_; lean_object* v_indGroupInst_3147_; lean_object* v_params_3148_; lean_object* v___x_3149_; size_t v_sz_3150_; size_t v___x_3151_; lean_object* v___x_3152_; 
v_a_3146_ = lean_array_uget_borrowed(v_as_3135_, v_i_3137_);
v_indGroupInst_3147_ = lean_ctor_get(v_a_3146_, 4);
v_params_3148_ = lean_ctor_get(v_indGroupInst_3147_, 2);
v___x_3149_ = lean_box(0);
v_sz_3150_ = lean_array_size(v_params_3148_);
v___x_3151_ = ((size_t)0ULL);
v___x_3152_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6(v_snd_3134_, v_params_3148_, v_sz_3150_, v___x_3151_, v___x_3149_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_);
if (lean_obj_tag(v___x_3152_) == 0)
{
size_t v___x_3153_; size_t v___x_3154_; 
lean_dec_ref_known(v___x_3152_, 1);
v___x_3153_ = ((size_t)1ULL);
v___x_3154_ = lean_usize_add(v_i_3137_, v___x_3153_);
v_i_3137_ = v___x_3154_;
v_b_3138_ = v___x_3149_;
goto _start;
}
else
{
return v___x_3152_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7___boxed(lean_object* v_snd_3156_, lean_object* v_as_3157_, lean_object* v_sz_3158_, lean_object* v_i_3159_, lean_object* v_b_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_){
_start:
{
size_t v_sz_boxed_3166_; size_t v_i_boxed_3167_; lean_object* v_res_3168_; 
v_sz_boxed_3166_ = lean_unbox_usize(v_sz_3158_);
lean_dec(v_sz_3158_);
v_i_boxed_3167_ = lean_unbox_usize(v_i_3159_);
lean_dec(v_i_3159_);
v_res_3168_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7(v_snd_3156_, v_as_3157_, v_sz_boxed_3166_, v_i_boxed_3167_, v_b_3160_, v___y_3161_, v___y_3162_, v___y_3163_, v___y_3164_);
lean_dec(v___y_3164_);
lean_dec_ref(v___y_3163_);
lean_dec(v___y_3162_);
lean_dec_ref(v___y_3161_);
lean_dec_ref(v_as_3157_);
lean_dec_ref(v_snd_3156_);
return v_res_3168_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__3___redArg(lean_object* v_fst_3169_, size_t v_sz_3170_, size_t v_i_3171_, lean_object* v_bs_3172_){
_start:
{
uint8_t v___x_3173_; 
v___x_3173_ = lean_usize_dec_lt(v_i_3171_, v_sz_3170_);
if (v___x_3173_ == 0)
{
return v_bs_3172_;
}
else
{
lean_object* v_v_3174_; lean_object* v_fnName_3175_; lean_object* v_recArgPos_3176_; lean_object* v_indicesPos_3177_; lean_object* v_indGroupInst_3178_; lean_object* v_indIdx_3179_; lean_object* v___x_3181_; uint8_t v_isShared_3182_; uint8_t v_isSharedCheck_3196_; 
v_v_3174_ = lean_array_uget(v_bs_3172_, v_i_3171_);
v_fnName_3175_ = lean_ctor_get(v_v_3174_, 0);
v_recArgPos_3176_ = lean_ctor_get(v_v_3174_, 2);
v_indicesPos_3177_ = lean_ctor_get(v_v_3174_, 3);
v_indGroupInst_3178_ = lean_ctor_get(v_v_3174_, 4);
v_indIdx_3179_ = lean_ctor_get(v_v_3174_, 5);
v_isSharedCheck_3196_ = !lean_is_exclusive(v_v_3174_);
if (v_isSharedCheck_3196_ == 0)
{
lean_object* v_unused_3197_; 
v_unused_3197_ = lean_ctor_get(v_v_3174_, 1);
lean_dec(v_unused_3197_);
v___x_3181_ = v_v_3174_;
v_isShared_3182_ = v_isSharedCheck_3196_;
goto v_resetjp_3180_;
}
else
{
lean_inc(v_indIdx_3179_);
lean_inc(v_indGroupInst_3178_);
lean_inc(v_indicesPos_3177_);
lean_inc(v_recArgPos_3176_);
lean_inc(v_fnName_3175_);
lean_dec(v_v_3174_);
v___x_3181_ = lean_box(0);
v_isShared_3182_ = v_isSharedCheck_3196_;
goto v_resetjp_3180_;
}
v_resetjp_3180_:
{
lean_object* v_perms_3183_; lean_object* v___x_3184_; lean_object* v_bs_x27_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3190_; 
v_perms_3183_ = lean_ctor_get(v_fst_3169_, 1);
v___x_3184_ = lean_unsigned_to_nat(0u);
v_bs_x27_3185_ = lean_array_uset(v_bs_3172_, v_i_3171_, v___x_3184_);
v___x_3186_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0);
v___x_3187_ = lean_usize_to_nat(v_i_3171_);
v___x_3188_ = lean_array_get_borrowed(v___x_3186_, v_perms_3183_, v___x_3187_);
lean_dec(v___x_3187_);
lean_inc(v___x_3188_);
if (v_isShared_3182_ == 0)
{
lean_ctor_set(v___x_3181_, 1, v___x_3188_);
v___x_3190_ = v___x_3181_;
goto v_reusejp_3189_;
}
else
{
lean_object* v_reuseFailAlloc_3195_; 
v_reuseFailAlloc_3195_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3195_, 0, v_fnName_3175_);
lean_ctor_set(v_reuseFailAlloc_3195_, 1, v___x_3188_);
lean_ctor_set(v_reuseFailAlloc_3195_, 2, v_recArgPos_3176_);
lean_ctor_set(v_reuseFailAlloc_3195_, 3, v_indicesPos_3177_);
lean_ctor_set(v_reuseFailAlloc_3195_, 4, v_indGroupInst_3178_);
lean_ctor_set(v_reuseFailAlloc_3195_, 5, v_indIdx_3179_);
v___x_3190_ = v_reuseFailAlloc_3195_;
goto v_reusejp_3189_;
}
v_reusejp_3189_:
{
size_t v___x_3191_; size_t v___x_3192_; lean_object* v___x_3193_; 
v___x_3191_ = ((size_t)1ULL);
v___x_3192_ = lean_usize_add(v_i_3171_, v___x_3191_);
v___x_3193_ = lean_array_uset(v_bs_x27_3185_, v_i_3171_, v___x_3190_);
v_i_3171_ = v___x_3192_;
v_bs_3172_ = v___x_3193_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__3___redArg___boxed(lean_object* v_fst_3198_, lean_object* v_sz_3199_, lean_object* v_i_3200_, lean_object* v_bs_3201_){
_start:
{
size_t v_sz_boxed_3202_; size_t v_i_boxed_3203_; lean_object* v_res_3204_; 
v_sz_boxed_3202_ = lean_unbox_usize(v_sz_3199_);
lean_dec(v_sz_3199_);
v_i_boxed_3203_ = lean_unbox_usize(v_i_3200_);
lean_dec(v_i_3200_);
v_res_3204_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__3___redArg(v_fst_3198_, v_sz_boxed_3202_, v_i_boxed_3203_, v_bs_3201_);
lean_dec_ref(v_fst_3198_);
return v_res_3204_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__13_spec__16_spec__20(lean_object* v_x_3205_, lean_object* v_x_3206_, lean_object* v_x_3207_){
_start:
{
if (lean_obj_tag(v_x_3207_) == 0)
{
lean_dec(v_x_3205_);
return v_x_3206_;
}
else
{
lean_object* v_head_3208_; lean_object* v_tail_3209_; lean_object* v___x_3211_; uint8_t v_isShared_3212_; uint8_t v_isSharedCheck_3219_; 
v_head_3208_ = lean_ctor_get(v_x_3207_, 0);
v_tail_3209_ = lean_ctor_get(v_x_3207_, 1);
v_isSharedCheck_3219_ = !lean_is_exclusive(v_x_3207_);
if (v_isSharedCheck_3219_ == 0)
{
v___x_3211_ = v_x_3207_;
v_isShared_3212_ = v_isSharedCheck_3219_;
goto v_resetjp_3210_;
}
else
{
lean_inc(v_tail_3209_);
lean_inc(v_head_3208_);
lean_dec(v_x_3207_);
v___x_3211_ = lean_box(0);
v_isShared_3212_ = v_isSharedCheck_3219_;
goto v_resetjp_3210_;
}
v_resetjp_3210_:
{
lean_object* v___x_3214_; 
lean_inc(v_x_3205_);
if (v_isShared_3212_ == 0)
{
lean_ctor_set_tag(v___x_3211_, 5);
lean_ctor_set(v___x_3211_, 1, v_x_3205_);
lean_ctor_set(v___x_3211_, 0, v_x_3206_);
v___x_3214_ = v___x_3211_;
goto v_reusejp_3213_;
}
else
{
lean_object* v_reuseFailAlloc_3218_; 
v_reuseFailAlloc_3218_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3218_, 0, v_x_3206_);
lean_ctor_set(v_reuseFailAlloc_3218_, 1, v_x_3205_);
v___x_3214_ = v_reuseFailAlloc_3218_;
goto v_reusejp_3213_;
}
v_reusejp_3213_:
{
lean_object* v___x_3215_; lean_object* v___x_3216_; 
v___x_3215_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(v_head_3208_);
v___x_3216_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3216_, 0, v___x_3214_);
lean_ctor_set(v___x_3216_, 1, v___x_3215_);
v_x_3206_ = v___x_3216_;
v_x_3207_ = v_tail_3209_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__13_spec__16(lean_object* v_x_3220_, lean_object* v_x_3221_, lean_object* v_x_3222_){
_start:
{
if (lean_obj_tag(v_x_3222_) == 0)
{
lean_dec(v_x_3220_);
return v_x_3221_;
}
else
{
lean_object* v_head_3223_; lean_object* v_tail_3224_; lean_object* v___x_3226_; uint8_t v_isShared_3227_; uint8_t v_isSharedCheck_3234_; 
v_head_3223_ = lean_ctor_get(v_x_3222_, 0);
v_tail_3224_ = lean_ctor_get(v_x_3222_, 1);
v_isSharedCheck_3234_ = !lean_is_exclusive(v_x_3222_);
if (v_isSharedCheck_3234_ == 0)
{
v___x_3226_ = v_x_3222_;
v_isShared_3227_ = v_isSharedCheck_3234_;
goto v_resetjp_3225_;
}
else
{
lean_inc(v_tail_3224_);
lean_inc(v_head_3223_);
lean_dec(v_x_3222_);
v___x_3226_ = lean_box(0);
v_isShared_3227_ = v_isSharedCheck_3234_;
goto v_resetjp_3225_;
}
v_resetjp_3225_:
{
lean_object* v___x_3229_; 
lean_inc(v_x_3220_);
if (v_isShared_3227_ == 0)
{
lean_ctor_set_tag(v___x_3226_, 5);
lean_ctor_set(v___x_3226_, 1, v_x_3220_);
lean_ctor_set(v___x_3226_, 0, v_x_3221_);
v___x_3229_ = v___x_3226_;
goto v_reusejp_3228_;
}
else
{
lean_object* v_reuseFailAlloc_3233_; 
v_reuseFailAlloc_3233_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3233_, 0, v_x_3221_);
lean_ctor_set(v_reuseFailAlloc_3233_, 1, v_x_3220_);
v___x_3229_ = v_reuseFailAlloc_3233_;
goto v_reusejp_3228_;
}
v_reusejp_3228_:
{
lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; 
v___x_3230_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(v_head_3223_);
v___x_3231_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3231_, 0, v___x_3229_);
lean_ctor_set(v___x_3231_, 1, v___x_3230_);
v___x_3232_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__13_spec__16_spec__20(v_x_3220_, v___x_3231_, v_tail_3224_);
return v___x_3232_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__13(lean_object* v_x_3235_, lean_object* v_x_3236_){
_start:
{
if (lean_obj_tag(v_x_3235_) == 0)
{
lean_object* v___x_3237_; 
lean_dec(v_x_3236_);
v___x_3237_ = lean_box(0);
return v___x_3237_;
}
else
{
lean_object* v_tail_3238_; 
v_tail_3238_ = lean_ctor_get(v_x_3235_, 1);
if (lean_obj_tag(v_tail_3238_) == 0)
{
lean_object* v_head_3239_; lean_object* v___x_3240_; 
lean_dec(v_x_3236_);
v_head_3239_ = lean_ctor_get(v_x_3235_, 0);
lean_inc(v_head_3239_);
lean_dec_ref_known(v_x_3235_, 2);
v___x_3240_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(v_head_3239_);
return v___x_3240_;
}
else
{
lean_object* v_head_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; 
lean_inc(v_tail_3238_);
v_head_3241_ = lean_ctor_get(v_x_3235_, 0);
lean_inc(v_head_3241_);
lean_dec_ref_known(v_x_3235_, 2);
v___x_3242_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(v_head_3241_);
v___x_3243_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__13_spec__16(v_x_3236_, v___x_3242_, v_tail_3238_);
return v___x_3243_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___closed__5(void){
_start:
{
lean_object* v___x_3252_; lean_object* v___x_3253_; 
v___x_3252_ = ((lean_object*)(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___closed__0));
v___x_3253_ = lean_string_length(v___x_3252_);
return v___x_3253_;
}
}
static lean_object* _init_l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___closed__6(void){
_start:
{
lean_object* v___x_3254_; lean_object* v___x_3255_; 
v___x_3254_ = lean_obj_once(&l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___closed__5, &l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___closed__5_once, _init_l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___closed__5);
v___x_3255_ = lean_nat_to_int(v___x_3254_);
return v___x_3255_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9(lean_object* v_xs_3263_){
_start:
{
lean_object* v___x_3264_; lean_object* v___x_3265_; uint8_t v___x_3266_; 
v___x_3264_ = lean_array_get_size(v_xs_3263_);
v___x_3265_ = lean_unsigned_to_nat(0u);
v___x_3266_ = lean_nat_dec_eq(v___x_3264_, v___x_3265_);
if (v___x_3266_ == 0)
{
lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; 
v___x_3267_ = lean_array_to_list(v_xs_3263_);
v___x_3268_ = ((lean_object*)(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___closed__3));
v___x_3269_ = l_Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__13(v___x_3267_, v___x_3268_);
v___x_3270_ = lean_obj_once(&l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___closed__6, &l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___closed__6_once, _init_l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___closed__6);
v___x_3271_ = ((lean_object*)(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___closed__7));
v___x_3272_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3272_, 0, v___x_3271_);
lean_ctor_set(v___x_3272_, 1, v___x_3269_);
v___x_3273_ = ((lean_object*)(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___closed__8));
v___x_3274_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3274_, 0, v___x_3272_);
lean_ctor_set(v___x_3274_, 1, v___x_3273_);
v___x_3275_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3275_, 0, v___x_3270_);
lean_ctor_set(v___x_3275_, 1, v___x_3274_);
v___x_3276_ = l_Std_Format_fill(v___x_3275_);
return v___x_3276_;
}
else
{
lean_object* v___x_3277_; 
lean_dec_ref(v_xs_3263_);
v___x_3277_ = ((lean_object*)(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___closed__10));
return v___x_3277_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10(size_t v_sz_3278_, size_t v_i_3279_, lean_object* v_bs_3280_){
_start:
{
uint8_t v___x_3281_; 
v___x_3281_ = lean_usize_dec_lt(v_i_3279_, v_sz_3278_);
if (v___x_3281_ == 0)
{
return v_bs_3280_;
}
else
{
lean_object* v_v_3282_; lean_object* v___x_3283_; lean_object* v_bs_x27_3284_; lean_object* v___x_3285_; size_t v___x_3286_; size_t v___x_3287_; lean_object* v___x_3288_; 
v_v_3282_ = lean_array_uget(v_bs_3280_, v_i_3279_);
v___x_3283_ = lean_unsigned_to_nat(0u);
v_bs_x27_3284_ = lean_array_uset(v_bs_3280_, v_i_3279_, v___x_3283_);
v___x_3285_ = l_Lean_mkFVar(v_v_3282_);
v___x_3286_ = ((size_t)1ULL);
v___x_3287_ = lean_usize_add(v_i_3279_, v___x_3286_);
v___x_3288_ = lean_array_uset(v_bs_x27_3284_, v_i_3279_, v___x_3285_);
v_i_3279_ = v___x_3287_;
v_bs_3280_ = v___x_3288_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___boxed(lean_object* v_sz_3290_, lean_object* v_i_3291_, lean_object* v_bs_3292_){
_start:
{
size_t v_sz_boxed_3293_; size_t v_i_boxed_3294_; lean_object* v_res_3295_; 
v_sz_boxed_3293_ = lean_unbox_usize(v_sz_3290_);
lean_dec(v_sz_3290_);
v_i_boxed_3294_ = lean_unbox_usize(v_i_3291_);
lean_dec(v_i_3291_);
v_res_3295_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10(v_sz_boxed_3293_, v_i_boxed_3294_, v_bs_3292_);
return v_res_3295_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__2(size_t v_sz_3296_, size_t v_i_3297_, lean_object* v_bs_3298_){
_start:
{
uint8_t v___x_3299_; 
v___x_3299_ = lean_usize_dec_lt(v_i_3297_, v_sz_3296_);
if (v___x_3299_ == 0)
{
return v_bs_3298_;
}
else
{
lean_object* v_v_3300_; lean_object* v___x_3301_; lean_object* v_bs_x27_3302_; lean_object* v___x_3303_; size_t v___x_3304_; size_t v___x_3305_; lean_object* v___x_3306_; 
v_v_3300_ = lean_array_uget(v_bs_3298_, v_i_3297_);
v___x_3301_ = lean_unsigned_to_nat(0u);
v_bs_x27_3302_ = lean_array_uset(v_bs_3298_, v_i_3297_, v___x_3301_);
v___x_3303_ = l_Lean_Elab_Structural_RecArgInfo_indicesAndRecArgPos(v_v_3300_);
v___x_3304_ = ((size_t)1ULL);
v___x_3305_ = lean_usize_add(v_i_3297_, v___x_3304_);
v___x_3306_ = lean_array_uset(v_bs_x27_3302_, v_i_3297_, v___x_3303_);
v_i_3297_ = v___x_3305_;
v_bs_3298_ = v___x_3306_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__2___boxed(lean_object* v_sz_3308_, lean_object* v_i_3309_, lean_object* v_bs_3310_){
_start:
{
size_t v_sz_boxed_3311_; size_t v_i_boxed_3312_; lean_object* v_res_3313_; 
v_sz_boxed_3311_ = lean_unbox_usize(v_sz_3308_);
lean_dec(v_sz_3308_);
v_i_boxed_3312_ = lean_unbox_usize(v_i_3309_);
lean_dec(v_i_3309_);
v_res_3313_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__2(v_sz_boxed_3311_, v_i_boxed_3312_, v_bs_3310_);
return v_res_3313_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__0(void){
_start:
{
lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; 
v___x_3314_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__5));
v___x_3315_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___closed__1));
v___x_3316_ = l_Lean_Name_append(v___x_3315_, v___x_3314_);
return v___x_3316_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3318_; lean_object* v___x_3319_; 
v___x_3318_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__1));
v___x_3319_ = l_Lean_stringToMessageData(v___x_3318_);
return v___x_3319_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__4(void){
_start:
{
lean_object* v___x_3321_; lean_object* v___x_3322_; 
v___x_3321_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__3));
v___x_3322_ = l_Lean_stringToMessageData(v___x_3321_);
return v___x_3322_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__6(void){
_start:
{
lean_object* v___x_3324_; lean_object* v___x_3325_; 
v___x_3324_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__5));
v___x_3325_ = l_Lean_stringToMessageData(v___x_3324_);
return v___x_3325_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__8(void){
_start:
{
lean_object* v___x_3327_; lean_object* v___x_3328_; 
v___x_3327_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__7));
v___x_3328_ = l_Lean_stringToMessageData(v___x_3327_);
return v___x_3328_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__10(void){
_start:
{
lean_object* v___x_3330_; lean_object* v___x_3331_; 
v___x_3330_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__9));
v___x_3331_ = l_Lean_stringToMessageData(v___x_3330_);
return v___x_3331_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0(size_t v___x_3332_, lean_object* v_a_3333_, lean_object* v_xs_3334_, lean_object* v_a_3335_, lean_object* v_recArgInfos_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_){
_start:
{
lean_object* v___y_3343_; lean_object* v___y_3344_; lean_object* v___y_3345_; lean_object* v___y_3346_; lean_object* v___y_3347_; lean_object* v___y_3348_; lean_object* v___y_3349_; size_t v_sz_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___y_3366_; lean_object* v___y_3367_; lean_object* v___y_3368_; lean_object* v___y_3369_; lean_object* v___y_3370_; lean_object* v___y_3371_; lean_object* v___y_3372_; lean_object* v___x_3449_; lean_object* v_a_3450_; uint8_t v___x_3451_; 
v_sz_3362_ = lean_array_size(v_recArgInfos_3336_);
lean_inc_ref(v_recArgInfos_3336_);
v___x_3363_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1(v_sz_3362_, v___x_3332_, v_recArgInfos_3336_);
v___x_3364_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__5));
v___x_3449_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1(v___x_3364_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_);
v_a_3450_ = lean_ctor_get(v___x_3449_, 0);
lean_inc(v_a_3450_);
lean_dec_ref(v___x_3449_);
v___x_3451_ = lean_unbox(v_a_3450_);
lean_dec(v_a_3450_);
if (v___x_3451_ == 0)
{
goto v___jp_3392_;
}
else
{
lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; 
v___x_3452_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__10, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__10);
lean_inc_ref(v___x_3363_);
v___x_3453_ = lean_array_to_list(v___x_3363_);
v___x_3454_ = lean_box(0);
v___x_3455_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__0(v___x_3453_, v___x_3454_);
v___x_3456_ = l_Lean_MessageData_ofList(v___x_3455_);
v___x_3457_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3457_, 0, v___x_3452_);
lean_ctor_set(v___x_3457_, 1, v___x_3456_);
v___x_3458_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_3364_, v___x_3457_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_);
if (lean_obj_tag(v___x_3458_) == 0)
{
lean_dec_ref_known(v___x_3458_, 1);
goto v___jp_3392_;
}
else
{
lean_object* v_a_3459_; lean_object* v___x_3461_; uint8_t v_isShared_3462_; uint8_t v_isSharedCheck_3466_; 
lean_dec_ref(v___x_3363_);
lean_dec_ref(v_recArgInfos_3336_);
lean_dec_ref(v_a_3335_);
lean_dec_ref(v_xs_3334_);
lean_dec_ref(v_a_3333_);
v_a_3459_ = lean_ctor_get(v___x_3458_, 0);
v_isSharedCheck_3466_ = !lean_is_exclusive(v___x_3458_);
if (v_isSharedCheck_3466_ == 0)
{
v___x_3461_ = v___x_3458_;
v_isShared_3462_ = v_isSharedCheck_3466_;
goto v_resetjp_3460_;
}
else
{
lean_inc(v_a_3459_);
lean_dec(v___x_3458_);
v___x_3461_ = lean_box(0);
v_isShared_3462_ = v_isSharedCheck_3466_;
goto v_resetjp_3460_;
}
v_resetjp_3460_:
{
lean_object* v___x_3464_; 
if (v_isShared_3462_ == 0)
{
v___x_3464_ = v___x_3461_;
goto v_reusejp_3463_;
}
else
{
lean_object* v_reuseFailAlloc_3465_; 
v_reuseFailAlloc_3465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3465_, 0, v_a_3459_);
v___x_3464_ = v_reuseFailAlloc_3465_;
goto v_reusejp_3463_;
}
v_reusejp_3463_:
{
return v___x_3464_;
}
}
}
}
v___jp_3342_:
{
lean_object* v___x_3350_; size_t v_sz_3351_; lean_object* v___x_3352_; 
v___x_3350_ = lean_box(0);
v_sz_3351_ = lean_array_size(v___y_3343_);
v___x_3352_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7(v___y_3344_, v___y_3343_, v_sz_3351_, v___x_3332_, v___x_3350_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_);
lean_dec_ref(v___y_3343_);
if (lean_obj_tag(v___x_3352_) == 0)
{
lean_object* v___x_3353_; 
lean_dec_ref_known(v___x_3352_, 1);
v___x_3353_ = l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8___redArg(v___y_3344_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_);
lean_dec_ref(v___y_3344_);
return v___x_3353_;
}
else
{
lean_object* v_a_3354_; lean_object* v___x_3356_; uint8_t v_isShared_3357_; uint8_t v_isSharedCheck_3361_; 
lean_dec_ref(v___y_3345_);
lean_dec_ref(v___y_3344_);
v_a_3354_ = lean_ctor_get(v___x_3352_, 0);
v_isSharedCheck_3361_ = !lean_is_exclusive(v___x_3352_);
if (v_isSharedCheck_3361_ == 0)
{
v___x_3356_ = v___x_3352_;
v_isShared_3357_ = v_isSharedCheck_3361_;
goto v_resetjp_3355_;
}
else
{
lean_inc(v_a_3354_);
lean_dec(v___x_3352_);
v___x_3356_ = lean_box(0);
v_isShared_3357_ = v_isSharedCheck_3361_;
goto v_resetjp_3355_;
}
v_resetjp_3355_:
{
lean_object* v___x_3359_; 
if (v_isShared_3357_ == 0)
{
v___x_3359_ = v___x_3356_;
goto v_reusejp_3358_;
}
else
{
lean_object* v_reuseFailAlloc_3360_; 
v_reuseFailAlloc_3360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3360_, 0, v_a_3354_);
v___x_3359_ = v_reuseFailAlloc_3360_;
goto v_reusejp_3358_;
}
v_reusejp_3358_:
{
return v___x_3359_;
}
}
}
}
v___jp_3365_:
{
lean_object* v_toCold_3373_; lean_object* v_options_3374_; uint8_t v_hasTrace_3375_; 
v_toCold_3373_ = lean_ctor_get(v___y_3371_, 0);
v_options_3374_ = lean_ctor_get(v_toCold_3373_, 2);
v_hasTrace_3375_ = lean_ctor_get_uint8(v_options_3374_, sizeof(void*)*1);
if (v_hasTrace_3375_ == 0)
{
v___y_3343_ = v___y_3366_;
v___y_3344_ = v___y_3367_;
v___y_3345_ = v___y_3368_;
v___y_3346_ = v___y_3369_;
v___y_3347_ = v___y_3370_;
v___y_3348_ = v___y_3371_;
v___y_3349_ = v___y_3372_;
goto v___jp_3342_;
}
else
{
lean_object* v_inheritedTraceOptions_3376_; lean_object* v___x_3377_; uint8_t v___x_3378_; 
v_inheritedTraceOptions_3376_ = lean_ctor_get(v_toCold_3373_, 11);
v___x_3377_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__0);
v___x_3378_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3376_, v_options_3374_, v___x_3377_);
if (v___x_3378_ == 0)
{
v___y_3343_ = v___y_3366_;
v___y_3344_ = v___y_3367_;
v___y_3345_ = v___y_3368_;
v___y_3346_ = v___y_3369_;
v___y_3347_ = v___y_3370_;
v___y_3348_ = v___y_3371_;
v___y_3349_ = v___y_3372_;
goto v___jp_3342_;
}
else
{
lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; 
v___x_3379_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__2);
lean_inc_ref(v___y_3366_);
v___x_3380_ = l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9(v___y_3366_);
v___x_3381_ = l_Lean_MessageData_ofFormat(v___x_3380_);
v___x_3382_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3382_, 0, v___x_3379_);
lean_ctor_set(v___x_3382_, 1, v___x_3381_);
v___x_3383_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_3364_, v___x_3382_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_);
if (lean_obj_tag(v___x_3383_) == 0)
{
lean_dec_ref_known(v___x_3383_, 1);
v___y_3343_ = v___y_3366_;
v___y_3344_ = v___y_3367_;
v___y_3345_ = v___y_3368_;
v___y_3346_ = v___y_3369_;
v___y_3347_ = v___y_3370_;
v___y_3348_ = v___y_3371_;
v___y_3349_ = v___y_3372_;
goto v___jp_3342_;
}
else
{
lean_object* v_a_3384_; lean_object* v___x_3386_; uint8_t v_isShared_3387_; uint8_t v_isSharedCheck_3391_; 
lean_dec_ref(v___y_3368_);
lean_dec_ref(v___y_3367_);
lean_dec_ref(v___y_3366_);
v_a_3384_ = lean_ctor_get(v___x_3383_, 0);
v_isSharedCheck_3391_ = !lean_is_exclusive(v___x_3383_);
if (v_isSharedCheck_3391_ == 0)
{
v___x_3386_ = v___x_3383_;
v_isShared_3387_ = v_isSharedCheck_3391_;
goto v_resetjp_3385_;
}
else
{
lean_inc(v_a_3384_);
lean_dec(v___x_3383_);
v___x_3386_ = lean_box(0);
v_isShared_3387_ = v_isSharedCheck_3391_;
goto v_resetjp_3385_;
}
v_resetjp_3385_:
{
lean_object* v___x_3389_; 
if (v_isShared_3387_ == 0)
{
v___x_3389_ = v___x_3386_;
goto v_reusejp_3388_;
}
else
{
lean_object* v_reuseFailAlloc_3390_; 
v_reuseFailAlloc_3390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3390_, 0, v_a_3384_);
v___x_3389_ = v_reuseFailAlloc_3390_;
goto v_reusejp_3388_;
}
v_reusejp_3388_:
{
return v___x_3389_;
}
}
}
}
}
}
v___jp_3392_:
{
lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v_snd_3395_; lean_object* v_fst_3396_; lean_object* v___x_3398_; uint8_t v_isShared_3399_; uint8_t v_isSharedCheck_3448_; 
lean_inc_ref(v_recArgInfos_3336_);
v___x_3393_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__2(v_sz_3362_, v___x_3332_, v_recArgInfos_3336_);
lean_inc_ref(v_xs_3334_);
v___x_3394_ = l_Lean_Elab_FixedParamPerms_erase(v_a_3333_, v_xs_3334_, v___x_3393_);
v_snd_3395_ = lean_ctor_get(v___x_3394_, 1);
v_fst_3396_ = lean_ctor_get(v___x_3394_, 0);
v_isSharedCheck_3448_ = !lean_is_exclusive(v___x_3394_);
if (v_isSharedCheck_3448_ == 0)
{
v___x_3398_ = v___x_3394_;
v_isShared_3399_ = v_isSharedCheck_3448_;
goto v_resetjp_3397_;
}
else
{
lean_inc(v_snd_3395_);
lean_inc(v_fst_3396_);
lean_dec(v___x_3394_);
v___x_3398_ = lean_box(0);
v_isShared_3399_ = v_isSharedCheck_3448_;
goto v_resetjp_3397_;
}
v_resetjp_3397_:
{
lean_object* v_fst_3400_; lean_object* v_snd_3401_; lean_object* v___x_3403_; uint8_t v_isShared_3404_; uint8_t v_isSharedCheck_3447_; 
v_fst_3400_ = lean_ctor_get(v_snd_3395_, 0);
v_snd_3401_ = lean_ctor_get(v_snd_3395_, 1);
v_isSharedCheck_3447_ = !lean_is_exclusive(v_snd_3395_);
if (v_isSharedCheck_3447_ == 0)
{
v___x_3403_ = v_snd_3395_;
v_isShared_3404_ = v_isSharedCheck_3447_;
goto v_resetjp_3402_;
}
else
{
lean_inc(v_snd_3401_);
lean_inc(v_fst_3400_);
lean_dec(v_snd_3395_);
v___x_3403_ = lean_box(0);
v_isShared_3404_ = v_isSharedCheck_3447_;
goto v_resetjp_3402_;
}
v_resetjp_3402_:
{
lean_object* v___x_3405_; lean_object* v___f_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; uint8_t v___x_3409_; 
v___x_3405_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__3___redArg(v_fst_3396_, v_sz_3362_, v___x_3332_, v_recArgInfos_3336_);
lean_inc_ref(v___x_3405_);
lean_inc(v_fst_3400_);
v___f_3406_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___boxed), 10, 5);
lean_closure_set(v___f_3406_, 0, v_a_3335_);
lean_closure_set(v___f_3406_, 1, v_fst_3396_);
lean_closure_set(v___f_3406_, 2, v_fst_3400_);
lean_closure_set(v___f_3406_, 3, v___x_3405_);
lean_closure_set(v___f_3406_, 4, v___x_3363_);
v___x_3407_ = lean_array_get_size(v_fst_3400_);
v___x_3408_ = lean_array_get_size(v_xs_3334_);
v___x_3409_ = lean_nat_dec_eq(v___x_3407_, v___x_3408_);
if (v___x_3409_ == 0)
{
lean_object* v___x_3410_; lean_object* v_a_3411_; uint8_t v___x_3412_; 
v___x_3410_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1(v___x_3364_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_);
v_a_3411_ = lean_ctor_get(v___x_3410_, 0);
lean_inc(v_a_3411_);
lean_dec_ref(v___x_3410_);
v___x_3412_ = lean_unbox(v_a_3411_);
lean_dec(v_a_3411_);
if (v___x_3412_ == 0)
{
lean_del_object(v___x_3403_);
lean_dec(v_fst_3400_);
lean_del_object(v___x_3398_);
lean_dec_ref(v_xs_3334_);
v___y_3366_ = v___x_3405_;
v___y_3367_ = v_snd_3401_;
v___y_3368_ = v___f_3406_;
v___y_3369_ = v___y_3337_;
v___y_3370_ = v___y_3338_;
v___y_3371_ = v___y_3339_;
v___y_3372_ = v___y_3340_;
goto v___jp_3365_;
}
else
{
lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3419_; 
v___x_3413_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__4);
v___x_3414_ = lean_array_to_list(v_xs_3334_);
v___x_3415_ = lean_box(0);
v___x_3416_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_3414_, v___x_3415_);
v___x_3417_ = l_Lean_MessageData_ofList(v___x_3416_);
if (v_isShared_3404_ == 0)
{
lean_ctor_set_tag(v___x_3403_, 7);
lean_ctor_set(v___x_3403_, 1, v___x_3417_);
lean_ctor_set(v___x_3403_, 0, v___x_3413_);
v___x_3419_ = v___x_3403_;
goto v_reusejp_3418_;
}
else
{
lean_object* v_reuseFailAlloc_3445_; 
v_reuseFailAlloc_3445_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3445_, 0, v___x_3413_);
lean_ctor_set(v_reuseFailAlloc_3445_, 1, v___x_3417_);
v___x_3419_ = v_reuseFailAlloc_3445_;
goto v_reusejp_3418_;
}
v_reusejp_3418_:
{
lean_object* v___x_3420_; lean_object* v___x_3422_; 
v___x_3420_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__6, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__6);
if (v_isShared_3399_ == 0)
{
lean_ctor_set_tag(v___x_3398_, 7);
lean_ctor_set(v___x_3398_, 1, v___x_3420_);
lean_ctor_set(v___x_3398_, 0, v___x_3419_);
v___x_3422_ = v___x_3398_;
goto v_reusejp_3421_;
}
else
{
lean_object* v_reuseFailAlloc_3444_; 
v_reuseFailAlloc_3444_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3444_, 0, v___x_3419_);
lean_ctor_set(v_reuseFailAlloc_3444_, 1, v___x_3420_);
v___x_3422_ = v_reuseFailAlloc_3444_;
goto v_reusejp_3421_;
}
v_reusejp_3421_:
{
lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; size_t v_sz_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; 
v___x_3423_ = lean_array_to_list(v_fst_3400_);
v___x_3424_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_3423_, v___x_3415_);
v___x_3425_ = l_Lean_MessageData_ofList(v___x_3424_);
v___x_3426_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3426_, 0, v___x_3422_);
lean_ctor_set(v___x_3426_, 1, v___x_3425_);
v___x_3427_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__8);
v___x_3428_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3428_, 0, v___x_3426_);
lean_ctor_set(v___x_3428_, 1, v___x_3427_);
v_sz_3429_ = lean_array_size(v_snd_3401_);
lean_inc(v_snd_3401_);
v___x_3430_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10(v_sz_3429_, v___x_3332_, v_snd_3401_);
v___x_3431_ = lean_array_to_list(v___x_3430_);
v___x_3432_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_3431_, v___x_3415_);
v___x_3433_ = l_Lean_MessageData_ofList(v___x_3432_);
v___x_3434_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3434_, 0, v___x_3428_);
lean_ctor_set(v___x_3434_, 1, v___x_3433_);
v___x_3435_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_3364_, v___x_3434_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_);
if (lean_obj_tag(v___x_3435_) == 0)
{
lean_dec_ref_known(v___x_3435_, 1);
v___y_3366_ = v___x_3405_;
v___y_3367_ = v_snd_3401_;
v___y_3368_ = v___f_3406_;
v___y_3369_ = v___y_3337_;
v___y_3370_ = v___y_3338_;
v___y_3371_ = v___y_3339_;
v___y_3372_ = v___y_3340_;
goto v___jp_3365_;
}
else
{
lean_object* v_a_3436_; lean_object* v___x_3438_; uint8_t v_isShared_3439_; uint8_t v_isSharedCheck_3443_; 
lean_dec_ref(v___f_3406_);
lean_dec_ref(v___x_3405_);
lean_dec(v_snd_3401_);
v_a_3436_ = lean_ctor_get(v___x_3435_, 0);
v_isSharedCheck_3443_ = !lean_is_exclusive(v___x_3435_);
if (v_isSharedCheck_3443_ == 0)
{
v___x_3438_ = v___x_3435_;
v_isShared_3439_ = v_isSharedCheck_3443_;
goto v_resetjp_3437_;
}
else
{
lean_inc(v_a_3436_);
lean_dec(v___x_3435_);
v___x_3438_ = lean_box(0);
v_isShared_3439_ = v_isSharedCheck_3443_;
goto v_resetjp_3437_;
}
v_resetjp_3437_:
{
lean_object* v___x_3441_; 
if (v_isShared_3439_ == 0)
{
v___x_3441_ = v___x_3438_;
goto v_reusejp_3440_;
}
else
{
lean_object* v_reuseFailAlloc_3442_; 
v_reuseFailAlloc_3442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3442_, 0, v_a_3436_);
v___x_3441_ = v_reuseFailAlloc_3442_;
goto v_reusejp_3440_;
}
v_reusejp_3440_:
{
return v___x_3441_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3446_; 
lean_dec_ref(v___x_3405_);
lean_del_object(v___x_3403_);
lean_dec(v_fst_3400_);
lean_del_object(v___x_3398_);
lean_dec_ref(v_xs_3334_);
v___x_3446_ = l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8___redArg(v_snd_3401_, v___f_3406_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_);
lean_dec(v_snd_3401_);
return v___x_3446_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___boxed(lean_object* v___x_3467_, lean_object* v_a_3468_, lean_object* v_xs_3469_, lean_object* v_a_3470_, lean_object* v_recArgInfos_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_){
_start:
{
size_t v___x_12976__boxed_3477_; lean_object* v_res_3478_; 
v___x_12976__boxed_3477_ = lean_unbox_usize(v___x_3467_);
lean_dec(v___x_3467_);
v_res_3478_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0(v___x_12976__boxed_3477_, v_a_3468_, v_xs_3469_, v_a_3470_, v_recArgInfos_3471_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_);
lean_dec(v___y_3475_);
lean_dec_ref(v___y_3474_);
lean_dec(v___y_3473_);
lean_dec_ref(v___y_3472_);
return v_res_3478_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__11___redArg(lean_object* v___x_3479_, lean_object* v_xs_3480_, size_t v_sz_3481_, size_t v_i_3482_, lean_object* v_bs_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_){
_start:
{
uint8_t v___x_3489_; 
v___x_3489_ = lean_usize_dec_lt(v_i_3482_, v_sz_3481_);
if (v___x_3489_ == 0)
{
lean_object* v___x_3490_; 
lean_dec_ref(v_xs_3480_);
v___x_3490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3490_, 0, v_bs_3483_);
return v___x_3490_;
}
else
{
lean_object* v_v_3491_; lean_object* v_value_3492_; lean_object* v___x_3493_; lean_object* v_bs_x27_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; 
v_v_3491_ = lean_array_uget_borrowed(v_bs_3483_, v_i_3482_);
v_value_3492_ = lean_ctor_get(v_v_3491_, 7);
lean_inc_ref(v_value_3492_);
v___x_3493_ = lean_unsigned_to_nat(0u);
v_bs_x27_3494_ = lean_array_uset(v_bs_3483_, v_i_3482_, v___x_3493_);
v___x_3495_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0);
v___x_3496_ = lean_usize_to_nat(v_i_3482_);
v___x_3497_ = lean_array_get_borrowed(v___x_3495_, v___x_3479_, v___x_3496_);
lean_dec(v___x_3496_);
lean_inc_ref(v_xs_3480_);
lean_inc(v___x_3497_);
v___x_3498_ = l_Lean_Elab_FixedParamPerm_instantiateLambda(v___x_3497_, v_value_3492_, v_xs_3480_, v___y_3484_, v___y_3485_, v___y_3486_, v___y_3487_);
if (lean_obj_tag(v___x_3498_) == 0)
{
lean_object* v_a_3499_; size_t v___x_3500_; size_t v___x_3501_; lean_object* v___x_3502_; 
v_a_3499_ = lean_ctor_get(v___x_3498_, 0);
lean_inc(v_a_3499_);
lean_dec_ref_known(v___x_3498_, 1);
v___x_3500_ = ((size_t)1ULL);
v___x_3501_ = lean_usize_add(v_i_3482_, v___x_3500_);
v___x_3502_ = lean_array_uset(v_bs_x27_3494_, v_i_3482_, v_a_3499_);
v_i_3482_ = v___x_3501_;
v_bs_3483_ = v___x_3502_;
goto _start;
}
else
{
lean_object* v_a_3504_; lean_object* v___x_3506_; uint8_t v_isShared_3507_; uint8_t v_isSharedCheck_3511_; 
lean_dec_ref(v_bs_x27_3494_);
lean_dec_ref(v_xs_3480_);
v_a_3504_ = lean_ctor_get(v___x_3498_, 0);
v_isSharedCheck_3511_ = !lean_is_exclusive(v___x_3498_);
if (v_isSharedCheck_3511_ == 0)
{
v___x_3506_ = v___x_3498_;
v_isShared_3507_ = v_isSharedCheck_3511_;
goto v_resetjp_3505_;
}
else
{
lean_inc(v_a_3504_);
lean_dec(v___x_3498_);
v___x_3506_ = lean_box(0);
v_isShared_3507_ = v_isSharedCheck_3511_;
goto v_resetjp_3505_;
}
v_resetjp_3505_:
{
lean_object* v___x_3509_; 
if (v_isShared_3507_ == 0)
{
v___x_3509_ = v___x_3506_;
goto v_reusejp_3508_;
}
else
{
lean_object* v_reuseFailAlloc_3510_; 
v_reuseFailAlloc_3510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3510_, 0, v_a_3504_);
v___x_3509_ = v_reuseFailAlloc_3510_;
goto v_reusejp_3508_;
}
v_reusejp_3508_:
{
return v___x_3509_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__11___redArg___boxed(lean_object* v___x_3512_, lean_object* v_xs_3513_, lean_object* v_sz_3514_, lean_object* v_i_3515_, lean_object* v_bs_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_){
_start:
{
size_t v_sz_boxed_3522_; size_t v_i_boxed_3523_; lean_object* v_res_3524_; 
v_sz_boxed_3522_ = lean_unbox_usize(v_sz_3514_);
lean_dec(v_sz_3514_);
v_i_boxed_3523_ = lean_unbox_usize(v_i_3515_);
lean_dec(v_i_3515_);
v_res_3524_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__11___redArg(v___x_3512_, v_xs_3513_, v_sz_boxed_3522_, v_i_boxed_3523_, v_bs_3516_, v___y_3517_, v___y_3518_, v___y_3519_, v___y_3520_);
lean_dec(v___y_3520_);
lean_dec_ref(v___y_3519_);
lean_dec(v___y_3518_);
lean_dec_ref(v___y_3517_);
lean_dec_ref(v___x_3512_);
return v_res_3524_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__2(size_t v___x_3525_, lean_object* v_a_3526_, lean_object* v_a_3527_, lean_object* v_perms_3528_, lean_object* v_fnNames_3529_, lean_object* v_termMeasure_x3fs_3530_, lean_object* v_xs_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_){
_start:
{
lean_object* v___x_3537_; lean_object* v___f_3538_; size_t v_sz_3539_; lean_object* v___x_3540_; 
v___x_3537_ = lean_box_usize(v___x_3525_);
lean_inc_ref_n(v_a_3527_, 2);
lean_inc_ref_n(v_xs_3531_, 2);
lean_inc_ref(v_a_3526_);
v___f_3538_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___boxed), 10, 4);
lean_closure_set(v___f_3538_, 0, v___x_3537_);
lean_closure_set(v___f_3538_, 1, v_a_3526_);
lean_closure_set(v___f_3538_, 2, v_xs_3531_);
lean_closure_set(v___f_3538_, 3, v_a_3527_);
v_sz_3539_ = lean_array_size(v_a_3527_);
v___x_3540_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__11___redArg(v_perms_3528_, v_xs_3531_, v_sz_3539_, v___x_3525_, v_a_3527_, v___y_3532_, v___y_3533_, v___y_3534_, v___y_3535_);
if (lean_obj_tag(v___x_3540_) == 0)
{
lean_object* v_a_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; 
v_a_3541_ = lean_ctor_get(v___x_3540_, 0);
lean_inc_n(v_a_3541_, 2);
lean_dec_ref_known(v___x_3540_, 1);
lean_inc_ref(v_xs_3531_);
lean_inc_ref(v_fnNames_3529_);
v___x_3542_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_findRecArgCandidates___boxed), 10, 5);
lean_closure_set(v___x_3542_, 0, v_fnNames_3529_);
lean_closure_set(v___x_3542_, 1, v_a_3526_);
lean_closure_set(v___x_3542_, 2, v_xs_3531_);
lean_closure_set(v___x_3542_, 3, v_a_3541_);
lean_closure_set(v___x_3542_, 4, v_termMeasure_x3fs_3530_);
v___x_3543_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v_a_3527_, v___x_3542_, v___y_3532_, v___y_3533_, v___y_3534_, v___y_3535_);
if (lean_obj_tag(v___x_3543_) == 0)
{
lean_object* v_a_3544_; lean_object* v___x_3545_; 
v_a_3544_ = lean_ctor_get(v___x_3543_, 0);
lean_inc(v_a_3544_);
lean_dec_ref_known(v___x_3543_, 1);
v___x_3545_ = l_Lean_Elab_Structural_tryCandidates___redArg(v_fnNames_3529_, v_xs_3531_, v_a_3541_, v_a_3544_, v___f_3538_, v___y_3532_, v___y_3533_, v___y_3534_, v___y_3535_);
lean_dec_ref(v_fnNames_3529_);
return v___x_3545_;
}
else
{
lean_object* v_a_3546_; lean_object* v___x_3548_; uint8_t v_isShared_3549_; uint8_t v_isSharedCheck_3553_; 
lean_dec(v_a_3541_);
lean_dec_ref(v___f_3538_);
lean_dec_ref(v_xs_3531_);
lean_dec_ref(v_fnNames_3529_);
v_a_3546_ = lean_ctor_get(v___x_3543_, 0);
v_isSharedCheck_3553_ = !lean_is_exclusive(v___x_3543_);
if (v_isSharedCheck_3553_ == 0)
{
v___x_3548_ = v___x_3543_;
v_isShared_3549_ = v_isSharedCheck_3553_;
goto v_resetjp_3547_;
}
else
{
lean_inc(v_a_3546_);
lean_dec(v___x_3543_);
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
else
{
lean_object* v_a_3554_; lean_object* v___x_3556_; uint8_t v_isShared_3557_; uint8_t v_isSharedCheck_3561_; 
lean_dec_ref(v___f_3538_);
lean_dec_ref(v_xs_3531_);
lean_dec_ref(v_termMeasure_x3fs_3530_);
lean_dec_ref(v_fnNames_3529_);
lean_dec_ref(v_a_3527_);
lean_dec_ref(v_a_3526_);
v_a_3554_ = lean_ctor_get(v___x_3540_, 0);
v_isSharedCheck_3561_ = !lean_is_exclusive(v___x_3540_);
if (v_isSharedCheck_3561_ == 0)
{
v___x_3556_ = v___x_3540_;
v_isShared_3557_ = v_isSharedCheck_3561_;
goto v_resetjp_3555_;
}
else
{
lean_inc(v_a_3554_);
lean_dec(v___x_3540_);
v___x_3556_ = lean_box(0);
v_isShared_3557_ = v_isSharedCheck_3561_;
goto v_resetjp_3555_;
}
v_resetjp_3555_:
{
lean_object* v___x_3559_; 
if (v_isShared_3557_ == 0)
{
v___x_3559_ = v___x_3556_;
goto v_reusejp_3558_;
}
else
{
lean_object* v_reuseFailAlloc_3560_; 
v_reuseFailAlloc_3560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3560_, 0, v_a_3554_);
v___x_3559_ = v_reuseFailAlloc_3560_;
goto v_reusejp_3558_;
}
v_reusejp_3558_:
{
return v___x_3559_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__2___boxed(lean_object* v___x_3562_, lean_object* v_a_3563_, lean_object* v_a_3564_, lean_object* v_perms_3565_, lean_object* v_fnNames_3566_, lean_object* v_termMeasure_x3fs_3567_, lean_object* v_xs_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_){
_start:
{
size_t v___x_13319__boxed_3574_; lean_object* v_res_3575_; 
v___x_13319__boxed_3574_ = lean_unbox_usize(v___x_3562_);
lean_dec(v___x_3562_);
v_res_3575_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__2(v___x_13319__boxed_3574_, v_a_3563_, v_a_3564_, v_perms_3565_, v_fnNames_3566_, v_termMeasure_x3fs_3567_, v_xs_3568_, v___y_3569_, v___y_3570_, v___y_3571_, v___y_3572_);
lean_dec(v___y_3572_);
lean_dec_ref(v___y_3571_);
lean_dec(v___y_3570_);
lean_dec_ref(v___y_3569_);
lean_dec_ref(v_perms_3565_);
return v_res_3575_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0___redArg(lean_object* v_fnNames_3576_, lean_object* v_numSectionVars_3577_, size_t v_sz_3578_, size_t v_i_3579_, lean_object* v_bs_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_){
_start:
{
uint8_t v___x_3584_; 
v___x_3584_ = lean_usize_dec_lt(v_i_3579_, v_sz_3578_);
if (v___x_3584_ == 0)
{
lean_object* v___x_3585_; 
lean_dec(v_numSectionVars_3577_);
lean_dec_ref(v_fnNames_3576_);
v___x_3585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3585_, 0, v_bs_3580_);
return v___x_3585_;
}
else
{
lean_object* v_v_3586_; lean_object* v_ref_3587_; uint8_t v_kind_3588_; lean_object* v_levelParams_3589_; lean_object* v_modifiers_3590_; lean_object* v_declName_3591_; lean_object* v_binders_3592_; lean_object* v_numSectionVars_3593_; lean_object* v_type_3594_; lean_object* v_value_3595_; lean_object* v_termination_3596_; lean_object* v___x_3598_; uint8_t v_isShared_3599_; uint8_t v_isSharedCheck_3619_; 
v_v_3586_ = lean_array_uget(v_bs_3580_, v_i_3579_);
v_ref_3587_ = lean_ctor_get(v_v_3586_, 0);
v_kind_3588_ = lean_ctor_get_uint8(v_v_3586_, sizeof(void*)*9);
v_levelParams_3589_ = lean_ctor_get(v_v_3586_, 1);
v_modifiers_3590_ = lean_ctor_get(v_v_3586_, 2);
v_declName_3591_ = lean_ctor_get(v_v_3586_, 3);
v_binders_3592_ = lean_ctor_get(v_v_3586_, 4);
v_numSectionVars_3593_ = lean_ctor_get(v_v_3586_, 5);
v_type_3594_ = lean_ctor_get(v_v_3586_, 6);
v_value_3595_ = lean_ctor_get(v_v_3586_, 7);
v_termination_3596_ = lean_ctor_get(v_v_3586_, 8);
v_isSharedCheck_3619_ = !lean_is_exclusive(v_v_3586_);
if (v_isSharedCheck_3619_ == 0)
{
v___x_3598_ = v_v_3586_;
v_isShared_3599_ = v_isSharedCheck_3619_;
goto v_resetjp_3597_;
}
else
{
lean_inc(v_termination_3596_);
lean_inc(v_value_3595_);
lean_inc(v_type_3594_);
lean_inc(v_numSectionVars_3593_);
lean_inc(v_binders_3592_);
lean_inc(v_declName_3591_);
lean_inc(v_modifiers_3590_);
lean_inc(v_levelParams_3589_);
lean_inc(v_ref_3587_);
lean_dec(v_v_3586_);
v___x_3598_ = lean_box(0);
v_isShared_3599_ = v_isSharedCheck_3619_;
goto v_resetjp_3597_;
}
v_resetjp_3597_:
{
lean_object* v___x_3600_; lean_object* v_bs_x27_3601_; lean_object* v___x_3602_; 
v___x_3600_ = lean_unsigned_to_nat(0u);
v_bs_x27_3601_ = lean_array_uset(v_bs_3580_, v_i_3579_, v___x_3600_);
lean_inc(v_numSectionVars_3577_);
lean_inc_ref(v_fnNames_3576_);
v___x_3602_ = l_Lean_Elab_Structural_preprocess(v_value_3595_, v_fnNames_3576_, v_numSectionVars_3577_, v___y_3581_, v___y_3582_);
if (lean_obj_tag(v___x_3602_) == 0)
{
lean_object* v_a_3603_; lean_object* v___x_3605_; 
v_a_3603_ = lean_ctor_get(v___x_3602_, 0);
lean_inc(v_a_3603_);
lean_dec_ref_known(v___x_3602_, 1);
if (v_isShared_3599_ == 0)
{
lean_ctor_set(v___x_3598_, 7, v_a_3603_);
v___x_3605_ = v___x_3598_;
goto v_reusejp_3604_;
}
else
{
lean_object* v_reuseFailAlloc_3610_; 
v_reuseFailAlloc_3610_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_3610_, 0, v_ref_3587_);
lean_ctor_set(v_reuseFailAlloc_3610_, 1, v_levelParams_3589_);
lean_ctor_set(v_reuseFailAlloc_3610_, 2, v_modifiers_3590_);
lean_ctor_set(v_reuseFailAlloc_3610_, 3, v_declName_3591_);
lean_ctor_set(v_reuseFailAlloc_3610_, 4, v_binders_3592_);
lean_ctor_set(v_reuseFailAlloc_3610_, 5, v_numSectionVars_3593_);
lean_ctor_set(v_reuseFailAlloc_3610_, 6, v_type_3594_);
lean_ctor_set(v_reuseFailAlloc_3610_, 7, v_a_3603_);
lean_ctor_set(v_reuseFailAlloc_3610_, 8, v_termination_3596_);
lean_ctor_set_uint8(v_reuseFailAlloc_3610_, sizeof(void*)*9, v_kind_3588_);
v___x_3605_ = v_reuseFailAlloc_3610_;
goto v_reusejp_3604_;
}
v_reusejp_3604_:
{
size_t v___x_3606_; size_t v___x_3607_; lean_object* v___x_3608_; 
v___x_3606_ = ((size_t)1ULL);
v___x_3607_ = lean_usize_add(v_i_3579_, v___x_3606_);
v___x_3608_ = lean_array_uset(v_bs_x27_3601_, v_i_3579_, v___x_3605_);
v_i_3579_ = v___x_3607_;
v_bs_3580_ = v___x_3608_;
goto _start;
}
}
else
{
lean_object* v_a_3611_; lean_object* v___x_3613_; uint8_t v_isShared_3614_; uint8_t v_isSharedCheck_3618_; 
lean_dec_ref(v_bs_x27_3601_);
lean_del_object(v___x_3598_);
lean_dec_ref(v_termination_3596_);
lean_dec_ref(v_type_3594_);
lean_dec(v_numSectionVars_3593_);
lean_dec(v_binders_3592_);
lean_dec(v_declName_3591_);
lean_dec_ref(v_modifiers_3590_);
lean_dec(v_levelParams_3589_);
lean_dec(v_ref_3587_);
lean_dec(v_numSectionVars_3577_);
lean_dec_ref(v_fnNames_3576_);
v_a_3611_ = lean_ctor_get(v___x_3602_, 0);
v_isSharedCheck_3618_ = !lean_is_exclusive(v___x_3602_);
if (v_isSharedCheck_3618_ == 0)
{
v___x_3613_ = v___x_3602_;
v_isShared_3614_ = v_isSharedCheck_3618_;
goto v_resetjp_3612_;
}
else
{
lean_inc(v_a_3611_);
lean_dec(v___x_3602_);
v___x_3613_ = lean_box(0);
v_isShared_3614_ = v_isSharedCheck_3618_;
goto v_resetjp_3612_;
}
v_resetjp_3612_:
{
lean_object* v___x_3616_; 
if (v_isShared_3614_ == 0)
{
v___x_3616_ = v___x_3613_;
goto v_reusejp_3615_;
}
else
{
lean_object* v_reuseFailAlloc_3617_; 
v_reuseFailAlloc_3617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3617_, 0, v_a_3611_);
v___x_3616_ = v_reuseFailAlloc_3617_;
goto v_reusejp_3615_;
}
v_reusejp_3615_:
{
return v___x_3616_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0___redArg___boxed(lean_object* v_fnNames_3620_, lean_object* v_numSectionVars_3621_, lean_object* v_sz_3622_, lean_object* v_i_3623_, lean_object* v_bs_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_){
_start:
{
size_t v_sz_boxed_3628_; size_t v_i_boxed_3629_; lean_object* v_res_3630_; 
v_sz_boxed_3628_ = lean_unbox_usize(v_sz_3622_);
lean_dec(v_sz_3622_);
v_i_boxed_3629_ = lean_unbox_usize(v_i_3623_);
lean_dec(v_i_3623_);
v_res_3630_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0___redArg(v_fnNames_3620_, v_numSectionVars_3621_, v_sz_boxed_3628_, v_i_boxed_3629_, v_bs_3624_, v___y_3625_, v___y_3626_);
lean_dec(v___y_3626_);
lean_dec_ref(v___y_3625_);
return v_res_3630_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0(lean_object* v_fnNames_3631_, lean_object* v_numSectionVars_3632_, size_t v_sz_3633_, size_t v_i_3634_, lean_object* v_bs_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_){
_start:
{
lean_object* v___x_3641_; 
v___x_3641_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0___redArg(v_fnNames_3631_, v_numSectionVars_3632_, v_sz_3633_, v_i_3634_, v_bs_3635_, v___y_3638_, v___y_3639_);
return v___x_3641_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0___boxed(lean_object* v_fnNames_3642_, lean_object* v_numSectionVars_3643_, lean_object* v_sz_3644_, lean_object* v_i_3645_, lean_object* v_bs_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_){
_start:
{
size_t v_sz_boxed_3652_; size_t v_i_boxed_3653_; lean_object* v_res_3654_; 
v_sz_boxed_3652_ = lean_unbox_usize(v_sz_3644_);
lean_dec(v_sz_3644_);
v_i_boxed_3653_ = lean_unbox_usize(v_i_3645_);
lean_dec(v_i_3645_);
v_res_3654_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0(v_fnNames_3642_, v_numSectionVars_3643_, v_sz_boxed_3652_, v_i_boxed_3653_, v_bs_3646_, v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_);
lean_dec(v___y_3650_);
lean_dec_ref(v___y_3649_);
lean_dec(v___y_3648_);
lean_dec_ref(v___y_3647_);
return v_res_3654_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos(lean_object* v_preDefs_3655_, lean_object* v_termMeasure_x3fs_3656_, lean_object* v_a_3657_, lean_object* v_a_3658_, lean_object* v_a_3659_, lean_object* v_a_3660_){
_start:
{
lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v_numSectionVars_3665_; size_t v_sz_3666_; lean_object* v___x_3667_; size_t v___x_3668_; lean_object* v_fnNames_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; 
v___x_3662_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_3663_ = lean_unsigned_to_nat(0u);
v___x_3664_ = lean_array_get_borrowed(v___x_3662_, v_preDefs_3655_, v___x_3663_);
v_numSectionVars_3665_ = lean_ctor_get(v___x_3664_, 5);
v_sz_3666_ = lean_array_size(v_preDefs_3655_);
v___x_3667_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0);
v___x_3668_ = ((size_t)0ULL);
lean_inc_ref_n(v_preDefs_3655_, 2);
v_fnNames_3669_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16(v_sz_3666_, v___x_3668_, v_preDefs_3655_);
v___x_3670_ = lean_box_usize(v_sz_3666_);
v___x_3671_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___boxed__const__1));
lean_inc(v_numSectionVars_3665_);
lean_inc_ref(v_fnNames_3669_);
v___x_3672_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0___boxed), 10, 5);
lean_closure_set(v___x_3672_, 0, v_fnNames_3669_);
lean_closure_set(v___x_3672_, 1, v_numSectionVars_3665_);
lean_closure_set(v___x_3672_, 2, v___x_3670_);
lean_closure_set(v___x_3672_, 3, v___x_3671_);
lean_closure_set(v___x_3672_, 4, v_preDefs_3655_);
v___x_3673_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v_preDefs_3655_, v___x_3672_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_);
if (lean_obj_tag(v___x_3673_) == 0)
{
lean_object* v_a_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; 
v_a_3674_ = lean_ctor_get(v___x_3673_, 0);
lean_inc_n(v_a_3674_, 3);
lean_dec_ref_known(v___x_3673_, 1);
v___x_3675_ = lean_alloc_closure((void*)(l_Lean_Elab_getFixedParamPerms___boxed), 6, 1);
lean_closure_set(v___x_3675_, 0, v_a_3674_);
v___x_3676_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v_a_3674_, v___x_3675_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_);
if (lean_obj_tag(v___x_3676_) == 0)
{
lean_object* v_a_3677_; lean_object* v_perms_3678_; lean_object* v___x_3679_; lean_object* v_type_3680_; lean_object* v___x_3681_; lean_object* v___f_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; 
v_a_3677_ = lean_ctor_get(v___x_3676_, 0);
lean_inc(v_a_3677_);
lean_dec_ref_known(v___x_3676_, 1);
v_perms_3678_ = lean_ctor_get(v_a_3677_, 1);
lean_inc_ref_n(v_perms_3678_, 2);
v___x_3679_ = lean_array_get_borrowed(v___x_3662_, v_a_3674_, v___x_3663_);
v_type_3680_ = lean_ctor_get(v___x_3679_, 6);
lean_inc_ref(v_type_3680_);
v___x_3681_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___boxed__const__1));
v___f_3682_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__2___boxed), 12, 6);
lean_closure_set(v___f_3682_, 0, v___x_3681_);
lean_closure_set(v___f_3682_, 1, v_a_3677_);
lean_closure_set(v___f_3682_, 2, v_a_3674_);
lean_closure_set(v___f_3682_, 3, v_perms_3678_);
lean_closure_set(v___f_3682_, 4, v_fnNames_3669_);
lean_closure_set(v___f_3682_, 5, v_termMeasure_x3fs_3656_);
v___x_3683_ = lean_array_get(v___x_3667_, v_perms_3678_, v___x_3663_);
lean_dec_ref(v_perms_3678_);
v___x_3684_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg(v___x_3683_, v_type_3680_, v___f_3682_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_);
return v___x_3684_;
}
else
{
lean_object* v_a_3685_; lean_object* v___x_3687_; uint8_t v_isShared_3688_; uint8_t v_isSharedCheck_3692_; 
lean_dec(v_a_3674_);
lean_dec_ref(v_fnNames_3669_);
lean_dec_ref(v_termMeasure_x3fs_3656_);
v_a_3685_ = lean_ctor_get(v___x_3676_, 0);
v_isSharedCheck_3692_ = !lean_is_exclusive(v___x_3676_);
if (v_isSharedCheck_3692_ == 0)
{
v___x_3687_ = v___x_3676_;
v_isShared_3688_ = v_isSharedCheck_3692_;
goto v_resetjp_3686_;
}
else
{
lean_inc(v_a_3685_);
lean_dec(v___x_3676_);
v___x_3687_ = lean_box(0);
v_isShared_3688_ = v_isSharedCheck_3692_;
goto v_resetjp_3686_;
}
v_resetjp_3686_:
{
lean_object* v___x_3690_; 
if (v_isShared_3688_ == 0)
{
v___x_3690_ = v___x_3687_;
goto v_reusejp_3689_;
}
else
{
lean_object* v_reuseFailAlloc_3691_; 
v_reuseFailAlloc_3691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3691_, 0, v_a_3685_);
v___x_3690_ = v_reuseFailAlloc_3691_;
goto v_reusejp_3689_;
}
v_reusejp_3689_:
{
return v___x_3690_;
}
}
}
}
else
{
lean_object* v_a_3693_; lean_object* v___x_3695_; uint8_t v_isShared_3696_; uint8_t v_isSharedCheck_3700_; 
lean_dec_ref(v_fnNames_3669_);
lean_dec_ref(v_termMeasure_x3fs_3656_);
v_a_3693_ = lean_ctor_get(v___x_3673_, 0);
v_isSharedCheck_3700_ = !lean_is_exclusive(v___x_3673_);
if (v_isSharedCheck_3700_ == 0)
{
v___x_3695_ = v___x_3673_;
v_isShared_3696_ = v_isSharedCheck_3700_;
goto v_resetjp_3694_;
}
else
{
lean_inc(v_a_3693_);
lean_dec(v___x_3673_);
v___x_3695_ = lean_box(0);
v_isShared_3696_ = v_isSharedCheck_3700_;
goto v_resetjp_3694_;
}
v_resetjp_3694_:
{
lean_object* v___x_3698_; 
if (v_isShared_3696_ == 0)
{
v___x_3698_ = v___x_3695_;
goto v_reusejp_3697_;
}
else
{
lean_object* v_reuseFailAlloc_3699_; 
v_reuseFailAlloc_3699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3699_, 0, v_a_3693_);
v___x_3698_ = v_reuseFailAlloc_3699_;
goto v_reusejp_3697_;
}
v_reusejp_3697_:
{
return v___x_3698_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___boxed(lean_object* v_preDefs_3701_, lean_object* v_termMeasure_x3fs_3702_, lean_object* v_a_3703_, lean_object* v_a_3704_, lean_object* v_a_3705_, lean_object* v_a_3706_, lean_object* v_a_3707_){
_start:
{
lean_object* v_res_3708_; 
v_res_3708_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos(v_preDefs_3701_, v_termMeasure_x3fs_3702_, v_a_3703_, v_a_3704_, v_a_3705_, v_a_3706_);
lean_dec(v_a_3706_);
lean_dec_ref(v_a_3705_);
lean_dec(v_a_3704_);
lean_dec_ref(v_a_3703_);
return v_res_3708_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__3(lean_object* v_fst_3709_, lean_object* v_as_3710_, size_t v_sz_3711_, size_t v_i_3712_, lean_object* v_bs_3713_){
_start:
{
lean_object* v___x_3714_; 
v___x_3714_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__3___redArg(v_fst_3709_, v_sz_3711_, v_i_3712_, v_bs_3713_);
return v___x_3714_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__3___boxed(lean_object* v_fst_3715_, lean_object* v_as_3716_, lean_object* v_sz_3717_, lean_object* v_i_3718_, lean_object* v_bs_3719_){
_start:
{
size_t v_sz_boxed_3720_; size_t v_i_boxed_3721_; lean_object* v_res_3722_; 
v_sz_boxed_3720_ = lean_unbox_usize(v_sz_3717_);
lean_dec(v_sz_3717_);
v_i_boxed_3721_ = lean_unbox_usize(v_i_3718_);
lean_dec(v_i_3718_);
v_res_3722_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__3(v_fst_3715_, v_as_3716_, v_sz_boxed_3720_, v_i_boxed_3721_, v_bs_3719_);
lean_dec_ref(v_as_3716_);
lean_dec_ref(v_fst_3715_);
return v_res_3722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__9(lean_object* v_00_u03b1_3723_, lean_object* v_lctx_3724_, lean_object* v_localInsts_3725_, lean_object* v_x_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_, lean_object* v___y_3730_){
_start:
{
lean_object* v___x_3732_; 
v___x_3732_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__9___redArg(v_lctx_3724_, v_localInsts_3725_, v_x_3726_, v___y_3727_, v___y_3728_, v___y_3729_, v___y_3730_);
return v___x_3732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__9___boxed(lean_object* v_00_u03b1_3733_, lean_object* v_lctx_3734_, lean_object* v_localInsts_3735_, lean_object* v_x_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_){
_start:
{
lean_object* v_res_3742_; 
v_res_3742_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__9(v_00_u03b1_3733_, v_lctx_3734_, v_localInsts_3735_, v_x_3736_, v___y_3737_, v___y_3738_, v___y_3739_, v___y_3740_);
lean_dec(v___y_3740_);
lean_dec_ref(v___y_3739_);
lean_dec(v___y_3738_);
lean_dec_ref(v___y_3737_);
return v_res_3742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8(lean_object* v_00_u03b1_3743_, lean_object* v_fvarIds_3744_, lean_object* v_k_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_){
_start:
{
lean_object* v___x_3751_; 
v___x_3751_ = l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8___redArg(v_fvarIds_3744_, v_k_3745_, v___y_3746_, v___y_3747_, v___y_3748_, v___y_3749_);
return v___x_3751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8___boxed(lean_object* v_00_u03b1_3752_, lean_object* v_fvarIds_3753_, lean_object* v_k_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_){
_start:
{
lean_object* v_res_3760_; 
v_res_3760_ = l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8(v_00_u03b1_3752_, v_fvarIds_3753_, v_k_3754_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_);
lean_dec(v___y_3758_);
lean_dec_ref(v___y_3757_);
lean_dec(v___y_3756_);
lean_dec_ref(v___y_3755_);
lean_dec_ref(v_fvarIds_3753_);
return v_res_3760_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__14(lean_object* v_a_3761_){
_start:
{
lean_object* v___x_3762_; 
v___x_3762_ = lean_nat_to_int(v_a_3761_);
return v___x_3762_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__11(lean_object* v___x_3763_, lean_object* v_xs_3764_, lean_object* v_as_3765_, size_t v_sz_3766_, size_t v_i_3767_, lean_object* v_bs_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_){
_start:
{
lean_object* v___x_3774_; 
v___x_3774_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__11___redArg(v___x_3763_, v_xs_3764_, v_sz_3766_, v_i_3767_, v_bs_3768_, v___y_3769_, v___y_3770_, v___y_3771_, v___y_3772_);
return v___x_3774_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__11___boxed(lean_object* v___x_3775_, lean_object* v_xs_3776_, lean_object* v_as_3777_, lean_object* v_sz_3778_, lean_object* v_i_3779_, lean_object* v_bs_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_){
_start:
{
size_t v_sz_boxed_3786_; size_t v_i_boxed_3787_; lean_object* v_res_3788_; 
v_sz_boxed_3786_ = lean_unbox_usize(v_sz_3778_);
lean_dec(v_sz_3778_);
v_i_boxed_3787_ = lean_unbox_usize(v_i_3779_);
lean_dec(v_i_3779_);
v_res_3788_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__11(v___x_3775_, v_xs_3776_, v_as_3777_, v_sz_boxed_3786_, v_i_boxed_3787_, v_bs_3780_, v___y_3781_, v___y_3782_, v___y_3783_, v___y_3784_);
lean_dec(v___y_3784_);
lean_dec_ref(v___y_3783_);
lean_dec(v___y_3782_);
lean_dec_ref(v___y_3781_);
lean_dec_ref(v_as_3777_);
lean_dec_ref(v___x_3775_);
return v_res_3788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure___lam__0(lean_object* v_xs_3789_, lean_object* v_x_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_){
_start:
{
lean_object* v___x_3796_; lean_object* v___x_3797_; 
v___x_3796_ = lean_array_get_size(v_xs_3789_);
v___x_3797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3797_, 0, v___x_3796_);
return v___x_3797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure___lam__0___boxed(lean_object* v_xs_3798_, lean_object* v_x_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_){
_start:
{
lean_object* v_res_3805_; 
v_res_3805_ = l_Lean_Elab_Structural_reportTermMeasure___lam__0(v_xs_3798_, v_x_3799_, v___y_3800_, v___y_3801_, v___y_3802_, v___y_3803_);
lean_dec(v___y_3803_);
lean_dec_ref(v___y_3802_);
lean_dec(v___y_3801_);
lean_dec_ref(v___y_3800_);
lean_dec_ref(v_x_3799_);
lean_dec_ref(v_xs_3798_);
return v_res_3805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure___lam__1(lean_object* v___x_3806_, lean_object* v_recArgPos_3807_, lean_object* v_xs_3808_, lean_object* v_x_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_){
_start:
{
lean_object* v___x_3815_; uint8_t v___x_3816_; uint8_t v___x_3817_; uint8_t v___x_3818_; lean_object* v___x_3819_; 
v___x_3815_ = lean_array_get_borrowed(v___x_3806_, v_xs_3808_, v_recArgPos_3807_);
v___x_3816_ = 0;
v___x_3817_ = 1;
v___x_3818_ = 1;
lean_inc(v___x_3815_);
v___x_3819_ = l_Lean_Meta_mkLambdaFVars(v_xs_3808_, v___x_3815_, v___x_3816_, v___x_3817_, v___x_3816_, v___x_3817_, v___x_3818_, v___y_3810_, v___y_3811_, v___y_3812_, v___y_3813_);
return v___x_3819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure___lam__1___boxed(lean_object* v___x_3820_, lean_object* v_recArgPos_3821_, lean_object* v_xs_3822_, lean_object* v_x_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_){
_start:
{
lean_object* v_res_3829_; 
v_res_3829_ = l_Lean_Elab_Structural_reportTermMeasure___lam__1(v___x_3820_, v_recArgPos_3821_, v_xs_3822_, v_x_3823_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_);
lean_dec(v___y_3827_);
lean_dec_ref(v___y_3826_);
lean_dec(v___y_3825_);
lean_dec_ref(v___y_3824_);
lean_dec_ref(v_x_3823_);
lean_dec_ref(v_xs_3822_);
lean_dec(v_recArgPos_3821_);
lean_dec_ref(v___x_3820_);
return v_res_3829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure(lean_object* v_preDef_3841_, lean_object* v_recArgPos_3842_, lean_object* v_a_3843_, lean_object* v_a_3844_, lean_object* v_a_3845_, lean_object* v_a_3846_){
_start:
{
lean_object* v_termination_3848_; lean_object* v_terminationBy_x3f_x3f_3849_; 
v_termination_3848_ = lean_ctor_get(v_preDef_3841_, 8);
lean_inc_ref(v_termination_3848_);
v_terminationBy_x3f_x3f_3849_ = lean_ctor_get(v_termination_3848_, 1);
lean_inc(v_terminationBy_x3f_x3f_3849_);
if (lean_obj_tag(v_terminationBy_x3f_x3f_3849_) == 1)
{
lean_object* v_value_3850_; lean_object* v_extraParams_3851_; lean_object* v_val_3852_; lean_object* v___f_3853_; lean_object* v___x_3854_; lean_object* v___f_3855_; uint8_t v___x_3856_; lean_object* v___x_3857_; 
v_value_3850_ = lean_ctor_get(v_preDef_3841_, 7);
lean_inc_ref_n(v_value_3850_, 2);
lean_dec_ref(v_preDef_3841_);
v_extraParams_3851_ = lean_ctor_get(v_termination_3848_, 5);
lean_inc(v_extraParams_3851_);
lean_dec_ref(v_termination_3848_);
v_val_3852_ = lean_ctor_get(v_terminationBy_x3f_x3f_3849_, 0);
lean_inc(v_val_3852_);
lean_dec_ref_known(v_terminationBy_x3f_x3f_3849_, 1);
v___f_3853_ = ((lean_object*)(l_Lean_Elab_Structural_reportTermMeasure___closed__0));
v___x_3854_ = l_Lean_instInhabitedExpr;
v___f_3855_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_reportTermMeasure___lam__1___boxed), 9, 2);
lean_closure_set(v___f_3855_, 0, v___x_3854_);
lean_closure_set(v___f_3855_, 1, v_recArgPos_3842_);
v___x_3856_ = 0;
v___x_3857_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg(v_value_3850_, v___f_3855_, v___x_3856_, v_a_3843_, v_a_3844_, v_a_3845_, v_a_3846_);
if (lean_obj_tag(v___x_3857_) == 0)
{
lean_object* v_a_3858_; lean_object* v___x_3859_; uint8_t v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; 
v_a_3858_ = lean_ctor_get(v___x_3857_, 0);
lean_inc(v_a_3858_);
lean_dec_ref_known(v___x_3857_, 1);
v___x_3859_ = lean_box(0);
v___x_3860_ = 1;
v___x_3861_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3861_, 0, v___x_3859_);
lean_ctor_set(v___x_3861_, 1, v_a_3858_);
lean_ctor_set_uint8(v___x_3861_, sizeof(void*)*2, v___x_3860_);
v___x_3862_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg(v_value_3850_, v___f_3853_, v___x_3856_, v_a_3843_, v_a_3844_, v_a_3845_, v_a_3846_);
if (lean_obj_tag(v___x_3862_) == 0)
{
lean_object* v_a_3863_; lean_object* v___x_3864_; 
v_a_3863_ = lean_ctor_get(v___x_3862_, 0);
lean_inc(v_a_3863_);
lean_dec_ref_known(v___x_3862_, 1);
v___x_3864_ = l_Lean_Elab_TerminationMeasure_delab(v_a_3863_, v_extraParams_3851_, v___x_3861_, v_a_3843_, v_a_3844_, v_a_3845_, v_a_3846_);
lean_dec(v_a_3863_);
if (lean_obj_tag(v___x_3864_) == 0)
{
lean_object* v_a_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; uint8_t v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; 
v_a_3865_ = lean_ctor_get(v___x_3864_, 0);
lean_inc(v_a_3865_);
lean_dec_ref_known(v___x_3864_, 1);
v___x_3866_ = ((lean_object*)(l_Lean_Elab_Structural_reportTermMeasure___closed__5));
v___x_3867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3867_, 0, v___x_3866_);
lean_ctor_set(v___x_3867_, 1, v_a_3865_);
v___x_3868_ = lean_box(0);
v___x_3869_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3869_, 0, v___x_3867_);
lean_ctor_set(v___x_3869_, 1, v___x_3868_);
lean_ctor_set(v___x_3869_, 2, v___x_3868_);
lean_ctor_set(v___x_3869_, 3, v___x_3868_);
lean_ctor_set(v___x_3869_, 4, v___x_3868_);
lean_ctor_set(v___x_3869_, 5, v___x_3868_);
v___x_3870_ = ((lean_object*)(l_Lean_Elab_Structural_reportTermMeasure___closed__6));
v___x_3871_ = 4;
v___x_3872_ = l_Lean_MessageData_nil;
v___x_3873_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_val_3852_, v___x_3869_, v___x_3868_, v___x_3870_, v___x_3868_, v___x_3871_, v___x_3872_, v_a_3845_, v_a_3846_);
return v___x_3873_;
}
else
{
lean_object* v_a_3874_; lean_object* v___x_3876_; uint8_t v_isShared_3877_; uint8_t v_isSharedCheck_3881_; 
lean_dec(v_val_3852_);
v_a_3874_ = lean_ctor_get(v___x_3864_, 0);
v_isSharedCheck_3881_ = !lean_is_exclusive(v___x_3864_);
if (v_isSharedCheck_3881_ == 0)
{
v___x_3876_ = v___x_3864_;
v_isShared_3877_ = v_isSharedCheck_3881_;
goto v_resetjp_3875_;
}
else
{
lean_inc(v_a_3874_);
lean_dec(v___x_3864_);
v___x_3876_ = lean_box(0);
v_isShared_3877_ = v_isSharedCheck_3881_;
goto v_resetjp_3875_;
}
v_resetjp_3875_:
{
lean_object* v___x_3879_; 
if (v_isShared_3877_ == 0)
{
v___x_3879_ = v___x_3876_;
goto v_reusejp_3878_;
}
else
{
lean_object* v_reuseFailAlloc_3880_; 
v_reuseFailAlloc_3880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3880_, 0, v_a_3874_);
v___x_3879_ = v_reuseFailAlloc_3880_;
goto v_reusejp_3878_;
}
v_reusejp_3878_:
{
return v___x_3879_;
}
}
}
}
else
{
lean_object* v_a_3882_; lean_object* v___x_3884_; uint8_t v_isShared_3885_; uint8_t v_isSharedCheck_3889_; 
lean_dec_ref_known(v___x_3861_, 2);
lean_dec(v_val_3852_);
lean_dec(v_extraParams_3851_);
v_a_3882_ = lean_ctor_get(v___x_3862_, 0);
v_isSharedCheck_3889_ = !lean_is_exclusive(v___x_3862_);
if (v_isSharedCheck_3889_ == 0)
{
v___x_3884_ = v___x_3862_;
v_isShared_3885_ = v_isSharedCheck_3889_;
goto v_resetjp_3883_;
}
else
{
lean_inc(v_a_3882_);
lean_dec(v___x_3862_);
v___x_3884_ = lean_box(0);
v_isShared_3885_ = v_isSharedCheck_3889_;
goto v_resetjp_3883_;
}
v_resetjp_3883_:
{
lean_object* v___x_3887_; 
if (v_isShared_3885_ == 0)
{
v___x_3887_ = v___x_3884_;
goto v_reusejp_3886_;
}
else
{
lean_object* v_reuseFailAlloc_3888_; 
v_reuseFailAlloc_3888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3888_, 0, v_a_3882_);
v___x_3887_ = v_reuseFailAlloc_3888_;
goto v_reusejp_3886_;
}
v_reusejp_3886_:
{
return v___x_3887_;
}
}
}
}
else
{
lean_object* v_a_3890_; lean_object* v___x_3892_; uint8_t v_isShared_3893_; uint8_t v_isSharedCheck_3897_; 
lean_dec(v_val_3852_);
lean_dec(v_extraParams_3851_);
lean_dec_ref(v_value_3850_);
v_a_3890_ = lean_ctor_get(v___x_3857_, 0);
v_isSharedCheck_3897_ = !lean_is_exclusive(v___x_3857_);
if (v_isSharedCheck_3897_ == 0)
{
v___x_3892_ = v___x_3857_;
v_isShared_3893_ = v_isSharedCheck_3897_;
goto v_resetjp_3891_;
}
else
{
lean_inc(v_a_3890_);
lean_dec(v___x_3857_);
v___x_3892_ = lean_box(0);
v_isShared_3893_ = v_isSharedCheck_3897_;
goto v_resetjp_3891_;
}
v_resetjp_3891_:
{
lean_object* v___x_3895_; 
if (v_isShared_3893_ == 0)
{
v___x_3895_ = v___x_3892_;
goto v_reusejp_3894_;
}
else
{
lean_object* v_reuseFailAlloc_3896_; 
v_reuseFailAlloc_3896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3896_, 0, v_a_3890_);
v___x_3895_ = v_reuseFailAlloc_3896_;
goto v_reusejp_3894_;
}
v_reusejp_3894_:
{
return v___x_3895_;
}
}
}
}
else
{
lean_object* v___x_3898_; lean_object* v___x_3899_; 
lean_dec(v_terminationBy_x3f_x3f_3849_);
lean_dec_ref(v_termination_3848_);
lean_dec(v_recArgPos_3842_);
lean_dec_ref(v_preDef_3841_);
v___x_3898_ = lean_box(0);
v___x_3899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3899_, 0, v___x_3898_);
return v___x_3899_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure___boxed(lean_object* v_preDef_3900_, lean_object* v_recArgPos_3901_, lean_object* v_a_3902_, lean_object* v_a_3903_, lean_object* v_a_3904_, lean_object* v_a_3905_, lean_object* v_a_3906_){
_start:
{
lean_object* v_res_3907_; 
v_res_3907_ = l_Lean_Elab_Structural_reportTermMeasure(v_preDef_3900_, v_recArgPos_3901_, v_a_3902_, v_a_3903_, v_a_3904_, v_a_3905_);
lean_dec(v_a_3905_);
lean_dec_ref(v_a_3904_);
lean_dec(v_a_3903_);
lean_dec_ref(v_a_3902_);
return v_res_3907_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___redArg(lean_object* v_as_3908_, size_t v_sz_3909_, size_t v_i_3910_, lean_object* v_b_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_){
_start:
{
uint8_t v___x_3917_; 
v___x_3917_ = lean_usize_dec_lt(v_i_3910_, v_sz_3909_);
if (v___x_3917_ == 0)
{
lean_object* v___x_3918_; 
v___x_3918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3918_, 0, v_b_3911_);
return v___x_3918_;
}
else
{
lean_object* v_a_3919_; lean_object* v_declName_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; 
v_a_3919_ = lean_array_uget_borrowed(v_as_3908_, v_i_3910_);
v_declName_3920_ = lean_ctor_get(v_a_3919_, 3);
v___x_3921_ = lean_box(0);
lean_inc(v_declName_3920_);
v___x_3922_ = l_Lean_Meta_saveEqnAffectingOptions(v_declName_3920_, v___y_3912_, v___y_3913_, v___y_3914_, v___y_3915_);
if (lean_obj_tag(v___x_3922_) == 0)
{
size_t v___x_3923_; size_t v___x_3924_; 
lean_dec_ref_known(v___x_3922_, 1);
v___x_3923_ = ((size_t)1ULL);
v___x_3924_ = lean_usize_add(v_i_3910_, v___x_3923_);
v_i_3910_ = v___x_3924_;
v_b_3911_ = v___x_3921_;
goto _start;
}
else
{
return v___x_3922_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___redArg___boxed(lean_object* v_as_3926_, lean_object* v_sz_3927_, lean_object* v_i_3928_, lean_object* v_b_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_){
_start:
{
size_t v_sz_boxed_3935_; size_t v_i_boxed_3936_; lean_object* v_res_3937_; 
v_sz_boxed_3935_ = lean_unbox_usize(v_sz_3927_);
lean_dec(v_sz_3927_);
v_i_boxed_3936_ = lean_unbox_usize(v_i_3928_);
lean_dec(v_i_3928_);
v_res_3937_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___redArg(v_as_3926_, v_sz_boxed_3935_, v_i_boxed_3936_, v_b_3929_, v___y_3930_, v___y_3931_, v___y_3932_, v___y_3933_);
lean_dec(v___y_3933_);
lean_dec_ref(v___y_3932_);
lean_dec(v___y_3931_);
lean_dec_ref(v___y_3930_);
lean_dec_ref(v_as_3926_);
return v_res_3937_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__1(lean_object* v_a_3938_, lean_object* v_fst_3939_, lean_object* v_docCtx_3940_, lean_object* v_snd_3941_, lean_object* v_as_3942_, size_t v_sz_3943_, size_t v_i_3944_, lean_object* v_b_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_){
_start:
{
uint8_t v___x_3953_; 
v___x_3953_ = lean_usize_dec_lt(v_i_3944_, v_sz_3943_);
if (v___x_3953_ == 0)
{
lean_object* v___x_3954_; 
lean_dec_ref(v_snd_3941_);
lean_dec_ref(v_docCtx_3940_);
lean_dec_ref(v_a_3938_);
v___x_3954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3954_, 0, v_b_3945_);
return v___x_3954_;
}
else
{
lean_object* v_array_3955_; lean_object* v_start_3956_; lean_object* v_stop_3957_; uint8_t v___x_3958_; 
v_array_3955_ = lean_ctor_get(v_b_3945_, 0);
v_start_3956_ = lean_ctor_get(v_b_3945_, 1);
v_stop_3957_ = lean_ctor_get(v_b_3945_, 2);
v___x_3958_ = lean_nat_dec_lt(v_start_3956_, v_stop_3957_);
if (v___x_3958_ == 0)
{
lean_object* v___x_3959_; 
lean_dec_ref(v_snd_3941_);
lean_dec_ref(v_docCtx_3940_);
lean_dec_ref(v_a_3938_);
v___x_3959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3959_, 0, v_b_3945_);
return v___x_3959_;
}
else
{
lean_object* v___x_3961_; uint8_t v_isShared_3962_; uint8_t v_isSharedCheck_4030_; 
lean_inc(v_stop_3957_);
lean_inc(v_start_3956_);
lean_inc_ref(v_array_3955_);
v_isSharedCheck_4030_ = !lean_is_exclusive(v_b_3945_);
if (v_isSharedCheck_4030_ == 0)
{
lean_object* v_unused_4031_; lean_object* v_unused_4032_; lean_object* v_unused_4033_; 
v_unused_4031_ = lean_ctor_get(v_b_3945_, 2);
lean_dec(v_unused_4031_);
v_unused_4032_ = lean_ctor_get(v_b_3945_, 1);
lean_dec(v_unused_4032_);
v_unused_4033_ = lean_ctor_get(v_b_3945_, 0);
lean_dec(v_unused_4033_);
v___x_3961_ = v_b_3945_;
v_isShared_3962_ = v_isSharedCheck_4030_;
goto v_resetjp_3960_;
}
else
{
lean_dec(v_b_3945_);
v___x_3961_ = lean_box(0);
v_isShared_3962_ = v_isSharedCheck_4030_;
goto v_resetjp_3960_;
}
v_resetjp_3960_:
{
lean_object* v_a_3963_; uint8_t v_kind_3964_; lean_object* v_type_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3970_; 
v_a_3963_ = lean_array_uget_borrowed(v_as_3942_, v_i_3944_);
v_kind_3964_ = lean_ctor_get_uint8(v_a_3963_, sizeof(void*)*9);
v_type_3965_ = lean_ctor_get(v_a_3963_, 6);
v___x_3966_ = lean_array_fget(v_array_3955_, v_start_3956_);
v___x_3967_ = lean_unsigned_to_nat(1u);
v___x_3968_ = lean_nat_add(v_start_3956_, v___x_3967_);
lean_dec(v_start_3956_);
if (v_isShared_3962_ == 0)
{
lean_ctor_set(v___x_3961_, 1, v___x_3968_);
v___x_3970_ = v___x_3961_;
goto v_reusejp_3969_;
}
else
{
lean_object* v_reuseFailAlloc_4029_; 
v_reuseFailAlloc_4029_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4029_, 0, v_array_3955_);
lean_ctor_set(v_reuseFailAlloc_4029_, 1, v___x_3968_);
lean_ctor_set(v_reuseFailAlloc_4029_, 2, v_stop_3957_);
v___x_3970_ = v_reuseFailAlloc_4029_;
goto v_reusejp_3969_;
}
v_reusejp_3969_:
{
lean_object* v_preDef_3972_; lean_object* v___y_3973_; lean_object* v___y_3974_; lean_object* v___y_3975_; lean_object* v___y_3976_; lean_object* v___y_3977_; lean_object* v___y_3978_; uint8_t v___x_3995_; 
v___x_3995_ = l_Lean_Elab_DefKind_isTheorem(v_kind_3964_);
if (v___x_3995_ == 0)
{
lean_object* v___x_3996_; 
lean_inc_ref(v_type_3965_);
v___x_3996_ = l_Lean_Meta_isProp(v_type_3965_, v___y_3948_, v___y_3949_, v___y_3950_, v___y_3951_);
if (lean_obj_tag(v___x_3996_) == 0)
{
lean_object* v_a_3997_; uint8_t v___x_3998_; 
v_a_3997_ = lean_ctor_get(v___x_3996_, 0);
lean_inc(v_a_3997_);
lean_dec_ref_known(v___x_3996_, 1);
v___x_3998_ = lean_unbox(v_a_3997_);
lean_dec(v_a_3997_);
if (v___x_3998_ == 0)
{
lean_object* v___x_3999_; 
lean_inc(v_a_3963_);
v___x_3999_ = l_Lean_Elab_abstractNestedProofs(v_a_3963_, v___x_3958_, v___y_3948_, v___y_3949_, v___y_3950_, v___y_3951_);
if (lean_obj_tag(v___x_3999_) == 0)
{
lean_object* v_a_4000_; size_t v_sz_4001_; size_t v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; 
v_a_4000_ = lean_ctor_get(v___x_3999_, 0);
lean_inc_n(v_a_4000_, 2);
lean_dec_ref_known(v___x_3999_, 1);
v_sz_4001_ = lean_array_size(v_a_3938_);
v___x_4002_ = ((size_t)0ULL);
lean_inc_ref(v_a_3938_);
v___x_4003_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16(v_sz_4001_, v___x_4002_, v_a_3938_);
lean_inc_ref(v_snd_3941_);
v___x_4004_ = l_Lean_Elab_Structural_registerEqnsInfo(v_a_4000_, v___x_4003_, v___x_3966_, v_snd_3941_, v___y_3950_, v___y_3951_);
if (lean_obj_tag(v___x_4004_) == 0)
{
lean_dec_ref_known(v___x_4004_, 1);
v_preDef_3972_ = v_a_4000_;
v___y_3973_ = v___y_3946_;
v___y_3974_ = v___y_3947_;
v___y_3975_ = v___y_3948_;
v___y_3976_ = v___y_3949_;
v___y_3977_ = v___y_3950_;
v___y_3978_ = v___y_3951_;
goto v___jp_3971_;
}
else
{
lean_object* v_a_4005_; lean_object* v___x_4007_; uint8_t v_isShared_4008_; uint8_t v_isSharedCheck_4012_; 
lean_dec(v_a_4000_);
lean_dec_ref(v___x_3970_);
lean_dec_ref(v_snd_3941_);
lean_dec_ref(v_docCtx_3940_);
lean_dec_ref(v_a_3938_);
v_a_4005_ = lean_ctor_get(v___x_4004_, 0);
v_isSharedCheck_4012_ = !lean_is_exclusive(v___x_4004_);
if (v_isSharedCheck_4012_ == 0)
{
v___x_4007_ = v___x_4004_;
v_isShared_4008_ = v_isSharedCheck_4012_;
goto v_resetjp_4006_;
}
else
{
lean_inc(v_a_4005_);
lean_dec(v___x_4004_);
v___x_4007_ = lean_box(0);
v_isShared_4008_ = v_isSharedCheck_4012_;
goto v_resetjp_4006_;
}
v_resetjp_4006_:
{
lean_object* v___x_4010_; 
if (v_isShared_4008_ == 0)
{
v___x_4010_ = v___x_4007_;
goto v_reusejp_4009_;
}
else
{
lean_object* v_reuseFailAlloc_4011_; 
v_reuseFailAlloc_4011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4011_, 0, v_a_4005_);
v___x_4010_ = v_reuseFailAlloc_4011_;
goto v_reusejp_4009_;
}
v_reusejp_4009_:
{
return v___x_4010_;
}
}
}
}
else
{
lean_object* v_a_4013_; lean_object* v___x_4015_; uint8_t v_isShared_4016_; uint8_t v_isSharedCheck_4020_; 
lean_dec_ref(v___x_3970_);
lean_dec(v___x_3966_);
lean_dec_ref(v_snd_3941_);
lean_dec_ref(v_docCtx_3940_);
lean_dec_ref(v_a_3938_);
v_a_4013_ = lean_ctor_get(v___x_3999_, 0);
v_isSharedCheck_4020_ = !lean_is_exclusive(v___x_3999_);
if (v_isSharedCheck_4020_ == 0)
{
v___x_4015_ = v___x_3999_;
v_isShared_4016_ = v_isSharedCheck_4020_;
goto v_resetjp_4014_;
}
else
{
lean_inc(v_a_4013_);
lean_dec(v___x_3999_);
v___x_4015_ = lean_box(0);
v_isShared_4016_ = v_isSharedCheck_4020_;
goto v_resetjp_4014_;
}
v_resetjp_4014_:
{
lean_object* v___x_4018_; 
if (v_isShared_4016_ == 0)
{
v___x_4018_ = v___x_4015_;
goto v_reusejp_4017_;
}
else
{
lean_object* v_reuseFailAlloc_4019_; 
v_reuseFailAlloc_4019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4019_, 0, v_a_4013_);
v___x_4018_ = v_reuseFailAlloc_4019_;
goto v_reusejp_4017_;
}
v_reusejp_4017_:
{
return v___x_4018_;
}
}
}
}
else
{
lean_dec(v___x_3966_);
lean_inc(v_a_3963_);
v_preDef_3972_ = v_a_3963_;
v___y_3973_ = v___y_3946_;
v___y_3974_ = v___y_3947_;
v___y_3975_ = v___y_3948_;
v___y_3976_ = v___y_3949_;
v___y_3977_ = v___y_3950_;
v___y_3978_ = v___y_3951_;
goto v___jp_3971_;
}
}
else
{
lean_object* v_a_4021_; lean_object* v___x_4023_; uint8_t v_isShared_4024_; uint8_t v_isSharedCheck_4028_; 
lean_dec_ref(v___x_3970_);
lean_dec(v___x_3966_);
lean_dec_ref(v_snd_3941_);
lean_dec_ref(v_docCtx_3940_);
lean_dec_ref(v_a_3938_);
v_a_4021_ = lean_ctor_get(v___x_3996_, 0);
v_isSharedCheck_4028_ = !lean_is_exclusive(v___x_3996_);
if (v_isSharedCheck_4028_ == 0)
{
v___x_4023_ = v___x_3996_;
v_isShared_4024_ = v_isSharedCheck_4028_;
goto v_resetjp_4022_;
}
else
{
lean_inc(v_a_4021_);
lean_dec(v___x_3996_);
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
lean_dec(v___x_3966_);
lean_inc(v_a_3963_);
v_preDef_3972_ = v_a_3963_;
v___y_3973_ = v___y_3946_;
v___y_3974_ = v___y_3947_;
v___y_3975_ = v___y_3948_;
v___y_3976_ = v___y_3949_;
v___y_3977_ = v___y_3950_;
v___y_3978_ = v___y_3951_;
goto v___jp_3971_;
}
v___jp_3971_:
{
size_t v_sz_3979_; size_t v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; 
v_sz_3979_ = lean_array_size(v_a_3938_);
v___x_3980_ = ((size_t)0ULL);
lean_inc_ref(v_a_3938_);
v___x_3981_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16(v_sz_3979_, v___x_3980_, v_a_3938_);
v___x_3982_ = l_Array_zip___redArg(v___x_3981_, v_fst_3939_);
lean_dec_ref(v___x_3981_);
lean_inc_ref(v_docCtx_3940_);
v___x_3983_ = l_Lean_Elab_Structural_addSmartUnfoldingDef(v_docCtx_3940_, v_preDef_3972_, v___x_3982_, v___y_3973_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_, v___y_3978_);
if (lean_obj_tag(v___x_3983_) == 0)
{
size_t v___x_3984_; size_t v___x_3985_; 
lean_dec_ref_known(v___x_3983_, 1);
v___x_3984_ = ((size_t)1ULL);
v___x_3985_ = lean_usize_add(v_i_3944_, v___x_3984_);
v_i_3944_ = v___x_3985_;
v_b_3945_ = v___x_3970_;
goto _start;
}
else
{
lean_object* v_a_3987_; lean_object* v___x_3989_; uint8_t v_isShared_3990_; uint8_t v_isSharedCheck_3994_; 
lean_dec_ref(v___x_3970_);
lean_dec_ref(v_snd_3941_);
lean_dec_ref(v_docCtx_3940_);
lean_dec_ref(v_a_3938_);
v_a_3987_ = lean_ctor_get(v___x_3983_, 0);
v_isSharedCheck_3994_ = !lean_is_exclusive(v___x_3983_);
if (v_isSharedCheck_3994_ == 0)
{
v___x_3989_ = v___x_3983_;
v_isShared_3990_ = v_isSharedCheck_3994_;
goto v_resetjp_3988_;
}
else
{
lean_inc(v_a_3987_);
lean_dec(v___x_3983_);
v___x_3989_ = lean_box(0);
v_isShared_3990_ = v_isSharedCheck_3994_;
goto v_resetjp_3988_;
}
v_resetjp_3988_:
{
lean_object* v___x_3992_; 
if (v_isShared_3990_ == 0)
{
v___x_3992_ = v___x_3989_;
goto v_reusejp_3991_;
}
else
{
lean_object* v_reuseFailAlloc_3993_; 
v_reuseFailAlloc_3993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3993_, 0, v_a_3987_);
v___x_3992_ = v_reuseFailAlloc_3993_;
goto v_reusejp_3991_;
}
v_reusejp_3991_:
{
return v___x_3992_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__1___boxed(lean_object* v_a_4034_, lean_object* v_fst_4035_, lean_object* v_docCtx_4036_, lean_object* v_snd_4037_, lean_object* v_as_4038_, lean_object* v_sz_4039_, lean_object* v_i_4040_, lean_object* v_b_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_){
_start:
{
size_t v_sz_boxed_4049_; size_t v_i_boxed_4050_; lean_object* v_res_4051_; 
v_sz_boxed_4049_ = lean_unbox_usize(v_sz_4039_);
lean_dec(v_sz_4039_);
v_i_boxed_4050_ = lean_unbox_usize(v_i_4040_);
lean_dec(v_i_4040_);
v_res_4051_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__1(v_a_4034_, v_fst_4035_, v_docCtx_4036_, v_snd_4037_, v_as_4038_, v_sz_boxed_4049_, v_i_boxed_4050_, v_b_4041_, v___y_4042_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_);
lean_dec(v___y_4047_);
lean_dec_ref(v___y_4046_);
lean_dec(v___y_4045_);
lean_dec_ref(v___y_4044_);
lean_dec(v___y_4043_);
lean_dec_ref(v___y_4042_);
lean_dec_ref(v_as_4038_);
lean_dec_ref(v_fst_4035_);
return v_res_4051_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___lam__0(lean_object* v___x_4052_, lean_object* v_e_4053_){
_start:
{
lean_object* v___x_4054_; lean_object* v___x_4055_; 
v___x_4054_ = l_Lean_indentD(v_e_4053_);
v___x_4055_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4055_, 0, v___x_4052_);
lean_ctor_set(v___x_4055_, 1, v___x_4054_);
return v___x_4055_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___lam__1(lean_object* v_docCtx_4056_, lean_object* v_a_4057_, uint8_t v___x_4058_, lean_object* v___x_4059_, uint8_t v___x_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_){
_start:
{
lean_object* v___x_4068_; 
v___x_4068_ = l_Lean_Elab_addNonRec(v_docCtx_4056_, v_a_4057_, v___x_4058_, v___x_4059_, v___x_4060_, v___x_4058_, v___x_4060_, v___x_4060_, v___y_4061_, v___y_4062_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_);
return v___x_4068_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___lam__1___boxed(lean_object* v_docCtx_4069_, lean_object* v_a_4070_, lean_object* v___x_4071_, lean_object* v___x_4072_, lean_object* v___x_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_){
_start:
{
uint8_t v___x_9352__boxed_4081_; uint8_t v___x_9354__boxed_4082_; lean_object* v_res_4083_; 
v___x_9352__boxed_4081_ = lean_unbox(v___x_4071_);
v___x_9354__boxed_4082_ = lean_unbox(v___x_4073_);
v_res_4083_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___lam__1(v_docCtx_4069_, v_a_4070_, v___x_9352__boxed_4081_, v___x_4072_, v___x_9354__boxed_4082_, v___y_4074_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_, v___y_4079_);
lean_dec(v___y_4079_);
lean_dec_ref(v___y_4078_);
lean_dec(v___y_4077_);
lean_dec_ref(v___y_4076_);
lean_dec(v___y_4075_);
lean_dec_ref(v___y_4074_);
return v_res_4083_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__1(void){
_start:
{
lean_object* v___x_4085_; lean_object* v___x_4086_; 
v___x_4085_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__0));
v___x_4086_ = l_Lean_stringToMessageData(v___x_4085_);
return v___x_4086_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__2(void){
_start:
{
lean_object* v___x_4087_; lean_object* v___f_4088_; 
v___x_4087_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__1);
v___f_4088_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___lam__0), 2, 1);
lean_closure_set(v___f_4088_, 0, v___x_4087_);
return v___f_4088_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5(lean_object* v_names_4089_, lean_object* v_docCtx_4090_, lean_object* v_as_4091_, size_t v_i_4092_, size_t v_stop_4093_, lean_object* v_b_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_){
_start:
{
uint8_t v___x_4102_; 
v___x_4102_ = lean_usize_dec_eq(v_i_4092_, v_stop_4093_);
if (v___x_4102_ == 0)
{
lean_object* v___x_4103_; lean_object* v___x_4104_; 
v___x_4103_ = lean_array_uget_borrowed(v_as_4091_, v_i_4092_);
lean_inc(v___x_4103_);
v___x_4104_ = l_Lean_Elab_eraseRecAppSyntax(v___x_4103_, v___y_4099_, v___y_4100_);
if (lean_obj_tag(v___x_4104_) == 0)
{
lean_object* v_a_4105_; lean_object* v___f_4106_; lean_object* v___x_4107_; uint8_t v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___f_4111_; lean_object* v___x_4112_; 
v_a_4105_ = lean_ctor_get(v___x_4104_, 0);
lean_inc(v_a_4105_);
lean_dec_ref_known(v___x_4104_, 1);
v___f_4106_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__2);
lean_inc_ref(v_names_4089_);
v___x_4107_ = lean_array_to_list(v_names_4089_);
v___x_4108_ = 1;
v___x_4109_ = lean_box(v___x_4102_);
v___x_4110_ = lean_box(v___x_4108_);
lean_inc(v___y_4096_);
lean_inc_ref(v___y_4095_);
lean_inc_ref(v_docCtx_4090_);
v___f_4111_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___lam__1___boxed), 12, 7);
lean_closure_set(v___f_4111_, 0, v_docCtx_4090_);
lean_closure_set(v___f_4111_, 1, v_a_4105_);
lean_closure_set(v___f_4111_, 2, v___x_4109_);
lean_closure_set(v___f_4111_, 3, v___x_4107_);
lean_closure_set(v___f_4111_, 4, v___x_4110_);
lean_closure_set(v___f_4111_, 5, v___y_4095_);
lean_closure_set(v___f_4111_, 6, v___y_4096_);
v___x_4112_ = l_Lean_Meta_mapErrorImp___redArg(v___f_4111_, v___f_4106_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_);
if (lean_obj_tag(v___x_4112_) == 0)
{
lean_object* v_a_4113_; size_t v___x_4114_; size_t v___x_4115_; 
v_a_4113_ = lean_ctor_get(v___x_4112_, 0);
lean_inc(v_a_4113_);
lean_dec_ref_known(v___x_4112_, 1);
v___x_4114_ = ((size_t)1ULL);
v___x_4115_ = lean_usize_add(v_i_4092_, v___x_4114_);
v_i_4092_ = v___x_4115_;
v_b_4094_ = v_a_4113_;
goto _start;
}
else
{
lean_object* v_a_4117_; lean_object* v___x_4119_; uint8_t v_isShared_4120_; uint8_t v_isSharedCheck_4124_; 
lean_dec_ref(v_docCtx_4090_);
lean_dec_ref(v_names_4089_);
v_a_4117_ = lean_ctor_get(v___x_4112_, 0);
v_isSharedCheck_4124_ = !lean_is_exclusive(v___x_4112_);
if (v_isSharedCheck_4124_ == 0)
{
v___x_4119_ = v___x_4112_;
v_isShared_4120_ = v_isSharedCheck_4124_;
goto v_resetjp_4118_;
}
else
{
lean_inc(v_a_4117_);
lean_dec(v___x_4112_);
v___x_4119_ = lean_box(0);
v_isShared_4120_ = v_isSharedCheck_4124_;
goto v_resetjp_4118_;
}
v_resetjp_4118_:
{
lean_object* v___x_4122_; 
if (v_isShared_4120_ == 0)
{
v___x_4122_ = v___x_4119_;
goto v_reusejp_4121_;
}
else
{
lean_object* v_reuseFailAlloc_4123_; 
v_reuseFailAlloc_4123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4123_, 0, v_a_4117_);
v___x_4122_ = v_reuseFailAlloc_4123_;
goto v_reusejp_4121_;
}
v_reusejp_4121_:
{
return v___x_4122_;
}
}
}
}
else
{
lean_object* v_a_4125_; lean_object* v___x_4127_; uint8_t v_isShared_4128_; uint8_t v_isSharedCheck_4132_; 
lean_dec_ref(v_docCtx_4090_);
lean_dec_ref(v_names_4089_);
v_a_4125_ = lean_ctor_get(v___x_4104_, 0);
v_isSharedCheck_4132_ = !lean_is_exclusive(v___x_4104_);
if (v_isSharedCheck_4132_ == 0)
{
v___x_4127_ = v___x_4104_;
v_isShared_4128_ = v_isSharedCheck_4132_;
goto v_resetjp_4126_;
}
else
{
lean_inc(v_a_4125_);
lean_dec(v___x_4104_);
v___x_4127_ = lean_box(0);
v_isShared_4128_ = v_isSharedCheck_4132_;
goto v_resetjp_4126_;
}
v_resetjp_4126_:
{
lean_object* v___x_4130_; 
if (v_isShared_4128_ == 0)
{
v___x_4130_ = v___x_4127_;
goto v_reusejp_4129_;
}
else
{
lean_object* v_reuseFailAlloc_4131_; 
v_reuseFailAlloc_4131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4131_, 0, v_a_4125_);
v___x_4130_ = v_reuseFailAlloc_4131_;
goto v_reusejp_4129_;
}
v_reusejp_4129_:
{
return v___x_4130_;
}
}
}
}
else
{
lean_object* v___x_4133_; 
lean_dec_ref(v_docCtx_4090_);
lean_dec_ref(v_names_4089_);
v___x_4133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4133_, 0, v_b_4094_);
return v___x_4133_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___boxed(lean_object* v_names_4134_, lean_object* v_docCtx_4135_, lean_object* v_as_4136_, lean_object* v_i_4137_, lean_object* v_stop_4138_, lean_object* v_b_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_){
_start:
{
size_t v_i_boxed_4147_; size_t v_stop_boxed_4148_; lean_object* v_res_4149_; 
v_i_boxed_4147_ = lean_unbox_usize(v_i_4137_);
lean_dec(v_i_4137_);
v_stop_boxed_4148_ = lean_unbox_usize(v_stop_4138_);
lean_dec(v_stop_4138_);
v_res_4149_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5(v_names_4134_, v_docCtx_4135_, v_as_4136_, v_i_boxed_4147_, v_stop_boxed_4148_, v_b_4139_, v___y_4140_, v___y_4141_, v___y_4142_, v___y_4143_, v___y_4144_, v___y_4145_);
lean_dec(v___y_4145_);
lean_dec_ref(v___y_4144_);
lean_dec(v___y_4143_);
lean_dec_ref(v___y_4142_);
lean_dec(v___y_4141_);
lean_dec_ref(v___y_4140_);
lean_dec_ref(v_as_4136_);
return v_res_4149_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4___redArg(lean_object* v_as_4150_, size_t v_sz_4151_, size_t v_i_4152_, lean_object* v_b_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_){
_start:
{
uint8_t v___x_4159_; 
v___x_4159_ = lean_usize_dec_lt(v_i_4152_, v_sz_4151_);
if (v___x_4159_ == 0)
{
lean_object* v___x_4160_; 
v___x_4160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4160_, 0, v_b_4153_);
return v___x_4160_;
}
else
{
lean_object* v_array_4161_; lean_object* v_start_4162_; lean_object* v_stop_4163_; uint8_t v___x_4164_; 
v_array_4161_ = lean_ctor_get(v_b_4153_, 0);
v_start_4162_ = lean_ctor_get(v_b_4153_, 1);
v_stop_4163_ = lean_ctor_get(v_b_4153_, 2);
v___x_4164_ = lean_nat_dec_lt(v_start_4162_, v_stop_4163_);
if (v___x_4164_ == 0)
{
lean_object* v___x_4165_; 
v___x_4165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4165_, 0, v_b_4153_);
return v___x_4165_;
}
else
{
lean_object* v___x_4167_; uint8_t v_isShared_4168_; uint8_t v_isSharedCheck_4188_; 
lean_inc(v_stop_4163_);
lean_inc(v_start_4162_);
lean_inc_ref(v_array_4161_);
v_isSharedCheck_4188_ = !lean_is_exclusive(v_b_4153_);
if (v_isSharedCheck_4188_ == 0)
{
lean_object* v_unused_4189_; lean_object* v_unused_4190_; lean_object* v_unused_4191_; 
v_unused_4189_ = lean_ctor_get(v_b_4153_, 2);
lean_dec(v_unused_4189_);
v_unused_4190_ = lean_ctor_get(v_b_4153_, 1);
lean_dec(v_unused_4190_);
v_unused_4191_ = lean_ctor_get(v_b_4153_, 0);
lean_dec(v_unused_4191_);
v___x_4167_ = v_b_4153_;
v_isShared_4168_ = v_isSharedCheck_4188_;
goto v_resetjp_4166_;
}
else
{
lean_dec(v_b_4153_);
v___x_4167_ = lean_box(0);
v_isShared_4168_ = v_isSharedCheck_4188_;
goto v_resetjp_4166_;
}
v_resetjp_4166_:
{
lean_object* v_a_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; lean_object* v___x_4174_; 
v_a_4169_ = lean_array_uget_borrowed(v_as_4150_, v_i_4152_);
v___x_4170_ = lean_array_fget(v_array_4161_, v_start_4162_);
v___x_4171_ = lean_unsigned_to_nat(1u);
v___x_4172_ = lean_nat_add(v_start_4162_, v___x_4171_);
lean_dec(v_start_4162_);
if (v_isShared_4168_ == 0)
{
lean_ctor_set(v___x_4167_, 1, v___x_4172_);
v___x_4174_ = v___x_4167_;
goto v_reusejp_4173_;
}
else
{
lean_object* v_reuseFailAlloc_4187_; 
v_reuseFailAlloc_4187_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4187_, 0, v_array_4161_);
lean_ctor_set(v_reuseFailAlloc_4187_, 1, v___x_4172_);
lean_ctor_set(v_reuseFailAlloc_4187_, 2, v_stop_4163_);
v___x_4174_ = v_reuseFailAlloc_4187_;
goto v_reusejp_4173_;
}
v_reusejp_4173_:
{
lean_object* v___x_4175_; 
lean_inc(v_a_4169_);
v___x_4175_ = l_Lean_Elab_Structural_reportTermMeasure(v___x_4170_, v_a_4169_, v___y_4154_, v___y_4155_, v___y_4156_, v___y_4157_);
if (lean_obj_tag(v___x_4175_) == 0)
{
size_t v___x_4176_; size_t v___x_4177_; 
lean_dec_ref_known(v___x_4175_, 1);
v___x_4176_ = ((size_t)1ULL);
v___x_4177_ = lean_usize_add(v_i_4152_, v___x_4176_);
v_i_4152_ = v___x_4177_;
v_b_4153_ = v___x_4174_;
goto _start;
}
else
{
lean_object* v_a_4179_; lean_object* v___x_4181_; uint8_t v_isShared_4182_; uint8_t v_isSharedCheck_4186_; 
lean_dec_ref(v___x_4174_);
v_a_4179_ = lean_ctor_get(v___x_4175_, 0);
v_isSharedCheck_4186_ = !lean_is_exclusive(v___x_4175_);
if (v_isSharedCheck_4186_ == 0)
{
v___x_4181_ = v___x_4175_;
v_isShared_4182_ = v_isSharedCheck_4186_;
goto v_resetjp_4180_;
}
else
{
lean_inc(v_a_4179_);
lean_dec(v___x_4175_);
v___x_4181_ = lean_box(0);
v_isShared_4182_ = v_isSharedCheck_4186_;
goto v_resetjp_4180_;
}
v_resetjp_4180_:
{
lean_object* v___x_4184_; 
if (v_isShared_4182_ == 0)
{
v___x_4184_ = v___x_4181_;
goto v_reusejp_4183_;
}
else
{
lean_object* v_reuseFailAlloc_4185_; 
v_reuseFailAlloc_4185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4185_, 0, v_a_4179_);
v___x_4184_ = v_reuseFailAlloc_4185_;
goto v_reusejp_4183_;
}
v_reusejp_4183_:
{
return v___x_4184_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4___redArg___boxed(lean_object* v_as_4192_, lean_object* v_sz_4193_, lean_object* v_i_4194_, lean_object* v_b_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_){
_start:
{
size_t v_sz_boxed_4201_; size_t v_i_boxed_4202_; lean_object* v_res_4203_; 
v_sz_boxed_4201_ = lean_unbox_usize(v_sz_4193_);
lean_dec(v_sz_4193_);
v_i_boxed_4202_ = lean_unbox_usize(v_i_4194_);
lean_dec(v_i_4194_);
v_res_4203_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4___redArg(v_as_4192_, v_sz_boxed_4201_, v_i_boxed_4202_, v_b_4195_, v___y_4196_, v___y_4197_, v___y_4198_, v___y_4199_);
lean_dec(v___y_4199_);
lean_dec_ref(v___y_4198_);
lean_dec(v___y_4197_);
lean_dec_ref(v___y_4196_);
lean_dec_ref(v_as_4192_);
return v_res_4203_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___redArg(size_t v_sz_4204_, size_t v_i_4205_, lean_object* v_bs_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_){
_start:
{
uint8_t v___x_4210_; 
v___x_4210_ = lean_usize_dec_lt(v_i_4205_, v_sz_4204_);
if (v___x_4210_ == 0)
{
lean_object* v___x_4211_; 
v___x_4211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4211_, 0, v_bs_4206_);
return v___x_4211_;
}
else
{
lean_object* v_v_4212_; lean_object* v___x_4213_; lean_object* v_bs_x27_4214_; lean_object* v___x_4215_; 
v_v_4212_ = lean_array_uget(v_bs_4206_, v_i_4205_);
v___x_4213_ = lean_unsigned_to_nat(0u);
v_bs_x27_4214_ = lean_array_uset(v_bs_4206_, v_i_4205_, v___x_4213_);
v___x_4215_ = l_Lean_Elab_eraseRecAppSyntax(v_v_4212_, v___y_4207_, v___y_4208_);
if (lean_obj_tag(v___x_4215_) == 0)
{
lean_object* v_a_4216_; size_t v___x_4217_; size_t v___x_4218_; lean_object* v___x_4219_; 
v_a_4216_ = lean_ctor_get(v___x_4215_, 0);
lean_inc(v_a_4216_);
lean_dec_ref_known(v___x_4215_, 1);
v___x_4217_ = ((size_t)1ULL);
v___x_4218_ = lean_usize_add(v_i_4205_, v___x_4217_);
v___x_4219_ = lean_array_uset(v_bs_x27_4214_, v_i_4205_, v_a_4216_);
v_i_4205_ = v___x_4218_;
v_bs_4206_ = v___x_4219_;
goto _start;
}
else
{
lean_object* v_a_4221_; lean_object* v___x_4223_; uint8_t v_isShared_4224_; uint8_t v_isSharedCheck_4228_; 
lean_dec_ref(v_bs_x27_4214_);
v_a_4221_ = lean_ctor_get(v___x_4215_, 0);
v_isSharedCheck_4228_ = !lean_is_exclusive(v___x_4215_);
if (v_isSharedCheck_4228_ == 0)
{
v___x_4223_ = v___x_4215_;
v_isShared_4224_ = v_isSharedCheck_4228_;
goto v_resetjp_4222_;
}
else
{
lean_inc(v_a_4221_);
lean_dec(v___x_4215_);
v___x_4223_ = lean_box(0);
v_isShared_4224_ = v_isSharedCheck_4228_;
goto v_resetjp_4222_;
}
v_resetjp_4222_:
{
lean_object* v___x_4226_; 
if (v_isShared_4224_ == 0)
{
v___x_4226_ = v___x_4223_;
goto v_reusejp_4225_;
}
else
{
lean_object* v_reuseFailAlloc_4227_; 
v_reuseFailAlloc_4227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4227_, 0, v_a_4221_);
v___x_4226_ = v_reuseFailAlloc_4227_;
goto v_reusejp_4225_;
}
v_reusejp_4225_:
{
return v___x_4226_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___redArg___boxed(lean_object* v_sz_4229_, lean_object* v_i_4230_, lean_object* v_bs_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_, lean_object* v___y_4234_){
_start:
{
size_t v_sz_boxed_4235_; size_t v_i_boxed_4236_; lean_object* v_res_4237_; 
v_sz_boxed_4235_ = lean_unbox_usize(v_sz_4229_);
lean_dec(v_sz_4229_);
v_i_boxed_4236_ = lean_unbox_usize(v_i_4230_);
lean_dec(v_i_4230_);
v_res_4237_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___redArg(v_sz_boxed_4235_, v_i_boxed_4236_, v_bs_4231_, v___y_4232_, v___y_4233_);
lean_dec(v___y_4233_);
lean_dec_ref(v___y_4232_);
return v_res_4237_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___redArg(lean_object* v_as_4238_, size_t v_sz_4239_, size_t v_i_4240_, lean_object* v_b_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_){
_start:
{
uint8_t v___x_4245_; 
v___x_4245_ = lean_usize_dec_lt(v_i_4240_, v_sz_4239_);
if (v___x_4245_ == 0)
{
lean_object* v___x_4246_; 
v___x_4246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4246_, 0, v_b_4241_);
return v___x_4246_;
}
else
{
lean_object* v_a_4247_; lean_object* v_declName_4248_; lean_object* v___x_4249_; lean_object* v___x_4250_; 
v_a_4247_ = lean_array_uget_borrowed(v_as_4238_, v_i_4240_);
v_declName_4248_ = lean_ctor_get(v_a_4247_, 3);
v___x_4249_ = lean_box(0);
lean_inc(v_declName_4248_);
v___x_4250_ = l_Lean_enableRealizationsForConst(v_declName_4248_, v___y_4242_, v___y_4243_);
if (lean_obj_tag(v___x_4250_) == 0)
{
size_t v___x_4251_; size_t v___x_4252_; 
lean_dec_ref_known(v___x_4250_, 1);
v___x_4251_ = ((size_t)1ULL);
v___x_4252_ = lean_usize_add(v_i_4240_, v___x_4251_);
v_i_4240_ = v___x_4252_;
v_b_4241_ = v___x_4249_;
goto _start;
}
else
{
return v___x_4250_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___redArg___boxed(lean_object* v_as_4254_, lean_object* v_sz_4255_, lean_object* v_i_4256_, lean_object* v_b_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_){
_start:
{
size_t v_sz_boxed_4261_; size_t v_i_boxed_4262_; lean_object* v_res_4263_; 
v_sz_boxed_4261_ = lean_unbox_usize(v_sz_4255_);
lean_dec(v_sz_4255_);
v_i_boxed_4262_ = lean_unbox_usize(v_i_4256_);
lean_dec(v_i_4256_);
v_res_4263_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___redArg(v_as_4254_, v_sz_boxed_4261_, v_i_boxed_4262_, v_b_4257_, v___y_4258_, v___y_4259_);
lean_dec(v___y_4259_);
lean_dec_ref(v___y_4258_);
lean_dec_ref(v_as_4254_);
return v_res_4263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_structuralRecursion(lean_object* v_docCtx_4264_, lean_object* v_preDefs_4265_, lean_object* v_termMeasure_x3fs_4266_, lean_object* v_a_4267_, lean_object* v_a_4268_, lean_object* v_a_4269_, lean_object* v_a_4270_, lean_object* v_a_4271_, lean_object* v_a_4272_){
_start:
{
size_t v_sz_4274_; size_t v___x_4275_; lean_object* v_names_4276_; lean_object* v___x_4277_; 
v_sz_4274_ = lean_array_size(v_preDefs_4265_);
v___x_4275_ = ((size_t)0ULL);
lean_inc_ref_n(v_preDefs_4265_, 2);
v_names_4276_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16(v_sz_4274_, v___x_4275_, v_preDefs_4265_);
v___x_4277_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos(v_preDefs_4265_, v_termMeasure_x3fs_4266_, v_a_4269_, v_a_4270_, v_a_4271_, v_a_4272_);
if (lean_obj_tag(v___x_4277_) == 0)
{
lean_object* v_a_4278_; lean_object* v_snd_4279_; lean_object* v_fst_4280_; lean_object* v_fst_4281_; lean_object* v_snd_4282_; lean_object* v___x_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; size_t v_sz_4316_; lean_object* v___x_4317_; 
v_a_4278_ = lean_ctor_get(v___x_4277_, 0);
lean_inc(v_a_4278_);
lean_dec_ref_known(v___x_4277_, 1);
v_snd_4279_ = lean_ctor_get(v_a_4278_, 1);
lean_inc(v_snd_4279_);
v_fst_4280_ = lean_ctor_get(v_a_4278_, 0);
lean_inc(v_fst_4280_);
lean_dec(v_a_4278_);
v_fst_4281_ = lean_ctor_get(v_snd_4279_, 0);
lean_inc(v_fst_4281_);
v_snd_4282_ = lean_ctor_get(v_snd_4279_, 1);
lean_inc(v_snd_4282_);
lean_dec(v_snd_4279_);
v___x_4313_ = lean_unsigned_to_nat(0u);
v___x_4314_ = lean_array_get_size(v_preDefs_4265_);
lean_inc_ref(v_preDefs_4265_);
v___x_4315_ = l_Array_toSubarray___redArg(v_preDefs_4265_, v___x_4313_, v___x_4314_);
v_sz_4316_ = lean_array_size(v_fst_4280_);
v___x_4317_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4___redArg(v_fst_4280_, v_sz_4316_, v___x_4275_, v___x_4315_, v_a_4269_, v_a_4270_, v_a_4271_, v_a_4272_);
if (lean_obj_tag(v___x_4317_) == 0)
{
lean_object* v___x_4318_; uint8_t v___x_4319_; 
lean_dec_ref_known(v___x_4317_, 1);
v___x_4318_ = lean_array_get_size(v_fst_4281_);
v___x_4319_ = lean_nat_dec_lt(v___x_4313_, v___x_4318_);
if (v___x_4319_ == 0)
{
lean_dec_ref(v_names_4276_);
goto v___jp_4283_;
}
else
{
lean_object* v___x_4320_; size_t v___x_4321_; lean_object* v___x_4322_; 
v___x_4320_ = lean_box(0);
v___x_4321_ = lean_usize_of_nat(v___x_4318_);
lean_inc_ref(v_docCtx_4264_);
v___x_4322_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5(v_names_4276_, v_docCtx_4264_, v_fst_4281_, v___x_4275_, v___x_4321_, v___x_4320_, v_a_4267_, v_a_4268_, v_a_4269_, v_a_4270_, v_a_4271_, v_a_4272_);
if (lean_obj_tag(v___x_4322_) == 0)
{
lean_dec_ref_known(v___x_4322_, 1);
goto v___jp_4283_;
}
else
{
lean_dec(v_snd_4282_);
lean_dec(v_fst_4281_);
lean_dec(v_fst_4280_);
lean_dec_ref(v_preDefs_4265_);
lean_dec_ref(v_docCtx_4264_);
return v___x_4322_;
}
}
}
else
{
lean_object* v_a_4323_; lean_object* v___x_4325_; uint8_t v_isShared_4326_; uint8_t v_isSharedCheck_4330_; 
lean_dec(v_snd_4282_);
lean_dec(v_fst_4281_);
lean_dec(v_fst_4280_);
lean_dec_ref(v_names_4276_);
lean_dec_ref(v_preDefs_4265_);
lean_dec_ref(v_docCtx_4264_);
v_a_4323_ = lean_ctor_get(v___x_4317_, 0);
v_isSharedCheck_4330_ = !lean_is_exclusive(v___x_4317_);
if (v_isSharedCheck_4330_ == 0)
{
v___x_4325_ = v___x_4317_;
v_isShared_4326_ = v_isSharedCheck_4330_;
goto v_resetjp_4324_;
}
else
{
lean_inc(v_a_4323_);
lean_dec(v___x_4317_);
v___x_4325_ = lean_box(0);
v_isShared_4326_ = v_isSharedCheck_4330_;
goto v_resetjp_4324_;
}
v_resetjp_4324_:
{
lean_object* v___x_4328_; 
if (v_isShared_4326_ == 0)
{
v___x_4328_ = v___x_4325_;
goto v_reusejp_4327_;
}
else
{
lean_object* v_reuseFailAlloc_4329_; 
v_reuseFailAlloc_4329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4329_, 0, v_a_4323_);
v___x_4328_ = v_reuseFailAlloc_4329_;
goto v_reusejp_4327_;
}
v_reusejp_4327_:
{
return v___x_4328_;
}
}
}
v___jp_4283_:
{
lean_object* v___x_4284_; 
v___x_4284_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___redArg(v_sz_4274_, v___x_4275_, v_preDefs_4265_, v_a_4271_, v_a_4272_);
if (lean_obj_tag(v___x_4284_) == 0)
{
lean_object* v_a_4285_; lean_object* v___x_4286_; 
v_a_4285_ = lean_ctor_get(v___x_4284_, 0);
lean_inc_n(v_a_4285_, 2);
lean_dec_ref_known(v___x_4284_, 1);
lean_inc_ref(v_docCtx_4264_);
v___x_4286_ = l_Lean_Elab_addAndCompilePartialRec(v_docCtx_4264_, v_a_4285_, v_a_4267_, v_a_4268_, v_a_4269_, v_a_4270_, v_a_4271_, v_a_4272_);
if (lean_obj_tag(v___x_4286_) == 0)
{
lean_object* v___x_4287_; lean_object* v___x_4288_; lean_object* v___x_4289_; size_t v_sz_4290_; lean_object* v___x_4291_; 
lean_dec_ref_known(v___x_4286_, 1);
v___x_4287_ = lean_unsigned_to_nat(0u);
v___x_4288_ = lean_array_get_size(v_fst_4280_);
lean_inc(v_fst_4280_);
v___x_4289_ = l_Array_toSubarray___redArg(v_fst_4280_, v___x_4287_, v___x_4288_);
v_sz_4290_ = lean_array_size(v_a_4285_);
lean_inc(v_a_4285_);
v___x_4291_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__1(v_a_4285_, v_fst_4280_, v_docCtx_4264_, v_snd_4282_, v_a_4285_, v_sz_4290_, v___x_4275_, v___x_4289_, v_a_4267_, v_a_4268_, v_a_4269_, v_a_4270_, v_a_4271_, v_a_4272_);
lean_dec(v_fst_4280_);
if (lean_obj_tag(v___x_4291_) == 0)
{
lean_object* v___x_4292_; lean_object* v___x_4293_; 
lean_dec_ref_known(v___x_4291_, 1);
v___x_4292_ = lean_box(0);
v___x_4293_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___redArg(v_a_4285_, v_sz_4290_, v___x_4275_, v___x_4292_, v_a_4269_, v_a_4270_, v_a_4271_, v_a_4272_);
if (lean_obj_tag(v___x_4293_) == 0)
{
lean_object* v___x_4294_; 
lean_dec_ref_known(v___x_4293_, 1);
v___x_4294_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___redArg(v_a_4285_, v_sz_4290_, v___x_4275_, v___x_4292_, v_a_4271_, v_a_4272_);
lean_dec(v_a_4285_);
if (lean_obj_tag(v___x_4294_) == 0)
{
uint8_t v___x_4295_; lean_object* v___x_4296_; 
lean_dec_ref_known(v___x_4294_, 1);
v___x_4295_ = 1;
v___x_4296_ = l_Lean_Elab_applyAttributesOf(v_fst_4281_, v___x_4295_, v_a_4267_, v_a_4268_, v_a_4269_, v_a_4270_, v_a_4271_, v_a_4272_);
lean_dec(v_fst_4281_);
return v___x_4296_;
}
else
{
lean_dec(v_fst_4281_);
return v___x_4294_;
}
}
else
{
lean_dec(v_a_4285_);
lean_dec(v_fst_4281_);
return v___x_4293_;
}
}
else
{
lean_object* v_a_4297_; lean_object* v___x_4299_; uint8_t v_isShared_4300_; uint8_t v_isSharedCheck_4304_; 
lean_dec(v_a_4285_);
lean_dec(v_fst_4281_);
v_a_4297_ = lean_ctor_get(v___x_4291_, 0);
v_isSharedCheck_4304_ = !lean_is_exclusive(v___x_4291_);
if (v_isSharedCheck_4304_ == 0)
{
v___x_4299_ = v___x_4291_;
v_isShared_4300_ = v_isSharedCheck_4304_;
goto v_resetjp_4298_;
}
else
{
lean_inc(v_a_4297_);
lean_dec(v___x_4291_);
v___x_4299_ = lean_box(0);
v_isShared_4300_ = v_isSharedCheck_4304_;
goto v_resetjp_4298_;
}
v_resetjp_4298_:
{
lean_object* v___x_4302_; 
if (v_isShared_4300_ == 0)
{
v___x_4302_ = v___x_4299_;
goto v_reusejp_4301_;
}
else
{
lean_object* v_reuseFailAlloc_4303_; 
v_reuseFailAlloc_4303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4303_, 0, v_a_4297_);
v___x_4302_ = v_reuseFailAlloc_4303_;
goto v_reusejp_4301_;
}
v_reusejp_4301_:
{
return v___x_4302_;
}
}
}
}
else
{
lean_dec(v_a_4285_);
lean_dec(v_snd_4282_);
lean_dec(v_fst_4281_);
lean_dec(v_fst_4280_);
lean_dec_ref(v_docCtx_4264_);
return v___x_4286_;
}
}
else
{
lean_object* v_a_4305_; lean_object* v___x_4307_; uint8_t v_isShared_4308_; uint8_t v_isSharedCheck_4312_; 
lean_dec(v_snd_4282_);
lean_dec(v_fst_4281_);
lean_dec(v_fst_4280_);
lean_dec_ref(v_docCtx_4264_);
v_a_4305_ = lean_ctor_get(v___x_4284_, 0);
v_isSharedCheck_4312_ = !lean_is_exclusive(v___x_4284_);
if (v_isSharedCheck_4312_ == 0)
{
v___x_4307_ = v___x_4284_;
v_isShared_4308_ = v_isSharedCheck_4312_;
goto v_resetjp_4306_;
}
else
{
lean_inc(v_a_4305_);
lean_dec(v___x_4284_);
v___x_4307_ = lean_box(0);
v_isShared_4308_ = v_isSharedCheck_4312_;
goto v_resetjp_4306_;
}
v_resetjp_4306_:
{
lean_object* v___x_4310_; 
if (v_isShared_4308_ == 0)
{
v___x_4310_ = v___x_4307_;
goto v_reusejp_4309_;
}
else
{
lean_object* v_reuseFailAlloc_4311_; 
v_reuseFailAlloc_4311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4311_, 0, v_a_4305_);
v___x_4310_ = v_reuseFailAlloc_4311_;
goto v_reusejp_4309_;
}
v_reusejp_4309_:
{
return v___x_4310_;
}
}
}
}
}
else
{
lean_object* v_a_4331_; lean_object* v___x_4333_; uint8_t v_isShared_4334_; uint8_t v_isSharedCheck_4338_; 
lean_dec_ref(v_names_4276_);
lean_dec_ref(v_preDefs_4265_);
lean_dec_ref(v_docCtx_4264_);
v_a_4331_ = lean_ctor_get(v___x_4277_, 0);
v_isSharedCheck_4338_ = !lean_is_exclusive(v___x_4277_);
if (v_isSharedCheck_4338_ == 0)
{
v___x_4333_ = v___x_4277_;
v_isShared_4334_ = v_isSharedCheck_4338_;
goto v_resetjp_4332_;
}
else
{
lean_inc(v_a_4331_);
lean_dec(v___x_4277_);
v___x_4333_ = lean_box(0);
v_isShared_4334_ = v_isSharedCheck_4338_;
goto v_resetjp_4332_;
}
v_resetjp_4332_:
{
lean_object* v___x_4336_; 
if (v_isShared_4334_ == 0)
{
v___x_4336_ = v___x_4333_;
goto v_reusejp_4335_;
}
else
{
lean_object* v_reuseFailAlloc_4337_; 
v_reuseFailAlloc_4337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4337_, 0, v_a_4331_);
v___x_4336_ = v_reuseFailAlloc_4337_;
goto v_reusejp_4335_;
}
v_reusejp_4335_:
{
return v___x_4336_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_structuralRecursion___boxed(lean_object* v_docCtx_4339_, lean_object* v_preDefs_4340_, lean_object* v_termMeasure_x3fs_4341_, lean_object* v_a_4342_, lean_object* v_a_4343_, lean_object* v_a_4344_, lean_object* v_a_4345_, lean_object* v_a_4346_, lean_object* v_a_4347_, lean_object* v_a_4348_){
_start:
{
lean_object* v_res_4349_; 
v_res_4349_ = l_Lean_Elab_Structural_structuralRecursion(v_docCtx_4339_, v_preDefs_4340_, v_termMeasure_x3fs_4341_, v_a_4342_, v_a_4343_, v_a_4344_, v_a_4345_, v_a_4346_, v_a_4347_);
lean_dec(v_a_4347_);
lean_dec_ref(v_a_4346_);
lean_dec(v_a_4345_);
lean_dec_ref(v_a_4344_);
lean_dec(v_a_4343_);
lean_dec_ref(v_a_4342_);
return v_res_4349_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0(size_t v_sz_4350_, size_t v_i_4351_, lean_object* v_bs_4352_, lean_object* v___y_4353_, lean_object* v___y_4354_, lean_object* v___y_4355_, lean_object* v___y_4356_, lean_object* v___y_4357_, lean_object* v___y_4358_){
_start:
{
lean_object* v___x_4360_; 
v___x_4360_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___redArg(v_sz_4350_, v_i_4351_, v_bs_4352_, v___y_4357_, v___y_4358_);
return v___x_4360_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___boxed(lean_object* v_sz_4361_, lean_object* v_i_4362_, lean_object* v_bs_4363_, lean_object* v___y_4364_, lean_object* v___y_4365_, lean_object* v___y_4366_, lean_object* v___y_4367_, lean_object* v___y_4368_, lean_object* v___y_4369_, lean_object* v___y_4370_){
_start:
{
size_t v_sz_boxed_4371_; size_t v_i_boxed_4372_; lean_object* v_res_4373_; 
v_sz_boxed_4371_ = lean_unbox_usize(v_sz_4361_);
lean_dec(v_sz_4361_);
v_i_boxed_4372_ = lean_unbox_usize(v_i_4362_);
lean_dec(v_i_4362_);
v_res_4373_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0(v_sz_boxed_4371_, v_i_boxed_4372_, v_bs_4363_, v___y_4364_, v___y_4365_, v___y_4366_, v___y_4367_, v___y_4368_, v___y_4369_);
lean_dec(v___y_4369_);
lean_dec_ref(v___y_4368_);
lean_dec(v___y_4367_);
lean_dec_ref(v___y_4366_);
lean_dec(v___y_4365_);
lean_dec_ref(v___y_4364_);
return v_res_4373_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2(lean_object* v_as_4374_, size_t v_sz_4375_, size_t v_i_4376_, lean_object* v_b_4377_, lean_object* v___y_4378_, lean_object* v___y_4379_, lean_object* v___y_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_, lean_object* v___y_4383_){
_start:
{
lean_object* v___x_4385_; 
v___x_4385_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___redArg(v_as_4374_, v_sz_4375_, v_i_4376_, v_b_4377_, v___y_4380_, v___y_4381_, v___y_4382_, v___y_4383_);
return v___x_4385_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___boxed(lean_object* v_as_4386_, lean_object* v_sz_4387_, lean_object* v_i_4388_, lean_object* v_b_4389_, lean_object* v___y_4390_, lean_object* v___y_4391_, lean_object* v___y_4392_, lean_object* v___y_4393_, lean_object* v___y_4394_, lean_object* v___y_4395_, lean_object* v___y_4396_){
_start:
{
size_t v_sz_boxed_4397_; size_t v_i_boxed_4398_; lean_object* v_res_4399_; 
v_sz_boxed_4397_ = lean_unbox_usize(v_sz_4387_);
lean_dec(v_sz_4387_);
v_i_boxed_4398_ = lean_unbox_usize(v_i_4388_);
lean_dec(v_i_4388_);
v_res_4399_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2(v_as_4386_, v_sz_boxed_4397_, v_i_boxed_4398_, v_b_4389_, v___y_4390_, v___y_4391_, v___y_4392_, v___y_4393_, v___y_4394_, v___y_4395_);
lean_dec(v___y_4395_);
lean_dec_ref(v___y_4394_);
lean_dec(v___y_4393_);
lean_dec_ref(v___y_4392_);
lean_dec(v___y_4391_);
lean_dec_ref(v___y_4390_);
lean_dec_ref(v_as_4386_);
return v_res_4399_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3(lean_object* v_as_4400_, size_t v_sz_4401_, size_t v_i_4402_, lean_object* v_b_4403_, lean_object* v___y_4404_, lean_object* v___y_4405_, lean_object* v___y_4406_, lean_object* v___y_4407_, lean_object* v___y_4408_, lean_object* v___y_4409_){
_start:
{
lean_object* v___x_4411_; 
v___x_4411_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___redArg(v_as_4400_, v_sz_4401_, v_i_4402_, v_b_4403_, v___y_4408_, v___y_4409_);
return v___x_4411_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___boxed(lean_object* v_as_4412_, lean_object* v_sz_4413_, lean_object* v_i_4414_, lean_object* v_b_4415_, lean_object* v___y_4416_, lean_object* v___y_4417_, lean_object* v___y_4418_, lean_object* v___y_4419_, lean_object* v___y_4420_, lean_object* v___y_4421_, lean_object* v___y_4422_){
_start:
{
size_t v_sz_boxed_4423_; size_t v_i_boxed_4424_; lean_object* v_res_4425_; 
v_sz_boxed_4423_ = lean_unbox_usize(v_sz_4413_);
lean_dec(v_sz_4413_);
v_i_boxed_4424_ = lean_unbox_usize(v_i_4414_);
lean_dec(v_i_4414_);
v_res_4425_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3(v_as_4412_, v_sz_boxed_4423_, v_i_boxed_4424_, v_b_4415_, v___y_4416_, v___y_4417_, v___y_4418_, v___y_4419_, v___y_4420_, v___y_4421_);
lean_dec(v___y_4421_);
lean_dec_ref(v___y_4420_);
lean_dec(v___y_4419_);
lean_dec_ref(v___y_4418_);
lean_dec(v___y_4417_);
lean_dec_ref(v___y_4416_);
lean_dec_ref(v_as_4412_);
return v_res_4425_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4(lean_object* v_as_4426_, size_t v_sz_4427_, size_t v_i_4428_, lean_object* v_b_4429_, lean_object* v___y_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_){
_start:
{
lean_object* v___x_4437_; 
v___x_4437_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4___redArg(v_as_4426_, v_sz_4427_, v_i_4428_, v_b_4429_, v___y_4432_, v___y_4433_, v___y_4434_, v___y_4435_);
return v___x_4437_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4___boxed(lean_object* v_as_4438_, lean_object* v_sz_4439_, lean_object* v_i_4440_, lean_object* v_b_4441_, lean_object* v___y_4442_, lean_object* v___y_4443_, lean_object* v___y_4444_, lean_object* v___y_4445_, lean_object* v___y_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_){
_start:
{
size_t v_sz_boxed_4449_; size_t v_i_boxed_4450_; lean_object* v_res_4451_; 
v_sz_boxed_4449_ = lean_unbox_usize(v_sz_4439_);
lean_dec(v_sz_4439_);
v_i_boxed_4450_ = lean_unbox_usize(v_i_4440_);
lean_dec(v_i_4440_);
v_res_4451_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4(v_as_4438_, v_sz_boxed_4449_, v_i_boxed_4450_, v_b_4441_, v___y_4442_, v___y_4443_, v___y_4444_, v___y_4445_, v___y_4446_, v___y_4447_);
lean_dec(v___y_4447_);
lean_dec_ref(v___y_4446_);
lean_dec(v___y_4445_);
lean_dec_ref(v___y_4444_);
lean_dec(v___y_4443_);
lean_dec_ref(v___y_4442_);
lean_dec_ref(v_as_4438_);
return v_res_4451_;
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
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_PreDefinition_Structural_Main(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
