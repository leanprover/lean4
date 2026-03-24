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
lean_object* l_Lean_Name_mkStr1(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVarOf(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Meta_PProdN_mkLambdas___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_mkBRecOnMotive(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Environment_unlockAsync(lean_object*);
lean_object* l_Lean_withEnv___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Lean_Elab_Structural_mkBRecOnApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Elab_TerminationMeasure_delab(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Elab_addAsAxiom___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_instInhabited(lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* lean_local_ctx_erase(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_Elab_Structural_RecArgInfo_indicesAndRecArgPos(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Elab_FixedParamPerm_instantiateLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_FixedParamPerm_instantiateForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Structural_instInhabitedRecArgInfo_default;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isInductiveCore_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_InductiveVal_numTypeFormers(lean_object*);
lean_object* l_Array_range(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Nat_blt___boxed(lean_object*, lean_object*);
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInductivePredicate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_zip___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_FixedParamPerm_buildArgs___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_beta(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferArgumentTypesN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_Positions_numIndices(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_instInhabitedPreDefinition_default;
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
lean_object* l_Lean_Meta_getLocalInstances___redArg(lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_Elab_FixedParamPerms_erase(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_tryCandidates___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_addSmartUnfoldingDef(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_DefKind_isTheorem(uint8_t);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_abstractNestedProofs(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_registerEqnsInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_enableRealizationsForConst(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_generateEagerEqns(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13_spec__25___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13_spec__25___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13_spec__25(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13_spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13_spec__24_spec__26___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13_spec__24_spec__26___redArg___closed__0;
static lean_once_cell_t l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13_spec__24_spec__26___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13_spec__24_spec__26___redArg___closed__1;
static lean_once_cell_t l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13_spec__24_spec__26___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13_spec__24_spec__26___redArg___closed__2;
static lean_once_cell_t l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13_spec__24_spec__26___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13_spec__24_spec__26___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13_spec__24_spec__26___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13_spec__24_spec__26___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13_spec__24___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13_spec__24___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13___redArg___lam__1___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13___redArg___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + sizeof(size_t)*1, .m_other = 0, .m_tag = 0}, .m_objs = {(lean_object*)(size_t)(0ULL)}};
LEAN_EXPORT const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13___redArg___boxed__const__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13___redArg___boxed__const__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__15___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__15___redArg___closed__0;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__15___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17_spec__30___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17_spec__30___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_f"};
static const lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___redArg___closed__0 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___redArg___closed__0_value;
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(253, 65, 185, 154, 193, 83, 240, 170)}};
static const lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___redArg___closed__1 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16(lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__15___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__15___redArg___closed__0;
static const lean_closure_object l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__15___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__15___redArg___closed__1 = (const lean_object*)&l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__15___redArg___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__15___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__15___redArg___closed__2 = (const lean_object*)&l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__15___redArg___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__15___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__15___redArg___closed__3 = (const lean_object*)&l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__15___redArg___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__15___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__15___redArg___closed__4 = (const lean_object*)&l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__15___redArg___closed__4_value;
static lean_once_cell_t l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__15___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__15___redArg___closed__5;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__14___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__16___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "Lean.Elab.PreDefinition.Structural.Basic"};
static const lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg___closed__0_value;
static const lean_string_object l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Lean.Elab.Structural.Positions.mapMwith"};
static const lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg___closed__1_value;
static const lean_string_object l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "assertion violation: positions.size = ys.size\n  "};
static const lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg___closed__3;
static const lean_string_object l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "assertion violation: positions.numIndices = xs.size\n  "};
static const lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg___closed__4 = (const lean_object*)&l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg___closed__5;
static const lean_array_object l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg___closed__6 = (const lean_object*)&l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9___redArg___closed__0;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "_inhabitedExprDummy"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 247, 56, 151, 29, 116, 116, 243)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___closed__2;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "packedFArgs: "};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___closed__3_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___closed__4;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "FArgs: "};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___closed__5 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___closed__5_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___closed__6;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "FTypes: "};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___closed__7 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___closed__7_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___closed__8;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "funTypes: "};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___closed__9 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___closed__9_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___closed__10;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = ", motives: "};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___closed__11 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___closed__11_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___closed__12;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__20___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__9_spec__10___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__9_spec__10___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__9_spec__10___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__9_spec__10___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__9_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__9___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__11___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Nat_blt___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__11___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__11___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__12(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__8___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__8___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__8(lean_object*);
static const lean_string_object l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "Lean.Elab.Structural.Positions.groupAndSort"};
static const lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__0_value;
static const lean_string_object l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "assertion violation: Array.range xs.size == positions.flatten.qsort Nat.blt\n  "};
static const lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__2;
static const lean_array_object l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__3 = (const lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_PProdN_mkLambdas___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__4 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__4_value;
static const lean_closure_object l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__5 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__5_value;
static const lean_array_object l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__6 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__6_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "assignments of type formers of "};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__7 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__7_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__8;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " to functions: "};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__9 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__9_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__10;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__15(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__15___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17_spec__30(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17_spec__30___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__14(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13_spec__24_spec__26(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13_spec__24_spec__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13_spec__24(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13_spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__9_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__9_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__2___boxed(lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "New recArgInfos "};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___closed__1;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Reduced fixed params from "};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___closed__3;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " to "};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___closed__5;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = ", erasing "};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___closed__6 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___closed__6_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___closed__7;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Trying argument set "};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___closed__8 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___closed__8_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___closed__9;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__15(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 58, .m_capacity = 58, .m_length = 57, .m_data = "structural recursion failed, produced type incorrect term"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4___closed__1;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_structuralRecursion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_structuralRecursion___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___redArg(lean_object* v_cls_139_, lean_object* v___y_140_){
_start:
{
lean_object* v_options_142_; uint8_t v_hasTrace_143_; 
v_options_142_ = lean_ctor_get(v___y_140_, 2);
v_hasTrace_143_ = lean_ctor_get_uint8(v_options_142_, sizeof(void*)*1);
if (v_hasTrace_143_ == 0)
{
lean_object* v___x_144_; lean_object* v___x_145_; 
lean_dec(v_cls_139_);
v___x_144_ = lean_box(v_hasTrace_143_);
v___x_145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_145_, 0, v___x_144_);
return v___x_145_;
}
else
{
lean_object* v_inheritedTraceOptions_146_; lean_object* v___x_147_; lean_object* v___x_148_; uint8_t v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v_inheritedTraceOptions_146_ = lean_ctor_get(v___y_140_, 13);
v___x_147_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___redArg___closed__1));
v___x_148_ = l_Lean_Name_append(v___x_147_, v_cls_139_);
v___x_149_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_146_, v_options_142_, v___x_148_);
lean_dec(v___x_148_);
v___x_150_ = lean_box(v___x_149_);
v___x_151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_151_, 0, v___x_150_);
return v___x_151_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___redArg___boxed(lean_object* v_cls_152_, lean_object* v___y_153_, lean_object* v___y_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___redArg(v_cls_152_, v___y_153_);
lean_dec_ref(v___y_153_);
return v_res_155_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5(lean_object* v_cls_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_){
_start:
{
lean_object* v___x_162_; 
v___x_162_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___redArg(v_cls_156_, v___y_159_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___boxed(lean_object* v_cls_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5(v_cls_163_, v___y_164_, v___y_165_, v___y_166_, v___y_167_);
lean_dec(v___y_167_);
lean_dec_ref(v___y_166_);
lean_dec(v___y_165_);
lean_dec_ref(v___y_164_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0(lean_object* v_x_170_){
_start:
{
lean_object* v_indIdx_171_; 
v_indIdx_171_ = lean_ctor_get(v_x_170_, 5);
lean_inc(v_indIdx_171_);
return v_indIdx_171_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0___boxed(lean_object* v_x_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0(v_x_172_);
lean_dec_ref(v_x_172_);
return v_res_173_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13___redArg___lam__1(lean_object* v___x_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_){
_start:
{
lean_object* v___x_180_; 
v___x_180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_180_, 0, v___x_174_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13___redArg___lam__1___boxed(lean_object* v___x_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13___redArg___lam__1(v___x_181_, v___y_182_, v___y_183_, v___y_184_, v___y_185_);
lean_dec(v___y_185_);
lean_dec_ref(v___y_184_);
lean_dec(v___y_183_);
lean_dec_ref(v___y_182_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13_spec__25___redArg(lean_object* v_as_188_, size_t v_i_189_, size_t v_stop_190_, lean_object* v_b_191_, lean_object* v___y_192_, lean_object* v___y_193_){
_start:
{
uint8_t v___x_195_; 
v___x_195_ = lean_usize_dec_eq(v_i_189_, v_stop_190_);
if (v___x_195_ == 0)
{
lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_196_ = lean_array_uget_borrowed(v_as_188_, v_i_189_);
v___x_197_ = l_Lean_Elab_addAsAxiom___redArg(v___x_196_, v___y_192_, v___y_193_);
if (lean_obj_tag(v___x_197_) == 0)
{
lean_object* v_a_198_; size_t v___x_199_; size_t v___x_200_; 
v_a_198_ = lean_ctor_get(v___x_197_, 0);
lean_inc(v_a_198_);
lean_dec_ref(v___x_197_);
v___x_199_ = ((size_t)1ULL);
v___x_200_ = lean_usize_add(v_i_189_, v___x_199_);
v_i_189_ = v___x_200_;
v_b_191_ = v_a_198_;
goto _start;
}
else
{
return v___x_197_;
}
}
else
{
lean_object* v___x_202_; 
v___x_202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_202_, 0, v_b_191_);
return v___x_202_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13_spec__25___redArg___boxed(lean_object* v_as_203_, lean_object* v_i_204_, lean_object* v_stop_205_, lean_object* v_b_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_){
_start:
{
size_t v_i_boxed_210_; size_t v_stop_boxed_211_; lean_object* v_res_212_; 
v_i_boxed_210_ = lean_unbox_usize(v_i_204_);
lean_dec(v_i_204_);
v_stop_boxed_211_ = lean_unbox_usize(v_stop_205_);
lean_dec(v_stop_205_);
v_res_212_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13_spec__25___redArg(v_as_203_, v_i_boxed_210_, v_stop_boxed_211_, v_b_206_, v___y_207_, v___y_208_);
lean_dec(v___y_208_);
lean_dec_ref(v___y_207_);
lean_dec_ref(v_as_203_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13_spec__25(lean_object* v_as_213_, size_t v_i_214_, size_t v_stop_215_, lean_object* v_b_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13_spec__25___redArg(v_as_213_, v_i_214_, v_stop_215_, v_b_216_, v___y_219_, v___y_220_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13_spec__25___boxed(lean_object* v_as_223_, lean_object* v_i_224_, lean_object* v_stop_225_, lean_object* v_b_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_){
_start:
{
size_t v_i_boxed_232_; size_t v_stop_boxed_233_; lean_object* v_res_234_; 
v_i_boxed_232_ = lean_unbox_usize(v_i_224_);
lean_dec(v_i_224_);
v_stop_boxed_233_ = lean_unbox_usize(v_stop_225_);
lean_dec(v_stop_225_);
v_res_234_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13_spec__25(v_as_223_, v_i_boxed_232_, v_stop_boxed_233_, v_b_226_, v___y_227_, v___y_228_, v___y_229_, v___y_230_);
lean_dec(v___y_230_);
lean_dec_ref(v___y_229_);
lean_dec(v___y_228_);
lean_dec_ref(v___y_227_);
lean_dec_ref(v_as_223_);
return v_res_234_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13_spec__24_spec__26___redArg___closed__0(void){
_start:
{
lean_object* v___x_235_; 
v___x_235_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_235_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13_spec__24_spec__26___redArg___closed__1(void){
_start:
{
lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_236_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13_spec__24_spec__26___redArg___closed__0, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13_spec__24_spec__26___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13_spec__24_spec__26___redArg___closed__0);
v___x_237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_237_, 0, v___x_236_);
return v___x_237_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13_spec__24_spec__26___redArg___closed__2(void){
_start:
{
lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_238_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13_spec__24_spec__26___redArg___closed__1, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13_spec__24_spec__26___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13_spec__24_spec__26___redArg___closed__1);
v___x_239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_239_, 0, v___x_238_);
lean_ctor_set(v___x_239_, 1, v___x_238_);
return v___x_239_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13_spec__24_spec__26___redArg___closed__3(void){
_start:
{
lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_240_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13_spec__24_spec__26___redArg___closed__1, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13_spec__24_spec__26___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13_spec__24_spec__26___redArg___closed__1);
v___x_241_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_241_, 0, v___x_240_);
lean_ctor_set(v___x_241_, 1, v___x_240_);
lean_ctor_set(v___x_241_, 2, v___x_240_);
lean_ctor_set(v___x_241_, 3, v___x_240_);
lean_ctor_set(v___x_241_, 4, v___x_240_);
lean_ctor_set(v___x_241_, 5, v___x_240_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13_spec__24_spec__26___redArg(lean_object* v_env_242_, lean_object* v___y_243_, lean_object* v___y_244_){
_start:
{
lean_object* v___x_246_; lean_object* v_nextMacroScope_247_; lean_object* v_ngen_248_; lean_object* v_auxDeclNGen_249_; lean_object* v_traceState_250_; lean_object* v_messages_251_; lean_object* v_infoState_252_; lean_object* v_snapshotTasks_253_; lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_279_; 
v___x_246_ = lean_st_ref_take(v___y_244_);
v_nextMacroScope_247_ = lean_ctor_get(v___x_246_, 1);
v_ngen_248_ = lean_ctor_get(v___x_246_, 2);
v_auxDeclNGen_249_ = lean_ctor_get(v___x_246_, 3);
v_traceState_250_ = lean_ctor_get(v___x_246_, 4);
v_messages_251_ = lean_ctor_get(v___x_246_, 6);
v_infoState_252_ = lean_ctor_get(v___x_246_, 7);
v_snapshotTasks_253_ = lean_ctor_get(v___x_246_, 8);
v_isSharedCheck_279_ = !lean_is_exclusive(v___x_246_);
if (v_isSharedCheck_279_ == 0)
{
lean_object* v_unused_280_; lean_object* v_unused_281_; 
v_unused_280_ = lean_ctor_get(v___x_246_, 5);
lean_dec(v_unused_280_);
v_unused_281_ = lean_ctor_get(v___x_246_, 0);
lean_dec(v_unused_281_);
v___x_255_ = v___x_246_;
v_isShared_256_ = v_isSharedCheck_279_;
goto v_resetjp_254_;
}
else
{
lean_inc(v_snapshotTasks_253_);
lean_inc(v_infoState_252_);
lean_inc(v_messages_251_);
lean_inc(v_traceState_250_);
lean_inc(v_auxDeclNGen_249_);
lean_inc(v_ngen_248_);
lean_inc(v_nextMacroScope_247_);
lean_dec(v___x_246_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_279_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
lean_object* v___x_257_; lean_object* v___x_259_; 
v___x_257_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13_spec__24_spec__26___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13_spec__24_spec__26___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13_spec__24_spec__26___redArg___closed__2);
if (v_isShared_256_ == 0)
{
lean_ctor_set(v___x_255_, 5, v___x_257_);
lean_ctor_set(v___x_255_, 0, v_env_242_);
v___x_259_ = v___x_255_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v_env_242_);
lean_ctor_set(v_reuseFailAlloc_278_, 1, v_nextMacroScope_247_);
lean_ctor_set(v_reuseFailAlloc_278_, 2, v_ngen_248_);
lean_ctor_set(v_reuseFailAlloc_278_, 3, v_auxDeclNGen_249_);
lean_ctor_set(v_reuseFailAlloc_278_, 4, v_traceState_250_);
lean_ctor_set(v_reuseFailAlloc_278_, 5, v___x_257_);
lean_ctor_set(v_reuseFailAlloc_278_, 6, v_messages_251_);
lean_ctor_set(v_reuseFailAlloc_278_, 7, v_infoState_252_);
lean_ctor_set(v_reuseFailAlloc_278_, 8, v_snapshotTasks_253_);
v___x_259_ = v_reuseFailAlloc_278_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v_mctx_262_; lean_object* v_zetaDeltaFVarIds_263_; lean_object* v_postponed_264_; lean_object* v_diag_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_276_; 
v___x_260_ = lean_st_ref_set(v___y_244_, v___x_259_);
v___x_261_ = lean_st_ref_take(v___y_243_);
v_mctx_262_ = lean_ctor_get(v___x_261_, 0);
v_zetaDeltaFVarIds_263_ = lean_ctor_get(v___x_261_, 2);
v_postponed_264_ = lean_ctor_get(v___x_261_, 3);
v_diag_265_ = lean_ctor_get(v___x_261_, 4);
v_isSharedCheck_276_ = !lean_is_exclusive(v___x_261_);
if (v_isSharedCheck_276_ == 0)
{
lean_object* v_unused_277_; 
v_unused_277_ = lean_ctor_get(v___x_261_, 1);
lean_dec(v_unused_277_);
v___x_267_ = v___x_261_;
v_isShared_268_ = v_isSharedCheck_276_;
goto v_resetjp_266_;
}
else
{
lean_inc(v_diag_265_);
lean_inc(v_postponed_264_);
lean_inc(v_zetaDeltaFVarIds_263_);
lean_inc(v_mctx_262_);
lean_dec(v___x_261_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_276_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v___x_269_; lean_object* v___x_271_; 
v___x_269_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13_spec__24_spec__26___redArg___closed__3, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13_spec__24_spec__26___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13_spec__24_spec__26___redArg___closed__3);
if (v_isShared_268_ == 0)
{
lean_ctor_set(v___x_267_, 1, v___x_269_);
v___x_271_ = v___x_267_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v_mctx_262_);
lean_ctor_set(v_reuseFailAlloc_275_, 1, v___x_269_);
lean_ctor_set(v_reuseFailAlloc_275_, 2, v_zetaDeltaFVarIds_263_);
lean_ctor_set(v_reuseFailAlloc_275_, 3, v_postponed_264_);
lean_ctor_set(v_reuseFailAlloc_275_, 4, v_diag_265_);
v___x_271_ = v_reuseFailAlloc_275_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_272_ = lean_st_ref_set(v___y_243_, v___x_271_);
v___x_273_ = lean_box(0);
v___x_274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_274_, 0, v___x_273_);
return v___x_274_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13_spec__24_spec__26___redArg___boxed(lean_object* v_env_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13_spec__24_spec__26___redArg(v_env_282_, v___y_283_, v___y_284_);
lean_dec(v___y_284_);
lean_dec(v___y_283_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13_spec__24___redArg(lean_object* v_env_287_, lean_object* v_x_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_){
_start:
{
lean_object* v___x_294_; lean_object* v_env_295_; lean_object* v_a_297_; lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_294_ = lean_st_ref_get(v___y_292_);
v_env_295_ = lean_ctor_get(v___x_294_, 0);
lean_inc_ref(v_env_295_);
lean_dec(v___x_294_);
v___x_307_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13_spec__24_spec__26___redArg(v_env_287_, v___y_290_, v___y_292_);
lean_dec_ref(v___x_307_);
lean_inc(v___y_292_);
lean_inc_ref(v___y_291_);
lean_inc(v___y_290_);
lean_inc_ref(v___y_289_);
v___x_308_ = lean_apply_5(v_x_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, lean_box(0));
if (lean_obj_tag(v___x_308_) == 0)
{
lean_object* v_a_309_; lean_object* v___x_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_317_; 
v_a_309_ = lean_ctor_get(v___x_308_, 0);
lean_inc(v_a_309_);
lean_dec_ref(v___x_308_);
v___x_310_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13_spec__24_spec__26___redArg(v_env_295_, v___y_290_, v___y_292_);
v_isSharedCheck_317_ = !lean_is_exclusive(v___x_310_);
if (v_isSharedCheck_317_ == 0)
{
lean_object* v_unused_318_; 
v_unused_318_ = lean_ctor_get(v___x_310_, 0);
lean_dec(v_unused_318_);
v___x_312_ = v___x_310_;
v_isShared_313_ = v_isSharedCheck_317_;
goto v_resetjp_311_;
}
else
{
lean_dec(v___x_310_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_317_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
lean_object* v___x_315_; 
if (v_isShared_313_ == 0)
{
lean_ctor_set(v___x_312_, 0, v_a_309_);
v___x_315_ = v___x_312_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v_a_309_);
v___x_315_ = v_reuseFailAlloc_316_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
return v___x_315_;
}
}
}
else
{
lean_object* v_a_319_; 
v_a_319_ = lean_ctor_get(v___x_308_, 0);
lean_inc(v_a_319_);
lean_dec_ref(v___x_308_);
v_a_297_ = v_a_319_;
goto v___jp_296_;
}
v___jp_296_:
{
lean_object* v___x_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_305_; 
v___x_298_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13_spec__24_spec__26___redArg(v_env_295_, v___y_290_, v___y_292_);
v_isSharedCheck_305_ = !lean_is_exclusive(v___x_298_);
if (v_isSharedCheck_305_ == 0)
{
lean_object* v_unused_306_; 
v_unused_306_ = lean_ctor_get(v___x_298_, 0);
lean_dec(v_unused_306_);
v___x_300_ = v___x_298_;
v_isShared_301_ = v_isSharedCheck_305_;
goto v_resetjp_299_;
}
else
{
lean_dec(v___x_298_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_305_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v___x_303_; 
if (v_isShared_301_ == 0)
{
lean_ctor_set_tag(v___x_300_, 1);
lean_ctor_set(v___x_300_, 0, v_a_297_);
v___x_303_ = v___x_300_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v_a_297_);
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
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13_spec__24___redArg___boxed(lean_object* v_env_320_, lean_object* v_x_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13_spec__24___redArg(v_env_320_, v_x_321_, v___y_322_, v___y_323_, v___y_324_, v___y_325_);
lean_dec(v___y_325_);
lean_dec_ref(v___y_324_);
lean_dec(v___y_323_);
lean_dec_ref(v___y_322_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13___redArg___lam__0(lean_object* v___y_328_, lean_object* v_k_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_){
_start:
{
lean_object* v___x_335_; 
lean_inc(v___y_333_);
lean_inc_ref(v___y_332_);
lean_inc(v___y_331_);
lean_inc_ref(v___y_330_);
v___x_335_ = lean_apply_5(v___y_328_, v___y_330_, v___y_331_, v___y_332_, v___y_333_, lean_box(0));
if (lean_obj_tag(v___x_335_) == 0)
{
lean_object* v___x_336_; 
lean_dec_ref(v___x_335_);
v___x_336_ = lean_apply_5(v_k_329_, v___y_330_, v___y_331_, v___y_332_, v___y_333_, lean_box(0));
return v___x_336_;
}
else
{
lean_object* v_a_337_; lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_344_; 
lean_dec(v___y_333_);
lean_dec_ref(v___y_332_);
lean_dec(v___y_331_);
lean_dec_ref(v___y_330_);
lean_dec_ref(v_k_329_);
v_a_337_ = lean_ctor_get(v___x_335_, 0);
v_isSharedCheck_344_ = !lean_is_exclusive(v___x_335_);
if (v_isSharedCheck_344_ == 0)
{
v___x_339_ = v___x_335_;
v_isShared_340_ = v_isSharedCheck_344_;
goto v_resetjp_338_;
}
else
{
lean_inc(v_a_337_);
lean_dec(v___x_335_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_344_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
lean_object* v___x_342_; 
if (v_isShared_340_ == 0)
{
v___x_342_ = v___x_339_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v_a_337_);
v___x_342_ = v_reuseFailAlloc_343_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
return v___x_342_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13___redArg___lam__0___boxed(lean_object* v___y_345_, lean_object* v_k_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13___redArg___lam__0(v___y_345_, v_k_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13___redArg(lean_object* v_preDefs_357_, lean_object* v_k_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_){
_start:
{
lean_object* v___y_365_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; uint8_t v___x_374_; 
v___x_371_ = lean_unsigned_to_nat(0u);
v___x_372_ = lean_array_get_size(v_preDefs_357_);
v___x_373_ = lean_box(0);
v___x_374_ = lean_nat_dec_lt(v___x_371_, v___x_372_);
if (v___x_374_ == 0)
{
lean_object* v___f_375_; 
lean_dec_ref(v_preDefs_357_);
v___f_375_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13___redArg___closed__0));
v___y_365_ = v___f_375_;
goto v___jp_364_;
}
else
{
uint8_t v___x_376_; 
v___x_376_ = lean_nat_dec_le(v___x_372_, v___x_372_);
if (v___x_376_ == 0)
{
if (v___x_374_ == 0)
{
lean_object* v___f_377_; 
lean_dec_ref(v_preDefs_357_);
v___f_377_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13___redArg___closed__0));
v___y_365_ = v___f_377_;
goto v___jp_364_;
}
else
{
size_t v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_378_ = lean_usize_of_nat(v___x_372_);
v___x_379_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13___redArg___boxed__const__1));
v___x_380_ = lean_box_usize(v___x_378_);
v___x_381_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13_spec__25___boxed), 9, 4);
lean_closure_set(v___x_381_, 0, v_preDefs_357_);
lean_closure_set(v___x_381_, 1, v___x_379_);
lean_closure_set(v___x_381_, 2, v___x_380_);
lean_closure_set(v___x_381_, 3, v___x_373_);
v___y_365_ = v___x_381_;
goto v___jp_364_;
}
}
else
{
size_t v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_382_ = lean_usize_of_nat(v___x_372_);
v___x_383_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13___redArg___boxed__const__1));
v___x_384_ = lean_box_usize(v___x_382_);
v___x_385_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13_spec__25___boxed), 9, 4);
lean_closure_set(v___x_385_, 0, v_preDefs_357_);
lean_closure_set(v___x_385_, 1, v___x_383_);
lean_closure_set(v___x_385_, 2, v___x_384_);
lean_closure_set(v___x_385_, 3, v___x_373_);
v___y_365_ = v___x_385_;
goto v___jp_364_;
}
}
v___jp_364_:
{
lean_object* v___x_366_; lean_object* v_env_367_; lean_object* v___f_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_366_ = lean_st_ref_get(v___y_362_);
v_env_367_ = lean_ctor_get(v___x_366_, 0);
lean_inc_ref(v_env_367_);
lean_dec(v___x_366_);
v___f_368_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_368_, 0, v___y_365_);
lean_closure_set(v___f_368_, 1, v_k_358_);
v___x_369_ = l_Lean_Environment_unlockAsync(v_env_367_);
v___x_370_ = l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13_spec__24___redArg(v___x_369_, v___f_368_, v___y_359_, v___y_360_, v___y_361_, v___y_362_);
return v___x_370_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13___redArg___boxed(lean_object* v_preDefs_386_, lean_object* v_k_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13___redArg(v_preDefs_386_, v_k_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_);
lean_dec(v___y_391_);
lean_dec_ref(v___y_390_);
lean_dec(v___y_389_);
lean_dec_ref(v___y_388_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14(lean_object* v_as_394_, size_t v_i_395_, size_t v_stop_396_, lean_object* v_b_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_){
_start:
{
uint8_t v___x_403_; 
v___x_403_ = lean_usize_dec_eq(v_i_395_, v_stop_396_);
if (v___x_403_ == 0)
{
lean_object* v___x_21134__overap_404_; lean_object* v___x_405_; 
v___x_21134__overap_404_ = lean_array_uget_borrowed(v_as_394_, v_i_395_);
lean_inc(v___x_21134__overap_404_);
lean_inc(v___y_401_);
lean_inc_ref(v___y_400_);
lean_inc(v___y_399_);
lean_inc_ref(v___y_398_);
v___x_405_ = lean_apply_5(v___x_21134__overap_404_, v___y_398_, v___y_399_, v___y_400_, v___y_401_, lean_box(0));
if (lean_obj_tag(v___x_405_) == 0)
{
lean_object* v_a_406_; size_t v___x_407_; size_t v___x_408_; 
v_a_406_ = lean_ctor_get(v___x_405_, 0);
lean_inc(v_a_406_);
lean_dec_ref(v___x_405_);
v___x_407_ = ((size_t)1ULL);
v___x_408_ = lean_usize_add(v_i_395_, v___x_407_);
v_i_395_ = v___x_408_;
v_b_397_ = v_a_406_;
goto _start;
}
else
{
return v___x_405_;
}
}
else
{
lean_object* v___x_410_; 
v___x_410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_410_, 0, v_b_397_);
return v___x_410_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___boxed(lean_object* v_as_411_, lean_object* v_i_412_, lean_object* v_stop_413_, lean_object* v_b_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_){
_start:
{
size_t v_i_boxed_420_; size_t v_stop_boxed_421_; lean_object* v_res_422_; 
v_i_boxed_420_ = lean_unbox_usize(v_i_412_);
lean_dec(v_i_412_);
v_stop_boxed_421_ = lean_unbox_usize(v_stop_413_);
lean_dec(v_stop_413_);
v_res_422_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14(v_as_411_, v_i_boxed_420_, v_stop_boxed_421_, v_b_414_, v___y_415_, v___y_416_, v___y_417_, v___y_418_);
lean_dec(v___y_418_);
lean_dec_ref(v___y_417_);
lean_dec(v___y_416_);
lean_dec_ref(v___y_415_);
lean_dec_ref(v_as_411_);
return v_res_422_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__15___redArg___closed__0(void){
_start:
{
lean_object* v___x_423_; lean_object* v_dummy_424_; 
v___x_423_ = lean_box(0);
v_dummy_424_ = l_Lean_Expr_sort___override(v___x_423_);
return v_dummy_424_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__15___redArg(uint8_t v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_recArgInfos_428_, lean_object* v___x_429_, lean_object* v_preDefs_430_, lean_object* v_a_431_, lean_object* v_as_432_, lean_object* v_i_433_, lean_object* v_j_434_, lean_object* v_bs_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_){
_start:
{
lean_object* v_zero_441_; uint8_t v_isZero_442_; 
v_zero_441_ = lean_unsigned_to_nat(0u);
v_isZero_442_ = lean_nat_dec_eq(v_i_433_, v_zero_441_);
if (v_isZero_442_ == 1)
{
lean_object* v___x_443_; 
lean_dec(v_j_434_);
lean_dec(v_i_433_);
lean_dec_ref(v_a_431_);
lean_dec_ref(v_preDefs_430_);
lean_dec_ref(v___x_429_);
lean_dec_ref(v_recArgInfos_428_);
v___x_443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_443_, 0, v_bs_435_);
return v___x_443_;
}
else
{
lean_object* v___x_444_; lean_object* v_one_445_; lean_object* v_n_446_; lean_object* v_a_448_; lean_object* v___x_452_; 
v___x_444_ = l_Lean_instInhabitedExpr;
v_one_445_ = lean_unsigned_to_nat(1u);
v_n_446_ = lean_nat_sub(v_i_433_, v_one_445_);
lean_dec(v_i_433_);
v___x_452_ = lean_array_fget_borrowed(v_as_432_, v_j_434_);
if (v_a_425_ == 0)
{
lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_453_ = lean_array_get_borrowed(v___x_444_, v_a_426_, v_j_434_);
v___x_454_ = lean_array_get_borrowed(v___x_444_, v_a_427_, v_j_434_);
lean_inc(v___x_454_);
lean_inc(v___x_453_);
lean_inc(v___x_452_);
lean_inc_ref(v___x_429_);
lean_inc_ref(v_recArgInfos_428_);
v___x_455_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnF___boxed), 10, 5);
lean_closure_set(v___x_455_, 0, v_recArgInfos_428_);
lean_closure_set(v___x_455_, 1, v___x_429_);
lean_closure_set(v___x_455_, 2, v___x_452_);
lean_closure_set(v___x_455_, 3, v___x_453_);
lean_closure_set(v___x_455_, 4, v___x_454_);
lean_inc_ref(v_preDefs_430_);
v___x_456_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13___redArg(v_preDefs_430_, v___x_455_, v___y_436_, v___y_437_, v___y_438_, v___y_439_);
if (lean_obj_tag(v___x_456_) == 0)
{
lean_object* v_a_457_; 
v_a_457_ = lean_ctor_get(v___x_456_, 0);
lean_inc(v_a_457_);
lean_dec_ref(v___x_456_);
v_a_448_ = v_a_457_;
goto v___jp_447_;
}
else
{
lean_object* v_a_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_465_; 
lean_dec(v_n_446_);
lean_dec_ref(v_bs_435_);
lean_dec(v_j_434_);
lean_dec_ref(v_a_431_);
lean_dec_ref(v_preDefs_430_);
lean_dec_ref(v___x_429_);
lean_dec_ref(v_recArgInfos_428_);
v_a_458_ = lean_ctor_get(v___x_456_, 0);
v_isSharedCheck_465_ = !lean_is_exclusive(v___x_456_);
if (v_isSharedCheck_465_ == 0)
{
v___x_460_ = v___x_456_;
v_isShared_461_ = v_isSharedCheck_465_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_a_458_);
lean_dec(v___x_456_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_465_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v___x_463_; 
if (v_isShared_461_ == 0)
{
v___x_463_ = v___x_460_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v_a_458_);
v___x_463_ = v_reuseFailAlloc_464_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
return v___x_463_;
}
}
}
}
else
{
lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v_dummy_469_; lean_object* v_nargs_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
v___x_466_ = lean_array_get_borrowed(v___x_444_, v_a_426_, v_j_434_);
v___x_467_ = lean_array_get_borrowed(v___x_444_, v_a_427_, v_j_434_);
lean_inc_ref(v_a_431_);
v___x_468_ = lean_apply_1(v_a_431_, v_zero_441_);
v_dummy_469_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__15___redArg___closed__0, &l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__15___redArg___closed__0_once, _init_l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__15___redArg___closed__0);
v_nargs_470_ = l_Lean_Expr_getAppNumArgs(v___x_468_);
lean_inc(v_nargs_470_);
v___x_471_ = lean_mk_array(v_nargs_470_, v_dummy_469_);
v___x_472_ = lean_nat_sub(v_nargs_470_, v_one_445_);
lean_dec(v_nargs_470_);
v___x_473_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___x_468_, v___x_471_, v___x_472_);
lean_inc(v___x_467_);
lean_inc(v___x_466_);
lean_inc(v___x_452_);
lean_inc_ref(v___x_429_);
lean_inc_ref(v_recArgInfos_428_);
v___x_474_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkIndPredBRecOnF___boxed), 11, 6);
lean_closure_set(v___x_474_, 0, v_recArgInfos_428_);
lean_closure_set(v___x_474_, 1, v___x_429_);
lean_closure_set(v___x_474_, 2, v___x_452_);
lean_closure_set(v___x_474_, 3, v___x_466_);
lean_closure_set(v___x_474_, 4, v___x_467_);
lean_closure_set(v___x_474_, 5, v___x_473_);
lean_inc_ref(v_preDefs_430_);
v___x_475_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13___redArg(v_preDefs_430_, v___x_474_, v___y_436_, v___y_437_, v___y_438_, v___y_439_);
if (lean_obj_tag(v___x_475_) == 0)
{
lean_object* v_a_476_; lean_object* v_fst_477_; lean_object* v_snd_478_; lean_object* v___y_480_; lean_object* v___x_489_; uint8_t v___x_490_; 
v_a_476_ = lean_ctor_get(v___x_475_, 0);
lean_inc(v_a_476_);
lean_dec_ref(v___x_475_);
v_fst_477_ = lean_ctor_get(v_a_476_, 0);
lean_inc(v_fst_477_);
v_snd_478_ = lean_ctor_get(v_a_476_, 1);
lean_inc(v_snd_478_);
lean_dec(v_a_476_);
v___x_489_ = lean_array_get_size(v_snd_478_);
v___x_490_ = lean_nat_dec_lt(v_zero_441_, v___x_489_);
if (v___x_490_ == 0)
{
lean_dec(v_snd_478_);
v_a_448_ = v_fst_477_;
goto v___jp_447_;
}
else
{
lean_object* v___x_491_; uint8_t v___x_492_; 
v___x_491_ = lean_box(0);
v___x_492_ = lean_nat_dec_le(v___x_489_, v___x_489_);
if (v___x_492_ == 0)
{
if (v___x_490_ == 0)
{
lean_dec(v_snd_478_);
v_a_448_ = v_fst_477_;
goto v___jp_447_;
}
else
{
size_t v___x_493_; size_t v___x_494_; lean_object* v___x_495_; 
v___x_493_ = ((size_t)0ULL);
v___x_494_ = lean_usize_of_nat(v___x_489_);
v___x_495_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14(v_snd_478_, v___x_493_, v___x_494_, v___x_491_, v___y_436_, v___y_437_, v___y_438_, v___y_439_);
lean_dec(v_snd_478_);
v___y_480_ = v___x_495_;
goto v___jp_479_;
}
}
else
{
size_t v___x_496_; size_t v___x_497_; lean_object* v___x_498_; 
v___x_496_ = ((size_t)0ULL);
v___x_497_ = lean_usize_of_nat(v___x_489_);
v___x_498_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14(v_snd_478_, v___x_496_, v___x_497_, v___x_491_, v___y_436_, v___y_437_, v___y_438_, v___y_439_);
lean_dec(v_snd_478_);
v___y_480_ = v___x_498_;
goto v___jp_479_;
}
}
v___jp_479_:
{
if (lean_obj_tag(v___y_480_) == 0)
{
lean_dec_ref(v___y_480_);
v_a_448_ = v_fst_477_;
goto v___jp_447_;
}
else
{
lean_object* v_a_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_488_; 
lean_dec(v_fst_477_);
lean_dec(v_n_446_);
lean_dec_ref(v_bs_435_);
lean_dec(v_j_434_);
lean_dec_ref(v_a_431_);
lean_dec_ref(v_preDefs_430_);
lean_dec_ref(v___x_429_);
lean_dec_ref(v_recArgInfos_428_);
v_a_481_ = lean_ctor_get(v___y_480_, 0);
v_isSharedCheck_488_ = !lean_is_exclusive(v___y_480_);
if (v_isSharedCheck_488_ == 0)
{
v___x_483_ = v___y_480_;
v_isShared_484_ = v_isSharedCheck_488_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_a_481_);
lean_dec(v___y_480_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_488_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v___x_486_; 
if (v_isShared_484_ == 0)
{
v___x_486_ = v___x_483_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v_a_481_);
v___x_486_ = v_reuseFailAlloc_487_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
return v___x_486_;
}
}
}
}
}
else
{
lean_object* v_a_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_506_; 
lean_dec(v_n_446_);
lean_dec_ref(v_bs_435_);
lean_dec(v_j_434_);
lean_dec_ref(v_a_431_);
lean_dec_ref(v_preDefs_430_);
lean_dec_ref(v___x_429_);
lean_dec_ref(v_recArgInfos_428_);
v_a_499_ = lean_ctor_get(v___x_475_, 0);
v_isSharedCheck_506_ = !lean_is_exclusive(v___x_475_);
if (v_isSharedCheck_506_ == 0)
{
v___x_501_ = v___x_475_;
v_isShared_502_ = v_isSharedCheck_506_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_a_499_);
lean_dec(v___x_475_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_506_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v___x_504_; 
if (v_isShared_502_ == 0)
{
v___x_504_ = v___x_501_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v_a_499_);
v___x_504_ = v_reuseFailAlloc_505_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
return v___x_504_;
}
}
}
}
v___jp_447_:
{
lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_449_ = lean_nat_add(v_j_434_, v_one_445_);
lean_dec(v_j_434_);
v___x_450_ = lean_array_push(v_bs_435_, v_a_448_);
v_i_433_ = v_n_446_;
v_j_434_ = v___x_449_;
v_bs_435_ = v___x_450_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__15___redArg___boxed(lean_object* v_a_507_, lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_recArgInfos_510_, lean_object* v___x_511_, lean_object* v_preDefs_512_, lean_object* v_a_513_, lean_object* v_as_514_, lean_object* v_i_515_, lean_object* v_j_516_, lean_object* v_bs_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_){
_start:
{
uint8_t v_a_27062__boxed_523_; lean_object* v_res_524_; 
v_a_27062__boxed_523_ = lean_unbox(v_a_507_);
v_res_524_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__15___redArg(v_a_27062__boxed_523_, v_a_508_, v_a_509_, v_recArgInfos_510_, v___x_511_, v_preDefs_512_, v_a_513_, v_as_514_, v_i_515_, v_j_516_, v_bs_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_);
lean_dec(v___y_521_);
lean_dec_ref(v___y_520_);
lean_dec(v___y_519_);
lean_dec_ref(v___y_518_);
lean_dec_ref(v_as_514_);
lean_dec_ref(v_a_509_);
lean_dec_ref(v_a_508_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17_spec__30___redArg(lean_object* v_declName_525_, uint8_t v_s_526_, lean_object* v___y_527_, lean_object* v___y_528_){
_start:
{
lean_object* v___x_530_; lean_object* v_env_531_; lean_object* v_nextMacroScope_532_; lean_object* v_ngen_533_; lean_object* v_auxDeclNGen_534_; lean_object* v_traceState_535_; lean_object* v_messages_536_; lean_object* v_infoState_537_; lean_object* v_snapshotTasks_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_567_; 
v___x_530_ = lean_st_ref_take(v___y_528_);
v_env_531_ = lean_ctor_get(v___x_530_, 0);
v_nextMacroScope_532_ = lean_ctor_get(v___x_530_, 1);
v_ngen_533_ = lean_ctor_get(v___x_530_, 2);
v_auxDeclNGen_534_ = lean_ctor_get(v___x_530_, 3);
v_traceState_535_ = lean_ctor_get(v___x_530_, 4);
v_messages_536_ = lean_ctor_get(v___x_530_, 6);
v_infoState_537_ = lean_ctor_get(v___x_530_, 7);
v_snapshotTasks_538_ = lean_ctor_get(v___x_530_, 8);
v_isSharedCheck_567_ = !lean_is_exclusive(v___x_530_);
if (v_isSharedCheck_567_ == 0)
{
lean_object* v_unused_568_; 
v_unused_568_ = lean_ctor_get(v___x_530_, 5);
lean_dec(v_unused_568_);
v___x_540_ = v___x_530_;
v_isShared_541_ = v_isSharedCheck_567_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_snapshotTasks_538_);
lean_inc(v_infoState_537_);
lean_inc(v_messages_536_);
lean_inc(v_traceState_535_);
lean_inc(v_auxDeclNGen_534_);
lean_inc(v_ngen_533_);
lean_inc(v_nextMacroScope_532_);
lean_inc(v_env_531_);
lean_dec(v___x_530_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_567_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
uint8_t v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_547_; 
v___x_542_ = 0;
v___x_543_ = lean_box(0);
v___x_544_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_531_, v_declName_525_, v_s_526_, v___x_542_, v___x_543_);
v___x_545_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13_spec__24_spec__26___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13_spec__24_spec__26___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13_spec__24_spec__26___redArg___closed__2);
if (v_isShared_541_ == 0)
{
lean_ctor_set(v___x_540_, 5, v___x_545_);
lean_ctor_set(v___x_540_, 0, v___x_544_);
v___x_547_ = v___x_540_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v___x_544_);
lean_ctor_set(v_reuseFailAlloc_566_, 1, v_nextMacroScope_532_);
lean_ctor_set(v_reuseFailAlloc_566_, 2, v_ngen_533_);
lean_ctor_set(v_reuseFailAlloc_566_, 3, v_auxDeclNGen_534_);
lean_ctor_set(v_reuseFailAlloc_566_, 4, v_traceState_535_);
lean_ctor_set(v_reuseFailAlloc_566_, 5, v___x_545_);
lean_ctor_set(v_reuseFailAlloc_566_, 6, v_messages_536_);
lean_ctor_set(v_reuseFailAlloc_566_, 7, v_infoState_537_);
lean_ctor_set(v_reuseFailAlloc_566_, 8, v_snapshotTasks_538_);
v___x_547_ = v_reuseFailAlloc_566_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v_mctx_550_; lean_object* v_zetaDeltaFVarIds_551_; lean_object* v_postponed_552_; lean_object* v_diag_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_564_; 
v___x_548_ = lean_st_ref_set(v___y_528_, v___x_547_);
v___x_549_ = lean_st_ref_take(v___y_527_);
v_mctx_550_ = lean_ctor_get(v___x_549_, 0);
v_zetaDeltaFVarIds_551_ = lean_ctor_get(v___x_549_, 2);
v_postponed_552_ = lean_ctor_get(v___x_549_, 3);
v_diag_553_ = lean_ctor_get(v___x_549_, 4);
v_isSharedCheck_564_ = !lean_is_exclusive(v___x_549_);
if (v_isSharedCheck_564_ == 0)
{
lean_object* v_unused_565_; 
v_unused_565_ = lean_ctor_get(v___x_549_, 1);
lean_dec(v_unused_565_);
v___x_555_ = v___x_549_;
v_isShared_556_ = v_isSharedCheck_564_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_diag_553_);
lean_inc(v_postponed_552_);
lean_inc(v_zetaDeltaFVarIds_551_);
lean_inc(v_mctx_550_);
lean_dec(v___x_549_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_564_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
lean_object* v___x_557_; lean_object* v___x_559_; 
v___x_557_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13_spec__24_spec__26___redArg___closed__3, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13_spec__24_spec__26___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13_spec__24_spec__26___redArg___closed__3);
if (v_isShared_556_ == 0)
{
lean_ctor_set(v___x_555_, 1, v___x_557_);
v___x_559_ = v___x_555_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v_mctx_550_);
lean_ctor_set(v_reuseFailAlloc_563_, 1, v___x_557_);
lean_ctor_set(v_reuseFailAlloc_563_, 2, v_zetaDeltaFVarIds_551_);
lean_ctor_set(v_reuseFailAlloc_563_, 3, v_postponed_552_);
lean_ctor_set(v_reuseFailAlloc_563_, 4, v_diag_553_);
v___x_559_ = v_reuseFailAlloc_563_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_560_ = lean_st_ref_set(v___y_527_, v___x_559_);
v___x_561_ = lean_box(0);
v___x_562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_562_, 0, v___x_561_);
return v___x_562_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17_spec__30___redArg___boxed(lean_object* v_declName_569_, lean_object* v_s_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_){
_start:
{
uint8_t v_s_boxed_574_; lean_object* v_res_575_; 
v_s_boxed_574_ = lean_unbox(v_s_570_);
v_res_575_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17_spec__30___redArg(v_declName_569_, v_s_boxed_574_, v___y_571_, v___y_572_);
lean_dec(v___y_572_);
lean_dec(v___y_571_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17(lean_object* v_declName_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_){
_start:
{
uint8_t v___x_582_; lean_object* v___x_583_; 
v___x_582_ = 0;
v___x_583_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17_spec__30___redArg(v_declName_576_, v___x_582_, v___y_578_, v___y_580_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___boxed(lean_object* v_declName_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_){
_start:
{
lean_object* v_res_590_; 
v_res_590_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17(v_declName_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_);
lean_dec(v___y_588_);
lean_dec_ref(v___y_587_);
lean_dec(v___y_586_);
lean_dec_ref(v___y_585_);
return v_res_590_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___redArg(lean_object* v_xs_594_, uint8_t v_a_595_, lean_object* v_preDefs_596_, lean_object* v___x_597_, lean_object* v_as_598_, lean_object* v_i_599_, lean_object* v_j_600_, lean_object* v_bs_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_){
_start:
{
lean_object* v_zero_607_; uint8_t v_isZero_608_; 
v_zero_607_ = lean_unsigned_to_nat(0u);
v_isZero_608_ = lean_nat_dec_eq(v_i_599_, v_zero_607_);
if (v_isZero_608_ == 1)
{
lean_object* v___x_609_; 
lean_dec(v_j_600_);
lean_dec(v_i_599_);
lean_dec(v___x_597_);
v___x_609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_609_, 0, v_bs_601_);
return v___x_609_;
}
else
{
uint8_t v___x_610_; lean_object* v_one_611_; lean_object* v_n_612_; lean_object* v_a_614_; lean_object* v___y_619_; lean_object* v___x_629_; uint8_t v___x_630_; lean_object* v___x_631_; 
v___x_610_ = 1;
v_one_611_ = lean_unsigned_to_nat(1u);
v_n_612_ = lean_nat_sub(v_i_599_, v_one_611_);
lean_dec(v_i_599_);
v___x_629_ = lean_array_fget_borrowed(v_as_598_, v_j_600_);
v___x_630_ = 1;
lean_inc(v___x_629_);
v___x_631_ = l_Lean_Meta_mkLambdaFVars(v_xs_594_, v___x_629_, v_a_595_, v___x_610_, v_a_595_, v___x_610_, v___x_630_, v___y_602_, v___y_603_, v___y_604_, v___y_605_);
if (lean_obj_tag(v___x_631_) == 0)
{
lean_object* v_a_632_; lean_object* v___x_633_; 
v_a_632_ = lean_ctor_get(v___x_631_, 0);
lean_inc(v_a_632_);
lean_dec_ref(v___x_631_);
v___x_633_ = l_Lean_Elab_eraseRecAppSyntaxExpr(v_a_632_, v___y_604_, v___y_605_);
if (lean_obj_tag(v___x_633_) == 0)
{
lean_object* v_a_634_; lean_object* v___x_635_; 
v_a_634_ = lean_ctor_get(v___x_633_, 0);
lean_inc(v_a_634_);
lean_dec_ref(v___x_633_);
lean_inc(v___y_605_);
lean_inc_ref(v___y_604_);
lean_inc(v___y_603_);
lean_inc_ref(v___y_602_);
lean_inc(v_a_634_);
v___x_635_ = lean_infer_type(v_a_634_, v___y_602_, v___y_603_, v___y_604_, v___y_605_);
if (lean_obj_tag(v___x_635_) == 0)
{
lean_object* v_a_636_; lean_object* v___x_637_; 
v_a_636_ = lean_ctor_get(v___x_635_, 0);
lean_inc(v_a_636_);
lean_dec_ref(v___x_635_);
v___x_637_ = l_Lean_Meta_letToHave(v_a_636_, v___y_602_, v___y_603_, v___y_604_, v___y_605_);
if (lean_obj_tag(v___x_637_) == 0)
{
lean_object* v_a_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_712_; 
v_a_638_ = lean_ctor_get(v___x_637_, 0);
v_isSharedCheck_712_ = !lean_is_exclusive(v___x_637_);
if (v_isSharedCheck_712_ == 0)
{
v___x_640_ = v___x_637_;
v_isShared_641_ = v_isSharedCheck_712_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_a_638_);
lean_dec(v___x_637_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_712_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v_modifiers_645_; lean_object* v_levelParams_646_; lean_object* v_declName_647_; lean_object* v_env_648_; uint8_t v_isUnsafe_649_; lean_object* v___x_650_; lean_object* v___x_651_; uint32_t v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; uint8_t v___y_656_; 
v___x_642_ = lean_st_ref_get(v___y_605_);
v___x_643_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_644_ = lean_array_get_borrowed(v___x_643_, v_preDefs_596_, v_j_600_);
v_modifiers_645_ = lean_ctor_get(v___x_644_, 2);
v_levelParams_646_ = lean_ctor_get(v___x_644_, 1);
v_declName_647_ = lean_ctor_get(v___x_644_, 3);
v_env_648_ = lean_ctor_get(v___x_642_, 0);
lean_inc_ref(v_env_648_);
lean_dec(v___x_642_);
v_isUnsafe_649_ = lean_ctor_get_uint8(v_modifiers_645_, sizeof(void*)*3 + 4);
v___x_650_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___redArg___closed__1));
lean_inc(v_declName_647_);
v___x_651_ = l_Lean_Name_append(v_declName_647_, v___x_650_);
lean_inc(v_a_634_);
v___x_652_ = l_Lean_getMaxHeight(v_env_648_, v_a_634_);
lean_inc(v_levelParams_646_);
lean_inc(v___x_651_);
v___x_653_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_653_, 0, v___x_651_);
lean_ctor_set(v___x_653_, 1, v_levelParams_646_);
lean_ctor_set(v___x_653_, 2, v_a_638_);
v___x_654_ = lean_box(1);
if (v_isUnsafe_649_ == 0)
{
uint8_t v___x_710_; 
v___x_710_ = 1;
v___y_656_ = v___x_710_;
goto v___jp_655_;
}
else
{
uint8_t v___x_711_; 
v___x_711_ = 0;
v___y_656_ = v___x_711_;
goto v___jp_655_;
}
v___jp_655_:
{
lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_661_; 
v___x_657_ = lean_box(0);
lean_inc(v___x_651_);
v___x_658_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_658_, 0, v___x_651_);
lean_ctor_set(v___x_658_, 1, v___x_657_);
v___x_659_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_659_, 0, v___x_653_);
lean_ctor_set(v___x_659_, 1, v_a_634_);
lean_ctor_set(v___x_659_, 2, v___x_654_);
lean_ctor_set(v___x_659_, 3, v___x_658_);
lean_ctor_set_uint8(v___x_659_, sizeof(void*)*4, v___y_656_);
if (v_isShared_641_ == 0)
{
lean_ctor_set_tag(v___x_640_, 1);
lean_ctor_set(v___x_640_, 0, v___x_659_);
v___x_661_ = v___x_640_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v___x_659_);
v___x_661_ = v_reuseFailAlloc_709_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
lean_object* v___x_662_; 
v___x_662_ = l_Lean_addDecl(v___x_661_, v_a_595_, v___y_604_, v___y_605_);
if (lean_obj_tag(v___x_662_) == 0)
{
lean_object* v___x_663_; lean_object* v_env_664_; lean_object* v_nextMacroScope_665_; lean_object* v_ngen_666_; lean_object* v_auxDeclNGen_667_; lean_object* v_traceState_668_; lean_object* v_messages_669_; lean_object* v_infoState_670_; lean_object* v_snapshotTasks_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_699_; 
lean_dec_ref(v___x_662_);
v___x_663_ = lean_st_ref_take(v___y_605_);
v_env_664_ = lean_ctor_get(v___x_663_, 0);
v_nextMacroScope_665_ = lean_ctor_get(v___x_663_, 1);
v_ngen_666_ = lean_ctor_get(v___x_663_, 2);
v_auxDeclNGen_667_ = lean_ctor_get(v___x_663_, 3);
v_traceState_668_ = lean_ctor_get(v___x_663_, 4);
v_messages_669_ = lean_ctor_get(v___x_663_, 6);
v_infoState_670_ = lean_ctor_get(v___x_663_, 7);
v_snapshotTasks_671_ = lean_ctor_get(v___x_663_, 8);
v_isSharedCheck_699_ = !lean_is_exclusive(v___x_663_);
if (v_isSharedCheck_699_ == 0)
{
lean_object* v_unused_700_; 
v_unused_700_ = lean_ctor_get(v___x_663_, 5);
lean_dec(v_unused_700_);
v___x_673_ = v___x_663_;
v_isShared_674_ = v_isSharedCheck_699_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_snapshotTasks_671_);
lean_inc(v_infoState_670_);
lean_inc(v_messages_669_);
lean_inc(v_traceState_668_);
lean_inc(v_auxDeclNGen_667_);
lean_inc(v_ngen_666_);
lean_inc(v_nextMacroScope_665_);
lean_inc(v_env_664_);
lean_dec(v___x_663_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_699_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_678_; 
lean_inc(v___x_651_);
v___x_675_ = l_Lean_setDefHeightOverride(v_env_664_, v___x_651_, v___x_652_);
v___x_676_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13_spec__24_spec__26___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13_spec__24_spec__26___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13_spec__24_spec__26___redArg___closed__2);
if (v_isShared_674_ == 0)
{
lean_ctor_set(v___x_673_, 5, v___x_676_);
lean_ctor_set(v___x_673_, 0, v___x_675_);
v___x_678_ = v___x_673_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v___x_675_);
lean_ctor_set(v_reuseFailAlloc_698_, 1, v_nextMacroScope_665_);
lean_ctor_set(v_reuseFailAlloc_698_, 2, v_ngen_666_);
lean_ctor_set(v_reuseFailAlloc_698_, 3, v_auxDeclNGen_667_);
lean_ctor_set(v_reuseFailAlloc_698_, 4, v_traceState_668_);
lean_ctor_set(v_reuseFailAlloc_698_, 5, v___x_676_);
lean_ctor_set(v_reuseFailAlloc_698_, 6, v_messages_669_);
lean_ctor_set(v_reuseFailAlloc_698_, 7, v_infoState_670_);
lean_ctor_set(v_reuseFailAlloc_698_, 8, v_snapshotTasks_671_);
v___x_678_ = v_reuseFailAlloc_698_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v_mctx_681_; lean_object* v_zetaDeltaFVarIds_682_; lean_object* v_postponed_683_; lean_object* v_diag_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_696_; 
v___x_679_ = lean_st_ref_set(v___y_605_, v___x_678_);
v___x_680_ = lean_st_ref_take(v___y_603_);
v_mctx_681_ = lean_ctor_get(v___x_680_, 0);
v_zetaDeltaFVarIds_682_ = lean_ctor_get(v___x_680_, 2);
v_postponed_683_ = lean_ctor_get(v___x_680_, 3);
v_diag_684_ = lean_ctor_get(v___x_680_, 4);
v_isSharedCheck_696_ = !lean_is_exclusive(v___x_680_);
if (v_isSharedCheck_696_ == 0)
{
lean_object* v_unused_697_; 
v_unused_697_ = lean_ctor_get(v___x_680_, 1);
lean_dec(v_unused_697_);
v___x_686_ = v___x_680_;
v_isShared_687_ = v_isSharedCheck_696_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_diag_684_);
lean_inc(v_postponed_683_);
lean_inc(v_zetaDeltaFVarIds_682_);
lean_inc(v_mctx_681_);
lean_dec(v___x_680_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_696_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_688_; lean_object* v___x_690_; 
v___x_688_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13_spec__24_spec__26___redArg___closed__3, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13_spec__24_spec__26___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13_spec__24_spec__26___redArg___closed__3);
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 1, v___x_688_);
v___x_690_ = v___x_686_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v_mctx_681_);
lean_ctor_set(v_reuseFailAlloc_695_, 1, v___x_688_);
lean_ctor_set(v_reuseFailAlloc_695_, 2, v_zetaDeltaFVarIds_682_);
lean_ctor_set(v_reuseFailAlloc_695_, 3, v_postponed_683_);
lean_ctor_set(v_reuseFailAlloc_695_, 4, v_diag_684_);
v___x_690_ = v_reuseFailAlloc_695_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_691_ = lean_st_ref_set(v___y_603_, v___x_690_);
lean_inc(v___x_651_);
v___x_692_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17(v___x_651_, v___y_602_, v___y_603_, v___y_604_, v___y_605_);
lean_dec_ref(v___x_692_);
lean_inc(v___x_597_);
v___x_693_ = l_Lean_mkConst(v___x_651_, v___x_597_);
v___x_694_ = l_Lean_mkAppN(v___x_693_, v_xs_594_);
v_a_614_ = v___x_694_;
goto v___jp_613_;
}
}
}
}
}
else
{
lean_object* v_a_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_708_; 
lean_dec(v___x_651_);
lean_dec(v_n_612_);
lean_dec_ref(v_bs_601_);
lean_dec(v_j_600_);
lean_dec(v___x_597_);
v_a_701_ = lean_ctor_get(v___x_662_, 0);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_662_);
if (v_isSharedCheck_708_ == 0)
{
v___x_703_ = v___x_662_;
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_a_701_);
lean_dec(v___x_662_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_706_; 
if (v_isShared_704_ == 0)
{
v___x_706_ = v___x_703_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_a_701_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_634_);
v___y_619_ = v___x_637_;
goto v___jp_618_;
}
}
else
{
lean_dec(v_a_634_);
v___y_619_ = v___x_635_;
goto v___jp_618_;
}
}
else
{
v___y_619_ = v___x_633_;
goto v___jp_618_;
}
}
else
{
v___y_619_ = v___x_631_;
goto v___jp_618_;
}
v___jp_613_:
{
lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_615_ = lean_nat_add(v_j_600_, v_one_611_);
lean_dec(v_j_600_);
v___x_616_ = lean_array_push(v_bs_601_, v_a_614_);
v_i_599_ = v_n_612_;
v_j_600_ = v___x_615_;
v_bs_601_ = v___x_616_;
goto _start;
}
v___jp_618_:
{
if (lean_obj_tag(v___y_619_) == 0)
{
lean_object* v_a_620_; 
v_a_620_ = lean_ctor_get(v___y_619_, 0);
lean_inc(v_a_620_);
lean_dec_ref(v___y_619_);
v_a_614_ = v_a_620_;
goto v___jp_613_;
}
else
{
lean_object* v_a_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_628_; 
lean_dec(v_n_612_);
lean_dec_ref(v_bs_601_);
lean_dec(v_j_600_);
lean_dec(v___x_597_);
v_a_621_ = lean_ctor_get(v___y_619_, 0);
v_isSharedCheck_628_ = !lean_is_exclusive(v___y_619_);
if (v_isSharedCheck_628_ == 0)
{
v___x_623_ = v___y_619_;
v_isShared_624_ = v_isSharedCheck_628_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_a_621_);
lean_dec(v___y_619_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_628_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v___x_626_; 
if (v_isShared_624_ == 0)
{
v___x_626_ = v___x_623_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v_a_621_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
return v___x_626_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___redArg___boxed(lean_object* v_xs_713_, lean_object* v_a_714_, lean_object* v_preDefs_715_, lean_object* v___x_716_, lean_object* v_as_717_, lean_object* v_i_718_, lean_object* v_j_719_, lean_object* v_bs_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_){
_start:
{
uint8_t v_a_27332__boxed_726_; lean_object* v_res_727_; 
v_a_27332__boxed_726_ = lean_unbox(v_a_714_);
v_res_727_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___redArg(v_xs_713_, v_a_27332__boxed_726_, v_preDefs_715_, v___x_716_, v_as_717_, v_i_718_, v_j_719_, v_bs_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_);
lean_dec(v___y_724_);
lean_dec_ref(v___y_723_);
lean_dec(v___y_722_);
lean_dec_ref(v___y_721_);
lean_dec_ref(v_as_717_);
lean_dec_ref(v_preDefs_715_);
lean_dec_ref(v_xs_713_);
return v_res_727_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16(lean_object* v_a_728_, lean_object* v_a_729_){
_start:
{
if (lean_obj_tag(v_a_728_) == 0)
{
lean_object* v___x_730_; 
v___x_730_ = l_List_reverse___redArg(v_a_729_);
return v___x_730_;
}
else
{
lean_object* v_head_731_; lean_object* v_tail_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_741_; 
v_head_731_ = lean_ctor_get(v_a_728_, 0);
v_tail_732_ = lean_ctor_get(v_a_728_, 1);
v_isSharedCheck_741_ = !lean_is_exclusive(v_a_728_);
if (v_isSharedCheck_741_ == 0)
{
v___x_734_ = v_a_728_;
v_isShared_735_ = v_isSharedCheck_741_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_tail_732_);
lean_inc(v_head_731_);
lean_dec(v_a_728_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_741_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
lean_object* v___x_736_; lean_object* v___x_738_; 
v___x_736_ = l_Lean_mkLevelParam(v_head_731_);
if (v_isShared_735_ == 0)
{
lean_ctor_set(v___x_734_, 1, v_a_729_);
lean_ctor_set(v___x_734_, 0, v___x_736_);
v___x_738_ = v___x_734_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v___x_736_);
lean_ctor_set(v_reuseFailAlloc_740_, 1, v_a_729_);
v___x_738_ = v_reuseFailAlloc_740_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
v_a_728_ = v_tail_732_;
v_a_729_ = v___x_738_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__15___redArg___closed__0(void){
_start:
{
lean_object* v___x_742_; 
v___x_742_ = l_instMonadEIO(lean_box(0));
return v___x_742_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__15___redArg___closed__5(void){
_start:
{
lean_object* v___x_747_; 
v___x_747_ = l_Array_instInhabited(lean_box(0));
return v___x_747_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__15___redArg(lean_object* v_msg_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_){
_start:
{
lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v_toApplicative_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_817_; 
v___x_754_ = lean_obj_once(&l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__15___redArg___closed__0, &l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__15___redArg___closed__0_once, _init_l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__15___redArg___closed__0);
v___x_755_ = l_StateRefT_x27_instMonad___redArg(v___x_754_);
v_toApplicative_756_ = lean_ctor_get(v___x_755_, 0);
v_isSharedCheck_817_ = !lean_is_exclusive(v___x_755_);
if (v_isSharedCheck_817_ == 0)
{
lean_object* v_unused_818_; 
v_unused_818_ = lean_ctor_get(v___x_755_, 1);
lean_dec(v_unused_818_);
v___x_758_ = v___x_755_;
v_isShared_759_ = v_isSharedCheck_817_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_toApplicative_756_);
lean_dec(v___x_755_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_817_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v_toFunctor_760_; lean_object* v_toSeq_761_; lean_object* v_toSeqLeft_762_; lean_object* v_toSeqRight_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_815_; 
v_toFunctor_760_ = lean_ctor_get(v_toApplicative_756_, 0);
v_toSeq_761_ = lean_ctor_get(v_toApplicative_756_, 2);
v_toSeqLeft_762_ = lean_ctor_get(v_toApplicative_756_, 3);
v_toSeqRight_763_ = lean_ctor_get(v_toApplicative_756_, 4);
v_isSharedCheck_815_ = !lean_is_exclusive(v_toApplicative_756_);
if (v_isSharedCheck_815_ == 0)
{
lean_object* v_unused_816_; 
v_unused_816_ = lean_ctor_get(v_toApplicative_756_, 1);
lean_dec(v_unused_816_);
v___x_765_ = v_toApplicative_756_;
v_isShared_766_ = v_isSharedCheck_815_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_toSeqRight_763_);
lean_inc(v_toSeqLeft_762_);
lean_inc(v_toSeq_761_);
lean_inc(v_toFunctor_760_);
lean_dec(v_toApplicative_756_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_815_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___f_767_; lean_object* v___f_768_; lean_object* v___f_769_; lean_object* v___f_770_; lean_object* v___x_771_; lean_object* v___f_772_; lean_object* v___f_773_; lean_object* v___f_774_; lean_object* v___x_776_; 
v___f_767_ = ((lean_object*)(l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__15___redArg___closed__1));
v___f_768_ = ((lean_object*)(l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__15___redArg___closed__2));
lean_inc_ref(v_toFunctor_760_);
v___f_769_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_769_, 0, v_toFunctor_760_);
v___f_770_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_770_, 0, v_toFunctor_760_);
v___x_771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_771_, 0, v___f_769_);
lean_ctor_set(v___x_771_, 1, v___f_770_);
v___f_772_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_772_, 0, v_toSeqRight_763_);
v___f_773_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_773_, 0, v_toSeqLeft_762_);
v___f_774_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_774_, 0, v_toSeq_761_);
if (v_isShared_766_ == 0)
{
lean_ctor_set(v___x_765_, 4, v___f_772_);
lean_ctor_set(v___x_765_, 3, v___f_773_);
lean_ctor_set(v___x_765_, 2, v___f_774_);
lean_ctor_set(v___x_765_, 1, v___f_767_);
lean_ctor_set(v___x_765_, 0, v___x_771_);
v___x_776_ = v___x_765_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v___x_771_);
lean_ctor_set(v_reuseFailAlloc_814_, 1, v___f_767_);
lean_ctor_set(v_reuseFailAlloc_814_, 2, v___f_774_);
lean_ctor_set(v_reuseFailAlloc_814_, 3, v___f_773_);
lean_ctor_set(v_reuseFailAlloc_814_, 4, v___f_772_);
v___x_776_ = v_reuseFailAlloc_814_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
lean_object* v___x_778_; 
if (v_isShared_759_ == 0)
{
lean_ctor_set(v___x_758_, 1, v___f_768_);
lean_ctor_set(v___x_758_, 0, v___x_776_);
v___x_778_ = v___x_758_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v___x_776_);
lean_ctor_set(v_reuseFailAlloc_813_, 1, v___f_768_);
v___x_778_ = v_reuseFailAlloc_813_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
lean_object* v___x_779_; lean_object* v_toApplicative_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_811_; 
v___x_779_ = l_StateRefT_x27_instMonad___redArg(v___x_778_);
v_toApplicative_780_ = lean_ctor_get(v___x_779_, 0);
v_isSharedCheck_811_ = !lean_is_exclusive(v___x_779_);
if (v_isSharedCheck_811_ == 0)
{
lean_object* v_unused_812_; 
v_unused_812_ = lean_ctor_get(v___x_779_, 1);
lean_dec(v_unused_812_);
v___x_782_ = v___x_779_;
v_isShared_783_ = v_isSharedCheck_811_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_toApplicative_780_);
lean_dec(v___x_779_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_811_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v_toFunctor_784_; lean_object* v_toSeq_785_; lean_object* v_toSeqLeft_786_; lean_object* v_toSeqRight_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_809_; 
v_toFunctor_784_ = lean_ctor_get(v_toApplicative_780_, 0);
v_toSeq_785_ = lean_ctor_get(v_toApplicative_780_, 2);
v_toSeqLeft_786_ = lean_ctor_get(v_toApplicative_780_, 3);
v_toSeqRight_787_ = lean_ctor_get(v_toApplicative_780_, 4);
v_isSharedCheck_809_ = !lean_is_exclusive(v_toApplicative_780_);
if (v_isSharedCheck_809_ == 0)
{
lean_object* v_unused_810_; 
v_unused_810_ = lean_ctor_get(v_toApplicative_780_, 1);
lean_dec(v_unused_810_);
v___x_789_ = v_toApplicative_780_;
v_isShared_790_ = v_isSharedCheck_809_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_toSeqRight_787_);
lean_inc(v_toSeqLeft_786_);
lean_inc(v_toSeq_785_);
lean_inc(v_toFunctor_784_);
lean_dec(v_toApplicative_780_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_809_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___f_791_; lean_object* v___f_792_; lean_object* v___f_793_; lean_object* v___f_794_; lean_object* v___x_795_; lean_object* v___f_796_; lean_object* v___f_797_; lean_object* v___f_798_; lean_object* v___x_800_; 
v___f_791_ = ((lean_object*)(l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__15___redArg___closed__3));
v___f_792_ = ((lean_object*)(l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__15___redArg___closed__4));
lean_inc_ref(v_toFunctor_784_);
v___f_793_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_793_, 0, v_toFunctor_784_);
v___f_794_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_794_, 0, v_toFunctor_784_);
v___x_795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_795_, 0, v___f_793_);
lean_ctor_set(v___x_795_, 1, v___f_794_);
v___f_796_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_796_, 0, v_toSeqRight_787_);
v___f_797_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_797_, 0, v_toSeqLeft_786_);
v___f_798_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_798_, 0, v_toSeq_785_);
if (v_isShared_790_ == 0)
{
lean_ctor_set(v___x_789_, 4, v___f_796_);
lean_ctor_set(v___x_789_, 3, v___f_797_);
lean_ctor_set(v___x_789_, 2, v___f_798_);
lean_ctor_set(v___x_789_, 1, v___f_791_);
lean_ctor_set(v___x_789_, 0, v___x_795_);
v___x_800_ = v___x_789_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v___x_795_);
lean_ctor_set(v_reuseFailAlloc_808_, 1, v___f_791_);
lean_ctor_set(v_reuseFailAlloc_808_, 2, v___f_798_);
lean_ctor_set(v_reuseFailAlloc_808_, 3, v___f_797_);
lean_ctor_set(v_reuseFailAlloc_808_, 4, v___f_796_);
v___x_800_ = v_reuseFailAlloc_808_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
lean_object* v___x_802_; 
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 1, v___f_792_);
lean_ctor_set(v___x_782_, 0, v___x_800_);
v___x_802_ = v___x_782_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v___x_800_);
lean_ctor_set(v_reuseFailAlloc_807_, 1, v___f_792_);
v___x_802_ = v_reuseFailAlloc_807_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_23207__overap_805_; lean_object* v___x_806_; 
v___x_803_ = lean_obj_once(&l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__15___redArg___closed__5, &l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__15___redArg___closed__5_once, _init_l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__15___redArg___closed__5);
v___x_804_ = l_instInhabitedOfMonad___redArg(v___x_802_, v___x_803_);
v___x_23207__overap_805_ = lean_panic_fn(v___x_804_, v_msg_748_);
lean_inc(v___y_752_);
lean_inc_ref(v___y_751_);
lean_inc(v___y_750_);
lean_inc_ref(v___y_749_);
v___x_806_ = lean_apply_5(v___x_23207__overap_805_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, lean_box(0));
return v___x_806_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__15___redArg___boxed(lean_object* v_msg_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_){
_start:
{
lean_object* v_res_825_; 
v_res_825_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__15___redArg(v_msg_819_, v___y_820_, v___y_821_, v___y_822_, v___y_823_);
lean_dec(v___y_823_);
lean_dec_ref(v___y_822_);
lean_dec(v___y_821_);
lean_dec_ref(v___y_820_);
return v_res_825_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__14___redArg(lean_object* v_inst_826_, lean_object* v_xs_827_, size_t v_sz_828_, size_t v_i_829_, lean_object* v_bs_830_){
_start:
{
uint8_t v___x_831_; 
v___x_831_ = lean_usize_dec_lt(v_i_829_, v_sz_828_);
if (v___x_831_ == 0)
{
lean_dec(v_inst_826_);
return v_bs_830_;
}
else
{
lean_object* v_v_832_; lean_object* v___x_833_; lean_object* v_bs_x27_834_; lean_object* v___x_835_; size_t v___x_836_; size_t v___x_837_; lean_object* v___x_838_; 
v_v_832_ = lean_array_uget(v_bs_830_, v_i_829_);
v___x_833_ = lean_unsigned_to_nat(0u);
v_bs_x27_834_ = lean_array_uset(v_bs_830_, v_i_829_, v___x_833_);
lean_inc(v_inst_826_);
v___x_835_ = lean_array_get_borrowed(v_inst_826_, v_xs_827_, v_v_832_);
lean_dec(v_v_832_);
v___x_836_ = ((size_t)1ULL);
v___x_837_ = lean_usize_add(v_i_829_, v___x_836_);
lean_inc(v___x_835_);
v___x_838_ = lean_array_uset(v_bs_x27_834_, v_i_829_, v___x_835_);
v_i_829_ = v___x_837_;
v_bs_830_ = v___x_838_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__14___redArg___boxed(lean_object* v_inst_840_, lean_object* v_xs_841_, lean_object* v_sz_842_, lean_object* v_i_843_, lean_object* v_bs_844_){
_start:
{
size_t v_sz_boxed_845_; size_t v_i_boxed_846_; lean_object* v_res_847_; 
v_sz_boxed_845_ = lean_unbox_usize(v_sz_842_);
lean_dec(v_sz_842_);
v_i_boxed_846_ = lean_unbox_usize(v_i_843_);
lean_dec(v_i_843_);
v_res_847_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__14___redArg(v_inst_840_, v_xs_841_, v_sz_boxed_845_, v_i_boxed_846_, v_bs_844_);
lean_dec_ref(v_xs_841_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__16___redArg(lean_object* v_inst_848_, lean_object* v_xs_849_, lean_object* v_f_850_, lean_object* v_as_851_, lean_object* v_bs_852_, lean_object* v_i_853_, lean_object* v_cs_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_){
_start:
{
lean_object* v___x_860_; uint8_t v___x_861_; 
v___x_860_ = lean_array_get_size(v_as_851_);
v___x_861_ = lean_nat_dec_lt(v_i_853_, v___x_860_);
if (v___x_861_ == 0)
{
lean_object* v___x_862_; 
lean_dec(v_i_853_);
lean_dec_ref(v_f_850_);
lean_dec(v_inst_848_);
v___x_862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_862_, 0, v_cs_854_);
return v___x_862_;
}
else
{
lean_object* v___x_863_; uint8_t v___x_864_; 
v___x_863_ = lean_array_get_size(v_bs_852_);
v___x_864_ = lean_nat_dec_lt(v_i_853_, v___x_863_);
if (v___x_864_ == 0)
{
lean_object* v___x_865_; 
lean_dec(v_i_853_);
lean_dec_ref(v_f_850_);
lean_dec(v_inst_848_);
v___x_865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_865_, 0, v_cs_854_);
return v___x_865_;
}
else
{
lean_object* v_a_866_; lean_object* v_b_867_; size_t v_sz_868_; size_t v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
v_a_866_ = lean_array_fget_borrowed(v_as_851_, v_i_853_);
v_b_867_ = lean_array_fget_borrowed(v_bs_852_, v_i_853_);
v_sz_868_ = lean_array_size(v_b_867_);
v___x_869_ = ((size_t)0ULL);
lean_inc(v_b_867_);
lean_inc(v_inst_848_);
v___x_870_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__14___redArg(v_inst_848_, v_xs_849_, v_sz_868_, v___x_869_, v_b_867_);
lean_inc_ref(v_f_850_);
lean_inc(v___y_858_);
lean_inc_ref(v___y_857_);
lean_inc(v___y_856_);
lean_inc_ref(v___y_855_);
lean_inc(v_a_866_);
v___x_871_ = lean_apply_7(v_f_850_, v_a_866_, v___x_870_, v___y_855_, v___y_856_, v___y_857_, v___y_858_, lean_box(0));
if (lean_obj_tag(v___x_871_) == 0)
{
lean_object* v_a_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; 
v_a_872_ = lean_ctor_get(v___x_871_, 0);
lean_inc(v_a_872_);
lean_dec_ref(v___x_871_);
v___x_873_ = lean_unsigned_to_nat(1u);
v___x_874_ = lean_nat_add(v_i_853_, v___x_873_);
lean_dec(v_i_853_);
v___x_875_ = lean_array_push(v_cs_854_, v_a_872_);
v_i_853_ = v___x_874_;
v_cs_854_ = v___x_875_;
goto _start;
}
else
{
lean_object* v_a_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_884_; 
lean_dec_ref(v_cs_854_);
lean_dec(v_i_853_);
lean_dec_ref(v_f_850_);
lean_dec(v_inst_848_);
v_a_877_ = lean_ctor_get(v___x_871_, 0);
v_isSharedCheck_884_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_884_ == 0)
{
v___x_879_ = v___x_871_;
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_a_877_);
lean_dec(v___x_871_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v___x_882_; 
if (v_isShared_880_ == 0)
{
v___x_882_ = v___x_879_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v_a_877_);
v___x_882_ = v_reuseFailAlloc_883_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
return v___x_882_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__16___redArg___boxed(lean_object* v_inst_885_, lean_object* v_xs_886_, lean_object* v_f_887_, lean_object* v_as_888_, lean_object* v_bs_889_, lean_object* v_i_890_, lean_object* v_cs_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_){
_start:
{
lean_object* v_res_897_; 
v_res_897_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__16___redArg(v_inst_885_, v_xs_886_, v_f_887_, v_as_888_, v_bs_889_, v_i_890_, v_cs_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_);
lean_dec(v___y_895_);
lean_dec_ref(v___y_894_);
lean_dec(v___y_893_);
lean_dec_ref(v___y_892_);
lean_dec_ref(v_bs_889_);
lean_dec_ref(v_as_888_);
lean_dec_ref(v_xs_886_);
return v_res_897_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_901_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg___closed__2));
v___x_902_ = lean_unsigned_to_nat(2u);
v___x_903_ = lean_unsigned_to_nat(73u);
v___x_904_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg___closed__1));
v___x_905_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg___closed__0));
v___x_906_ = l_mkPanicMessageWithDecl(v___x_905_, v___x_904_, v___x_903_, v___x_902_, v___x_901_);
return v___x_906_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_908_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg___closed__4));
v___x_909_ = lean_unsigned_to_nat(2u);
v___x_910_ = lean_unsigned_to_nat(74u);
v___x_911_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg___closed__1));
v___x_912_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg___closed__0));
v___x_913_ = l_mkPanicMessageWithDecl(v___x_912_, v___x_911_, v___x_910_, v___x_909_, v___x_908_);
return v___x_913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg(lean_object* v_inst_916_, lean_object* v_f_917_, lean_object* v_positions_918_, lean_object* v_ys_919_, lean_object* v_xs_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_){
_start:
{
lean_object* v___x_926_; lean_object* v___x_927_; uint8_t v___x_928_; 
v___x_926_ = lean_array_get_size(v_positions_918_);
v___x_927_ = lean_array_get_size(v_ys_919_);
v___x_928_ = lean_nat_dec_eq(v___x_926_, v___x_927_);
if (v___x_928_ == 0)
{
lean_object* v___x_929_; lean_object* v___x_930_; 
lean_dec_ref(v_f_917_);
lean_dec(v_inst_916_);
v___x_929_ = lean_obj_once(&l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg___closed__3, &l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg___closed__3_once, _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg___closed__3);
v___x_930_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__15___redArg(v___x_929_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
return v___x_930_;
}
else
{
lean_object* v___x_931_; lean_object* v___x_932_; uint8_t v___x_933_; 
v___x_931_ = l_Lean_Elab_Structural_Positions_numIndices(v_positions_918_);
v___x_932_ = lean_array_get_size(v_xs_920_);
v___x_933_ = lean_nat_dec_eq(v___x_931_, v___x_932_);
lean_dec(v___x_931_);
if (v___x_933_ == 0)
{
lean_object* v___x_934_; lean_object* v___x_935_; 
lean_dec_ref(v_f_917_);
lean_dec(v_inst_916_);
v___x_934_ = lean_obj_once(&l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg___closed__5, &l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg___closed__5_once, _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg___closed__5);
v___x_935_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__15___redArg(v___x_934_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
return v___x_935_;
}
else
{
lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
v___x_936_ = lean_unsigned_to_nat(0u);
v___x_937_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg___closed__6));
v___x_938_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__16___redArg(v_inst_916_, v_xs_920_, v_f_917_, v_ys_919_, v_positions_918_, v___x_936_, v___x_937_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
return v___x_938_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg___boxed(lean_object* v_inst_939_, lean_object* v_f_940_, lean_object* v_positions_941_, lean_object* v_ys_942_, lean_object* v_xs_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg(v_inst_939_, v_f_940_, v_positions_941_, v_ys_942_, v_xs_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_);
lean_dec(v___y_947_);
lean_dec_ref(v___y_946_);
lean_dec(v___y_945_);
lean_dec_ref(v___y_944_);
lean_dec_ref(v_xs_943_);
lean_dec_ref(v_ys_942_);
lean_dec_ref(v_positions_941_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__22(lean_object* v_msgData_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_){
_start:
{
lean_object* v___x_956_; lean_object* v_env_957_; lean_object* v___x_958_; lean_object* v_mctx_959_; lean_object* v_lctx_960_; lean_object* v_options_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_956_ = lean_st_ref_get(v___y_954_);
v_env_957_ = lean_ctor_get(v___x_956_, 0);
lean_inc_ref(v_env_957_);
lean_dec(v___x_956_);
v___x_958_ = lean_st_ref_get(v___y_952_);
v_mctx_959_ = lean_ctor_get(v___x_958_, 0);
lean_inc_ref(v_mctx_959_);
lean_dec(v___x_958_);
v_lctx_960_ = lean_ctor_get(v___y_951_, 2);
v_options_961_ = lean_ctor_get(v___y_953_, 2);
lean_inc_ref(v_options_961_);
lean_inc_ref(v_lctx_960_);
v___x_962_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_962_, 0, v_env_957_);
lean_ctor_set(v___x_962_, 1, v_mctx_959_);
lean_ctor_set(v___x_962_, 2, v_lctx_960_);
lean_ctor_set(v___x_962_, 3, v_options_961_);
v___x_963_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_963_, 0, v___x_962_);
lean_ctor_set(v___x_963_, 1, v_msgData_950_);
v___x_964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_964_, 0, v___x_963_);
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__22___boxed(lean_object* v_msgData_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_){
_start:
{
lean_object* v_res_971_; 
v_res_971_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__22(v_msgData_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_);
lean_dec(v___y_969_);
lean_dec_ref(v___y_968_);
lean_dec(v___y_967_);
lean_dec_ref(v___y_966_);
return v_res_971_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___closed__0(void){
_start:
{
lean_object* v___x_972_; double v___x_973_; 
v___x_972_ = lean_unsigned_to_nat(0u);
v___x_973_ = lean_float_of_nat(v___x_972_);
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12(lean_object* v_cls_977_, lean_object* v_msg_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_){
_start:
{
lean_object* v_ref_984_; lean_object* v___x_985_; lean_object* v_a_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_1030_; 
v_ref_984_ = lean_ctor_get(v___y_981_, 5);
v___x_985_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__22(v_msg_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_);
v_a_986_ = lean_ctor_get(v___x_985_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_985_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_988_ = v___x_985_;
v_isShared_989_ = v_isSharedCheck_1030_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_a_986_);
lean_dec(v___x_985_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_1030_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
lean_object* v___x_990_; lean_object* v_traceState_991_; lean_object* v_env_992_; lean_object* v_nextMacroScope_993_; lean_object* v_ngen_994_; lean_object* v_auxDeclNGen_995_; lean_object* v_cache_996_; lean_object* v_messages_997_; lean_object* v_infoState_998_; lean_object* v_snapshotTasks_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1029_; 
v___x_990_ = lean_st_ref_take(v___y_982_);
v_traceState_991_ = lean_ctor_get(v___x_990_, 4);
v_env_992_ = lean_ctor_get(v___x_990_, 0);
v_nextMacroScope_993_ = lean_ctor_get(v___x_990_, 1);
v_ngen_994_ = lean_ctor_get(v___x_990_, 2);
v_auxDeclNGen_995_ = lean_ctor_get(v___x_990_, 3);
v_cache_996_ = lean_ctor_get(v___x_990_, 5);
v_messages_997_ = lean_ctor_get(v___x_990_, 6);
v_infoState_998_ = lean_ctor_get(v___x_990_, 7);
v_snapshotTasks_999_ = lean_ctor_get(v___x_990_, 8);
v_isSharedCheck_1029_ = !lean_is_exclusive(v___x_990_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1001_ = v___x_990_;
v_isShared_1002_ = v_isSharedCheck_1029_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_snapshotTasks_999_);
lean_inc(v_infoState_998_);
lean_inc(v_messages_997_);
lean_inc(v_cache_996_);
lean_inc(v_traceState_991_);
lean_inc(v_auxDeclNGen_995_);
lean_inc(v_ngen_994_);
lean_inc(v_nextMacroScope_993_);
lean_inc(v_env_992_);
lean_dec(v___x_990_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1029_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
uint64_t v_tid_1003_; lean_object* v_traces_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1028_; 
v_tid_1003_ = lean_ctor_get_uint64(v_traceState_991_, sizeof(void*)*1);
v_traces_1004_ = lean_ctor_get(v_traceState_991_, 0);
v_isSharedCheck_1028_ = !lean_is_exclusive(v_traceState_991_);
if (v_isSharedCheck_1028_ == 0)
{
v___x_1006_ = v_traceState_991_;
v_isShared_1007_ = v_isSharedCheck_1028_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_traces_1004_);
lean_dec(v_traceState_991_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1028_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v___x_1008_; double v___x_1009_; uint8_t v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1018_; 
v___x_1008_ = lean_box(0);
v___x_1009_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___closed__0);
v___x_1010_ = 0;
v___x_1011_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___closed__1));
v___x_1012_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1012_, 0, v_cls_977_);
lean_ctor_set(v___x_1012_, 1, v___x_1008_);
lean_ctor_set(v___x_1012_, 2, v___x_1011_);
lean_ctor_set_float(v___x_1012_, sizeof(void*)*3, v___x_1009_);
lean_ctor_set_float(v___x_1012_, sizeof(void*)*3 + 8, v___x_1009_);
lean_ctor_set_uint8(v___x_1012_, sizeof(void*)*3 + 16, v___x_1010_);
v___x_1013_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___closed__2));
v___x_1014_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1012_);
lean_ctor_set(v___x_1014_, 1, v_a_986_);
lean_ctor_set(v___x_1014_, 2, v___x_1013_);
lean_inc(v_ref_984_);
v___x_1015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1015_, 0, v_ref_984_);
lean_ctor_set(v___x_1015_, 1, v___x_1014_);
v___x_1016_ = l_Lean_PersistentArray_push___redArg(v_traces_1004_, v___x_1015_);
if (v_isShared_1007_ == 0)
{
lean_ctor_set(v___x_1006_, 0, v___x_1016_);
v___x_1018_ = v___x_1006_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v___x_1016_);
lean_ctor_set_uint64(v_reuseFailAlloc_1027_, sizeof(void*)*1, v_tid_1003_);
v___x_1018_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
lean_object* v___x_1020_; 
if (v_isShared_1002_ == 0)
{
lean_ctor_set(v___x_1001_, 4, v___x_1018_);
v___x_1020_ = v___x_1001_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1026_; 
v_reuseFailAlloc_1026_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1026_, 0, v_env_992_);
lean_ctor_set(v_reuseFailAlloc_1026_, 1, v_nextMacroScope_993_);
lean_ctor_set(v_reuseFailAlloc_1026_, 2, v_ngen_994_);
lean_ctor_set(v_reuseFailAlloc_1026_, 3, v_auxDeclNGen_995_);
lean_ctor_set(v_reuseFailAlloc_1026_, 4, v___x_1018_);
lean_ctor_set(v_reuseFailAlloc_1026_, 5, v_cache_996_);
lean_ctor_set(v_reuseFailAlloc_1026_, 6, v_messages_997_);
lean_ctor_set(v_reuseFailAlloc_1026_, 7, v_infoState_998_);
lean_ctor_set(v_reuseFailAlloc_1026_, 8, v_snapshotTasks_999_);
v___x_1020_ = v_reuseFailAlloc_1026_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1024_; 
v___x_1021_ = lean_st_ref_set(v___y_982_, v___x_1020_);
v___x_1022_ = lean_box(0);
if (v_isShared_989_ == 0)
{
lean_ctor_set(v___x_988_, 0, v___x_1022_);
v___x_1024_ = v___x_988_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v___x_1022_);
v___x_1024_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
return v___x_1024_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___boxed(lean_object* v_cls_1031_, lean_object* v_msg_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_){
_start:
{
lean_object* v_res_1038_; 
v_res_1038_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12(v_cls_1031_, v_msg_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
return v_res_1038_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg(lean_object* v___x_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_funTypes_1042_, lean_object* v_as_1043_, lean_object* v_i_1044_, lean_object* v_j_1045_, lean_object* v_bs_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_){
_start:
{
lean_object* v_zero_1052_; uint8_t v_isZero_1053_; 
v_zero_1052_ = lean_unsigned_to_nat(0u);
v_isZero_1053_ = lean_nat_dec_eq(v_i_1044_, v_zero_1052_);
if (v_isZero_1053_ == 1)
{
lean_object* v___x_1054_; 
lean_dec(v_j_1045_);
lean_dec(v_i_1044_);
lean_dec_ref(v_funTypes_1042_);
lean_dec_ref(v_a_1041_);
lean_dec_ref(v_a_1040_);
lean_dec_ref(v___x_1039_);
v___x_1054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1054_, 0, v_bs_1046_);
return v___x_1054_;
}
else
{
lean_object* v___x_1055_; lean_object* v_fst_1056_; lean_object* v_snd_1057_; lean_object* v___x_1058_; 
v___x_1055_ = lean_array_fget_borrowed(v_as_1043_, v_j_1045_);
v_fst_1056_ = lean_ctor_get(v___x_1055_, 0);
v_snd_1057_ = lean_ctor_get(v___x_1055_, 1);
lean_inc(v_snd_1057_);
lean_inc(v_fst_1056_);
lean_inc_ref(v_funTypes_1042_);
lean_inc_ref(v_a_1041_);
lean_inc_ref(v_a_1040_);
lean_inc(v_j_1045_);
lean_inc_ref(v___x_1039_);
v___x_1058_ = l_Lean_Elab_Structural_mkBRecOnApp(v___x_1039_, v_j_1045_, v_a_1040_, v_a_1041_, v_funTypes_1042_, v_fst_1056_, v_snd_1057_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_);
if (lean_obj_tag(v___x_1058_) == 0)
{
lean_object* v_a_1059_; lean_object* v_one_1060_; lean_object* v_n_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; 
v_a_1059_ = lean_ctor_get(v___x_1058_, 0);
lean_inc(v_a_1059_);
lean_dec_ref(v___x_1058_);
v_one_1060_ = lean_unsigned_to_nat(1u);
v_n_1061_ = lean_nat_sub(v_i_1044_, v_one_1060_);
lean_dec(v_i_1044_);
v___x_1062_ = lean_nat_add(v_j_1045_, v_one_1060_);
lean_dec(v_j_1045_);
v___x_1063_ = lean_array_push(v_bs_1046_, v_a_1059_);
v_i_1044_ = v_n_1061_;
v_j_1045_ = v___x_1062_;
v_bs_1046_ = v___x_1063_;
goto _start;
}
else
{
lean_object* v_a_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1072_; 
lean_dec_ref(v_bs_1046_);
lean_dec(v_j_1045_);
lean_dec(v_i_1044_);
lean_dec_ref(v_funTypes_1042_);
lean_dec_ref(v_a_1041_);
lean_dec_ref(v_a_1040_);
lean_dec_ref(v___x_1039_);
v_a_1065_ = lean_ctor_get(v___x_1058_, 0);
v_isSharedCheck_1072_ = !lean_is_exclusive(v___x_1058_);
if (v_isSharedCheck_1072_ == 0)
{
v___x_1067_ = v___x_1058_;
v_isShared_1068_ = v_isSharedCheck_1072_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_a_1065_);
lean_dec(v___x_1058_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1072_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v___x_1070_; 
if (v_isShared_1068_ == 0)
{
v___x_1070_ = v___x_1067_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v_a_1065_);
v___x_1070_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
return v___x_1070_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___boxed(lean_object* v___x_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_funTypes_1076_, lean_object* v_as_1077_, lean_object* v_i_1078_, lean_object* v_j_1079_, lean_object* v_bs_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_){
_start:
{
lean_object* v_res_1086_; 
v_res_1086_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg(v___x_1073_, v_a_1074_, v_a_1075_, v_funTypes_1076_, v_as_1077_, v_i_1078_, v_j_1079_, v_bs_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_);
lean_dec(v___y_1084_);
lean_dec_ref(v___y_1083_);
lean_dec(v___y_1082_);
lean_dec_ref(v___y_1081_);
lean_dec_ref(v_as_1077_);
return v_res_1086_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9___redArg___lam__0(lean_object* v_fixedParamPerms_1087_, lean_object* v___x_1088_, lean_object* v_j_1089_, lean_object* v_xs_1090_, lean_object* v_snd_1091_, uint8_t v_isZero_1092_, lean_object* v_ys_1093_, lean_object* v_x_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_){
_start:
{
lean_object* v_perms_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; uint8_t v___x_1104_; uint8_t v___x_1105_; lean_object* v___x_1106_; 
v_perms_1100_ = lean_ctor_get(v_fixedParamPerms_1087_, 1);
v___x_1101_ = lean_array_get_borrowed(v___x_1088_, v_perms_1100_, v_j_1089_);
lean_inc_ref(v_ys_1093_);
lean_inc(v___x_1101_);
v___x_1102_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v___x_1101_, v_xs_1090_, v_ys_1093_);
v___x_1103_ = l_Lean_Expr_beta(v_snd_1091_, v_ys_1093_);
v___x_1104_ = 1;
v___x_1105_ = 1;
v___x_1106_ = l_Lean_Meta_mkLambdaFVars(v___x_1102_, v___x_1103_, v_isZero_1092_, v___x_1104_, v_isZero_1092_, v___x_1104_, v___x_1105_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_);
lean_dec_ref(v___x_1102_);
return v___x_1106_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9___redArg___lam__0___boxed(lean_object* v_fixedParamPerms_1107_, lean_object* v___x_1108_, lean_object* v_j_1109_, lean_object* v_xs_1110_, lean_object* v_snd_1111_, lean_object* v_isZero_1112_, lean_object* v_ys_1113_, lean_object* v_x_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_){
_start:
{
uint8_t v_isZero_boxed_1120_; lean_object* v_res_1121_; 
v_isZero_boxed_1120_ = lean_unbox(v_isZero_1112_);
v_res_1121_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9___redArg___lam__0(v_fixedParamPerms_1107_, v___x_1108_, v_j_1109_, v_xs_1110_, v_snd_1111_, v_isZero_boxed_1120_, v_ys_1113_, v_x_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_);
lean_dec(v___y_1118_);
lean_dec_ref(v___y_1117_);
lean_dec(v___y_1116_);
lean_dec_ref(v___y_1115_);
lean_dec_ref(v_x_1114_);
lean_dec_ref(v_xs_1110_);
lean_dec(v_j_1109_);
lean_dec_ref(v_fixedParamPerms_1107_);
return v_res_1121_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_1122_; 
v___x_1122_ = l_Array_instInhabited(lean_box(0));
return v___x_1122_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9___redArg(lean_object* v_fixedParamPerms_1123_, lean_object* v_xs_1124_, lean_object* v_as_1125_, lean_object* v_i_1126_, lean_object* v_j_1127_, lean_object* v_bs_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_){
_start:
{
lean_object* v_zero_1134_; uint8_t v_isZero_1135_; 
v_zero_1134_ = lean_unsigned_to_nat(0u);
v_isZero_1135_ = lean_nat_dec_eq(v_i_1126_, v_zero_1134_);
if (v_isZero_1135_ == 1)
{
lean_object* v___x_1136_; 
lean_dec(v_j_1127_);
lean_dec(v_i_1126_);
lean_dec_ref(v_xs_1124_);
lean_dec_ref(v_fixedParamPerms_1123_);
v___x_1136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1136_, 0, v_bs_1128_);
return v___x_1136_;
}
else
{
lean_object* v___x_1137_; lean_object* v_fst_1138_; lean_object* v_snd_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___f_1142_; lean_object* v___x_1143_; 
v___x_1137_ = lean_array_fget_borrowed(v_as_1125_, v_j_1127_);
v_fst_1138_ = lean_ctor_get(v___x_1137_, 0);
v_snd_1139_ = lean_ctor_get(v___x_1137_, 1);
v___x_1140_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9___redArg___closed__0, &l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9___redArg___closed__0_once, _init_l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9___redArg___closed__0);
v___x_1141_ = lean_box(v_isZero_1135_);
lean_inc(v_snd_1139_);
lean_inc_ref(v_xs_1124_);
lean_inc(v_j_1127_);
lean_inc_ref(v_fixedParamPerms_1123_);
v___f_1142_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9___redArg___lam__0___boxed), 13, 6);
lean_closure_set(v___f_1142_, 0, v_fixedParamPerms_1123_);
lean_closure_set(v___f_1142_, 1, v___x_1140_);
lean_closure_set(v___f_1142_, 2, v_j_1127_);
lean_closure_set(v___f_1142_, 3, v_xs_1124_);
lean_closure_set(v___f_1142_, 4, v_snd_1139_);
lean_closure_set(v___f_1142_, 5, v___x_1141_);
lean_inc(v_fst_1138_);
v___x_1143_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg(v_fst_1138_, v___f_1142_, v_isZero_1135_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_);
if (lean_obj_tag(v___x_1143_) == 0)
{
lean_object* v_a_1144_; lean_object* v_one_1145_; lean_object* v_n_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; 
v_a_1144_ = lean_ctor_get(v___x_1143_, 0);
lean_inc(v_a_1144_);
lean_dec_ref(v___x_1143_);
v_one_1145_ = lean_unsigned_to_nat(1u);
v_n_1146_ = lean_nat_sub(v_i_1126_, v_one_1145_);
lean_dec(v_i_1126_);
v___x_1147_ = lean_nat_add(v_j_1127_, v_one_1145_);
lean_dec(v_j_1127_);
v___x_1148_ = lean_array_push(v_bs_1128_, v_a_1144_);
v_i_1126_ = v_n_1146_;
v_j_1127_ = v___x_1147_;
v_bs_1128_ = v___x_1148_;
goto _start;
}
else
{
lean_object* v_a_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1157_; 
lean_dec_ref(v_bs_1128_);
lean_dec(v_j_1127_);
lean_dec(v_i_1126_);
lean_dec_ref(v_xs_1124_);
lean_dec_ref(v_fixedParamPerms_1123_);
v_a_1150_ = lean_ctor_get(v___x_1143_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1143_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1152_ = v___x_1143_;
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_a_1150_);
lean_dec(v___x_1143_);
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
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9___redArg___boxed(lean_object* v_fixedParamPerms_1158_, lean_object* v_xs_1159_, lean_object* v_as_1160_, lean_object* v_i_1161_, lean_object* v_j_1162_, lean_object* v_bs_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_){
_start:
{
lean_object* v_res_1169_; 
v_res_1169_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9___redArg(v_fixedParamPerms_1158_, v_xs_1159_, v_as_1160_, v_i_1161_, v_j_1162_, v_bs_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_);
lean_dec(v___y_1167_);
lean_dec_ref(v___y_1166_);
lean_dec(v___y_1165_);
lean_dec_ref(v___y_1164_);
lean_dec_ref(v_as_1160_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(lean_object* v_a_1170_, lean_object* v_a_1171_){
_start:
{
if (lean_obj_tag(v_a_1170_) == 0)
{
lean_object* v___x_1172_; 
v___x_1172_ = l_List_reverse___redArg(v_a_1171_);
return v___x_1172_;
}
else
{
lean_object* v_head_1173_; lean_object* v_tail_1174_; lean_object* v___x_1176_; uint8_t v_isShared_1177_; uint8_t v_isSharedCheck_1183_; 
v_head_1173_ = lean_ctor_get(v_a_1170_, 0);
v_tail_1174_ = lean_ctor_get(v_a_1170_, 1);
v_isSharedCheck_1183_ = !lean_is_exclusive(v_a_1170_);
if (v_isSharedCheck_1183_ == 0)
{
v___x_1176_ = v_a_1170_;
v_isShared_1177_ = v_isSharedCheck_1183_;
goto v_resetjp_1175_;
}
else
{
lean_inc(v_tail_1174_);
lean_inc(v_head_1173_);
lean_dec(v_a_1170_);
v___x_1176_ = lean_box(0);
v_isShared_1177_ = v_isSharedCheck_1183_;
goto v_resetjp_1175_;
}
v_resetjp_1175_:
{
lean_object* v___x_1178_; lean_object* v___x_1180_; 
v___x_1178_ = l_Lean_MessageData_ofExpr(v_head_1173_);
if (v_isShared_1177_ == 0)
{
lean_ctor_set(v___x_1176_, 1, v_a_1171_);
lean_ctor_set(v___x_1176_, 0, v___x_1178_);
v___x_1180_ = v___x_1176_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v___x_1178_);
lean_ctor_set(v_reuseFailAlloc_1182_, 1, v_a_1171_);
v___x_1180_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
v_a_1170_ = v_tail_1174_;
v_a_1171_ = v___x_1180_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(lean_object* v_as_1184_, lean_object* v_bs_1185_, lean_object* v_i_1186_, lean_object* v_cs_1187_){
_start:
{
lean_object* v___x_1188_; uint8_t v___x_1189_; 
v___x_1188_ = lean_array_get_size(v_as_1184_);
v___x_1189_ = lean_nat_dec_lt(v_i_1186_, v___x_1188_);
if (v___x_1189_ == 0)
{
lean_dec(v_i_1186_);
return v_cs_1187_;
}
else
{
lean_object* v___x_1190_; uint8_t v___x_1191_; 
v___x_1190_ = lean_array_get_size(v_bs_1185_);
v___x_1191_ = lean_nat_dec_lt(v_i_1186_, v___x_1190_);
if (v___x_1191_ == 0)
{
lean_dec(v_i_1186_);
return v_cs_1187_;
}
else
{
lean_object* v_a_1192_; lean_object* v_ref_1193_; uint8_t v_kind_1194_; lean_object* v_levelParams_1195_; lean_object* v_modifiers_1196_; lean_object* v_declName_1197_; lean_object* v_binders_1198_; lean_object* v_numSectionVars_1199_; lean_object* v_type_1200_; lean_object* v_termination_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1213_; 
v_a_1192_ = lean_array_fget(v_as_1184_, v_i_1186_);
v_ref_1193_ = lean_ctor_get(v_a_1192_, 0);
v_kind_1194_ = lean_ctor_get_uint8(v_a_1192_, sizeof(void*)*9);
v_levelParams_1195_ = lean_ctor_get(v_a_1192_, 1);
v_modifiers_1196_ = lean_ctor_get(v_a_1192_, 2);
v_declName_1197_ = lean_ctor_get(v_a_1192_, 3);
v_binders_1198_ = lean_ctor_get(v_a_1192_, 4);
v_numSectionVars_1199_ = lean_ctor_get(v_a_1192_, 5);
v_type_1200_ = lean_ctor_get(v_a_1192_, 6);
v_termination_1201_ = lean_ctor_get(v_a_1192_, 8);
v_isSharedCheck_1213_ = !lean_is_exclusive(v_a_1192_);
if (v_isSharedCheck_1213_ == 0)
{
lean_object* v_unused_1214_; 
v_unused_1214_ = lean_ctor_get(v_a_1192_, 7);
lean_dec(v_unused_1214_);
v___x_1203_ = v_a_1192_;
v_isShared_1204_ = v_isSharedCheck_1213_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_termination_1201_);
lean_inc(v_type_1200_);
lean_inc(v_numSectionVars_1199_);
lean_inc(v_binders_1198_);
lean_inc(v_declName_1197_);
lean_inc(v_modifiers_1196_);
lean_inc(v_levelParams_1195_);
lean_inc(v_ref_1193_);
lean_dec(v_a_1192_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1213_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v_b_1205_; lean_object* v___x_1207_; 
v_b_1205_ = lean_array_fget_borrowed(v_bs_1185_, v_i_1186_);
lean_inc(v_b_1205_);
if (v_isShared_1204_ == 0)
{
lean_ctor_set(v___x_1203_, 7, v_b_1205_);
v___x_1207_ = v___x_1203_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v_ref_1193_);
lean_ctor_set(v_reuseFailAlloc_1212_, 1, v_levelParams_1195_);
lean_ctor_set(v_reuseFailAlloc_1212_, 2, v_modifiers_1196_);
lean_ctor_set(v_reuseFailAlloc_1212_, 3, v_declName_1197_);
lean_ctor_set(v_reuseFailAlloc_1212_, 4, v_binders_1198_);
lean_ctor_set(v_reuseFailAlloc_1212_, 5, v_numSectionVars_1199_);
lean_ctor_set(v_reuseFailAlloc_1212_, 6, v_type_1200_);
lean_ctor_set(v_reuseFailAlloc_1212_, 7, v_b_1205_);
lean_ctor_set(v_reuseFailAlloc_1212_, 8, v_termination_1201_);
lean_ctor_set_uint8(v_reuseFailAlloc_1212_, sizeof(void*)*9, v_kind_1194_);
v___x_1207_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; 
v___x_1208_ = lean_unsigned_to_nat(1u);
v___x_1209_ = lean_nat_add(v_i_1186_, v___x_1208_);
lean_dec(v_i_1186_);
v___x_1210_ = lean_array_push(v_cs_1187_, v___x_1207_);
v_i_1186_ = v___x_1209_;
v_cs_1187_ = v___x_1210_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10___boxed(lean_object* v_as_1215_, lean_object* v_bs_1216_, lean_object* v_i_1217_, lean_object* v_cs_1218_){
_start:
{
lean_object* v_res_1219_; 
v_res_1219_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v_as_1215_, v_bs_1216_, v_i_1217_, v_cs_1218_);
lean_dec_ref(v_bs_1216_);
lean_dec_ref(v_as_1215_);
return v_res_1219_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___closed__2(void){
_start:
{
lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; 
v___x_1223_ = lean_box(0);
v___x_1224_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___closed__1));
v___x_1225_ = l_Lean_Expr_const___override(v___x_1224_, v___x_1223_);
return v___x_1225_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___closed__4(void){
_start:
{
lean_object* v___x_1227_; lean_object* v___x_1228_; 
v___x_1227_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___closed__3));
v___x_1228_ = l_Lean_stringToMessageData(v___x_1227_);
return v___x_1228_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___closed__6(void){
_start:
{
lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___x_1230_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___closed__5));
v___x_1231_ = l_Lean_stringToMessageData(v___x_1230_);
return v___x_1231_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___closed__8(void){
_start:
{
lean_object* v___x_1233_; lean_object* v___x_1234_; 
v___x_1233_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___closed__7));
v___x_1234_ = l_Lean_stringToMessageData(v___x_1233_);
return v___x_1234_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___closed__10(void){
_start:
{
lean_object* v___x_1236_; lean_object* v___x_1237_; 
v___x_1236_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___closed__9));
v___x_1237_ = l_Lean_stringToMessageData(v___x_1236_);
return v___x_1237_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___closed__12(void){
_start:
{
lean_object* v___x_1239_; lean_object* v___x_1240_; 
v___x_1239_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___closed__11));
v___x_1240_ = l_Lean_stringToMessageData(v___x_1239_);
return v___x_1240_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1(lean_object* v___x_1241_, lean_object* v_recArgInfos_1242_, lean_object* v_a_1243_, lean_object* v___x_1244_, lean_object* v___x_1245_, lean_object* v_fixedParamPerms_1246_, lean_object* v_xs_1247_, lean_object* v_preDefs_1248_, lean_object* v_numIndices_1249_, lean_object* v___x_1250_, lean_object* v___f_1251_, uint8_t v_a_1252_, lean_object* v_funTypes_1253_, lean_object* v_motives_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_){
_start:
{
lean_object* v___y_1261_; lean_object* v___y_1262_; lean_object* v___y_1263_; lean_object* v___y_1264_; lean_object* v___y_1265_; lean_object* v___y_1266_; lean_object* v___y_1303_; lean_object* v_FArgs_1304_; lean_object* v___y_1305_; lean_object* v___y_1306_; lean_object* v___y_1307_; lean_object* v___y_1308_; lean_object* v___y_1355_; lean_object* v___y_1356_; lean_object* v___y_1357_; lean_object* v___y_1358_; lean_object* v___y_1359_; lean_object* v___y_1360_; lean_object* v___y_1379_; lean_object* v___y_1380_; lean_object* v___y_1381_; lean_object* v___y_1382_; lean_object* v___y_1383_; lean_object* v___y_1384_; lean_object* v___y_1416_; lean_object* v___y_1417_; lean_object* v___y_1418_; lean_object* v___y_1419_; lean_object* v___x_1458_; lean_object* v_a_1459_; uint8_t v___x_1460_; 
lean_inc(v___x_1241_);
v___x_1458_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___redArg(v___x_1241_, v___y_1257_);
v_a_1459_ = lean_ctor_get(v___x_1458_, 0);
lean_inc(v_a_1459_);
lean_dec_ref(v___x_1458_);
v___x_1460_ = lean_unbox(v_a_1459_);
lean_dec(v_a_1459_);
if (v___x_1460_ == 0)
{
v___y_1416_ = v___y_1255_;
v___y_1417_ = v___y_1256_;
v___y_1418_ = v___y_1257_;
v___y_1419_ = v___y_1258_;
goto v___jp_1415_;
}
else
{
lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; 
v___x_1461_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___closed__10, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___closed__10);
lean_inc_ref(v_funTypes_1253_);
v___x_1462_ = lean_array_to_list(v_funTypes_1253_);
v___x_1463_ = lean_box(0);
v___x_1464_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_1462_, v___x_1463_);
v___x_1465_ = l_Lean_MessageData_ofList(v___x_1464_);
v___x_1466_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1466_, 0, v___x_1461_);
lean_ctor_set(v___x_1466_, 1, v___x_1465_);
v___x_1467_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___closed__12, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___closed__12_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___closed__12);
v___x_1468_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1468_, 0, v___x_1466_);
lean_ctor_set(v___x_1468_, 1, v___x_1467_);
lean_inc_ref(v_motives_1254_);
v___x_1469_ = lean_array_to_list(v_motives_1254_);
v___x_1470_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_1469_, v___x_1463_);
v___x_1471_ = l_Lean_MessageData_ofList(v___x_1470_);
v___x_1472_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1472_, 0, v___x_1468_);
lean_ctor_set(v___x_1472_, 1, v___x_1471_);
lean_inc(v___x_1241_);
v___x_1473_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12(v___x_1241_, v___x_1472_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_);
if (lean_obj_tag(v___x_1473_) == 0)
{
lean_dec_ref(v___x_1473_);
v___y_1416_ = v___y_1255_;
v___y_1417_ = v___y_1256_;
v___y_1418_ = v___y_1257_;
v___y_1419_ = v___y_1258_;
goto v___jp_1415_;
}
else
{
lean_object* v_a_1474_; lean_object* v___x_1476_; uint8_t v_isShared_1477_; uint8_t v_isSharedCheck_1481_; 
lean_dec_ref(v_motives_1254_);
lean_dec_ref(v_funTypes_1253_);
lean_dec_ref(v___f_1251_);
lean_dec_ref(v___x_1250_);
lean_dec_ref(v_preDefs_1248_);
lean_dec_ref(v_xs_1247_);
lean_dec_ref(v_fixedParamPerms_1246_);
lean_dec(v___x_1245_);
lean_dec_ref(v___x_1244_);
lean_dec_ref(v_recArgInfos_1242_);
lean_dec(v___x_1241_);
v_a_1474_ = lean_ctor_get(v___x_1473_, 0);
v_isSharedCheck_1481_ = !lean_is_exclusive(v___x_1473_);
if (v_isSharedCheck_1481_ == 0)
{
v___x_1476_ = v___x_1473_;
v_isShared_1477_ = v_isSharedCheck_1481_;
goto v_resetjp_1475_;
}
else
{
lean_inc(v_a_1474_);
lean_dec(v___x_1473_);
v___x_1476_ = lean_box(0);
v_isShared_1477_ = v_isSharedCheck_1481_;
goto v_resetjp_1475_;
}
v_resetjp_1475_:
{
lean_object* v___x_1479_; 
if (v_isShared_1477_ == 0)
{
v___x_1479_ = v___x_1476_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v_a_1474_);
v___x_1479_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
return v___x_1479_;
}
}
}
}
v___jp_1260_:
{
lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1267_ = l_Array_zip___redArg(v_recArgInfos_1242_, v_a_1243_);
lean_dec_ref(v_recArgInfos_1242_);
v___x_1268_ = lean_array_get_size(v___x_1267_);
v___x_1269_ = lean_mk_empty_array_with_capacity(v___x_1268_);
lean_inc(v___x_1245_);
v___x_1270_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg(v___x_1244_, v___y_1261_, v___y_1262_, v_funTypes_1253_, v___x_1267_, v___x_1268_, v___x_1245_, v___x_1269_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_);
lean_dec_ref(v___x_1267_);
if (lean_obj_tag(v___x_1270_) == 0)
{
lean_object* v_a_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; 
v_a_1271_ = lean_ctor_get(v___x_1270_, 0);
lean_inc(v_a_1271_);
lean_dec_ref(v___x_1270_);
v___x_1272_ = l_Array_zip___redArg(v_a_1243_, v_a_1271_);
lean_dec(v_a_1271_);
v___x_1273_ = lean_array_get_size(v___x_1272_);
v___x_1274_ = lean_mk_empty_array_with_capacity(v___x_1273_);
lean_inc(v___x_1245_);
v___x_1275_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9___redArg(v_fixedParamPerms_1246_, v_xs_1247_, v___x_1272_, v___x_1273_, v___x_1245_, v___x_1274_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_);
lean_dec_ref(v___x_1272_);
if (lean_obj_tag(v___x_1275_) == 0)
{
lean_object* v_a_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1285_; 
v_a_1276_ = lean_ctor_get(v___x_1275_, 0);
v_isSharedCheck_1285_ = !lean_is_exclusive(v___x_1275_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1278_ = v___x_1275_;
v_isShared_1279_ = v_isSharedCheck_1285_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_a_1276_);
lean_dec(v___x_1275_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1285_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1283_; 
v___x_1280_ = lean_mk_empty_array_with_capacity(v___x_1245_);
v___x_1281_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v_preDefs_1248_, v_a_1276_, v___x_1245_, v___x_1280_);
lean_dec(v_a_1276_);
lean_dec_ref(v_preDefs_1248_);
if (v_isShared_1279_ == 0)
{
lean_ctor_set(v___x_1278_, 0, v___x_1281_);
v___x_1283_ = v___x_1278_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v___x_1281_);
v___x_1283_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
return v___x_1283_;
}
}
}
else
{
lean_object* v_a_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1293_; 
lean_dec_ref(v_preDefs_1248_);
lean_dec(v___x_1245_);
v_a_1286_ = lean_ctor_get(v___x_1275_, 0);
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1275_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1288_ = v___x_1275_;
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_a_1286_);
lean_dec(v___x_1275_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v___x_1291_; 
if (v_isShared_1289_ == 0)
{
v___x_1291_ = v___x_1288_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v_a_1286_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
}
}
}
}
else
{
lean_object* v_a_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1301_; 
lean_dec_ref(v_preDefs_1248_);
lean_dec_ref(v_xs_1247_);
lean_dec_ref(v_fixedParamPerms_1246_);
lean_dec(v___x_1245_);
v_a_1294_ = lean_ctor_get(v___x_1270_, 0);
v_isSharedCheck_1301_ = !lean_is_exclusive(v___x_1270_);
if (v_isSharedCheck_1301_ == 0)
{
v___x_1296_ = v___x_1270_;
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_a_1294_);
lean_dec(v___x_1270_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v___x_1299_; 
if (v_isShared_1297_ == 0)
{
v___x_1299_ = v___x_1296_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v_a_1294_);
v___x_1299_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
return v___x_1299_;
}
}
}
}
v___jp_1302_:
{
lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; 
lean_inc_ref(v___y_1303_);
lean_inc(v___x_1245_);
v___x_1309_ = lean_apply_1(v___y_1303_, v___x_1245_);
v___x_1310_ = lean_unsigned_to_nat(1u);
v___x_1311_ = lean_nat_add(v_numIndices_1249_, v___x_1310_);
v___x_1312_ = lean_box(0);
v___x_1313_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___closed__2);
v___x_1314_ = lean_mk_array(v___x_1311_, v___x_1313_);
v___x_1315_ = l_Lean_mkAppN(v___x_1309_, v___x_1314_);
lean_dec_ref(v___x_1314_);
v___x_1316_ = lean_array_get_size(v___x_1244_);
v___x_1317_ = l_Lean_Meta_inferArgumentTypesN(v___x_1316_, v___x_1315_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_);
if (lean_obj_tag(v___x_1317_) == 0)
{
lean_object* v_a_1318_; lean_object* v___x_1319_; 
v_a_1318_ = lean_ctor_get(v___x_1317_, 0);
lean_inc(v_a_1318_);
lean_dec_ref(v___x_1317_);
v___x_1319_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg(v___x_1250_, v___f_1251_, v___x_1244_, v_a_1318_, v_FArgs_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_);
lean_dec_ref(v_FArgs_1304_);
lean_dec(v_a_1318_);
if (lean_obj_tag(v___x_1319_) == 0)
{
lean_object* v_a_1320_; lean_object* v___x_1321_; lean_object* v_a_1322_; uint8_t v___x_1323_; 
v_a_1320_ = lean_ctor_get(v___x_1319_, 0);
lean_inc(v_a_1320_);
lean_dec_ref(v___x_1319_);
lean_inc(v___x_1241_);
v___x_1321_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___redArg(v___x_1241_, v___y_1307_);
v_a_1322_ = lean_ctor_get(v___x_1321_, 0);
lean_inc(v_a_1322_);
lean_dec_ref(v___x_1321_);
v___x_1323_ = lean_unbox(v_a_1322_);
lean_dec(v_a_1322_);
if (v___x_1323_ == 0)
{
lean_dec(v___x_1241_);
v___y_1261_ = v___y_1303_;
v___y_1262_ = v_a_1320_;
v___y_1263_ = v___y_1305_;
v___y_1264_ = v___y_1306_;
v___y_1265_ = v___y_1307_;
v___y_1266_ = v___y_1308_;
goto v___jp_1260_;
}
else
{
lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; 
v___x_1324_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___closed__4);
lean_inc(v_a_1320_);
v___x_1325_ = lean_array_to_list(v_a_1320_);
v___x_1326_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_1325_, v___x_1312_);
v___x_1327_ = l_Lean_MessageData_ofList(v___x_1326_);
v___x_1328_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1328_, 0, v___x_1324_);
lean_ctor_set(v___x_1328_, 1, v___x_1327_);
v___x_1329_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12(v___x_1241_, v___x_1328_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_);
if (lean_obj_tag(v___x_1329_) == 0)
{
lean_dec_ref(v___x_1329_);
v___y_1261_ = v___y_1303_;
v___y_1262_ = v_a_1320_;
v___y_1263_ = v___y_1305_;
v___y_1264_ = v___y_1306_;
v___y_1265_ = v___y_1307_;
v___y_1266_ = v___y_1308_;
goto v___jp_1260_;
}
else
{
lean_object* v_a_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1337_; 
lean_dec(v_a_1320_);
lean_dec_ref(v___y_1303_);
lean_dec_ref(v_funTypes_1253_);
lean_dec_ref(v_preDefs_1248_);
lean_dec_ref(v_xs_1247_);
lean_dec_ref(v_fixedParamPerms_1246_);
lean_dec(v___x_1245_);
lean_dec_ref(v___x_1244_);
lean_dec_ref(v_recArgInfos_1242_);
v_a_1330_ = lean_ctor_get(v___x_1329_, 0);
v_isSharedCheck_1337_ = !lean_is_exclusive(v___x_1329_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1332_ = v___x_1329_;
v_isShared_1333_ = v_isSharedCheck_1337_;
goto v_resetjp_1331_;
}
else
{
lean_inc(v_a_1330_);
lean_dec(v___x_1329_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1337_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
lean_object* v___x_1335_; 
if (v_isShared_1333_ == 0)
{
v___x_1335_ = v___x_1332_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v_a_1330_);
v___x_1335_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
return v___x_1335_;
}
}
}
}
}
else
{
lean_object* v_a_1338_; lean_object* v___x_1340_; uint8_t v_isShared_1341_; uint8_t v_isSharedCheck_1345_; 
lean_dec_ref(v___y_1303_);
lean_dec_ref(v_funTypes_1253_);
lean_dec_ref(v_preDefs_1248_);
lean_dec_ref(v_xs_1247_);
lean_dec_ref(v_fixedParamPerms_1246_);
lean_dec(v___x_1245_);
lean_dec_ref(v___x_1244_);
lean_dec_ref(v_recArgInfos_1242_);
lean_dec(v___x_1241_);
v_a_1338_ = lean_ctor_get(v___x_1319_, 0);
v_isSharedCheck_1345_ = !lean_is_exclusive(v___x_1319_);
if (v_isSharedCheck_1345_ == 0)
{
v___x_1340_ = v___x_1319_;
v_isShared_1341_ = v_isSharedCheck_1345_;
goto v_resetjp_1339_;
}
else
{
lean_inc(v_a_1338_);
lean_dec(v___x_1319_);
v___x_1340_ = lean_box(0);
v_isShared_1341_ = v_isSharedCheck_1345_;
goto v_resetjp_1339_;
}
v_resetjp_1339_:
{
lean_object* v___x_1343_; 
if (v_isShared_1341_ == 0)
{
v___x_1343_ = v___x_1340_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v_a_1338_);
v___x_1343_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
return v___x_1343_;
}
}
}
}
else
{
lean_object* v_a_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1353_; 
lean_dec_ref(v_FArgs_1304_);
lean_dec_ref(v___y_1303_);
lean_dec_ref(v_funTypes_1253_);
lean_dec_ref(v___f_1251_);
lean_dec_ref(v___x_1250_);
lean_dec_ref(v_preDefs_1248_);
lean_dec_ref(v_xs_1247_);
lean_dec_ref(v_fixedParamPerms_1246_);
lean_dec(v___x_1245_);
lean_dec_ref(v___x_1244_);
lean_dec_ref(v_recArgInfos_1242_);
lean_dec(v___x_1241_);
v_a_1346_ = lean_ctor_get(v___x_1317_, 0);
v_isSharedCheck_1353_ = !lean_is_exclusive(v___x_1317_);
if (v_isSharedCheck_1353_ == 0)
{
v___x_1348_ = v___x_1317_;
v_isShared_1349_ = v_isSharedCheck_1353_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_a_1346_);
lean_dec(v___x_1317_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1353_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v___x_1351_; 
if (v_isShared_1349_ == 0)
{
v___x_1351_ = v___x_1348_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v_a_1346_);
v___x_1351_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
return v___x_1351_;
}
}
}
}
v___jp_1354_:
{
if (v_a_1252_ == 0)
{
lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v_levelParams_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; 
v___x_1361_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_1362_ = lean_array_get_borrowed(v___x_1361_, v_preDefs_1248_, v___x_1245_);
v_levelParams_1363_ = lean_ctor_get(v___x_1362_, 1);
v___x_1364_ = lean_box(0);
lean_inc(v_levelParams_1363_);
v___x_1365_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16(v_levelParams_1363_, v___x_1364_);
v___x_1366_ = lean_array_get_size(v___y_1356_);
v___x_1367_ = lean_mk_empty_array_with_capacity(v___x_1366_);
lean_inc(v___x_1245_);
v___x_1368_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___redArg(v_xs_1247_, v_a_1252_, v_preDefs_1248_, v___x_1365_, v___y_1356_, v___x_1366_, v___x_1245_, v___x_1367_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_);
lean_dec_ref(v___y_1356_);
if (lean_obj_tag(v___x_1368_) == 0)
{
lean_object* v_a_1369_; 
v_a_1369_ = lean_ctor_get(v___x_1368_, 0);
lean_inc(v_a_1369_);
lean_dec_ref(v___x_1368_);
v___y_1303_ = v___y_1355_;
v_FArgs_1304_ = v_a_1369_;
v___y_1305_ = v___y_1357_;
v___y_1306_ = v___y_1358_;
v___y_1307_ = v___y_1359_;
v___y_1308_ = v___y_1360_;
goto v___jp_1302_;
}
else
{
lean_object* v_a_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1377_; 
lean_dec_ref(v___y_1355_);
lean_dec_ref(v_funTypes_1253_);
lean_dec_ref(v___f_1251_);
lean_dec_ref(v___x_1250_);
lean_dec_ref(v_preDefs_1248_);
lean_dec_ref(v_xs_1247_);
lean_dec_ref(v_fixedParamPerms_1246_);
lean_dec(v___x_1245_);
lean_dec_ref(v___x_1244_);
lean_dec_ref(v_recArgInfos_1242_);
lean_dec(v___x_1241_);
v_a_1370_ = lean_ctor_get(v___x_1368_, 0);
v_isSharedCheck_1377_ = !lean_is_exclusive(v___x_1368_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1372_ = v___x_1368_;
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_a_1370_);
lean_dec(v___x_1368_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1375_; 
if (v_isShared_1373_ == 0)
{
v___x_1375_ = v___x_1372_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v_a_1370_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
}
}
else
{
v___y_1303_ = v___y_1355_;
v_FArgs_1304_ = v___y_1356_;
v___y_1305_ = v___y_1357_;
v___y_1306_ = v___y_1358_;
v___y_1307_ = v___y_1359_;
v___y_1308_ = v___y_1360_;
goto v___jp_1302_;
}
}
v___jp_1378_:
{
lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; 
v___x_1385_ = lean_array_get_size(v_recArgInfos_1242_);
v___x_1386_ = lean_mk_empty_array_with_capacity(v___x_1385_);
lean_inc(v___x_1245_);
lean_inc_ref(v___y_1379_);
lean_inc_ref(v_preDefs_1248_);
lean_inc_ref(v___x_1244_);
lean_inc_ref(v_recArgInfos_1242_);
v___x_1387_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__15___redArg(v_a_1252_, v_a_1243_, v___y_1380_, v_recArgInfos_1242_, v___x_1244_, v_preDefs_1248_, v___y_1379_, v_recArgInfos_1242_, v___x_1385_, v___x_1245_, v___x_1386_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_);
lean_dec_ref(v___y_1380_);
if (lean_obj_tag(v___x_1387_) == 0)
{
lean_object* v_a_1388_; lean_object* v___x_1389_; lean_object* v_a_1390_; uint8_t v___x_1391_; 
v_a_1388_ = lean_ctor_get(v___x_1387_, 0);
lean_inc(v_a_1388_);
lean_dec_ref(v___x_1387_);
lean_inc(v___x_1241_);
v___x_1389_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___redArg(v___x_1241_, v___y_1383_);
v_a_1390_ = lean_ctor_get(v___x_1389_, 0);
lean_inc(v_a_1390_);
lean_dec_ref(v___x_1389_);
v___x_1391_ = lean_unbox(v_a_1390_);
lean_dec(v_a_1390_);
if (v___x_1391_ == 0)
{
v___y_1355_ = v___y_1379_;
v___y_1356_ = v_a_1388_;
v___y_1357_ = v___y_1381_;
v___y_1358_ = v___y_1382_;
v___y_1359_ = v___y_1383_;
v___y_1360_ = v___y_1384_;
goto v___jp_1354_;
}
else
{
lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; 
v___x_1392_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___closed__6, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___closed__6);
lean_inc(v_a_1388_);
v___x_1393_ = lean_array_to_list(v_a_1388_);
v___x_1394_ = lean_box(0);
v___x_1395_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_1393_, v___x_1394_);
v___x_1396_ = l_Lean_MessageData_ofList(v___x_1395_);
v___x_1397_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1397_, 0, v___x_1392_);
lean_ctor_set(v___x_1397_, 1, v___x_1396_);
lean_inc(v___x_1241_);
v___x_1398_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12(v___x_1241_, v___x_1397_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_);
if (lean_obj_tag(v___x_1398_) == 0)
{
lean_dec_ref(v___x_1398_);
v___y_1355_ = v___y_1379_;
v___y_1356_ = v_a_1388_;
v___y_1357_ = v___y_1381_;
v___y_1358_ = v___y_1382_;
v___y_1359_ = v___y_1383_;
v___y_1360_ = v___y_1384_;
goto v___jp_1354_;
}
else
{
lean_object* v_a_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1406_; 
lean_dec(v_a_1388_);
lean_dec_ref(v___y_1379_);
lean_dec_ref(v_funTypes_1253_);
lean_dec_ref(v___f_1251_);
lean_dec_ref(v___x_1250_);
lean_dec_ref(v_preDefs_1248_);
lean_dec_ref(v_xs_1247_);
lean_dec_ref(v_fixedParamPerms_1246_);
lean_dec(v___x_1245_);
lean_dec_ref(v___x_1244_);
lean_dec_ref(v_recArgInfos_1242_);
lean_dec(v___x_1241_);
v_a_1399_ = lean_ctor_get(v___x_1398_, 0);
v_isSharedCheck_1406_ = !lean_is_exclusive(v___x_1398_);
if (v_isSharedCheck_1406_ == 0)
{
v___x_1401_ = v___x_1398_;
v_isShared_1402_ = v_isSharedCheck_1406_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_a_1399_);
lean_dec(v___x_1398_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1406_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
lean_object* v___x_1404_; 
if (v_isShared_1402_ == 0)
{
v___x_1404_ = v___x_1401_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v_a_1399_);
v___x_1404_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
return v___x_1404_;
}
}
}
}
}
else
{
lean_object* v_a_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1414_; 
lean_dec_ref(v___y_1379_);
lean_dec_ref(v_funTypes_1253_);
lean_dec_ref(v___f_1251_);
lean_dec_ref(v___x_1250_);
lean_dec_ref(v_preDefs_1248_);
lean_dec_ref(v_xs_1247_);
lean_dec_ref(v_fixedParamPerms_1246_);
lean_dec(v___x_1245_);
lean_dec_ref(v___x_1244_);
lean_dec_ref(v_recArgInfos_1242_);
lean_dec(v___x_1241_);
v_a_1407_ = lean_ctor_get(v___x_1387_, 0);
v_isSharedCheck_1414_ = !lean_is_exclusive(v___x_1387_);
if (v_isSharedCheck_1414_ == 0)
{
v___x_1409_ = v___x_1387_;
v_isShared_1410_ = v_isSharedCheck_1414_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_a_1407_);
lean_dec(v___x_1387_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1414_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v___x_1412_; 
if (v_isShared_1410_ == 0)
{
v___x_1412_ = v___x_1409_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v_a_1407_);
v___x_1412_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
return v___x_1412_;
}
}
}
}
v___jp_1415_:
{
lean_object* v___x_1420_; 
v___x_1420_ = l_Lean_Elab_Structural_mkBRecOnConst(v_recArgInfos_1242_, v___x_1244_, v_motives_1254_, v_a_1252_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_);
lean_dec_ref(v_motives_1254_);
if (lean_obj_tag(v___x_1420_) == 0)
{
lean_object* v_a_1421_; lean_object* v___x_1422_; 
v_a_1421_ = lean_ctor_get(v___x_1420_, 0);
lean_inc(v_a_1421_);
lean_dec_ref(v___x_1420_);
lean_inc(v_a_1421_);
lean_inc_ref(v___x_1244_);
v___x_1422_ = l_Lean_Elab_Structural_inferBRecOnFTypes(v_recArgInfos_1242_, v___x_1244_, v_a_1421_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_);
if (lean_obj_tag(v___x_1422_) == 0)
{
lean_object* v_a_1423_; lean_object* v___x_1424_; lean_object* v_a_1425_; uint8_t v___x_1426_; 
v_a_1423_ = lean_ctor_get(v___x_1422_, 0);
lean_inc(v_a_1423_);
lean_dec_ref(v___x_1422_);
lean_inc(v___x_1241_);
v___x_1424_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___redArg(v___x_1241_, v___y_1418_);
v_a_1425_ = lean_ctor_get(v___x_1424_, 0);
lean_inc(v_a_1425_);
lean_dec_ref(v___x_1424_);
v___x_1426_ = lean_unbox(v_a_1425_);
lean_dec(v_a_1425_);
if (v___x_1426_ == 0)
{
v___y_1379_ = v_a_1421_;
v___y_1380_ = v_a_1423_;
v___y_1381_ = v___y_1416_;
v___y_1382_ = v___y_1417_;
v___y_1383_ = v___y_1418_;
v___y_1384_ = v___y_1419_;
goto v___jp_1378_;
}
else
{
lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; 
v___x_1427_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___closed__8);
lean_inc(v_a_1423_);
v___x_1428_ = lean_array_to_list(v_a_1423_);
v___x_1429_ = lean_box(0);
v___x_1430_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_1428_, v___x_1429_);
v___x_1431_ = l_Lean_MessageData_ofList(v___x_1430_);
v___x_1432_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1432_, 0, v___x_1427_);
lean_ctor_set(v___x_1432_, 1, v___x_1431_);
lean_inc(v___x_1241_);
v___x_1433_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12(v___x_1241_, v___x_1432_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_);
if (lean_obj_tag(v___x_1433_) == 0)
{
lean_dec_ref(v___x_1433_);
v___y_1379_ = v_a_1421_;
v___y_1380_ = v_a_1423_;
v___y_1381_ = v___y_1416_;
v___y_1382_ = v___y_1417_;
v___y_1383_ = v___y_1418_;
v___y_1384_ = v___y_1419_;
goto v___jp_1378_;
}
else
{
lean_object* v_a_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1441_; 
lean_dec(v_a_1423_);
lean_dec(v_a_1421_);
lean_dec_ref(v_funTypes_1253_);
lean_dec_ref(v___f_1251_);
lean_dec_ref(v___x_1250_);
lean_dec_ref(v_preDefs_1248_);
lean_dec_ref(v_xs_1247_);
lean_dec_ref(v_fixedParamPerms_1246_);
lean_dec(v___x_1245_);
lean_dec_ref(v___x_1244_);
lean_dec_ref(v_recArgInfos_1242_);
lean_dec(v___x_1241_);
v_a_1434_ = lean_ctor_get(v___x_1433_, 0);
v_isSharedCheck_1441_ = !lean_is_exclusive(v___x_1433_);
if (v_isSharedCheck_1441_ == 0)
{
v___x_1436_ = v___x_1433_;
v_isShared_1437_ = v_isSharedCheck_1441_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_a_1434_);
lean_dec(v___x_1433_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1441_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
lean_object* v___x_1439_; 
if (v_isShared_1437_ == 0)
{
v___x_1439_ = v___x_1436_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v_a_1434_);
v___x_1439_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
return v___x_1439_;
}
}
}
}
}
else
{
lean_object* v_a_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1449_; 
lean_dec(v_a_1421_);
lean_dec_ref(v_funTypes_1253_);
lean_dec_ref(v___f_1251_);
lean_dec_ref(v___x_1250_);
lean_dec_ref(v_preDefs_1248_);
lean_dec_ref(v_xs_1247_);
lean_dec_ref(v_fixedParamPerms_1246_);
lean_dec(v___x_1245_);
lean_dec_ref(v___x_1244_);
lean_dec_ref(v_recArgInfos_1242_);
lean_dec(v___x_1241_);
v_a_1442_ = lean_ctor_get(v___x_1422_, 0);
v_isSharedCheck_1449_ = !lean_is_exclusive(v___x_1422_);
if (v_isSharedCheck_1449_ == 0)
{
v___x_1444_ = v___x_1422_;
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_a_1442_);
lean_dec(v___x_1422_);
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
lean_dec_ref(v_funTypes_1253_);
lean_dec_ref(v___f_1251_);
lean_dec_ref(v___x_1250_);
lean_dec_ref(v_preDefs_1248_);
lean_dec_ref(v_xs_1247_);
lean_dec_ref(v_fixedParamPerms_1246_);
lean_dec(v___x_1245_);
lean_dec_ref(v___x_1244_);
lean_dec_ref(v_recArgInfos_1242_);
lean_dec(v___x_1241_);
v_a_1450_ = lean_ctor_get(v___x_1420_, 0);
v_isSharedCheck_1457_ = !lean_is_exclusive(v___x_1420_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1452_ = v___x_1420_;
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_a_1450_);
lean_dec(v___x_1420_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___boxed(lean_object** _args){
lean_object* v___x_1482_ = _args[0];
lean_object* v_recArgInfos_1483_ = _args[1];
lean_object* v_a_1484_ = _args[2];
lean_object* v___x_1485_ = _args[3];
lean_object* v___x_1486_ = _args[4];
lean_object* v_fixedParamPerms_1487_ = _args[5];
lean_object* v_xs_1488_ = _args[6];
lean_object* v_preDefs_1489_ = _args[7];
lean_object* v_numIndices_1490_ = _args[8];
lean_object* v___x_1491_ = _args[9];
lean_object* v___f_1492_ = _args[10];
lean_object* v_a_1493_ = _args[11];
lean_object* v_funTypes_1494_ = _args[12];
lean_object* v_motives_1495_ = _args[13];
lean_object* v___y_1496_ = _args[14];
lean_object* v___y_1497_ = _args[15];
lean_object* v___y_1498_ = _args[16];
lean_object* v___y_1499_ = _args[17];
lean_object* v___y_1500_ = _args[18];
_start:
{
uint8_t v_a_28273__boxed_1501_; lean_object* v_res_1502_; 
v_a_28273__boxed_1501_ = lean_unbox(v_a_1493_);
v_res_1502_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1(v___x_1482_, v_recArgInfos_1483_, v_a_1484_, v___x_1485_, v___x_1486_, v_fixedParamPerms_1487_, v_xs_1488_, v_preDefs_1489_, v_numIndices_1490_, v___x_1491_, v___f_1492_, v_a_28273__boxed_1501_, v_funTypes_1494_, v_motives_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_);
lean_dec(v___y_1499_);
lean_dec_ref(v___y_1498_);
lean_dec(v___y_1497_);
lean_dec_ref(v___y_1496_);
lean_dec(v_numIndices_1490_);
lean_dec_ref(v_a_1484_);
return v_res_1502_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___redArg(lean_object* v_a_1503_, lean_object* v_funTypes_1504_, lean_object* v_as_1505_, lean_object* v_i_1506_, lean_object* v_j_1507_, lean_object* v_bs_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_){
_start:
{
lean_object* v_zero_1514_; uint8_t v_isZero_1515_; 
v_zero_1514_ = lean_unsigned_to_nat(0u);
v_isZero_1515_ = lean_nat_dec_eq(v_i_1506_, v_zero_1514_);
if (v_isZero_1515_ == 1)
{
lean_object* v___x_1516_; 
lean_dec(v_j_1507_);
lean_dec(v_i_1506_);
v___x_1516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1516_, 0, v_bs_1508_);
return v___x_1516_;
}
else
{
lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; 
v___x_1517_ = l_Lean_instInhabitedExpr;
v___x_1518_ = lean_array_fget_borrowed(v_as_1505_, v_j_1507_);
v___x_1519_ = lean_array_get_borrowed(v___x_1517_, v_a_1503_, v_j_1507_);
v___x_1520_ = lean_array_get_borrowed(v___x_1517_, v_funTypes_1504_, v_j_1507_);
lean_inc(v___x_1520_);
lean_inc(v___x_1519_);
lean_inc(v___x_1518_);
v___x_1521_ = l_Lean_Elab_Structural_mkIndPredBRecOnMotive(v___x_1518_, v___x_1519_, v___x_1520_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_);
if (lean_obj_tag(v___x_1521_) == 0)
{
lean_object* v_a_1522_; lean_object* v_one_1523_; lean_object* v_n_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; 
v_a_1522_ = lean_ctor_get(v___x_1521_, 0);
lean_inc(v_a_1522_);
lean_dec_ref(v___x_1521_);
v_one_1523_ = lean_unsigned_to_nat(1u);
v_n_1524_ = lean_nat_sub(v_i_1506_, v_one_1523_);
lean_dec(v_i_1506_);
v___x_1525_ = lean_nat_add(v_j_1507_, v_one_1523_);
lean_dec(v_j_1507_);
v___x_1526_ = lean_array_push(v_bs_1508_, v_a_1522_);
v_i_1506_ = v_n_1524_;
v_j_1507_ = v___x_1525_;
v_bs_1508_ = v___x_1526_;
goto _start;
}
else
{
lean_object* v_a_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1535_; 
lean_dec_ref(v_bs_1508_);
lean_dec(v_j_1507_);
lean_dec(v_i_1506_);
v_a_1528_ = lean_ctor_get(v___x_1521_, 0);
v_isSharedCheck_1535_ = !lean_is_exclusive(v___x_1521_);
if (v_isSharedCheck_1535_ == 0)
{
v___x_1530_ = v___x_1521_;
v_isShared_1531_ = v_isSharedCheck_1535_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_a_1528_);
lean_dec(v___x_1521_);
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
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___redArg___boxed(lean_object* v_a_1536_, lean_object* v_funTypes_1537_, lean_object* v_as_1538_, lean_object* v_i_1539_, lean_object* v_j_1540_, lean_object* v_bs_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_){
_start:
{
lean_object* v_res_1547_; 
v_res_1547_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___redArg(v_a_1536_, v_funTypes_1537_, v_as_1538_, v_i_1539_, v_j_1540_, v_bs_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_);
lean_dec(v___y_1545_);
lean_dec_ref(v___y_1544_);
lean_dec(v___y_1543_);
lean_dec_ref(v___y_1542_);
lean_dec_ref(v_as_1538_);
lean_dec_ref(v_funTypes_1537_);
lean_dec_ref(v_a_1536_);
return v_res_1547_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2(lean_object* v_recArgInfos_1548_, lean_object* v_a_1549_, lean_object* v___x_1550_, lean_object* v___f_1551_, lean_object* v_funTypes_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_){
_start:
{
lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; 
v___x_1558_ = lean_array_get_size(v_recArgInfos_1548_);
v___x_1559_ = lean_mk_empty_array_with_capacity(v___x_1558_);
v___x_1560_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___redArg(v_a_1549_, v_funTypes_1552_, v_recArgInfos_1548_, v___x_1558_, v___x_1550_, v___x_1559_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_);
if (lean_obj_tag(v___x_1560_) == 0)
{
lean_object* v_a_1561_; lean_object* v___x_1562_; 
v_a_1561_ = lean_ctor_get(v___x_1560_, 0);
lean_inc(v_a_1561_);
lean_dec_ref(v___x_1560_);
lean_inc(v___y_1556_);
lean_inc_ref(v___y_1555_);
lean_inc(v___y_1554_);
lean_inc_ref(v___y_1553_);
v___x_1562_ = lean_apply_7(v___f_1551_, v_funTypes_1552_, v_a_1561_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_, lean_box(0));
return v___x_1562_;
}
else
{
lean_object* v_a_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1570_; 
lean_dec_ref(v_funTypes_1552_);
lean_dec_ref(v___f_1551_);
v_a_1563_ = lean_ctor_get(v___x_1560_, 0);
v_isSharedCheck_1570_ = !lean_is_exclusive(v___x_1560_);
if (v_isSharedCheck_1570_ == 0)
{
v___x_1565_ = v___x_1560_;
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_a_1563_);
lean_dec(v___x_1560_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
lean_object* v___x_1568_; 
if (v_isShared_1566_ == 0)
{
v___x_1568_ = v___x_1565_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v_a_1563_);
v___x_1568_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
return v___x_1568_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___boxed(lean_object* v_recArgInfos_1571_, lean_object* v_a_1572_, lean_object* v___x_1573_, lean_object* v___f_1574_, lean_object* v_funTypes_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_){
_start:
{
lean_object* v_res_1581_; 
v_res_1581_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2(v_recArgInfos_1571_, v_a_1572_, v___x_1573_, v___f_1574_, v_funTypes_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_);
lean_dec(v___y_1579_);
lean_dec_ref(v___y_1578_);
lean_dec(v___y_1577_);
lean_dec_ref(v___y_1576_);
lean_dec_ref(v_a_1572_);
lean_dec_ref(v_recArgInfos_1571_);
return v_res_1581_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__0(lean_object* v_a_1582_, lean_object* v_a_1583_){
_start:
{
if (lean_obj_tag(v_a_1582_) == 0)
{
lean_object* v___x_1584_; 
v___x_1584_ = l_List_reverse___redArg(v_a_1583_);
return v___x_1584_;
}
else
{
lean_object* v_head_1585_; lean_object* v_tail_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1597_; 
v_head_1585_ = lean_ctor_get(v_a_1582_, 0);
v_tail_1586_ = lean_ctor_get(v_a_1582_, 1);
v_isSharedCheck_1597_ = !lean_is_exclusive(v_a_1582_);
if (v_isSharedCheck_1597_ == 0)
{
v___x_1588_ = v_a_1582_;
v_isShared_1589_ = v_isSharedCheck_1597_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_tail_1586_);
lean_inc(v_head_1585_);
lean_dec(v_a_1582_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1597_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1594_; 
v___x_1590_ = l_Nat_reprFast(v_head_1585_);
v___x_1591_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1591_, 0, v___x_1590_);
v___x_1592_ = l_Lean_MessageData_ofFormat(v___x_1591_);
if (v_isShared_1589_ == 0)
{
lean_ctor_set(v___x_1588_, 1, v_a_1583_);
lean_ctor_set(v___x_1588_, 0, v___x_1592_);
v___x_1594_ = v___x_1588_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v___x_1592_);
lean_ctor_set(v_reuseFailAlloc_1596_, 1, v_a_1583_);
v___x_1594_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
v_a_1582_ = v_tail_1586_;
v_a_1583_ = v___x_1594_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__21(lean_object* v_a_1598_, lean_object* v_a_1599_){
_start:
{
if (lean_obj_tag(v_a_1598_) == 0)
{
lean_object* v___x_1600_; 
v___x_1600_ = l_List_reverse___redArg(v_a_1599_);
return v___x_1600_;
}
else
{
lean_object* v_head_1601_; lean_object* v_tail_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1614_; 
v_head_1601_ = lean_ctor_get(v_a_1598_, 0);
v_tail_1602_ = lean_ctor_get(v_a_1598_, 1);
v_isSharedCheck_1614_ = !lean_is_exclusive(v_a_1598_);
if (v_isSharedCheck_1614_ == 0)
{
v___x_1604_ = v_a_1598_;
v_isShared_1605_ = v_isSharedCheck_1614_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_tail_1602_);
lean_inc(v_head_1601_);
lean_dec(v_a_1598_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1614_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1611_; 
v___x_1606_ = lean_array_to_list(v_head_1601_);
v___x_1607_ = lean_box(0);
v___x_1608_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__0(v___x_1606_, v___x_1607_);
v___x_1609_ = l_Lean_MessageData_ofList(v___x_1608_);
if (v_isShared_1605_ == 0)
{
lean_ctor_set(v___x_1604_, 1, v_a_1599_);
lean_ctor_set(v___x_1604_, 0, v___x_1609_);
v___x_1611_ = v___x_1604_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v___x_1609_);
lean_ctor_set(v_reuseFailAlloc_1613_, 1, v_a_1599_);
v___x_1611_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
v_a_1598_ = v_tail_1602_;
v_a_1599_ = v___x_1611_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg(lean_object* v_msg_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_){
_start:
{
lean_object* v_ref_1621_; lean_object* v___x_1622_; lean_object* v_a_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1631_; 
v_ref_1621_ = lean_ctor_get(v___y_1618_, 5);
v___x_1622_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__22(v_msg_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_);
v_a_1623_ = lean_ctor_get(v___x_1622_, 0);
v_isSharedCheck_1631_ = !lean_is_exclusive(v___x_1622_);
if (v_isSharedCheck_1631_ == 0)
{
v___x_1625_ = v___x_1622_;
v_isShared_1626_ = v_isSharedCheck_1631_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_a_1623_);
lean_dec(v___x_1622_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1631_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v___x_1627_; lean_object* v___x_1629_; 
lean_inc(v_ref_1621_);
v___x_1627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1627_, 0, v_ref_1621_);
lean_ctor_set(v___x_1627_, 1, v_a_1623_);
if (v_isShared_1626_ == 0)
{
lean_ctor_set_tag(v___x_1625_, 1);
lean_ctor_set(v___x_1625_, 0, v___x_1627_);
v___x_1629_ = v___x_1625_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v___x_1627_);
v___x_1629_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
return v___x_1629_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg___boxed(lean_object* v_msg_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_){
_start:
{
lean_object* v_res_1638_; 
v_res_1638_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg(v_msg_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
lean_dec(v___y_1636_);
lean_dec_ref(v___y_1635_);
lean_dec(v___y_1634_);
lean_dec_ref(v___y_1633_);
return v_res_1638_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1640_; lean_object* v___x_1641_; 
v___x_1640_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__0));
v___x_1641_ = l_Lean_stringToMessageData(v___x_1640_);
return v___x_1641_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__3(void){
_start:
{
lean_object* v___x_1643_; lean_object* v___x_1644_; 
v___x_1643_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__2));
v___x_1644_ = l_Lean_stringToMessageData(v___x_1643_);
return v___x_1644_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4(lean_object* v_constName_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_){
_start:
{
lean_object* v___x_1651_; lean_object* v_env_1652_; lean_object* v___x_1653_; 
v___x_1651_ = lean_st_ref_get(v___y_1649_);
v_env_1652_ = lean_ctor_get(v___x_1651_, 0);
lean_inc_ref(v_env_1652_);
lean_dec(v___x_1651_);
lean_inc(v_constName_1645_);
v___x_1653_ = l_Lean_isInductiveCore_x3f(v_env_1652_, v_constName_1645_);
if (lean_obj_tag(v___x_1653_) == 0)
{
lean_object* v___x_1654_; uint8_t v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; 
v___x_1654_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__1, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__1);
v___x_1655_ = 0;
v___x_1656_ = l_Lean_MessageData_ofConstName(v_constName_1645_, v___x_1655_);
v___x_1657_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1657_, 0, v___x_1654_);
lean_ctor_set(v___x_1657_, 1, v___x_1656_);
v___x_1658_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__3, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__3_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__3);
v___x_1659_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1659_, 0, v___x_1657_);
lean_ctor_set(v___x_1659_, 1, v___x_1658_);
v___x_1660_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg(v___x_1659_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_);
return v___x_1660_;
}
else
{
lean_object* v_val_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1668_; 
lean_dec(v_constName_1645_);
v_val_1661_ = lean_ctor_get(v___x_1653_, 0);
v_isSharedCheck_1668_ = !lean_is_exclusive(v___x_1653_);
if (v_isSharedCheck_1668_ == 0)
{
v___x_1663_ = v___x_1653_;
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_val_1661_);
lean_dec(v___x_1653_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v___x_1666_; 
if (v_isShared_1664_ == 0)
{
lean_ctor_set_tag(v___x_1663_, 0);
v___x_1666_ = v___x_1663_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v_val_1661_);
v___x_1666_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
return v___x_1666_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___boxed(lean_object* v_constName_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_){
_start:
{
lean_object* v_res_1675_; 
v_res_1675_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4(v_constName_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_);
lean_dec(v___y_1673_);
lean_dec_ref(v___y_1672_);
lean_dec(v___y_1671_);
lean_dec_ref(v___y_1670_);
return v_res_1675_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__20___redArg(lean_object* v_a_1676_, lean_object* v_a_1677_, lean_object* v_as_1678_, lean_object* v_i_1679_, lean_object* v_j_1680_, lean_object* v_bs_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_){
_start:
{
lean_object* v_zero_1687_; uint8_t v_isZero_1688_; 
v_zero_1687_ = lean_unsigned_to_nat(0u);
v_isZero_1688_ = lean_nat_dec_eq(v_i_1679_, v_zero_1687_);
if (v_isZero_1688_ == 1)
{
lean_object* v___x_1689_; 
lean_dec(v_j_1680_);
lean_dec(v_i_1679_);
v___x_1689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1689_, 0, v_bs_1681_);
return v___x_1689_;
}
else
{
lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; 
v___x_1690_ = l_Lean_instInhabitedExpr;
v___x_1691_ = lean_array_fget_borrowed(v_as_1678_, v_j_1680_);
v___x_1692_ = lean_array_get_borrowed(v___x_1690_, v_a_1676_, v_j_1680_);
v___x_1693_ = lean_array_get_borrowed(v___x_1690_, v_a_1677_, v_j_1680_);
lean_inc(v___x_1693_);
lean_inc(v___x_1692_);
lean_inc(v___x_1691_);
v___x_1694_ = l_Lean_Elab_Structural_mkBRecOnMotive(v___x_1691_, v___x_1692_, v___x_1693_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_);
if (lean_obj_tag(v___x_1694_) == 0)
{
lean_object* v_a_1695_; lean_object* v_one_1696_; lean_object* v_n_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; 
v_a_1695_ = lean_ctor_get(v___x_1694_, 0);
lean_inc(v_a_1695_);
lean_dec_ref(v___x_1694_);
v_one_1696_ = lean_unsigned_to_nat(1u);
v_n_1697_ = lean_nat_sub(v_i_1679_, v_one_1696_);
lean_dec(v_i_1679_);
v___x_1698_ = lean_nat_add(v_j_1680_, v_one_1696_);
lean_dec(v_j_1680_);
v___x_1699_ = lean_array_push(v_bs_1681_, v_a_1695_);
v_i_1679_ = v_n_1697_;
v_j_1680_ = v___x_1698_;
v_bs_1681_ = v___x_1699_;
goto _start;
}
else
{
lean_object* v_a_1701_; lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1708_; 
lean_dec_ref(v_bs_1681_);
lean_dec(v_j_1680_);
lean_dec(v_i_1679_);
v_a_1701_ = lean_ctor_get(v___x_1694_, 0);
v_isSharedCheck_1708_ = !lean_is_exclusive(v___x_1694_);
if (v_isSharedCheck_1708_ == 0)
{
v___x_1703_ = v___x_1694_;
v_isShared_1704_ = v_isSharedCheck_1708_;
goto v_resetjp_1702_;
}
else
{
lean_inc(v_a_1701_);
lean_dec(v___x_1694_);
v___x_1703_ = lean_box(0);
v_isShared_1704_ = v_isSharedCheck_1708_;
goto v_resetjp_1702_;
}
v_resetjp_1702_:
{
lean_object* v___x_1706_; 
if (v_isShared_1704_ == 0)
{
v___x_1706_ = v___x_1703_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v_a_1701_);
v___x_1706_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
return v___x_1706_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__20___redArg___boxed(lean_object* v_a_1709_, lean_object* v_a_1710_, lean_object* v_as_1711_, lean_object* v_i_1712_, lean_object* v_j_1713_, lean_object* v_bs_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_){
_start:
{
lean_object* v_res_1720_; 
v_res_1720_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__20___redArg(v_a_1709_, v_a_1710_, v_as_1711_, v_i_1712_, v_j_1713_, v_bs_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_);
lean_dec(v___y_1718_);
lean_dec_ref(v___y_1717_);
lean_dec(v___y_1716_);
lean_dec_ref(v___y_1715_);
lean_dec_ref(v_as_1711_);
lean_dec_ref(v_a_1710_);
lean_dec_ref(v_a_1709_);
return v_res_1720_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__7___redArg(lean_object* v_inst_1721_, lean_object* v_xs_1722_, lean_object* v_f_1723_, lean_object* v_x_1724_, lean_object* v_as_1725_, size_t v_i_1726_, size_t v_stop_1727_, lean_object* v_b_1728_){
_start:
{
lean_object* v___y_1730_; uint8_t v___x_1734_; 
v___x_1734_ = lean_usize_dec_eq(v_i_1726_, v_stop_1727_);
if (v___x_1734_ == 0)
{
lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; uint8_t v___x_1738_; 
v___x_1735_ = lean_array_uget_borrowed(v_as_1725_, v_i_1726_);
lean_inc(v_inst_1721_);
v___x_1736_ = lean_array_get_borrowed(v_inst_1721_, v_xs_1722_, v___x_1735_);
lean_inc_ref(v_f_1723_);
lean_inc(v___x_1736_);
v___x_1737_ = lean_apply_1(v_f_1723_, v___x_1736_);
v___x_1738_ = lean_nat_dec_eq(v___x_1737_, v_x_1724_);
lean_dec(v___x_1737_);
if (v___x_1738_ == 0)
{
v___y_1730_ = v_b_1728_;
goto v___jp_1729_;
}
else
{
lean_object* v___x_1739_; 
lean_inc(v___x_1735_);
v___x_1739_ = lean_array_push(v_b_1728_, v___x_1735_);
v___y_1730_ = v___x_1739_;
goto v___jp_1729_;
}
}
else
{
lean_dec_ref(v_f_1723_);
lean_dec(v_inst_1721_);
return v_b_1728_;
}
v___jp_1729_:
{
size_t v___x_1731_; size_t v___x_1732_; 
v___x_1731_ = ((size_t)1ULL);
v___x_1732_ = lean_usize_add(v_i_1726_, v___x_1731_);
v_i_1726_ = v___x_1732_;
v_b_1728_ = v___y_1730_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__7___redArg___boxed(lean_object* v_inst_1740_, lean_object* v_xs_1741_, lean_object* v_f_1742_, lean_object* v_x_1743_, lean_object* v_as_1744_, lean_object* v_i_1745_, lean_object* v_stop_1746_, lean_object* v_b_1747_){
_start:
{
size_t v_i_boxed_1748_; size_t v_stop_boxed_1749_; lean_object* v_res_1750_; 
v_i_boxed_1748_ = lean_unbox_usize(v_i_1745_);
lean_dec(v_i_1745_);
v_stop_boxed_1749_ = lean_unbox_usize(v_stop_1746_);
lean_dec(v_stop_1746_);
v_res_1750_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__7___redArg(v_inst_1740_, v_xs_1741_, v_f_1742_, v_x_1743_, v_as_1744_, v_i_boxed_1748_, v_stop_boxed_1749_, v_b_1747_);
lean_dec_ref(v_as_1744_);
lean_dec(v_x_1743_);
lean_dec_ref(v_xs_1741_);
return v_res_1750_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__9_spec__10___redArg(lean_object* v_xs_1753_, lean_object* v_inst_1754_, lean_object* v_f_1755_, size_t v_sz_1756_, size_t v_i_1757_, lean_object* v_bs_1758_){
_start:
{
uint8_t v___x_1759_; 
v___x_1759_ = lean_usize_dec_lt(v_i_1757_, v_sz_1756_);
if (v___x_1759_ == 0)
{
lean_dec_ref(v_f_1755_);
lean_dec(v_inst_1754_);
return v_bs_1758_;
}
else
{
lean_object* v_v_1760_; lean_object* v___x_1761_; lean_object* v_bs_x27_1762_; lean_object* v___y_1764_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; uint8_t v___x_1773_; 
v_v_1760_ = lean_array_uget(v_bs_1758_, v_i_1757_);
v___x_1761_ = lean_unsigned_to_nat(0u);
v_bs_x27_1762_ = lean_array_uset(v_bs_1758_, v_i_1757_, v___x_1761_);
v___x_1769_ = lean_array_get_size(v_xs_1753_);
v___x_1770_ = l_Array_range(v___x_1769_);
v___x_1771_ = lean_array_get_size(v___x_1770_);
v___x_1772_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__9_spec__10___redArg___closed__0));
v___x_1773_ = lean_nat_dec_lt(v___x_1761_, v___x_1771_);
if (v___x_1773_ == 0)
{
lean_dec_ref(v___x_1770_);
lean_dec(v_v_1760_);
v___y_1764_ = v___x_1772_;
goto v___jp_1763_;
}
else
{
uint8_t v___x_1774_; 
v___x_1774_ = lean_nat_dec_le(v___x_1771_, v___x_1771_);
if (v___x_1774_ == 0)
{
if (v___x_1773_ == 0)
{
lean_dec_ref(v___x_1770_);
lean_dec(v_v_1760_);
v___y_1764_ = v___x_1772_;
goto v___jp_1763_;
}
else
{
size_t v___x_1775_; size_t v___x_1776_; lean_object* v___x_1777_; 
v___x_1775_ = ((size_t)0ULL);
v___x_1776_ = lean_usize_of_nat(v___x_1771_);
lean_inc_ref(v_f_1755_);
lean_inc(v_inst_1754_);
v___x_1777_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__7___redArg(v_inst_1754_, v_xs_1753_, v_f_1755_, v_v_1760_, v___x_1770_, v___x_1775_, v___x_1776_, v___x_1772_);
lean_dec_ref(v___x_1770_);
lean_dec(v_v_1760_);
v___y_1764_ = v___x_1777_;
goto v___jp_1763_;
}
}
else
{
size_t v___x_1778_; size_t v___x_1779_; lean_object* v___x_1780_; 
v___x_1778_ = ((size_t)0ULL);
v___x_1779_ = lean_usize_of_nat(v___x_1771_);
lean_inc_ref(v_f_1755_);
lean_inc(v_inst_1754_);
v___x_1780_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__7___redArg(v_inst_1754_, v_xs_1753_, v_f_1755_, v_v_1760_, v___x_1770_, v___x_1778_, v___x_1779_, v___x_1772_);
lean_dec_ref(v___x_1770_);
lean_dec(v_v_1760_);
v___y_1764_ = v___x_1780_;
goto v___jp_1763_;
}
}
v___jp_1763_:
{
size_t v___x_1765_; size_t v___x_1766_; lean_object* v___x_1767_; 
v___x_1765_ = ((size_t)1ULL);
v___x_1766_ = lean_usize_add(v_i_1757_, v___x_1765_);
v___x_1767_ = lean_array_uset(v_bs_x27_1762_, v_i_1757_, v___y_1764_);
v_i_1757_ = v___x_1766_;
v_bs_1758_ = v___x_1767_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__9_spec__10___redArg___boxed(lean_object* v_xs_1781_, lean_object* v_inst_1782_, lean_object* v_f_1783_, lean_object* v_sz_1784_, lean_object* v_i_1785_, lean_object* v_bs_1786_){
_start:
{
size_t v_sz_boxed_1787_; size_t v_i_boxed_1788_; lean_object* v_res_1789_; 
v_sz_boxed_1787_ = lean_unbox_usize(v_sz_1784_);
lean_dec(v_sz_1784_);
v_i_boxed_1788_ = lean_unbox_usize(v_i_1785_);
lean_dec(v_i_1785_);
v_res_1789_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__9_spec__10___redArg(v_xs_1781_, v_inst_1782_, v_f_1783_, v_sz_boxed_1787_, v_i_boxed_1788_, v_bs_1786_);
lean_dec_ref(v_xs_1781_);
return v_res_1789_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__9___redArg(lean_object* v_inst_1790_, lean_object* v_xs_1791_, lean_object* v_f_1792_, size_t v_sz_1793_, size_t v_i_1794_, lean_object* v_bs_1795_){
_start:
{
uint8_t v___x_1796_; 
v___x_1796_ = lean_usize_dec_lt(v_i_1794_, v_sz_1793_);
if (v___x_1796_ == 0)
{
lean_dec_ref(v_f_1792_);
lean_dec(v_inst_1790_);
return v_bs_1795_;
}
else
{
lean_object* v_v_1797_; lean_object* v___x_1798_; lean_object* v_bs_x27_1799_; lean_object* v___y_1801_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; uint8_t v___x_1810_; 
v_v_1797_ = lean_array_uget(v_bs_1795_, v_i_1794_);
v___x_1798_ = lean_unsigned_to_nat(0u);
v_bs_x27_1799_ = lean_array_uset(v_bs_1795_, v_i_1794_, v___x_1798_);
v___x_1806_ = lean_array_get_size(v_xs_1791_);
v___x_1807_ = l_Array_range(v___x_1806_);
v___x_1808_ = lean_array_get_size(v___x_1807_);
v___x_1809_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__9_spec__10___redArg___closed__0));
v___x_1810_ = lean_nat_dec_lt(v___x_1798_, v___x_1808_);
if (v___x_1810_ == 0)
{
lean_dec_ref(v___x_1807_);
lean_dec(v_v_1797_);
v___y_1801_ = v___x_1809_;
goto v___jp_1800_;
}
else
{
uint8_t v___x_1811_; 
v___x_1811_ = lean_nat_dec_le(v___x_1808_, v___x_1808_);
if (v___x_1811_ == 0)
{
if (v___x_1810_ == 0)
{
lean_dec_ref(v___x_1807_);
lean_dec(v_v_1797_);
v___y_1801_ = v___x_1809_;
goto v___jp_1800_;
}
else
{
size_t v___x_1812_; size_t v___x_1813_; lean_object* v___x_1814_; 
v___x_1812_ = ((size_t)0ULL);
v___x_1813_ = lean_usize_of_nat(v___x_1808_);
lean_inc_ref(v_f_1792_);
lean_inc(v_inst_1790_);
v___x_1814_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__7___redArg(v_inst_1790_, v_xs_1791_, v_f_1792_, v_v_1797_, v___x_1807_, v___x_1812_, v___x_1813_, v___x_1809_);
lean_dec_ref(v___x_1807_);
lean_dec(v_v_1797_);
v___y_1801_ = v___x_1814_;
goto v___jp_1800_;
}
}
else
{
size_t v___x_1815_; size_t v___x_1816_; lean_object* v___x_1817_; 
v___x_1815_ = ((size_t)0ULL);
v___x_1816_ = lean_usize_of_nat(v___x_1808_);
lean_inc_ref(v_f_1792_);
lean_inc(v_inst_1790_);
v___x_1817_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__7___redArg(v_inst_1790_, v_xs_1791_, v_f_1792_, v_v_1797_, v___x_1807_, v___x_1815_, v___x_1816_, v___x_1809_);
lean_dec_ref(v___x_1807_);
lean_dec(v_v_1797_);
v___y_1801_ = v___x_1817_;
goto v___jp_1800_;
}
}
v___jp_1800_:
{
size_t v___x_1802_; size_t v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; 
v___x_1802_ = ((size_t)1ULL);
v___x_1803_ = lean_usize_add(v_i_1794_, v___x_1802_);
v___x_1804_ = lean_array_uset(v_bs_x27_1799_, v_i_1794_, v___y_1801_);
v___x_1805_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__9_spec__10___redArg(v_xs_1791_, v_inst_1790_, v_f_1792_, v_sz_1793_, v___x_1803_, v___x_1804_);
return v___x_1805_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__9___redArg___boxed(lean_object* v_inst_1818_, lean_object* v_xs_1819_, lean_object* v_f_1820_, lean_object* v_sz_1821_, lean_object* v_i_1822_, lean_object* v_bs_1823_){
_start:
{
size_t v_sz_boxed_1824_; size_t v_i_boxed_1825_; lean_object* v_res_1826_; 
v_sz_boxed_1824_ = lean_unbox_usize(v_sz_1821_);
lean_dec(v_sz_1821_);
v_i_boxed_1825_ = lean_unbox_usize(v_i_1822_);
lean_dec(v_i_1822_);
v_res_1826_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__9___redArg(v_inst_1818_, v_xs_1819_, v_f_1820_, v_sz_boxed_1824_, v_i_boxed_1825_, v_bs_1823_);
lean_dec_ref(v_xs_1819_);
return v_res_1826_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__11___redArg(lean_object* v_as_1828_, lean_object* v_lo_1829_, lean_object* v_hi_1830_){
_start:
{
uint8_t v___x_1831_; 
v___x_1831_ = lean_nat_dec_lt(v_lo_1829_, v_hi_1830_);
if (v___x_1831_ == 0)
{
lean_dec(v_lo_1829_);
return v_as_1828_;
}
else
{
lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v_fst_1834_; lean_object* v_snd_1835_; uint8_t v___x_1836_; 
v___x_1832_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__11___redArg___closed__0));
lean_inc(v_lo_1829_);
v___x_1833_ = l_Array_qpartition___redArg(v_as_1828_, v___x_1832_, v_lo_1829_, v_hi_1830_);
v_fst_1834_ = lean_ctor_get(v___x_1833_, 0);
lean_inc(v_fst_1834_);
v_snd_1835_ = lean_ctor_get(v___x_1833_, 1);
lean_inc(v_snd_1835_);
lean_dec_ref(v___x_1833_);
v___x_1836_ = lean_nat_dec_le(v_hi_1830_, v_fst_1834_);
if (v___x_1836_ == 0)
{
lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; 
v___x_1837_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__11___redArg(v_snd_1835_, v_lo_1829_, v_fst_1834_);
v___x_1838_ = lean_unsigned_to_nat(1u);
v___x_1839_ = lean_nat_add(v_fst_1834_, v___x_1838_);
lean_dec(v_fst_1834_);
v_as_1828_ = v___x_1837_;
v_lo_1829_ = v___x_1839_;
goto _start;
}
else
{
lean_dec(v_fst_1834_);
lean_dec(v_lo_1829_);
return v_snd_1835_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__11___redArg___boxed(lean_object* v_as_1841_, lean_object* v_lo_1842_, lean_object* v_hi_1843_){
_start:
{
lean_object* v_res_1844_; 
v_res_1844_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__11___redArg(v_as_1841_, v_lo_1842_, v_hi_1843_);
lean_dec(v_hi_1843_);
return v_res_1844_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__12(lean_object* v_as_1845_, size_t v_i_1846_, size_t v_stop_1847_, lean_object* v_b_1848_){
_start:
{
uint8_t v___x_1849_; 
v___x_1849_ = lean_usize_dec_eq(v_i_1846_, v_stop_1847_);
if (v___x_1849_ == 0)
{
lean_object* v___x_1850_; lean_object* v___x_1851_; size_t v___x_1852_; size_t v___x_1853_; 
v___x_1850_ = lean_array_uget_borrowed(v_as_1845_, v_i_1846_);
v___x_1851_ = l_Array_append___redArg(v_b_1848_, v___x_1850_);
v___x_1852_ = ((size_t)1ULL);
v___x_1853_ = lean_usize_add(v_i_1846_, v___x_1852_);
v_i_1846_ = v___x_1853_;
v_b_1848_ = v___x_1851_;
goto _start;
}
else
{
return v_b_1848_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__12___boxed(lean_object* v_as_1855_, lean_object* v_i_1856_, lean_object* v_stop_1857_, lean_object* v_b_1858_){
_start:
{
size_t v_i_boxed_1859_; size_t v_stop_boxed_1860_; lean_object* v_res_1861_; 
v_i_boxed_1859_ = lean_unbox_usize(v_i_1856_);
lean_dec(v_i_1856_);
v_stop_boxed_1860_ = lean_unbox_usize(v_stop_1857_);
lean_dec(v_stop_1857_);
v_res_1861_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__12(v_as_1855_, v_i_boxed_1859_, v_stop_boxed_1860_, v_b_1858_);
lean_dec_ref(v_as_1855_);
return v_res_1861_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__10___redArg(lean_object* v_xs_1862_, lean_object* v_ys_1863_, lean_object* v_x_1864_){
_start:
{
lean_object* v_zero_1865_; uint8_t v_isZero_1866_; 
v_zero_1865_ = lean_unsigned_to_nat(0u);
v_isZero_1866_ = lean_nat_dec_eq(v_x_1864_, v_zero_1865_);
if (v_isZero_1866_ == 1)
{
lean_dec(v_x_1864_);
return v_isZero_1866_;
}
else
{
lean_object* v_one_1867_; lean_object* v_n_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; uint8_t v___x_1871_; 
v_one_1867_ = lean_unsigned_to_nat(1u);
v_n_1868_ = lean_nat_sub(v_x_1864_, v_one_1867_);
lean_dec(v_x_1864_);
v___x_1869_ = lean_array_fget_borrowed(v_xs_1862_, v_n_1868_);
v___x_1870_ = lean_array_fget_borrowed(v_ys_1863_, v_n_1868_);
v___x_1871_ = lean_nat_dec_eq(v___x_1869_, v___x_1870_);
if (v___x_1871_ == 0)
{
lean_dec(v_n_1868_);
return v___x_1871_;
}
else
{
v_x_1864_ = v_n_1868_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__10___redArg___boxed(lean_object* v_xs_1873_, lean_object* v_ys_1874_, lean_object* v_x_1875_){
_start:
{
uint8_t v_res_1876_; lean_object* v_r_1877_; 
v_res_1876_ = l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__10___redArg(v_xs_1873_, v_ys_1874_, v_x_1875_);
lean_dec_ref(v_ys_1874_);
lean_dec_ref(v_xs_1873_);
v_r_1877_ = lean_box(v_res_1876_);
return v_r_1877_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__8___closed__0(void){
_start:
{
lean_object* v___x_1878_; 
v___x_1878_ = l_Array_instInhabited(lean_box(0));
return v___x_1878_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__8(lean_object* v_msg_1879_){
_start:
{
lean_object* v___x_1880_; lean_object* v___x_1881_; 
v___x_1880_ = lean_obj_once(&l_panic___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__8___closed__0, &l_panic___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__8___closed__0_once, _init_l_panic___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__8___closed__0);
v___x_1881_ = lean_panic_fn(v___x_1880_, v_msg_1879_);
return v___x_1881_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; 
v___x_1884_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__1));
v___x_1885_ = lean_unsigned_to_nat(2u);
v___x_1886_ = lean_unsigned_to_nat(63u);
v___x_1887_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__0));
v___x_1888_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg___closed__0));
v___x_1889_ = l_mkPanicMessageWithDecl(v___x_1888_, v___x_1887_, v___x_1886_, v___x_1885_, v___x_1884_);
return v___x_1889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg(lean_object* v_inst_1892_, lean_object* v_f_1893_, lean_object* v_xs_1894_, lean_object* v_ys_1895_){
_start:
{
size_t v_sz_1899_; size_t v___x_1900_; lean_object* v_positions_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___y_1905_; lean_object* v___y_1911_; lean_object* v___y_1912_; lean_object* v___y_1913_; lean_object* v___y_1914_; lean_object* v___y_1917_; lean_object* v___y_1918_; lean_object* v___y_1919_; lean_object* v___y_1920_; lean_object* v___y_1923_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; uint8_t v___x_1933_; 
v_sz_1899_ = lean_array_size(v_ys_1895_);
v___x_1900_ = ((size_t)0ULL);
v_positions_1901_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__9___redArg(v_inst_1892_, v_xs_1894_, v_f_1893_, v_sz_1899_, v___x_1900_, v_ys_1895_);
v___x_1902_ = lean_array_get_size(v_xs_1894_);
v___x_1903_ = l_Array_range(v___x_1902_);
v___x_1930_ = lean_unsigned_to_nat(0u);
v___x_1931_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__3));
v___x_1932_ = lean_array_get_size(v_positions_1901_);
v___x_1933_ = lean_nat_dec_lt(v___x_1930_, v___x_1932_);
if (v___x_1933_ == 0)
{
v___y_1923_ = v___x_1931_;
goto v___jp_1922_;
}
else
{
uint8_t v___x_1934_; 
v___x_1934_ = lean_nat_dec_le(v___x_1932_, v___x_1932_);
if (v___x_1934_ == 0)
{
if (v___x_1933_ == 0)
{
v___y_1923_ = v___x_1931_;
goto v___jp_1922_;
}
else
{
size_t v___x_1935_; lean_object* v___x_1936_; 
v___x_1935_ = lean_usize_of_nat(v___x_1932_);
v___x_1936_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__12(v_positions_1901_, v___x_1900_, v___x_1935_, v___x_1931_);
v___y_1923_ = v___x_1936_;
goto v___jp_1922_;
}
}
else
{
size_t v___x_1937_; lean_object* v___x_1938_; 
v___x_1937_ = lean_usize_of_nat(v___x_1932_);
v___x_1938_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__12(v_positions_1901_, v___x_1900_, v___x_1937_, v___x_1931_);
v___y_1923_ = v___x_1938_;
goto v___jp_1922_;
}
}
v___jp_1896_:
{
lean_object* v___x_1897_; lean_object* v___x_1898_; 
v___x_1897_ = lean_obj_once(&l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__2, &l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__2_once, _init_l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__2);
v___x_1898_ = l_panic___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__8(v___x_1897_);
return v___x_1898_;
}
v___jp_1904_:
{
lean_object* v___x_1906_; lean_object* v___x_1907_; uint8_t v___x_1908_; 
v___x_1906_ = lean_array_get_size(v___x_1903_);
v___x_1907_ = lean_array_get_size(v___y_1905_);
v___x_1908_ = lean_nat_dec_eq(v___x_1906_, v___x_1907_);
if (v___x_1908_ == 0)
{
lean_dec_ref(v___y_1905_);
lean_dec_ref(v___x_1903_);
lean_dec_ref(v_positions_1901_);
goto v___jp_1896_;
}
else
{
uint8_t v___x_1909_; 
v___x_1909_ = l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__10___redArg(v___x_1903_, v___y_1905_, v___x_1906_);
lean_dec_ref(v___y_1905_);
lean_dec_ref(v___x_1903_);
if (v___x_1909_ == 0)
{
lean_dec_ref(v_positions_1901_);
goto v___jp_1896_;
}
else
{
return v_positions_1901_;
}
}
}
v___jp_1910_:
{
lean_object* v___x_1915_; 
lean_dec(v___y_1912_);
v___x_1915_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__11___redArg(v___y_1913_, v___y_1911_, v___y_1914_);
lean_dec(v___y_1914_);
v___y_1905_ = v___x_1915_;
goto v___jp_1904_;
}
v___jp_1916_:
{
uint8_t v___x_1921_; 
v___x_1921_ = lean_nat_dec_le(v___y_1920_, v___y_1918_);
if (v___x_1921_ == 0)
{
lean_dec(v___y_1918_);
lean_inc(v___y_1920_);
v___y_1911_ = v___y_1920_;
v___y_1912_ = v___y_1917_;
v___y_1913_ = v___y_1919_;
v___y_1914_ = v___y_1920_;
goto v___jp_1910_;
}
else
{
v___y_1911_ = v___y_1920_;
v___y_1912_ = v___y_1917_;
v___y_1913_ = v___y_1919_;
v___y_1914_ = v___y_1918_;
goto v___jp_1910_;
}
}
v___jp_1922_:
{
lean_object* v___x_1924_; lean_object* v___x_1925_; uint8_t v___x_1926_; 
v___x_1924_ = lean_array_get_size(v___y_1923_);
v___x_1925_ = lean_unsigned_to_nat(0u);
v___x_1926_ = lean_nat_dec_eq(v___x_1924_, v___x_1925_);
if (v___x_1926_ == 0)
{
lean_object* v___x_1927_; lean_object* v___x_1928_; uint8_t v___x_1929_; 
v___x_1927_ = lean_unsigned_to_nat(1u);
v___x_1928_ = lean_nat_sub(v___x_1924_, v___x_1927_);
v___x_1929_ = lean_nat_dec_le(v___x_1925_, v___x_1928_);
if (v___x_1929_ == 0)
{
lean_inc(v___x_1928_);
v___y_1917_ = v___x_1924_;
v___y_1918_ = v___x_1928_;
v___y_1919_ = v___y_1923_;
v___y_1920_ = v___x_1928_;
goto v___jp_1916_;
}
else
{
v___y_1917_ = v___x_1924_;
v___y_1918_ = v___x_1928_;
v___y_1919_ = v___y_1923_;
v___y_1920_ = v___x_1925_;
goto v___jp_1916_;
}
}
else
{
v___y_1905_ = v___y_1923_;
goto v___jp_1904_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___boxed(lean_object* v_inst_1939_, lean_object* v_f_1940_, lean_object* v_xs_1941_, lean_object* v_ys_1942_){
_start:
{
lean_object* v_res_1943_; 
v_res_1943_ = l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg(v_inst_1939_, v_f_1940_, v_xs_1941_, v_ys_1942_);
lean_dec_ref(v_xs_1941_);
return v_res_1943_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___redArg(lean_object* v_fixedParamPerms_1944_, lean_object* v_xs_1945_, lean_object* v_as_1946_, lean_object* v_i_1947_, lean_object* v_j_1948_, lean_object* v_bs_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_){
_start:
{
lean_object* v_zero_1955_; uint8_t v_isZero_1956_; 
v_zero_1955_ = lean_unsigned_to_nat(0u);
v_isZero_1956_ = lean_nat_dec_eq(v_i_1947_, v_zero_1955_);
if (v_isZero_1956_ == 1)
{
lean_object* v___x_1957_; 
lean_dec(v_j_1948_);
lean_dec(v_i_1947_);
lean_dec_ref(v_xs_1945_);
v___x_1957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1957_, 0, v_bs_1949_);
return v___x_1957_;
}
else
{
lean_object* v_perms_1958_; lean_object* v___x_1959_; lean_object* v_value_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; 
v_perms_1958_ = lean_ctor_get(v_fixedParamPerms_1944_, 1);
v___x_1959_ = lean_array_fget_borrowed(v_as_1946_, v_j_1948_);
v_value_1960_ = lean_ctor_get(v___x_1959_, 7);
v___x_1961_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9___redArg___closed__0, &l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9___redArg___closed__0_once, _init_l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9___redArg___closed__0);
v___x_1962_ = lean_array_get_borrowed(v___x_1961_, v_perms_1958_, v_j_1948_);
lean_inc_ref(v_xs_1945_);
lean_inc_ref(v_value_1960_);
lean_inc(v___x_1962_);
v___x_1963_ = l_Lean_Elab_FixedParamPerm_instantiateLambda(v___x_1962_, v_value_1960_, v_xs_1945_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_);
if (lean_obj_tag(v___x_1963_) == 0)
{
lean_object* v_a_1964_; lean_object* v_one_1965_; lean_object* v_n_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; 
v_a_1964_ = lean_ctor_get(v___x_1963_, 0);
lean_inc(v_a_1964_);
lean_dec_ref(v___x_1963_);
v_one_1965_ = lean_unsigned_to_nat(1u);
v_n_1966_ = lean_nat_sub(v_i_1947_, v_one_1965_);
lean_dec(v_i_1947_);
v___x_1967_ = lean_nat_add(v_j_1948_, v_one_1965_);
lean_dec(v_j_1948_);
v___x_1968_ = lean_array_push(v_bs_1949_, v_a_1964_);
v_i_1947_ = v_n_1966_;
v_j_1948_ = v___x_1967_;
v_bs_1949_ = v___x_1968_;
goto _start;
}
else
{
lean_object* v_a_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_1977_; 
lean_dec_ref(v_bs_1949_);
lean_dec(v_j_1948_);
lean_dec(v_i_1947_);
lean_dec_ref(v_xs_1945_);
v_a_1970_ = lean_ctor_get(v___x_1963_, 0);
v_isSharedCheck_1977_ = !lean_is_exclusive(v___x_1963_);
if (v_isSharedCheck_1977_ == 0)
{
v___x_1972_ = v___x_1963_;
v_isShared_1973_ = v_isSharedCheck_1977_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_a_1970_);
lean_dec(v___x_1963_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_1977_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v___x_1975_; 
if (v_isShared_1973_ == 0)
{
v___x_1975_ = v___x_1972_;
goto v_reusejp_1974_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v_a_1970_);
v___x_1975_ = v_reuseFailAlloc_1976_;
goto v_reusejp_1974_;
}
v_reusejp_1974_:
{
return v___x_1975_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___redArg___boxed(lean_object* v_fixedParamPerms_1978_, lean_object* v_xs_1979_, lean_object* v_as_1980_, lean_object* v_i_1981_, lean_object* v_j_1982_, lean_object* v_bs_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_){
_start:
{
lean_object* v_res_1989_; 
v_res_1989_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___redArg(v_fixedParamPerms_1978_, v_xs_1979_, v_as_1980_, v_i_1981_, v_j_1982_, v_bs_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_);
lean_dec(v___y_1987_);
lean_dec_ref(v___y_1986_);
lean_dec(v___y_1985_);
lean_dec_ref(v___y_1984_);
lean_dec_ref(v_as_1980_);
lean_dec_ref(v_fixedParamPerms_1978_);
return v_res_1989_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___redArg(lean_object* v_fixedParamPerms_1990_, lean_object* v_xs_1991_, lean_object* v_as_1992_, lean_object* v_i_1993_, lean_object* v_j_1994_, lean_object* v_bs_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_){
_start:
{
lean_object* v_zero_2001_; uint8_t v_isZero_2002_; 
v_zero_2001_ = lean_unsigned_to_nat(0u);
v_isZero_2002_ = lean_nat_dec_eq(v_i_1993_, v_zero_2001_);
if (v_isZero_2002_ == 1)
{
lean_object* v___x_2003_; 
lean_dec(v_j_1994_);
lean_dec(v_i_1993_);
lean_dec_ref(v_xs_1991_);
v___x_2003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2003_, 0, v_bs_1995_);
return v___x_2003_;
}
else
{
lean_object* v_perms_2004_; lean_object* v___x_2005_; lean_object* v_type_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; 
v_perms_2004_ = lean_ctor_get(v_fixedParamPerms_1990_, 1);
v___x_2005_ = lean_array_fget_borrowed(v_as_1992_, v_j_1994_);
v_type_2006_ = lean_ctor_get(v___x_2005_, 6);
v___x_2007_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9___redArg___closed__0, &l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9___redArg___closed__0_once, _init_l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9___redArg___closed__0);
v___x_2008_ = lean_array_get_borrowed(v___x_2007_, v_perms_2004_, v_j_1994_);
lean_inc_ref(v_xs_1991_);
lean_inc_ref(v_type_2006_);
lean_inc(v___x_2008_);
v___x_2009_ = l_Lean_Elab_FixedParamPerm_instantiateForall(v___x_2008_, v_type_2006_, v_xs_1991_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_);
if (lean_obj_tag(v___x_2009_) == 0)
{
lean_object* v_a_2010_; lean_object* v_one_2011_; lean_object* v_n_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; 
v_a_2010_ = lean_ctor_get(v___x_2009_, 0);
lean_inc(v_a_2010_);
lean_dec_ref(v___x_2009_);
v_one_2011_ = lean_unsigned_to_nat(1u);
v_n_2012_ = lean_nat_sub(v_i_1993_, v_one_2011_);
lean_dec(v_i_1993_);
v___x_2013_ = lean_nat_add(v_j_1994_, v_one_2011_);
lean_dec(v_j_1994_);
v___x_2014_ = lean_array_push(v_bs_1995_, v_a_2010_);
v_i_1993_ = v_n_2012_;
v_j_1994_ = v___x_2013_;
v_bs_1995_ = v___x_2014_;
goto _start;
}
else
{
lean_object* v_a_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2023_; 
lean_dec_ref(v_bs_1995_);
lean_dec(v_j_1994_);
lean_dec(v_i_1993_);
lean_dec_ref(v_xs_1991_);
v_a_2016_ = lean_ctor_get(v___x_2009_, 0);
v_isSharedCheck_2023_ = !lean_is_exclusive(v___x_2009_);
if (v_isSharedCheck_2023_ == 0)
{
v___x_2018_ = v___x_2009_;
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_a_2016_);
lean_dec(v___x_2009_);
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
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___redArg___boxed(lean_object* v_fixedParamPerms_2024_, lean_object* v_xs_2025_, lean_object* v_as_2026_, lean_object* v_i_2027_, lean_object* v_j_2028_, lean_object* v_bs_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_){
_start:
{
lean_object* v_res_2035_; 
v_res_2035_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___redArg(v_fixedParamPerms_2024_, v_xs_2025_, v_as_2026_, v_i_2027_, v_j_2028_, v_bs_2029_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_);
lean_dec(v___y_2033_);
lean_dec_ref(v___y_2032_);
lean_dec(v___y_2031_);
lean_dec_ref(v___y_2030_);
lean_dec_ref(v_as_2026_);
lean_dec_ref(v_fixedParamPerms_2024_);
return v_res_2035_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__8(void){
_start:
{
lean_object* v___x_2048_; lean_object* v___x_2049_; 
v___x_2048_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__7));
v___x_2049_ = l_Lean_stringToMessageData(v___x_2048_);
return v___x_2049_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__10(void){
_start:
{
lean_object* v___x_2051_; lean_object* v___x_2052_; 
v___x_2051_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__9));
v___x_2052_ = l_Lean_stringToMessageData(v___x_2051_);
return v___x_2052_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion(lean_object* v_preDefs_2053_, lean_object* v_fixedParamPerms_2054_, lean_object* v_xs_2055_, lean_object* v_recArgInfos_2056_, lean_object* v_a_2057_, lean_object* v_a_2058_, lean_object* v_a_2059_, lean_object* v_a_2060_){
_start:
{
lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; 
v___x_2062_ = lean_array_get_size(v_preDefs_2053_);
v___x_2063_ = lean_unsigned_to_nat(0u);
v___x_2064_ = lean_mk_empty_array_with_capacity(v___x_2062_);
lean_inc_ref(v___x_2064_);
lean_inc_ref(v_xs_2055_);
v___x_2065_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___redArg(v_fixedParamPerms_2054_, v_xs_2055_, v_preDefs_2053_, v___x_2062_, v___x_2063_, v___x_2064_, v_a_2057_, v_a_2058_, v_a_2059_, v_a_2060_);
if (lean_obj_tag(v___x_2065_) == 0)
{
lean_object* v_a_2066_; lean_object* v___x_2067_; 
v_a_2066_ = lean_ctor_get(v___x_2065_, 0);
lean_inc(v_a_2066_);
lean_dec_ref(v___x_2065_);
lean_inc_ref(v_xs_2055_);
v___x_2067_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___redArg(v_fixedParamPerms_2054_, v_xs_2055_, v_preDefs_2053_, v___x_2062_, v___x_2063_, v___x_2064_, v_a_2057_, v_a_2058_, v_a_2059_, v_a_2060_);
if (lean_obj_tag(v___x_2067_) == 0)
{
lean_object* v_a_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v_indGroupInst_2071_; lean_object* v_toIndGroupInfo_2072_; lean_object* v_all_2073_; lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2159_; 
v_a_2068_ = lean_ctor_get(v___x_2067_, 0);
lean_inc(v_a_2068_);
lean_dec_ref(v___x_2067_);
v___x_2069_ = l_Lean_Elab_Structural_instInhabitedRecArgInfo_default;
v___x_2070_ = lean_array_get_borrowed(v___x_2069_, v_recArgInfos_2056_, v___x_2063_);
v_indGroupInst_2071_ = lean_ctor_get(v___x_2070_, 4);
v_toIndGroupInfo_2072_ = lean_ctor_get(v_indGroupInst_2071_, 0);
lean_inc_ref(v_toIndGroupInfo_2072_);
v_all_2073_ = lean_ctor_get(v_toIndGroupInfo_2072_, 0);
v_isSharedCheck_2159_ = !lean_is_exclusive(v_toIndGroupInfo_2072_);
if (v_isSharedCheck_2159_ == 0)
{
lean_object* v_unused_2160_; 
v_unused_2160_ = lean_ctor_get(v_toIndGroupInfo_2072_, 1);
lean_dec(v_unused_2160_);
v___x_2075_ = v_toIndGroupInfo_2072_;
v_isShared_2076_ = v_isSharedCheck_2159_;
goto v_resetjp_2074_;
}
else
{
lean_inc(v_all_2073_);
lean_dec(v_toIndGroupInfo_2072_);
v___x_2075_ = lean_box(0);
v_isShared_2076_ = v_isSharedCheck_2159_;
goto v_resetjp_2074_;
}
v_resetjp_2074_:
{
lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; 
v___x_2077_ = lean_box(0);
v___x_2078_ = lean_array_get(v___x_2077_, v_all_2073_, v___x_2063_);
lean_dec_ref(v_all_2073_);
v___x_2079_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4(v___x_2078_, v_a_2057_, v_a_2058_, v_a_2059_, v_a_2060_);
if (lean_obj_tag(v___x_2079_) == 0)
{
lean_object* v_a_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v_a_2083_; lean_object* v___f_2084_; lean_object* v___f_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___y_2091_; lean_object* v___y_2092_; lean_object* v___y_2093_; lean_object* v___y_2094_; uint8_t v___x_2127_; 
v_a_2080_ = lean_ctor_get(v___x_2079_, 0);
lean_inc(v_a_2080_);
lean_dec_ref(v___x_2079_);
v___x_2081_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__3));
v___x_2082_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___redArg(v___x_2081_, v_a_2059_);
v_a_2083_ = lean_ctor_get(v___x_2082_, 0);
lean_inc(v_a_2083_);
lean_dec_ref(v___x_2082_);
v___f_2084_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__4));
v___f_2085_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__5));
v___x_2086_ = l_Lean_instInhabitedExpr;
v___x_2087_ = l_Lean_InductiveVal_numTypeFormers(v_a_2080_);
v___x_2088_ = l_Array_range(v___x_2087_);
v___x_2089_ = l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg(v___x_2069_, v___f_2085_, v_recArgInfos_2056_, v___x_2088_);
v___x_2127_ = lean_unbox(v_a_2083_);
lean_dec(v_a_2083_);
if (v___x_2127_ == 0)
{
lean_del_object(v___x_2075_);
v___y_2091_ = v_a_2057_;
v___y_2092_ = v_a_2058_;
v___y_2093_ = v_a_2059_;
v___y_2094_ = v_a_2060_;
goto v___jp_2090_;
}
else
{
lean_object* v_toConstantVal_2128_; lean_object* v_name_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2133_; 
v_toConstantVal_2128_ = lean_ctor_get(v_a_2080_, 0);
v_name_2129_ = lean_ctor_get(v_toConstantVal_2128_, 0);
v___x_2130_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__8);
lean_inc(v_name_2129_);
v___x_2131_ = l_Lean_MessageData_ofName(v_name_2129_);
if (v_isShared_2076_ == 0)
{
lean_ctor_set_tag(v___x_2075_, 7);
lean_ctor_set(v___x_2075_, 1, v___x_2131_);
lean_ctor_set(v___x_2075_, 0, v___x_2130_);
v___x_2133_ = v___x_2075_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2150_; 
v_reuseFailAlloc_2150_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2150_, 0, v___x_2130_);
lean_ctor_set(v_reuseFailAlloc_2150_, 1, v___x_2131_);
v___x_2133_ = v_reuseFailAlloc_2150_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; 
v___x_2134_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__10, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__10);
v___x_2135_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2135_, 0, v___x_2133_);
lean_ctor_set(v___x_2135_, 1, v___x_2134_);
lean_inc_ref(v___x_2089_);
v___x_2136_ = lean_array_to_list(v___x_2089_);
v___x_2137_ = lean_box(0);
v___x_2138_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__21(v___x_2136_, v___x_2137_);
v___x_2139_ = l_Lean_MessageData_ofList(v___x_2138_);
v___x_2140_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2140_, 0, v___x_2135_);
lean_ctor_set(v___x_2140_, 1, v___x_2139_);
v___x_2141_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12(v___x_2081_, v___x_2140_, v_a_2057_, v_a_2058_, v_a_2059_, v_a_2060_);
if (lean_obj_tag(v___x_2141_) == 0)
{
lean_dec_ref(v___x_2141_);
v___y_2091_ = v_a_2057_;
v___y_2092_ = v_a_2058_;
v___y_2093_ = v_a_2059_;
v___y_2094_ = v_a_2060_;
goto v___jp_2090_;
}
else
{
lean_object* v_a_2142_; lean_object* v___x_2144_; uint8_t v_isShared_2145_; uint8_t v_isSharedCheck_2149_; 
lean_dec_ref(v___x_2089_);
lean_dec(v_a_2080_);
lean_dec(v_a_2068_);
lean_dec(v_a_2066_);
lean_dec_ref(v_recArgInfos_2056_);
lean_dec_ref(v_xs_2055_);
lean_dec_ref(v_fixedParamPerms_2054_);
lean_dec_ref(v_preDefs_2053_);
v_a_2142_ = lean_ctor_get(v___x_2141_, 0);
v_isSharedCheck_2149_ = !lean_is_exclusive(v___x_2141_);
if (v_isSharedCheck_2149_ == 0)
{
v___x_2144_ = v___x_2141_;
v_isShared_2145_ = v_isSharedCheck_2149_;
goto v_resetjp_2143_;
}
else
{
lean_inc(v_a_2142_);
lean_dec(v___x_2141_);
v___x_2144_ = lean_box(0);
v_isShared_2145_ = v_isSharedCheck_2149_;
goto v_resetjp_2143_;
}
v_resetjp_2143_:
{
lean_object* v___x_2147_; 
if (v_isShared_2145_ == 0)
{
v___x_2147_ = v___x_2144_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v_a_2142_);
v___x_2147_ = v_reuseFailAlloc_2148_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
return v___x_2147_;
}
}
}
}
}
v___jp_2090_:
{
lean_object* v_toConstantVal_2095_; lean_object* v_numIndices_2096_; lean_object* v_name_2097_; lean_object* v___x_2098_; 
v_toConstantVal_2095_ = lean_ctor_get(v_a_2080_, 0);
lean_inc_ref(v_toConstantVal_2095_);
v_numIndices_2096_ = lean_ctor_get(v_a_2080_, 2);
lean_inc(v_numIndices_2096_);
lean_dec(v_a_2080_);
v_name_2097_ = lean_ctor_get(v_toConstantVal_2095_, 0);
lean_inc(v_name_2097_);
lean_dec_ref(v_toConstantVal_2095_);
v___x_2098_ = l_Lean_Meta_isInductivePredicate(v_name_2097_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_);
if (lean_obj_tag(v___x_2098_) == 0)
{
lean_object* v_a_2099_; lean_object* v___f_2100_; uint8_t v___x_2101_; 
v_a_2099_ = lean_ctor_get(v___x_2098_, 0);
lean_inc(v_a_2099_);
lean_dec_ref(v___x_2098_);
lean_inc(v_a_2099_);
lean_inc(v_numIndices_2096_);
lean_inc_ref(v_preDefs_2053_);
lean_inc_ref(v_xs_2055_);
lean_inc_ref(v_fixedParamPerms_2054_);
lean_inc_ref(v___x_2089_);
lean_inc(v_a_2066_);
lean_inc_ref(v_recArgInfos_2056_);
v___f_2100_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___boxed), 19, 12);
lean_closure_set(v___f_2100_, 0, v___x_2081_);
lean_closure_set(v___f_2100_, 1, v_recArgInfos_2056_);
lean_closure_set(v___f_2100_, 2, v_a_2066_);
lean_closure_set(v___f_2100_, 3, v___x_2089_);
lean_closure_set(v___f_2100_, 4, v___x_2063_);
lean_closure_set(v___f_2100_, 5, v_fixedParamPerms_2054_);
lean_closure_set(v___f_2100_, 6, v_xs_2055_);
lean_closure_set(v___f_2100_, 7, v_preDefs_2053_);
lean_closure_set(v___f_2100_, 8, v_numIndices_2096_);
lean_closure_set(v___f_2100_, 9, v___x_2086_);
lean_closure_set(v___f_2100_, 10, v___f_2084_);
lean_closure_set(v___f_2100_, 11, v_a_2099_);
v___x_2101_ = lean_unbox(v_a_2099_);
if (v___x_2101_ == 0)
{
lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; 
lean_dec_ref(v___f_2100_);
v___x_2102_ = lean_array_get_size(v_recArgInfos_2056_);
v___x_2103_ = lean_mk_empty_array_with_capacity(v___x_2102_);
v___x_2104_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__20___redArg(v_a_2066_, v_a_2068_, v_recArgInfos_2056_, v___x_2102_, v___x_2063_, v___x_2103_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_);
lean_dec(v_a_2068_);
if (lean_obj_tag(v___x_2104_) == 0)
{
lean_object* v_a_2105_; lean_object* v___x_2106_; uint8_t v___x_2107_; lean_object* v___x_2108_; 
v_a_2105_ = lean_ctor_get(v___x_2104_, 0);
lean_inc(v_a_2105_);
lean_dec_ref(v___x_2104_);
v___x_2106_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__6));
v___x_2107_ = lean_unbox(v_a_2099_);
lean_dec(v_a_2099_);
v___x_2108_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1(v___x_2081_, v_recArgInfos_2056_, v_a_2066_, v___x_2089_, v___x_2063_, v_fixedParamPerms_2054_, v_xs_2055_, v_preDefs_2053_, v_numIndices_2096_, v___x_2086_, v___f_2084_, v___x_2107_, v___x_2106_, v_a_2105_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_);
lean_dec(v_numIndices_2096_);
lean_dec(v_a_2066_);
return v___x_2108_;
}
else
{
lean_object* v_a_2109_; lean_object* v___x_2111_; uint8_t v_isShared_2112_; uint8_t v_isSharedCheck_2116_; 
lean_dec(v_a_2099_);
lean_dec(v_numIndices_2096_);
lean_dec_ref(v___x_2089_);
lean_dec(v_a_2066_);
lean_dec_ref(v_recArgInfos_2056_);
lean_dec_ref(v_xs_2055_);
lean_dec_ref(v_fixedParamPerms_2054_);
lean_dec_ref(v_preDefs_2053_);
v_a_2109_ = lean_ctor_get(v___x_2104_, 0);
v_isSharedCheck_2116_ = !lean_is_exclusive(v___x_2104_);
if (v_isSharedCheck_2116_ == 0)
{
v___x_2111_ = v___x_2104_;
v_isShared_2112_ = v_isSharedCheck_2116_;
goto v_resetjp_2110_;
}
else
{
lean_inc(v_a_2109_);
lean_dec(v___x_2104_);
v___x_2111_ = lean_box(0);
v_isShared_2112_ = v_isSharedCheck_2116_;
goto v_resetjp_2110_;
}
v_resetjp_2110_:
{
lean_object* v___x_2114_; 
if (v_isShared_2112_ == 0)
{
v___x_2114_ = v___x_2111_;
goto v_reusejp_2113_;
}
else
{
lean_object* v_reuseFailAlloc_2115_; 
v_reuseFailAlloc_2115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2115_, 0, v_a_2109_);
v___x_2114_ = v_reuseFailAlloc_2115_;
goto v_reusejp_2113_;
}
v_reusejp_2113_:
{
return v___x_2114_;
}
}
}
}
else
{
lean_object* v___f_2117_; lean_object* v___x_2118_; 
lean_dec(v_a_2099_);
lean_dec(v_numIndices_2096_);
lean_dec_ref(v___x_2089_);
lean_dec(v_a_2068_);
lean_dec_ref(v_xs_2055_);
lean_dec_ref(v_fixedParamPerms_2054_);
lean_dec_ref(v_preDefs_2053_);
lean_inc(v_a_2066_);
v___f_2117_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___boxed), 10, 4);
lean_closure_set(v___f_2117_, 0, v_recArgInfos_2056_);
lean_closure_set(v___f_2117_, 1, v_a_2066_);
lean_closure_set(v___f_2117_, 2, v___x_2063_);
lean_closure_set(v___f_2117_, 3, v___f_2100_);
v___x_2118_ = l_Lean_Elab_Structural_withFunTypes___redArg(v_a_2066_, v___f_2117_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_);
return v___x_2118_;
}
}
else
{
lean_object* v_a_2119_; lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2126_; 
lean_dec(v_numIndices_2096_);
lean_dec_ref(v___x_2089_);
lean_dec(v_a_2068_);
lean_dec(v_a_2066_);
lean_dec_ref(v_recArgInfos_2056_);
lean_dec_ref(v_xs_2055_);
lean_dec_ref(v_fixedParamPerms_2054_);
lean_dec_ref(v_preDefs_2053_);
v_a_2119_ = lean_ctor_get(v___x_2098_, 0);
v_isSharedCheck_2126_ = !lean_is_exclusive(v___x_2098_);
if (v_isSharedCheck_2126_ == 0)
{
v___x_2121_ = v___x_2098_;
v_isShared_2122_ = v_isSharedCheck_2126_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_a_2119_);
lean_dec(v___x_2098_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2126_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
lean_object* v___x_2124_; 
if (v_isShared_2122_ == 0)
{
v___x_2124_ = v___x_2121_;
goto v_reusejp_2123_;
}
else
{
lean_object* v_reuseFailAlloc_2125_; 
v_reuseFailAlloc_2125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2125_, 0, v_a_2119_);
v___x_2124_ = v_reuseFailAlloc_2125_;
goto v_reusejp_2123_;
}
v_reusejp_2123_:
{
return v___x_2124_;
}
}
}
}
}
else
{
lean_object* v_a_2151_; lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2158_; 
lean_del_object(v___x_2075_);
lean_dec(v_a_2068_);
lean_dec(v_a_2066_);
lean_dec_ref(v_recArgInfos_2056_);
lean_dec_ref(v_xs_2055_);
lean_dec_ref(v_fixedParamPerms_2054_);
lean_dec_ref(v_preDefs_2053_);
v_a_2151_ = lean_ctor_get(v___x_2079_, 0);
v_isSharedCheck_2158_ = !lean_is_exclusive(v___x_2079_);
if (v_isSharedCheck_2158_ == 0)
{
v___x_2153_ = v___x_2079_;
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
else
{
lean_inc(v_a_2151_);
lean_dec(v___x_2079_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
lean_object* v___x_2156_; 
if (v_isShared_2154_ == 0)
{
v___x_2156_ = v___x_2153_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v_a_2151_);
v___x_2156_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
return v___x_2156_;
}
}
}
}
}
else
{
lean_object* v_a_2161_; lean_object* v___x_2163_; uint8_t v_isShared_2164_; uint8_t v_isSharedCheck_2168_; 
lean_dec(v_a_2066_);
lean_dec_ref(v_recArgInfos_2056_);
lean_dec_ref(v_xs_2055_);
lean_dec_ref(v_fixedParamPerms_2054_);
lean_dec_ref(v_preDefs_2053_);
v_a_2161_ = lean_ctor_get(v___x_2067_, 0);
v_isSharedCheck_2168_ = !lean_is_exclusive(v___x_2067_);
if (v_isSharedCheck_2168_ == 0)
{
v___x_2163_ = v___x_2067_;
v_isShared_2164_ = v_isSharedCheck_2168_;
goto v_resetjp_2162_;
}
else
{
lean_inc(v_a_2161_);
lean_dec(v___x_2067_);
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
lean_dec_ref(v___x_2064_);
lean_dec_ref(v_recArgInfos_2056_);
lean_dec_ref(v_xs_2055_);
lean_dec_ref(v_fixedParamPerms_2054_);
lean_dec_ref(v_preDefs_2053_);
v_a_2169_ = lean_ctor_get(v___x_2065_, 0);
v_isSharedCheck_2176_ = !lean_is_exclusive(v___x_2065_);
if (v_isSharedCheck_2176_ == 0)
{
v___x_2171_ = v___x_2065_;
v_isShared_2172_ = v_isSharedCheck_2176_;
goto v_resetjp_2170_;
}
else
{
lean_inc(v_a_2169_);
lean_dec(v___x_2065_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___boxed(lean_object* v_preDefs_2177_, lean_object* v_fixedParamPerms_2178_, lean_object* v_xs_2179_, lean_object* v_recArgInfos_2180_, lean_object* v_a_2181_, lean_object* v_a_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_){
_start:
{
lean_object* v_res_2186_; 
v_res_2186_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion(v_preDefs_2177_, v_fixedParamPerms_2178_, v_xs_2179_, v_recArgInfos_2180_, v_a_2181_, v_a_2182_, v_a_2183_, v_a_2184_);
lean_dec(v_a_2184_);
lean_dec_ref(v_a_2183_);
lean_dec(v_a_2182_);
lean_dec_ref(v_a_2181_);
return v_res_2186_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2(lean_object* v_fixedParamPerms_2187_, lean_object* v_xs_2188_, lean_object* v_as_2189_, lean_object* v_i_2190_, lean_object* v_j_2191_, lean_object* v_inv_2192_, lean_object* v_bs_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_){
_start:
{
lean_object* v___x_2199_; 
v___x_2199_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___redArg(v_fixedParamPerms_2187_, v_xs_2188_, v_as_2189_, v_i_2190_, v_j_2191_, v_bs_2193_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_);
return v___x_2199_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___boxed(lean_object* v_fixedParamPerms_2200_, lean_object* v_xs_2201_, lean_object* v_as_2202_, lean_object* v_i_2203_, lean_object* v_j_2204_, lean_object* v_inv_2205_, lean_object* v_bs_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_){
_start:
{
lean_object* v_res_2212_; 
v_res_2212_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2(v_fixedParamPerms_2200_, v_xs_2201_, v_as_2202_, v_i_2203_, v_j_2204_, v_inv_2205_, v_bs_2206_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_);
lean_dec(v___y_2210_);
lean_dec_ref(v___y_2209_);
lean_dec(v___y_2208_);
lean_dec_ref(v___y_2207_);
lean_dec_ref(v_as_2202_);
lean_dec_ref(v_fixedParamPerms_2200_);
return v_res_2212_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3(lean_object* v_fixedParamPerms_2213_, lean_object* v_xs_2214_, lean_object* v_as_2215_, lean_object* v_i_2216_, lean_object* v_j_2217_, lean_object* v_inv_2218_, lean_object* v_bs_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_){
_start:
{
lean_object* v___x_2225_; 
v___x_2225_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___redArg(v_fixedParamPerms_2213_, v_xs_2214_, v_as_2215_, v_i_2216_, v_j_2217_, v_bs_2219_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_);
return v___x_2225_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___boxed(lean_object* v_fixedParamPerms_2226_, lean_object* v_xs_2227_, lean_object* v_as_2228_, lean_object* v_i_2229_, lean_object* v_j_2230_, lean_object* v_inv_2231_, lean_object* v_bs_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_){
_start:
{
lean_object* v_res_2238_; 
v_res_2238_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3(v_fixedParamPerms_2226_, v_xs_2227_, v_as_2228_, v_i_2229_, v_j_2230_, v_inv_2231_, v_bs_2232_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_);
lean_dec(v___y_2236_);
lean_dec_ref(v___y_2235_);
lean_dec(v___y_2234_);
lean_dec_ref(v___y_2233_);
lean_dec_ref(v_as_2228_);
lean_dec_ref(v_fixedParamPerms_2226_);
return v_res_2238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6(lean_object* v_00_u03b1_2239_, lean_object* v_inst_2240_, lean_object* v_f_2241_, lean_object* v_xs_2242_, lean_object* v_ys_2243_){
_start:
{
lean_object* v___x_2244_; 
v___x_2244_ = l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg(v_inst_2240_, v_f_2241_, v_xs_2242_, v_ys_2243_);
return v___x_2244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___boxed(lean_object* v_00_u03b1_2245_, lean_object* v_inst_2246_, lean_object* v_f_2247_, lean_object* v_xs_2248_, lean_object* v_ys_2249_){
_start:
{
lean_object* v_res_2250_; 
v_res_2250_ = l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6(v_00_u03b1_2245_, v_inst_2246_, v_f_2247_, v_xs_2248_, v_ys_2249_);
lean_dec_ref(v_xs_2248_);
return v_res_2250_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__15(lean_object* v_00_u03b3_2251_, lean_object* v_msg_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_){
_start:
{
lean_object* v___x_2258_; 
v___x_2258_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__15___redArg(v_msg_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_);
return v___x_2258_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__15___boxed(lean_object* v_00_u03b3_2259_, lean_object* v_msg_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_){
_start:
{
lean_object* v_res_2266_; 
v_res_2266_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__15(v_00_u03b3_2259_, v_msg_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_);
lean_dec(v___y_2264_);
lean_dec_ref(v___y_2263_);
lean_dec(v___y_2262_);
lean_dec_ref(v___y_2261_);
return v_res_2266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7(lean_object* v_00_u03b3_2267_, lean_object* v_00_u03b1_2268_, lean_object* v_00_u03b2_2269_, lean_object* v_inst_2270_, lean_object* v_f_2271_, lean_object* v_positions_2272_, lean_object* v_ys_2273_, lean_object* v_xs_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_){
_start:
{
lean_object* v___x_2280_; 
v___x_2280_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg(v_inst_2270_, v_f_2271_, v_positions_2272_, v_ys_2273_, v_xs_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_);
return v___x_2280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___boxed(lean_object* v_00_u03b3_2281_, lean_object* v_00_u03b1_2282_, lean_object* v_00_u03b2_2283_, lean_object* v_inst_2284_, lean_object* v_f_2285_, lean_object* v_positions_2286_, lean_object* v_ys_2287_, lean_object* v_xs_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_){
_start:
{
lean_object* v_res_2294_; 
v_res_2294_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7(v_00_u03b3_2281_, v_00_u03b1_2282_, v_00_u03b2_2283_, v_inst_2284_, v_f_2285_, v_positions_2286_, v_ys_2287_, v_xs_2288_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_);
lean_dec(v___y_2292_);
lean_dec_ref(v___y_2291_);
lean_dec(v___y_2290_);
lean_dec_ref(v___y_2289_);
lean_dec_ref(v_xs_2288_);
lean_dec_ref(v_ys_2287_);
lean_dec_ref(v_positions_2286_);
return v_res_2294_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8(lean_object* v___x_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_, lean_object* v_funTypes_2298_, lean_object* v_as_2299_, lean_object* v_i_2300_, lean_object* v_j_2301_, lean_object* v_inv_2302_, lean_object* v_bs_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_){
_start:
{
lean_object* v___x_2309_; 
v___x_2309_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg(v___x_2295_, v_a_2296_, v_a_2297_, v_funTypes_2298_, v_as_2299_, v_i_2300_, v_j_2301_, v_bs_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_);
return v___x_2309_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___boxed(lean_object* v___x_2310_, lean_object* v_a_2311_, lean_object* v_a_2312_, lean_object* v_funTypes_2313_, lean_object* v_as_2314_, lean_object* v_i_2315_, lean_object* v_j_2316_, lean_object* v_inv_2317_, lean_object* v_bs_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_){
_start:
{
lean_object* v_res_2324_; 
v_res_2324_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8(v___x_2310_, v_a_2311_, v_a_2312_, v_funTypes_2313_, v_as_2314_, v_i_2315_, v_j_2316_, v_inv_2317_, v_bs_2318_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_);
lean_dec(v___y_2322_);
lean_dec_ref(v___y_2321_);
lean_dec(v___y_2320_);
lean_dec_ref(v___y_2319_);
lean_dec_ref(v_as_2314_);
return v_res_2324_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9(lean_object* v_fixedParamPerms_2325_, lean_object* v_xs_2326_, lean_object* v_as_2327_, lean_object* v_i_2328_, lean_object* v_j_2329_, lean_object* v_inv_2330_, lean_object* v_bs_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_){
_start:
{
lean_object* v___x_2337_; 
v___x_2337_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9___redArg(v_fixedParamPerms_2325_, v_xs_2326_, v_as_2327_, v_i_2328_, v_j_2329_, v_bs_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_);
return v___x_2337_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9___boxed(lean_object* v_fixedParamPerms_2338_, lean_object* v_xs_2339_, lean_object* v_as_2340_, lean_object* v_i_2341_, lean_object* v_j_2342_, lean_object* v_inv_2343_, lean_object* v_bs_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_){
_start:
{
lean_object* v_res_2350_; 
v_res_2350_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9(v_fixedParamPerms_2338_, v_xs_2339_, v_as_2340_, v_i_2341_, v_j_2342_, v_inv_2343_, v_bs_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_);
lean_dec(v___y_2348_);
lean_dec_ref(v___y_2347_);
lean_dec(v___y_2346_);
lean_dec_ref(v___y_2345_);
lean_dec_ref(v_as_2340_);
return v_res_2350_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13(lean_object* v_00_u03b1_2351_, lean_object* v_preDefs_2352_, lean_object* v_k_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_){
_start:
{
lean_object* v___x_2359_; 
v___x_2359_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13___redArg(v_preDefs_2352_, v_k_2353_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_);
return v___x_2359_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13___boxed(lean_object* v_00_u03b1_2360_, lean_object* v_preDefs_2361_, lean_object* v_k_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_){
_start:
{
lean_object* v_res_2368_; 
v_res_2368_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13(v_00_u03b1_2360_, v_preDefs_2361_, v_k_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_);
lean_dec(v___y_2366_);
lean_dec_ref(v___y_2365_);
lean_dec(v___y_2364_);
lean_dec_ref(v___y_2363_);
return v_res_2368_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__15(uint8_t v_a_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_, lean_object* v_recArgInfos_2372_, lean_object* v___x_2373_, lean_object* v_preDefs_2374_, lean_object* v_a_2375_, lean_object* v_as_2376_, lean_object* v_i_2377_, lean_object* v_j_2378_, lean_object* v_inv_2379_, lean_object* v_bs_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_){
_start:
{
lean_object* v___x_2386_; 
v___x_2386_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__15___redArg(v_a_2369_, v_a_2370_, v_a_2371_, v_recArgInfos_2372_, v___x_2373_, v_preDefs_2374_, v_a_2375_, v_as_2376_, v_i_2377_, v_j_2378_, v_bs_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_);
return v___x_2386_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__15___boxed(lean_object** _args){
lean_object* v_a_2387_ = _args[0];
lean_object* v_a_2388_ = _args[1];
lean_object* v_a_2389_ = _args[2];
lean_object* v_recArgInfos_2390_ = _args[3];
lean_object* v___x_2391_ = _args[4];
lean_object* v_preDefs_2392_ = _args[5];
lean_object* v_a_2393_ = _args[6];
lean_object* v_as_2394_ = _args[7];
lean_object* v_i_2395_ = _args[8];
lean_object* v_j_2396_ = _args[9];
lean_object* v_inv_2397_ = _args[10];
lean_object* v_bs_2398_ = _args[11];
lean_object* v___y_2399_ = _args[12];
lean_object* v___y_2400_ = _args[13];
lean_object* v___y_2401_ = _args[14];
lean_object* v___y_2402_ = _args[15];
lean_object* v___y_2403_ = _args[16];
_start:
{
uint8_t v_a_29909__boxed_2404_; lean_object* v_res_2405_; 
v_a_29909__boxed_2404_ = lean_unbox(v_a_2387_);
v_res_2405_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__15(v_a_29909__boxed_2404_, v_a_2388_, v_a_2389_, v_recArgInfos_2390_, v___x_2391_, v_preDefs_2392_, v_a_2393_, v_as_2394_, v_i_2395_, v_j_2396_, v_inv_2397_, v_bs_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_);
lean_dec(v___y_2402_);
lean_dec_ref(v___y_2401_);
lean_dec(v___y_2400_);
lean_dec_ref(v___y_2399_);
lean_dec_ref(v_as_2394_);
lean_dec_ref(v_a_2389_);
lean_dec_ref(v_a_2388_);
return v_res_2405_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17_spec__30(lean_object* v_declName_2406_, uint8_t v_s_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_){
_start:
{
lean_object* v___x_2413_; 
v___x_2413_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17_spec__30___redArg(v_declName_2406_, v_s_2407_, v___y_2409_, v___y_2411_);
return v___x_2413_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17_spec__30___boxed(lean_object* v_declName_2414_, lean_object* v_s_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_){
_start:
{
uint8_t v_s_boxed_2421_; lean_object* v_res_2422_; 
v_s_boxed_2421_ = lean_unbox(v_s_2415_);
v_res_2422_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17_spec__30(v_declName_2414_, v_s_boxed_2421_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_);
lean_dec(v___y_2419_);
lean_dec_ref(v___y_2418_);
lean_dec(v___y_2417_);
lean_dec_ref(v___y_2416_);
return v_res_2422_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18(lean_object* v_xs_2423_, uint8_t v_a_2424_, lean_object* v_preDefs_2425_, lean_object* v___x_2426_, lean_object* v_as_2427_, lean_object* v_i_2428_, lean_object* v_j_2429_, lean_object* v_inv_2430_, lean_object* v_bs_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_){
_start:
{
lean_object* v___x_2437_; 
v___x_2437_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___redArg(v_xs_2423_, v_a_2424_, v_preDefs_2425_, v___x_2426_, v_as_2427_, v_i_2428_, v_j_2429_, v_bs_2431_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_);
return v___x_2437_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___boxed(lean_object* v_xs_2438_, lean_object* v_a_2439_, lean_object* v_preDefs_2440_, lean_object* v___x_2441_, lean_object* v_as_2442_, lean_object* v_i_2443_, lean_object* v_j_2444_, lean_object* v_inv_2445_, lean_object* v_bs_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_){
_start:
{
uint8_t v_a_29958__boxed_2452_; lean_object* v_res_2453_; 
v_a_29958__boxed_2452_ = lean_unbox(v_a_2439_);
v_res_2453_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18(v_xs_2438_, v_a_29958__boxed_2452_, v_preDefs_2440_, v___x_2441_, v_as_2442_, v_i_2443_, v_j_2444_, v_inv_2445_, v_bs_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_);
lean_dec(v___y_2450_);
lean_dec_ref(v___y_2449_);
lean_dec(v___y_2448_);
lean_dec_ref(v___y_2447_);
lean_dec_ref(v_as_2442_);
lean_dec_ref(v_preDefs_2440_);
lean_dec_ref(v_xs_2438_);
return v_res_2453_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19(lean_object* v_a_2454_, lean_object* v_funTypes_2455_, lean_object* v_as_2456_, lean_object* v_i_2457_, lean_object* v_j_2458_, lean_object* v_inv_2459_, lean_object* v_bs_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_){
_start:
{
lean_object* v___x_2466_; 
v___x_2466_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___redArg(v_a_2454_, v_funTypes_2455_, v_as_2456_, v_i_2457_, v_j_2458_, v_bs_2460_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_);
return v___x_2466_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___boxed(lean_object* v_a_2467_, lean_object* v_funTypes_2468_, lean_object* v_as_2469_, lean_object* v_i_2470_, lean_object* v_j_2471_, lean_object* v_inv_2472_, lean_object* v_bs_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_){
_start:
{
lean_object* v_res_2479_; 
v_res_2479_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19(v_a_2467_, v_funTypes_2468_, v_as_2469_, v_i_2470_, v_j_2471_, v_inv_2472_, v_bs_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_);
lean_dec(v___y_2477_);
lean_dec_ref(v___y_2476_);
lean_dec(v___y_2475_);
lean_dec_ref(v___y_2474_);
lean_dec_ref(v_as_2469_);
lean_dec_ref(v_funTypes_2468_);
lean_dec_ref(v_a_2467_);
return v_res_2479_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__20(lean_object* v_a_2480_, lean_object* v_a_2481_, lean_object* v_as_2482_, lean_object* v_i_2483_, lean_object* v_j_2484_, lean_object* v_inv_2485_, lean_object* v_bs_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_){
_start:
{
lean_object* v___x_2492_; 
v___x_2492_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__20___redArg(v_a_2480_, v_a_2481_, v_as_2482_, v_i_2483_, v_j_2484_, v_bs_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_);
return v___x_2492_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__20___boxed(lean_object* v_a_2493_, lean_object* v_a_2494_, lean_object* v_as_2495_, lean_object* v_i_2496_, lean_object* v_j_2497_, lean_object* v_inv_2498_, lean_object* v_bs_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_){
_start:
{
lean_object* v_res_2505_; 
v_res_2505_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__20(v_a_2493_, v_a_2494_, v_as_2495_, v_i_2496_, v_j_2497_, v_inv_2498_, v_bs_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_);
lean_dec(v___y_2503_);
lean_dec_ref(v___y_2502_);
lean_dec(v___y_2501_);
lean_dec_ref(v___y_2500_);
lean_dec_ref(v_as_2495_);
lean_dec_ref(v_a_2494_);
lean_dec_ref(v_a_2493_);
return v_res_2505_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4(lean_object* v_00_u03b1_2506_, lean_object* v_msg_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_){
_start:
{
lean_object* v___x_2513_; 
v___x_2513_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg(v_msg_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_);
return v___x_2513_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___boxed(lean_object* v_00_u03b1_2514_, lean_object* v_msg_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_){
_start:
{
lean_object* v_res_2521_; 
v_res_2521_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4(v_00_u03b1_2514_, v_msg_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_);
lean_dec(v___y_2519_);
lean_dec_ref(v___y_2518_);
lean_dec(v___y_2517_);
lean_dec_ref(v___y_2516_);
return v_res_2521_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__7(lean_object* v_00_u03b1_2522_, lean_object* v_inst_2523_, lean_object* v_xs_2524_, lean_object* v_f_2525_, lean_object* v_x_2526_, lean_object* v_as_2527_, size_t v_i_2528_, size_t v_stop_2529_, lean_object* v_b_2530_){
_start:
{
lean_object* v___x_2531_; 
v___x_2531_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__7___redArg(v_inst_2523_, v_xs_2524_, v_f_2525_, v_x_2526_, v_as_2527_, v_i_2528_, v_stop_2529_, v_b_2530_);
return v___x_2531_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__7___boxed(lean_object* v_00_u03b1_2532_, lean_object* v_inst_2533_, lean_object* v_xs_2534_, lean_object* v_f_2535_, lean_object* v_x_2536_, lean_object* v_as_2537_, lean_object* v_i_2538_, lean_object* v_stop_2539_, lean_object* v_b_2540_){
_start:
{
size_t v_i_boxed_2541_; size_t v_stop_boxed_2542_; lean_object* v_res_2543_; 
v_i_boxed_2541_ = lean_unbox_usize(v_i_2538_);
lean_dec(v_i_2538_);
v_stop_boxed_2542_ = lean_unbox_usize(v_stop_2539_);
lean_dec(v_stop_2539_);
v_res_2543_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__7(v_00_u03b1_2532_, v_inst_2533_, v_xs_2534_, v_f_2535_, v_x_2536_, v_as_2537_, v_i_boxed_2541_, v_stop_boxed_2542_, v_b_2540_);
lean_dec_ref(v_as_2537_);
lean_dec(v_x_2536_);
lean_dec_ref(v_xs_2534_);
return v_res_2543_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__9(lean_object* v_00_u03b1_2544_, lean_object* v_inst_2545_, lean_object* v_xs_2546_, lean_object* v_f_2547_, size_t v_sz_2548_, size_t v_i_2549_, lean_object* v_bs_2550_){
_start:
{
lean_object* v___x_2551_; 
v___x_2551_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__9___redArg(v_inst_2545_, v_xs_2546_, v_f_2547_, v_sz_2548_, v_i_2549_, v_bs_2550_);
return v___x_2551_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__9___boxed(lean_object* v_00_u03b1_2552_, lean_object* v_inst_2553_, lean_object* v_xs_2554_, lean_object* v_f_2555_, lean_object* v_sz_2556_, lean_object* v_i_2557_, lean_object* v_bs_2558_){
_start:
{
size_t v_sz_boxed_2559_; size_t v_i_boxed_2560_; lean_object* v_res_2561_; 
v_sz_boxed_2559_ = lean_unbox_usize(v_sz_2556_);
lean_dec(v_sz_2556_);
v_i_boxed_2560_ = lean_unbox_usize(v_i_2557_);
lean_dec(v_i_2557_);
v_res_2561_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__9(v_00_u03b1_2552_, v_inst_2553_, v_xs_2554_, v_f_2555_, v_sz_boxed_2559_, v_i_boxed_2560_, v_bs_2558_);
lean_dec_ref(v_xs_2554_);
return v_res_2561_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__10(lean_object* v_xs_2562_, lean_object* v_ys_2563_, lean_object* v_hsz_2564_, lean_object* v_x_2565_, lean_object* v_x_2566_){
_start:
{
uint8_t v___x_2567_; 
v___x_2567_ = l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__10___redArg(v_xs_2562_, v_ys_2563_, v_x_2565_);
return v___x_2567_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__10___boxed(lean_object* v_xs_2568_, lean_object* v_ys_2569_, lean_object* v_hsz_2570_, lean_object* v_x_2571_, lean_object* v_x_2572_){
_start:
{
uint8_t v_res_2573_; lean_object* v_r_2574_; 
v_res_2573_ = l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__10(v_xs_2568_, v_ys_2569_, v_hsz_2570_, v_x_2571_, v_x_2572_);
lean_dec_ref(v_ys_2569_);
lean_dec_ref(v_xs_2568_);
v_r_2574_ = lean_box(v_res_2573_);
return v_r_2574_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__11(lean_object* v_n_2575_, lean_object* v_as_2576_, lean_object* v_lo_2577_, lean_object* v_hi_2578_, lean_object* v_w_2579_, lean_object* v_hlo_2580_, lean_object* v_hhi_2581_){
_start:
{
lean_object* v___x_2582_; 
v___x_2582_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__11___redArg(v_as_2576_, v_lo_2577_, v_hi_2578_);
return v___x_2582_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__11___boxed(lean_object* v_n_2583_, lean_object* v_as_2584_, lean_object* v_lo_2585_, lean_object* v_hi_2586_, lean_object* v_w_2587_, lean_object* v_hlo_2588_, lean_object* v_hhi_2589_){
_start:
{
lean_object* v_res_2590_; 
v_res_2590_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__11(v_n_2583_, v_as_2584_, v_lo_2585_, v_hi_2586_, v_w_2587_, v_hlo_2588_, v_hhi_2589_);
lean_dec(v_hi_2586_);
lean_dec(v_n_2583_);
return v_res_2590_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__14(lean_object* v_00_u03b2_2591_, lean_object* v_inst_2592_, lean_object* v_xs_2593_, size_t v_sz_2594_, size_t v_i_2595_, lean_object* v_bs_2596_){
_start:
{
lean_object* v___x_2597_; 
v___x_2597_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__14___redArg(v_inst_2592_, v_xs_2593_, v_sz_2594_, v_i_2595_, v_bs_2596_);
return v___x_2597_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__14___boxed(lean_object* v_00_u03b2_2598_, lean_object* v_inst_2599_, lean_object* v_xs_2600_, lean_object* v_sz_2601_, lean_object* v_i_2602_, lean_object* v_bs_2603_){
_start:
{
size_t v_sz_boxed_2604_; size_t v_i_boxed_2605_; lean_object* v_res_2606_; 
v_sz_boxed_2604_ = lean_unbox_usize(v_sz_2601_);
lean_dec(v_sz_2601_);
v_i_boxed_2605_ = lean_unbox_usize(v_i_2602_);
lean_dec(v_i_2602_);
v_res_2606_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__14(v_00_u03b2_2598_, v_inst_2599_, v_xs_2600_, v_sz_boxed_2604_, v_i_boxed_2605_, v_bs_2603_);
lean_dec_ref(v_xs_2600_);
return v_res_2606_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__16(lean_object* v_00_u03b1_2607_, lean_object* v_00_u03b3_2608_, lean_object* v_00_u03b2_2609_, lean_object* v_inst_2610_, lean_object* v_xs_2611_, lean_object* v_f_2612_, lean_object* v_as_2613_, lean_object* v_bs_2614_, lean_object* v_i_2615_, lean_object* v_cs_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_){
_start:
{
lean_object* v___x_2622_; 
v___x_2622_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__16___redArg(v_inst_2610_, v_xs_2611_, v_f_2612_, v_as_2613_, v_bs_2614_, v_i_2615_, v_cs_2616_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_);
return v___x_2622_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__16___boxed(lean_object* v_00_u03b1_2623_, lean_object* v_00_u03b3_2624_, lean_object* v_00_u03b2_2625_, lean_object* v_inst_2626_, lean_object* v_xs_2627_, lean_object* v_f_2628_, lean_object* v_as_2629_, lean_object* v_bs_2630_, lean_object* v_i_2631_, lean_object* v_cs_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_){
_start:
{
lean_object* v_res_2638_; 
v_res_2638_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__16(v_00_u03b1_2623_, v_00_u03b3_2624_, v_00_u03b2_2625_, v_inst_2626_, v_xs_2627_, v_f_2628_, v_as_2629_, v_bs_2630_, v_i_2631_, v_cs_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_);
lean_dec(v___y_2636_);
lean_dec_ref(v___y_2635_);
lean_dec(v___y_2634_);
lean_dec_ref(v___y_2633_);
lean_dec_ref(v_bs_2630_);
lean_dec_ref(v_as_2629_);
lean_dec_ref(v_xs_2627_);
return v_res_2638_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13_spec__24_spec__26(lean_object* v_env_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_){
_start:
{
lean_object* v___x_2645_; 
v___x_2645_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13_spec__24_spec__26___redArg(v_env_2639_, v___y_2641_, v___y_2643_);
return v___x_2645_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13_spec__24_spec__26___boxed(lean_object* v_env_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_){
_start:
{
lean_object* v_res_2652_; 
v_res_2652_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13_spec__24_spec__26(v_env_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_);
lean_dec(v___y_2650_);
lean_dec_ref(v___y_2649_);
lean_dec(v___y_2648_);
lean_dec_ref(v___y_2647_);
return v_res_2652_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13_spec__24(lean_object* v_00_u03b1_2653_, lean_object* v_env_2654_, lean_object* v_x_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_){
_start:
{
lean_object* v___x_2661_; 
v___x_2661_ = l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13_spec__24___redArg(v_env_2654_, v_x_2655_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_);
return v___x_2661_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13_spec__24___boxed(lean_object* v_00_u03b1_2662_, lean_object* v_env_2663_, lean_object* v_x_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_){
_start:
{
lean_object* v_res_2670_; 
v_res_2670_ = l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13_spec__24(v_00_u03b1_2662_, v_env_2663_, v_x_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_);
lean_dec(v___y_2668_);
lean_dec_ref(v___y_2667_);
lean_dec(v___y_2666_);
lean_dec_ref(v___y_2665_);
return v_res_2670_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__9_spec__10(lean_object* v_00_u03b1_2671_, lean_object* v_xs_2672_, lean_object* v_inst_2673_, lean_object* v_f_2674_, size_t v_sz_2675_, size_t v_i_2676_, lean_object* v_bs_2677_){
_start:
{
lean_object* v___x_2678_; 
v___x_2678_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__9_spec__10___redArg(v_xs_2672_, v_inst_2673_, v_f_2674_, v_sz_2675_, v_i_2676_, v_bs_2677_);
return v___x_2678_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__9_spec__10___boxed(lean_object* v_00_u03b1_2679_, lean_object* v_xs_2680_, lean_object* v_inst_2681_, lean_object* v_f_2682_, lean_object* v_sz_2683_, lean_object* v_i_2684_, lean_object* v_bs_2685_){
_start:
{
size_t v_sz_boxed_2686_; size_t v_i_boxed_2687_; lean_object* v_res_2688_; 
v_sz_boxed_2686_ = lean_unbox_usize(v_sz_2683_);
lean_dec(v_sz_2683_);
v_i_boxed_2687_ = lean_unbox_usize(v_i_2684_);
lean_dec(v_i_2684_);
v_res_2688_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__9_spec__10(v_00_u03b1_2679_, v_xs_2680_, v_inst_2681_, v_f_2682_, v_sz_boxed_2686_, v_i_boxed_2687_, v_bs_2685_);
lean_dec_ref(v_xs_2680_);
return v_res_2688_;
}
}
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___lam__0(lean_object* v_x_2689_){
_start:
{
uint8_t v___x_2690_; 
v___x_2690_ = 0;
return v___x_2690_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___lam__0___boxed(lean_object* v_x_2691_){
_start:
{
uint8_t v_res_2692_; lean_object* v_r_2693_; 
v_res_2692_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___lam__0(v_x_2691_);
lean_dec(v_x_2691_);
v_r_2693_ = lean_box(v_res_2692_);
return v_r_2693_;
}
}
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___lam__1(lean_object* v_fvarId_2694_, lean_object* v_x_2695_){
_start:
{
uint8_t v___x_2696_; 
v___x_2696_ = l_Lean_instBEqFVarId_beq(v_fvarId_2694_, v_x_2695_);
return v___x_2696_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___lam__1___boxed(lean_object* v_fvarId_2697_, lean_object* v_x_2698_){
_start:
{
uint8_t v_res_2699_; lean_object* v_r_2700_; 
v_res_2699_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___lam__1(v_fvarId_2697_, v_x_2698_);
lean_dec(v_x_2698_);
lean_dec(v_fvarId_2697_);
v_r_2700_ = lean_box(v_res_2699_);
return v_r_2700_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; 
v___x_2702_ = lean_box(0);
v___x_2703_ = lean_unsigned_to_nat(16u);
v___x_2704_ = lean_mk_array(v___x_2703_, v___x_2702_);
return v___x_2704_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; 
v___x_2705_ = lean_obj_once(&l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__1, &l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__1_once, _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__1);
v___x_2706_ = lean_unsigned_to_nat(0u);
v___x_2707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2707_, 0, v___x_2706_);
lean_ctor_set(v___x_2707_, 1, v___x_2705_);
return v___x_2707_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg(lean_object* v_e_2708_, lean_object* v_fvarId_2709_, lean_object* v___y_2710_){
_start:
{
lean_object* v___x_2712_; uint8_t v_fst_2714_; lean_object* v_mctx_2715_; lean_object* v___y_2733_; lean_object* v_mctx_2738_; lean_object* v___f_2739_; lean_object* v___f_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; uint8_t v___x_2743_; 
v___x_2712_ = lean_st_ref_get(v___y_2710_);
v_mctx_2738_ = lean_ctor_get(v___x_2712_, 0);
lean_inc_ref(v_mctx_2738_);
lean_dec(v___x_2712_);
v___f_2739_ = ((lean_object*)(l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__0));
v___f_2740_ = lean_alloc_closure((void*)(l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_2740_, 0, v_fvarId_2709_);
v___x_2741_ = lean_obj_once(&l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__2, &l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__2_once, _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__2);
lean_inc_ref(v_mctx_2738_);
v___x_2742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2742_, 0, v___x_2741_);
lean_ctor_set(v___x_2742_, 1, v_mctx_2738_);
v___x_2743_ = l_Lean_Expr_hasFVar(v_e_2708_);
if (v___x_2743_ == 0)
{
uint8_t v___x_2744_; 
v___x_2744_ = l_Lean_Expr_hasMVar(v_e_2708_);
if (v___x_2744_ == 0)
{
lean_dec_ref(v___x_2742_);
lean_dec_ref(v___f_2740_);
lean_dec_ref(v_e_2708_);
v_fst_2714_ = v___x_2744_;
v_mctx_2715_ = v_mctx_2738_;
goto v___jp_2713_;
}
else
{
lean_object* v___x_2745_; 
lean_dec_ref(v_mctx_2738_);
v___x_2745_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2740_, v___f_2739_, v_e_2708_, v___x_2742_);
v___y_2733_ = v___x_2745_;
goto v___jp_2732_;
}
}
else
{
lean_object* v___x_2746_; 
lean_dec_ref(v_mctx_2738_);
v___x_2746_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2740_, v___f_2739_, v_e_2708_, v___x_2742_);
v___y_2733_ = v___x_2746_;
goto v___jp_2732_;
}
v___jp_2713_:
{
lean_object* v___x_2716_; lean_object* v_cache_2717_; lean_object* v_zetaDeltaFVarIds_2718_; lean_object* v_postponed_2719_; lean_object* v_diag_2720_; lean_object* v___x_2722_; uint8_t v_isShared_2723_; uint8_t v_isSharedCheck_2730_; 
v___x_2716_ = lean_st_ref_take(v___y_2710_);
v_cache_2717_ = lean_ctor_get(v___x_2716_, 1);
v_zetaDeltaFVarIds_2718_ = lean_ctor_get(v___x_2716_, 2);
v_postponed_2719_ = lean_ctor_get(v___x_2716_, 3);
v_diag_2720_ = lean_ctor_get(v___x_2716_, 4);
v_isSharedCheck_2730_ = !lean_is_exclusive(v___x_2716_);
if (v_isSharedCheck_2730_ == 0)
{
lean_object* v_unused_2731_; 
v_unused_2731_ = lean_ctor_get(v___x_2716_, 0);
lean_dec(v_unused_2731_);
v___x_2722_ = v___x_2716_;
v_isShared_2723_ = v_isSharedCheck_2730_;
goto v_resetjp_2721_;
}
else
{
lean_inc(v_diag_2720_);
lean_inc(v_postponed_2719_);
lean_inc(v_zetaDeltaFVarIds_2718_);
lean_inc(v_cache_2717_);
lean_dec(v___x_2716_);
v___x_2722_ = lean_box(0);
v_isShared_2723_ = v_isSharedCheck_2730_;
goto v_resetjp_2721_;
}
v_resetjp_2721_:
{
lean_object* v___x_2725_; 
if (v_isShared_2723_ == 0)
{
lean_ctor_set(v___x_2722_, 0, v_mctx_2715_);
v___x_2725_ = v___x_2722_;
goto v_reusejp_2724_;
}
else
{
lean_object* v_reuseFailAlloc_2729_; 
v_reuseFailAlloc_2729_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2729_, 0, v_mctx_2715_);
lean_ctor_set(v_reuseFailAlloc_2729_, 1, v_cache_2717_);
lean_ctor_set(v_reuseFailAlloc_2729_, 2, v_zetaDeltaFVarIds_2718_);
lean_ctor_set(v_reuseFailAlloc_2729_, 3, v_postponed_2719_);
lean_ctor_set(v_reuseFailAlloc_2729_, 4, v_diag_2720_);
v___x_2725_ = v_reuseFailAlloc_2729_;
goto v_reusejp_2724_;
}
v_reusejp_2724_:
{
lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; 
v___x_2726_ = lean_st_ref_set(v___y_2710_, v___x_2725_);
v___x_2727_ = lean_box(v_fst_2714_);
v___x_2728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2728_, 0, v___x_2727_);
return v___x_2728_;
}
}
}
v___jp_2732_:
{
lean_object* v_snd_2734_; lean_object* v_fst_2735_; lean_object* v_mctx_2736_; uint8_t v___x_2737_; 
v_snd_2734_ = lean_ctor_get(v___y_2733_, 1);
lean_inc(v_snd_2734_);
v_fst_2735_ = lean_ctor_get(v___y_2733_, 0);
lean_inc(v_fst_2735_);
lean_dec_ref(v___y_2733_);
v_mctx_2736_ = lean_ctor_get(v_snd_2734_, 1);
lean_inc_ref(v_mctx_2736_);
lean_dec(v_snd_2734_);
v___x_2737_ = lean_unbox(v_fst_2735_);
lean_dec(v_fst_2735_);
v_fst_2714_ = v___x_2737_;
v_mctx_2715_ = v_mctx_2736_;
goto v___jp_2713_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___boxed(lean_object* v_e_2747_, lean_object* v_fvarId_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_){
_start:
{
lean_object* v_res_2751_; 
v_res_2751_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg(v_e_2747_, v_fvarId_2748_, v___y_2749_);
lean_dec(v___y_2749_);
return v_res_2751_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5(lean_object* v_e_2752_, lean_object* v_fvarId_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_){
_start:
{
lean_object* v___x_2759_; 
v___x_2759_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg(v_e_2752_, v_fvarId_2753_, v___y_2755_);
return v___x_2759_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___boxed(lean_object* v_e_2760_, lean_object* v_fvarId_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_){
_start:
{
lean_object* v_res_2767_; 
v_res_2767_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5(v_e_2760_, v_fvarId_2761_, v___y_2762_, v___y_2763_, v___y_2764_, v___y_2765_);
lean_dec(v___y_2765_);
lean_dec_ref(v___y_2764_);
lean_dec(v___y_2763_);
lean_dec_ref(v___y_2762_);
return v_res_2767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg___lam__0(lean_object* v_k_2768_, lean_object* v_b_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_){
_start:
{
lean_object* v___x_2775_; 
lean_inc(v___y_2773_);
lean_inc_ref(v___y_2772_);
lean_inc(v___y_2771_);
lean_inc_ref(v___y_2770_);
v___x_2775_ = lean_apply_6(v_k_2768_, v_b_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_, lean_box(0));
return v___x_2775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg___lam__0___boxed(lean_object* v_k_2776_, lean_object* v_b_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_){
_start:
{
lean_object* v_res_2783_; 
v_res_2783_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg___lam__0(v_k_2776_, v_b_2777_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_);
lean_dec(v___y_2781_);
lean_dec_ref(v___y_2780_);
lean_dec(v___y_2779_);
lean_dec_ref(v___y_2778_);
return v_res_2783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg(lean_object* v_perm_2784_, lean_object* v_type_2785_, lean_object* v_k_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_){
_start:
{
lean_object* v___f_2792_; lean_object* v___x_2793_; 
v___f_2792_ = lean_alloc_closure((void*)(l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2792_, 0, v_k_2786_);
v___x_2793_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl(lean_box(0), v_perm_2784_, v_type_2785_, v___f_2792_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_);
if (lean_obj_tag(v___x_2793_) == 0)
{
lean_object* v_a_2794_; lean_object* v___x_2796_; uint8_t v_isShared_2797_; uint8_t v_isSharedCheck_2801_; 
v_a_2794_ = lean_ctor_get(v___x_2793_, 0);
v_isSharedCheck_2801_ = !lean_is_exclusive(v___x_2793_);
if (v_isSharedCheck_2801_ == 0)
{
v___x_2796_ = v___x_2793_;
v_isShared_2797_ = v_isSharedCheck_2801_;
goto v_resetjp_2795_;
}
else
{
lean_inc(v_a_2794_);
lean_dec(v___x_2793_);
v___x_2796_ = lean_box(0);
v_isShared_2797_ = v_isSharedCheck_2801_;
goto v_resetjp_2795_;
}
v_resetjp_2795_:
{
lean_object* v___x_2799_; 
if (v_isShared_2797_ == 0)
{
v___x_2799_ = v___x_2796_;
goto v_reusejp_2798_;
}
else
{
lean_object* v_reuseFailAlloc_2800_; 
v_reuseFailAlloc_2800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2800_, 0, v_a_2794_);
v___x_2799_ = v_reuseFailAlloc_2800_;
goto v_reusejp_2798_;
}
v_reusejp_2798_:
{
return v___x_2799_;
}
}
}
else
{
lean_object* v_a_2802_; lean_object* v___x_2804_; uint8_t v_isShared_2805_; uint8_t v_isSharedCheck_2809_; 
v_a_2802_ = lean_ctor_get(v___x_2793_, 0);
v_isSharedCheck_2809_ = !lean_is_exclusive(v___x_2793_);
if (v_isSharedCheck_2809_ == 0)
{
v___x_2804_ = v___x_2793_;
v_isShared_2805_ = v_isSharedCheck_2809_;
goto v_resetjp_2803_;
}
else
{
lean_inc(v_a_2802_);
lean_dec(v___x_2793_);
v___x_2804_ = lean_box(0);
v_isShared_2805_ = v_isSharedCheck_2809_;
goto v_resetjp_2803_;
}
v_resetjp_2803_:
{
lean_object* v___x_2807_; 
if (v_isShared_2805_ == 0)
{
v___x_2807_ = v___x_2804_;
goto v_reusejp_2806_;
}
else
{
lean_object* v_reuseFailAlloc_2808_; 
v_reuseFailAlloc_2808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2808_, 0, v_a_2802_);
v___x_2807_ = v_reuseFailAlloc_2808_;
goto v_reusejp_2806_;
}
v_reusejp_2806_:
{
return v___x_2807_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg___boxed(lean_object* v_perm_2810_, lean_object* v_type_2811_, lean_object* v_k_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_){
_start:
{
lean_object* v_res_2818_; 
v_res_2818_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg(v_perm_2810_, v_type_2811_, v_k_2812_, v___y_2813_, v___y_2814_, v___y_2815_, v___y_2816_);
lean_dec(v___y_2816_);
lean_dec_ref(v___y_2815_);
lean_dec(v___y_2814_);
lean_dec_ref(v___y_2813_);
return v_res_2818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13(lean_object* v_00_u03b1_2819_, lean_object* v_perm_2820_, lean_object* v_type_2821_, lean_object* v_k_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_){
_start:
{
lean_object* v___x_2828_; 
v___x_2828_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg(v_perm_2820_, v_type_2821_, v_k_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_);
return v___x_2828_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___boxed(lean_object* v_00_u03b1_2829_, lean_object* v_perm_2830_, lean_object* v_type_2831_, lean_object* v_k_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_){
_start:
{
lean_object* v_res_2838_; 
v_res_2838_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13(v_00_u03b1_2829_, v_perm_2830_, v_type_2831_, v_k_2832_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_);
lean_dec(v___y_2836_);
lean_dec_ref(v___y_2835_);
lean_dec(v___y_2834_);
lean_dec_ref(v___y_2833_);
return v_res_2838_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0(lean_object* v_a_2839_, lean_object* v_fst_2840_, lean_object* v_fst_2841_, lean_object* v___x_2842_, lean_object* v___x_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_){
_start:
{
lean_object* v___x_2849_; 
lean_inc_ref(v_fst_2840_);
v___x_2849_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion(v_a_2839_, v_fst_2840_, v_fst_2841_, v___x_2842_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_);
if (lean_obj_tag(v___x_2849_) == 0)
{
lean_object* v_a_2850_; lean_object* v___x_2852_; uint8_t v_isShared_2853_; uint8_t v_isSharedCheck_2859_; 
v_a_2850_ = lean_ctor_get(v___x_2849_, 0);
v_isSharedCheck_2859_ = !lean_is_exclusive(v___x_2849_);
if (v_isSharedCheck_2859_ == 0)
{
v___x_2852_ = v___x_2849_;
v_isShared_2853_ = v_isSharedCheck_2859_;
goto v_resetjp_2851_;
}
else
{
lean_inc(v_a_2850_);
lean_dec(v___x_2849_);
v___x_2852_ = lean_box(0);
v_isShared_2853_ = v_isSharedCheck_2859_;
goto v_resetjp_2851_;
}
v_resetjp_2851_:
{
lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2857_; 
v___x_2854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2854_, 0, v_a_2850_);
lean_ctor_set(v___x_2854_, 1, v_fst_2840_);
v___x_2855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2855_, 0, v___x_2843_);
lean_ctor_set(v___x_2855_, 1, v___x_2854_);
if (v_isShared_2853_ == 0)
{
lean_ctor_set(v___x_2852_, 0, v___x_2855_);
v___x_2857_ = v___x_2852_;
goto v_reusejp_2856_;
}
else
{
lean_object* v_reuseFailAlloc_2858_; 
v_reuseFailAlloc_2858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2858_, 0, v___x_2855_);
v___x_2857_ = v_reuseFailAlloc_2858_;
goto v_reusejp_2856_;
}
v_reusejp_2856_:
{
return v___x_2857_;
}
}
}
else
{
lean_object* v_a_2860_; lean_object* v___x_2862_; uint8_t v_isShared_2863_; uint8_t v_isSharedCheck_2867_; 
lean_dec_ref(v___x_2843_);
lean_dec_ref(v_fst_2840_);
v_a_2860_ = lean_ctor_get(v___x_2849_, 0);
v_isSharedCheck_2867_ = !lean_is_exclusive(v___x_2849_);
if (v_isSharedCheck_2867_ == 0)
{
v___x_2862_ = v___x_2849_;
v_isShared_2863_ = v_isSharedCheck_2867_;
goto v_resetjp_2861_;
}
else
{
lean_inc(v_a_2860_);
lean_dec(v___x_2849_);
v___x_2862_ = lean_box(0);
v_isShared_2863_ = v_isSharedCheck_2867_;
goto v_resetjp_2861_;
}
v_resetjp_2861_:
{
lean_object* v___x_2865_; 
if (v_isShared_2863_ == 0)
{
v___x_2865_ = v___x_2862_;
goto v_reusejp_2864_;
}
else
{
lean_object* v_reuseFailAlloc_2866_; 
v_reuseFailAlloc_2866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2866_, 0, v_a_2860_);
v___x_2865_ = v_reuseFailAlloc_2866_;
goto v_reusejp_2864_;
}
v_reusejp_2864_:
{
return v___x_2865_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___boxed(lean_object* v_a_2868_, lean_object* v_fst_2869_, lean_object* v_fst_2870_, lean_object* v___x_2871_, lean_object* v___x_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_){
_start:
{
lean_object* v_res_2878_; 
v_res_2878_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0(v_a_2868_, v_fst_2869_, v_fst_2870_, v___x_2871_, v___x_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_);
lean_dec(v___y_2876_);
lean_dec_ref(v___y_2875_);
lean_dec(v___y_2874_);
lean_dec_ref(v___y_2873_);
return v_res_2878_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__3(size_t v_sz_2879_, size_t v_i_2880_, lean_object* v_bs_2881_){
_start:
{
uint8_t v___x_2882_; 
v___x_2882_ = lean_usize_dec_lt(v_i_2880_, v_sz_2879_);
if (v___x_2882_ == 0)
{
return v_bs_2881_;
}
else
{
lean_object* v_v_2883_; lean_object* v___x_2884_; lean_object* v_bs_x27_2885_; lean_object* v___x_2886_; size_t v___x_2887_; size_t v___x_2888_; lean_object* v___x_2889_; 
v_v_2883_ = lean_array_uget(v_bs_2881_, v_i_2880_);
v___x_2884_ = lean_unsigned_to_nat(0u);
v_bs_x27_2885_ = lean_array_uset(v_bs_2881_, v_i_2880_, v___x_2884_);
v___x_2886_ = l_Lean_Elab_Structural_RecArgInfo_indicesAndRecArgPos(v_v_2883_);
v___x_2887_ = ((size_t)1ULL);
v___x_2888_ = lean_usize_add(v_i_2880_, v___x_2887_);
v___x_2889_ = lean_array_uset(v_bs_x27_2885_, v_i_2880_, v___x_2886_);
v_i_2880_ = v___x_2888_;
v_bs_2881_ = v___x_2889_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__3___boxed(lean_object* v_sz_2891_, lean_object* v_i_2892_, lean_object* v_bs_2893_){
_start:
{
size_t v_sz_boxed_2894_; size_t v_i_boxed_2895_; lean_object* v_res_2896_; 
v_sz_boxed_2894_ = lean_unbox_usize(v_sz_2891_);
lean_dec(v_sz_2891_);
v_i_boxed_2895_ = lean_unbox_usize(v_i_2892_);
lean_dec(v_i_2892_);
v_res_2896_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__3(v_sz_boxed_2894_, v_i_boxed_2895_, v_bs_2893_);
return v_res_2896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___redArg(lean_object* v_lctx_2897_, lean_object* v_localInsts_2898_, lean_object* v_x_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_){
_start:
{
lean_object* v___x_2905_; 
v___x_2905_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_2897_, v_localInsts_2898_, v_x_2899_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_);
if (lean_obj_tag(v___x_2905_) == 0)
{
lean_object* v_a_2906_; lean_object* v___x_2908_; uint8_t v_isShared_2909_; uint8_t v_isSharedCheck_2913_; 
v_a_2906_ = lean_ctor_get(v___x_2905_, 0);
v_isSharedCheck_2913_ = !lean_is_exclusive(v___x_2905_);
if (v_isSharedCheck_2913_ == 0)
{
v___x_2908_ = v___x_2905_;
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
else
{
lean_inc(v_a_2906_);
lean_dec(v___x_2905_);
v___x_2908_ = lean_box(0);
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
v_resetjp_2907_:
{
lean_object* v___x_2911_; 
if (v_isShared_2909_ == 0)
{
v___x_2911_ = v___x_2908_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v_a_2906_);
v___x_2911_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
return v___x_2911_;
}
}
}
else
{
lean_object* v_a_2914_; lean_object* v___x_2916_; uint8_t v_isShared_2917_; uint8_t v_isSharedCheck_2921_; 
v_a_2914_ = lean_ctor_get(v___x_2905_, 0);
v_isSharedCheck_2921_ = !lean_is_exclusive(v___x_2905_);
if (v_isSharedCheck_2921_ == 0)
{
v___x_2916_ = v___x_2905_;
v_isShared_2917_ = v_isSharedCheck_2921_;
goto v_resetjp_2915_;
}
else
{
lean_inc(v_a_2914_);
lean_dec(v___x_2905_);
v___x_2916_ = lean_box(0);
v_isShared_2917_ = v_isSharedCheck_2921_;
goto v_resetjp_2915_;
}
v_resetjp_2915_:
{
lean_object* v___x_2919_; 
if (v_isShared_2917_ == 0)
{
v___x_2919_ = v___x_2916_;
goto v_reusejp_2918_;
}
else
{
lean_object* v_reuseFailAlloc_2920_; 
v_reuseFailAlloc_2920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2920_, 0, v_a_2914_);
v___x_2919_ = v_reuseFailAlloc_2920_;
goto v_reusejp_2918_;
}
v_reusejp_2918_:
{
return v___x_2919_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___redArg___boxed(lean_object* v_lctx_2922_, lean_object* v_localInsts_2923_, lean_object* v_x_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_){
_start:
{
lean_object* v_res_2930_; 
v_res_2930_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___redArg(v_lctx_2922_, v_localInsts_2923_, v_x_2924_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_);
lean_dec(v___y_2928_);
lean_dec_ref(v___y_2927_);
lean_dec(v___y_2926_);
lean_dec_ref(v___y_2925_);
return v_res_2930_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__12(lean_object* v_as_2931_, size_t v_i_2932_, size_t v_stop_2933_, lean_object* v_b_2934_){
_start:
{
uint8_t v___x_2935_; 
v___x_2935_ = lean_usize_dec_eq(v_i_2932_, v_stop_2933_);
if (v___x_2935_ == 0)
{
lean_object* v___x_2936_; lean_object* v___x_2937_; size_t v___x_2938_; size_t v___x_2939_; 
v___x_2936_ = lean_array_uget_borrowed(v_as_2931_, v_i_2932_);
lean_inc(v___x_2936_);
v___x_2937_ = lean_local_ctx_erase(v_b_2934_, v___x_2936_);
v___x_2938_ = ((size_t)1ULL);
v___x_2939_ = lean_usize_add(v_i_2932_, v___x_2938_);
v_i_2932_ = v___x_2939_;
v_b_2934_ = v___x_2937_;
goto _start;
}
else
{
return v_b_2934_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__12___boxed(lean_object* v_as_2941_, lean_object* v_i_2942_, lean_object* v_stop_2943_, lean_object* v_b_2944_){
_start:
{
size_t v_i_boxed_2945_; size_t v_stop_boxed_2946_; lean_object* v_res_2947_; 
v_i_boxed_2945_ = lean_unbox_usize(v_i_2942_);
lean_dec(v_i_2942_);
v_stop_boxed_2946_ = lean_unbox_usize(v_stop_2943_);
lean_dec(v_stop_2943_);
v_res_2947_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__12(v_as_2941_, v_i_boxed_2945_, v_stop_boxed_2946_, v_b_2944_);
lean_dec_ref(v_as_2941_);
return v_res_2947_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9_spec__11(lean_object* v_a_2948_, lean_object* v_as_2949_, size_t v_i_2950_, size_t v_stop_2951_){
_start:
{
uint8_t v___x_2952_; 
v___x_2952_ = lean_usize_dec_eq(v_i_2950_, v_stop_2951_);
if (v___x_2952_ == 0)
{
lean_object* v___x_2953_; uint8_t v___x_2954_; 
v___x_2953_ = lean_array_uget_borrowed(v_as_2949_, v_i_2950_);
v___x_2954_ = l_Lean_instBEqFVarId_beq(v_a_2948_, v___x_2953_);
if (v___x_2954_ == 0)
{
size_t v___x_2955_; size_t v___x_2956_; 
v___x_2955_ = ((size_t)1ULL);
v___x_2956_ = lean_usize_add(v_i_2950_, v___x_2955_);
v_i_2950_ = v___x_2956_;
goto _start;
}
else
{
return v___x_2954_;
}
}
else
{
uint8_t v___x_2958_; 
v___x_2958_ = 0;
return v___x_2958_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9_spec__11___boxed(lean_object* v_a_2959_, lean_object* v_as_2960_, lean_object* v_i_2961_, lean_object* v_stop_2962_){
_start:
{
size_t v_i_boxed_2963_; size_t v_stop_boxed_2964_; uint8_t v_res_2965_; lean_object* v_r_2966_; 
v_i_boxed_2963_ = lean_unbox_usize(v_i_2961_);
lean_dec(v_i_2961_);
v_stop_boxed_2964_ = lean_unbox_usize(v_stop_2962_);
lean_dec(v_stop_2962_);
v_res_2965_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9_spec__11(v_a_2959_, v_as_2960_, v_i_boxed_2963_, v_stop_boxed_2964_);
lean_dec_ref(v_as_2960_);
lean_dec(v_a_2959_);
v_r_2966_ = lean_box(v_res_2965_);
return v_r_2966_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9(lean_object* v_as_2967_, lean_object* v_a_2968_){
_start:
{
lean_object* v___x_2969_; lean_object* v___x_2970_; uint8_t v___x_2971_; 
v___x_2969_ = lean_unsigned_to_nat(0u);
v___x_2970_ = lean_array_get_size(v_as_2967_);
v___x_2971_ = lean_nat_dec_lt(v___x_2969_, v___x_2970_);
if (v___x_2971_ == 0)
{
return v___x_2971_;
}
else
{
if (v___x_2971_ == 0)
{
return v___x_2971_;
}
else
{
size_t v___x_2972_; size_t v___x_2973_; uint8_t v___x_2974_; 
v___x_2972_ = ((size_t)0ULL);
v___x_2973_ = lean_usize_of_nat(v___x_2970_);
v___x_2974_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9_spec__11(v_a_2968_, v_as_2967_, v___x_2972_, v___x_2973_);
return v___x_2974_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9___boxed(lean_object* v_as_2975_, lean_object* v_a_2976_){
_start:
{
uint8_t v_res_2977_; lean_object* v_r_2978_; 
v_res_2977_ = l_Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9(v_as_2975_, v_a_2976_);
lean_dec(v_a_2976_);
lean_dec_ref(v_as_2975_);
v_r_2978_ = lean_box(v_res_2977_);
return v_r_2978_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__11(lean_object* v_fvarIds_2979_, lean_object* v_as_2980_, size_t v_i_2981_, size_t v_stop_2982_, lean_object* v_b_2983_){
_start:
{
lean_object* v___y_2985_; uint8_t v___x_2989_; 
v___x_2989_ = lean_usize_dec_eq(v_i_2981_, v_stop_2982_);
if (v___x_2989_ == 0)
{
lean_object* v___x_2990_; lean_object* v_fvar_2991_; lean_object* v___x_2992_; uint8_t v___x_2993_; 
v___x_2990_ = lean_array_uget_borrowed(v_as_2980_, v_i_2981_);
v_fvar_2991_ = lean_ctor_get(v___x_2990_, 1);
v___x_2992_ = l_Lean_Expr_fvarId_x21(v_fvar_2991_);
v___x_2993_ = l_Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9(v_fvarIds_2979_, v___x_2992_);
lean_dec(v___x_2992_);
if (v___x_2993_ == 0)
{
lean_object* v___x_2994_; 
lean_inc(v___x_2990_);
v___x_2994_ = lean_array_push(v_b_2983_, v___x_2990_);
v___y_2985_ = v___x_2994_;
goto v___jp_2984_;
}
else
{
v___y_2985_ = v_b_2983_;
goto v___jp_2984_;
}
}
else
{
return v_b_2983_;
}
v___jp_2984_:
{
size_t v___x_2986_; size_t v___x_2987_; 
v___x_2986_ = ((size_t)1ULL);
v___x_2987_ = lean_usize_add(v_i_2981_, v___x_2986_);
v_i_2981_ = v___x_2987_;
v_b_2983_ = v___y_2985_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__11___boxed(lean_object* v_fvarIds_2995_, lean_object* v_as_2996_, lean_object* v_i_2997_, lean_object* v_stop_2998_, lean_object* v_b_2999_){
_start:
{
size_t v_i_boxed_3000_; size_t v_stop_boxed_3001_; lean_object* v_res_3002_; 
v_i_boxed_3000_ = lean_unbox_usize(v_i_2997_);
lean_dec(v_i_2997_);
v_stop_boxed_3001_ = lean_unbox_usize(v_stop_2998_);
lean_dec(v_stop_2998_);
v_res_3002_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__11(v_fvarIds_2995_, v_as_2996_, v_i_boxed_3000_, v_stop_boxed_3001_, v_b_2999_);
lean_dec_ref(v_as_2996_);
lean_dec_ref(v_fvarIds_2995_);
return v_res_3002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___redArg(lean_object* v_fvarIds_3005_, lean_object* v_k_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_){
_start:
{
lean_object* v_lctx_3012_; lean_object* v___x_3013_; 
v_lctx_3012_ = lean_ctor_get(v___y_3007_, 2);
v___x_3013_ = l_Lean_Meta_getLocalInstances___redArg(v___y_3007_);
if (lean_obj_tag(v___x_3013_) == 0)
{
lean_object* v_a_3014_; lean_object* v___x_3015_; lean_object* v___y_3017_; lean_object* v___x_3032_; uint8_t v___x_3033_; 
v_a_3014_ = lean_ctor_get(v___x_3013_, 0);
lean_inc(v_a_3014_);
lean_dec_ref(v___x_3013_);
v___x_3015_ = lean_unsigned_to_nat(0u);
v___x_3032_ = lean_array_get_size(v_fvarIds_3005_);
v___x_3033_ = lean_nat_dec_lt(v___x_3015_, v___x_3032_);
if (v___x_3033_ == 0)
{
lean_inc_ref(v_lctx_3012_);
v___y_3017_ = v_lctx_3012_;
goto v___jp_3016_;
}
else
{
uint8_t v___x_3034_; 
v___x_3034_ = lean_nat_dec_le(v___x_3032_, v___x_3032_);
if (v___x_3034_ == 0)
{
if (v___x_3033_ == 0)
{
lean_inc_ref(v_lctx_3012_);
v___y_3017_ = v_lctx_3012_;
goto v___jp_3016_;
}
else
{
size_t v___x_3035_; size_t v___x_3036_; lean_object* v___x_3037_; 
v___x_3035_ = ((size_t)0ULL);
v___x_3036_ = lean_usize_of_nat(v___x_3032_);
lean_inc_ref(v_lctx_3012_);
v___x_3037_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__12(v_fvarIds_3005_, v___x_3035_, v___x_3036_, v_lctx_3012_);
v___y_3017_ = v___x_3037_;
goto v___jp_3016_;
}
}
else
{
size_t v___x_3038_; size_t v___x_3039_; lean_object* v___x_3040_; 
v___x_3038_ = ((size_t)0ULL);
v___x_3039_ = lean_usize_of_nat(v___x_3032_);
lean_inc_ref(v_lctx_3012_);
v___x_3040_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__12(v_fvarIds_3005_, v___x_3038_, v___x_3039_, v_lctx_3012_);
v___y_3017_ = v___x_3040_;
goto v___jp_3016_;
}
}
v___jp_3016_:
{
lean_object* v___x_3018_; lean_object* v___x_3019_; uint8_t v___x_3020_; 
v___x_3018_ = lean_array_get_size(v_a_3014_);
v___x_3019_ = ((lean_object*)(l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___redArg___closed__0));
v___x_3020_ = lean_nat_dec_lt(v___x_3015_, v___x_3018_);
if (v___x_3020_ == 0)
{
lean_object* v___x_3021_; 
lean_dec(v_a_3014_);
v___x_3021_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___redArg(v___y_3017_, v___x_3019_, v_k_3006_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_);
lean_dec_ref(v___y_3007_);
return v___x_3021_;
}
else
{
uint8_t v___x_3022_; 
v___x_3022_ = lean_nat_dec_le(v___x_3018_, v___x_3018_);
if (v___x_3022_ == 0)
{
if (v___x_3020_ == 0)
{
lean_object* v___x_3023_; 
lean_dec(v_a_3014_);
v___x_3023_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___redArg(v___y_3017_, v___x_3019_, v_k_3006_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_);
lean_dec_ref(v___y_3007_);
return v___x_3023_;
}
else
{
size_t v___x_3024_; size_t v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; 
v___x_3024_ = ((size_t)0ULL);
v___x_3025_ = lean_usize_of_nat(v___x_3018_);
v___x_3026_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__11(v_fvarIds_3005_, v_a_3014_, v___x_3024_, v___x_3025_, v___x_3019_);
lean_dec(v_a_3014_);
v___x_3027_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___redArg(v___y_3017_, v___x_3026_, v_k_3006_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_);
lean_dec_ref(v___y_3007_);
return v___x_3027_;
}
}
else
{
size_t v___x_3028_; size_t v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; 
v___x_3028_ = ((size_t)0ULL);
v___x_3029_ = lean_usize_of_nat(v___x_3018_);
v___x_3030_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__11(v_fvarIds_3005_, v_a_3014_, v___x_3028_, v___x_3029_, v___x_3019_);
lean_dec(v_a_3014_);
v___x_3031_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___redArg(v___y_3017_, v___x_3030_, v_k_3006_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_);
lean_dec_ref(v___y_3007_);
return v___x_3031_;
}
}
}
}
else
{
lean_object* v_a_3041_; lean_object* v___x_3043_; uint8_t v_isShared_3044_; uint8_t v_isSharedCheck_3048_; 
lean_dec_ref(v___y_3007_);
lean_dec_ref(v_k_3006_);
v_a_3041_ = lean_ctor_get(v___x_3013_, 0);
v_isSharedCheck_3048_ = !lean_is_exclusive(v___x_3013_);
if (v_isSharedCheck_3048_ == 0)
{
v___x_3043_ = v___x_3013_;
v_isShared_3044_ = v_isSharedCheck_3048_;
goto v_resetjp_3042_;
}
else
{
lean_inc(v_a_3041_);
lean_dec(v___x_3013_);
v___x_3043_ = lean_box(0);
v_isShared_3044_ = v_isSharedCheck_3048_;
goto v_resetjp_3042_;
}
v_resetjp_3042_:
{
lean_object* v___x_3046_; 
if (v_isShared_3044_ == 0)
{
v___x_3046_ = v___x_3043_;
goto v_reusejp_3045_;
}
else
{
lean_object* v_reuseFailAlloc_3047_; 
v_reuseFailAlloc_3047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3047_, 0, v_a_3041_);
v___x_3046_ = v_reuseFailAlloc_3047_;
goto v_reusejp_3045_;
}
v_reusejp_3045_:
{
return v___x_3046_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___redArg___boxed(lean_object* v_fvarIds_3049_, lean_object* v_k_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_){
_start:
{
lean_object* v_res_3056_; 
v_res_3056_ = l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___redArg(v_fvarIds_3049_, v_k_3050_, v___y_3051_, v___y_3052_, v___y_3053_, v___y_3054_);
lean_dec(v___y_3054_);
lean_dec_ref(v___y_3053_);
lean_dec(v___y_3052_);
lean_dec_ref(v_fvarIds_3049_);
return v_res_3056_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__14_spec__17_spec__21(lean_object* v_x_3057_, lean_object* v_x_3058_, lean_object* v_x_3059_){
_start:
{
if (lean_obj_tag(v_x_3059_) == 0)
{
lean_dec(v_x_3057_);
return v_x_3058_;
}
else
{
lean_object* v_head_3060_; lean_object* v_tail_3061_; lean_object* v___x_3063_; uint8_t v_isShared_3064_; uint8_t v_isSharedCheck_3071_; 
v_head_3060_ = lean_ctor_get(v_x_3059_, 0);
v_tail_3061_ = lean_ctor_get(v_x_3059_, 1);
v_isSharedCheck_3071_ = !lean_is_exclusive(v_x_3059_);
if (v_isSharedCheck_3071_ == 0)
{
v___x_3063_ = v_x_3059_;
v_isShared_3064_ = v_isSharedCheck_3071_;
goto v_resetjp_3062_;
}
else
{
lean_inc(v_tail_3061_);
lean_inc(v_head_3060_);
lean_dec(v_x_3059_);
v___x_3063_ = lean_box(0);
v_isShared_3064_ = v_isSharedCheck_3071_;
goto v_resetjp_3062_;
}
v_resetjp_3062_:
{
lean_object* v___x_3066_; 
lean_inc(v_x_3057_);
if (v_isShared_3064_ == 0)
{
lean_ctor_set_tag(v___x_3063_, 5);
lean_ctor_set(v___x_3063_, 1, v_x_3057_);
lean_ctor_set(v___x_3063_, 0, v_x_3058_);
v___x_3066_ = v___x_3063_;
goto v_reusejp_3065_;
}
else
{
lean_object* v_reuseFailAlloc_3070_; 
v_reuseFailAlloc_3070_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3070_, 0, v_x_3058_);
lean_ctor_set(v_reuseFailAlloc_3070_, 1, v_x_3057_);
v___x_3066_ = v_reuseFailAlloc_3070_;
goto v_reusejp_3065_;
}
v_reusejp_3065_:
{
lean_object* v___x_3067_; lean_object* v___x_3068_; 
v___x_3067_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(v_head_3060_);
v___x_3068_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3068_, 0, v___x_3066_);
lean_ctor_set(v___x_3068_, 1, v___x_3067_);
v_x_3058_ = v___x_3068_;
v_x_3059_ = v_tail_3061_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__14_spec__17(lean_object* v_x_3072_, lean_object* v_x_3073_, lean_object* v_x_3074_){
_start:
{
if (lean_obj_tag(v_x_3074_) == 0)
{
lean_dec(v_x_3072_);
return v_x_3073_;
}
else
{
lean_object* v_head_3075_; lean_object* v_tail_3076_; lean_object* v___x_3078_; uint8_t v_isShared_3079_; uint8_t v_isSharedCheck_3086_; 
v_head_3075_ = lean_ctor_get(v_x_3074_, 0);
v_tail_3076_ = lean_ctor_get(v_x_3074_, 1);
v_isSharedCheck_3086_ = !lean_is_exclusive(v_x_3074_);
if (v_isSharedCheck_3086_ == 0)
{
v___x_3078_ = v_x_3074_;
v_isShared_3079_ = v_isSharedCheck_3086_;
goto v_resetjp_3077_;
}
else
{
lean_inc(v_tail_3076_);
lean_inc(v_head_3075_);
lean_dec(v_x_3074_);
v___x_3078_ = lean_box(0);
v_isShared_3079_ = v_isSharedCheck_3086_;
goto v_resetjp_3077_;
}
v_resetjp_3077_:
{
lean_object* v___x_3081_; 
lean_inc(v_x_3072_);
if (v_isShared_3079_ == 0)
{
lean_ctor_set_tag(v___x_3078_, 5);
lean_ctor_set(v___x_3078_, 1, v_x_3072_);
lean_ctor_set(v___x_3078_, 0, v_x_3073_);
v___x_3081_ = v___x_3078_;
goto v_reusejp_3080_;
}
else
{
lean_object* v_reuseFailAlloc_3085_; 
v_reuseFailAlloc_3085_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3085_, 0, v_x_3073_);
lean_ctor_set(v_reuseFailAlloc_3085_, 1, v_x_3072_);
v___x_3081_ = v_reuseFailAlloc_3085_;
goto v_reusejp_3080_;
}
v_reusejp_3080_:
{
lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; 
v___x_3082_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(v_head_3075_);
v___x_3083_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3083_, 0, v___x_3081_);
lean_ctor_set(v___x_3083_, 1, v___x_3082_);
v___x_3084_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__14_spec__17_spec__21(v_x_3072_, v___x_3083_, v_tail_3076_);
return v___x_3084_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__14(lean_object* v_x_3087_, lean_object* v_x_3088_){
_start:
{
if (lean_obj_tag(v_x_3087_) == 0)
{
lean_object* v___x_3089_; 
lean_dec(v_x_3088_);
v___x_3089_ = lean_box(0);
return v___x_3089_;
}
else
{
lean_object* v_tail_3090_; 
v_tail_3090_ = lean_ctor_get(v_x_3087_, 1);
if (lean_obj_tag(v_tail_3090_) == 0)
{
lean_object* v_head_3091_; lean_object* v___x_3092_; 
lean_dec(v_x_3088_);
v_head_3091_ = lean_ctor_get(v_x_3087_, 0);
lean_inc(v_head_3091_);
lean_dec_ref(v_x_3087_);
v___x_3092_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(v_head_3091_);
return v___x_3092_;
}
else
{
lean_object* v_head_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; 
lean_inc(v_tail_3090_);
v_head_3093_ = lean_ctor_get(v_x_3087_, 0);
lean_inc(v_head_3093_);
lean_dec_ref(v_x_3087_);
v___x_3094_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(v_head_3093_);
v___x_3095_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__14_spec__17(v_x_3088_, v___x_3094_, v_tail_3090_);
return v___x_3095_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__5(void){
_start:
{
lean_object* v___x_3104_; lean_object* v___x_3105_; 
v___x_3104_ = ((lean_object*)(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__0));
v___x_3105_ = lean_string_length(v___x_3104_);
return v___x_3105_;
}
}
static lean_object* _init_l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__6(void){
_start:
{
lean_object* v___x_3106_; lean_object* v___x_3107_; 
v___x_3106_ = lean_obj_once(&l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__5, &l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__5_once, _init_l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__5);
v___x_3107_ = lean_nat_to_int(v___x_3106_);
return v___x_3107_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10(lean_object* v_xs_3115_){
_start:
{
lean_object* v___x_3116_; lean_object* v___x_3117_; uint8_t v___x_3118_; 
v___x_3116_ = lean_array_get_size(v_xs_3115_);
v___x_3117_ = lean_unsigned_to_nat(0u);
v___x_3118_ = lean_nat_dec_eq(v___x_3116_, v___x_3117_);
if (v___x_3118_ == 0)
{
lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; 
v___x_3119_ = lean_array_to_list(v_xs_3115_);
v___x_3120_ = ((lean_object*)(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__3));
v___x_3121_ = l_Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__14(v___x_3119_, v___x_3120_);
v___x_3122_ = lean_obj_once(&l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__6, &l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__6_once, _init_l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__6);
v___x_3123_ = ((lean_object*)(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__7));
v___x_3124_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3124_, 0, v___x_3123_);
lean_ctor_set(v___x_3124_, 1, v___x_3121_);
v___x_3125_ = ((lean_object*)(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__8));
v___x_3126_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3126_, 0, v___x_3124_);
lean_ctor_set(v___x_3126_, 1, v___x_3125_);
v___x_3127_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3127_, 0, v___x_3122_);
lean_ctor_set(v___x_3127_, 1, v___x_3126_);
v___x_3128_ = l_Std_Format_fill(v___x_3127_);
return v___x_3128_;
}
else
{
lean_object* v___x_3129_; 
lean_dec_ref(v_xs_3115_);
v___x_3129_ = ((lean_object*)(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__10));
return v___x_3129_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__11(size_t v_sz_3130_, size_t v_i_3131_, lean_object* v_bs_3132_){
_start:
{
uint8_t v___x_3133_; 
v___x_3133_ = lean_usize_dec_lt(v_i_3131_, v_sz_3130_);
if (v___x_3133_ == 0)
{
return v_bs_3132_;
}
else
{
lean_object* v_v_3134_; lean_object* v___x_3135_; lean_object* v_bs_x27_3136_; lean_object* v___x_3137_; size_t v___x_3138_; size_t v___x_3139_; lean_object* v___x_3140_; 
v_v_3134_ = lean_array_uget(v_bs_3132_, v_i_3131_);
v___x_3135_ = lean_unsigned_to_nat(0u);
v_bs_x27_3136_ = lean_array_uset(v_bs_3132_, v_i_3131_, v___x_3135_);
v___x_3137_ = l_Lean_mkFVar(v_v_3134_);
v___x_3138_ = ((size_t)1ULL);
v___x_3139_ = lean_usize_add(v_i_3131_, v___x_3138_);
v___x_3140_ = lean_array_uset(v_bs_x27_3136_, v_i_3131_, v___x_3137_);
v_i_3131_ = v___x_3139_;
v_bs_3132_ = v___x_3140_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__11___boxed(lean_object* v_sz_3142_, lean_object* v_i_3143_, lean_object* v_bs_3144_){
_start:
{
size_t v_sz_boxed_3145_; size_t v_i_boxed_3146_; lean_object* v_res_3147_; 
v_sz_boxed_3145_ = lean_unbox_usize(v_sz_3142_);
lean_dec(v_sz_3142_);
v_i_boxed_3146_ = lean_unbox_usize(v_i_3143_);
lean_dec(v_i_3143_);
v_res_3147_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__11(v_sz_boxed_3145_, v_i_boxed_3146_, v_bs_3144_);
return v_res_3147_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg(lean_object* v_fst_3148_, lean_object* v_as_3149_, lean_object* v_i_3150_, lean_object* v_j_3151_, lean_object* v_bs_3152_){
_start:
{
lean_object* v_zero_3153_; uint8_t v_isZero_3154_; 
v_zero_3153_ = lean_unsigned_to_nat(0u);
v_isZero_3154_ = lean_nat_dec_eq(v_i_3150_, v_zero_3153_);
if (v_isZero_3154_ == 1)
{
lean_dec(v_j_3151_);
lean_dec(v_i_3150_);
return v_bs_3152_;
}
else
{
lean_object* v___x_3155_; lean_object* v_fnName_3156_; lean_object* v_recArgPos_3157_; lean_object* v_indicesPos_3158_; lean_object* v_indGroupInst_3159_; lean_object* v_indIdx_3160_; lean_object* v___x_3162_; uint8_t v_isShared_3163_; uint8_t v_isSharedCheck_3175_; 
v___x_3155_ = lean_array_fget(v_as_3149_, v_j_3151_);
v_fnName_3156_ = lean_ctor_get(v___x_3155_, 0);
v_recArgPos_3157_ = lean_ctor_get(v___x_3155_, 2);
v_indicesPos_3158_ = lean_ctor_get(v___x_3155_, 3);
v_indGroupInst_3159_ = lean_ctor_get(v___x_3155_, 4);
v_indIdx_3160_ = lean_ctor_get(v___x_3155_, 5);
v_isSharedCheck_3175_ = !lean_is_exclusive(v___x_3155_);
if (v_isSharedCheck_3175_ == 0)
{
lean_object* v_unused_3176_; 
v_unused_3176_ = lean_ctor_get(v___x_3155_, 1);
lean_dec(v_unused_3176_);
v___x_3162_ = v___x_3155_;
v_isShared_3163_ = v_isSharedCheck_3175_;
goto v_resetjp_3161_;
}
else
{
lean_inc(v_indIdx_3160_);
lean_inc(v_indGroupInst_3159_);
lean_inc(v_indicesPos_3158_);
lean_inc(v_recArgPos_3157_);
lean_inc(v_fnName_3156_);
lean_dec(v___x_3155_);
v___x_3162_ = lean_box(0);
v_isShared_3163_ = v_isSharedCheck_3175_;
goto v_resetjp_3161_;
}
v_resetjp_3161_:
{
lean_object* v_perms_3164_; lean_object* v___x_3165_; lean_object* v_one_3166_; lean_object* v_n_3167_; lean_object* v___x_3168_; lean_object* v___x_3170_; 
v_perms_3164_ = lean_ctor_get(v_fst_3148_, 1);
v___x_3165_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9___redArg___closed__0, &l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9___redArg___closed__0_once, _init_l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9___redArg___closed__0);
v_one_3166_ = lean_unsigned_to_nat(1u);
v_n_3167_ = lean_nat_sub(v_i_3150_, v_one_3166_);
lean_dec(v_i_3150_);
v___x_3168_ = lean_array_get_borrowed(v___x_3165_, v_perms_3164_, v_j_3151_);
lean_inc(v___x_3168_);
if (v_isShared_3163_ == 0)
{
lean_ctor_set(v___x_3162_, 1, v___x_3168_);
v___x_3170_ = v___x_3162_;
goto v_reusejp_3169_;
}
else
{
lean_object* v_reuseFailAlloc_3174_; 
v_reuseFailAlloc_3174_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3174_, 0, v_fnName_3156_);
lean_ctor_set(v_reuseFailAlloc_3174_, 1, v___x_3168_);
lean_ctor_set(v_reuseFailAlloc_3174_, 2, v_recArgPos_3157_);
lean_ctor_set(v_reuseFailAlloc_3174_, 3, v_indicesPos_3158_);
lean_ctor_set(v_reuseFailAlloc_3174_, 4, v_indGroupInst_3159_);
lean_ctor_set(v_reuseFailAlloc_3174_, 5, v_indIdx_3160_);
v___x_3170_ = v_reuseFailAlloc_3174_;
goto v_reusejp_3169_;
}
v_reusejp_3169_:
{
lean_object* v___x_3171_; lean_object* v___x_3172_; 
v___x_3171_ = lean_nat_add(v_j_3151_, v_one_3166_);
lean_dec(v_j_3151_);
v___x_3172_ = lean_array_push(v_bs_3152_, v___x_3170_);
v_i_3150_ = v_n_3167_;
v_j_3151_ = v___x_3171_;
v_bs_3152_ = v___x_3172_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg___boxed(lean_object* v_fst_3177_, lean_object* v_as_3178_, lean_object* v_i_3179_, lean_object* v_j_3180_, lean_object* v_bs_3181_){
_start:
{
lean_object* v_res_3182_; 
v_res_3182_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg(v_fst_3177_, v_as_3178_, v_i_3179_, v_j_3180_, v_bs_3181_);
lean_dec_ref(v_as_3178_);
lean_dec_ref(v_fst_3177_);
return v_res_3182_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__2(size_t v_sz_3183_, size_t v_i_3184_, lean_object* v_bs_3185_){
_start:
{
uint8_t v___x_3186_; 
v___x_3186_ = lean_usize_dec_lt(v_i_3184_, v_sz_3183_);
if (v___x_3186_ == 0)
{
return v_bs_3185_;
}
else
{
lean_object* v_v_3187_; lean_object* v_recArgPos_3188_; lean_object* v___x_3189_; lean_object* v_bs_x27_3190_; size_t v___x_3191_; size_t v___x_3192_; lean_object* v___x_3193_; 
v_v_3187_ = lean_array_uget_borrowed(v_bs_3185_, v_i_3184_);
v_recArgPos_3188_ = lean_ctor_get(v_v_3187_, 2);
lean_inc(v_recArgPos_3188_);
v___x_3189_ = lean_unsigned_to_nat(0u);
v_bs_x27_3190_ = lean_array_uset(v_bs_3185_, v_i_3184_, v___x_3189_);
v___x_3191_ = ((size_t)1ULL);
v___x_3192_ = lean_usize_add(v_i_3184_, v___x_3191_);
v___x_3193_ = lean_array_uset(v_bs_x27_3190_, v_i_3184_, v_recArgPos_3188_);
v_i_3184_ = v___x_3192_;
v_bs_3185_ = v___x_3193_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__2___boxed(lean_object* v_sz_3195_, lean_object* v_i_3196_, lean_object* v_bs_3197_){
_start:
{
size_t v_sz_boxed_3198_; size_t v_i_boxed_3199_; lean_object* v_res_3200_; 
v_sz_boxed_3198_ = lean_unbox_usize(v_sz_3195_);
lean_dec(v_sz_3195_);
v_i_boxed_3199_ = lean_unbox_usize(v_i_3196_);
lean_dec(v_i_3196_);
v_res_3200_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__2(v_sz_boxed_3198_, v_i_boxed_3199_, v_bs_3197_);
return v_res_3200_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__1(void){
_start:
{
lean_object* v___x_3202_; lean_object* v___x_3203_; 
v___x_3202_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__0));
v___x_3203_ = l_Lean_stringToMessageData(v___x_3202_);
return v___x_3203_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__3(void){
_start:
{
lean_object* v___x_3205_; lean_object* v___x_3206_; 
v___x_3205_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__2));
v___x_3206_ = l_Lean_stringToMessageData(v___x_3205_);
return v___x_3206_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__5(void){
_start:
{
lean_object* v___x_3208_; lean_object* v___x_3209_; 
v___x_3208_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__4));
v___x_3209_ = l_Lean_stringToMessageData(v___x_3208_);
return v___x_3209_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6(lean_object* v_a_3210_, lean_object* v_as_3211_, size_t v_sz_3212_, size_t v_i_3213_, lean_object* v_b_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_){
_start:
{
lean_object* v_a_3221_; uint8_t v___x_3225_; 
v___x_3225_ = lean_usize_dec_lt(v_i_3213_, v_sz_3212_);
if (v___x_3225_ == 0)
{
lean_object* v___x_3226_; 
lean_dec_ref(v_a_3210_);
v___x_3226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3226_, 0, v_b_3214_);
return v___x_3226_;
}
else
{
lean_object* v_a_3227_; lean_object* v___x_3228_; 
v_a_3227_ = lean_array_uget_borrowed(v_as_3211_, v_i_3213_);
lean_inc(v_a_3227_);
lean_inc_ref(v_a_3210_);
v___x_3228_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg(v_a_3210_, v_a_3227_, v___y_3216_);
if (lean_obj_tag(v___x_3228_) == 0)
{
lean_object* v_a_3229_; lean_object* v___x_3230_; uint8_t v___x_3231_; 
v_a_3229_ = lean_ctor_get(v___x_3228_, 0);
lean_inc(v_a_3229_);
lean_dec_ref(v___x_3228_);
v___x_3230_ = lean_box(0);
v___x_3231_ = lean_unbox(v_a_3229_);
lean_dec(v_a_3229_);
if (v___x_3231_ == 0)
{
v_a_3221_ = v___x_3230_;
goto v___jp_3220_;
}
else
{
uint8_t v___x_3232_; 
v___x_3232_ = l_Lean_Expr_isFVarOf(v_a_3210_, v_a_3227_);
if (v___x_3232_ == 0)
{
lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; 
v___x_3233_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__1);
lean_inc_ref(v_a_3210_);
v___x_3234_ = l_Lean_indentExpr(v_a_3210_);
v___x_3235_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3235_, 0, v___x_3233_);
lean_ctor_set(v___x_3235_, 1, v___x_3234_);
v___x_3236_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__3);
v___x_3237_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3237_, 0, v___x_3235_);
lean_ctor_set(v___x_3237_, 1, v___x_3236_);
lean_inc(v_a_3227_);
v___x_3238_ = l_Lean_mkFVar(v_a_3227_);
v___x_3239_ = l_Lean_indentExpr(v___x_3238_);
v___x_3240_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3240_, 0, v___x_3237_);
lean_ctor_set(v___x_3240_, 1, v___x_3239_);
v___x_3241_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__5);
v___x_3242_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3242_, 0, v___x_3240_);
lean_ctor_set(v___x_3242_, 1, v___x_3241_);
v___x_3243_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg(v___x_3242_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_);
if (lean_obj_tag(v___x_3243_) == 0)
{
lean_dec_ref(v___x_3243_);
v_a_3221_ = v___x_3230_;
goto v___jp_3220_;
}
else
{
lean_dec_ref(v_a_3210_);
return v___x_3243_;
}
}
else
{
lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; 
v___x_3244_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__1);
lean_inc_ref(v_a_3210_);
v___x_3245_ = l_Lean_indentExpr(v_a_3210_);
v___x_3246_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3246_, 0, v___x_3244_);
lean_ctor_set(v___x_3246_, 1, v___x_3245_);
v___x_3247_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__5);
v___x_3248_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3248_, 0, v___x_3246_);
lean_ctor_set(v___x_3248_, 1, v___x_3247_);
v___x_3249_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg(v___x_3248_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_);
if (lean_obj_tag(v___x_3249_) == 0)
{
lean_dec_ref(v___x_3249_);
v_a_3221_ = v___x_3230_;
goto v___jp_3220_;
}
else
{
lean_dec_ref(v_a_3210_);
return v___x_3249_;
}
}
}
}
else
{
lean_object* v_a_3250_; lean_object* v___x_3252_; uint8_t v_isShared_3253_; uint8_t v_isSharedCheck_3257_; 
lean_dec_ref(v_a_3210_);
v_a_3250_ = lean_ctor_get(v___x_3228_, 0);
v_isSharedCheck_3257_ = !lean_is_exclusive(v___x_3228_);
if (v_isSharedCheck_3257_ == 0)
{
v___x_3252_ = v___x_3228_;
v_isShared_3253_ = v_isSharedCheck_3257_;
goto v_resetjp_3251_;
}
else
{
lean_inc(v_a_3250_);
lean_dec(v___x_3228_);
v___x_3252_ = lean_box(0);
v_isShared_3253_ = v_isSharedCheck_3257_;
goto v_resetjp_3251_;
}
v_resetjp_3251_:
{
lean_object* v___x_3255_; 
if (v_isShared_3253_ == 0)
{
v___x_3255_ = v___x_3252_;
goto v_reusejp_3254_;
}
else
{
lean_object* v_reuseFailAlloc_3256_; 
v_reuseFailAlloc_3256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3256_, 0, v_a_3250_);
v___x_3255_ = v_reuseFailAlloc_3256_;
goto v_reusejp_3254_;
}
v_reusejp_3254_:
{
return v___x_3255_;
}
}
}
}
v___jp_3220_:
{
size_t v___x_3222_; size_t v___x_3223_; 
v___x_3222_ = ((size_t)1ULL);
v___x_3223_ = lean_usize_add(v_i_3213_, v___x_3222_);
v_i_3213_ = v___x_3223_;
v_b_3214_ = v_a_3221_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___boxed(lean_object* v_a_3258_, lean_object* v_as_3259_, lean_object* v_sz_3260_, lean_object* v_i_3261_, lean_object* v_b_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_){
_start:
{
size_t v_sz_boxed_3268_; size_t v_i_boxed_3269_; lean_object* v_res_3270_; 
v_sz_boxed_3268_ = lean_unbox_usize(v_sz_3260_);
lean_dec(v_sz_3260_);
v_i_boxed_3269_ = lean_unbox_usize(v_i_3261_);
lean_dec(v_i_3261_);
v_res_3270_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6(v_a_3258_, v_as_3259_, v_sz_boxed_3268_, v_i_boxed_3269_, v_b_3262_, v___y_3263_, v___y_3264_, v___y_3265_, v___y_3266_);
lean_dec(v___y_3266_);
lean_dec_ref(v___y_3265_);
lean_dec(v___y_3264_);
lean_dec_ref(v___y_3263_);
lean_dec_ref(v_as_3259_);
return v_res_3270_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7(lean_object* v_snd_3271_, lean_object* v_as_3272_, size_t v_sz_3273_, size_t v_i_3274_, lean_object* v_b_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_){
_start:
{
uint8_t v___x_3281_; 
v___x_3281_ = lean_usize_dec_lt(v_i_3274_, v_sz_3273_);
if (v___x_3281_ == 0)
{
lean_object* v___x_3282_; 
v___x_3282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3282_, 0, v_b_3275_);
return v___x_3282_;
}
else
{
lean_object* v___x_3283_; lean_object* v_a_3284_; size_t v_sz_3285_; size_t v___x_3286_; lean_object* v___x_3287_; 
v___x_3283_ = lean_box(0);
v_a_3284_ = lean_array_uget_borrowed(v_as_3272_, v_i_3274_);
v_sz_3285_ = lean_array_size(v_snd_3271_);
v___x_3286_ = ((size_t)0ULL);
lean_inc(v_a_3284_);
v___x_3287_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6(v_a_3284_, v_snd_3271_, v_sz_3285_, v___x_3286_, v___x_3283_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_);
if (lean_obj_tag(v___x_3287_) == 0)
{
size_t v___x_3288_; size_t v___x_3289_; 
lean_dec_ref(v___x_3287_);
v___x_3288_ = ((size_t)1ULL);
v___x_3289_ = lean_usize_add(v_i_3274_, v___x_3288_);
v_i_3274_ = v___x_3289_;
v_b_3275_ = v___x_3283_;
goto _start;
}
else
{
return v___x_3287_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7___boxed(lean_object* v_snd_3291_, lean_object* v_as_3292_, lean_object* v_sz_3293_, lean_object* v_i_3294_, lean_object* v_b_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_){
_start:
{
size_t v_sz_boxed_3301_; size_t v_i_boxed_3302_; lean_object* v_res_3303_; 
v_sz_boxed_3301_ = lean_unbox_usize(v_sz_3293_);
lean_dec(v_sz_3293_);
v_i_boxed_3302_ = lean_unbox_usize(v_i_3294_);
lean_dec(v_i_3294_);
v_res_3303_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7(v_snd_3291_, v_as_3292_, v_sz_boxed_3301_, v_i_boxed_3302_, v_b_3295_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_);
lean_dec(v___y_3299_);
lean_dec_ref(v___y_3298_);
lean_dec(v___y_3297_);
lean_dec_ref(v___y_3296_);
lean_dec_ref(v_as_3292_);
lean_dec_ref(v_snd_3291_);
return v_res_3303_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8(lean_object* v_snd_3304_, lean_object* v_as_3305_, size_t v_sz_3306_, size_t v_i_3307_, lean_object* v_b_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_){
_start:
{
uint8_t v___x_3314_; 
v___x_3314_ = lean_usize_dec_lt(v_i_3307_, v_sz_3306_);
if (v___x_3314_ == 0)
{
lean_object* v___x_3315_; 
v___x_3315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3315_, 0, v_b_3308_);
return v___x_3315_;
}
else
{
lean_object* v_a_3316_; lean_object* v_indGroupInst_3317_; lean_object* v_params_3318_; lean_object* v___x_3319_; size_t v_sz_3320_; size_t v___x_3321_; lean_object* v___x_3322_; 
v_a_3316_ = lean_array_uget_borrowed(v_as_3305_, v_i_3307_);
v_indGroupInst_3317_ = lean_ctor_get(v_a_3316_, 4);
v_params_3318_ = lean_ctor_get(v_indGroupInst_3317_, 2);
v___x_3319_ = lean_box(0);
v_sz_3320_ = lean_array_size(v_params_3318_);
v___x_3321_ = ((size_t)0ULL);
v___x_3322_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7(v_snd_3304_, v_params_3318_, v_sz_3320_, v___x_3321_, v___x_3319_, v___y_3309_, v___y_3310_, v___y_3311_, v___y_3312_);
if (lean_obj_tag(v___x_3322_) == 0)
{
size_t v___x_3323_; size_t v___x_3324_; 
lean_dec_ref(v___x_3322_);
v___x_3323_ = ((size_t)1ULL);
v___x_3324_ = lean_usize_add(v_i_3307_, v___x_3323_);
v_i_3307_ = v___x_3324_;
v_b_3308_ = v___x_3319_;
goto _start;
}
else
{
return v___x_3322_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8___boxed(lean_object* v_snd_3326_, lean_object* v_as_3327_, lean_object* v_sz_3328_, lean_object* v_i_3329_, lean_object* v_b_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_){
_start:
{
size_t v_sz_boxed_3336_; size_t v_i_boxed_3337_; lean_object* v_res_3338_; 
v_sz_boxed_3336_ = lean_unbox_usize(v_sz_3328_);
lean_dec(v_sz_3328_);
v_i_boxed_3337_ = lean_unbox_usize(v_i_3329_);
lean_dec(v_i_3329_);
v_res_3338_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8(v_snd_3326_, v_as_3327_, v_sz_boxed_3336_, v_i_boxed_3337_, v_b_3330_, v___y_3331_, v___y_3332_, v___y_3333_, v___y_3334_);
lean_dec(v___y_3334_);
lean_dec_ref(v___y_3333_);
lean_dec(v___y_3332_);
lean_dec_ref(v___y_3331_);
lean_dec_ref(v_as_3327_);
lean_dec_ref(v_snd_3326_);
return v_res_3338_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3340_; lean_object* v___x_3341_; 
v___x_3340_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___closed__0));
v___x_3341_ = l_Lean_stringToMessageData(v___x_3340_);
return v___x_3341_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___closed__3(void){
_start:
{
lean_object* v___x_3343_; lean_object* v___x_3344_; 
v___x_3343_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___closed__2));
v___x_3344_ = l_Lean_stringToMessageData(v___x_3343_);
return v___x_3344_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___closed__5(void){
_start:
{
lean_object* v___x_3346_; lean_object* v___x_3347_; 
v___x_3346_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___closed__4));
v___x_3347_ = l_Lean_stringToMessageData(v___x_3346_);
return v___x_3347_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___closed__7(void){
_start:
{
lean_object* v___x_3349_; lean_object* v___x_3350_; 
v___x_3349_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___closed__6));
v___x_3350_ = l_Lean_stringToMessageData(v___x_3349_);
return v___x_3350_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___closed__9(void){
_start:
{
lean_object* v___x_3352_; lean_object* v___x_3353_; 
v___x_3352_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___closed__8));
v___x_3353_ = l_Lean_stringToMessageData(v___x_3352_);
return v___x_3353_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1(size_t v___x_3354_, lean_object* v_a_3355_, lean_object* v_xs_3356_, lean_object* v___x_3357_, lean_object* v_a_3358_, lean_object* v_recArgInfos_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_){
_start:
{
lean_object* v___y_3366_; lean_object* v___y_3367_; lean_object* v___y_3368_; lean_object* v___y_3369_; lean_object* v___y_3370_; lean_object* v___y_3371_; lean_object* v___y_3372_; lean_object* v___x_3385_; lean_object* v___y_3387_; lean_object* v___y_3388_; lean_object* v___y_3389_; lean_object* v___y_3390_; lean_object* v___y_3391_; lean_object* v___y_3392_; lean_object* v___y_3393_; lean_object* v___x_3410_; lean_object* v_a_3411_; size_t v_sz_3412_; lean_object* v___x_3413_; lean_object* v___y_3415_; lean_object* v___y_3416_; lean_object* v___y_3417_; lean_object* v___y_3418_; uint8_t v___x_3477_; 
v___x_3385_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__3));
v___x_3410_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___redArg(v___x_3385_, v___y_3362_);
v_a_3411_ = lean_ctor_get(v___x_3410_, 0);
lean_inc(v_a_3411_);
lean_dec_ref(v___x_3410_);
v_sz_3412_ = lean_array_size(v_recArgInfos_3359_);
lean_inc_ref(v_recArgInfos_3359_);
v___x_3413_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__2(v_sz_3412_, v___x_3354_, v_recArgInfos_3359_);
v___x_3477_ = lean_unbox(v_a_3411_);
lean_dec(v_a_3411_);
if (v___x_3477_ == 0)
{
v___y_3415_ = v___y_3360_;
v___y_3416_ = v___y_3361_;
v___y_3417_ = v___y_3362_;
v___y_3418_ = v___y_3363_;
goto v___jp_3414_;
}
else
{
lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; 
v___x_3478_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___closed__9, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___closed__9_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___closed__9);
lean_inc_ref(v___x_3413_);
v___x_3479_ = lean_array_to_list(v___x_3413_);
v___x_3480_ = lean_box(0);
v___x_3481_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__0(v___x_3479_, v___x_3480_);
v___x_3482_ = l_Lean_MessageData_ofList(v___x_3481_);
v___x_3483_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3483_, 0, v___x_3478_);
lean_ctor_set(v___x_3483_, 1, v___x_3482_);
v___x_3484_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12(v___x_3385_, v___x_3483_, v___y_3360_, v___y_3361_, v___y_3362_, v___y_3363_);
if (lean_obj_tag(v___x_3484_) == 0)
{
lean_dec_ref(v___x_3484_);
v___y_3415_ = v___y_3360_;
v___y_3416_ = v___y_3361_;
v___y_3417_ = v___y_3362_;
v___y_3418_ = v___y_3363_;
goto v___jp_3414_;
}
else
{
lean_object* v_a_3485_; lean_object* v___x_3487_; uint8_t v_isShared_3488_; uint8_t v_isSharedCheck_3492_; 
lean_dec_ref(v___x_3413_);
lean_dec_ref(v_recArgInfos_3359_);
lean_dec_ref(v_a_3358_);
lean_dec(v___x_3357_);
lean_dec_ref(v_xs_3356_);
lean_dec_ref(v_a_3355_);
v_a_3485_ = lean_ctor_get(v___x_3484_, 0);
v_isSharedCheck_3492_ = !lean_is_exclusive(v___x_3484_);
if (v_isSharedCheck_3492_ == 0)
{
v___x_3487_ = v___x_3484_;
v_isShared_3488_ = v_isSharedCheck_3492_;
goto v_resetjp_3486_;
}
else
{
lean_inc(v_a_3485_);
lean_dec(v___x_3484_);
v___x_3487_ = lean_box(0);
v_isShared_3488_ = v_isSharedCheck_3492_;
goto v_resetjp_3486_;
}
v_resetjp_3486_:
{
lean_object* v___x_3490_; 
if (v_isShared_3488_ == 0)
{
v___x_3490_ = v___x_3487_;
goto v_reusejp_3489_;
}
else
{
lean_object* v_reuseFailAlloc_3491_; 
v_reuseFailAlloc_3491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3491_, 0, v_a_3485_);
v___x_3490_ = v_reuseFailAlloc_3491_;
goto v_reusejp_3489_;
}
v_reusejp_3489_:
{
return v___x_3490_;
}
}
}
}
v___jp_3365_:
{
lean_object* v___x_3373_; size_t v_sz_3374_; lean_object* v___x_3375_; 
v___x_3373_ = lean_box(0);
v_sz_3374_ = lean_array_size(v___y_3366_);
v___x_3375_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8(v___y_3368_, v___y_3366_, v_sz_3374_, v___x_3354_, v___x_3373_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_);
lean_dec_ref(v___y_3366_);
if (lean_obj_tag(v___x_3375_) == 0)
{
lean_object* v___x_3376_; 
lean_dec_ref(v___x_3375_);
lean_inc_ref(v___y_3369_);
v___x_3376_ = l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___redArg(v___y_3368_, v___y_3367_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_);
lean_dec_ref(v___y_3368_);
return v___x_3376_;
}
else
{
lean_object* v_a_3377_; lean_object* v___x_3379_; uint8_t v_isShared_3380_; uint8_t v_isSharedCheck_3384_; 
lean_dec_ref(v___y_3368_);
lean_dec_ref(v___y_3367_);
v_a_3377_ = lean_ctor_get(v___x_3375_, 0);
v_isSharedCheck_3384_ = !lean_is_exclusive(v___x_3375_);
if (v_isSharedCheck_3384_ == 0)
{
v___x_3379_ = v___x_3375_;
v_isShared_3380_ = v_isSharedCheck_3384_;
goto v_resetjp_3378_;
}
else
{
lean_inc(v_a_3377_);
lean_dec(v___x_3375_);
v___x_3379_ = lean_box(0);
v_isShared_3380_ = v_isSharedCheck_3384_;
goto v_resetjp_3378_;
}
v_resetjp_3378_:
{
lean_object* v___x_3382_; 
if (v_isShared_3380_ == 0)
{
v___x_3382_ = v___x_3379_;
goto v_reusejp_3381_;
}
else
{
lean_object* v_reuseFailAlloc_3383_; 
v_reuseFailAlloc_3383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3383_, 0, v_a_3377_);
v___x_3382_ = v_reuseFailAlloc_3383_;
goto v_reusejp_3381_;
}
v_reusejp_3381_:
{
return v___x_3382_;
}
}
}
}
v___jp_3386_:
{
lean_object* v___x_3394_; lean_object* v_a_3395_; uint8_t v___x_3396_; 
v___x_3394_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___redArg(v___x_3385_, v___y_3392_);
v_a_3395_ = lean_ctor_get(v___x_3394_, 0);
lean_inc(v_a_3395_);
lean_dec_ref(v___x_3394_);
v___x_3396_ = lean_unbox(v_a_3395_);
lean_dec(v_a_3395_);
if (v___x_3396_ == 0)
{
v___y_3366_ = v___y_3387_;
v___y_3367_ = v___y_3388_;
v___y_3368_ = v___y_3389_;
v___y_3369_ = v___y_3390_;
v___y_3370_ = v___y_3391_;
v___y_3371_ = v___y_3392_;
v___y_3372_ = v___y_3393_;
goto v___jp_3365_;
}
else
{
lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; 
v___x_3397_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___closed__1);
lean_inc_ref(v___y_3387_);
v___x_3398_ = l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10(v___y_3387_);
v___x_3399_ = l_Lean_MessageData_ofFormat(v___x_3398_);
v___x_3400_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3400_, 0, v___x_3397_);
lean_ctor_set(v___x_3400_, 1, v___x_3399_);
v___x_3401_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12(v___x_3385_, v___x_3400_, v___y_3390_, v___y_3391_, v___y_3392_, v___y_3393_);
if (lean_obj_tag(v___x_3401_) == 0)
{
lean_dec_ref(v___x_3401_);
v___y_3366_ = v___y_3387_;
v___y_3367_ = v___y_3388_;
v___y_3368_ = v___y_3389_;
v___y_3369_ = v___y_3390_;
v___y_3370_ = v___y_3391_;
v___y_3371_ = v___y_3392_;
v___y_3372_ = v___y_3393_;
goto v___jp_3365_;
}
else
{
lean_object* v_a_3402_; lean_object* v___x_3404_; uint8_t v_isShared_3405_; uint8_t v_isSharedCheck_3409_; 
lean_dec_ref(v___y_3389_);
lean_dec_ref(v___y_3388_);
lean_dec_ref(v___y_3387_);
v_a_3402_ = lean_ctor_get(v___x_3401_, 0);
v_isSharedCheck_3409_ = !lean_is_exclusive(v___x_3401_);
if (v_isSharedCheck_3409_ == 0)
{
v___x_3404_ = v___x_3401_;
v_isShared_3405_ = v_isSharedCheck_3409_;
goto v_resetjp_3403_;
}
else
{
lean_inc(v_a_3402_);
lean_dec(v___x_3401_);
v___x_3404_ = lean_box(0);
v_isShared_3405_ = v_isSharedCheck_3409_;
goto v_resetjp_3403_;
}
v_resetjp_3403_:
{
lean_object* v___x_3407_; 
if (v_isShared_3405_ == 0)
{
v___x_3407_ = v___x_3404_;
goto v_reusejp_3406_;
}
else
{
lean_object* v_reuseFailAlloc_3408_; 
v_reuseFailAlloc_3408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3408_, 0, v_a_3402_);
v___x_3407_ = v_reuseFailAlloc_3408_;
goto v_reusejp_3406_;
}
v_reusejp_3406_:
{
return v___x_3407_;
}
}
}
}
}
v___jp_3414_:
{
lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v_snd_3421_; lean_object* v_fst_3422_; lean_object* v___x_3424_; uint8_t v_isShared_3425_; uint8_t v_isSharedCheck_3476_; 
lean_inc_ref(v_recArgInfos_3359_);
v___x_3419_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__3(v_sz_3412_, v___x_3354_, v_recArgInfos_3359_);
lean_inc_ref(v_xs_3356_);
v___x_3420_ = l_Lean_Elab_FixedParamPerms_erase(v_a_3355_, v_xs_3356_, v___x_3419_);
v_snd_3421_ = lean_ctor_get(v___x_3420_, 1);
v_fst_3422_ = lean_ctor_get(v___x_3420_, 0);
v_isSharedCheck_3476_ = !lean_is_exclusive(v___x_3420_);
if (v_isSharedCheck_3476_ == 0)
{
v___x_3424_ = v___x_3420_;
v_isShared_3425_ = v_isSharedCheck_3476_;
goto v_resetjp_3423_;
}
else
{
lean_inc(v_snd_3421_);
lean_inc(v_fst_3422_);
lean_dec(v___x_3420_);
v___x_3424_ = lean_box(0);
v_isShared_3425_ = v_isSharedCheck_3476_;
goto v_resetjp_3423_;
}
v_resetjp_3423_:
{
lean_object* v_fst_3426_; lean_object* v_snd_3427_; lean_object* v___x_3429_; uint8_t v_isShared_3430_; uint8_t v_isSharedCheck_3475_; 
v_fst_3426_ = lean_ctor_get(v_snd_3421_, 0);
v_snd_3427_ = lean_ctor_get(v_snd_3421_, 1);
v_isSharedCheck_3475_ = !lean_is_exclusive(v_snd_3421_);
if (v_isSharedCheck_3475_ == 0)
{
v___x_3429_ = v_snd_3421_;
v_isShared_3430_ = v_isSharedCheck_3475_;
goto v_resetjp_3428_;
}
else
{
lean_inc(v_snd_3427_);
lean_inc(v_fst_3426_);
lean_dec(v_snd_3421_);
v___x_3429_ = lean_box(0);
v_isShared_3430_ = v_isSharedCheck_3475_;
goto v_resetjp_3428_;
}
v_resetjp_3428_:
{
lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___f_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; uint8_t v___x_3437_; 
v___x_3431_ = lean_array_get_size(v_recArgInfos_3359_);
v___x_3432_ = lean_mk_empty_array_with_capacity(v___x_3431_);
v___x_3433_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg(v_fst_3422_, v_recArgInfos_3359_, v___x_3431_, v___x_3357_, v___x_3432_);
lean_dec_ref(v_recArgInfos_3359_);
lean_inc_ref(v___x_3433_);
lean_inc(v_fst_3426_);
v___f_3434_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___boxed), 10, 5);
lean_closure_set(v___f_3434_, 0, v_a_3358_);
lean_closure_set(v___f_3434_, 1, v_fst_3422_);
lean_closure_set(v___f_3434_, 2, v_fst_3426_);
lean_closure_set(v___f_3434_, 3, v___x_3433_);
lean_closure_set(v___f_3434_, 4, v___x_3413_);
v___x_3435_ = lean_array_get_size(v_fst_3426_);
v___x_3436_ = lean_array_get_size(v_xs_3356_);
v___x_3437_ = lean_nat_dec_eq(v___x_3435_, v___x_3436_);
if (v___x_3437_ == 0)
{
lean_object* v___x_3438_; lean_object* v_a_3439_; uint8_t v___x_3440_; 
v___x_3438_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___redArg(v___x_3385_, v___y_3417_);
v_a_3439_ = lean_ctor_get(v___x_3438_, 0);
lean_inc(v_a_3439_);
lean_dec_ref(v___x_3438_);
v___x_3440_ = lean_unbox(v_a_3439_);
lean_dec(v_a_3439_);
if (v___x_3440_ == 0)
{
lean_del_object(v___x_3429_);
lean_dec(v_fst_3426_);
lean_del_object(v___x_3424_);
lean_dec_ref(v_xs_3356_);
v___y_3387_ = v___x_3433_;
v___y_3388_ = v___f_3434_;
v___y_3389_ = v_snd_3427_;
v___y_3390_ = v___y_3415_;
v___y_3391_ = v___y_3416_;
v___y_3392_ = v___y_3417_;
v___y_3393_ = v___y_3418_;
goto v___jp_3386_;
}
else
{
lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3447_; 
v___x_3441_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___closed__3, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___closed__3);
v___x_3442_ = lean_array_to_list(v_xs_3356_);
v___x_3443_ = lean_box(0);
v___x_3444_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_3442_, v___x_3443_);
v___x_3445_ = l_Lean_MessageData_ofList(v___x_3444_);
if (v_isShared_3430_ == 0)
{
lean_ctor_set_tag(v___x_3429_, 7);
lean_ctor_set(v___x_3429_, 1, v___x_3445_);
lean_ctor_set(v___x_3429_, 0, v___x_3441_);
v___x_3447_ = v___x_3429_;
goto v_reusejp_3446_;
}
else
{
lean_object* v_reuseFailAlloc_3473_; 
v_reuseFailAlloc_3473_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3473_, 0, v___x_3441_);
lean_ctor_set(v_reuseFailAlloc_3473_, 1, v___x_3445_);
v___x_3447_ = v_reuseFailAlloc_3473_;
goto v_reusejp_3446_;
}
v_reusejp_3446_:
{
lean_object* v___x_3448_; lean_object* v___x_3450_; 
v___x_3448_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___closed__5, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___closed__5);
if (v_isShared_3425_ == 0)
{
lean_ctor_set_tag(v___x_3424_, 7);
lean_ctor_set(v___x_3424_, 1, v___x_3448_);
lean_ctor_set(v___x_3424_, 0, v___x_3447_);
v___x_3450_ = v___x_3424_;
goto v_reusejp_3449_;
}
else
{
lean_object* v_reuseFailAlloc_3472_; 
v_reuseFailAlloc_3472_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3472_, 0, v___x_3447_);
lean_ctor_set(v_reuseFailAlloc_3472_, 1, v___x_3448_);
v___x_3450_ = v_reuseFailAlloc_3472_;
goto v_reusejp_3449_;
}
v_reusejp_3449_:
{
lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; size_t v_sz_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; 
v___x_3451_ = lean_array_to_list(v_fst_3426_);
v___x_3452_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_3451_, v___x_3443_);
v___x_3453_ = l_Lean_MessageData_ofList(v___x_3452_);
v___x_3454_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3454_, 0, v___x_3450_);
lean_ctor_set(v___x_3454_, 1, v___x_3453_);
v___x_3455_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___closed__7, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___closed__7);
v___x_3456_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3456_, 0, v___x_3454_);
lean_ctor_set(v___x_3456_, 1, v___x_3455_);
v_sz_3457_ = lean_array_size(v_snd_3427_);
lean_inc(v_snd_3427_);
v___x_3458_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__11(v_sz_3457_, v___x_3354_, v_snd_3427_);
v___x_3459_ = lean_array_to_list(v___x_3458_);
v___x_3460_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_3459_, v___x_3443_);
v___x_3461_ = l_Lean_MessageData_ofList(v___x_3460_);
v___x_3462_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3462_, 0, v___x_3456_);
lean_ctor_set(v___x_3462_, 1, v___x_3461_);
v___x_3463_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12(v___x_3385_, v___x_3462_, v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_);
if (lean_obj_tag(v___x_3463_) == 0)
{
lean_dec_ref(v___x_3463_);
v___y_3387_ = v___x_3433_;
v___y_3388_ = v___f_3434_;
v___y_3389_ = v_snd_3427_;
v___y_3390_ = v___y_3415_;
v___y_3391_ = v___y_3416_;
v___y_3392_ = v___y_3417_;
v___y_3393_ = v___y_3418_;
goto v___jp_3386_;
}
else
{
lean_object* v_a_3464_; lean_object* v___x_3466_; uint8_t v_isShared_3467_; uint8_t v_isSharedCheck_3471_; 
lean_dec_ref(v___f_3434_);
lean_dec_ref(v___x_3433_);
lean_dec(v_snd_3427_);
v_a_3464_ = lean_ctor_get(v___x_3463_, 0);
v_isSharedCheck_3471_ = !lean_is_exclusive(v___x_3463_);
if (v_isSharedCheck_3471_ == 0)
{
v___x_3466_ = v___x_3463_;
v_isShared_3467_ = v_isSharedCheck_3471_;
goto v_resetjp_3465_;
}
else
{
lean_inc(v_a_3464_);
lean_dec(v___x_3463_);
v___x_3466_ = lean_box(0);
v_isShared_3467_ = v_isSharedCheck_3471_;
goto v_resetjp_3465_;
}
v_resetjp_3465_:
{
lean_object* v___x_3469_; 
if (v_isShared_3467_ == 0)
{
v___x_3469_ = v___x_3466_;
goto v_reusejp_3468_;
}
else
{
lean_object* v_reuseFailAlloc_3470_; 
v_reuseFailAlloc_3470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3470_, 0, v_a_3464_);
v___x_3469_ = v_reuseFailAlloc_3470_;
goto v_reusejp_3468_;
}
v_reusejp_3468_:
{
return v___x_3469_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3474_; 
lean_dec_ref(v___x_3433_);
lean_del_object(v___x_3429_);
lean_dec(v_fst_3426_);
lean_del_object(v___x_3424_);
lean_dec_ref(v_xs_3356_);
lean_inc_ref(v___y_3415_);
v___x_3474_ = l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___redArg(v_snd_3427_, v___f_3434_, v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_);
lean_dec(v_snd_3427_);
return v___x_3474_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___boxed(lean_object* v___x_3493_, lean_object* v_a_3494_, lean_object* v_xs_3495_, lean_object* v___x_3496_, lean_object* v_a_3497_, lean_object* v_recArgInfos_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_){
_start:
{
size_t v___x_14880__boxed_3504_; lean_object* v_res_3505_; 
v___x_14880__boxed_3504_ = lean_unbox_usize(v___x_3493_);
lean_dec(v___x_3493_);
v_res_3505_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1(v___x_14880__boxed_3504_, v_a_3494_, v_xs_3495_, v___x_3496_, v_a_3497_, v_recArgInfos_3498_, v___y_3499_, v___y_3500_, v___y_3501_, v___y_3502_);
lean_dec(v___y_3502_);
lean_dec_ref(v___y_3501_);
lean_dec(v___y_3500_);
lean_dec_ref(v___y_3499_);
return v_res_3505_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg(lean_object* v___x_3506_, lean_object* v_xs_3507_, lean_object* v_as_3508_, lean_object* v_i_3509_, lean_object* v_j_3510_, lean_object* v_bs_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_){
_start:
{
lean_object* v_zero_3517_; uint8_t v_isZero_3518_; 
v_zero_3517_ = lean_unsigned_to_nat(0u);
v_isZero_3518_ = lean_nat_dec_eq(v_i_3509_, v_zero_3517_);
if (v_isZero_3518_ == 1)
{
lean_object* v___x_3519_; 
lean_dec(v_j_3510_);
lean_dec(v_i_3509_);
lean_dec_ref(v_xs_3507_);
v___x_3519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3519_, 0, v_bs_3511_);
return v___x_3519_;
}
else
{
lean_object* v___x_3520_; lean_object* v_value_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; 
v___x_3520_ = lean_array_fget_borrowed(v_as_3508_, v_j_3510_);
v_value_3521_ = lean_ctor_get(v___x_3520_, 7);
v___x_3522_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9___redArg___closed__0, &l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9___redArg___closed__0_once, _init_l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9___redArg___closed__0);
v___x_3523_ = lean_array_get_borrowed(v___x_3522_, v___x_3506_, v_j_3510_);
lean_inc_ref(v_xs_3507_);
lean_inc_ref(v_value_3521_);
lean_inc(v___x_3523_);
v___x_3524_ = l_Lean_Elab_FixedParamPerm_instantiateLambda(v___x_3523_, v_value_3521_, v_xs_3507_, v___y_3512_, v___y_3513_, v___y_3514_, v___y_3515_);
if (lean_obj_tag(v___x_3524_) == 0)
{
lean_object* v_a_3525_; lean_object* v_one_3526_; lean_object* v_n_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; 
v_a_3525_ = lean_ctor_get(v___x_3524_, 0);
lean_inc(v_a_3525_);
lean_dec_ref(v___x_3524_);
v_one_3526_ = lean_unsigned_to_nat(1u);
v_n_3527_ = lean_nat_sub(v_i_3509_, v_one_3526_);
lean_dec(v_i_3509_);
v___x_3528_ = lean_nat_add(v_j_3510_, v_one_3526_);
lean_dec(v_j_3510_);
v___x_3529_ = lean_array_push(v_bs_3511_, v_a_3525_);
v_i_3509_ = v_n_3527_;
v_j_3510_ = v___x_3528_;
v_bs_3511_ = v___x_3529_;
goto _start;
}
else
{
lean_object* v_a_3531_; lean_object* v___x_3533_; uint8_t v_isShared_3534_; uint8_t v_isSharedCheck_3538_; 
lean_dec_ref(v_bs_3511_);
lean_dec(v_j_3510_);
lean_dec(v_i_3509_);
lean_dec_ref(v_xs_3507_);
v_a_3531_ = lean_ctor_get(v___x_3524_, 0);
v_isSharedCheck_3538_ = !lean_is_exclusive(v___x_3524_);
if (v_isSharedCheck_3538_ == 0)
{
v___x_3533_ = v___x_3524_;
v_isShared_3534_ = v_isSharedCheck_3538_;
goto v_resetjp_3532_;
}
else
{
lean_inc(v_a_3531_);
lean_dec(v___x_3524_);
v___x_3533_ = lean_box(0);
v_isShared_3534_ = v_isSharedCheck_3538_;
goto v_resetjp_3532_;
}
v_resetjp_3532_:
{
lean_object* v___x_3536_; 
if (v_isShared_3534_ == 0)
{
v___x_3536_ = v___x_3533_;
goto v_reusejp_3535_;
}
else
{
lean_object* v_reuseFailAlloc_3537_; 
v_reuseFailAlloc_3537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3537_, 0, v_a_3531_);
v___x_3536_ = v_reuseFailAlloc_3537_;
goto v_reusejp_3535_;
}
v_reusejp_3535_:
{
return v___x_3536_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg___boxed(lean_object* v___x_3539_, lean_object* v_xs_3540_, lean_object* v_as_3541_, lean_object* v_i_3542_, lean_object* v_j_3543_, lean_object* v_bs_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_){
_start:
{
lean_object* v_res_3550_; 
v_res_3550_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg(v___x_3539_, v_xs_3540_, v_as_3541_, v_i_3542_, v_j_3543_, v_bs_3544_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_);
lean_dec(v___y_3548_);
lean_dec_ref(v___y_3547_);
lean_dec(v___y_3546_);
lean_dec_ref(v___y_3545_);
lean_dec_ref(v_as_3541_);
lean_dec_ref(v___x_3539_);
return v_res_3550_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__2(lean_object* v_a_3551_, lean_object* v_perms_3552_, lean_object* v___x_3553_, lean_object* v_fnNames_3554_, lean_object* v_a_3555_, lean_object* v_termMeasure_x3fs_3556_, size_t v___x_3557_, lean_object* v_xs_3558_, lean_object* v___y_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_){
_start:
{
lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; 
v___x_3564_ = lean_array_get_size(v_a_3551_);
v___x_3565_ = lean_mk_empty_array_with_capacity(v___x_3564_);
lean_inc(v___x_3553_);
lean_inc_ref(v_xs_3558_);
v___x_3566_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg(v_perms_3552_, v_xs_3558_, v_a_3551_, v___x_3564_, v___x_3553_, v___x_3565_, v___y_3559_, v___y_3560_, v___y_3561_, v___y_3562_);
if (lean_obj_tag(v___x_3566_) == 0)
{
lean_object* v_a_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; 
v_a_3567_ = lean_ctor_get(v___x_3566_, 0);
lean_inc(v_a_3567_);
lean_dec_ref(v___x_3566_);
lean_inc(v_a_3567_);
lean_inc_ref(v_xs_3558_);
lean_inc_ref(v_a_3555_);
lean_inc_ref(v_fnNames_3554_);
v___x_3568_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_findRecArgCandidates___boxed), 10, 5);
lean_closure_set(v___x_3568_, 0, v_fnNames_3554_);
lean_closure_set(v___x_3568_, 1, v_a_3555_);
lean_closure_set(v___x_3568_, 2, v_xs_3558_);
lean_closure_set(v___x_3568_, 3, v_a_3567_);
lean_closure_set(v___x_3568_, 4, v_termMeasure_x3fs_3556_);
lean_inc_ref(v_a_3551_);
v___x_3569_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13___redArg(v_a_3551_, v___x_3568_, v___y_3559_, v___y_3560_, v___y_3561_, v___y_3562_);
if (lean_obj_tag(v___x_3569_) == 0)
{
lean_object* v_a_3570_; lean_object* v___x_3571_; lean_object* v___f_3572_; lean_object* v___x_3573_; 
v_a_3570_ = lean_ctor_get(v___x_3569_, 0);
lean_inc(v_a_3570_);
lean_dec_ref(v___x_3569_);
v___x_3571_ = lean_box_usize(v___x_3557_);
lean_inc_ref(v_xs_3558_);
v___f_3572_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___boxed), 11, 5);
lean_closure_set(v___f_3572_, 0, v___x_3571_);
lean_closure_set(v___f_3572_, 1, v_a_3555_);
lean_closure_set(v___f_3572_, 2, v_xs_3558_);
lean_closure_set(v___f_3572_, 3, v___x_3553_);
lean_closure_set(v___f_3572_, 4, v_a_3551_);
v___x_3573_ = l_Lean_Elab_Structural_tryCandidates___redArg(v_fnNames_3554_, v_xs_3558_, v_a_3567_, v_a_3570_, v___f_3572_, v___y_3559_, v___y_3560_, v___y_3561_, v___y_3562_);
lean_dec_ref(v_fnNames_3554_);
return v___x_3573_;
}
else
{
lean_object* v_a_3574_; lean_object* v___x_3576_; uint8_t v_isShared_3577_; uint8_t v_isSharedCheck_3581_; 
lean_dec(v_a_3567_);
lean_dec_ref(v_xs_3558_);
lean_dec_ref(v_a_3555_);
lean_dec_ref(v_fnNames_3554_);
lean_dec(v___x_3553_);
lean_dec_ref(v_a_3551_);
v_a_3574_ = lean_ctor_get(v___x_3569_, 0);
v_isSharedCheck_3581_ = !lean_is_exclusive(v___x_3569_);
if (v_isSharedCheck_3581_ == 0)
{
v___x_3576_ = v___x_3569_;
v_isShared_3577_ = v_isSharedCheck_3581_;
goto v_resetjp_3575_;
}
else
{
lean_inc(v_a_3574_);
lean_dec(v___x_3569_);
v___x_3576_ = lean_box(0);
v_isShared_3577_ = v_isSharedCheck_3581_;
goto v_resetjp_3575_;
}
v_resetjp_3575_:
{
lean_object* v___x_3579_; 
if (v_isShared_3577_ == 0)
{
v___x_3579_ = v___x_3576_;
goto v_reusejp_3578_;
}
else
{
lean_object* v_reuseFailAlloc_3580_; 
v_reuseFailAlloc_3580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3580_, 0, v_a_3574_);
v___x_3579_ = v_reuseFailAlloc_3580_;
goto v_reusejp_3578_;
}
v_reusejp_3578_:
{
return v___x_3579_;
}
}
}
}
else
{
lean_object* v_a_3582_; lean_object* v___x_3584_; uint8_t v_isShared_3585_; uint8_t v_isSharedCheck_3589_; 
lean_dec_ref(v_xs_3558_);
lean_dec_ref(v_termMeasure_x3fs_3556_);
lean_dec_ref(v_a_3555_);
lean_dec_ref(v_fnNames_3554_);
lean_dec(v___x_3553_);
lean_dec_ref(v_a_3551_);
v_a_3582_ = lean_ctor_get(v___x_3566_, 0);
v_isSharedCheck_3589_ = !lean_is_exclusive(v___x_3566_);
if (v_isSharedCheck_3589_ == 0)
{
v___x_3584_ = v___x_3566_;
v_isShared_3585_ = v_isSharedCheck_3589_;
goto v_resetjp_3583_;
}
else
{
lean_inc(v_a_3582_);
lean_dec(v___x_3566_);
v___x_3584_ = lean_box(0);
v_isShared_3585_ = v_isSharedCheck_3589_;
goto v_resetjp_3583_;
}
v_resetjp_3583_:
{
lean_object* v___x_3587_; 
if (v_isShared_3585_ == 0)
{
v___x_3587_ = v___x_3584_;
goto v_reusejp_3586_;
}
else
{
lean_object* v_reuseFailAlloc_3588_; 
v_reuseFailAlloc_3588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3588_, 0, v_a_3582_);
v___x_3587_ = v_reuseFailAlloc_3588_;
goto v_reusejp_3586_;
}
v_reusejp_3586_:
{
return v___x_3587_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__2___boxed(lean_object* v_a_3590_, lean_object* v_perms_3591_, lean_object* v___x_3592_, lean_object* v_fnNames_3593_, lean_object* v_a_3594_, lean_object* v_termMeasure_x3fs_3595_, lean_object* v___x_3596_, lean_object* v_xs_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_){
_start:
{
size_t v___x_15237__boxed_3603_; lean_object* v_res_3604_; 
v___x_15237__boxed_3603_ = lean_unbox_usize(v___x_3596_);
lean_dec(v___x_3596_);
v_res_3604_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__2(v_a_3590_, v_perms_3591_, v___x_3592_, v_fnNames_3593_, v_a_3594_, v_termMeasure_x3fs_3595_, v___x_15237__boxed_3603_, v_xs_3597_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_);
lean_dec(v___y_3601_);
lean_dec_ref(v___y_3600_);
lean_dec(v___y_3599_);
lean_dec_ref(v___y_3598_);
lean_dec_ref(v_perms_3591_);
return v_res_3604_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0(size_t v_sz_3605_, size_t v_i_3606_, lean_object* v_bs_3607_){
_start:
{
uint8_t v___x_3608_; 
v___x_3608_ = lean_usize_dec_lt(v_i_3606_, v_sz_3605_);
if (v___x_3608_ == 0)
{
return v_bs_3607_;
}
else
{
lean_object* v_v_3609_; lean_object* v_declName_3610_; lean_object* v___x_3611_; lean_object* v_bs_x27_3612_; size_t v___x_3613_; size_t v___x_3614_; lean_object* v___x_3615_; 
v_v_3609_ = lean_array_uget_borrowed(v_bs_3607_, v_i_3606_);
v_declName_3610_ = lean_ctor_get(v_v_3609_, 3);
lean_inc(v_declName_3610_);
v___x_3611_ = lean_unsigned_to_nat(0u);
v_bs_x27_3612_ = lean_array_uset(v_bs_3607_, v_i_3606_, v___x_3611_);
v___x_3613_ = ((size_t)1ULL);
v___x_3614_ = lean_usize_add(v_i_3606_, v___x_3613_);
v___x_3615_ = lean_array_uset(v_bs_x27_3612_, v_i_3606_, v_declName_3610_);
v_i_3606_ = v___x_3614_;
v_bs_3607_ = v___x_3615_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0___boxed(lean_object* v_sz_3617_, lean_object* v_i_3618_, lean_object* v_bs_3619_){
_start:
{
size_t v_sz_boxed_3620_; size_t v_i_boxed_3621_; lean_object* v_res_3622_; 
v_sz_boxed_3620_ = lean_unbox_usize(v_sz_3617_);
lean_dec(v_sz_3617_);
v_i_boxed_3621_ = lean_unbox_usize(v_i_3618_);
lean_dec(v_i_3618_);
v_res_3622_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0(v_sz_boxed_3620_, v_i_boxed_3621_, v_bs_3619_);
return v_res_3622_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1___redArg(lean_object* v_fnNames_3623_, lean_object* v_numSectionVars_3624_, size_t v_sz_3625_, size_t v_i_3626_, lean_object* v_bs_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_){
_start:
{
uint8_t v___x_3631_; 
v___x_3631_ = lean_usize_dec_lt(v_i_3626_, v_sz_3625_);
if (v___x_3631_ == 0)
{
lean_object* v___x_3632_; 
lean_dec(v_numSectionVars_3624_);
lean_dec_ref(v_fnNames_3623_);
v___x_3632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3632_, 0, v_bs_3627_);
return v___x_3632_;
}
else
{
lean_object* v_v_3633_; lean_object* v_ref_3634_; uint8_t v_kind_3635_; lean_object* v_levelParams_3636_; lean_object* v_modifiers_3637_; lean_object* v_declName_3638_; lean_object* v_binders_3639_; lean_object* v_numSectionVars_3640_; lean_object* v_type_3641_; lean_object* v_value_3642_; lean_object* v_termination_3643_; lean_object* v___x_3645_; uint8_t v_isShared_3646_; uint8_t v_isSharedCheck_3666_; 
v_v_3633_ = lean_array_uget(v_bs_3627_, v_i_3626_);
v_ref_3634_ = lean_ctor_get(v_v_3633_, 0);
v_kind_3635_ = lean_ctor_get_uint8(v_v_3633_, sizeof(void*)*9);
v_levelParams_3636_ = lean_ctor_get(v_v_3633_, 1);
v_modifiers_3637_ = lean_ctor_get(v_v_3633_, 2);
v_declName_3638_ = lean_ctor_get(v_v_3633_, 3);
v_binders_3639_ = lean_ctor_get(v_v_3633_, 4);
v_numSectionVars_3640_ = lean_ctor_get(v_v_3633_, 5);
v_type_3641_ = lean_ctor_get(v_v_3633_, 6);
v_value_3642_ = lean_ctor_get(v_v_3633_, 7);
v_termination_3643_ = lean_ctor_get(v_v_3633_, 8);
v_isSharedCheck_3666_ = !lean_is_exclusive(v_v_3633_);
if (v_isSharedCheck_3666_ == 0)
{
v___x_3645_ = v_v_3633_;
v_isShared_3646_ = v_isSharedCheck_3666_;
goto v_resetjp_3644_;
}
else
{
lean_inc(v_termination_3643_);
lean_inc(v_value_3642_);
lean_inc(v_type_3641_);
lean_inc(v_numSectionVars_3640_);
lean_inc(v_binders_3639_);
lean_inc(v_declName_3638_);
lean_inc(v_modifiers_3637_);
lean_inc(v_levelParams_3636_);
lean_inc(v_ref_3634_);
lean_dec(v_v_3633_);
v___x_3645_ = lean_box(0);
v_isShared_3646_ = v_isSharedCheck_3666_;
goto v_resetjp_3644_;
}
v_resetjp_3644_:
{
lean_object* v___x_3647_; 
lean_inc(v_numSectionVars_3624_);
lean_inc_ref(v_fnNames_3623_);
v___x_3647_ = l_Lean_Elab_Structural_preprocess(v_value_3642_, v_fnNames_3623_, v_numSectionVars_3624_, v___y_3628_, v___y_3629_);
if (lean_obj_tag(v___x_3647_) == 0)
{
lean_object* v_a_3648_; lean_object* v___x_3649_; lean_object* v_bs_x27_3650_; lean_object* v___x_3652_; 
v_a_3648_ = lean_ctor_get(v___x_3647_, 0);
lean_inc(v_a_3648_);
lean_dec_ref(v___x_3647_);
v___x_3649_ = lean_unsigned_to_nat(0u);
v_bs_x27_3650_ = lean_array_uset(v_bs_3627_, v_i_3626_, v___x_3649_);
if (v_isShared_3646_ == 0)
{
lean_ctor_set(v___x_3645_, 7, v_a_3648_);
v___x_3652_ = v___x_3645_;
goto v_reusejp_3651_;
}
else
{
lean_object* v_reuseFailAlloc_3657_; 
v_reuseFailAlloc_3657_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_3657_, 0, v_ref_3634_);
lean_ctor_set(v_reuseFailAlloc_3657_, 1, v_levelParams_3636_);
lean_ctor_set(v_reuseFailAlloc_3657_, 2, v_modifiers_3637_);
lean_ctor_set(v_reuseFailAlloc_3657_, 3, v_declName_3638_);
lean_ctor_set(v_reuseFailAlloc_3657_, 4, v_binders_3639_);
lean_ctor_set(v_reuseFailAlloc_3657_, 5, v_numSectionVars_3640_);
lean_ctor_set(v_reuseFailAlloc_3657_, 6, v_type_3641_);
lean_ctor_set(v_reuseFailAlloc_3657_, 7, v_a_3648_);
lean_ctor_set(v_reuseFailAlloc_3657_, 8, v_termination_3643_);
lean_ctor_set_uint8(v_reuseFailAlloc_3657_, sizeof(void*)*9, v_kind_3635_);
v___x_3652_ = v_reuseFailAlloc_3657_;
goto v_reusejp_3651_;
}
v_reusejp_3651_:
{
size_t v___x_3653_; size_t v___x_3654_; lean_object* v___x_3655_; 
v___x_3653_ = ((size_t)1ULL);
v___x_3654_ = lean_usize_add(v_i_3626_, v___x_3653_);
v___x_3655_ = lean_array_uset(v_bs_x27_3650_, v_i_3626_, v___x_3652_);
v_i_3626_ = v___x_3654_;
v_bs_3627_ = v___x_3655_;
goto _start;
}
}
else
{
lean_object* v_a_3658_; lean_object* v___x_3660_; uint8_t v_isShared_3661_; uint8_t v_isSharedCheck_3665_; 
lean_del_object(v___x_3645_);
lean_dec_ref(v_termination_3643_);
lean_dec_ref(v_type_3641_);
lean_dec(v_numSectionVars_3640_);
lean_dec(v_binders_3639_);
lean_dec(v_declName_3638_);
lean_dec_ref(v_modifiers_3637_);
lean_dec(v_levelParams_3636_);
lean_dec(v_ref_3634_);
lean_dec_ref(v_bs_3627_);
lean_dec(v_numSectionVars_3624_);
lean_dec_ref(v_fnNames_3623_);
v_a_3658_ = lean_ctor_get(v___x_3647_, 0);
v_isSharedCheck_3665_ = !lean_is_exclusive(v___x_3647_);
if (v_isSharedCheck_3665_ == 0)
{
v___x_3660_ = v___x_3647_;
v_isShared_3661_ = v_isSharedCheck_3665_;
goto v_resetjp_3659_;
}
else
{
lean_inc(v_a_3658_);
lean_dec(v___x_3647_);
v___x_3660_ = lean_box(0);
v_isShared_3661_ = v_isSharedCheck_3665_;
goto v_resetjp_3659_;
}
v_resetjp_3659_:
{
lean_object* v___x_3663_; 
if (v_isShared_3661_ == 0)
{
v___x_3663_ = v___x_3660_;
goto v_reusejp_3662_;
}
else
{
lean_object* v_reuseFailAlloc_3664_; 
v_reuseFailAlloc_3664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3664_, 0, v_a_3658_);
v___x_3663_ = v_reuseFailAlloc_3664_;
goto v_reusejp_3662_;
}
v_reusejp_3662_:
{
return v___x_3663_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1___redArg___boxed(lean_object* v_fnNames_3667_, lean_object* v_numSectionVars_3668_, lean_object* v_sz_3669_, lean_object* v_i_3670_, lean_object* v_bs_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_){
_start:
{
size_t v_sz_boxed_3675_; size_t v_i_boxed_3676_; lean_object* v_res_3677_; 
v_sz_boxed_3675_ = lean_unbox_usize(v_sz_3669_);
lean_dec(v_sz_3669_);
v_i_boxed_3676_ = lean_unbox_usize(v_i_3670_);
lean_dec(v_i_3670_);
v_res_3677_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1___redArg(v_fnNames_3667_, v_numSectionVars_3668_, v_sz_boxed_3675_, v_i_boxed_3676_, v_bs_3671_, v___y_3672_, v___y_3673_);
lean_dec(v___y_3673_);
lean_dec_ref(v___y_3672_);
return v_res_3677_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1(lean_object* v_fnNames_3678_, lean_object* v_numSectionVars_3679_, size_t v_sz_3680_, size_t v_i_3681_, lean_object* v_bs_3682_, lean_object* v___y_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_){
_start:
{
lean_object* v___x_3688_; 
v___x_3688_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1___redArg(v_fnNames_3678_, v_numSectionVars_3679_, v_sz_3680_, v_i_3681_, v_bs_3682_, v___y_3685_, v___y_3686_);
return v___x_3688_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1___boxed(lean_object* v_fnNames_3689_, lean_object* v_numSectionVars_3690_, lean_object* v_sz_3691_, lean_object* v_i_3692_, lean_object* v_bs_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_){
_start:
{
size_t v_sz_boxed_3699_; size_t v_i_boxed_3700_; lean_object* v_res_3701_; 
v_sz_boxed_3699_ = lean_unbox_usize(v_sz_3691_);
lean_dec(v_sz_3691_);
v_i_boxed_3700_ = lean_unbox_usize(v_i_3692_);
lean_dec(v_i_3692_);
v_res_3701_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1(v_fnNames_3689_, v_numSectionVars_3690_, v_sz_boxed_3699_, v_i_boxed_3700_, v_bs_3693_, v___y_3694_, v___y_3695_, v___y_3696_, v___y_3697_);
lean_dec(v___y_3697_);
lean_dec_ref(v___y_3696_);
lean_dec(v___y_3695_);
lean_dec_ref(v___y_3694_);
return v_res_3701_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos(lean_object* v_preDefs_3702_, lean_object* v_termMeasure_x3fs_3703_, lean_object* v_a_3704_, lean_object* v_a_3705_, lean_object* v_a_3706_, lean_object* v_a_3707_){
_start:
{
lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v_numSectionVars_3712_; size_t v_sz_3713_; size_t v___x_3714_; lean_object* v_fnNames_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; 
v___x_3709_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_3710_ = lean_unsigned_to_nat(0u);
v___x_3711_ = lean_array_get_borrowed(v___x_3709_, v_preDefs_3702_, v___x_3710_);
v_numSectionVars_3712_ = lean_ctor_get(v___x_3711_, 5);
v_sz_3713_ = lean_array_size(v_preDefs_3702_);
v___x_3714_ = ((size_t)0ULL);
lean_inc_ref(v_preDefs_3702_);
v_fnNames_3715_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0(v_sz_3713_, v___x_3714_, v_preDefs_3702_);
v___x_3716_ = lean_box_usize(v_sz_3713_);
v___x_3717_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13___redArg___boxed__const__1));
lean_inc_ref(v_preDefs_3702_);
lean_inc(v_numSectionVars_3712_);
lean_inc_ref(v_fnNames_3715_);
v___x_3718_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1___boxed), 10, 5);
lean_closure_set(v___x_3718_, 0, v_fnNames_3715_);
lean_closure_set(v___x_3718_, 1, v_numSectionVars_3712_);
lean_closure_set(v___x_3718_, 2, v___x_3716_);
lean_closure_set(v___x_3718_, 3, v___x_3717_);
lean_closure_set(v___x_3718_, 4, v_preDefs_3702_);
v___x_3719_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13___redArg(v_preDefs_3702_, v___x_3718_, v_a_3704_, v_a_3705_, v_a_3706_, v_a_3707_);
if (lean_obj_tag(v___x_3719_) == 0)
{
lean_object* v_a_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; 
v_a_3720_ = lean_ctor_get(v___x_3719_, 0);
lean_inc(v_a_3720_);
lean_dec_ref(v___x_3719_);
lean_inc(v_a_3720_);
v___x_3721_ = lean_alloc_closure((void*)(l_Lean_Elab_getFixedParamPerms___boxed), 6, 1);
lean_closure_set(v___x_3721_, 0, v_a_3720_);
lean_inc(v_a_3720_);
v___x_3722_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13___redArg(v_a_3720_, v___x_3721_, v_a_3704_, v_a_3705_, v_a_3706_, v_a_3707_);
if (lean_obj_tag(v___x_3722_) == 0)
{
lean_object* v_a_3723_; lean_object* v_perms_3724_; lean_object* v___x_3725_; lean_object* v_type_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___f_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; 
v_a_3723_ = lean_ctor_get(v___x_3722_, 0);
lean_inc(v_a_3723_);
lean_dec_ref(v___x_3722_);
v_perms_3724_ = lean_ctor_get(v_a_3723_, 1);
lean_inc_ref(v_perms_3724_);
v___x_3725_ = lean_array_get_borrowed(v___x_3709_, v_a_3720_, v___x_3710_);
v_type_3726_ = lean_ctor_get(v___x_3725_, 6);
lean_inc_ref(v_type_3726_);
v___x_3727_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9___redArg___closed__0, &l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9___redArg___closed__0_once, _init_l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9___redArg___closed__0);
v___x_3728_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13___redArg___boxed__const__1));
lean_inc_ref(v_perms_3724_);
v___f_3729_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__2___boxed), 13, 7);
lean_closure_set(v___f_3729_, 0, v_a_3720_);
lean_closure_set(v___f_3729_, 1, v_perms_3724_);
lean_closure_set(v___f_3729_, 2, v___x_3710_);
lean_closure_set(v___f_3729_, 3, v_fnNames_3715_);
lean_closure_set(v___f_3729_, 4, v_a_3723_);
lean_closure_set(v___f_3729_, 5, v_termMeasure_x3fs_3703_);
lean_closure_set(v___f_3729_, 6, v___x_3728_);
v___x_3730_ = lean_array_get(v___x_3727_, v_perms_3724_, v___x_3710_);
lean_dec_ref(v_perms_3724_);
v___x_3731_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg(v___x_3730_, v_type_3726_, v___f_3729_, v_a_3704_, v_a_3705_, v_a_3706_, v_a_3707_);
return v___x_3731_;
}
else
{
lean_object* v_a_3732_; lean_object* v___x_3734_; uint8_t v_isShared_3735_; uint8_t v_isSharedCheck_3739_; 
lean_dec(v_a_3720_);
lean_dec_ref(v_fnNames_3715_);
lean_dec_ref(v_termMeasure_x3fs_3703_);
v_a_3732_ = lean_ctor_get(v___x_3722_, 0);
v_isSharedCheck_3739_ = !lean_is_exclusive(v___x_3722_);
if (v_isSharedCheck_3739_ == 0)
{
v___x_3734_ = v___x_3722_;
v_isShared_3735_ = v_isSharedCheck_3739_;
goto v_resetjp_3733_;
}
else
{
lean_inc(v_a_3732_);
lean_dec(v___x_3722_);
v___x_3734_ = lean_box(0);
v_isShared_3735_ = v_isSharedCheck_3739_;
goto v_resetjp_3733_;
}
v_resetjp_3733_:
{
lean_object* v___x_3737_; 
if (v_isShared_3735_ == 0)
{
v___x_3737_ = v___x_3734_;
goto v_reusejp_3736_;
}
else
{
lean_object* v_reuseFailAlloc_3738_; 
v_reuseFailAlloc_3738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3738_, 0, v_a_3732_);
v___x_3737_ = v_reuseFailAlloc_3738_;
goto v_reusejp_3736_;
}
v_reusejp_3736_:
{
return v___x_3737_;
}
}
}
}
else
{
lean_object* v_a_3740_; lean_object* v___x_3742_; uint8_t v_isShared_3743_; uint8_t v_isSharedCheck_3747_; 
lean_dec_ref(v_fnNames_3715_);
lean_dec_ref(v_termMeasure_x3fs_3703_);
v_a_3740_ = lean_ctor_get(v___x_3719_, 0);
v_isSharedCheck_3747_ = !lean_is_exclusive(v___x_3719_);
if (v_isSharedCheck_3747_ == 0)
{
v___x_3742_ = v___x_3719_;
v_isShared_3743_ = v_isSharedCheck_3747_;
goto v_resetjp_3741_;
}
else
{
lean_inc(v_a_3740_);
lean_dec(v___x_3719_);
v___x_3742_ = lean_box(0);
v_isShared_3743_ = v_isSharedCheck_3747_;
goto v_resetjp_3741_;
}
v_resetjp_3741_:
{
lean_object* v___x_3745_; 
if (v_isShared_3743_ == 0)
{
v___x_3745_ = v___x_3742_;
goto v_reusejp_3744_;
}
else
{
lean_object* v_reuseFailAlloc_3746_; 
v_reuseFailAlloc_3746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3746_, 0, v_a_3740_);
v___x_3745_ = v_reuseFailAlloc_3746_;
goto v_reusejp_3744_;
}
v_reusejp_3744_:
{
return v___x_3745_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___boxed(lean_object* v_preDefs_3748_, lean_object* v_termMeasure_x3fs_3749_, lean_object* v_a_3750_, lean_object* v_a_3751_, lean_object* v_a_3752_, lean_object* v_a_3753_, lean_object* v_a_3754_){
_start:
{
lean_object* v_res_3755_; 
v_res_3755_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos(v_preDefs_3748_, v_termMeasure_x3fs_3749_, v_a_3750_, v_a_3751_, v_a_3752_, v_a_3753_);
lean_dec(v_a_3753_);
lean_dec_ref(v_a_3752_);
lean_dec(v_a_3751_);
lean_dec_ref(v_a_3750_);
return v_res_3755_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4(lean_object* v_fst_3756_, lean_object* v_as_3757_, lean_object* v_i_3758_, lean_object* v_j_3759_, lean_object* v_inv_3760_, lean_object* v_bs_3761_){
_start:
{
lean_object* v___x_3762_; 
v___x_3762_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg(v_fst_3756_, v_as_3757_, v_i_3758_, v_j_3759_, v_bs_3761_);
return v___x_3762_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___boxed(lean_object* v_fst_3763_, lean_object* v_as_3764_, lean_object* v_i_3765_, lean_object* v_j_3766_, lean_object* v_inv_3767_, lean_object* v_bs_3768_){
_start:
{
lean_object* v_res_3769_; 
v_res_3769_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4(v_fst_3763_, v_as_3764_, v_i_3765_, v_j_3766_, v_inv_3767_, v_bs_3768_);
lean_dec_ref(v_as_3764_);
lean_dec_ref(v_fst_3763_);
return v_res_3769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10(lean_object* v_00_u03b1_3770_, lean_object* v_lctx_3771_, lean_object* v_localInsts_3772_, lean_object* v_x_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_){
_start:
{
lean_object* v___x_3779_; 
v___x_3779_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___redArg(v_lctx_3771_, v_localInsts_3772_, v_x_3773_, v___y_3774_, v___y_3775_, v___y_3776_, v___y_3777_);
return v___x_3779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___boxed(lean_object* v_00_u03b1_3780_, lean_object* v_lctx_3781_, lean_object* v_localInsts_3782_, lean_object* v_x_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_){
_start:
{
lean_object* v_res_3789_; 
v_res_3789_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10(v_00_u03b1_3780_, v_lctx_3781_, v_localInsts_3782_, v_x_3783_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_);
lean_dec(v___y_3787_);
lean_dec_ref(v___y_3786_);
lean_dec(v___y_3785_);
lean_dec_ref(v___y_3784_);
return v_res_3789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9(lean_object* v_00_u03b1_3790_, lean_object* v_fvarIds_3791_, lean_object* v_k_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_){
_start:
{
lean_object* v___x_3798_; 
lean_inc_ref(v___y_3793_);
v___x_3798_ = l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___redArg(v_fvarIds_3791_, v_k_3792_, v___y_3793_, v___y_3794_, v___y_3795_, v___y_3796_);
return v___x_3798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___boxed(lean_object* v_00_u03b1_3799_, lean_object* v_fvarIds_3800_, lean_object* v_k_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_){
_start:
{
lean_object* v_res_3807_; 
v_res_3807_ = l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9(v_00_u03b1_3799_, v_fvarIds_3800_, v_k_3801_, v___y_3802_, v___y_3803_, v___y_3804_, v___y_3805_);
lean_dec(v___y_3805_);
lean_dec_ref(v___y_3804_);
lean_dec(v___y_3803_);
lean_dec_ref(v___y_3802_);
lean_dec_ref(v_fvarIds_3800_);
return v_res_3807_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__15(lean_object* v_a_3808_){
_start:
{
lean_object* v___x_3809_; 
v___x_3809_ = lean_nat_to_int(v_a_3808_);
return v___x_3809_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12(lean_object* v___x_3810_, lean_object* v_xs_3811_, lean_object* v_as_3812_, lean_object* v_i_3813_, lean_object* v_j_3814_, lean_object* v_inv_3815_, lean_object* v_bs_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_){
_start:
{
lean_object* v___x_3822_; 
v___x_3822_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg(v___x_3810_, v_xs_3811_, v_as_3812_, v_i_3813_, v_j_3814_, v_bs_3816_, v___y_3817_, v___y_3818_, v___y_3819_, v___y_3820_);
return v___x_3822_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___boxed(lean_object* v___x_3823_, lean_object* v_xs_3824_, lean_object* v_as_3825_, lean_object* v_i_3826_, lean_object* v_j_3827_, lean_object* v_inv_3828_, lean_object* v_bs_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_){
_start:
{
lean_object* v_res_3835_; 
v_res_3835_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12(v___x_3823_, v_xs_3824_, v_as_3825_, v_i_3826_, v_j_3827_, v_inv_3828_, v_bs_3829_, v___y_3830_, v___y_3831_, v___y_3832_, v___y_3833_);
lean_dec(v___y_3833_);
lean_dec_ref(v___y_3832_);
lean_dec(v___y_3831_);
lean_dec_ref(v___y_3830_);
lean_dec_ref(v_as_3825_);
lean_dec_ref(v___x_3823_);
return v_res_3835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure___lam__0(lean_object* v___x_3836_, lean_object* v_recArgPos_3837_, lean_object* v_xs_3838_, lean_object* v_x_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_){
_start:
{
lean_object* v___x_3845_; uint8_t v___x_3846_; uint8_t v___x_3847_; uint8_t v___x_3848_; lean_object* v___x_3849_; 
v___x_3845_ = lean_array_get_borrowed(v___x_3836_, v_xs_3838_, v_recArgPos_3837_);
v___x_3846_ = 0;
v___x_3847_ = 1;
v___x_3848_ = 1;
lean_inc(v___x_3845_);
v___x_3849_ = l_Lean_Meta_mkLambdaFVars(v_xs_3838_, v___x_3845_, v___x_3846_, v___x_3847_, v___x_3846_, v___x_3847_, v___x_3848_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_);
return v___x_3849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure___lam__0___boxed(lean_object* v___x_3850_, lean_object* v_recArgPos_3851_, lean_object* v_xs_3852_, lean_object* v_x_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_){
_start:
{
lean_object* v_res_3859_; 
v_res_3859_ = l_Lean_Elab_Structural_reportTermMeasure___lam__0(v___x_3850_, v_recArgPos_3851_, v_xs_3852_, v_x_3853_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_);
lean_dec(v___y_3857_);
lean_dec_ref(v___y_3856_);
lean_dec(v___y_3855_);
lean_dec_ref(v___y_3854_);
lean_dec_ref(v_x_3853_);
lean_dec_ref(v_xs_3852_);
lean_dec(v_recArgPos_3851_);
return v_res_3859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure___lam__1(lean_object* v_xs_3860_, lean_object* v_x_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_){
_start:
{
lean_object* v___x_3867_; lean_object* v___x_3868_; 
v___x_3867_ = lean_array_get_size(v_xs_3860_);
v___x_3868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3868_, 0, v___x_3867_);
return v___x_3868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure___lam__1___boxed(lean_object* v_xs_3869_, lean_object* v_x_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_){
_start:
{
lean_object* v_res_3876_; 
v_res_3876_ = l_Lean_Elab_Structural_reportTermMeasure___lam__1(v_xs_3869_, v_x_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_);
lean_dec(v___y_3874_);
lean_dec_ref(v___y_3873_);
lean_dec(v___y_3872_);
lean_dec_ref(v___y_3871_);
lean_dec_ref(v_x_3870_);
lean_dec_ref(v_xs_3869_);
return v_res_3876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure(lean_object* v_preDef_3888_, lean_object* v_recArgPos_3889_, lean_object* v_a_3890_, lean_object* v_a_3891_, lean_object* v_a_3892_, lean_object* v_a_3893_){
_start:
{
lean_object* v_termination_3895_; lean_object* v_terminationBy_x3f_x3f_3896_; 
v_termination_3895_ = lean_ctor_get(v_preDef_3888_, 8);
lean_inc_ref(v_termination_3895_);
v_terminationBy_x3f_x3f_3896_ = lean_ctor_get(v_termination_3895_, 1);
lean_inc(v_terminationBy_x3f_x3f_3896_);
if (lean_obj_tag(v_terminationBy_x3f_x3f_3896_) == 1)
{
lean_object* v_value_3897_; lean_object* v_extraParams_3898_; lean_object* v___x_3900_; uint8_t v_isShared_3901_; uint8_t v_isSharedCheck_3949_; 
v_value_3897_ = lean_ctor_get(v_preDef_3888_, 7);
lean_inc_ref(v_value_3897_);
lean_dec_ref(v_preDef_3888_);
v_extraParams_3898_ = lean_ctor_get(v_termination_3895_, 5);
v_isSharedCheck_3949_ = !lean_is_exclusive(v_termination_3895_);
if (v_isSharedCheck_3949_ == 0)
{
lean_object* v_unused_3950_; lean_object* v_unused_3951_; lean_object* v_unused_3952_; lean_object* v_unused_3953_; lean_object* v_unused_3954_; 
v_unused_3950_ = lean_ctor_get(v_termination_3895_, 4);
lean_dec(v_unused_3950_);
v_unused_3951_ = lean_ctor_get(v_termination_3895_, 3);
lean_dec(v_unused_3951_);
v_unused_3952_ = lean_ctor_get(v_termination_3895_, 2);
lean_dec(v_unused_3952_);
v_unused_3953_ = lean_ctor_get(v_termination_3895_, 1);
lean_dec(v_unused_3953_);
v_unused_3954_ = lean_ctor_get(v_termination_3895_, 0);
lean_dec(v_unused_3954_);
v___x_3900_ = v_termination_3895_;
v_isShared_3901_ = v_isSharedCheck_3949_;
goto v_resetjp_3899_;
}
else
{
lean_inc(v_extraParams_3898_);
lean_dec(v_termination_3895_);
v___x_3900_ = lean_box(0);
v_isShared_3901_ = v_isSharedCheck_3949_;
goto v_resetjp_3899_;
}
v_resetjp_3899_:
{
lean_object* v_val_3902_; lean_object* v___x_3903_; lean_object* v___f_3904_; uint8_t v___x_3905_; lean_object* v___x_3906_; 
v_val_3902_ = lean_ctor_get(v_terminationBy_x3f_x3f_3896_, 0);
lean_inc(v_val_3902_);
lean_dec_ref(v_terminationBy_x3f_x3f_3896_);
v___x_3903_ = l_Lean_instInhabitedExpr;
v___f_3904_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_reportTermMeasure___lam__0___boxed), 9, 2);
lean_closure_set(v___f_3904_, 0, v___x_3903_);
lean_closure_set(v___f_3904_, 1, v_recArgPos_3889_);
v___x_3905_ = 0;
lean_inc_ref(v_value_3897_);
v___x_3906_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg(v_value_3897_, v___f_3904_, v___x_3905_, v_a_3890_, v_a_3891_, v_a_3892_, v_a_3893_);
if (lean_obj_tag(v___x_3906_) == 0)
{
lean_object* v_a_3907_; lean_object* v___f_3908_; lean_object* v___x_3909_; 
v_a_3907_ = lean_ctor_get(v___x_3906_, 0);
lean_inc(v_a_3907_);
lean_dec_ref(v___x_3906_);
v___f_3908_ = ((lean_object*)(l_Lean_Elab_Structural_reportTermMeasure___closed__0));
v___x_3909_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg(v_value_3897_, v___f_3908_, v___x_3905_, v_a_3890_, v_a_3891_, v_a_3892_, v_a_3893_);
if (lean_obj_tag(v___x_3909_) == 0)
{
lean_object* v_a_3910_; lean_object* v___x_3911_; uint8_t v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; 
v_a_3910_ = lean_ctor_get(v___x_3909_, 0);
lean_inc(v_a_3910_);
lean_dec_ref(v___x_3909_);
v___x_3911_ = lean_box(0);
v___x_3912_ = 1;
v___x_3913_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3913_, 0, v___x_3911_);
lean_ctor_set(v___x_3913_, 1, v_a_3907_);
lean_ctor_set_uint8(v___x_3913_, sizeof(void*)*2, v___x_3912_);
v___x_3914_ = l_Lean_Elab_TerminationMeasure_delab(v_a_3910_, v_extraParams_3898_, v___x_3913_, v_a_3890_, v_a_3891_, v_a_3892_, v_a_3893_);
lean_dec(v_a_3910_);
if (lean_obj_tag(v___x_3914_) == 0)
{
lean_object* v_a_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3920_; 
v_a_3915_ = lean_ctor_get(v___x_3914_, 0);
lean_inc(v_a_3915_);
lean_dec_ref(v___x_3914_);
v___x_3916_ = ((lean_object*)(l_Lean_Elab_Structural_reportTermMeasure___closed__5));
v___x_3917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3917_, 0, v___x_3916_);
lean_ctor_set(v___x_3917_, 1, v_a_3915_);
v___x_3918_ = lean_box(0);
if (v_isShared_3901_ == 0)
{
lean_ctor_set(v___x_3900_, 5, v___x_3918_);
lean_ctor_set(v___x_3900_, 4, v___x_3918_);
lean_ctor_set(v___x_3900_, 3, v___x_3918_);
lean_ctor_set(v___x_3900_, 2, v___x_3918_);
lean_ctor_set(v___x_3900_, 1, v___x_3918_);
lean_ctor_set(v___x_3900_, 0, v___x_3917_);
v___x_3920_ = v___x_3900_;
goto v_reusejp_3919_;
}
else
{
lean_object* v_reuseFailAlloc_3924_; 
v_reuseFailAlloc_3924_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3924_, 0, v___x_3917_);
lean_ctor_set(v_reuseFailAlloc_3924_, 1, v___x_3918_);
lean_ctor_set(v_reuseFailAlloc_3924_, 2, v___x_3918_);
lean_ctor_set(v_reuseFailAlloc_3924_, 3, v___x_3918_);
lean_ctor_set(v_reuseFailAlloc_3924_, 4, v___x_3918_);
lean_ctor_set(v_reuseFailAlloc_3924_, 5, v___x_3918_);
v___x_3920_ = v_reuseFailAlloc_3924_;
goto v_reusejp_3919_;
}
v_reusejp_3919_:
{
lean_object* v___x_3921_; uint8_t v___x_3922_; lean_object* v___x_3923_; 
v___x_3921_ = ((lean_object*)(l_Lean_Elab_Structural_reportTermMeasure___closed__6));
v___x_3922_ = 4;
v___x_3923_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_val_3902_, v___x_3920_, v___x_3918_, v___x_3921_, v___x_3918_, v___x_3922_, v_a_3892_, v_a_3893_);
return v___x_3923_;
}
}
else
{
lean_object* v_a_3925_; lean_object* v___x_3927_; uint8_t v_isShared_3928_; uint8_t v_isSharedCheck_3932_; 
lean_dec(v_val_3902_);
lean_del_object(v___x_3900_);
v_a_3925_ = lean_ctor_get(v___x_3914_, 0);
v_isSharedCheck_3932_ = !lean_is_exclusive(v___x_3914_);
if (v_isSharedCheck_3932_ == 0)
{
v___x_3927_ = v___x_3914_;
v_isShared_3928_ = v_isSharedCheck_3932_;
goto v_resetjp_3926_;
}
else
{
lean_inc(v_a_3925_);
lean_dec(v___x_3914_);
v___x_3927_ = lean_box(0);
v_isShared_3928_ = v_isSharedCheck_3932_;
goto v_resetjp_3926_;
}
v_resetjp_3926_:
{
lean_object* v___x_3930_; 
if (v_isShared_3928_ == 0)
{
v___x_3930_ = v___x_3927_;
goto v_reusejp_3929_;
}
else
{
lean_object* v_reuseFailAlloc_3931_; 
v_reuseFailAlloc_3931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3931_, 0, v_a_3925_);
v___x_3930_ = v_reuseFailAlloc_3931_;
goto v_reusejp_3929_;
}
v_reusejp_3929_:
{
return v___x_3930_;
}
}
}
}
else
{
lean_object* v_a_3933_; lean_object* v___x_3935_; uint8_t v_isShared_3936_; uint8_t v_isSharedCheck_3940_; 
lean_dec(v_a_3907_);
lean_dec(v_val_3902_);
lean_del_object(v___x_3900_);
lean_dec(v_extraParams_3898_);
v_a_3933_ = lean_ctor_get(v___x_3909_, 0);
v_isSharedCheck_3940_ = !lean_is_exclusive(v___x_3909_);
if (v_isSharedCheck_3940_ == 0)
{
v___x_3935_ = v___x_3909_;
v_isShared_3936_ = v_isSharedCheck_3940_;
goto v_resetjp_3934_;
}
else
{
lean_inc(v_a_3933_);
lean_dec(v___x_3909_);
v___x_3935_ = lean_box(0);
v_isShared_3936_ = v_isSharedCheck_3940_;
goto v_resetjp_3934_;
}
v_resetjp_3934_:
{
lean_object* v___x_3938_; 
if (v_isShared_3936_ == 0)
{
v___x_3938_ = v___x_3935_;
goto v_reusejp_3937_;
}
else
{
lean_object* v_reuseFailAlloc_3939_; 
v_reuseFailAlloc_3939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3939_, 0, v_a_3933_);
v___x_3938_ = v_reuseFailAlloc_3939_;
goto v_reusejp_3937_;
}
v_reusejp_3937_:
{
return v___x_3938_;
}
}
}
}
else
{
lean_object* v_a_3941_; lean_object* v___x_3943_; uint8_t v_isShared_3944_; uint8_t v_isSharedCheck_3948_; 
lean_dec(v_val_3902_);
lean_del_object(v___x_3900_);
lean_dec(v_extraParams_3898_);
lean_dec_ref(v_value_3897_);
v_a_3941_ = lean_ctor_get(v___x_3906_, 0);
v_isSharedCheck_3948_ = !lean_is_exclusive(v___x_3906_);
if (v_isSharedCheck_3948_ == 0)
{
v___x_3943_ = v___x_3906_;
v_isShared_3944_ = v_isSharedCheck_3948_;
goto v_resetjp_3942_;
}
else
{
lean_inc(v_a_3941_);
lean_dec(v___x_3906_);
v___x_3943_ = lean_box(0);
v_isShared_3944_ = v_isSharedCheck_3948_;
goto v_resetjp_3942_;
}
v_resetjp_3942_:
{
lean_object* v___x_3946_; 
if (v_isShared_3944_ == 0)
{
v___x_3946_ = v___x_3943_;
goto v_reusejp_3945_;
}
else
{
lean_object* v_reuseFailAlloc_3947_; 
v_reuseFailAlloc_3947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3947_, 0, v_a_3941_);
v___x_3946_ = v_reuseFailAlloc_3947_;
goto v_reusejp_3945_;
}
v_reusejp_3945_:
{
return v___x_3946_;
}
}
}
}
}
else
{
lean_object* v___x_3955_; lean_object* v___x_3956_; 
lean_dec(v_terminationBy_x3f_x3f_3896_);
lean_dec_ref(v_termination_3895_);
lean_dec(v_recArgPos_3889_);
lean_dec_ref(v_preDef_3888_);
v___x_3955_ = lean_box(0);
v___x_3956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3956_, 0, v___x_3955_);
return v___x_3956_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure___boxed(lean_object* v_preDef_3957_, lean_object* v_recArgPos_3958_, lean_object* v_a_3959_, lean_object* v_a_3960_, lean_object* v_a_3961_, lean_object* v_a_3962_, lean_object* v_a_3963_){
_start:
{
lean_object* v_res_3964_; 
v_res_3964_ = l_Lean_Elab_Structural_reportTermMeasure(v_preDef_3957_, v_recArgPos_3958_, v_a_3959_, v_a_3960_, v_a_3961_, v_a_3962_);
lean_dec(v_a_3962_);
lean_dec_ref(v_a_3961_);
lean_dec(v_a_3960_);
lean_dec_ref(v_a_3959_);
return v_res_3964_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___redArg(lean_object* v_as_3965_, size_t v_sz_3966_, size_t v_i_3967_, lean_object* v_b_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_){
_start:
{
uint8_t v___x_3974_; 
v___x_3974_ = lean_usize_dec_lt(v_i_3967_, v_sz_3966_);
if (v___x_3974_ == 0)
{
lean_object* v___x_3975_; 
v___x_3975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3975_, 0, v_b_3968_);
return v___x_3975_;
}
else
{
lean_object* v_a_3976_; lean_object* v_declName_3977_; lean_object* v___x_3978_; 
v_a_3976_ = lean_array_uget_borrowed(v_as_3965_, v_i_3967_);
v_declName_3977_ = lean_ctor_get(v_a_3976_, 3);
lean_inc_ref(v___y_3971_);
lean_inc(v_declName_3977_);
v___x_3978_ = l_Lean_enableRealizationsForConst(v_declName_3977_, v___y_3971_, v___y_3972_);
if (lean_obj_tag(v___x_3978_) == 0)
{
lean_object* v___x_3979_; 
lean_dec_ref(v___x_3978_);
lean_inc(v_declName_3977_);
v___x_3979_ = l_Lean_Meta_generateEagerEqns(v_declName_3977_, v___y_3969_, v___y_3970_, v___y_3971_, v___y_3972_);
if (lean_obj_tag(v___x_3979_) == 0)
{
lean_object* v___x_3980_; size_t v___x_3981_; size_t v___x_3982_; 
lean_dec_ref(v___x_3979_);
v___x_3980_ = lean_box(0);
v___x_3981_ = ((size_t)1ULL);
v___x_3982_ = lean_usize_add(v_i_3967_, v___x_3981_);
v_i_3967_ = v___x_3982_;
v_b_3968_ = v___x_3980_;
goto _start;
}
else
{
return v___x_3979_;
}
}
else
{
return v___x_3978_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___redArg___boxed(lean_object* v_as_3984_, lean_object* v_sz_3985_, lean_object* v_i_3986_, lean_object* v_b_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_){
_start:
{
size_t v_sz_boxed_3993_; size_t v_i_boxed_3994_; lean_object* v_res_3995_; 
v_sz_boxed_3993_ = lean_unbox_usize(v_sz_3985_);
lean_dec(v_sz_3985_);
v_i_boxed_3994_ = lean_unbox_usize(v_i_3986_);
lean_dec(v_i_3986_);
v_res_3995_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___redArg(v_as_3984_, v_sz_boxed_3993_, v_i_boxed_3994_, v_b_3987_, v___y_3988_, v___y_3989_, v___y_3990_, v___y_3991_);
lean_dec(v___y_3991_);
lean_dec_ref(v___y_3990_);
lean_dec(v___y_3989_);
lean_dec_ref(v___y_3988_);
lean_dec_ref(v_as_3984_);
return v_res_3995_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4___lam__0(lean_object* v___x_3996_, lean_object* v_e_3997_){
_start:
{
lean_object* v___x_3998_; lean_object* v___x_3999_; 
v___x_3998_ = l_Lean_indentD(v_e_3997_);
v___x_3999_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3999_, 0, v___x_3996_);
lean_ctor_set(v___x_3999_, 1, v___x_3998_);
return v___x_3999_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4___lam__1(lean_object* v_docCtx_4000_, lean_object* v_a_4001_, uint8_t v___x_4002_, lean_object* v___x_4003_, uint8_t v___x_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_){
_start:
{
lean_object* v___x_4012_; 
v___x_4012_ = l_Lean_Elab_addNonRec(v_docCtx_4000_, v_a_4001_, v___x_4002_, v___x_4003_, v___x_4004_, v___x_4002_, v___x_4004_, v___y_4005_, v___y_4006_, v___y_4007_, v___y_4008_, v___y_4009_, v___y_4010_);
return v___x_4012_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4___lam__1___boxed(lean_object* v_docCtx_4013_, lean_object* v_a_4014_, lean_object* v___x_4015_, lean_object* v___x_4016_, lean_object* v___x_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_){
_start:
{
uint8_t v___x_8569__boxed_4025_; uint8_t v___x_8571__boxed_4026_; lean_object* v_res_4027_; 
v___x_8569__boxed_4025_ = lean_unbox(v___x_4015_);
v___x_8571__boxed_4026_ = lean_unbox(v___x_4017_);
v_res_4027_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4___lam__1(v_docCtx_4013_, v_a_4014_, v___x_8569__boxed_4025_, v___x_4016_, v___x_8571__boxed_4026_, v___y_4018_, v___y_4019_, v___y_4020_, v___y_4021_, v___y_4022_, v___y_4023_);
lean_dec(v___y_4023_);
lean_dec_ref(v___y_4022_);
lean_dec(v___y_4021_);
lean_dec_ref(v___y_4020_);
lean_dec(v___y_4019_);
lean_dec_ref(v___y_4018_);
return v_res_4027_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4___closed__1(void){
_start:
{
lean_object* v___x_4029_; lean_object* v___x_4030_; 
v___x_4029_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4___closed__0));
v___x_4030_ = l_Lean_stringToMessageData(v___x_4029_);
return v___x_4030_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4___closed__2(void){
_start:
{
lean_object* v___x_4031_; lean_object* v___f_4032_; 
v___x_4031_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4___closed__1);
v___f_4032_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4___lam__0), 2, 1);
lean_closure_set(v___f_4032_, 0, v___x_4031_);
return v___f_4032_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4(lean_object* v_names_4033_, lean_object* v_docCtx_4034_, lean_object* v_as_4035_, size_t v_i_4036_, size_t v_stop_4037_, lean_object* v_b_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_){
_start:
{
uint8_t v___x_4046_; 
v___x_4046_ = lean_usize_dec_eq(v_i_4036_, v_stop_4037_);
if (v___x_4046_ == 0)
{
lean_object* v___x_4047_; lean_object* v___x_4048_; 
v___x_4047_ = lean_array_uget_borrowed(v_as_4035_, v_i_4036_);
lean_inc(v___x_4047_);
v___x_4048_ = l_Lean_Elab_eraseRecAppSyntax(v___x_4047_, v___y_4043_, v___y_4044_);
if (lean_obj_tag(v___x_4048_) == 0)
{
lean_object* v_a_4049_; lean_object* v___f_4050_; lean_object* v___x_4051_; uint8_t v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___f_4055_; lean_object* v___x_4056_; 
v_a_4049_ = lean_ctor_get(v___x_4048_, 0);
lean_inc(v_a_4049_);
lean_dec_ref(v___x_4048_);
v___f_4050_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4___closed__2, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4___closed__2);
lean_inc_ref(v_names_4033_);
v___x_4051_ = lean_array_to_list(v_names_4033_);
v___x_4052_ = 1;
v___x_4053_ = lean_box(v___x_4046_);
v___x_4054_ = lean_box(v___x_4052_);
lean_inc(v___y_4040_);
lean_inc_ref(v___y_4039_);
lean_inc_ref(v_docCtx_4034_);
v___f_4055_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4___lam__1___boxed), 12, 7);
lean_closure_set(v___f_4055_, 0, v_docCtx_4034_);
lean_closure_set(v___f_4055_, 1, v_a_4049_);
lean_closure_set(v___f_4055_, 2, v___x_4053_);
lean_closure_set(v___f_4055_, 3, v___x_4051_);
lean_closure_set(v___f_4055_, 4, v___x_4054_);
lean_closure_set(v___f_4055_, 5, v___y_4039_);
lean_closure_set(v___f_4055_, 6, v___y_4040_);
v___x_4056_ = l_Lean_Meta_mapErrorImp___redArg(v___f_4055_, v___f_4050_, v___y_4041_, v___y_4042_, v___y_4043_, v___y_4044_);
if (lean_obj_tag(v___x_4056_) == 0)
{
if (lean_obj_tag(v___x_4056_) == 0)
{
lean_object* v_a_4057_; size_t v___x_4058_; size_t v___x_4059_; 
v_a_4057_ = lean_ctor_get(v___x_4056_, 0);
lean_inc(v_a_4057_);
lean_dec_ref(v___x_4056_);
v___x_4058_ = ((size_t)1ULL);
v___x_4059_ = lean_usize_add(v_i_4036_, v___x_4058_);
v_i_4036_ = v___x_4059_;
v_b_4038_ = v_a_4057_;
goto _start;
}
else
{
lean_dec_ref(v_docCtx_4034_);
lean_dec_ref(v_names_4033_);
return v___x_4056_;
}
}
else
{
lean_object* v_a_4061_; lean_object* v___x_4063_; uint8_t v_isShared_4064_; uint8_t v_isSharedCheck_4068_; 
lean_dec_ref(v_docCtx_4034_);
lean_dec_ref(v_names_4033_);
v_a_4061_ = lean_ctor_get(v___x_4056_, 0);
v_isSharedCheck_4068_ = !lean_is_exclusive(v___x_4056_);
if (v_isSharedCheck_4068_ == 0)
{
v___x_4063_ = v___x_4056_;
v_isShared_4064_ = v_isSharedCheck_4068_;
goto v_resetjp_4062_;
}
else
{
lean_inc(v_a_4061_);
lean_dec(v___x_4056_);
v___x_4063_ = lean_box(0);
v_isShared_4064_ = v_isSharedCheck_4068_;
goto v_resetjp_4062_;
}
v_resetjp_4062_:
{
lean_object* v___x_4066_; 
if (v_isShared_4064_ == 0)
{
v___x_4066_ = v___x_4063_;
goto v_reusejp_4065_;
}
else
{
lean_object* v_reuseFailAlloc_4067_; 
v_reuseFailAlloc_4067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4067_, 0, v_a_4061_);
v___x_4066_ = v_reuseFailAlloc_4067_;
goto v_reusejp_4065_;
}
v_reusejp_4065_:
{
return v___x_4066_;
}
}
}
}
else
{
lean_object* v_a_4069_; lean_object* v___x_4071_; uint8_t v_isShared_4072_; uint8_t v_isSharedCheck_4076_; 
lean_dec_ref(v_docCtx_4034_);
lean_dec_ref(v_names_4033_);
v_a_4069_ = lean_ctor_get(v___x_4048_, 0);
v_isSharedCheck_4076_ = !lean_is_exclusive(v___x_4048_);
if (v_isSharedCheck_4076_ == 0)
{
v___x_4071_ = v___x_4048_;
v_isShared_4072_ = v_isSharedCheck_4076_;
goto v_resetjp_4070_;
}
else
{
lean_inc(v_a_4069_);
lean_dec(v___x_4048_);
v___x_4071_ = lean_box(0);
v_isShared_4072_ = v_isSharedCheck_4076_;
goto v_resetjp_4070_;
}
v_resetjp_4070_:
{
lean_object* v___x_4074_; 
if (v_isShared_4072_ == 0)
{
v___x_4074_ = v___x_4071_;
goto v_reusejp_4073_;
}
else
{
lean_object* v_reuseFailAlloc_4075_; 
v_reuseFailAlloc_4075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4075_, 0, v_a_4069_);
v___x_4074_ = v_reuseFailAlloc_4075_;
goto v_reusejp_4073_;
}
v_reusejp_4073_:
{
return v___x_4074_;
}
}
}
}
else
{
lean_object* v___x_4077_; 
lean_dec_ref(v_docCtx_4034_);
lean_dec_ref(v_names_4033_);
v___x_4077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4077_, 0, v_b_4038_);
return v___x_4077_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4___boxed(lean_object* v_names_4078_, lean_object* v_docCtx_4079_, lean_object* v_as_4080_, lean_object* v_i_4081_, lean_object* v_stop_4082_, lean_object* v_b_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_){
_start:
{
size_t v_i_boxed_4091_; size_t v_stop_boxed_4092_; lean_object* v_res_4093_; 
v_i_boxed_4091_ = lean_unbox_usize(v_i_4081_);
lean_dec(v_i_4081_);
v_stop_boxed_4092_ = lean_unbox_usize(v_stop_4082_);
lean_dec(v_stop_4082_);
v_res_4093_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4(v_names_4078_, v_docCtx_4079_, v_as_4080_, v_i_boxed_4091_, v_stop_boxed_4092_, v_b_4083_, v___y_4084_, v___y_4085_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_);
lean_dec(v___y_4089_);
lean_dec_ref(v___y_4088_);
lean_dec(v___y_4087_);
lean_dec_ref(v___y_4086_);
lean_dec(v___y_4085_);
lean_dec_ref(v___y_4084_);
lean_dec_ref(v_as_4080_);
return v_res_4093_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__1(lean_object* v_docCtx_4094_, lean_object* v_a_4095_, lean_object* v_snd_4096_, lean_object* v_as_4097_, size_t v_sz_4098_, size_t v_i_4099_, lean_object* v_b_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_){
_start:
{
uint8_t v___x_4108_; 
v___x_4108_ = lean_usize_dec_lt(v_i_4099_, v_sz_4098_);
if (v___x_4108_ == 0)
{
lean_object* v___x_4109_; 
lean_dec_ref(v_snd_4096_);
lean_dec_ref(v_a_4095_);
lean_dec_ref(v_docCtx_4094_);
v___x_4109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4109_, 0, v_b_4100_);
return v___x_4109_;
}
else
{
lean_object* v_array_4110_; lean_object* v_start_4111_; lean_object* v_stop_4112_; uint8_t v___x_4113_; 
v_array_4110_ = lean_ctor_get(v_b_4100_, 0);
v_start_4111_ = lean_ctor_get(v_b_4100_, 1);
v_stop_4112_ = lean_ctor_get(v_b_4100_, 2);
v___x_4113_ = lean_nat_dec_lt(v_start_4111_, v_stop_4112_);
if (v___x_4113_ == 0)
{
lean_object* v___x_4114_; 
lean_dec_ref(v_snd_4096_);
lean_dec_ref(v_a_4095_);
lean_dec_ref(v_docCtx_4094_);
v___x_4114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4114_, 0, v_b_4100_);
return v___x_4114_;
}
else
{
lean_object* v___x_4116_; uint8_t v_isShared_4117_; uint8_t v_isSharedCheck_4181_; 
lean_inc(v_stop_4112_);
lean_inc(v_start_4111_);
lean_inc_ref(v_array_4110_);
v_isSharedCheck_4181_ = !lean_is_exclusive(v_b_4100_);
if (v_isSharedCheck_4181_ == 0)
{
lean_object* v_unused_4182_; lean_object* v_unused_4183_; lean_object* v_unused_4184_; 
v_unused_4182_ = lean_ctor_get(v_b_4100_, 2);
lean_dec(v_unused_4182_);
v_unused_4183_ = lean_ctor_get(v_b_4100_, 1);
lean_dec(v_unused_4183_);
v_unused_4184_ = lean_ctor_get(v_b_4100_, 0);
lean_dec(v_unused_4184_);
v___x_4116_ = v_b_4100_;
v_isShared_4117_ = v_isSharedCheck_4181_;
goto v_resetjp_4115_;
}
else
{
lean_dec(v_b_4100_);
v___x_4116_ = lean_box(0);
v_isShared_4117_ = v_isSharedCheck_4181_;
goto v_resetjp_4115_;
}
v_resetjp_4115_:
{
lean_object* v_a_4118_; uint8_t v_kind_4119_; lean_object* v_type_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4125_; 
v_a_4118_ = lean_array_uget_borrowed(v_as_4097_, v_i_4099_);
v_kind_4119_ = lean_ctor_get_uint8(v_a_4118_, sizeof(void*)*9);
v_type_4120_ = lean_ctor_get(v_a_4118_, 6);
v___x_4121_ = lean_array_fget(v_array_4110_, v_start_4111_);
v___x_4122_ = lean_unsigned_to_nat(1u);
v___x_4123_ = lean_nat_add(v_start_4111_, v___x_4122_);
lean_dec(v_start_4111_);
if (v_isShared_4117_ == 0)
{
lean_ctor_set(v___x_4116_, 1, v___x_4123_);
v___x_4125_ = v___x_4116_;
goto v_reusejp_4124_;
}
else
{
lean_object* v_reuseFailAlloc_4180_; 
v_reuseFailAlloc_4180_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4180_, 0, v_array_4110_);
lean_ctor_set(v_reuseFailAlloc_4180_, 1, v___x_4123_);
lean_ctor_set(v_reuseFailAlloc_4180_, 2, v_stop_4112_);
v___x_4125_ = v_reuseFailAlloc_4180_;
goto v_reusejp_4124_;
}
v_reusejp_4124_:
{
lean_object* v_preDef_4127_; lean_object* v___y_4128_; lean_object* v___y_4129_; lean_object* v___y_4130_; lean_object* v___y_4131_; lean_object* v___y_4132_; lean_object* v___y_4133_; uint8_t v___x_4146_; 
v___x_4146_ = l_Lean_Elab_DefKind_isTheorem(v_kind_4119_);
if (v___x_4146_ == 0)
{
lean_object* v___x_4147_; 
lean_inc_ref(v_type_4120_);
v___x_4147_ = l_Lean_Meta_isProp(v_type_4120_, v___y_4103_, v___y_4104_, v___y_4105_, v___y_4106_);
if (lean_obj_tag(v___x_4147_) == 0)
{
lean_object* v_a_4148_; uint8_t v___x_4149_; 
v_a_4148_ = lean_ctor_get(v___x_4147_, 0);
lean_inc(v_a_4148_);
lean_dec_ref(v___x_4147_);
v___x_4149_ = lean_unbox(v_a_4148_);
lean_dec(v_a_4148_);
if (v___x_4149_ == 0)
{
lean_object* v___x_4150_; 
lean_inc(v_a_4118_);
v___x_4150_ = l_Lean_Elab_abstractNestedProofs(v_a_4118_, v___x_4113_, v___y_4103_, v___y_4104_, v___y_4105_, v___y_4106_);
if (lean_obj_tag(v___x_4150_) == 0)
{
lean_object* v_a_4151_; size_t v_sz_4152_; size_t v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; 
v_a_4151_ = lean_ctor_get(v___x_4150_, 0);
lean_inc(v_a_4151_);
lean_dec_ref(v___x_4150_);
v_sz_4152_ = lean_array_size(v_a_4095_);
v___x_4153_ = ((size_t)0ULL);
lean_inc_ref(v_a_4095_);
v___x_4154_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0(v_sz_4152_, v___x_4153_, v_a_4095_);
lean_inc_ref(v_snd_4096_);
lean_inc(v___x_4121_);
lean_inc(v_a_4151_);
v___x_4155_ = l_Lean_Elab_Structural_registerEqnsInfo(v_a_4151_, v___x_4154_, v___x_4121_, v_snd_4096_, v___y_4105_, v___y_4106_);
if (lean_obj_tag(v___x_4155_) == 0)
{
lean_dec_ref(v___x_4155_);
v_preDef_4127_ = v_a_4151_;
v___y_4128_ = v___y_4101_;
v___y_4129_ = v___y_4102_;
v___y_4130_ = v___y_4103_;
v___y_4131_ = v___y_4104_;
v___y_4132_ = v___y_4105_;
v___y_4133_ = v___y_4106_;
goto v___jp_4126_;
}
else
{
lean_object* v_a_4156_; lean_object* v___x_4158_; uint8_t v_isShared_4159_; uint8_t v_isSharedCheck_4163_; 
lean_dec(v_a_4151_);
lean_dec_ref(v___x_4125_);
lean_dec(v___x_4121_);
lean_dec_ref(v_snd_4096_);
lean_dec_ref(v_a_4095_);
lean_dec_ref(v_docCtx_4094_);
v_a_4156_ = lean_ctor_get(v___x_4155_, 0);
v_isSharedCheck_4163_ = !lean_is_exclusive(v___x_4155_);
if (v_isSharedCheck_4163_ == 0)
{
v___x_4158_ = v___x_4155_;
v_isShared_4159_ = v_isSharedCheck_4163_;
goto v_resetjp_4157_;
}
else
{
lean_inc(v_a_4156_);
lean_dec(v___x_4155_);
v___x_4158_ = lean_box(0);
v_isShared_4159_ = v_isSharedCheck_4163_;
goto v_resetjp_4157_;
}
v_resetjp_4157_:
{
lean_object* v___x_4161_; 
if (v_isShared_4159_ == 0)
{
v___x_4161_ = v___x_4158_;
goto v_reusejp_4160_;
}
else
{
lean_object* v_reuseFailAlloc_4162_; 
v_reuseFailAlloc_4162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4162_, 0, v_a_4156_);
v___x_4161_ = v_reuseFailAlloc_4162_;
goto v_reusejp_4160_;
}
v_reusejp_4160_:
{
return v___x_4161_;
}
}
}
}
else
{
lean_object* v_a_4164_; lean_object* v___x_4166_; uint8_t v_isShared_4167_; uint8_t v_isSharedCheck_4171_; 
lean_dec_ref(v___x_4125_);
lean_dec(v___x_4121_);
lean_dec_ref(v_snd_4096_);
lean_dec_ref(v_a_4095_);
lean_dec_ref(v_docCtx_4094_);
v_a_4164_ = lean_ctor_get(v___x_4150_, 0);
v_isSharedCheck_4171_ = !lean_is_exclusive(v___x_4150_);
if (v_isSharedCheck_4171_ == 0)
{
v___x_4166_ = v___x_4150_;
v_isShared_4167_ = v_isSharedCheck_4171_;
goto v_resetjp_4165_;
}
else
{
lean_inc(v_a_4164_);
lean_dec(v___x_4150_);
v___x_4166_ = lean_box(0);
v_isShared_4167_ = v_isSharedCheck_4171_;
goto v_resetjp_4165_;
}
v_resetjp_4165_:
{
lean_object* v___x_4169_; 
if (v_isShared_4167_ == 0)
{
v___x_4169_ = v___x_4166_;
goto v_reusejp_4168_;
}
else
{
lean_object* v_reuseFailAlloc_4170_; 
v_reuseFailAlloc_4170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4170_, 0, v_a_4164_);
v___x_4169_ = v_reuseFailAlloc_4170_;
goto v_reusejp_4168_;
}
v_reusejp_4168_:
{
return v___x_4169_;
}
}
}
}
else
{
lean_inc(v_a_4118_);
v_preDef_4127_ = v_a_4118_;
v___y_4128_ = v___y_4101_;
v___y_4129_ = v___y_4102_;
v___y_4130_ = v___y_4103_;
v___y_4131_ = v___y_4104_;
v___y_4132_ = v___y_4105_;
v___y_4133_ = v___y_4106_;
goto v___jp_4126_;
}
}
else
{
lean_object* v_a_4172_; lean_object* v___x_4174_; uint8_t v_isShared_4175_; uint8_t v_isSharedCheck_4179_; 
lean_dec_ref(v___x_4125_);
lean_dec(v___x_4121_);
lean_dec_ref(v_snd_4096_);
lean_dec_ref(v_a_4095_);
lean_dec_ref(v_docCtx_4094_);
v_a_4172_ = lean_ctor_get(v___x_4147_, 0);
v_isSharedCheck_4179_ = !lean_is_exclusive(v___x_4147_);
if (v_isSharedCheck_4179_ == 0)
{
v___x_4174_ = v___x_4147_;
v_isShared_4175_ = v_isSharedCheck_4179_;
goto v_resetjp_4173_;
}
else
{
lean_inc(v_a_4172_);
lean_dec(v___x_4147_);
v___x_4174_ = lean_box(0);
v_isShared_4175_ = v_isSharedCheck_4179_;
goto v_resetjp_4173_;
}
v_resetjp_4173_:
{
lean_object* v___x_4177_; 
if (v_isShared_4175_ == 0)
{
v___x_4177_ = v___x_4174_;
goto v_reusejp_4176_;
}
else
{
lean_object* v_reuseFailAlloc_4178_; 
v_reuseFailAlloc_4178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4178_, 0, v_a_4172_);
v___x_4177_ = v_reuseFailAlloc_4178_;
goto v_reusejp_4176_;
}
v_reusejp_4176_:
{
return v___x_4177_;
}
}
}
}
else
{
lean_inc(v_a_4118_);
v_preDef_4127_ = v_a_4118_;
v___y_4128_ = v___y_4101_;
v___y_4129_ = v___y_4102_;
v___y_4130_ = v___y_4103_;
v___y_4131_ = v___y_4104_;
v___y_4132_ = v___y_4105_;
v___y_4133_ = v___y_4106_;
goto v___jp_4126_;
}
v___jp_4126_:
{
lean_object* v___x_4134_; 
lean_inc_ref(v_docCtx_4094_);
v___x_4134_ = l_Lean_Elab_Structural_addSmartUnfoldingDef(v_docCtx_4094_, v_preDef_4127_, v___x_4121_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_, v___y_4132_, v___y_4133_);
if (lean_obj_tag(v___x_4134_) == 0)
{
size_t v___x_4135_; size_t v___x_4136_; 
lean_dec_ref(v___x_4134_);
v___x_4135_ = ((size_t)1ULL);
v___x_4136_ = lean_usize_add(v_i_4099_, v___x_4135_);
v_i_4099_ = v___x_4136_;
v_b_4100_ = v___x_4125_;
goto _start;
}
else
{
lean_object* v_a_4138_; lean_object* v___x_4140_; uint8_t v_isShared_4141_; uint8_t v_isSharedCheck_4145_; 
lean_dec_ref(v___x_4125_);
lean_dec_ref(v_snd_4096_);
lean_dec_ref(v_a_4095_);
lean_dec_ref(v_docCtx_4094_);
v_a_4138_ = lean_ctor_get(v___x_4134_, 0);
v_isSharedCheck_4145_ = !lean_is_exclusive(v___x_4134_);
if (v_isSharedCheck_4145_ == 0)
{
v___x_4140_ = v___x_4134_;
v_isShared_4141_ = v_isSharedCheck_4145_;
goto v_resetjp_4139_;
}
else
{
lean_inc(v_a_4138_);
lean_dec(v___x_4134_);
v___x_4140_ = lean_box(0);
v_isShared_4141_ = v_isSharedCheck_4145_;
goto v_resetjp_4139_;
}
v_resetjp_4139_:
{
lean_object* v___x_4143_; 
if (v_isShared_4141_ == 0)
{
v___x_4143_ = v___x_4140_;
goto v_reusejp_4142_;
}
else
{
lean_object* v_reuseFailAlloc_4144_; 
v_reuseFailAlloc_4144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4144_, 0, v_a_4138_);
v___x_4143_ = v_reuseFailAlloc_4144_;
goto v_reusejp_4142_;
}
v_reusejp_4142_:
{
return v___x_4143_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__1___boxed(lean_object* v_docCtx_4185_, lean_object* v_a_4186_, lean_object* v_snd_4187_, lean_object* v_as_4188_, lean_object* v_sz_4189_, lean_object* v_i_4190_, lean_object* v_b_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_){
_start:
{
size_t v_sz_boxed_4199_; size_t v_i_boxed_4200_; lean_object* v_res_4201_; 
v_sz_boxed_4199_ = lean_unbox_usize(v_sz_4189_);
lean_dec(v_sz_4189_);
v_i_boxed_4200_ = lean_unbox_usize(v_i_4190_);
lean_dec(v_i_4190_);
v_res_4201_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__1(v_docCtx_4185_, v_a_4186_, v_snd_4187_, v_as_4188_, v_sz_boxed_4199_, v_i_boxed_4200_, v_b_4191_, v___y_4192_, v___y_4193_, v___y_4194_, v___y_4195_, v___y_4196_, v___y_4197_);
lean_dec(v___y_4197_);
lean_dec_ref(v___y_4196_);
lean_dec(v___y_4195_);
lean_dec_ref(v___y_4194_);
lean_dec(v___y_4193_);
lean_dec_ref(v___y_4192_);
lean_dec_ref(v_as_4188_);
return v_res_4201_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___redArg(size_t v_sz_4202_, size_t v_i_4203_, lean_object* v_bs_4204_, lean_object* v___y_4205_, lean_object* v___y_4206_){
_start:
{
uint8_t v___x_4208_; 
v___x_4208_ = lean_usize_dec_lt(v_i_4203_, v_sz_4202_);
if (v___x_4208_ == 0)
{
lean_object* v___x_4209_; 
v___x_4209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4209_, 0, v_bs_4204_);
return v___x_4209_;
}
else
{
lean_object* v_v_4210_; lean_object* v___x_4211_; 
v_v_4210_ = lean_array_uget_borrowed(v_bs_4204_, v_i_4203_);
lean_inc(v_v_4210_);
v___x_4211_ = l_Lean_Elab_eraseRecAppSyntax(v_v_4210_, v___y_4205_, v___y_4206_);
if (lean_obj_tag(v___x_4211_) == 0)
{
lean_object* v_a_4212_; lean_object* v___x_4213_; lean_object* v_bs_x27_4214_; size_t v___x_4215_; size_t v___x_4216_; lean_object* v___x_4217_; 
v_a_4212_ = lean_ctor_get(v___x_4211_, 0);
lean_inc(v_a_4212_);
lean_dec_ref(v___x_4211_);
v___x_4213_ = lean_unsigned_to_nat(0u);
v_bs_x27_4214_ = lean_array_uset(v_bs_4204_, v_i_4203_, v___x_4213_);
v___x_4215_ = ((size_t)1ULL);
v___x_4216_ = lean_usize_add(v_i_4203_, v___x_4215_);
v___x_4217_ = lean_array_uset(v_bs_x27_4214_, v_i_4203_, v_a_4212_);
v_i_4203_ = v___x_4216_;
v_bs_4204_ = v___x_4217_;
goto _start;
}
else
{
lean_object* v_a_4219_; lean_object* v___x_4221_; uint8_t v_isShared_4222_; uint8_t v_isSharedCheck_4226_; 
lean_dec_ref(v_bs_4204_);
v_a_4219_ = lean_ctor_get(v___x_4211_, 0);
v_isSharedCheck_4226_ = !lean_is_exclusive(v___x_4211_);
if (v_isSharedCheck_4226_ == 0)
{
v___x_4221_ = v___x_4211_;
v_isShared_4222_ = v_isSharedCheck_4226_;
goto v_resetjp_4220_;
}
else
{
lean_inc(v_a_4219_);
lean_dec(v___x_4211_);
v___x_4221_ = lean_box(0);
v_isShared_4222_ = v_isSharedCheck_4226_;
goto v_resetjp_4220_;
}
v_resetjp_4220_:
{
lean_object* v___x_4224_; 
if (v_isShared_4222_ == 0)
{
v___x_4224_ = v___x_4221_;
goto v_reusejp_4223_;
}
else
{
lean_object* v_reuseFailAlloc_4225_; 
v_reuseFailAlloc_4225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4225_, 0, v_a_4219_);
v___x_4224_ = v_reuseFailAlloc_4225_;
goto v_reusejp_4223_;
}
v_reusejp_4223_:
{
return v___x_4224_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___redArg___boxed(lean_object* v_sz_4227_, lean_object* v_i_4228_, lean_object* v_bs_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_){
_start:
{
size_t v_sz_boxed_4233_; size_t v_i_boxed_4234_; lean_object* v_res_4235_; 
v_sz_boxed_4233_ = lean_unbox_usize(v_sz_4227_);
lean_dec(v_sz_4227_);
v_i_boxed_4234_ = lean_unbox_usize(v_i_4228_);
lean_dec(v_i_4228_);
v_res_4235_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___redArg(v_sz_boxed_4233_, v_i_boxed_4234_, v_bs_4229_, v___y_4230_, v___y_4231_);
lean_dec(v___y_4231_);
lean_dec_ref(v___y_4230_);
return v_res_4235_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___redArg(lean_object* v_as_4236_, size_t v_sz_4237_, size_t v_i_4238_, lean_object* v_b_4239_, lean_object* v___y_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_){
_start:
{
uint8_t v___x_4245_; 
v___x_4245_ = lean_usize_dec_lt(v_i_4238_, v_sz_4237_);
if (v___x_4245_ == 0)
{
lean_object* v___x_4246_; 
v___x_4246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4246_, 0, v_b_4239_);
return v___x_4246_;
}
else
{
lean_object* v_array_4247_; lean_object* v_start_4248_; lean_object* v_stop_4249_; uint8_t v___x_4250_; 
v_array_4247_ = lean_ctor_get(v_b_4239_, 0);
v_start_4248_ = lean_ctor_get(v_b_4239_, 1);
v_stop_4249_ = lean_ctor_get(v_b_4239_, 2);
v___x_4250_ = lean_nat_dec_lt(v_start_4248_, v_stop_4249_);
if (v___x_4250_ == 0)
{
lean_object* v___x_4251_; 
v___x_4251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4251_, 0, v_b_4239_);
return v___x_4251_;
}
else
{
lean_object* v___x_4253_; uint8_t v_isShared_4254_; uint8_t v_isSharedCheck_4274_; 
lean_inc(v_stop_4249_);
lean_inc(v_start_4248_);
lean_inc_ref(v_array_4247_);
v_isSharedCheck_4274_ = !lean_is_exclusive(v_b_4239_);
if (v_isSharedCheck_4274_ == 0)
{
lean_object* v_unused_4275_; lean_object* v_unused_4276_; lean_object* v_unused_4277_; 
v_unused_4275_ = lean_ctor_get(v_b_4239_, 2);
lean_dec(v_unused_4275_);
v_unused_4276_ = lean_ctor_get(v_b_4239_, 1);
lean_dec(v_unused_4276_);
v_unused_4277_ = lean_ctor_get(v_b_4239_, 0);
lean_dec(v_unused_4277_);
v___x_4253_ = v_b_4239_;
v_isShared_4254_ = v_isSharedCheck_4274_;
goto v_resetjp_4252_;
}
else
{
lean_dec(v_b_4239_);
v___x_4253_ = lean_box(0);
v_isShared_4254_ = v_isSharedCheck_4274_;
goto v_resetjp_4252_;
}
v_resetjp_4252_:
{
lean_object* v_a_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; 
v_a_4255_ = lean_array_uget_borrowed(v_as_4236_, v_i_4238_);
v___x_4256_ = lean_array_fget_borrowed(v_array_4247_, v_start_4248_);
lean_inc(v_a_4255_);
lean_inc(v___x_4256_);
v___x_4257_ = l_Lean_Elab_Structural_reportTermMeasure(v___x_4256_, v_a_4255_, v___y_4240_, v___y_4241_, v___y_4242_, v___y_4243_);
if (lean_obj_tag(v___x_4257_) == 0)
{
lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4261_; 
lean_dec_ref(v___x_4257_);
v___x_4258_ = lean_unsigned_to_nat(1u);
v___x_4259_ = lean_nat_add(v_start_4248_, v___x_4258_);
lean_dec(v_start_4248_);
if (v_isShared_4254_ == 0)
{
lean_ctor_set(v___x_4253_, 1, v___x_4259_);
v___x_4261_ = v___x_4253_;
goto v_reusejp_4260_;
}
else
{
lean_object* v_reuseFailAlloc_4265_; 
v_reuseFailAlloc_4265_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4265_, 0, v_array_4247_);
lean_ctor_set(v_reuseFailAlloc_4265_, 1, v___x_4259_);
lean_ctor_set(v_reuseFailAlloc_4265_, 2, v_stop_4249_);
v___x_4261_ = v_reuseFailAlloc_4265_;
goto v_reusejp_4260_;
}
v_reusejp_4260_:
{
size_t v___x_4262_; size_t v___x_4263_; 
v___x_4262_ = ((size_t)1ULL);
v___x_4263_ = lean_usize_add(v_i_4238_, v___x_4262_);
v_i_4238_ = v___x_4263_;
v_b_4239_ = v___x_4261_;
goto _start;
}
}
else
{
lean_object* v_a_4266_; lean_object* v___x_4268_; uint8_t v_isShared_4269_; uint8_t v_isSharedCheck_4273_; 
lean_del_object(v___x_4253_);
lean_dec(v_stop_4249_);
lean_dec(v_start_4248_);
lean_dec_ref(v_array_4247_);
v_a_4266_ = lean_ctor_get(v___x_4257_, 0);
v_isSharedCheck_4273_ = !lean_is_exclusive(v___x_4257_);
if (v_isSharedCheck_4273_ == 0)
{
v___x_4268_ = v___x_4257_;
v_isShared_4269_ = v_isSharedCheck_4273_;
goto v_resetjp_4267_;
}
else
{
lean_inc(v_a_4266_);
lean_dec(v___x_4257_);
v___x_4268_ = lean_box(0);
v_isShared_4269_ = v_isSharedCheck_4273_;
goto v_resetjp_4267_;
}
v_resetjp_4267_:
{
lean_object* v___x_4271_; 
if (v_isShared_4269_ == 0)
{
v___x_4271_ = v___x_4268_;
goto v_reusejp_4270_;
}
else
{
lean_object* v_reuseFailAlloc_4272_; 
v_reuseFailAlloc_4272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4272_, 0, v_a_4266_);
v___x_4271_ = v_reuseFailAlloc_4272_;
goto v_reusejp_4270_;
}
v_reusejp_4270_:
{
return v___x_4271_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___redArg___boxed(lean_object* v_as_4278_, lean_object* v_sz_4279_, lean_object* v_i_4280_, lean_object* v_b_4281_, lean_object* v___y_4282_, lean_object* v___y_4283_, lean_object* v___y_4284_, lean_object* v___y_4285_, lean_object* v___y_4286_){
_start:
{
size_t v_sz_boxed_4287_; size_t v_i_boxed_4288_; lean_object* v_res_4289_; 
v_sz_boxed_4287_ = lean_unbox_usize(v_sz_4279_);
lean_dec(v_sz_4279_);
v_i_boxed_4288_ = lean_unbox_usize(v_i_4280_);
lean_dec(v_i_4280_);
v_res_4289_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___redArg(v_as_4278_, v_sz_boxed_4287_, v_i_boxed_4288_, v_b_4281_, v___y_4282_, v___y_4283_, v___y_4284_, v___y_4285_);
lean_dec(v___y_4285_);
lean_dec_ref(v___y_4284_);
lean_dec(v___y_4283_);
lean_dec_ref(v___y_4282_);
lean_dec_ref(v_as_4278_);
return v_res_4289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_structuralRecursion(lean_object* v_docCtx_4290_, lean_object* v_preDefs_4291_, lean_object* v_termMeasure_x3fs_4292_, lean_object* v_a_4293_, lean_object* v_a_4294_, lean_object* v_a_4295_, lean_object* v_a_4296_, lean_object* v_a_4297_, lean_object* v_a_4298_){
_start:
{
size_t v_sz_4300_; size_t v___x_4301_; lean_object* v_names_4302_; lean_object* v___x_4303_; 
v_sz_4300_ = lean_array_size(v_preDefs_4291_);
v___x_4301_ = ((size_t)0ULL);
lean_inc_ref(v_preDefs_4291_);
v_names_4302_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0(v_sz_4300_, v___x_4301_, v_preDefs_4291_);
lean_inc_ref(v_preDefs_4291_);
v___x_4303_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos(v_preDefs_4291_, v_termMeasure_x3fs_4292_, v_a_4295_, v_a_4296_, v_a_4297_, v_a_4298_);
if (lean_obj_tag(v___x_4303_) == 0)
{
lean_object* v_a_4304_; lean_object* v_snd_4305_; lean_object* v_fst_4306_; lean_object* v_fst_4307_; lean_object* v_snd_4308_; lean_object* v___y_4339_; lean_object* v___x_4340_; lean_object* v___x_4341_; lean_object* v___x_4342_; size_t v_sz_4343_; lean_object* v___x_4344_; 
v_a_4304_ = lean_ctor_get(v___x_4303_, 0);
lean_inc(v_a_4304_);
lean_dec_ref(v___x_4303_);
v_snd_4305_ = lean_ctor_get(v_a_4304_, 1);
lean_inc(v_snd_4305_);
v_fst_4306_ = lean_ctor_get(v_a_4304_, 0);
lean_inc(v_fst_4306_);
lean_dec(v_a_4304_);
v_fst_4307_ = lean_ctor_get(v_snd_4305_, 0);
lean_inc(v_fst_4307_);
v_snd_4308_ = lean_ctor_get(v_snd_4305_, 1);
lean_inc(v_snd_4308_);
lean_dec(v_snd_4305_);
v___x_4340_ = lean_unsigned_to_nat(0u);
v___x_4341_ = lean_array_get_size(v_preDefs_4291_);
lean_inc_ref(v_preDefs_4291_);
v___x_4342_ = l_Array_toSubarray___redArg(v_preDefs_4291_, v___x_4340_, v___x_4341_);
v_sz_4343_ = lean_array_size(v_fst_4306_);
v___x_4344_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___redArg(v_fst_4306_, v_sz_4343_, v___x_4301_, v___x_4342_, v_a_4295_, v_a_4296_, v_a_4297_, v_a_4298_);
if (lean_obj_tag(v___x_4344_) == 0)
{
lean_object* v___x_4345_; uint8_t v___x_4346_; 
lean_dec_ref(v___x_4344_);
v___x_4345_ = lean_array_get_size(v_fst_4307_);
v___x_4346_ = lean_nat_dec_lt(v___x_4340_, v___x_4345_);
if (v___x_4346_ == 0)
{
lean_dec_ref(v_names_4302_);
goto v___jp_4309_;
}
else
{
lean_object* v___x_4347_; uint8_t v___x_4348_; 
v___x_4347_ = lean_box(0);
v___x_4348_ = lean_nat_dec_le(v___x_4345_, v___x_4345_);
if (v___x_4348_ == 0)
{
if (v___x_4346_ == 0)
{
lean_dec_ref(v_names_4302_);
goto v___jp_4309_;
}
else
{
size_t v___x_4349_; lean_object* v___x_4350_; 
v___x_4349_ = lean_usize_of_nat(v___x_4345_);
lean_inc_ref(v_docCtx_4290_);
v___x_4350_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4(v_names_4302_, v_docCtx_4290_, v_fst_4307_, v___x_4301_, v___x_4349_, v___x_4347_, v_a_4293_, v_a_4294_, v_a_4295_, v_a_4296_, v_a_4297_, v_a_4298_);
v___y_4339_ = v___x_4350_;
goto v___jp_4338_;
}
}
else
{
size_t v___x_4351_; lean_object* v___x_4352_; 
v___x_4351_ = lean_usize_of_nat(v___x_4345_);
lean_inc_ref(v_docCtx_4290_);
v___x_4352_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4(v_names_4302_, v_docCtx_4290_, v_fst_4307_, v___x_4301_, v___x_4351_, v___x_4347_, v_a_4293_, v_a_4294_, v_a_4295_, v_a_4296_, v_a_4297_, v_a_4298_);
v___y_4339_ = v___x_4352_;
goto v___jp_4338_;
}
}
}
else
{
lean_object* v_a_4353_; lean_object* v___x_4355_; uint8_t v_isShared_4356_; uint8_t v_isSharedCheck_4360_; 
lean_dec(v_snd_4308_);
lean_dec(v_fst_4307_);
lean_dec(v_fst_4306_);
lean_dec_ref(v_names_4302_);
lean_dec_ref(v_preDefs_4291_);
lean_dec_ref(v_docCtx_4290_);
v_a_4353_ = lean_ctor_get(v___x_4344_, 0);
v_isSharedCheck_4360_ = !lean_is_exclusive(v___x_4344_);
if (v_isSharedCheck_4360_ == 0)
{
v___x_4355_ = v___x_4344_;
v_isShared_4356_ = v_isSharedCheck_4360_;
goto v_resetjp_4354_;
}
else
{
lean_inc(v_a_4353_);
lean_dec(v___x_4344_);
v___x_4355_ = lean_box(0);
v_isShared_4356_ = v_isSharedCheck_4360_;
goto v_resetjp_4354_;
}
v_resetjp_4354_:
{
lean_object* v___x_4358_; 
if (v_isShared_4356_ == 0)
{
v___x_4358_ = v___x_4355_;
goto v_reusejp_4357_;
}
else
{
lean_object* v_reuseFailAlloc_4359_; 
v_reuseFailAlloc_4359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4359_, 0, v_a_4353_);
v___x_4358_ = v_reuseFailAlloc_4359_;
goto v_reusejp_4357_;
}
v_reusejp_4357_:
{
return v___x_4358_;
}
}
}
v___jp_4309_:
{
lean_object* v___x_4310_; 
v___x_4310_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___redArg(v_sz_4300_, v___x_4301_, v_preDefs_4291_, v_a_4297_, v_a_4298_);
if (lean_obj_tag(v___x_4310_) == 0)
{
lean_object* v_a_4311_; lean_object* v___x_4312_; 
v_a_4311_ = lean_ctor_get(v___x_4310_, 0);
lean_inc(v_a_4311_);
lean_dec_ref(v___x_4310_);
lean_inc(v_a_4311_);
lean_inc_ref(v_docCtx_4290_);
v___x_4312_ = l_Lean_Elab_addAndCompilePartialRec(v_docCtx_4290_, v_a_4311_, v_a_4293_, v_a_4294_, v_a_4295_, v_a_4296_, v_a_4297_, v_a_4298_);
if (lean_obj_tag(v___x_4312_) == 0)
{
lean_object* v___x_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; size_t v_sz_4316_; lean_object* v___x_4317_; 
lean_dec_ref(v___x_4312_);
v___x_4313_ = lean_unsigned_to_nat(0u);
v___x_4314_ = lean_array_get_size(v_fst_4306_);
v___x_4315_ = l_Array_toSubarray___redArg(v_fst_4306_, v___x_4313_, v___x_4314_);
v_sz_4316_ = lean_array_size(v_a_4311_);
lean_inc(v_a_4311_);
v___x_4317_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__1(v_docCtx_4290_, v_a_4311_, v_snd_4308_, v_a_4311_, v_sz_4316_, v___x_4301_, v___x_4315_, v_a_4293_, v_a_4294_, v_a_4295_, v_a_4296_, v_a_4297_, v_a_4298_);
if (lean_obj_tag(v___x_4317_) == 0)
{
lean_object* v___x_4318_; lean_object* v___x_4319_; 
lean_dec_ref(v___x_4317_);
v___x_4318_ = lean_box(0);
v___x_4319_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___redArg(v_a_4311_, v_sz_4316_, v___x_4301_, v___x_4318_, v_a_4295_, v_a_4296_, v_a_4297_, v_a_4298_);
lean_dec(v_a_4311_);
if (lean_obj_tag(v___x_4319_) == 0)
{
uint8_t v___x_4320_; lean_object* v___x_4321_; 
lean_dec_ref(v___x_4319_);
v___x_4320_ = 1;
v___x_4321_ = l_Lean_Elab_applyAttributesOf(v_fst_4307_, v___x_4320_, v_a_4293_, v_a_4294_, v_a_4295_, v_a_4296_, v_a_4297_, v_a_4298_);
lean_dec(v_fst_4307_);
return v___x_4321_;
}
else
{
lean_dec(v_fst_4307_);
return v___x_4319_;
}
}
else
{
lean_object* v_a_4322_; lean_object* v___x_4324_; uint8_t v_isShared_4325_; uint8_t v_isSharedCheck_4329_; 
lean_dec(v_a_4311_);
lean_dec(v_fst_4307_);
v_a_4322_ = lean_ctor_get(v___x_4317_, 0);
v_isSharedCheck_4329_ = !lean_is_exclusive(v___x_4317_);
if (v_isSharedCheck_4329_ == 0)
{
v___x_4324_ = v___x_4317_;
v_isShared_4325_ = v_isSharedCheck_4329_;
goto v_resetjp_4323_;
}
else
{
lean_inc(v_a_4322_);
lean_dec(v___x_4317_);
v___x_4324_ = lean_box(0);
v_isShared_4325_ = v_isSharedCheck_4329_;
goto v_resetjp_4323_;
}
v_resetjp_4323_:
{
lean_object* v___x_4327_; 
if (v_isShared_4325_ == 0)
{
v___x_4327_ = v___x_4324_;
goto v_reusejp_4326_;
}
else
{
lean_object* v_reuseFailAlloc_4328_; 
v_reuseFailAlloc_4328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4328_, 0, v_a_4322_);
v___x_4327_ = v_reuseFailAlloc_4328_;
goto v_reusejp_4326_;
}
v_reusejp_4326_:
{
return v___x_4327_;
}
}
}
}
else
{
lean_dec(v_a_4311_);
lean_dec(v_snd_4308_);
lean_dec(v_fst_4307_);
lean_dec(v_fst_4306_);
lean_dec_ref(v_docCtx_4290_);
return v___x_4312_;
}
}
else
{
lean_object* v_a_4330_; lean_object* v___x_4332_; uint8_t v_isShared_4333_; uint8_t v_isSharedCheck_4337_; 
lean_dec(v_snd_4308_);
lean_dec(v_fst_4307_);
lean_dec(v_fst_4306_);
lean_dec_ref(v_docCtx_4290_);
v_a_4330_ = lean_ctor_get(v___x_4310_, 0);
v_isSharedCheck_4337_ = !lean_is_exclusive(v___x_4310_);
if (v_isSharedCheck_4337_ == 0)
{
v___x_4332_ = v___x_4310_;
v_isShared_4333_ = v_isSharedCheck_4337_;
goto v_resetjp_4331_;
}
else
{
lean_inc(v_a_4330_);
lean_dec(v___x_4310_);
v___x_4332_ = lean_box(0);
v_isShared_4333_ = v_isSharedCheck_4337_;
goto v_resetjp_4331_;
}
v_resetjp_4331_:
{
lean_object* v___x_4335_; 
if (v_isShared_4333_ == 0)
{
v___x_4335_ = v___x_4332_;
goto v_reusejp_4334_;
}
else
{
lean_object* v_reuseFailAlloc_4336_; 
v_reuseFailAlloc_4336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4336_, 0, v_a_4330_);
v___x_4335_ = v_reuseFailAlloc_4336_;
goto v_reusejp_4334_;
}
v_reusejp_4334_:
{
return v___x_4335_;
}
}
}
}
v___jp_4338_:
{
if (lean_obj_tag(v___y_4339_) == 0)
{
lean_dec_ref(v___y_4339_);
goto v___jp_4309_;
}
else
{
lean_dec(v_snd_4308_);
lean_dec(v_fst_4307_);
lean_dec(v_fst_4306_);
lean_dec_ref(v_preDefs_4291_);
lean_dec_ref(v_docCtx_4290_);
return v___y_4339_;
}
}
}
else
{
lean_object* v_a_4361_; lean_object* v___x_4363_; uint8_t v_isShared_4364_; uint8_t v_isSharedCheck_4368_; 
lean_dec_ref(v_names_4302_);
lean_dec_ref(v_preDefs_4291_);
lean_dec_ref(v_docCtx_4290_);
v_a_4361_ = lean_ctor_get(v___x_4303_, 0);
v_isSharedCheck_4368_ = !lean_is_exclusive(v___x_4303_);
if (v_isSharedCheck_4368_ == 0)
{
v___x_4363_ = v___x_4303_;
v_isShared_4364_ = v_isSharedCheck_4368_;
goto v_resetjp_4362_;
}
else
{
lean_inc(v_a_4361_);
lean_dec(v___x_4303_);
v___x_4363_ = lean_box(0);
v_isShared_4364_ = v_isSharedCheck_4368_;
goto v_resetjp_4362_;
}
v_resetjp_4362_:
{
lean_object* v___x_4366_; 
if (v_isShared_4364_ == 0)
{
v___x_4366_ = v___x_4363_;
goto v_reusejp_4365_;
}
else
{
lean_object* v_reuseFailAlloc_4367_; 
v_reuseFailAlloc_4367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4367_, 0, v_a_4361_);
v___x_4366_ = v_reuseFailAlloc_4367_;
goto v_reusejp_4365_;
}
v_reusejp_4365_:
{
return v___x_4366_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_structuralRecursion___boxed(lean_object* v_docCtx_4369_, lean_object* v_preDefs_4370_, lean_object* v_termMeasure_x3fs_4371_, lean_object* v_a_4372_, lean_object* v_a_4373_, lean_object* v_a_4374_, lean_object* v_a_4375_, lean_object* v_a_4376_, lean_object* v_a_4377_, lean_object* v_a_4378_){
_start:
{
lean_object* v_res_4379_; 
v_res_4379_ = l_Lean_Elab_Structural_structuralRecursion(v_docCtx_4369_, v_preDefs_4370_, v_termMeasure_x3fs_4371_, v_a_4372_, v_a_4373_, v_a_4374_, v_a_4375_, v_a_4376_, v_a_4377_);
lean_dec(v_a_4377_);
lean_dec_ref(v_a_4376_);
lean_dec(v_a_4375_);
lean_dec_ref(v_a_4374_);
lean_dec(v_a_4373_);
lean_dec_ref(v_a_4372_);
return v_res_4379_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0(size_t v_sz_4380_, size_t v_i_4381_, lean_object* v_bs_4382_, lean_object* v___y_4383_, lean_object* v___y_4384_, lean_object* v___y_4385_, lean_object* v___y_4386_, lean_object* v___y_4387_, lean_object* v___y_4388_){
_start:
{
lean_object* v___x_4390_; 
v___x_4390_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___redArg(v_sz_4380_, v_i_4381_, v_bs_4382_, v___y_4387_, v___y_4388_);
return v___x_4390_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___boxed(lean_object* v_sz_4391_, lean_object* v_i_4392_, lean_object* v_bs_4393_, lean_object* v___y_4394_, lean_object* v___y_4395_, lean_object* v___y_4396_, lean_object* v___y_4397_, lean_object* v___y_4398_, lean_object* v___y_4399_, lean_object* v___y_4400_){
_start:
{
size_t v_sz_boxed_4401_; size_t v_i_boxed_4402_; lean_object* v_res_4403_; 
v_sz_boxed_4401_ = lean_unbox_usize(v_sz_4391_);
lean_dec(v_sz_4391_);
v_i_boxed_4402_ = lean_unbox_usize(v_i_4392_);
lean_dec(v_i_4392_);
v_res_4403_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0(v_sz_boxed_4401_, v_i_boxed_4402_, v_bs_4393_, v___y_4394_, v___y_4395_, v___y_4396_, v___y_4397_, v___y_4398_, v___y_4399_);
lean_dec(v___y_4399_);
lean_dec_ref(v___y_4398_);
lean_dec(v___y_4397_);
lean_dec_ref(v___y_4396_);
lean_dec(v___y_4395_);
lean_dec_ref(v___y_4394_);
return v_res_4403_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2(lean_object* v_as_4404_, size_t v_sz_4405_, size_t v_i_4406_, lean_object* v_b_4407_, lean_object* v___y_4408_, lean_object* v___y_4409_, lean_object* v___y_4410_, lean_object* v___y_4411_, lean_object* v___y_4412_, lean_object* v___y_4413_){
_start:
{
lean_object* v___x_4415_; 
v___x_4415_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___redArg(v_as_4404_, v_sz_4405_, v_i_4406_, v_b_4407_, v___y_4410_, v___y_4411_, v___y_4412_, v___y_4413_);
return v___x_4415_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___boxed(lean_object* v_as_4416_, lean_object* v_sz_4417_, lean_object* v_i_4418_, lean_object* v_b_4419_, lean_object* v___y_4420_, lean_object* v___y_4421_, lean_object* v___y_4422_, lean_object* v___y_4423_, lean_object* v___y_4424_, lean_object* v___y_4425_, lean_object* v___y_4426_){
_start:
{
size_t v_sz_boxed_4427_; size_t v_i_boxed_4428_; lean_object* v_res_4429_; 
v_sz_boxed_4427_ = lean_unbox_usize(v_sz_4417_);
lean_dec(v_sz_4417_);
v_i_boxed_4428_ = lean_unbox_usize(v_i_4418_);
lean_dec(v_i_4418_);
v_res_4429_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2(v_as_4416_, v_sz_boxed_4427_, v_i_boxed_4428_, v_b_4419_, v___y_4420_, v___y_4421_, v___y_4422_, v___y_4423_, v___y_4424_, v___y_4425_);
lean_dec(v___y_4425_);
lean_dec_ref(v___y_4424_);
lean_dec(v___y_4423_);
lean_dec_ref(v___y_4422_);
lean_dec(v___y_4421_);
lean_dec_ref(v___y_4420_);
lean_dec_ref(v_as_4416_);
return v_res_4429_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3(lean_object* v_as_4430_, size_t v_sz_4431_, size_t v_i_4432_, lean_object* v_b_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_){
_start:
{
lean_object* v___x_4441_; 
v___x_4441_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___redArg(v_as_4430_, v_sz_4431_, v_i_4432_, v_b_4433_, v___y_4436_, v___y_4437_, v___y_4438_, v___y_4439_);
return v___x_4441_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___boxed(lean_object* v_as_4442_, lean_object* v_sz_4443_, lean_object* v_i_4444_, lean_object* v_b_4445_, lean_object* v___y_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_, lean_object* v___y_4452_){
_start:
{
size_t v_sz_boxed_4453_; size_t v_i_boxed_4454_; lean_object* v_res_4455_; 
v_sz_boxed_4453_ = lean_unbox_usize(v_sz_4443_);
lean_dec(v_sz_4443_);
v_i_boxed_4454_ = lean_unbox_usize(v_i_4444_);
lean_dec(v_i_4444_);
v_res_4455_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3(v_as_4442_, v_sz_boxed_4453_, v_i_boxed_4454_, v_b_4445_, v___y_4446_, v___y_4447_, v___y_4448_, v___y_4449_, v___y_4450_, v___y_4451_);
lean_dec(v___y_4451_);
lean_dec_ref(v___y_4450_);
lean_dec(v___y_4449_);
lean_dec_ref(v___y_4448_);
lean_dec(v___y_4447_);
lean_dec_ref(v___y_4446_);
lean_dec_ref(v_as_4442_);
return v_res_4455_;
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
