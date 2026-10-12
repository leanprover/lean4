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
lean_object* l_Lean_Elab_Structural_mkBRecOnMotive(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_FixedParamPerm_instantiateForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_unlockAsync(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Elab_addAsAxiom___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_Meta_PProdN_mkLambdas___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_withEnv___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Lean_enableRealizationsForConst(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_erase(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_Elab_Structural_RecArgInfo_indicesAndRecArgPos(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
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
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
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
lean_object* l_Lean_Elab_addNonRec(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16_spec__29___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16_spec__29___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_f"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(253, 65, 185, 154, 193, 83, 240, 170)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg(lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16_spec__29(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16_spec__29___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__2(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___f_39_; uint8_t v___x_40_; 
v___f_39_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___redArg___lam__2), 3, 1);
lean_closure_set(v___f_39_, 0, v_inst_19_);
v___x_40_ = lean_nat_dec_le(v___x_35_, v___x_35_);
if (v___x_40_ == 0)
{
if (v___x_37_ == 0)
{
lean_object* v___x_41_; 
lean_dec_ref(v___f_39_);
lean_dec_ref(v_preDefs_22_);
lean_inc(v_toPure_26_);
v___x_41_ = lean_apply_2(v_toPure_26_, lean_box(0), v___x_36_);
v___y_29_ = v___x_41_;
goto v___jp_28_;
}
else
{
size_t v___x_42_; size_t v___x_43_; lean_object* v___x_44_; 
v___x_42_ = ((size_t)0ULL);
v___x_43_ = lean_usize_of_nat(v___x_35_);
lean_inc_ref(v_inst_18_);
v___x_44_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_18_, v___f_39_, v_preDefs_22_, v___x_42_, v___x_43_, v___x_36_);
v___y_29_ = v___x_44_;
goto v___jp_28_;
}
}
else
{
size_t v___x_45_; size_t v___x_46_; lean_object* v___x_47_; 
v___x_45_ = ((size_t)0ULL);
v___x_46_ = lean_usize_of_nat(v___x_35_);
lean_inc_ref(v_inst_18_);
v___x_47_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_18_, v___f_39_, v_preDefs_22_, v___x_45_, v___x_46_, v___x_36_);
v___y_29_ = v___x_47_;
goto v___jp_28_;
}
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms(lean_object* v_n_48_, lean_object* v_00_u03b1_49_, lean_object* v_inst_50_, lean_object* v_inst_51_, lean_object* v_inst_52_, lean_object* v_inst_53_, lean_object* v_preDefs_54_, lean_object* v_k_55_){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___redArg(v_inst_50_, v_inst_51_, v_inst_52_, v_inst_53_, v_preDefs_54_, v_k_55_);
return v___x_56_;
}
}
lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg___lam__0(lean_object* v_k_57_, lean_object* v_b_58_, lean_object* v_c_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_){
_start:
{
lean_object* v___x_65_; 
lean_inc(v___y_63_);
lean_inc_ref(v___y_62_);
lean_inc(v___y_61_);
lean_inc_ref(v___y_60_);
v___x_65_ = lean_apply_7(v_k_57_, v_b_58_, v_c_59_, v___y_60_, v___y_61_, v___y_62_, v___y_63_, lean_box(0));
return v___x_65_;
}
}
LEAN_EXPORT void l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_57_ = stack[0].m_obj;
lean_object* v_b_58_ = stack[1].m_obj;
lean_object* v_c_59_ = stack[2].m_obj;
lean_object* v___y_60_ = stack[3].m_obj;
lean_object* v___y_61_ = stack[4].m_obj;
lean_object* v___y_62_ = stack[5].m_obj;
lean_object* v___y_63_ = stack[6].m_obj;
lean_object* v_res_66_;
v_res_66_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg___lam__0(v_k_57_, v_b_58_, v_c_59_, v___y_60_, v___y_61_, v___y_62_, v___y_63_);
stack->m_obj
 = v_res_66_;
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
lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg(lean_object* v_e_76_, lean_object* v_k_77_, uint8_t v_cleanupAnnotations_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_){
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
LEAN_EXPORT void l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_76_ = stack[0].m_obj;
lean_object* v_k_77_ = stack[1].m_obj;
uint8_t v_cleanupAnnotations_78_ = stack[2].m_num;
lean_object* v___y_79_ = stack[3].m_obj;
lean_object* v___y_80_ = stack[4].m_obj;
lean_object* v___y_81_ = stack[5].m_obj;
lean_object* v___y_82_ = stack[6].m_obj;
lean_object* v_res_105_;
v_res_105_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg(v_e_76_, v_k_77_, v_cleanupAnnotations_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_);
stack->m_obj
 = v_res_105_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg___boxed(lean_object* v_e_106_, lean_object* v_k_107_, lean_object* v_cleanupAnnotations_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_114_; lean_object* v_res_115_; 
v_cleanupAnnotations_boxed_114_ = lean_unbox(v_cleanupAnnotations_108_);
v_res_115_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg(v_e_106_, v_k_107_, v_cleanupAnnotations_boxed_114_, v___y_109_, v___y_110_, v___y_111_, v___y_112_);
lean_dec(v___y_112_);
lean_dec_ref(v___y_111_);
lean_dec(v___y_110_);
lean_dec_ref(v___y_109_);
return v_res_115_;
}
}
lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1(lean_object* v_00_u03b1_116_, lean_object* v_e_117_, lean_object* v_k_118_, uint8_t v_cleanupAnnotations_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_){
_start:
{
lean_object* v___x_125_; 
v___x_125_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg(v_e_117_, v_k_118_, v_cleanupAnnotations_119_, v___y_120_, v___y_121_, v___y_122_, v___y_123_);
return v___x_125_;
}
}
LEAN_EXPORT void l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_117_ = stack[1].m_obj;
lean_object* v_k_118_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_119_ = stack[3].m_num;
lean_object* v___y_120_ = stack[4].m_obj;
lean_object* v___y_121_ = stack[5].m_obj;
lean_object* v___y_122_ = stack[6].m_obj;
lean_object* v___y_123_ = stack[7].m_obj;
lean_object* v_res_126_;
v_res_126_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1(lean_box(0), v_e_117_, v_k_118_, v_cleanupAnnotations_119_, v___y_120_, v___y_121_, v___y_122_, v___y_123_);
stack->m_obj
 = v_res_126_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___boxed(lean_object* v_00_u03b1_127_, lean_object* v_e_128_, lean_object* v_k_129_, lean_object* v_cleanupAnnotations_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_136_; lean_object* v_res_137_; 
v_cleanupAnnotations_boxed_136_ = lean_unbox(v_cleanupAnnotations_130_);
v_res_137_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1(v_00_u03b1_127_, v_e_128_, v_k_129_, v_cleanupAnnotations_boxed_136_, v___y_131_, v___y_132_, v___y_133_, v___y_134_);
lean_dec(v___y_134_);
lean_dec_ref(v___y_133_);
lean_dec(v___y_132_);
lean_dec_ref(v___y_131_);
return v_res_137_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0(lean_object* v_x_138_){
_start:
{
lean_object* v_indIdx_139_; 
v_indIdx_139_ = lean_ctor_get(v_x_138_, 5);
lean_inc(v_indIdx_139_);
return v_indIdx_139_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0___boxed(lean_object* v_x_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0(v_x_140_);
lean_dec_ref(v_x_140_);
return v_res_141_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1(lean_object* v___x_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_){
_start:
{
lean_object* v_toCold_151_; lean_object* v_options_152_; uint8_t v_hasTrace_153_; 
v_toCold_151_ = lean_ctor_get(v___y_148_, 0);
v_options_152_ = lean_ctor_get(v_toCold_151_, 2);
v_hasTrace_153_ = lean_ctor_get_uint8(v_options_152_, sizeof(void*)*1);
if (v_hasTrace_153_ == 0)
{
lean_object* v___x_154_; lean_object* v___x_155_; 
lean_dec(v___x_145_);
v___x_154_ = lean_box(v_hasTrace_153_);
v___x_155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_155_, 0, v___x_154_);
return v___x_155_;
}
else
{
lean_object* v_inheritedTraceOptions_156_; lean_object* v___x_157_; lean_object* v___x_158_; uint8_t v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v_inheritedTraceOptions_156_ = lean_ctor_get(v_toCold_151_, 11);
v___x_157_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___closed__1));
v___x_158_ = l_Lean_Name_append(v___x_157_, v___x_145_);
v___x_159_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_156_, v_options_152_, v___x_158_);
lean_dec(v___x_158_);
v___x_160_ = lean_box(v___x_159_);
v___x_161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_161_, 0, v___x_160_);
return v___x_161_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_145_ = stack[0].m_obj;
lean_object* v___y_146_ = stack[1].m_obj;
lean_object* v___y_147_ = stack[2].m_obj;
lean_object* v___y_148_ = stack[3].m_obj;
lean_object* v___y_149_ = stack[4].m_obj;
lean_object* v_res_162_;
v_res_162_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1(v___x_145_, v___y_146_, v___y_147_, v___y_148_, v___y_149_);
stack->m_obj
 = v_res_162_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___boxed(lean_object* v___x_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1(v___x_163_, v___y_164_, v___y_165_, v___y_166_, v___y_167_);
lean_dec(v___y_167_);
lean_dec_ref(v___y_166_);
lean_dec(v___y_165_);
lean_dec_ref(v___y_164_);
return v_res_169_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13(lean_object* v_as_170_, size_t v_i_171_, size_t v_stop_172_, lean_object* v_b_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_){
_start:
{
uint8_t v___x_179_; 
v___x_179_ = lean_usize_dec_eq(v_i_171_, v_stop_172_);
if (v___x_179_ == 0)
{
lean_object* v___x_19437__overap_180_; lean_object* v___x_181_; 
v___x_19437__overap_180_ = lean_array_uget_borrowed(v_as_170_, v_i_171_);
lean_inc(v___x_19437__overap_180_);
lean_inc(v___y_177_);
lean_inc_ref(v___y_176_);
lean_inc(v___y_175_);
lean_inc_ref(v___y_174_);
v___x_181_ = lean_apply_5(v___x_19437__overap_180_, v___y_174_, v___y_175_, v___y_176_, v___y_177_, lean_box(0));
if (lean_obj_tag(v___x_181_) == 0)
{
lean_object* v_a_182_; size_t v___x_183_; size_t v___x_184_; 
v_a_182_ = lean_ctor_get(v___x_181_, 0);
lean_inc(v_a_182_);
lean_dec_ref_known(v___x_181_, 1);
v___x_183_ = ((size_t)1ULL);
v___x_184_ = lean_usize_add(v_i_171_, v___x_183_);
v_i_171_ = v___x_184_;
v_b_173_ = v_a_182_;
goto _start;
}
else
{
return v___x_181_;
}
}
else
{
lean_object* v___x_186_; 
v___x_186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_186_, 0, v_b_173_);
return v___x_186_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_170_ = stack[0].m_obj;
size_t v_i_171_ = stack[1].m_num;
size_t v_stop_172_ = stack[2].m_num;
lean_object* v_b_173_ = stack[3].m_obj;
lean_object* v___y_174_ = stack[4].m_obj;
lean_object* v___y_175_ = stack[5].m_obj;
lean_object* v___y_176_ = stack[6].m_obj;
lean_object* v___y_177_ = stack[7].m_obj;
lean_object* v_res_187_;
v_res_187_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13(v_as_170_, v_i_171_, v_stop_172_, v_b_173_, v___y_174_, v___y_175_, v___y_176_, v___y_177_);
stack->m_obj
 = v_res_187_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13___boxed(lean_object* v_as_188_, lean_object* v_i_189_, lean_object* v_stop_190_, lean_object* v_b_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_){
_start:
{
size_t v_i_boxed_197_; size_t v_stop_boxed_198_; lean_object* v_res_199_; 
v_i_boxed_197_ = lean_unbox_usize(v_i_189_);
lean_dec(v_i_189_);
v_stop_boxed_198_ = lean_unbox_usize(v_stop_190_);
lean_dec(v_stop_190_);
v_res_199_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13(v_as_188_, v_i_boxed_197_, v_stop_boxed_198_, v_b_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_);
lean_dec(v___y_195_);
lean_dec_ref(v___y_194_);
lean_dec(v___y_193_);
lean_dec_ref(v___y_192_);
lean_dec_ref(v_as_188_);
return v_res_199_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__24___redArg(lean_object* v_as_200_, size_t v_i_201_, size_t v_stop_202_, lean_object* v_b_203_, lean_object* v___y_204_, lean_object* v___y_205_){
_start:
{
uint8_t v___x_207_; 
v___x_207_ = lean_usize_dec_eq(v_i_201_, v_stop_202_);
if (v___x_207_ == 0)
{
lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_208_ = lean_array_uget_borrowed(v_as_200_, v_i_201_);
v___x_209_ = l_Lean_Elab_addAsAxiom___redArg(v___x_208_, v___y_204_, v___y_205_);
if (lean_obj_tag(v___x_209_) == 0)
{
lean_object* v_a_210_; size_t v___x_211_; size_t v___x_212_; 
v_a_210_ = lean_ctor_get(v___x_209_, 0);
lean_inc(v_a_210_);
lean_dec_ref_known(v___x_209_, 1);
v___x_211_ = ((size_t)1ULL);
v___x_212_ = lean_usize_add(v_i_201_, v___x_211_);
v_i_201_ = v___x_212_;
v_b_203_ = v_a_210_;
goto _start;
}
else
{
return v___x_209_;
}
}
else
{
lean_object* v___x_214_; 
v___x_214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_214_, 0, v_b_203_);
return v___x_214_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__24___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_200_ = stack[0].m_obj;
size_t v_i_201_ = stack[1].m_num;
size_t v_stop_202_ = stack[2].m_num;
lean_object* v_b_203_ = stack[3].m_obj;
lean_object* v___y_204_ = stack[4].m_obj;
lean_object* v___y_205_ = stack[5].m_obj;
lean_object* v_res_215_;
v_res_215_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__24___redArg(v_as_200_, v_i_201_, v_stop_202_, v_b_203_, v___y_204_, v___y_205_);
stack->m_obj
 = v_res_215_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__24___redArg___boxed(lean_object* v_as_216_, lean_object* v_i_217_, lean_object* v_stop_218_, lean_object* v_b_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_){
_start:
{
size_t v_i_boxed_223_; size_t v_stop_boxed_224_; lean_object* v_res_225_; 
v_i_boxed_223_ = lean_unbox_usize(v_i_217_);
lean_dec(v_i_217_);
v_stop_boxed_224_ = lean_unbox_usize(v_stop_218_);
lean_dec(v_stop_218_);
v_res_225_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__24___redArg(v_as_216_, v_i_boxed_223_, v_stop_boxed_224_, v_b_219_, v___y_220_, v___y_221_);
lean_dec(v___y_221_);
lean_dec_ref(v___y_220_);
lean_dec_ref(v_as_216_);
return v_res_225_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__24(lean_object* v_as_226_, size_t v_i_227_, size_t v_stop_228_, lean_object* v_b_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_){
_start:
{
lean_object* v___x_235_; 
v___x_235_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__24___redArg(v_as_226_, v_i_227_, v_stop_228_, v_b_229_, v___y_232_, v___y_233_);
return v___x_235_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__24_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_226_ = stack[0].m_obj;
size_t v_i_227_ = stack[1].m_num;
size_t v_stop_228_ = stack[2].m_num;
lean_object* v_b_229_ = stack[3].m_obj;
lean_object* v___y_230_ = stack[4].m_obj;
lean_object* v___y_231_ = stack[5].m_obj;
lean_object* v___y_232_ = stack[6].m_obj;
lean_object* v___y_233_ = stack[7].m_obj;
lean_object* v_res_236_;
v_res_236_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__24(v_as_226_, v_i_227_, v_stop_228_, v_b_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_);
stack->m_obj
 = v_res_236_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__24___boxed(lean_object* v_as_237_, lean_object* v_i_238_, lean_object* v_stop_239_, lean_object* v_b_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_){
_start:
{
size_t v_i_boxed_246_; size_t v_stop_boxed_247_; lean_object* v_res_248_; 
v_i_boxed_246_ = lean_unbox_usize(v_i_238_);
lean_dec(v_i_238_);
v_stop_boxed_247_ = lean_unbox_usize(v_stop_239_);
lean_dec(v_stop_239_);
v_res_248_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__24(v_as_237_, v_i_boxed_246_, v_stop_boxed_247_, v_b_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_);
lean_dec(v___y_244_);
lean_dec_ref(v___y_243_);
lean_dec(v___y_242_);
lean_dec_ref(v___y_241_);
lean_dec_ref(v_as_237_);
return v_res_248_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__0(void){
_start:
{
lean_object* v___x_249_; 
v___x_249_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_249_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__1(void){
_start:
{
lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_250_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__0, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__0);
v___x_251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_251_, 0, v___x_250_);
return v___x_251_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__2(void){
_start:
{
lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_252_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__1, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__1);
v___x_253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_253_, 0, v___x_252_);
lean_ctor_set(v___x_253_, 1, v___x_252_);
return v___x_253_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__3(void){
_start:
{
lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_254_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__1, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__1);
v___x_255_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_255_, 0, v___x_254_);
lean_ctor_set(v___x_255_, 1, v___x_254_);
lean_ctor_set(v___x_255_, 2, v___x_254_);
lean_ctor_set(v___x_255_, 3, v___x_254_);
lean_ctor_set(v___x_255_, 4, v___x_254_);
lean_ctor_set(v___x_255_, 5, v___x_254_);
return v___x_255_;
}
}
lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg(lean_object* v_env_256_, lean_object* v___y_257_, lean_object* v___y_258_){
_start:
{
lean_object* v___x_260_; lean_object* v_nextMacroScope_261_; lean_object* v_ngen_262_; lean_object* v_auxDeclNGen_263_; lean_object* v_traceState_264_; lean_object* v_recordedDeps_265_; lean_object* v_messages_266_; lean_object* v_infoState_267_; lean_object* v_snapshotTasks_268_; lean_object* v___x_270_; uint8_t v_isShared_271_; uint8_t v_isSharedCheck_294_; 
v___x_260_ = lean_st_ref_take(v___y_258_);
v_nextMacroScope_261_ = lean_ctor_get(v___x_260_, 1);
v_ngen_262_ = lean_ctor_get(v___x_260_, 2);
v_auxDeclNGen_263_ = lean_ctor_get(v___x_260_, 3);
v_traceState_264_ = lean_ctor_get(v___x_260_, 4);
v_recordedDeps_265_ = lean_ctor_get(v___x_260_, 6);
v_messages_266_ = lean_ctor_get(v___x_260_, 7);
v_infoState_267_ = lean_ctor_get(v___x_260_, 8);
v_snapshotTasks_268_ = lean_ctor_get(v___x_260_, 9);
v_isSharedCheck_294_ = !lean_is_exclusive(v___x_260_);
if (v_isSharedCheck_294_ == 0)
{
lean_object* v_unused_295_; lean_object* v_unused_296_; 
v_unused_295_ = lean_ctor_get(v___x_260_, 5);
lean_dec(v_unused_295_);
v_unused_296_ = lean_ctor_get(v___x_260_, 0);
lean_dec(v_unused_296_);
v___x_270_ = v___x_260_;
v_isShared_271_ = v_isSharedCheck_294_;
goto v_resetjp_269_;
}
else
{
lean_inc(v_snapshotTasks_268_);
lean_inc(v_infoState_267_);
lean_inc(v_messages_266_);
lean_inc(v_recordedDeps_265_);
lean_inc(v_traceState_264_);
lean_inc(v_auxDeclNGen_263_);
lean_inc(v_ngen_262_);
lean_inc(v_nextMacroScope_261_);
lean_dec(v___x_260_);
v___x_270_ = lean_box(0);
v_isShared_271_ = v_isSharedCheck_294_;
goto v_resetjp_269_;
}
v_resetjp_269_:
{
lean_object* v___x_272_; lean_object* v___x_274_; 
v___x_272_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__2);
if (v_isShared_271_ == 0)
{
lean_ctor_set(v___x_270_, 5, v___x_272_);
lean_ctor_set(v___x_270_, 0, v_env_256_);
v___x_274_ = v___x_270_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v_env_256_);
lean_ctor_set(v_reuseFailAlloc_293_, 1, v_nextMacroScope_261_);
lean_ctor_set(v_reuseFailAlloc_293_, 2, v_ngen_262_);
lean_ctor_set(v_reuseFailAlloc_293_, 3, v_auxDeclNGen_263_);
lean_ctor_set(v_reuseFailAlloc_293_, 4, v_traceState_264_);
lean_ctor_set(v_reuseFailAlloc_293_, 5, v___x_272_);
lean_ctor_set(v_reuseFailAlloc_293_, 6, v_recordedDeps_265_);
lean_ctor_set(v_reuseFailAlloc_293_, 7, v_messages_266_);
lean_ctor_set(v_reuseFailAlloc_293_, 8, v_infoState_267_);
lean_ctor_set(v_reuseFailAlloc_293_, 9, v_snapshotTasks_268_);
v___x_274_ = v_reuseFailAlloc_293_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v_mctx_277_; lean_object* v_zetaDeltaFVarIds_278_; lean_object* v_postponed_279_; lean_object* v_diag_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_291_; 
v___x_275_ = lean_st_ref_put(v___y_258_, v___x_274_);
v___x_276_ = lean_st_ref_take(v___y_257_);
v_mctx_277_ = lean_ctor_get(v___x_276_, 0);
v_zetaDeltaFVarIds_278_ = lean_ctor_get(v___x_276_, 2);
v_postponed_279_ = lean_ctor_get(v___x_276_, 3);
v_diag_280_ = lean_ctor_get(v___x_276_, 4);
v_isSharedCheck_291_ = !lean_is_exclusive(v___x_276_);
if (v_isSharedCheck_291_ == 0)
{
lean_object* v_unused_292_; 
v_unused_292_ = lean_ctor_get(v___x_276_, 1);
lean_dec(v_unused_292_);
v___x_282_ = v___x_276_;
v_isShared_283_ = v_isSharedCheck_291_;
goto v_resetjp_281_;
}
else
{
lean_inc(v_diag_280_);
lean_inc(v_postponed_279_);
lean_inc(v_zetaDeltaFVarIds_278_);
lean_inc(v_mctx_277_);
lean_dec(v___x_276_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_291_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_287_; 
v___x_284_ = lean_box(0);
v___x_285_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__3, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__3);
if (v_isShared_283_ == 0)
{
lean_ctor_set(v___x_282_, 1, v___x_285_);
v___x_287_ = v___x_282_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v_mctx_277_);
lean_ctor_set(v_reuseFailAlloc_290_, 1, v___x_285_);
lean_ctor_set(v_reuseFailAlloc_290_, 2, v_zetaDeltaFVarIds_278_);
lean_ctor_set(v_reuseFailAlloc_290_, 3, v_postponed_279_);
lean_ctor_set(v_reuseFailAlloc_290_, 4, v_diag_280_);
v___x_287_ = v_reuseFailAlloc_290_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_288_ = lean_st_ref_put(v___y_257_, v___x_287_);
v___x_289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_289_, 0, v___x_284_);
return v___x_289_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_256_ = stack[0].m_obj;
lean_object* v___y_257_ = stack[1].m_obj;
lean_object* v___y_258_ = stack[2].m_obj;
lean_object* v_res_297_;
v_res_297_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg(v_env_256_, v___y_257_, v___y_258_);
stack->m_obj
 = v_res_297_;
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___boxed(lean_object* v_env_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg(v_env_298_, v___y_299_, v___y_300_);
lean_dec(v___y_300_);
lean_dec(v___y_299_);
return v_res_302_;
}
}
lean_object* l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23___redArg(lean_object* v_env_303_, lean_object* v_x_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_){
_start:
{
lean_object* v___x_310_; lean_object* v_env_311_; lean_object* v_a_313_; lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_310_ = lean_st_ref_get(v___y_308_);
v_env_311_ = lean_ctor_get(v___x_310_, 0);
lean_inc_ref(v_env_311_);
lean_dec(v___x_310_);
v___x_323_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg(v_env_303_, v___y_306_, v___y_308_);
lean_dec_ref(v___x_323_);
lean_inc(v___y_308_);
lean_inc_ref(v___y_307_);
lean_inc(v___y_306_);
lean_inc_ref(v___y_305_);
v___x_324_ = lean_apply_5(v_x_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_, lean_box(0));
if (lean_obj_tag(v___x_324_) == 0)
{
lean_object* v_a_325_; lean_object* v___x_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_333_; 
v_a_325_ = lean_ctor_get(v___x_324_, 0);
lean_inc(v_a_325_);
lean_dec_ref_known(v___x_324_, 1);
v___x_326_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg(v_env_311_, v___y_306_, v___y_308_);
v_isSharedCheck_333_ = !lean_is_exclusive(v___x_326_);
if (v_isSharedCheck_333_ == 0)
{
lean_object* v_unused_334_; 
v_unused_334_ = lean_ctor_get(v___x_326_, 0);
lean_dec(v_unused_334_);
v___x_328_ = v___x_326_;
v_isShared_329_ = v_isSharedCheck_333_;
goto v_resetjp_327_;
}
else
{
lean_dec(v___x_326_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_333_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___x_331_; 
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 0, v_a_325_);
v___x_331_ = v___x_328_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v_a_325_);
v___x_331_ = v_reuseFailAlloc_332_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
return v___x_331_;
}
}
}
else
{
lean_object* v_a_335_; 
v_a_335_ = lean_ctor_get(v___x_324_, 0);
lean_inc(v_a_335_);
lean_dec_ref_known(v___x_324_, 1);
v_a_313_ = v_a_335_;
goto v___jp_312_;
}
v___jp_312_:
{
lean_object* v___x_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_321_; 
v___x_314_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg(v_env_311_, v___y_306_, v___y_308_);
v_isSharedCheck_321_ = !lean_is_exclusive(v___x_314_);
if (v_isSharedCheck_321_ == 0)
{
lean_object* v_unused_322_; 
v_unused_322_ = lean_ctor_get(v___x_314_, 0);
lean_dec(v_unused_322_);
v___x_316_ = v___x_314_;
v_isShared_317_ = v_isSharedCheck_321_;
goto v_resetjp_315_;
}
else
{
lean_dec(v___x_314_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_321_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
lean_object* v___x_319_; 
if (v_isShared_317_ == 0)
{
lean_ctor_set_tag(v___x_316_, 1);
lean_ctor_set(v___x_316_, 0, v_a_313_);
v___x_319_ = v___x_316_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v_a_313_);
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
}
LEAN_EXPORT void l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_303_ = stack[0].m_obj;
lean_object* v_x_304_ = stack[1].m_obj;
lean_object* v___y_305_ = stack[2].m_obj;
lean_object* v___y_306_ = stack[3].m_obj;
lean_object* v___y_307_ = stack[4].m_obj;
lean_object* v___y_308_ = stack[5].m_obj;
lean_object* v_res_336_;
v_res_336_ = l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23___redArg(v_env_303_, v_x_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_);
stack->m_obj
 = v_res_336_;
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23___redArg___boxed(lean_object* v_env_337_, lean_object* v_x_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23___redArg(v_env_337_, v_x_338_, v___y_339_, v___y_340_, v___y_341_, v___y_342_);
lean_dec(v___y_342_);
lean_dec_ref(v___y_341_);
lean_dec(v___y_340_);
lean_dec_ref(v___y_339_);
return v_res_344_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___lam__1(lean_object* v___x_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_){
_start:
{
lean_object* v___x_351_; 
v___x_351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_351_, 0, v___x_345_);
return v___x_351_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_345_ = stack[0].m_obj;
lean_object* v___y_346_ = stack[1].m_obj;
lean_object* v___y_347_ = stack[2].m_obj;
lean_object* v___y_348_ = stack[3].m_obj;
lean_object* v___y_349_ = stack[4].m_obj;
lean_object* v_res_352_;
v_res_352_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___lam__1(v___x_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_);
stack->m_obj
 = v_res_352_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___lam__1___boxed(lean_object* v___x_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___lam__1(v___x_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_);
lean_dec(v___y_357_);
lean_dec_ref(v___y_356_);
lean_dec(v___y_355_);
lean_dec_ref(v___y_354_);
return v_res_359_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___lam__0(lean_object* v___y_360_, lean_object* v_k_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_){
_start:
{
lean_object* v___x_367_; 
lean_inc(v___y_365_);
lean_inc_ref(v___y_364_);
lean_inc(v___y_363_);
lean_inc_ref(v___y_362_);
v___x_367_ = lean_apply_5(v___y_360_, v___y_362_, v___y_363_, v___y_364_, v___y_365_, lean_box(0));
if (lean_obj_tag(v___x_367_) == 0)
{
lean_object* v___x_368_; 
lean_dec_ref_known(v___x_367_, 1);
v___x_368_ = lean_apply_5(v_k_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_, lean_box(0));
return v___x_368_;
}
else
{
lean_object* v_a_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_376_; 
lean_dec(v___y_365_);
lean_dec_ref(v___y_364_);
lean_dec(v___y_363_);
lean_dec_ref(v___y_362_);
lean_dec_ref(v_k_361_);
v_a_369_ = lean_ctor_get(v___x_367_, 0);
v_isSharedCheck_376_ = !lean_is_exclusive(v___x_367_);
if (v_isSharedCheck_376_ == 0)
{
v___x_371_ = v___x_367_;
v_isShared_372_ = v_isSharedCheck_376_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_a_369_);
lean_dec(v___x_367_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_376_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v___x_374_; 
if (v_isShared_372_ == 0)
{
v___x_374_ = v___x_371_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v_a_369_);
v___x_374_ = v_reuseFailAlloc_375_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
return v___x_374_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_360_ = stack[0].m_obj;
lean_object* v_k_361_ = stack[1].m_obj;
lean_object* v___y_362_ = stack[2].m_obj;
lean_object* v___y_363_ = stack[3].m_obj;
lean_object* v___y_364_ = stack[4].m_obj;
lean_object* v___y_365_ = stack[5].m_obj;
lean_object* v_res_377_;
v_res_377_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___lam__0(v___y_360_, v_k_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_);
stack->m_obj
 = v_res_377_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___lam__0___boxed(lean_object* v___y_378_, lean_object* v_k_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___lam__0(v___y_378_, v_k_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_);
return v_res_385_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(lean_object* v_preDefs_390_, lean_object* v_k_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_){
_start:
{
lean_object* v___y_398_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; uint8_t v___x_407_; 
v___x_404_ = lean_unsigned_to_nat(0u);
v___x_405_ = lean_array_get_size(v_preDefs_390_);
v___x_406_ = lean_box(0);
v___x_407_ = lean_nat_dec_lt(v___x_404_, v___x_405_);
if (v___x_407_ == 0)
{
lean_object* v___f_408_; 
lean_dec_ref(v_preDefs_390_);
v___f_408_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___closed__0));
v___y_398_ = v___f_408_;
goto v___jp_397_;
}
else
{
size_t v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_409_ = lean_usize_of_nat(v___x_405_);
v___x_410_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___boxed__const__1));
v___x_411_ = lean_box_usize(v___x_409_);
v___x_412_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__24___boxed), 9, 4);
lean_closure_set(v___x_412_, 0, v_preDefs_390_);
lean_closure_set(v___x_412_, 1, v___x_410_);
lean_closure_set(v___x_412_, 2, v___x_411_);
lean_closure_set(v___x_412_, 3, v___x_406_);
v___y_398_ = v___x_412_;
goto v___jp_397_;
}
v___jp_397_:
{
lean_object* v___f_399_; lean_object* v___x_400_; lean_object* v_env_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
v___f_399_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_399_, 0, v___y_398_);
lean_closure_set(v___f_399_, 1, v_k_391_);
v___x_400_ = lean_st_ref_get(v___y_395_);
v_env_401_ = lean_ctor_get(v___x_400_, 0);
lean_inc_ref(v_env_401_);
lean_dec(v___x_400_);
v___x_402_ = l_Lean_Environment_unlockAsync(v_env_401_);
v___x_403_ = l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23___redArg(v___x_402_, v___f_399_, v___y_392_, v___y_393_, v___y_394_, v___y_395_);
return v___x_403_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_preDefs_390_ = stack[0].m_obj;
lean_object* v_k_391_ = stack[1].m_obj;
lean_object* v___y_392_ = stack[2].m_obj;
lean_object* v___y_393_ = stack[3].m_obj;
lean_object* v___y_394_ = stack[4].m_obj;
lean_object* v___y_395_ = stack[5].m_obj;
lean_object* v_res_413_;
v_res_413_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v_preDefs_390_, v_k_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_);
stack->m_obj
 = v_res_413_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___boxed(lean_object* v_preDefs_414_, lean_object* v_k_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v_preDefs_414_, v_k_415_, v___y_416_, v___y_417_, v___y_418_, v___y_419_);
lean_dec(v___y_419_);
lean_dec_ref(v___y_418_);
lean_dec(v___y_417_);
lean_dec_ref(v___y_416_);
return v_res_421_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg___closed__0(void){
_start:
{
lean_object* v___x_422_; lean_object* v_dummy_423_; 
v___x_422_ = lean_box(0);
v_dummy_423_ = l_Lean_Expr_sort___override(v___x_422_);
return v_dummy_423_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg(uint8_t v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_recArgInfos_427_, lean_object* v___x_428_, lean_object* v_preDefs_429_, lean_object* v_a_430_, size_t v_sz_431_, size_t v_i_432_, lean_object* v_bs_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_){
_start:
{
uint8_t v___x_439_; 
v___x_439_ = lean_usize_dec_lt(v_i_432_, v_sz_431_);
if (v___x_439_ == 0)
{
lean_object* v___x_440_; 
lean_dec_ref(v_a_430_);
lean_dec_ref(v_preDefs_429_);
lean_dec_ref(v___x_428_);
lean_dec_ref(v_recArgInfos_427_);
v___x_440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_440_, 0, v_bs_433_);
return v___x_440_;
}
else
{
lean_object* v___x_441_; lean_object* v_v_442_; lean_object* v___x_443_; lean_object* v_bs_x27_444_; lean_object* v_a_446_; lean_object* v___x_451_; 
v___x_441_ = l_Lean_instInhabitedExpr;
v_v_442_ = lean_array_uget(v_bs_433_, v_i_432_);
v___x_443_ = lean_unsigned_to_nat(0u);
v_bs_x27_444_ = lean_array_uset(v_bs_433_, v_i_432_, v___x_443_);
v___x_451_ = lean_usize_to_nat(v_i_432_);
if (v_a_424_ == 0)
{
lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_452_ = lean_array_get_borrowed(v___x_441_, v_a_425_, v___x_451_);
v___x_453_ = lean_array_get_borrowed(v___x_441_, v_a_426_, v___x_451_);
lean_dec(v___x_451_);
lean_inc(v___x_453_);
lean_inc(v___x_452_);
lean_inc_ref(v___x_428_);
lean_inc_ref(v_recArgInfos_427_);
v___x_454_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnF___boxed), 10, 5);
lean_closure_set(v___x_454_, 0, v_recArgInfos_427_);
lean_closure_set(v___x_454_, 1, v___x_428_);
lean_closure_set(v___x_454_, 2, v_v_442_);
lean_closure_set(v___x_454_, 3, v___x_452_);
lean_closure_set(v___x_454_, 4, v___x_453_);
lean_inc_ref(v_preDefs_429_);
v___x_455_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v_preDefs_429_, v___x_454_, v___y_434_, v___y_435_, v___y_436_, v___y_437_);
if (lean_obj_tag(v___x_455_) == 0)
{
lean_object* v_a_456_; 
v_a_456_ = lean_ctor_get(v___x_455_, 0);
lean_inc(v_a_456_);
lean_dec_ref_known(v___x_455_, 1);
v_a_446_ = v_a_456_;
goto v___jp_445_;
}
else
{
lean_object* v_a_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_464_; 
lean_dec_ref(v_bs_x27_444_);
lean_dec_ref(v_a_430_);
lean_dec_ref(v_preDefs_429_);
lean_dec_ref(v___x_428_);
lean_dec_ref(v_recArgInfos_427_);
v_a_457_ = lean_ctor_get(v___x_455_, 0);
v_isSharedCheck_464_ = !lean_is_exclusive(v___x_455_);
if (v_isSharedCheck_464_ == 0)
{
v___x_459_ = v___x_455_;
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_a_457_);
lean_dec(v___x_455_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_462_; 
if (v_isShared_460_ == 0)
{
v___x_462_ = v___x_459_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_a_457_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
}
}
else
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v_dummy_468_; lean_object* v_nargs_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
v___x_465_ = lean_array_get_borrowed(v___x_441_, v_a_425_, v___x_451_);
v___x_466_ = lean_array_get_borrowed(v___x_441_, v_a_426_, v___x_451_);
lean_dec(v___x_451_);
lean_inc_ref(v_a_430_);
v___x_467_ = lean_apply_1(v_a_430_, v___x_443_);
v_dummy_468_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg___closed__0);
v_nargs_469_ = l_Lean_Expr_getAppNumArgs(v___x_467_);
lean_inc(v_nargs_469_);
v___x_470_ = lean_mk_array(v_nargs_469_, v_dummy_468_);
v___x_471_ = lean_unsigned_to_nat(1u);
v___x_472_ = lean_nat_sub(v_nargs_469_, v___x_471_);
lean_dec(v_nargs_469_);
v___x_473_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___x_467_, v___x_470_, v___x_472_);
lean_inc(v___x_466_);
lean_inc(v___x_465_);
lean_inc_ref(v___x_428_);
lean_inc_ref(v_recArgInfos_427_);
v___x_474_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkIndPredBRecOnF___boxed), 11, 6);
lean_closure_set(v___x_474_, 0, v_recArgInfos_427_);
lean_closure_set(v___x_474_, 1, v___x_428_);
lean_closure_set(v___x_474_, 2, v_v_442_);
lean_closure_set(v___x_474_, 3, v___x_465_);
lean_closure_set(v___x_474_, 4, v___x_466_);
lean_closure_set(v___x_474_, 5, v___x_473_);
lean_inc_ref(v_preDefs_429_);
v___x_475_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v_preDefs_429_, v___x_474_, v___y_434_, v___y_435_, v___y_436_, v___y_437_);
if (lean_obj_tag(v___x_475_) == 0)
{
lean_object* v_a_476_; lean_object* v_fst_477_; lean_object* v_snd_478_; lean_object* v___y_480_; lean_object* v___x_489_; uint8_t v___x_490_; 
v_a_476_ = lean_ctor_get(v___x_475_, 0);
lean_inc(v_a_476_);
lean_dec_ref_known(v___x_475_, 1);
v_fst_477_ = lean_ctor_get(v_a_476_, 0);
lean_inc(v_fst_477_);
v_snd_478_ = lean_ctor_get(v_a_476_, 1);
lean_inc(v_snd_478_);
lean_dec(v_a_476_);
v___x_489_ = lean_array_get_size(v_snd_478_);
v___x_490_ = lean_nat_dec_lt(v___x_443_, v___x_489_);
if (v___x_490_ == 0)
{
lean_dec(v_snd_478_);
v_a_446_ = v_fst_477_;
goto v___jp_445_;
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
v_a_446_ = v_fst_477_;
goto v___jp_445_;
}
else
{
size_t v___x_493_; size_t v___x_494_; lean_object* v___x_495_; 
v___x_493_ = ((size_t)0ULL);
v___x_494_ = lean_usize_of_nat(v___x_489_);
v___x_495_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13(v_snd_478_, v___x_493_, v___x_494_, v___x_491_, v___y_434_, v___y_435_, v___y_436_, v___y_437_);
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
v___x_498_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13(v_snd_478_, v___x_496_, v___x_497_, v___x_491_, v___y_434_, v___y_435_, v___y_436_, v___y_437_);
lean_dec(v_snd_478_);
v___y_480_ = v___x_498_;
goto v___jp_479_;
}
}
v___jp_479_:
{
if (lean_obj_tag(v___y_480_) == 0)
{
lean_dec_ref_known(v___y_480_, 1);
v_a_446_ = v_fst_477_;
goto v___jp_445_;
}
else
{
lean_object* v_a_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_488_; 
lean_dec(v_fst_477_);
lean_dec_ref(v_bs_x27_444_);
lean_dec_ref(v_a_430_);
lean_dec_ref(v_preDefs_429_);
lean_dec_ref(v___x_428_);
lean_dec_ref(v_recArgInfos_427_);
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
lean_dec_ref(v_bs_x27_444_);
lean_dec_ref(v_a_430_);
lean_dec_ref(v_preDefs_429_);
lean_dec_ref(v___x_428_);
lean_dec_ref(v_recArgInfos_427_);
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
v___jp_445_:
{
size_t v___x_447_; size_t v___x_448_; lean_object* v___x_449_; 
v___x_447_ = ((size_t)1ULL);
v___x_448_ = lean_usize_add(v_i_432_, v___x_447_);
v___x_449_ = lean_array_uset(v_bs_x27_444_, v_i_432_, v_a_446_);
v_i_432_ = v___x_448_;
v_bs_433_ = v___x_449_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_424_ = stack[0].m_num;
lean_object* v_a_425_ = stack[1].m_obj;
lean_object* v_a_426_ = stack[2].m_obj;
lean_object* v_recArgInfos_427_ = stack[3].m_obj;
lean_object* v___x_428_ = stack[4].m_obj;
lean_object* v_preDefs_429_ = stack[5].m_obj;
lean_object* v_a_430_ = stack[6].m_obj;
size_t v_sz_431_ = stack[7].m_num;
size_t v_i_432_ = stack[8].m_num;
lean_object* v_bs_433_ = stack[9].m_obj;
lean_object* v___y_434_ = stack[10].m_obj;
lean_object* v___y_435_ = stack[11].m_obj;
lean_object* v___y_436_ = stack[12].m_obj;
lean_object* v___y_437_ = stack[13].m_obj;
lean_object* v_res_507_;
v_res_507_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg(v_a_424_, v_a_425_, v_a_426_, v_recArgInfos_427_, v___x_428_, v_preDefs_429_, v_a_430_, v_sz_431_, v_i_432_, v_bs_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_);
stack->m_obj
 = v_res_507_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg___boxed(lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_recArgInfos_511_, lean_object* v___x_512_, lean_object* v_preDefs_513_, lean_object* v_a_514_, lean_object* v_sz_515_, lean_object* v_i_516_, lean_object* v_bs_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_){
_start:
{
uint8_t v_a_25586__boxed_523_; size_t v_sz_boxed_524_; size_t v_i_boxed_525_; lean_object* v_res_526_; 
v_a_25586__boxed_523_ = lean_unbox(v_a_508_);
v_sz_boxed_524_ = lean_unbox_usize(v_sz_515_);
lean_dec(v_sz_515_);
v_i_boxed_525_ = lean_unbox_usize(v_i_516_);
lean_dec(v_i_516_);
v_res_526_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg(v_a_25586__boxed_523_, v_a_509_, v_a_510_, v_recArgInfos_511_, v___x_512_, v_preDefs_513_, v_a_514_, v_sz_boxed_524_, v_i_boxed_525_, v_bs_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_);
lean_dec(v___y_521_);
lean_dec_ref(v___y_520_);
lean_dec(v___y_519_);
lean_dec_ref(v___y_518_);
lean_dec_ref(v_a_510_);
lean_dec_ref(v_a_509_);
return v_res_526_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11_spec__21(lean_object* v_msgData_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_){
_start:
{
lean_object* v___x_533_; lean_object* v_env_534_; uint8_t v___x_535_; lean_object* v_env_536_; lean_object* v___x_537_; lean_object* v_toCold_538_; lean_object* v_mctx_539_; lean_object* v_lctx_540_; lean_object* v_options_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_533_ = lean_st_ref_get(v___y_531_);
v_env_534_ = lean_ctor_get(v___x_533_, 0);
lean_inc_ref(v_env_534_);
lean_dec(v___x_533_);
v___x_535_ = 0;
v_env_536_ = l_Lean_Environment_setRecordingDeps(v_env_534_, v___x_535_);
v___x_537_ = lean_st_ref_get(v___y_529_);
v_toCold_538_ = lean_ctor_get(v___y_530_, 0);
v_mctx_539_ = lean_ctor_get(v___x_537_, 0);
lean_inc_ref(v_mctx_539_);
lean_dec(v___x_537_);
v_lctx_540_ = lean_ctor_get(v___y_528_, 2);
v_options_541_ = lean_ctor_get(v_toCold_538_, 2);
lean_inc_ref(v_options_541_);
lean_inc_ref(v_lctx_540_);
v___x_542_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_542_, 0, v_env_536_);
lean_ctor_set(v___x_542_, 1, v_mctx_539_);
lean_ctor_set(v___x_542_, 2, v_lctx_540_);
lean_ctor_set(v___x_542_, 3, v_options_541_);
v___x_543_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_543_, 0, v___x_542_);
lean_ctor_set(v___x_543_, 1, v_msgData_527_);
v___x_544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_544_, 0, v___x_543_);
return v___x_544_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11_spec__21_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_527_ = stack[0].m_obj;
lean_object* v___y_528_ = stack[1].m_obj;
lean_object* v___y_529_ = stack[2].m_obj;
lean_object* v___y_530_ = stack[3].m_obj;
lean_object* v___y_531_ = stack[4].m_obj;
lean_object* v_res_545_;
v_res_545_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11_spec__21(v_msgData_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_);
stack->m_obj
 = v_res_545_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11_spec__21___boxed(lean_object* v_msgData_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11_spec__21(v_msgData_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_);
lean_dec(v___y_550_);
lean_dec_ref(v___y_549_);
lean_dec(v___y_548_);
lean_dec_ref(v___y_547_);
return v_res_552_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___closed__0(void){
_start:
{
lean_object* v___x_553_; double v___x_554_; 
v___x_553_ = lean_unsigned_to_nat(0u);
v___x_554_ = lean_float_of_nat(v___x_553_);
return v___x_554_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(lean_object* v_cls_558_, lean_object* v_msg_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_){
_start:
{
lean_object* v_ref_565_; lean_object* v___x_566_; lean_object* v_a_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_612_; 
v_ref_565_ = lean_ctor_get(v___y_562_, 2);
v___x_566_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11_spec__21(v_msg_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_);
v_a_567_ = lean_ctor_get(v___x_566_, 0);
v_isSharedCheck_612_ = !lean_is_exclusive(v___x_566_);
if (v_isSharedCheck_612_ == 0)
{
v___x_569_ = v___x_566_;
v_isShared_570_ = v_isSharedCheck_612_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_a_567_);
lean_dec(v___x_566_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_612_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v___x_571_; lean_object* v_traceState_572_; lean_object* v_env_573_; lean_object* v_nextMacroScope_574_; lean_object* v_ngen_575_; lean_object* v_auxDeclNGen_576_; lean_object* v_cache_577_; lean_object* v_recordedDeps_578_; lean_object* v_messages_579_; lean_object* v_infoState_580_; lean_object* v_snapshotTasks_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_611_; 
v___x_571_ = lean_st_ref_take(v___y_563_);
v_traceState_572_ = lean_ctor_get(v___x_571_, 4);
v_env_573_ = lean_ctor_get(v___x_571_, 0);
v_nextMacroScope_574_ = lean_ctor_get(v___x_571_, 1);
v_ngen_575_ = lean_ctor_get(v___x_571_, 2);
v_auxDeclNGen_576_ = lean_ctor_get(v___x_571_, 3);
v_cache_577_ = lean_ctor_get(v___x_571_, 5);
v_recordedDeps_578_ = lean_ctor_get(v___x_571_, 6);
v_messages_579_ = lean_ctor_get(v___x_571_, 7);
v_infoState_580_ = lean_ctor_get(v___x_571_, 8);
v_snapshotTasks_581_ = lean_ctor_get(v___x_571_, 9);
v_isSharedCheck_611_ = !lean_is_exclusive(v___x_571_);
if (v_isSharedCheck_611_ == 0)
{
v___x_583_ = v___x_571_;
v_isShared_584_ = v_isSharedCheck_611_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_snapshotTasks_581_);
lean_inc(v_infoState_580_);
lean_inc(v_messages_579_);
lean_inc(v_recordedDeps_578_);
lean_inc(v_cache_577_);
lean_inc(v_traceState_572_);
lean_inc(v_auxDeclNGen_576_);
lean_inc(v_ngen_575_);
lean_inc(v_nextMacroScope_574_);
lean_inc(v_env_573_);
lean_dec(v___x_571_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_611_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
uint64_t v_tid_585_; lean_object* v_traces_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_610_; 
v_tid_585_ = lean_ctor_get_uint64(v_traceState_572_, sizeof(void*)*1);
v_traces_586_ = lean_ctor_get(v_traceState_572_, 0);
v_isSharedCheck_610_ = !lean_is_exclusive(v_traceState_572_);
if (v_isSharedCheck_610_ == 0)
{
v___x_588_ = v_traceState_572_;
v_isShared_589_ = v_isSharedCheck_610_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_traces_586_);
lean_dec(v_traceState_572_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_610_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v___x_590_; lean_object* v___x_591_; double v___x_592_; uint8_t v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_601_; 
v___x_590_ = lean_box(0);
v___x_591_ = lean_box(0);
v___x_592_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___closed__0);
v___x_593_ = 0;
v___x_594_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___closed__1));
v___x_595_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_595_, 0, v_cls_558_);
lean_ctor_set(v___x_595_, 1, v___x_591_);
lean_ctor_set(v___x_595_, 2, v___x_594_);
lean_ctor_set_float(v___x_595_, sizeof(void*)*3, v___x_592_);
lean_ctor_set_float(v___x_595_, sizeof(void*)*3 + 8, v___x_592_);
lean_ctor_set_uint8(v___x_595_, sizeof(void*)*3 + 16, v___x_593_);
v___x_596_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___closed__2));
v___x_597_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_597_, 0, v___x_595_);
lean_ctor_set(v___x_597_, 1, v_a_567_);
lean_ctor_set(v___x_597_, 2, v___x_596_);
lean_inc(v_ref_565_);
v___x_598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_598_, 0, v_ref_565_);
lean_ctor_set(v___x_598_, 1, v___x_597_);
v___x_599_ = l_Lean_PersistentArray_push___redArg(v_traces_586_, v___x_598_);
if (v_isShared_589_ == 0)
{
lean_ctor_set(v___x_588_, 0, v___x_599_);
v___x_601_ = v___x_588_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v___x_599_);
lean_ctor_set_uint64(v_reuseFailAlloc_609_, sizeof(void*)*1, v_tid_585_);
v___x_601_ = v_reuseFailAlloc_609_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
lean_object* v___x_603_; 
if (v_isShared_584_ == 0)
{
lean_ctor_set(v___x_583_, 4, v___x_601_);
v___x_603_ = v___x_583_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v_env_573_);
lean_ctor_set(v_reuseFailAlloc_608_, 1, v_nextMacroScope_574_);
lean_ctor_set(v_reuseFailAlloc_608_, 2, v_ngen_575_);
lean_ctor_set(v_reuseFailAlloc_608_, 3, v_auxDeclNGen_576_);
lean_ctor_set(v_reuseFailAlloc_608_, 4, v___x_601_);
lean_ctor_set(v_reuseFailAlloc_608_, 5, v_cache_577_);
lean_ctor_set(v_reuseFailAlloc_608_, 6, v_recordedDeps_578_);
lean_ctor_set(v_reuseFailAlloc_608_, 7, v_messages_579_);
lean_ctor_set(v_reuseFailAlloc_608_, 8, v_infoState_580_);
lean_ctor_set(v_reuseFailAlloc_608_, 9, v_snapshotTasks_581_);
v___x_603_ = v_reuseFailAlloc_608_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
lean_object* v___x_604_; lean_object* v___x_606_; 
v___x_604_ = lean_st_ref_put(v___y_563_, v___x_603_);
if (v_isShared_570_ == 0)
{
lean_ctor_set(v___x_569_, 0, v___x_590_);
v___x_606_ = v___x_569_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v___x_590_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
return v___x_606_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_558_ = stack[0].m_obj;
lean_object* v_msg_559_ = stack[1].m_obj;
lean_object* v___y_560_ = stack[2].m_obj;
lean_object* v___y_561_ = stack[3].m_obj;
lean_object* v___y_562_ = stack[4].m_obj;
lean_object* v___y_563_ = stack[5].m_obj;
lean_object* v_res_613_;
v_res_613_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v_cls_558_, v_msg_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_);
stack->m_obj
 = v_res_613_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___boxed(lean_object* v_cls_614_, lean_object* v_msg_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v_cls_614_, v_msg_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_);
lean_dec(v___y_619_);
lean_dec_ref(v___y_618_);
lean_dec(v___y_617_);
lean_dec_ref(v___y_616_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9(lean_object* v_as_622_, lean_object* v_bs_623_, lean_object* v_i_624_, lean_object* v_cs_625_){
_start:
{
lean_object* v___x_626_; uint8_t v___x_627_; 
v___x_626_ = lean_array_get_size(v_as_622_);
v___x_627_ = lean_nat_dec_lt(v_i_624_, v___x_626_);
if (v___x_627_ == 0)
{
lean_dec(v_i_624_);
return v_cs_625_;
}
else
{
lean_object* v___x_628_; uint8_t v___x_629_; 
v___x_628_ = lean_array_get_size(v_bs_623_);
v___x_629_ = lean_nat_dec_lt(v_i_624_, v___x_628_);
if (v___x_629_ == 0)
{
lean_dec(v_i_624_);
return v_cs_625_;
}
else
{
lean_object* v_a_630_; lean_object* v_ref_631_; uint8_t v_kind_632_; lean_object* v_levelParams_633_; lean_object* v_modifiers_634_; lean_object* v_declName_635_; lean_object* v_binders_636_; lean_object* v_numSectionVars_637_; lean_object* v_type_638_; lean_object* v_termination_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_651_; 
v_a_630_ = lean_array_fget(v_as_622_, v_i_624_);
v_ref_631_ = lean_ctor_get(v_a_630_, 0);
v_kind_632_ = lean_ctor_get_uint8(v_a_630_, sizeof(void*)*9);
v_levelParams_633_ = lean_ctor_get(v_a_630_, 1);
v_modifiers_634_ = lean_ctor_get(v_a_630_, 2);
v_declName_635_ = lean_ctor_get(v_a_630_, 3);
v_binders_636_ = lean_ctor_get(v_a_630_, 4);
v_numSectionVars_637_ = lean_ctor_get(v_a_630_, 5);
v_type_638_ = lean_ctor_get(v_a_630_, 6);
v_termination_639_ = lean_ctor_get(v_a_630_, 8);
v_isSharedCheck_651_ = !lean_is_exclusive(v_a_630_);
if (v_isSharedCheck_651_ == 0)
{
lean_object* v_unused_652_; 
v_unused_652_ = lean_ctor_get(v_a_630_, 7);
lean_dec(v_unused_652_);
v___x_641_ = v_a_630_;
v_isShared_642_ = v_isSharedCheck_651_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_termination_639_);
lean_inc(v_type_638_);
lean_inc(v_numSectionVars_637_);
lean_inc(v_binders_636_);
lean_inc(v_declName_635_);
lean_inc(v_modifiers_634_);
lean_inc(v_levelParams_633_);
lean_inc(v_ref_631_);
lean_dec(v_a_630_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_651_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v_b_643_; lean_object* v___x_645_; 
v_b_643_ = lean_array_fget_borrowed(v_bs_623_, v_i_624_);
lean_inc(v_b_643_);
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 7, v_b_643_);
v___x_645_ = v___x_641_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v_ref_631_);
lean_ctor_set(v_reuseFailAlloc_650_, 1, v_levelParams_633_);
lean_ctor_set(v_reuseFailAlloc_650_, 2, v_modifiers_634_);
lean_ctor_set(v_reuseFailAlloc_650_, 3, v_declName_635_);
lean_ctor_set(v_reuseFailAlloc_650_, 4, v_binders_636_);
lean_ctor_set(v_reuseFailAlloc_650_, 5, v_numSectionVars_637_);
lean_ctor_set(v_reuseFailAlloc_650_, 6, v_type_638_);
lean_ctor_set(v_reuseFailAlloc_650_, 7, v_b_643_);
lean_ctor_set(v_reuseFailAlloc_650_, 8, v_termination_639_);
lean_ctor_set_uint8(v_reuseFailAlloc_650_, sizeof(void*)*9, v_kind_632_);
v___x_645_ = v_reuseFailAlloc_650_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_646_ = lean_unsigned_to_nat(1u);
v___x_647_ = lean_nat_add(v_i_624_, v___x_646_);
lean_dec(v_i_624_);
v___x_648_ = lean_array_push(v_cs_625_, v___x_645_);
v_i_624_ = v___x_647_;
v_cs_625_ = v___x_648_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9___boxed(lean_object* v_as_653_, lean_object* v_bs_654_, lean_object* v_i_655_, lean_object* v_cs_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9(v_as_653_, v_bs_654_, v_i_655_, v_cs_656_);
lean_dec_ref(v_bs_654_);
lean_dec_ref(v_as_653_);
return v_res_657_;
}
}
lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16_spec__29___redArg(lean_object* v_declName_658_, uint8_t v_s_659_, lean_object* v___y_660_, lean_object* v___y_661_){
_start:
{
lean_object* v___x_663_; lean_object* v_env_664_; lean_object* v_nextMacroScope_665_; lean_object* v_ngen_666_; lean_object* v_auxDeclNGen_667_; lean_object* v_traceState_668_; lean_object* v_recordedDeps_669_; lean_object* v_messages_670_; lean_object* v_infoState_671_; lean_object* v_snapshotTasks_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_701_; 
v___x_663_ = lean_st_ref_take(v___y_661_);
v_env_664_ = lean_ctor_get(v___x_663_, 0);
v_nextMacroScope_665_ = lean_ctor_get(v___x_663_, 1);
v_ngen_666_ = lean_ctor_get(v___x_663_, 2);
v_auxDeclNGen_667_ = lean_ctor_get(v___x_663_, 3);
v_traceState_668_ = lean_ctor_get(v___x_663_, 4);
v_recordedDeps_669_ = lean_ctor_get(v___x_663_, 6);
v_messages_670_ = lean_ctor_get(v___x_663_, 7);
v_infoState_671_ = lean_ctor_get(v___x_663_, 8);
v_snapshotTasks_672_ = lean_ctor_get(v___x_663_, 9);
v_isSharedCheck_701_ = !lean_is_exclusive(v___x_663_);
if (v_isSharedCheck_701_ == 0)
{
lean_object* v_unused_702_; 
v_unused_702_ = lean_ctor_get(v___x_663_, 5);
lean_dec(v_unused_702_);
v___x_674_ = v___x_663_;
v_isShared_675_ = v_isSharedCheck_701_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_snapshotTasks_672_);
lean_inc(v_infoState_671_);
lean_inc(v_messages_670_);
lean_inc(v_recordedDeps_669_);
lean_inc(v_traceState_668_);
lean_inc(v_auxDeclNGen_667_);
lean_inc(v_ngen_666_);
lean_inc(v_nextMacroScope_665_);
lean_inc(v_env_664_);
lean_dec(v___x_663_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_701_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
uint8_t v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_681_; 
v___x_676_ = 0;
v___x_677_ = lean_box(0);
v___x_678_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_664_, v_declName_658_, v_s_659_, v___x_676_, v___x_677_);
v___x_679_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__2);
if (v_isShared_675_ == 0)
{
lean_ctor_set(v___x_674_, 5, v___x_679_);
lean_ctor_set(v___x_674_, 0, v___x_678_);
v___x_681_ = v___x_674_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v___x_678_);
lean_ctor_set(v_reuseFailAlloc_700_, 1, v_nextMacroScope_665_);
lean_ctor_set(v_reuseFailAlloc_700_, 2, v_ngen_666_);
lean_ctor_set(v_reuseFailAlloc_700_, 3, v_auxDeclNGen_667_);
lean_ctor_set(v_reuseFailAlloc_700_, 4, v_traceState_668_);
lean_ctor_set(v_reuseFailAlloc_700_, 5, v___x_679_);
lean_ctor_set(v_reuseFailAlloc_700_, 6, v_recordedDeps_669_);
lean_ctor_set(v_reuseFailAlloc_700_, 7, v_messages_670_);
lean_ctor_set(v_reuseFailAlloc_700_, 8, v_infoState_671_);
lean_ctor_set(v_reuseFailAlloc_700_, 9, v_snapshotTasks_672_);
v___x_681_ = v_reuseFailAlloc_700_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v_mctx_684_; lean_object* v_zetaDeltaFVarIds_685_; lean_object* v_postponed_686_; lean_object* v_diag_687_; lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_698_; 
v___x_682_ = lean_st_ref_put(v___y_661_, v___x_681_);
v___x_683_ = lean_st_ref_take(v___y_660_);
v_mctx_684_ = lean_ctor_get(v___x_683_, 0);
v_zetaDeltaFVarIds_685_ = lean_ctor_get(v___x_683_, 2);
v_postponed_686_ = lean_ctor_get(v___x_683_, 3);
v_diag_687_ = lean_ctor_get(v___x_683_, 4);
v_isSharedCheck_698_ = !lean_is_exclusive(v___x_683_);
if (v_isSharedCheck_698_ == 0)
{
lean_object* v_unused_699_; 
v_unused_699_ = lean_ctor_get(v___x_683_, 1);
lean_dec(v_unused_699_);
v___x_689_ = v___x_683_;
v_isShared_690_ = v_isSharedCheck_698_;
goto v_resetjp_688_;
}
else
{
lean_inc(v_diag_687_);
lean_inc(v_postponed_686_);
lean_inc(v_zetaDeltaFVarIds_685_);
lean_inc(v_mctx_684_);
lean_dec(v___x_683_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_698_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_694_; 
v___x_691_ = lean_box(0);
v___x_692_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__3, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__3);
if (v_isShared_690_ == 0)
{
lean_ctor_set(v___x_689_, 1, v___x_692_);
v___x_694_ = v___x_689_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_mctx_684_);
lean_ctor_set(v_reuseFailAlloc_697_, 1, v___x_692_);
lean_ctor_set(v_reuseFailAlloc_697_, 2, v_zetaDeltaFVarIds_685_);
lean_ctor_set(v_reuseFailAlloc_697_, 3, v_postponed_686_);
lean_ctor_set(v_reuseFailAlloc_697_, 4, v_diag_687_);
v___x_694_ = v_reuseFailAlloc_697_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_695_ = lean_st_ref_put(v___y_660_, v___x_694_);
v___x_696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_696_, 0, v___x_691_);
return v___x_696_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16_spec__29___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_658_ = stack[0].m_obj;
uint8_t v_s_659_ = stack[1].m_num;
lean_object* v___y_660_ = stack[2].m_obj;
lean_object* v___y_661_ = stack[3].m_obj;
lean_object* v_res_703_;
v_res_703_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16_spec__29___redArg(v_declName_658_, v_s_659_, v___y_660_, v___y_661_);
stack->m_obj
 = v_res_703_;
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16_spec__29___redArg___boxed(lean_object* v_declName_704_, lean_object* v_s_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_){
_start:
{
uint8_t v_s_boxed_709_; lean_object* v_res_710_; 
v_s_boxed_709_ = lean_unbox(v_s_705_);
v_res_710_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16_spec__29___redArg(v_declName_704_, v_s_boxed_709_, v___y_706_, v___y_707_);
lean_dec(v___y_707_);
lean_dec(v___y_706_);
return v_res_710_;
}
}
lean_object* l_Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16(lean_object* v_declName_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_){
_start:
{
uint8_t v___x_717_; lean_object* v___x_718_; 
v___x_717_ = 0;
v___x_718_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16_spec__29___redArg(v_declName_711_, v___x_717_, v___y_713_, v___y_715_);
return v___x_718_;
}
}
LEAN_EXPORT void l_Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_711_ = stack[0].m_obj;
lean_object* v___y_712_ = stack[1].m_obj;
lean_object* v___y_713_ = stack[2].m_obj;
lean_object* v___y_714_ = stack[3].m_obj;
lean_object* v___y_715_ = stack[4].m_obj;
lean_object* v_res_719_;
v_res_719_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16(v_declName_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_);
stack->m_obj
 = v_res_719_;
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16___boxed(lean_object* v_declName_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_){
_start:
{
lean_object* v_res_726_; 
v_res_726_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16(v_declName_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_);
lean_dec(v___y_724_);
lean_dec_ref(v___y_723_);
lean_dec(v___y_722_);
lean_dec_ref(v___y_721_);
return v_res_726_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg(lean_object* v_preDefs_730_, lean_object* v_xs_731_, uint8_t v_a_732_, lean_object* v___x_733_, size_t v_sz_734_, size_t v_i_735_, lean_object* v_bs_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_){
_start:
{
uint8_t v___x_742_; 
v___x_742_ = lean_usize_dec_lt(v_i_735_, v_sz_734_);
if (v___x_742_ == 0)
{
lean_object* v___x_743_; 
lean_dec(v___x_733_);
v___x_743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_743_, 0, v_bs_736_);
return v___x_743_;
}
else
{
lean_object* v___x_744_; lean_object* v_v_745_; lean_object* v___x_746_; lean_object* v_bs_x27_747_; lean_object* v_a_749_; lean_object* v___y_755_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v_levelParams_767_; lean_object* v_modifiers_768_; lean_object* v_declName_769_; lean_object* v___x_770_; lean_object* v___x_771_; uint8_t v___x_772_; lean_object* v___x_773_; 
v___x_744_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v_v_745_ = lean_array_uget(v_bs_736_, v_i_735_);
v___x_746_ = lean_unsigned_to_nat(0u);
v_bs_x27_747_ = lean_array_uset(v_bs_736_, v_i_735_, v___x_746_);
v___x_765_ = lean_usize_to_nat(v_i_735_);
v___x_766_ = lean_array_get_borrowed(v___x_744_, v_preDefs_730_, v___x_765_);
lean_dec(v___x_765_);
v_levelParams_767_ = lean_ctor_get(v___x_766_, 1);
v_modifiers_768_ = lean_ctor_get(v___x_766_, 2);
v_declName_769_ = lean_ctor_get(v___x_766_, 3);
v___x_770_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg___closed__1));
lean_inc(v_declName_769_);
v___x_771_ = l_Lean_Name_append(v_declName_769_, v___x_770_);
v___x_772_ = 1;
v___x_773_ = l_Lean_Meta_mkLambdaFVars(v_xs_731_, v_v_745_, v_a_732_, v___x_742_, v_a_732_, v___x_742_, v___x_772_, v___y_737_, v___y_738_, v___y_739_, v___y_740_);
if (lean_obj_tag(v___x_773_) == 0)
{
lean_object* v_a_774_; lean_object* v___x_775_; 
v_a_774_ = lean_ctor_get(v___x_773_, 0);
lean_inc(v_a_774_);
lean_dec_ref_known(v___x_773_, 1);
v___x_775_ = l_Lean_Elab_eraseRecAppSyntaxExpr(v_a_774_, v___y_739_, v___y_740_);
if (lean_obj_tag(v___x_775_) == 0)
{
lean_object* v_a_776_; lean_object* v___x_777_; 
v_a_776_ = lean_ctor_get(v___x_775_, 0);
lean_inc_n(v_a_776_, 2);
lean_dec_ref_known(v___x_775_, 1);
lean_inc(v___y_740_);
lean_inc_ref(v___y_739_);
lean_inc(v___y_738_);
lean_inc_ref(v___y_737_);
v___x_777_ = lean_infer_type(v_a_776_, v___y_737_, v___y_738_, v___y_739_, v___y_740_);
if (lean_obj_tag(v___x_777_) == 0)
{
lean_object* v_a_778_; lean_object* v___x_779_; 
v_a_778_ = lean_ctor_get(v___x_777_, 0);
lean_inc(v_a_778_);
lean_dec_ref_known(v___x_777_, 1);
v___x_779_ = l_Lean_Meta_letToHave(v_a_778_, v___y_737_, v___y_738_, v___y_739_, v___y_740_);
if (lean_obj_tag(v___x_779_) == 0)
{
lean_object* v_a_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_856_; 
v_a_780_ = lean_ctor_get(v___x_779_, 0);
v_isSharedCheck_856_ = !lean_is_exclusive(v___x_779_);
if (v_isSharedCheck_856_ == 0)
{
v___x_782_ = v___x_779_;
v_isShared_783_ = v_isSharedCheck_856_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_a_780_);
lean_dec(v___x_779_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_856_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___x_784_; lean_object* v_env_785_; uint8_t v_isUnsafe_786_; uint32_t v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; uint8_t v___y_791_; 
v___x_784_ = lean_st_ref_get(v___y_740_);
v_env_785_ = lean_ctor_get(v___x_784_, 0);
lean_inc_ref(v_env_785_);
lean_dec(v___x_784_);
v_isUnsafe_786_ = lean_ctor_get_uint8(v_modifiers_768_, sizeof(void*)*3 + 4);
lean_inc(v_a_776_);
v___x_787_ = l_Lean_getMaxHeight(v_env_785_, v_a_776_);
lean_inc(v_levelParams_767_);
lean_inc(v___x_771_);
v___x_788_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_788_, 0, v___x_771_);
lean_ctor_set(v___x_788_, 1, v_levelParams_767_);
lean_ctor_set(v___x_788_, 2, v_a_780_);
v___x_789_ = lean_box(1);
if (v_isUnsafe_786_ == 0)
{
uint8_t v___x_854_; 
v___x_854_ = 1;
v___y_791_ = v___x_854_;
goto v___jp_790_;
}
else
{
uint8_t v___x_855_; 
v___x_855_ = 0;
v___y_791_ = v___x_855_;
goto v___jp_790_;
}
v___jp_790_:
{
lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_796_; 
v___x_792_ = lean_box(0);
lean_inc(v___x_771_);
v___x_793_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_793_, 0, v___x_771_);
lean_ctor_set(v___x_793_, 1, v___x_792_);
v___x_794_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_794_, 0, v___x_788_);
lean_ctor_set(v___x_794_, 1, v_a_776_);
lean_ctor_set(v___x_794_, 2, v___x_789_);
lean_ctor_set(v___x_794_, 3, v___x_793_);
lean_ctor_set_uint8(v___x_794_, sizeof(void*)*4, v___y_791_);
if (v_isShared_783_ == 0)
{
lean_ctor_set_tag(v___x_782_, 1);
lean_ctor_set(v___x_782_, 0, v___x_794_);
v___x_796_ = v___x_782_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v___x_794_);
v___x_796_ = v_reuseFailAlloc_853_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
lean_object* v___x_797_; 
v___x_797_ = l_Lean_addDecl(v___x_796_, v_a_732_, v___y_739_, v___y_740_);
if (lean_obj_tag(v___x_797_) == 0)
{
lean_object* v___x_798_; lean_object* v_env_799_; lean_object* v_nextMacroScope_800_; lean_object* v_ngen_801_; lean_object* v_auxDeclNGen_802_; lean_object* v_traceState_803_; lean_object* v_recordedDeps_804_; lean_object* v_messages_805_; lean_object* v_infoState_806_; lean_object* v_snapshotTasks_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_843_; 
lean_dec_ref_known(v___x_797_, 1);
v___x_798_ = lean_st_ref_take(v___y_740_);
v_env_799_ = lean_ctor_get(v___x_798_, 0);
v_nextMacroScope_800_ = lean_ctor_get(v___x_798_, 1);
v_ngen_801_ = lean_ctor_get(v___x_798_, 2);
v_auxDeclNGen_802_ = lean_ctor_get(v___x_798_, 3);
v_traceState_803_ = lean_ctor_get(v___x_798_, 4);
v_recordedDeps_804_ = lean_ctor_get(v___x_798_, 6);
v_messages_805_ = lean_ctor_get(v___x_798_, 7);
v_infoState_806_ = lean_ctor_get(v___x_798_, 8);
v_snapshotTasks_807_ = lean_ctor_get(v___x_798_, 9);
v_isSharedCheck_843_ = !lean_is_exclusive(v___x_798_);
if (v_isSharedCheck_843_ == 0)
{
lean_object* v_unused_844_; 
v_unused_844_ = lean_ctor_get(v___x_798_, 5);
lean_dec(v_unused_844_);
v___x_809_ = v___x_798_;
v_isShared_810_ = v_isSharedCheck_843_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_snapshotTasks_807_);
lean_inc(v_infoState_806_);
lean_inc(v_messages_805_);
lean_inc(v_recordedDeps_804_);
lean_inc(v_traceState_803_);
lean_inc(v_auxDeclNGen_802_);
lean_inc(v_ngen_801_);
lean_inc(v_nextMacroScope_800_);
lean_inc(v_env_799_);
lean_dec(v___x_798_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_843_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_814_; 
lean_inc(v___x_771_);
v___x_811_ = l_Lean_setDefHeightOverride(v_env_799_, v___x_771_, v___x_787_);
v___x_812_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__2);
if (v_isShared_810_ == 0)
{
lean_ctor_set(v___x_809_, 5, v___x_812_);
lean_ctor_set(v___x_809_, 0, v___x_811_);
v___x_814_ = v___x_809_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v___x_811_);
lean_ctor_set(v_reuseFailAlloc_842_, 1, v_nextMacroScope_800_);
lean_ctor_set(v_reuseFailAlloc_842_, 2, v_ngen_801_);
lean_ctor_set(v_reuseFailAlloc_842_, 3, v_auxDeclNGen_802_);
lean_ctor_set(v_reuseFailAlloc_842_, 4, v_traceState_803_);
lean_ctor_set(v_reuseFailAlloc_842_, 5, v___x_812_);
lean_ctor_set(v_reuseFailAlloc_842_, 6, v_recordedDeps_804_);
lean_ctor_set(v_reuseFailAlloc_842_, 7, v_messages_805_);
lean_ctor_set(v_reuseFailAlloc_842_, 8, v_infoState_806_);
lean_ctor_set(v_reuseFailAlloc_842_, 9, v_snapshotTasks_807_);
v___x_814_ = v_reuseFailAlloc_842_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v_mctx_817_; lean_object* v_zetaDeltaFVarIds_818_; lean_object* v_postponed_819_; lean_object* v_diag_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_840_; 
v___x_815_ = lean_st_ref_put(v___y_740_, v___x_814_);
v___x_816_ = lean_st_ref_take(v___y_738_);
v_mctx_817_ = lean_ctor_get(v___x_816_, 0);
v_zetaDeltaFVarIds_818_ = lean_ctor_get(v___x_816_, 2);
v_postponed_819_ = lean_ctor_get(v___x_816_, 3);
v_diag_820_ = lean_ctor_get(v___x_816_, 4);
v_isSharedCheck_840_ = !lean_is_exclusive(v___x_816_);
if (v_isSharedCheck_840_ == 0)
{
lean_object* v_unused_841_; 
v_unused_841_ = lean_ctor_get(v___x_816_, 1);
lean_dec(v_unused_841_);
v___x_822_ = v___x_816_;
v_isShared_823_ = v_isSharedCheck_840_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_diag_820_);
lean_inc(v_postponed_819_);
lean_inc(v_zetaDeltaFVarIds_818_);
lean_inc(v_mctx_817_);
lean_dec(v___x_816_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_840_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v___x_824_; lean_object* v___x_826_; 
v___x_824_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__3, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__3);
if (v_isShared_823_ == 0)
{
lean_ctor_set(v___x_822_, 1, v___x_824_);
v___x_826_ = v___x_822_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v_mctx_817_);
lean_ctor_set(v_reuseFailAlloc_839_, 1, v___x_824_);
lean_ctor_set(v_reuseFailAlloc_839_, 2, v_zetaDeltaFVarIds_818_);
lean_ctor_set(v_reuseFailAlloc_839_, 3, v_postponed_819_);
lean_ctor_set(v_reuseFailAlloc_839_, 4, v_diag_820_);
v___x_826_ = v_reuseFailAlloc_839_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_827_ = lean_st_ref_put(v___y_738_, v___x_826_);
lean_inc(v___x_771_);
v___x_828_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16(v___x_771_, v___y_737_, v___y_738_, v___y_739_, v___y_740_);
if (lean_obj_tag(v___x_828_) == 0)
{
lean_object* v___x_829_; lean_object* v___x_830_; 
lean_dec_ref_known(v___x_828_, 1);
lean_inc(v___x_733_);
v___x_829_ = l_Lean_mkConst(v___x_771_, v___x_733_);
v___x_830_ = l_Lean_mkAppN(v___x_829_, v_xs_731_);
v_a_749_ = v___x_830_;
goto v___jp_748_;
}
else
{
lean_object* v_a_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_838_; 
lean_dec(v___x_771_);
lean_dec_ref(v_bs_x27_747_);
lean_dec(v___x_733_);
v_a_831_ = lean_ctor_get(v___x_828_, 0);
v_isSharedCheck_838_ = !lean_is_exclusive(v___x_828_);
if (v_isSharedCheck_838_ == 0)
{
v___x_833_ = v___x_828_;
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_a_831_);
lean_dec(v___x_828_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v___x_836_; 
if (v_isShared_834_ == 0)
{
v___x_836_ = v___x_833_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_a_831_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
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
lean_object* v_a_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_852_; 
lean_dec(v___x_771_);
lean_dec_ref(v_bs_x27_747_);
lean_dec(v___x_733_);
v_a_845_ = lean_ctor_get(v___x_797_, 0);
v_isSharedCheck_852_ = !lean_is_exclusive(v___x_797_);
if (v_isSharedCheck_852_ == 0)
{
v___x_847_ = v___x_797_;
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_a_845_);
lean_dec(v___x_797_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v___x_850_; 
if (v_isShared_848_ == 0)
{
v___x_850_ = v___x_847_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v_a_845_);
v___x_850_ = v_reuseFailAlloc_851_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
return v___x_850_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_776_);
lean_dec(v___x_771_);
v___y_755_ = v___x_779_;
goto v___jp_754_;
}
}
else
{
lean_dec(v_a_776_);
lean_dec(v___x_771_);
v___y_755_ = v___x_777_;
goto v___jp_754_;
}
}
else
{
lean_dec(v___x_771_);
v___y_755_ = v___x_775_;
goto v___jp_754_;
}
}
else
{
lean_dec(v___x_771_);
v___y_755_ = v___x_773_;
goto v___jp_754_;
}
v___jp_748_:
{
size_t v___x_750_; size_t v___x_751_; lean_object* v___x_752_; 
v___x_750_ = ((size_t)1ULL);
v___x_751_ = lean_usize_add(v_i_735_, v___x_750_);
v___x_752_ = lean_array_uset(v_bs_x27_747_, v_i_735_, v_a_749_);
v_i_735_ = v___x_751_;
v_bs_736_ = v___x_752_;
goto _start;
}
v___jp_754_:
{
if (lean_obj_tag(v___y_755_) == 0)
{
lean_object* v_a_756_; 
v_a_756_ = lean_ctor_get(v___y_755_, 0);
lean_inc(v_a_756_);
lean_dec_ref_known(v___y_755_, 1);
v_a_749_ = v_a_756_;
goto v___jp_748_;
}
else
{
lean_object* v_a_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_764_; 
lean_dec_ref(v_bs_x27_747_);
lean_dec(v___x_733_);
v_a_757_ = lean_ctor_get(v___y_755_, 0);
v_isSharedCheck_764_ = !lean_is_exclusive(v___y_755_);
if (v_isSharedCheck_764_ == 0)
{
v___x_759_ = v___y_755_;
v_isShared_760_ = v_isSharedCheck_764_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_a_757_);
lean_dec(v___y_755_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_764_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v___x_762_; 
if (v_isShared_760_ == 0)
{
v___x_762_ = v___x_759_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v_a_757_);
v___x_762_ = v_reuseFailAlloc_763_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
return v___x_762_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_preDefs_730_ = stack[0].m_obj;
lean_object* v_xs_731_ = stack[1].m_obj;
uint8_t v_a_732_ = stack[2].m_num;
lean_object* v___x_733_ = stack[3].m_obj;
size_t v_sz_734_ = stack[4].m_num;
size_t v_i_735_ = stack[5].m_num;
lean_object* v_bs_736_ = stack[6].m_obj;
lean_object* v___y_737_ = stack[7].m_obj;
lean_object* v___y_738_ = stack[8].m_obj;
lean_object* v___y_739_ = stack[9].m_obj;
lean_object* v___y_740_ = stack[10].m_obj;
lean_object* v_res_857_;
v_res_857_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg(v_preDefs_730_, v_xs_731_, v_a_732_, v___x_733_, v_sz_734_, v_i_735_, v_bs_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_);
stack->m_obj
 = v_res_857_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg___boxed(lean_object* v_preDefs_858_, lean_object* v_xs_859_, lean_object* v_a_860_, lean_object* v___x_861_, lean_object* v_sz_862_, lean_object* v_i_863_, lean_object* v_bs_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_){
_start:
{
uint8_t v_a_26234__boxed_870_; size_t v_sz_boxed_871_; size_t v_i_boxed_872_; lean_object* v_res_873_; 
v_a_26234__boxed_870_ = lean_unbox(v_a_860_);
v_sz_boxed_871_ = lean_unbox_usize(v_sz_862_);
lean_dec(v_sz_862_);
v_i_boxed_872_ = lean_unbox_usize(v_i_863_);
lean_dec(v_i_863_);
v_res_873_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg(v_preDefs_858_, v_xs_859_, v_a_26234__boxed_870_, v___x_861_, v_sz_boxed_871_, v_i_boxed_872_, v_bs_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_);
lean_dec(v___y_868_);
lean_dec_ref(v___y_867_);
lean_dec(v___y_866_);
lean_dec_ref(v___y_865_);
lean_dec_ref(v_xs_859_);
lean_dec_ref(v_preDefs_858_);
return v_res_873_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___lam__0(lean_object* v_fixedParamPerms_874_, lean_object* v___x_875_, lean_object* v___x_876_, lean_object* v_xs_877_, lean_object* v_snd_878_, uint8_t v___x_879_, lean_object* v_ys_880_, lean_object* v_x_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_){
_start:
{
lean_object* v_perms_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; uint8_t v___x_891_; uint8_t v___x_892_; lean_object* v___x_893_; 
v_perms_887_ = lean_ctor_get(v_fixedParamPerms_874_, 1);
v___x_888_ = lean_array_get_borrowed(v___x_875_, v_perms_887_, v___x_876_);
lean_inc_ref(v_ys_880_);
lean_inc(v___x_888_);
v___x_889_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v___x_888_, v_xs_877_, v_ys_880_);
v___x_890_ = l_Lean_Expr_beta(v_snd_878_, v_ys_880_);
v___x_891_ = 0;
v___x_892_ = 1;
v___x_893_ = l_Lean_Meta_mkLambdaFVars(v___x_889_, v___x_890_, v___x_891_, v___x_879_, v___x_891_, v___x_879_, v___x_892_, v___y_882_, v___y_883_, v___y_884_, v___y_885_);
lean_dec_ref(v___x_889_);
return v___x_893_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fixedParamPerms_874_ = stack[0].m_obj;
lean_object* v___x_875_ = stack[1].m_obj;
lean_object* v___x_876_ = stack[2].m_obj;
lean_object* v_xs_877_ = stack[3].m_obj;
lean_object* v_snd_878_ = stack[4].m_obj;
uint8_t v___x_879_ = stack[5].m_num;
lean_object* v_ys_880_ = stack[6].m_obj;
lean_object* v_x_881_ = stack[7].m_obj;
lean_object* v___y_882_ = stack[8].m_obj;
lean_object* v___y_883_ = stack[9].m_obj;
lean_object* v___y_884_ = stack[10].m_obj;
lean_object* v___y_885_ = stack[11].m_obj;
lean_object* v_res_894_;
v_res_894_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___lam__0(v_fixedParamPerms_874_, v___x_875_, v___x_876_, v_xs_877_, v_snd_878_, v___x_879_, v_ys_880_, v_x_881_, v___y_882_, v___y_883_, v___y_884_, v___y_885_);
stack->m_obj
 = v_res_894_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___lam__0___boxed(lean_object* v_fixedParamPerms_895_, lean_object* v___x_896_, lean_object* v___x_897_, lean_object* v_xs_898_, lean_object* v_snd_899_, lean_object* v___x_900_, lean_object* v_ys_901_, lean_object* v_x_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_){
_start:
{
uint8_t v___x_26569__boxed_908_; lean_object* v_res_909_; 
v___x_26569__boxed_908_ = lean_unbox(v___x_900_);
v_res_909_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___lam__0(v_fixedParamPerms_895_, v___x_896_, v___x_897_, v_xs_898_, v_snd_899_, v___x_26569__boxed_908_, v_ys_901_, v_x_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_);
lean_dec(v___y_906_);
lean_dec_ref(v___y_905_);
lean_dec(v___y_904_);
lean_dec_ref(v___y_903_);
lean_dec_ref(v_x_902_);
lean_dec_ref(v_xs_898_);
lean_dec(v___x_897_);
lean_dec_ref(v___x_896_);
lean_dec_ref(v_fixedParamPerms_895_);
return v_res_909_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_910_; 
v___x_910_ = l_Array_instInhabited___redArg();
return v___x_910_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg(lean_object* v_fixedParamPerms_911_, lean_object* v_xs_912_, size_t v_sz_913_, size_t v_i_914_, lean_object* v_bs_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_){
_start:
{
uint8_t v___x_921_; 
v___x_921_ = lean_usize_dec_lt(v_i_914_, v_sz_913_);
if (v___x_921_ == 0)
{
lean_object* v___x_922_; 
lean_dec_ref(v_xs_912_);
lean_dec_ref(v_fixedParamPerms_911_);
v___x_922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_922_, 0, v_bs_915_);
return v___x_922_;
}
else
{
lean_object* v_v_923_; lean_object* v_fst_924_; lean_object* v_snd_925_; lean_object* v___x_926_; lean_object* v_bs_x27_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___f_931_; uint8_t v___x_932_; lean_object* v___x_933_; 
v_v_923_ = lean_array_uget_borrowed(v_bs_915_, v_i_914_);
v_fst_924_ = lean_ctor_get(v_v_923_, 0);
lean_inc(v_fst_924_);
v_snd_925_ = lean_ctor_get(v_v_923_, 1);
lean_inc(v_snd_925_);
v___x_926_ = lean_unsigned_to_nat(0u);
v_bs_x27_927_ = lean_array_uset(v_bs_915_, v_i_914_, v___x_926_);
v___x_928_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0);
v___x_929_ = lean_usize_to_nat(v_i_914_);
v___x_930_ = lean_box(v___x_921_);
lean_inc_ref(v_xs_912_);
lean_inc_ref(v_fixedParamPerms_911_);
v___f_931_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___lam__0___boxed), 13, 6);
lean_closure_set(v___f_931_, 0, v_fixedParamPerms_911_);
lean_closure_set(v___f_931_, 1, v___x_928_);
lean_closure_set(v___f_931_, 2, v___x_929_);
lean_closure_set(v___f_931_, 3, v_xs_912_);
lean_closure_set(v___f_931_, 4, v_snd_925_);
lean_closure_set(v___f_931_, 5, v___x_930_);
v___x_932_ = 0;
v___x_933_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg(v_fst_924_, v___f_931_, v___x_932_, v___y_916_, v___y_917_, v___y_918_, v___y_919_);
if (lean_obj_tag(v___x_933_) == 0)
{
lean_object* v_a_934_; size_t v___x_935_; size_t v___x_936_; lean_object* v___x_937_; 
v_a_934_ = lean_ctor_get(v___x_933_, 0);
lean_inc(v_a_934_);
lean_dec_ref_known(v___x_933_, 1);
v___x_935_ = ((size_t)1ULL);
v___x_936_ = lean_usize_add(v_i_914_, v___x_935_);
v___x_937_ = lean_array_uset(v_bs_x27_927_, v_i_914_, v_a_934_);
v_i_914_ = v___x_936_;
v_bs_915_ = v___x_937_;
goto _start;
}
else
{
lean_object* v_a_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_946_; 
lean_dec_ref(v_bs_x27_927_);
lean_dec_ref(v_xs_912_);
lean_dec_ref(v_fixedParamPerms_911_);
v_a_939_ = lean_ctor_get(v___x_933_, 0);
v_isSharedCheck_946_ = !lean_is_exclusive(v___x_933_);
if (v_isSharedCheck_946_ == 0)
{
v___x_941_ = v___x_933_;
v_isShared_942_ = v_isSharedCheck_946_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_a_939_);
lean_dec(v___x_933_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_946_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v___x_944_; 
if (v_isShared_942_ == 0)
{
v___x_944_ = v___x_941_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v_a_939_);
v___x_944_ = v_reuseFailAlloc_945_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
return v___x_944_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_fixedParamPerms_911_ = stack[0].m_obj;
lean_object* v_xs_912_ = stack[1].m_obj;
size_t v_sz_913_ = stack[2].m_num;
size_t v_i_914_ = stack[3].m_num;
lean_object* v_bs_915_ = stack[4].m_obj;
lean_object* v___y_916_ = stack[5].m_obj;
lean_object* v___y_917_ = stack[6].m_obj;
lean_object* v___y_918_ = stack[7].m_obj;
lean_object* v___y_919_ = stack[8].m_obj;
lean_object* v_res_947_;
v_res_947_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg(v_fixedParamPerms_911_, v_xs_912_, v_sz_913_, v_i_914_, v_bs_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_);
stack->m_obj
 = v_res_947_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___boxed(lean_object* v_fixedParamPerms_948_, lean_object* v_xs_949_, lean_object* v_sz_950_, lean_object* v_i_951_, lean_object* v_bs_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_){
_start:
{
size_t v_sz_boxed_958_; size_t v_i_boxed_959_; lean_object* v_res_960_; 
v_sz_boxed_958_ = lean_unbox_usize(v_sz_950_);
lean_dec(v_sz_950_);
v_i_boxed_959_ = lean_unbox_usize(v_i_951_);
lean_dec(v_i_951_);
v_res_960_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg(v_fixedParamPerms_948_, v_xs_949_, v_sz_boxed_958_, v_i_boxed_959_, v_bs_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
lean_dec(v___y_954_);
lean_dec_ref(v___y_953_);
return v_res_960_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(lean_object* v_a_961_, lean_object* v_a_962_){
_start:
{
if (lean_obj_tag(v_a_961_) == 0)
{
lean_object* v___x_963_; 
v___x_963_ = l_List_reverse___redArg(v_a_962_);
return v___x_963_;
}
else
{
lean_object* v_head_964_; lean_object* v_tail_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_974_; 
v_head_964_ = lean_ctor_get(v_a_961_, 0);
v_tail_965_ = lean_ctor_get(v_a_961_, 1);
v_isSharedCheck_974_ = !lean_is_exclusive(v_a_961_);
if (v_isSharedCheck_974_ == 0)
{
v___x_967_ = v_a_961_;
v_isShared_968_ = v_isSharedCheck_974_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_tail_965_);
lean_inc(v_head_964_);
lean_dec(v_a_961_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_974_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
lean_object* v___x_969_; lean_object* v___x_971_; 
v___x_969_ = l_Lean_MessageData_ofExpr(v_head_964_);
if (v_isShared_968_ == 0)
{
lean_ctor_set(v___x_967_, 1, v_a_962_);
lean_ctor_set(v___x_967_, 0, v___x_969_);
v___x_971_ = v___x_967_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v___x_969_);
lean_ctor_set(v_reuseFailAlloc_973_, 1, v_a_962_);
v___x_971_ = v_reuseFailAlloc_973_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
v_a_961_ = v_tail_965_;
v_a_962_ = v___x_971_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__15(lean_object* v_a_975_, lean_object* v_a_976_){
_start:
{
if (lean_obj_tag(v_a_975_) == 0)
{
lean_object* v___x_977_; 
v___x_977_ = l_List_reverse___redArg(v_a_976_);
return v___x_977_;
}
else
{
lean_object* v_head_978_; lean_object* v_tail_979_; lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_988_; 
v_head_978_ = lean_ctor_get(v_a_975_, 0);
v_tail_979_ = lean_ctor_get(v_a_975_, 1);
v_isSharedCheck_988_ = !lean_is_exclusive(v_a_975_);
if (v_isSharedCheck_988_ == 0)
{
v___x_981_ = v_a_975_;
v_isShared_982_ = v_isSharedCheck_988_;
goto v_resetjp_980_;
}
else
{
lean_inc(v_tail_979_);
lean_inc(v_head_978_);
lean_dec(v_a_975_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_988_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
lean_object* v___x_983_; lean_object* v___x_985_; 
v___x_983_ = l_Lean_mkLevelParam(v_head_978_);
if (v_isShared_982_ == 0)
{
lean_ctor_set(v___x_981_, 1, v_a_976_);
lean_ctor_set(v___x_981_, 0, v___x_983_);
v___x_985_ = v___x_981_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v___x_983_);
lean_ctor_set(v_reuseFailAlloc_987_, 1, v_a_976_);
v___x_985_ = v_reuseFailAlloc_987_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
v_a_975_ = v_tail_979_;
v_a_976_ = v___x_985_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__0(void){
_start:
{
lean_object* v___x_989_; 
v___x_989_ = l_instMonadEIO___redArg();
return v___x_989_;
}
}
lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg(lean_object* v_msg_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_){
_start:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v_toApplicative_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1063_; 
v___x_1000_ = lean_obj_once(&l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__0, &l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__0_once, _init_l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__0);
v___x_1001_ = l_StateRefT_x27_instMonad___redArg(v___x_1000_);
v_toApplicative_1002_ = lean_ctor_get(v___x_1001_, 0);
v_isSharedCheck_1063_ = !lean_is_exclusive(v___x_1001_);
if (v_isSharedCheck_1063_ == 0)
{
lean_object* v_unused_1064_; 
v_unused_1064_ = lean_ctor_get(v___x_1001_, 1);
lean_dec(v_unused_1064_);
v___x_1004_ = v___x_1001_;
v_isShared_1005_ = v_isSharedCheck_1063_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_toApplicative_1002_);
lean_dec(v___x_1001_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1063_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v_toFunctor_1006_; lean_object* v_toSeq_1007_; lean_object* v_toSeqLeft_1008_; lean_object* v_toSeqRight_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1061_; 
v_toFunctor_1006_ = lean_ctor_get(v_toApplicative_1002_, 0);
v_toSeq_1007_ = lean_ctor_get(v_toApplicative_1002_, 2);
v_toSeqLeft_1008_ = lean_ctor_get(v_toApplicative_1002_, 3);
v_toSeqRight_1009_ = lean_ctor_get(v_toApplicative_1002_, 4);
v_isSharedCheck_1061_ = !lean_is_exclusive(v_toApplicative_1002_);
if (v_isSharedCheck_1061_ == 0)
{
lean_object* v_unused_1062_; 
v_unused_1062_ = lean_ctor_get(v_toApplicative_1002_, 1);
lean_dec(v_unused_1062_);
v___x_1011_ = v_toApplicative_1002_;
v_isShared_1012_ = v_isSharedCheck_1061_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_toSeqRight_1009_);
lean_inc(v_toSeqLeft_1008_);
lean_inc(v_toSeq_1007_);
lean_inc(v_toFunctor_1006_);
lean_dec(v_toApplicative_1002_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1061_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v___f_1013_; lean_object* v___f_1014_; lean_object* v___f_1015_; lean_object* v___f_1016_; lean_object* v___x_1017_; lean_object* v___f_1018_; lean_object* v___f_1019_; lean_object* v___f_1020_; lean_object* v___x_1022_; 
v___f_1013_ = ((lean_object*)(l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__1));
v___f_1014_ = ((lean_object*)(l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__2));
lean_inc_ref(v_toFunctor_1006_);
v___f_1015_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1015_, 0, v_toFunctor_1006_);
v___f_1016_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1016_, 0, v_toFunctor_1006_);
v___x_1017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1017_, 0, v___f_1015_);
lean_ctor_set(v___x_1017_, 1, v___f_1016_);
v___f_1018_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1018_, 0, v_toSeqRight_1009_);
v___f_1019_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1019_, 0, v_toSeqLeft_1008_);
v___f_1020_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1020_, 0, v_toSeq_1007_);
if (v_isShared_1012_ == 0)
{
lean_ctor_set(v___x_1011_, 4, v___f_1018_);
lean_ctor_set(v___x_1011_, 3, v___f_1019_);
lean_ctor_set(v___x_1011_, 2, v___f_1020_);
lean_ctor_set(v___x_1011_, 1, v___f_1013_);
lean_ctor_set(v___x_1011_, 0, v___x_1017_);
v___x_1022_ = v___x_1011_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v___x_1017_);
lean_ctor_set(v_reuseFailAlloc_1060_, 1, v___f_1013_);
lean_ctor_set(v_reuseFailAlloc_1060_, 2, v___f_1020_);
lean_ctor_set(v_reuseFailAlloc_1060_, 3, v___f_1019_);
lean_ctor_set(v_reuseFailAlloc_1060_, 4, v___f_1018_);
v___x_1022_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
lean_object* v___x_1024_; 
if (v_isShared_1005_ == 0)
{
lean_ctor_set(v___x_1004_, 1, v___f_1014_);
lean_ctor_set(v___x_1004_, 0, v___x_1022_);
v___x_1024_ = v___x_1004_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v___x_1022_);
lean_ctor_set(v_reuseFailAlloc_1059_, 1, v___f_1014_);
v___x_1024_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
lean_object* v___x_1025_; lean_object* v_toApplicative_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1057_; 
v___x_1025_ = l_StateRefT_x27_instMonad___redArg(v___x_1024_);
v_toApplicative_1026_ = lean_ctor_get(v___x_1025_, 0);
v_isSharedCheck_1057_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1057_ == 0)
{
lean_object* v_unused_1058_; 
v_unused_1058_ = lean_ctor_get(v___x_1025_, 1);
lean_dec(v_unused_1058_);
v___x_1028_ = v___x_1025_;
v_isShared_1029_ = v_isSharedCheck_1057_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_toApplicative_1026_);
lean_dec(v___x_1025_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1057_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v_toFunctor_1030_; lean_object* v_toSeq_1031_; lean_object* v_toSeqLeft_1032_; lean_object* v_toSeqRight_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1055_; 
v_toFunctor_1030_ = lean_ctor_get(v_toApplicative_1026_, 0);
v_toSeq_1031_ = lean_ctor_get(v_toApplicative_1026_, 2);
v_toSeqLeft_1032_ = lean_ctor_get(v_toApplicative_1026_, 3);
v_toSeqRight_1033_ = lean_ctor_get(v_toApplicative_1026_, 4);
v_isSharedCheck_1055_ = !lean_is_exclusive(v_toApplicative_1026_);
if (v_isSharedCheck_1055_ == 0)
{
lean_object* v_unused_1056_; 
v_unused_1056_ = lean_ctor_get(v_toApplicative_1026_, 1);
lean_dec(v_unused_1056_);
v___x_1035_ = v_toApplicative_1026_;
v_isShared_1036_ = v_isSharedCheck_1055_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_toSeqRight_1033_);
lean_inc(v_toSeqLeft_1032_);
lean_inc(v_toSeq_1031_);
lean_inc(v_toFunctor_1030_);
lean_dec(v_toApplicative_1026_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1055_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
lean_object* v___f_1037_; lean_object* v___f_1038_; lean_object* v___f_1039_; lean_object* v___f_1040_; lean_object* v___x_1041_; lean_object* v___f_1042_; lean_object* v___f_1043_; lean_object* v___f_1044_; lean_object* v___x_1046_; 
v___f_1037_ = ((lean_object*)(l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__3));
v___f_1038_ = ((lean_object*)(l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__4));
lean_inc_ref(v_toFunctor_1030_);
v___f_1039_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1039_, 0, v_toFunctor_1030_);
v___f_1040_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1040_, 0, v_toFunctor_1030_);
v___x_1041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1041_, 0, v___f_1039_);
lean_ctor_set(v___x_1041_, 1, v___f_1040_);
v___f_1042_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1042_, 0, v_toSeqRight_1033_);
v___f_1043_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1043_, 0, v_toSeqLeft_1032_);
v___f_1044_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1044_, 0, v_toSeq_1031_);
if (v_isShared_1036_ == 0)
{
lean_ctor_set(v___x_1035_, 4, v___f_1042_);
lean_ctor_set(v___x_1035_, 3, v___f_1043_);
lean_ctor_set(v___x_1035_, 2, v___f_1044_);
lean_ctor_set(v___x_1035_, 1, v___f_1037_);
lean_ctor_set(v___x_1035_, 0, v___x_1041_);
v___x_1046_ = v___x_1035_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v___x_1041_);
lean_ctor_set(v_reuseFailAlloc_1054_, 1, v___f_1037_);
lean_ctor_set(v_reuseFailAlloc_1054_, 2, v___f_1044_);
lean_ctor_set(v_reuseFailAlloc_1054_, 3, v___f_1043_);
lean_ctor_set(v_reuseFailAlloc_1054_, 4, v___f_1042_);
v___x_1046_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
lean_object* v___x_1048_; 
if (v_isShared_1029_ == 0)
{
lean_ctor_set(v___x_1028_, 1, v___f_1038_);
lean_ctor_set(v___x_1028_, 0, v___x_1046_);
v___x_1048_ = v___x_1028_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v___x_1046_);
lean_ctor_set(v_reuseFailAlloc_1053_, 1, v___f_1038_);
v___x_1048_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_21563__overap_1051_; lean_object* v___x_1052_; 
v___x_1049_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0);
v___x_1050_ = l_instInhabitedOfMonad___redArg(v___x_1048_, v___x_1049_);
v___x_21563__overap_1051_ = lean_panic_fn_borrowed(v___x_1050_, v_msg_994_);
lean_dec(v___x_1050_);
lean_inc(v___y_998_);
lean_inc_ref(v___y_997_);
lean_inc(v___y_996_);
lean_inc_ref(v___y_995_);
v___x_1052_ = lean_apply_5(v___x_21563__overap_1051_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, lean_box(0));
return v___x_1052_;
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
LEAN_EXPORT void l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_994_ = stack[0].m_obj;
lean_object* v___y_995_ = stack[1].m_obj;
lean_object* v___y_996_ = stack[2].m_obj;
lean_object* v___y_997_ = stack[3].m_obj;
lean_object* v___y_998_ = stack[4].m_obj;
lean_object* v_res_1065_;
v_res_1065_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg(v_msg_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_);
stack->m_obj
 = v_res_1065_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___boxed(lean_object* v_msg_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_){
_start:
{
lean_object* v_res_1072_; 
v_res_1072_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg(v_msg_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_);
lean_dec(v___y_1070_);
lean_dec_ref(v___y_1069_);
lean_dec(v___y_1068_);
lean_dec_ref(v___y_1067_);
return v_res_1072_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__13(lean_object* v_xs_1073_, size_t v_sz_1074_, size_t v_i_1075_, lean_object* v_bs_1076_){
_start:
{
uint8_t v___x_1077_; 
v___x_1077_ = lean_usize_dec_lt(v_i_1075_, v_sz_1074_);
if (v___x_1077_ == 0)
{
return v_bs_1076_;
}
else
{
lean_object* v___x_1078_; lean_object* v_v_1079_; lean_object* v___x_1080_; lean_object* v_bs_x27_1081_; lean_object* v___x_1082_; size_t v___x_1083_; size_t v___x_1084_; lean_object* v___x_1085_; 
v___x_1078_ = l_Lean_instInhabitedExpr;
v_v_1079_ = lean_array_uget(v_bs_1076_, v_i_1075_);
v___x_1080_ = lean_unsigned_to_nat(0u);
v_bs_x27_1081_ = lean_array_uset(v_bs_1076_, v_i_1075_, v___x_1080_);
v___x_1082_ = lean_array_get_borrowed(v___x_1078_, v_xs_1073_, v_v_1079_);
lean_dec(v_v_1079_);
v___x_1083_ = ((size_t)1ULL);
v___x_1084_ = lean_usize_add(v_i_1075_, v___x_1083_);
lean_inc(v___x_1082_);
v___x_1085_ = lean_array_uset(v_bs_x27_1081_, v_i_1075_, v___x_1082_);
v_i_1075_ = v___x_1084_;
v_bs_1076_ = v___x_1085_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__13_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_1073_ = stack[0].m_obj;
size_t v_sz_1074_ = stack[1].m_num;
size_t v_i_1075_ = stack[2].m_num;
lean_object* v_bs_1076_ = stack[3].m_obj;
lean_object* v_res_1087_;
v_res_1087_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__13(v_xs_1073_, v_sz_1074_, v_i_1075_, v_bs_1076_);
stack->m_obj
 = v_res_1087_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__13___boxed(lean_object* v_xs_1088_, lean_object* v_sz_1089_, lean_object* v_i_1090_, lean_object* v_bs_1091_){
_start:
{
size_t v_sz_boxed_1092_; size_t v_i_boxed_1093_; lean_object* v_res_1094_; 
v_sz_boxed_1092_ = lean_unbox_usize(v_sz_1089_);
lean_dec(v_sz_1089_);
v_i_boxed_1093_ = lean_unbox_usize(v_i_1090_);
lean_dec(v_i_1090_);
v_res_1094_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__13(v_xs_1088_, v_sz_boxed_1092_, v_i_boxed_1093_, v_bs_1091_);
lean_dec_ref(v_xs_1088_);
return v_res_1094_;
}
}
lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15___redArg(lean_object* v_xs_1095_, lean_object* v_f_1096_, lean_object* v_as_1097_, lean_object* v_bs_1098_, lean_object* v_i_1099_, lean_object* v_cs_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_){
_start:
{
lean_object* v___x_1106_; uint8_t v___x_1107_; 
v___x_1106_ = lean_array_get_size(v_as_1097_);
v___x_1107_ = lean_nat_dec_lt(v_i_1099_, v___x_1106_);
if (v___x_1107_ == 0)
{
lean_object* v___x_1108_; 
lean_dec(v_i_1099_);
lean_dec_ref(v_f_1096_);
v___x_1108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1108_, 0, v_cs_1100_);
return v___x_1108_;
}
else
{
lean_object* v___x_1109_; uint8_t v___x_1110_; 
v___x_1109_ = lean_array_get_size(v_bs_1098_);
v___x_1110_ = lean_nat_dec_lt(v_i_1099_, v___x_1109_);
if (v___x_1110_ == 0)
{
lean_object* v___x_1111_; 
lean_dec(v_i_1099_);
lean_dec_ref(v_f_1096_);
v___x_1111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1111_, 0, v_cs_1100_);
return v___x_1111_;
}
else
{
lean_object* v_a_1112_; lean_object* v_b_1113_; size_t v_sz_1114_; size_t v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
v_a_1112_ = lean_array_fget_borrowed(v_as_1097_, v_i_1099_);
v_b_1113_ = lean_array_fget_borrowed(v_bs_1098_, v_i_1099_);
v_sz_1114_ = lean_array_size(v_b_1113_);
v___x_1115_ = ((size_t)0ULL);
lean_inc(v_b_1113_);
v___x_1116_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__13(v_xs_1095_, v_sz_1114_, v___x_1115_, v_b_1113_);
lean_inc_ref(v_f_1096_);
lean_inc(v___y_1104_);
lean_inc_ref(v___y_1103_);
lean_inc(v___y_1102_);
lean_inc_ref(v___y_1101_);
lean_inc(v_a_1112_);
v___x_1117_ = lean_apply_7(v_f_1096_, v_a_1112_, v___x_1116_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_, lean_box(0));
if (lean_obj_tag(v___x_1117_) == 0)
{
lean_object* v_a_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; 
v_a_1118_ = lean_ctor_get(v___x_1117_, 0);
lean_inc(v_a_1118_);
lean_dec_ref_known(v___x_1117_, 1);
v___x_1119_ = lean_unsigned_to_nat(1u);
v___x_1120_ = lean_nat_add(v_i_1099_, v___x_1119_);
lean_dec(v_i_1099_);
v___x_1121_ = lean_array_push(v_cs_1100_, v_a_1118_);
v_i_1099_ = v___x_1120_;
v_cs_1100_ = v___x_1121_;
goto _start;
}
else
{
lean_object* v_a_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1130_; 
lean_dec_ref(v_cs_1100_);
lean_dec(v_i_1099_);
lean_dec_ref(v_f_1096_);
v_a_1123_ = lean_ctor_get(v___x_1117_, 0);
v_isSharedCheck_1130_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1125_ = v___x_1117_;
v_isShared_1126_ = v_isSharedCheck_1130_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_a_1123_);
lean_dec(v___x_1117_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1130_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___x_1128_; 
if (v_isShared_1126_ == 0)
{
v___x_1128_ = v___x_1125_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v_a_1123_);
v___x_1128_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
return v___x_1128_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_1095_ = stack[0].m_obj;
lean_object* v_f_1096_ = stack[1].m_obj;
lean_object* v_as_1097_ = stack[2].m_obj;
lean_object* v_bs_1098_ = stack[3].m_obj;
lean_object* v_i_1099_ = stack[4].m_obj;
lean_object* v_cs_1100_ = stack[5].m_obj;
lean_object* v___y_1101_ = stack[6].m_obj;
lean_object* v___y_1102_ = stack[7].m_obj;
lean_object* v___y_1103_ = stack[8].m_obj;
lean_object* v___y_1104_ = stack[9].m_obj;
lean_object* v_res_1131_;
v_res_1131_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15___redArg(v_xs_1095_, v_f_1096_, v_as_1097_, v_bs_1098_, v_i_1099_, v_cs_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_);
stack->m_obj
 = v_res_1131_;
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15___redArg___boxed(lean_object* v_xs_1132_, lean_object* v_f_1133_, lean_object* v_as_1134_, lean_object* v_bs_1135_, lean_object* v_i_1136_, lean_object* v_cs_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_){
_start:
{
lean_object* v_res_1143_; 
v_res_1143_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15___redArg(v_xs_1132_, v_f_1133_, v_as_1134_, v_bs_1135_, v_i_1136_, v_cs_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_);
lean_dec(v___y_1141_);
lean_dec_ref(v___y_1140_);
lean_dec(v___y_1139_);
lean_dec_ref(v___y_1138_);
lean_dec_ref(v_bs_1135_);
lean_dec_ref(v_as_1134_);
lean_dec_ref(v_xs_1132_);
return v_res_1143_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; 
v___x_1147_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__2));
v___x_1148_ = lean_unsigned_to_nat(2u);
v___x_1149_ = lean_unsigned_to_nat(73u);
v___x_1150_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__1));
v___x_1151_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__0));
v___x_1152_ = l_mkPanicMessageWithDecl(v___x_1151_, v___x_1150_, v___x_1149_, v___x_1148_, v___x_1147_);
return v___x_1152_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1154_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__4));
v___x_1155_ = lean_unsigned_to_nat(2u);
v___x_1156_ = lean_unsigned_to_nat(74u);
v___x_1157_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__1));
v___x_1158_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__0));
v___x_1159_ = l_mkPanicMessageWithDecl(v___x_1158_, v___x_1157_, v___x_1156_, v___x_1155_, v___x_1154_);
return v___x_1159_;
}
}
lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg(lean_object* v_f_1162_, lean_object* v_positions_1163_, lean_object* v_ys_1164_, lean_object* v_xs_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_){
_start:
{
lean_object* v___x_1171_; lean_object* v___x_1172_; uint8_t v___x_1173_; 
v___x_1171_ = lean_array_get_size(v_positions_1163_);
v___x_1172_ = lean_array_get_size(v_ys_1164_);
v___x_1173_ = lean_nat_dec_eq(v___x_1171_, v___x_1172_);
if (v___x_1173_ == 0)
{
lean_object* v___x_1174_; lean_object* v___x_1175_; 
lean_dec_ref(v_f_1162_);
v___x_1174_ = lean_obj_once(&l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__3, &l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__3_once, _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__3);
v___x_1175_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg(v___x_1174_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_);
return v___x_1175_;
}
else
{
lean_object* v___x_1176_; lean_object* v___x_1177_; uint8_t v___x_1178_; 
v___x_1176_ = l_Lean_Elab_Structural_Positions_numIndices(v_positions_1163_);
v___x_1177_ = lean_array_get_size(v_xs_1165_);
v___x_1178_ = lean_nat_dec_eq(v___x_1176_, v___x_1177_);
lean_dec(v___x_1176_);
if (v___x_1178_ == 0)
{
lean_object* v___x_1179_; lean_object* v___x_1180_; 
lean_dec_ref(v_f_1162_);
v___x_1179_ = lean_obj_once(&l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__5, &l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__5_once, _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__5);
v___x_1180_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg(v___x_1179_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_);
return v___x_1180_;
}
else
{
lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; 
v___x_1181_ = lean_unsigned_to_nat(0u);
v___x_1182_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__6));
v___x_1183_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15___redArg(v_xs_1165_, v_f_1162_, v_ys_1164_, v_positions_1163_, v___x_1181_, v___x_1182_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_);
return v___x_1183_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1162_ = stack[0].m_obj;
lean_object* v_positions_1163_ = stack[1].m_obj;
lean_object* v_ys_1164_ = stack[2].m_obj;
lean_object* v_xs_1165_ = stack[3].m_obj;
lean_object* v___y_1166_ = stack[4].m_obj;
lean_object* v___y_1167_ = stack[5].m_obj;
lean_object* v___y_1168_ = stack[6].m_obj;
lean_object* v___y_1169_ = stack[7].m_obj;
lean_object* v_res_1184_;
v_res_1184_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg(v_f_1162_, v_positions_1163_, v_ys_1164_, v_xs_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_);
stack->m_obj
 = v_res_1184_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___boxed(lean_object* v_f_1185_, lean_object* v_positions_1186_, lean_object* v_ys_1187_, lean_object* v_xs_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_){
_start:
{
lean_object* v_res_1194_; 
v_res_1194_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg(v_f_1185_, v_positions_1186_, v_ys_1187_, v_xs_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_);
lean_dec(v___y_1192_);
lean_dec_ref(v___y_1191_);
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
lean_dec_ref(v_xs_1188_);
lean_dec_ref(v_ys_1187_);
lean_dec_ref(v_positions_1186_);
return v_res_1194_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg(lean_object* v___x_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_, lean_object* v_funTypes_1198_, size_t v_sz_1199_, size_t v_i_1200_, lean_object* v_bs_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_){
_start:
{
uint8_t v___x_1207_; 
v___x_1207_ = lean_usize_dec_lt(v_i_1200_, v_sz_1199_);
if (v___x_1207_ == 0)
{
lean_object* v___x_1208_; 
lean_dec_ref(v_funTypes_1198_);
lean_dec_ref(v_a_1197_);
lean_dec_ref(v_a_1196_);
lean_dec_ref(v___x_1195_);
v___x_1208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1208_, 0, v_bs_1201_);
return v___x_1208_;
}
else
{
lean_object* v_v_1209_; lean_object* v_fst_1210_; lean_object* v_snd_1211_; lean_object* v___x_1212_; lean_object* v_bs_x27_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; 
v_v_1209_ = lean_array_uget_borrowed(v_bs_1201_, v_i_1200_);
v_fst_1210_ = lean_ctor_get(v_v_1209_, 0);
lean_inc(v_fst_1210_);
v_snd_1211_ = lean_ctor_get(v_v_1209_, 1);
lean_inc(v_snd_1211_);
v___x_1212_ = lean_unsigned_to_nat(0u);
v_bs_x27_1213_ = lean_array_uset(v_bs_1201_, v_i_1200_, v___x_1212_);
v___x_1214_ = lean_usize_to_nat(v_i_1200_);
lean_inc_ref(v_funTypes_1198_);
lean_inc_ref(v_a_1197_);
lean_inc_ref(v_a_1196_);
lean_inc_ref(v___x_1195_);
v___x_1215_ = l_Lean_Elab_Structural_mkBRecOnApp(v___x_1195_, v___x_1214_, v_a_1196_, v_a_1197_, v_funTypes_1198_, v_fst_1210_, v_snd_1211_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_);
if (lean_obj_tag(v___x_1215_) == 0)
{
lean_object* v_a_1216_; size_t v___x_1217_; size_t v___x_1218_; lean_object* v___x_1219_; 
v_a_1216_ = lean_ctor_get(v___x_1215_, 0);
lean_inc(v_a_1216_);
lean_dec_ref_known(v___x_1215_, 1);
v___x_1217_ = ((size_t)1ULL);
v___x_1218_ = lean_usize_add(v_i_1200_, v___x_1217_);
v___x_1219_ = lean_array_uset(v_bs_x27_1213_, v_i_1200_, v_a_1216_);
v_i_1200_ = v___x_1218_;
v_bs_1201_ = v___x_1219_;
goto _start;
}
else
{
lean_object* v_a_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1228_; 
lean_dec_ref(v_bs_x27_1213_);
lean_dec_ref(v_funTypes_1198_);
lean_dec_ref(v_a_1197_);
lean_dec_ref(v_a_1196_);
lean_dec_ref(v___x_1195_);
v_a_1221_ = lean_ctor_get(v___x_1215_, 0);
v_isSharedCheck_1228_ = !lean_is_exclusive(v___x_1215_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1223_ = v___x_1215_;
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_a_1221_);
lean_dec(v___x_1215_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___x_1226_; 
if (v_isShared_1224_ == 0)
{
v___x_1226_ = v___x_1223_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v_a_1221_);
v___x_1226_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
return v___x_1226_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1195_ = stack[0].m_obj;
lean_object* v_a_1196_ = stack[1].m_obj;
lean_object* v_a_1197_ = stack[2].m_obj;
lean_object* v_funTypes_1198_ = stack[3].m_obj;
size_t v_sz_1199_ = stack[4].m_num;
size_t v_i_1200_ = stack[5].m_num;
lean_object* v_bs_1201_ = stack[6].m_obj;
lean_object* v___y_1202_ = stack[7].m_obj;
lean_object* v___y_1203_ = stack[8].m_obj;
lean_object* v___y_1204_ = stack[9].m_obj;
lean_object* v___y_1205_ = stack[10].m_obj;
lean_object* v_res_1229_;
v_res_1229_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg(v___x_1195_, v_a_1196_, v_a_1197_, v_funTypes_1198_, v_sz_1199_, v_i_1200_, v_bs_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_);
stack->m_obj
 = v_res_1229_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg___boxed(lean_object* v___x_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_, lean_object* v_funTypes_1233_, lean_object* v_sz_1234_, lean_object* v_i_1235_, lean_object* v_bs_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_){
_start:
{
size_t v_sz_boxed_1242_; size_t v_i_boxed_1243_; lean_object* v_res_1244_; 
v_sz_boxed_1242_ = lean_unbox_usize(v_sz_1234_);
lean_dec(v_sz_1234_);
v_i_boxed_1243_ = lean_unbox_usize(v_i_1235_);
lean_dec(v_i_1235_);
v_res_1244_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg(v___x_1230_, v_a_1231_, v_a_1232_, v_funTypes_1233_, v_sz_boxed_1242_, v_i_boxed_1243_, v_bs_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_);
lean_dec(v___y_1240_);
lean_dec_ref(v___y_1239_);
lean_dec(v___y_1238_);
lean_dec_ref(v___y_1237_);
return v_res_1244_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__2(void){
_start:
{
lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; 
v___x_1248_ = lean_box(0);
v___x_1249_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__1));
v___x_1250_ = l_Lean_Expr_const___override(v___x_1249_, v___x_1248_);
return v___x_1250_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__4(void){
_start:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; 
v___x_1252_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__3));
v___x_1253_ = l_Lean_stringToMessageData(v___x_1252_);
return v___x_1253_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__6(void){
_start:
{
lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1255_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__5));
v___x_1256_ = l_Lean_stringToMessageData(v___x_1255_);
return v___x_1256_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__8(void){
_start:
{
lean_object* v___x_1258_; lean_object* v___x_1259_; 
v___x_1258_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__7));
v___x_1259_ = l_Lean_stringToMessageData(v___x_1258_);
return v___x_1259_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__10(void){
_start:
{
lean_object* v___x_1261_; lean_object* v___x_1262_; 
v___x_1261_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__9));
v___x_1262_ = l_Lean_stringToMessageData(v___x_1261_);
return v___x_1262_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__12(void){
_start:
{
lean_object* v___x_1264_; lean_object* v___x_1265_; 
v___x_1264_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__11));
v___x_1265_ = l_Lean_stringToMessageData(v___x_1264_);
return v___x_1265_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2(lean_object* v_recArgInfos_1266_, lean_object* v_a_1267_, lean_object* v___x_1268_, size_t v___x_1269_, lean_object* v_fixedParamPerms_1270_, lean_object* v_xs_1271_, lean_object* v___x_1272_, lean_object* v_preDefs_1273_, lean_object* v_numIndices_1274_, lean_object* v___f_1275_, lean_object* v___x_1276_, uint8_t v_a_1277_, lean_object* v___x_1278_, lean_object* v___f_1279_, lean_object* v_funTypes_1280_, lean_object* v_motives_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_){
_start:
{
lean_object* v___y_1288_; lean_object* v___y_1289_; lean_object* v___y_1290_; lean_object* v___y_1291_; lean_object* v___y_1292_; lean_object* v___y_1293_; lean_object* v___y_1328_; lean_object* v_FArgs_1329_; lean_object* v___y_1330_; lean_object* v___y_1331_; lean_object* v___y_1332_; lean_object* v___y_1333_; lean_object* v___y_1385_; lean_object* v___y_1386_; lean_object* v___y_1387_; lean_object* v___y_1388_; lean_object* v___y_1389_; lean_object* v___y_1390_; lean_object* v___y_1407_; lean_object* v___y_1408_; lean_object* v___y_1409_; lean_object* v___y_1410_; lean_object* v___y_1411_; lean_object* v___y_1412_; lean_object* v___x_1497_; 
lean_inc_ref(v___f_1279_);
lean_inc(v___y_1285_);
lean_inc_ref(v___y_1284_);
lean_inc(v___y_1283_);
lean_inc_ref(v___y_1282_);
v___x_1497_ = lean_apply_5(v___f_1279_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, lean_box(0));
if (lean_obj_tag(v___x_1497_) == 0)
{
lean_object* v_a_1498_; uint8_t v___x_1499_; 
v_a_1498_ = lean_ctor_get(v___x_1497_, 0);
lean_inc(v_a_1498_);
lean_dec_ref_known(v___x_1497_, 1);
v___x_1499_ = lean_unbox(v_a_1498_);
lean_dec(v_a_1498_);
if (v___x_1499_ == 0)
{
goto v___jp_1450_;
}
else
{
lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; 
v___x_1500_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__10, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__10);
lean_inc_ref(v_funTypes_1280_);
v___x_1501_ = lean_array_to_list(v_funTypes_1280_);
v___x_1502_ = lean_box(0);
v___x_1503_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_1501_, v___x_1502_);
v___x_1504_ = l_Lean_MessageData_ofList(v___x_1503_);
v___x_1505_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1505_, 0, v___x_1500_);
lean_ctor_set(v___x_1505_, 1, v___x_1504_);
v___x_1506_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__12, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__12_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__12);
v___x_1507_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1507_, 0, v___x_1505_);
lean_ctor_set(v___x_1507_, 1, v___x_1506_);
lean_inc_ref(v_motives_1281_);
v___x_1508_ = lean_array_to_list(v_motives_1281_);
v___x_1509_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_1508_, v___x_1502_);
v___x_1510_ = l_Lean_MessageData_ofList(v___x_1509_);
v___x_1511_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1511_, 0, v___x_1507_);
lean_ctor_set(v___x_1511_, 1, v___x_1510_);
lean_inc(v___x_1276_);
v___x_1512_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_1276_, v___x_1511_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_);
if (lean_obj_tag(v___x_1512_) == 0)
{
lean_dec_ref_known(v___x_1512_, 1);
goto v___jp_1450_;
}
else
{
lean_object* v_a_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1520_; 
lean_dec_ref(v_motives_1281_);
lean_dec_ref(v_funTypes_1280_);
lean_dec_ref(v___f_1279_);
lean_dec(v___x_1276_);
lean_dec_ref(v___f_1275_);
lean_dec_ref(v_preDefs_1273_);
lean_dec(v___x_1272_);
lean_dec_ref(v_xs_1271_);
lean_dec_ref(v_fixedParamPerms_1270_);
lean_dec_ref(v___x_1268_);
lean_dec_ref(v_recArgInfos_1266_);
v_a_1513_ = lean_ctor_get(v___x_1512_, 0);
v_isSharedCheck_1520_ = !lean_is_exclusive(v___x_1512_);
if (v_isSharedCheck_1520_ == 0)
{
v___x_1515_ = v___x_1512_;
v_isShared_1516_ = v_isSharedCheck_1520_;
goto v_resetjp_1514_;
}
else
{
lean_inc(v_a_1513_);
lean_dec(v___x_1512_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1520_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
lean_object* v___x_1518_; 
if (v_isShared_1516_ == 0)
{
v___x_1518_ = v___x_1515_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v_a_1513_);
v___x_1518_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
return v___x_1518_;
}
}
}
}
}
else
{
lean_object* v_a_1521_; lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1528_; 
lean_dec_ref(v_motives_1281_);
lean_dec_ref(v_funTypes_1280_);
lean_dec_ref(v___f_1279_);
lean_dec(v___x_1276_);
lean_dec_ref(v___f_1275_);
lean_dec_ref(v_preDefs_1273_);
lean_dec(v___x_1272_);
lean_dec_ref(v_xs_1271_);
lean_dec_ref(v_fixedParamPerms_1270_);
lean_dec_ref(v___x_1268_);
lean_dec_ref(v_recArgInfos_1266_);
v_a_1521_ = lean_ctor_get(v___x_1497_, 0);
v_isSharedCheck_1528_ = !lean_is_exclusive(v___x_1497_);
if (v_isSharedCheck_1528_ == 0)
{
v___x_1523_ = v___x_1497_;
v_isShared_1524_ = v_isSharedCheck_1528_;
goto v_resetjp_1522_;
}
else
{
lean_inc(v_a_1521_);
lean_dec(v___x_1497_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1528_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
lean_object* v___x_1526_; 
if (v_isShared_1524_ == 0)
{
v___x_1526_ = v___x_1523_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v_a_1521_);
v___x_1526_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
return v___x_1526_;
}
}
}
v___jp_1287_:
{
lean_object* v___x_1294_; size_t v_sz_1295_; lean_object* v___x_1296_; 
v___x_1294_ = l_Array_zip___redArg(v_recArgInfos_1266_, v_a_1267_);
lean_dec_ref(v_recArgInfos_1266_);
v_sz_1295_ = lean_array_size(v___x_1294_);
v___x_1296_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg(v___x_1268_, v___y_1288_, v___y_1289_, v_funTypes_1280_, v_sz_1295_, v___x_1269_, v___x_1294_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_);
if (lean_obj_tag(v___x_1296_) == 0)
{
lean_object* v_a_1297_; lean_object* v___x_1298_; size_t v_sz_1299_; lean_object* v___x_1300_; 
v_a_1297_ = lean_ctor_get(v___x_1296_, 0);
lean_inc(v_a_1297_);
lean_dec_ref_known(v___x_1296_, 1);
v___x_1298_ = l_Array_zip___redArg(v_a_1267_, v_a_1297_);
lean_dec(v_a_1297_);
v_sz_1299_ = lean_array_size(v___x_1298_);
v___x_1300_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg(v_fixedParamPerms_1270_, v_xs_1271_, v_sz_1299_, v___x_1269_, v___x_1298_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_);
if (lean_obj_tag(v___x_1300_) == 0)
{
lean_object* v_a_1301_; lean_object* v___x_1303_; uint8_t v_isShared_1304_; uint8_t v_isSharedCheck_1310_; 
v_a_1301_ = lean_ctor_get(v___x_1300_, 0);
v_isSharedCheck_1310_ = !lean_is_exclusive(v___x_1300_);
if (v_isSharedCheck_1310_ == 0)
{
v___x_1303_ = v___x_1300_;
v_isShared_1304_ = v_isSharedCheck_1310_;
goto v_resetjp_1302_;
}
else
{
lean_inc(v_a_1301_);
lean_dec(v___x_1300_);
v___x_1303_ = lean_box(0);
v_isShared_1304_ = v_isSharedCheck_1310_;
goto v_resetjp_1302_;
}
v_resetjp_1302_:
{
lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1308_; 
v___x_1305_ = lean_mk_empty_array_with_capacity(v___x_1272_);
v___x_1306_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9(v_preDefs_1273_, v_a_1301_, v___x_1272_, v___x_1305_);
lean_dec(v_a_1301_);
lean_dec_ref(v_preDefs_1273_);
if (v_isShared_1304_ == 0)
{
lean_ctor_set(v___x_1303_, 0, v___x_1306_);
v___x_1308_ = v___x_1303_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v___x_1306_);
v___x_1308_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
return v___x_1308_;
}
}
}
else
{
lean_object* v_a_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1318_; 
lean_dec_ref(v_preDefs_1273_);
lean_dec(v___x_1272_);
v_a_1311_ = lean_ctor_get(v___x_1300_, 0);
v_isSharedCheck_1318_ = !lean_is_exclusive(v___x_1300_);
if (v_isSharedCheck_1318_ == 0)
{
v___x_1313_ = v___x_1300_;
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_a_1311_);
lean_dec(v___x_1300_);
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
else
{
lean_object* v_a_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1326_; 
lean_dec_ref(v_preDefs_1273_);
lean_dec(v___x_1272_);
lean_dec_ref(v_xs_1271_);
lean_dec_ref(v_fixedParamPerms_1270_);
v_a_1319_ = lean_ctor_get(v___x_1296_, 0);
v_isSharedCheck_1326_ = !lean_is_exclusive(v___x_1296_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1321_ = v___x_1296_;
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_a_1319_);
lean_dec(v___x_1296_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v___x_1324_; 
if (v_isShared_1322_ == 0)
{
v___x_1324_ = v___x_1321_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v_a_1319_);
v___x_1324_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
return v___x_1324_;
}
}
}
}
v___jp_1327_:
{
lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; 
lean_inc_ref(v___y_1328_);
lean_inc(v___x_1272_);
v___x_1334_ = lean_apply_1(v___y_1328_, v___x_1272_);
v___x_1335_ = lean_unsigned_to_nat(1u);
v___x_1336_ = lean_nat_add(v_numIndices_1274_, v___x_1335_);
v___x_1337_ = lean_box(0);
v___x_1338_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__2);
v___x_1339_ = lean_mk_array(v___x_1336_, v___x_1338_);
v___x_1340_ = l_Lean_mkAppN(v___x_1334_, v___x_1339_);
lean_dec_ref(v___x_1339_);
v___x_1341_ = lean_array_get_size(v___x_1268_);
v___x_1342_ = l_Lean_Meta_inferArgumentTypesN(v___x_1341_, v___x_1340_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_);
if (lean_obj_tag(v___x_1342_) == 0)
{
lean_object* v_a_1343_; lean_object* v___x_1344_; 
v_a_1343_ = lean_ctor_get(v___x_1342_, 0);
lean_inc(v_a_1343_);
lean_dec_ref_known(v___x_1342_, 1);
v___x_1344_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg(v___f_1275_, v___x_1268_, v_a_1343_, v_FArgs_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_);
lean_dec_ref(v_FArgs_1329_);
lean_dec(v_a_1343_);
if (lean_obj_tag(v___x_1344_) == 0)
{
lean_object* v_toCold_1345_; lean_object* v_options_1346_; uint8_t v_hasTrace_1347_; 
v_toCold_1345_ = lean_ctor_get(v___y_1332_, 0);
v_options_1346_ = lean_ctor_get(v_toCold_1345_, 2);
v_hasTrace_1347_ = lean_ctor_get_uint8(v_options_1346_, sizeof(void*)*1);
if (v_hasTrace_1347_ == 0)
{
lean_object* v_a_1348_; 
lean_dec(v___x_1276_);
v_a_1348_ = lean_ctor_get(v___x_1344_, 0);
lean_inc(v_a_1348_);
lean_dec_ref_known(v___x_1344_, 1);
v___y_1288_ = v___y_1328_;
v___y_1289_ = v_a_1348_;
v___y_1290_ = v___y_1330_;
v___y_1291_ = v___y_1331_;
v___y_1292_ = v___y_1332_;
v___y_1293_ = v___y_1333_;
goto v___jp_1287_;
}
else
{
lean_object* v_a_1349_; lean_object* v_inheritedTraceOptions_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; uint8_t v___x_1353_; 
v_a_1349_ = lean_ctor_get(v___x_1344_, 0);
lean_inc(v_a_1349_);
lean_dec_ref_known(v___x_1344_, 1);
v_inheritedTraceOptions_1350_ = lean_ctor_get(v_toCold_1345_, 11);
v___x_1351_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___closed__1));
lean_inc(v___x_1276_);
v___x_1352_ = l_Lean_Name_append(v___x_1351_, v___x_1276_);
v___x_1353_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1350_, v_options_1346_, v___x_1352_);
lean_dec(v___x_1352_);
if (v___x_1353_ == 0)
{
lean_dec(v___x_1276_);
v___y_1288_ = v___y_1328_;
v___y_1289_ = v_a_1349_;
v___y_1290_ = v___y_1330_;
v___y_1291_ = v___y_1331_;
v___y_1292_ = v___y_1332_;
v___y_1293_ = v___y_1333_;
goto v___jp_1287_;
}
else
{
lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; 
v___x_1354_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__4);
lean_inc(v_a_1349_);
v___x_1355_ = lean_array_to_list(v_a_1349_);
v___x_1356_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_1355_, v___x_1337_);
v___x_1357_ = l_Lean_MessageData_ofList(v___x_1356_);
v___x_1358_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1358_, 0, v___x_1354_);
lean_ctor_set(v___x_1358_, 1, v___x_1357_);
v___x_1359_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_1276_, v___x_1358_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_);
if (lean_obj_tag(v___x_1359_) == 0)
{
lean_dec_ref_known(v___x_1359_, 1);
v___y_1288_ = v___y_1328_;
v___y_1289_ = v_a_1349_;
v___y_1290_ = v___y_1330_;
v___y_1291_ = v___y_1331_;
v___y_1292_ = v___y_1332_;
v___y_1293_ = v___y_1333_;
goto v___jp_1287_;
}
else
{
lean_object* v_a_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1367_; 
lean_dec(v_a_1349_);
lean_dec_ref(v___y_1328_);
lean_dec_ref(v_funTypes_1280_);
lean_dec_ref(v_preDefs_1273_);
lean_dec(v___x_1272_);
lean_dec_ref(v_xs_1271_);
lean_dec_ref(v_fixedParamPerms_1270_);
lean_dec_ref(v___x_1268_);
lean_dec_ref(v_recArgInfos_1266_);
v_a_1360_ = lean_ctor_get(v___x_1359_, 0);
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1359_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1362_ = v___x_1359_;
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_a_1360_);
lean_dec(v___x_1359_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1365_; 
if (v_isShared_1363_ == 0)
{
v___x_1365_ = v___x_1362_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_a_1360_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
return v___x_1365_;
}
}
}
}
}
}
else
{
lean_object* v_a_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1375_; 
lean_dec_ref(v___y_1328_);
lean_dec_ref(v_funTypes_1280_);
lean_dec(v___x_1276_);
lean_dec_ref(v_preDefs_1273_);
lean_dec(v___x_1272_);
lean_dec_ref(v_xs_1271_);
lean_dec_ref(v_fixedParamPerms_1270_);
lean_dec_ref(v___x_1268_);
lean_dec_ref(v_recArgInfos_1266_);
v_a_1368_ = lean_ctor_get(v___x_1344_, 0);
v_isSharedCheck_1375_ = !lean_is_exclusive(v___x_1344_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1370_ = v___x_1344_;
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_a_1368_);
lean_dec(v___x_1344_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1373_; 
if (v_isShared_1371_ == 0)
{
v___x_1373_ = v___x_1370_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v_a_1368_);
v___x_1373_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
return v___x_1373_;
}
}
}
}
else
{
lean_object* v_a_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1383_; 
lean_dec_ref(v_FArgs_1329_);
lean_dec_ref(v___y_1328_);
lean_dec_ref(v_funTypes_1280_);
lean_dec(v___x_1276_);
lean_dec_ref(v___f_1275_);
lean_dec_ref(v_preDefs_1273_);
lean_dec(v___x_1272_);
lean_dec_ref(v_xs_1271_);
lean_dec_ref(v_fixedParamPerms_1270_);
lean_dec_ref(v___x_1268_);
lean_dec_ref(v_recArgInfos_1266_);
v_a_1376_ = lean_ctor_get(v___x_1342_, 0);
v_isSharedCheck_1383_ = !lean_is_exclusive(v___x_1342_);
if (v_isSharedCheck_1383_ == 0)
{
v___x_1378_ = v___x_1342_;
v_isShared_1379_ = v_isSharedCheck_1383_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_a_1376_);
lean_dec(v___x_1342_);
v___x_1378_ = lean_box(0);
v_isShared_1379_ = v_isSharedCheck_1383_;
goto v_resetjp_1377_;
}
v_resetjp_1377_:
{
lean_object* v___x_1381_; 
if (v_isShared_1379_ == 0)
{
v___x_1381_ = v___x_1378_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v_a_1376_);
v___x_1381_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
return v___x_1381_;
}
}
}
}
v___jp_1384_:
{
if (v_a_1277_ == 0)
{
lean_object* v___x_1391_; lean_object* v_levelParams_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; size_t v_sz_1395_; lean_object* v___x_1396_; 
v___x_1391_ = lean_array_get_borrowed(v___x_1278_, v_preDefs_1273_, v___x_1272_);
v_levelParams_1392_ = lean_ctor_get(v___x_1391_, 1);
v___x_1393_ = lean_box(0);
lean_inc(v_levelParams_1392_);
v___x_1394_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__15(v_levelParams_1392_, v___x_1393_);
v_sz_1395_ = lean_array_size(v___y_1386_);
v___x_1396_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg(v_preDefs_1273_, v_xs_1271_, v_a_1277_, v___x_1394_, v_sz_1395_, v___x_1269_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_);
if (lean_obj_tag(v___x_1396_) == 0)
{
lean_object* v_a_1397_; 
v_a_1397_ = lean_ctor_get(v___x_1396_, 0);
lean_inc(v_a_1397_);
lean_dec_ref_known(v___x_1396_, 1);
v___y_1328_ = v___y_1385_;
v_FArgs_1329_ = v_a_1397_;
v___y_1330_ = v___y_1387_;
v___y_1331_ = v___y_1388_;
v___y_1332_ = v___y_1389_;
v___y_1333_ = v___y_1390_;
goto v___jp_1327_;
}
else
{
lean_object* v_a_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1405_; 
lean_dec_ref(v___y_1385_);
lean_dec_ref(v_funTypes_1280_);
lean_dec(v___x_1276_);
lean_dec_ref(v___f_1275_);
lean_dec_ref(v_preDefs_1273_);
lean_dec(v___x_1272_);
lean_dec_ref(v_xs_1271_);
lean_dec_ref(v_fixedParamPerms_1270_);
lean_dec_ref(v___x_1268_);
lean_dec_ref(v_recArgInfos_1266_);
v_a_1398_ = lean_ctor_get(v___x_1396_, 0);
v_isSharedCheck_1405_ = !lean_is_exclusive(v___x_1396_);
if (v_isSharedCheck_1405_ == 0)
{
v___x_1400_ = v___x_1396_;
v_isShared_1401_ = v_isSharedCheck_1405_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_a_1398_);
lean_dec(v___x_1396_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1405_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
lean_object* v___x_1403_; 
if (v_isShared_1401_ == 0)
{
v___x_1403_ = v___x_1400_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v_a_1398_);
v___x_1403_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
return v___x_1403_;
}
}
}
}
else
{
v___y_1328_ = v___y_1385_;
v_FArgs_1329_ = v___y_1386_;
v___y_1330_ = v___y_1387_;
v___y_1331_ = v___y_1388_;
v___y_1332_ = v___y_1389_;
v___y_1333_ = v___y_1390_;
goto v___jp_1327_;
}
}
v___jp_1406_:
{
size_t v_sz_1413_; lean_object* v___x_1414_; 
v_sz_1413_ = lean_array_size(v_recArgInfos_1266_);
lean_inc_ref(v___y_1407_);
lean_inc_ref(v_preDefs_1273_);
lean_inc_ref(v___x_1268_);
lean_inc_ref_n(v_recArgInfos_1266_, 2);
v___x_1414_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg(v_a_1277_, v_a_1267_, v___y_1408_, v_recArgInfos_1266_, v___x_1268_, v_preDefs_1273_, v___y_1407_, v_sz_1413_, v___x_1269_, v_recArgInfos_1266_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_);
lean_dec_ref(v___y_1408_);
if (lean_obj_tag(v___x_1414_) == 0)
{
lean_object* v_a_1415_; lean_object* v___x_1416_; 
v_a_1415_ = lean_ctor_get(v___x_1414_, 0);
lean_inc(v_a_1415_);
lean_dec_ref_known(v___x_1414_, 1);
lean_inc(v___y_1412_);
lean_inc_ref(v___y_1411_);
lean_inc(v___y_1410_);
lean_inc_ref(v___y_1409_);
v___x_1416_ = lean_apply_5(v___f_1279_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_, lean_box(0));
if (lean_obj_tag(v___x_1416_) == 0)
{
lean_object* v_a_1417_; uint8_t v___x_1418_; 
v_a_1417_ = lean_ctor_get(v___x_1416_, 0);
lean_inc(v_a_1417_);
lean_dec_ref_known(v___x_1416_, 1);
v___x_1418_ = lean_unbox(v_a_1417_);
lean_dec(v_a_1417_);
if (v___x_1418_ == 0)
{
v___y_1385_ = v___y_1407_;
v___y_1386_ = v_a_1415_;
v___y_1387_ = v___y_1409_;
v___y_1388_ = v___y_1410_;
v___y_1389_ = v___y_1411_;
v___y_1390_ = v___y_1412_;
goto v___jp_1384_;
}
else
{
lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; 
v___x_1419_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__6, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__6);
lean_inc(v_a_1415_);
v___x_1420_ = lean_array_to_list(v_a_1415_);
v___x_1421_ = lean_box(0);
v___x_1422_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_1420_, v___x_1421_);
v___x_1423_ = l_Lean_MessageData_ofList(v___x_1422_);
v___x_1424_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1424_, 0, v___x_1419_);
lean_ctor_set(v___x_1424_, 1, v___x_1423_);
lean_inc(v___x_1276_);
v___x_1425_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_1276_, v___x_1424_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_);
if (lean_obj_tag(v___x_1425_) == 0)
{
lean_dec_ref_known(v___x_1425_, 1);
v___y_1385_ = v___y_1407_;
v___y_1386_ = v_a_1415_;
v___y_1387_ = v___y_1409_;
v___y_1388_ = v___y_1410_;
v___y_1389_ = v___y_1411_;
v___y_1390_ = v___y_1412_;
goto v___jp_1384_;
}
else
{
lean_object* v_a_1426_; lean_object* v___x_1428_; uint8_t v_isShared_1429_; uint8_t v_isSharedCheck_1433_; 
lean_dec(v_a_1415_);
lean_dec_ref(v___y_1407_);
lean_dec_ref(v_funTypes_1280_);
lean_dec(v___x_1276_);
lean_dec_ref(v___f_1275_);
lean_dec_ref(v_preDefs_1273_);
lean_dec(v___x_1272_);
lean_dec_ref(v_xs_1271_);
lean_dec_ref(v_fixedParamPerms_1270_);
lean_dec_ref(v___x_1268_);
lean_dec_ref(v_recArgInfos_1266_);
v_a_1426_ = lean_ctor_get(v___x_1425_, 0);
v_isSharedCheck_1433_ = !lean_is_exclusive(v___x_1425_);
if (v_isSharedCheck_1433_ == 0)
{
v___x_1428_ = v___x_1425_;
v_isShared_1429_ = v_isSharedCheck_1433_;
goto v_resetjp_1427_;
}
else
{
lean_inc(v_a_1426_);
lean_dec(v___x_1425_);
v___x_1428_ = lean_box(0);
v_isShared_1429_ = v_isSharedCheck_1433_;
goto v_resetjp_1427_;
}
v_resetjp_1427_:
{
lean_object* v___x_1431_; 
if (v_isShared_1429_ == 0)
{
v___x_1431_ = v___x_1428_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v_a_1426_);
v___x_1431_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
return v___x_1431_;
}
}
}
}
}
else
{
lean_object* v_a_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1441_; 
lean_dec(v_a_1415_);
lean_dec_ref(v___y_1407_);
lean_dec_ref(v_funTypes_1280_);
lean_dec(v___x_1276_);
lean_dec_ref(v___f_1275_);
lean_dec_ref(v_preDefs_1273_);
lean_dec(v___x_1272_);
lean_dec_ref(v_xs_1271_);
lean_dec_ref(v_fixedParamPerms_1270_);
lean_dec_ref(v___x_1268_);
lean_dec_ref(v_recArgInfos_1266_);
v_a_1434_ = lean_ctor_get(v___x_1416_, 0);
v_isSharedCheck_1441_ = !lean_is_exclusive(v___x_1416_);
if (v_isSharedCheck_1441_ == 0)
{
v___x_1436_ = v___x_1416_;
v_isShared_1437_ = v_isSharedCheck_1441_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_a_1434_);
lean_dec(v___x_1416_);
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
else
{
lean_object* v_a_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1449_; 
lean_dec_ref(v___y_1407_);
lean_dec_ref(v_funTypes_1280_);
lean_dec_ref(v___f_1279_);
lean_dec(v___x_1276_);
lean_dec_ref(v___f_1275_);
lean_dec_ref(v_preDefs_1273_);
lean_dec(v___x_1272_);
lean_dec_ref(v_xs_1271_);
lean_dec_ref(v_fixedParamPerms_1270_);
lean_dec_ref(v___x_1268_);
lean_dec_ref(v_recArgInfos_1266_);
v_a_1442_ = lean_ctor_get(v___x_1414_, 0);
v_isSharedCheck_1449_ = !lean_is_exclusive(v___x_1414_);
if (v_isSharedCheck_1449_ == 0)
{
v___x_1444_ = v___x_1414_;
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_a_1442_);
lean_dec(v___x_1414_);
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
v___jp_1450_:
{
lean_object* v___x_1451_; 
v___x_1451_ = l_Lean_Elab_Structural_mkBRecOnConst(v_recArgInfos_1266_, v___x_1268_, v_motives_1281_, v_a_1277_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_);
lean_dec_ref(v_motives_1281_);
if (lean_obj_tag(v___x_1451_) == 0)
{
lean_object* v_a_1452_; lean_object* v___x_1453_; 
v_a_1452_ = lean_ctor_get(v___x_1451_, 0);
lean_inc_n(v_a_1452_, 2);
lean_dec_ref_known(v___x_1451_, 1);
lean_inc_ref(v___x_1268_);
v___x_1453_ = l_Lean_Elab_Structural_inferBRecOnFTypes(v_recArgInfos_1266_, v___x_1268_, v_a_1452_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_);
if (lean_obj_tag(v___x_1453_) == 0)
{
lean_object* v_a_1454_; lean_object* v___x_1455_; 
v_a_1454_ = lean_ctor_get(v___x_1453_, 0);
lean_inc(v_a_1454_);
lean_dec_ref_known(v___x_1453_, 1);
lean_inc_ref(v___f_1279_);
lean_inc(v___y_1285_);
lean_inc_ref(v___y_1284_);
lean_inc(v___y_1283_);
lean_inc_ref(v___y_1282_);
v___x_1455_ = lean_apply_5(v___f_1279_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, lean_box(0));
if (lean_obj_tag(v___x_1455_) == 0)
{
lean_object* v_a_1456_; uint8_t v___x_1457_; 
v_a_1456_ = lean_ctor_get(v___x_1455_, 0);
lean_inc(v_a_1456_);
lean_dec_ref_known(v___x_1455_, 1);
v___x_1457_ = lean_unbox(v_a_1456_);
lean_dec(v_a_1456_);
if (v___x_1457_ == 0)
{
v___y_1407_ = v_a_1452_;
v___y_1408_ = v_a_1454_;
v___y_1409_ = v___y_1282_;
v___y_1410_ = v___y_1283_;
v___y_1411_ = v___y_1284_;
v___y_1412_ = v___y_1285_;
goto v___jp_1406_;
}
else
{
lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; 
v___x_1458_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__8);
lean_inc(v_a_1454_);
v___x_1459_ = lean_array_to_list(v_a_1454_);
v___x_1460_ = lean_box(0);
v___x_1461_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_1459_, v___x_1460_);
v___x_1462_ = l_Lean_MessageData_ofList(v___x_1461_);
v___x_1463_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1463_, 0, v___x_1458_);
lean_ctor_set(v___x_1463_, 1, v___x_1462_);
lean_inc(v___x_1276_);
v___x_1464_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_1276_, v___x_1463_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_);
if (lean_obj_tag(v___x_1464_) == 0)
{
lean_dec_ref_known(v___x_1464_, 1);
v___y_1407_ = v_a_1452_;
v___y_1408_ = v_a_1454_;
v___y_1409_ = v___y_1282_;
v___y_1410_ = v___y_1283_;
v___y_1411_ = v___y_1284_;
v___y_1412_ = v___y_1285_;
goto v___jp_1406_;
}
else
{
lean_object* v_a_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1472_; 
lean_dec(v_a_1454_);
lean_dec(v_a_1452_);
lean_dec_ref(v_funTypes_1280_);
lean_dec_ref(v___f_1279_);
lean_dec(v___x_1276_);
lean_dec_ref(v___f_1275_);
lean_dec_ref(v_preDefs_1273_);
lean_dec(v___x_1272_);
lean_dec_ref(v_xs_1271_);
lean_dec_ref(v_fixedParamPerms_1270_);
lean_dec_ref(v___x_1268_);
lean_dec_ref(v_recArgInfos_1266_);
v_a_1465_ = lean_ctor_get(v___x_1464_, 0);
v_isSharedCheck_1472_ = !lean_is_exclusive(v___x_1464_);
if (v_isSharedCheck_1472_ == 0)
{
v___x_1467_ = v___x_1464_;
v_isShared_1468_ = v_isSharedCheck_1472_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_a_1465_);
lean_dec(v___x_1464_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1472_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v___x_1470_; 
if (v_isShared_1468_ == 0)
{
v___x_1470_ = v___x_1467_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v_a_1465_);
v___x_1470_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
return v___x_1470_;
}
}
}
}
}
else
{
lean_object* v_a_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1480_; 
lean_dec(v_a_1454_);
lean_dec(v_a_1452_);
lean_dec_ref(v_funTypes_1280_);
lean_dec_ref(v___f_1279_);
lean_dec(v___x_1276_);
lean_dec_ref(v___f_1275_);
lean_dec_ref(v_preDefs_1273_);
lean_dec(v___x_1272_);
lean_dec_ref(v_xs_1271_);
lean_dec_ref(v_fixedParamPerms_1270_);
lean_dec_ref(v___x_1268_);
lean_dec_ref(v_recArgInfos_1266_);
v_a_1473_ = lean_ctor_get(v___x_1455_, 0);
v_isSharedCheck_1480_ = !lean_is_exclusive(v___x_1455_);
if (v_isSharedCheck_1480_ == 0)
{
v___x_1475_ = v___x_1455_;
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_a_1473_);
lean_dec(v___x_1455_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___x_1478_; 
if (v_isShared_1476_ == 0)
{
v___x_1478_ = v___x_1475_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v_a_1473_);
v___x_1478_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
return v___x_1478_;
}
}
}
}
else
{
lean_object* v_a_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1488_; 
lean_dec(v_a_1452_);
lean_dec_ref(v_funTypes_1280_);
lean_dec_ref(v___f_1279_);
lean_dec(v___x_1276_);
lean_dec_ref(v___f_1275_);
lean_dec_ref(v_preDefs_1273_);
lean_dec(v___x_1272_);
lean_dec_ref(v_xs_1271_);
lean_dec_ref(v_fixedParamPerms_1270_);
lean_dec_ref(v___x_1268_);
lean_dec_ref(v_recArgInfos_1266_);
v_a_1481_ = lean_ctor_get(v___x_1453_, 0);
v_isSharedCheck_1488_ = !lean_is_exclusive(v___x_1453_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1483_ = v___x_1453_;
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_a_1481_);
lean_dec(v___x_1453_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v___x_1486_; 
if (v_isShared_1484_ == 0)
{
v___x_1486_ = v___x_1483_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v_a_1481_);
v___x_1486_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
return v___x_1486_;
}
}
}
}
else
{
lean_object* v_a_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1496_; 
lean_dec_ref(v_funTypes_1280_);
lean_dec_ref(v___f_1279_);
lean_dec(v___x_1276_);
lean_dec_ref(v___f_1275_);
lean_dec_ref(v_preDefs_1273_);
lean_dec(v___x_1272_);
lean_dec_ref(v_xs_1271_);
lean_dec_ref(v_fixedParamPerms_1270_);
lean_dec_ref(v___x_1268_);
lean_dec_ref(v_recArgInfos_1266_);
v_a_1489_ = lean_ctor_get(v___x_1451_, 0);
v_isSharedCheck_1496_ = !lean_is_exclusive(v___x_1451_);
if (v_isSharedCheck_1496_ == 0)
{
v___x_1491_ = v___x_1451_;
v_isShared_1492_ = v_isSharedCheck_1496_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_a_1489_);
lean_dec(v___x_1451_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1496_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
lean_object* v___x_1494_; 
if (v_isShared_1492_ == 0)
{
v___x_1494_ = v___x_1491_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v_a_1489_);
v___x_1494_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
return v___x_1494_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_recArgInfos_1266_ = stack[0].m_obj;
lean_object* v_a_1267_ = stack[1].m_obj;
lean_object* v___x_1268_ = stack[2].m_obj;
size_t v___x_1269_ = stack[3].m_num;
lean_object* v_fixedParamPerms_1270_ = stack[4].m_obj;
lean_object* v_xs_1271_ = stack[5].m_obj;
lean_object* v___x_1272_ = stack[6].m_obj;
lean_object* v_preDefs_1273_ = stack[7].m_obj;
lean_object* v_numIndices_1274_ = stack[8].m_obj;
lean_object* v___f_1275_ = stack[9].m_obj;
lean_object* v___x_1276_ = stack[10].m_obj;
uint8_t v_a_1277_ = stack[11].m_num;
lean_object* v___x_1278_ = stack[12].m_obj;
lean_object* v___f_1279_ = stack[13].m_obj;
lean_object* v_funTypes_1280_ = stack[14].m_obj;
lean_object* v_motives_1281_ = stack[15].m_obj;
lean_object* v___y_1282_ = stack[16].m_obj;
lean_object* v___y_1283_ = stack[17].m_obj;
lean_object* v___y_1284_ = stack[18].m_obj;
lean_object* v___y_1285_ = stack[19].m_obj;
lean_object* v_res_1529_;
v_res_1529_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2(v_recArgInfos_1266_, v_a_1267_, v___x_1268_, v___x_1269_, v_fixedParamPerms_1270_, v_xs_1271_, v___x_1272_, v_preDefs_1273_, v_numIndices_1274_, v___f_1275_, v___x_1276_, v_a_1277_, v___x_1278_, v___f_1279_, v_funTypes_1280_, v_motives_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_);
stack->m_obj
 = v_res_1529_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___boxed(lean_object** _args){
lean_object* v_recArgInfos_1530_ = _args[0];
lean_object* v_a_1531_ = _args[1];
lean_object* v___x_1532_ = _args[2];
lean_object* v___x_1533_ = _args[3];
lean_object* v_fixedParamPerms_1534_ = _args[4];
lean_object* v_xs_1535_ = _args[5];
lean_object* v___x_1536_ = _args[6];
lean_object* v_preDefs_1537_ = _args[7];
lean_object* v_numIndices_1538_ = _args[8];
lean_object* v___f_1539_ = _args[9];
lean_object* v___x_1540_ = _args[10];
lean_object* v_a_1541_ = _args[11];
lean_object* v___x_1542_ = _args[12];
lean_object* v___f_1543_ = _args[13];
lean_object* v_funTypes_1544_ = _args[14];
lean_object* v_motives_1545_ = _args[15];
lean_object* v___y_1546_ = _args[16];
lean_object* v___y_1547_ = _args[17];
lean_object* v___y_1548_ = _args[18];
lean_object* v___y_1549_ = _args[19];
lean_object* v___y_1550_ = _args[20];
_start:
{
size_t v___x_27427__boxed_1551_; uint8_t v_a_27431__boxed_1552_; lean_object* v_res_1553_; 
v___x_27427__boxed_1551_ = lean_unbox_usize(v___x_1533_);
lean_dec(v___x_1533_);
v_a_27431__boxed_1552_ = lean_unbox(v_a_1541_);
v_res_1553_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2(v_recArgInfos_1530_, v_a_1531_, v___x_1532_, v___x_27427__boxed_1551_, v_fixedParamPerms_1534_, v_xs_1535_, v___x_1536_, v_preDefs_1537_, v_numIndices_1538_, v___f_1539_, v___x_1540_, v_a_27431__boxed_1552_, v___x_1542_, v___f_1543_, v_funTypes_1544_, v_motives_1545_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_);
lean_dec(v___y_1549_);
lean_dec_ref(v___y_1548_);
lean_dec(v___y_1547_);
lean_dec_ref(v___y_1546_);
lean_dec_ref(v___x_1542_);
lean_dec(v_numIndices_1538_);
lean_dec_ref(v_a_1531_);
return v_res_1553_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___redArg(lean_object* v_a_1554_, lean_object* v_funTypes_1555_, size_t v_sz_1556_, size_t v_i_1557_, lean_object* v_bs_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_){
_start:
{
uint8_t v___x_1564_; 
v___x_1564_ = lean_usize_dec_lt(v_i_1557_, v_sz_1556_);
if (v___x_1564_ == 0)
{
lean_object* v___x_1565_; 
v___x_1565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1565_, 0, v_bs_1558_);
return v___x_1565_;
}
else
{
lean_object* v___x_1566_; lean_object* v_v_1567_; lean_object* v___x_1568_; lean_object* v_bs_x27_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; 
v___x_1566_ = l_Lean_instInhabitedExpr;
v_v_1567_ = lean_array_uget(v_bs_1558_, v_i_1557_);
v___x_1568_ = lean_unsigned_to_nat(0u);
v_bs_x27_1569_ = lean_array_uset(v_bs_1558_, v_i_1557_, v___x_1568_);
v___x_1570_ = lean_usize_to_nat(v_i_1557_);
v___x_1571_ = lean_array_get_borrowed(v___x_1566_, v_a_1554_, v___x_1570_);
v___x_1572_ = lean_array_get_borrowed(v___x_1566_, v_funTypes_1555_, v___x_1570_);
lean_dec(v___x_1570_);
lean_inc(v___x_1572_);
lean_inc(v___x_1571_);
v___x_1573_ = l_Lean_Elab_Structural_mkIndPredBRecOnMotive(v_v_1567_, v___x_1571_, v___x_1572_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_);
if (lean_obj_tag(v___x_1573_) == 0)
{
lean_object* v_a_1574_; size_t v___x_1575_; size_t v___x_1576_; lean_object* v___x_1577_; 
v_a_1574_ = lean_ctor_get(v___x_1573_, 0);
lean_inc(v_a_1574_);
lean_dec_ref_known(v___x_1573_, 1);
v___x_1575_ = ((size_t)1ULL);
v___x_1576_ = lean_usize_add(v_i_1557_, v___x_1575_);
v___x_1577_ = lean_array_uset(v_bs_x27_1569_, v_i_1557_, v_a_1574_);
v_i_1557_ = v___x_1576_;
v_bs_1558_ = v___x_1577_;
goto _start;
}
else
{
lean_object* v_a_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1586_; 
lean_dec_ref(v_bs_x27_1569_);
v_a_1579_ = lean_ctor_get(v___x_1573_, 0);
v_isSharedCheck_1586_ = !lean_is_exclusive(v___x_1573_);
if (v_isSharedCheck_1586_ == 0)
{
v___x_1581_ = v___x_1573_;
v_isShared_1582_ = v_isSharedCheck_1586_;
goto v_resetjp_1580_;
}
else
{
lean_inc(v_a_1579_);
lean_dec(v___x_1573_);
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
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1554_ = stack[0].m_obj;
lean_object* v_funTypes_1555_ = stack[1].m_obj;
size_t v_sz_1556_ = stack[2].m_num;
size_t v_i_1557_ = stack[3].m_num;
lean_object* v_bs_1558_ = stack[4].m_obj;
lean_object* v___y_1559_ = stack[5].m_obj;
lean_object* v___y_1560_ = stack[6].m_obj;
lean_object* v___y_1561_ = stack[7].m_obj;
lean_object* v___y_1562_ = stack[8].m_obj;
lean_object* v_res_1587_;
v_res_1587_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___redArg(v_a_1554_, v_funTypes_1555_, v_sz_1556_, v_i_1557_, v_bs_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_);
stack->m_obj
 = v_res_1587_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___redArg___boxed(lean_object* v_a_1588_, lean_object* v_funTypes_1589_, lean_object* v_sz_1590_, lean_object* v_i_1591_, lean_object* v_bs_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_){
_start:
{
size_t v_sz_boxed_1598_; size_t v_i_boxed_1599_; lean_object* v_res_1600_; 
v_sz_boxed_1598_ = lean_unbox_usize(v_sz_1590_);
lean_dec(v_sz_1590_);
v_i_boxed_1599_ = lean_unbox_usize(v_i_1591_);
lean_dec(v_i_1591_);
v_res_1600_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___redArg(v_a_1588_, v_funTypes_1589_, v_sz_boxed_1598_, v_i_boxed_1599_, v_bs_1592_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_);
lean_dec(v___y_1596_);
lean_dec_ref(v___y_1595_);
lean_dec(v___y_1594_);
lean_dec_ref(v___y_1593_);
lean_dec_ref(v_funTypes_1589_);
lean_dec_ref(v_a_1588_);
return v_res_1600_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__3(lean_object* v_recArgInfos_1601_, lean_object* v_a_1602_, size_t v___x_1603_, lean_object* v___f_1604_, lean_object* v_funTypes_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_){
_start:
{
size_t v_sz_1611_; lean_object* v___x_1612_; 
v_sz_1611_ = lean_array_size(v_recArgInfos_1601_);
v___x_1612_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___redArg(v_a_1602_, v_funTypes_1605_, v_sz_1611_, v___x_1603_, v_recArgInfos_1601_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_);
if (lean_obj_tag(v___x_1612_) == 0)
{
lean_object* v_a_1613_; lean_object* v___x_1614_; 
v_a_1613_ = lean_ctor_get(v___x_1612_, 0);
lean_inc(v_a_1613_);
lean_dec_ref_known(v___x_1612_, 1);
lean_inc(v___y_1609_);
lean_inc_ref(v___y_1608_);
lean_inc(v___y_1607_);
lean_inc_ref(v___y_1606_);
v___x_1614_ = lean_apply_7(v___f_1604_, v_funTypes_1605_, v_a_1613_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_, lean_box(0));
return v___x_1614_;
}
else
{
lean_object* v_a_1615_; lean_object* v___x_1617_; uint8_t v_isShared_1618_; uint8_t v_isSharedCheck_1622_; 
lean_dec_ref(v_funTypes_1605_);
lean_dec_ref(v___f_1604_);
v_a_1615_ = lean_ctor_get(v___x_1612_, 0);
v_isSharedCheck_1622_ = !lean_is_exclusive(v___x_1612_);
if (v_isSharedCheck_1622_ == 0)
{
v___x_1617_ = v___x_1612_;
v_isShared_1618_ = v_isSharedCheck_1622_;
goto v_resetjp_1616_;
}
else
{
lean_inc(v_a_1615_);
lean_dec(v___x_1612_);
v___x_1617_ = lean_box(0);
v_isShared_1618_ = v_isSharedCheck_1622_;
goto v_resetjp_1616_;
}
v_resetjp_1616_:
{
lean_object* v___x_1620_; 
if (v_isShared_1618_ == 0)
{
v___x_1620_ = v___x_1617_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v_a_1615_);
v___x_1620_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
return v___x_1620_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_recArgInfos_1601_ = stack[0].m_obj;
lean_object* v_a_1602_ = stack[1].m_obj;
size_t v___x_1603_ = stack[2].m_num;
lean_object* v___f_1604_ = stack[3].m_obj;
lean_object* v_funTypes_1605_ = stack[4].m_obj;
lean_object* v___y_1606_ = stack[5].m_obj;
lean_object* v___y_1607_ = stack[6].m_obj;
lean_object* v___y_1608_ = stack[7].m_obj;
lean_object* v___y_1609_ = stack[8].m_obj;
lean_object* v_res_1623_;
v_res_1623_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__3(v_recArgInfos_1601_, v_a_1602_, v___x_1603_, v___f_1604_, v_funTypes_1605_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_);
stack->m_obj
 = v_res_1623_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__3___boxed(lean_object* v_recArgInfos_1624_, lean_object* v_a_1625_, lean_object* v___x_1626_, lean_object* v___f_1627_, lean_object* v_funTypes_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_){
_start:
{
size_t v___x_28331__boxed_1634_; lean_object* v_res_1635_; 
v___x_28331__boxed_1634_ = lean_unbox_usize(v___x_1626_);
lean_dec(v___x_1626_);
v_res_1635_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__3(v_recArgInfos_1624_, v_a_1625_, v___x_28331__boxed_1634_, v___f_1627_, v_funTypes_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_);
lean_dec(v___y_1632_);
lean_dec_ref(v___y_1631_);
lean_dec(v___y_1630_);
lean_dec_ref(v___y_1629_);
lean_dec_ref(v_a_1625_);
return v_res_1635_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___redArg(lean_object* v_a_1636_, lean_object* v_a_1637_, size_t v_sz_1638_, size_t v_i_1639_, lean_object* v_bs_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_){
_start:
{
uint8_t v___x_1646_; 
v___x_1646_ = lean_usize_dec_lt(v_i_1639_, v_sz_1638_);
if (v___x_1646_ == 0)
{
lean_object* v___x_1647_; 
v___x_1647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1647_, 0, v_bs_1640_);
return v___x_1647_;
}
else
{
lean_object* v___x_1648_; lean_object* v_v_1649_; lean_object* v___x_1650_; lean_object* v_bs_x27_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; 
v___x_1648_ = l_Lean_instInhabitedExpr;
v_v_1649_ = lean_array_uget(v_bs_1640_, v_i_1639_);
v___x_1650_ = lean_unsigned_to_nat(0u);
v_bs_x27_1651_ = lean_array_uset(v_bs_1640_, v_i_1639_, v___x_1650_);
v___x_1652_ = lean_usize_to_nat(v_i_1639_);
v___x_1653_ = lean_array_get_borrowed(v___x_1648_, v_a_1636_, v___x_1652_);
v___x_1654_ = lean_array_get_borrowed(v___x_1648_, v_a_1637_, v___x_1652_);
lean_dec(v___x_1652_);
lean_inc(v___x_1654_);
lean_inc(v___x_1653_);
v___x_1655_ = l_Lean_Elab_Structural_mkBRecOnMotive(v_v_1649_, v___x_1653_, v___x_1654_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_);
if (lean_obj_tag(v___x_1655_) == 0)
{
lean_object* v_a_1656_; size_t v___x_1657_; size_t v___x_1658_; lean_object* v___x_1659_; 
v_a_1656_ = lean_ctor_get(v___x_1655_, 0);
lean_inc(v_a_1656_);
lean_dec_ref_known(v___x_1655_, 1);
v___x_1657_ = ((size_t)1ULL);
v___x_1658_ = lean_usize_add(v_i_1639_, v___x_1657_);
v___x_1659_ = lean_array_uset(v_bs_x27_1651_, v_i_1639_, v_a_1656_);
v_i_1639_ = v___x_1658_;
v_bs_1640_ = v___x_1659_;
goto _start;
}
else
{
lean_object* v_a_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1668_; 
lean_dec_ref(v_bs_x27_1651_);
v_a_1661_ = lean_ctor_get(v___x_1655_, 0);
v_isSharedCheck_1668_ = !lean_is_exclusive(v___x_1655_);
if (v_isSharedCheck_1668_ == 0)
{
v___x_1663_ = v___x_1655_;
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_a_1661_);
lean_dec(v___x_1655_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v___x_1666_; 
if (v_isShared_1664_ == 0)
{
v___x_1666_ = v___x_1663_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v_a_1661_);
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
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1636_ = stack[0].m_obj;
lean_object* v_a_1637_ = stack[1].m_obj;
size_t v_sz_1638_ = stack[2].m_num;
size_t v_i_1639_ = stack[3].m_num;
lean_object* v_bs_1640_ = stack[4].m_obj;
lean_object* v___y_1641_ = stack[5].m_obj;
lean_object* v___y_1642_ = stack[6].m_obj;
lean_object* v___y_1643_ = stack[7].m_obj;
lean_object* v___y_1644_ = stack[8].m_obj;
lean_object* v_res_1669_;
v_res_1669_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___redArg(v_a_1636_, v_a_1637_, v_sz_1638_, v_i_1639_, v_bs_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_);
stack->m_obj
 = v_res_1669_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___redArg___boxed(lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_sz_1672_, lean_object* v_i_1673_, lean_object* v_bs_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_){
_start:
{
size_t v_sz_boxed_1680_; size_t v_i_boxed_1681_; lean_object* v_res_1682_; 
v_sz_boxed_1680_ = lean_unbox_usize(v_sz_1672_);
lean_dec(v_sz_1672_);
v_i_boxed_1681_ = lean_unbox_usize(v_i_1673_);
lean_dec(v_i_1673_);
v_res_1682_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___redArg(v_a_1670_, v_a_1671_, v_sz_boxed_1680_, v_i_boxed_1681_, v_bs_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_);
lean_dec(v___y_1678_);
lean_dec_ref(v___y_1677_);
lean_dec(v___y_1676_);
lean_dec_ref(v___y_1675_);
lean_dec_ref(v_a_1671_);
lean_dec_ref(v_a_1670_);
return v_res_1682_;
}
}
lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg(lean_object* v_msg_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_){
_start:
{
lean_object* v_ref_1689_; lean_object* v___x_1690_; lean_object* v_a_1691_; lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1699_; 
v_ref_1689_ = lean_ctor_get(v___y_1686_, 2);
v___x_1690_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11_spec__21(v_msg_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
v_a_1691_ = lean_ctor_get(v___x_1690_, 0);
v_isSharedCheck_1699_ = !lean_is_exclusive(v___x_1690_);
if (v_isSharedCheck_1699_ == 0)
{
v___x_1693_ = v___x_1690_;
v_isShared_1694_ = v_isSharedCheck_1699_;
goto v_resetjp_1692_;
}
else
{
lean_inc(v_a_1691_);
lean_dec(v___x_1690_);
v___x_1693_ = lean_box(0);
v_isShared_1694_ = v_isSharedCheck_1699_;
goto v_resetjp_1692_;
}
v_resetjp_1692_:
{
lean_object* v___x_1695_; lean_object* v___x_1697_; 
lean_inc(v_ref_1689_);
v___x_1695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1695_, 0, v_ref_1689_);
lean_ctor_set(v___x_1695_, 1, v_a_1691_);
if (v_isShared_1694_ == 0)
{
lean_ctor_set_tag(v___x_1693_, 1);
lean_ctor_set(v___x_1693_, 0, v___x_1695_);
v___x_1697_ = v___x_1693_;
goto v_reusejp_1696_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v___x_1695_);
v___x_1697_ = v_reuseFailAlloc_1698_;
goto v_reusejp_1696_;
}
v_reusejp_1696_:
{
return v___x_1697_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1683_ = stack[0].m_obj;
lean_object* v___y_1684_ = stack[1].m_obj;
lean_object* v___y_1685_ = stack[2].m_obj;
lean_object* v___y_1686_ = stack[3].m_obj;
lean_object* v___y_1687_ = stack[4].m_obj;
lean_object* v_res_1700_;
v_res_1700_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg(v_msg_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
stack->m_obj
 = v_res_1700_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg___boxed(lean_object* v_msg_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_){
_start:
{
lean_object* v_res_1707_; 
v_res_1707_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg(v_msg_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
lean_dec(v___y_1705_);
lean_dec_ref(v___y_1704_);
lean_dec(v___y_1703_);
lean_dec_ref(v___y_1702_);
return v_res_1707_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1709_; lean_object* v___x_1710_; 
v___x_1709_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__0));
v___x_1710_ = l_Lean_stringToMessageData(v___x_1709_);
return v___x_1710_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__3(void){
_start:
{
lean_object* v___x_1712_; lean_object* v___x_1713_; 
v___x_1712_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__2));
v___x_1713_ = l_Lean_stringToMessageData(v___x_1712_);
return v___x_1713_;
}
}
lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4(lean_object* v_constName_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_){
_start:
{
lean_object* v___x_1720_; lean_object* v_env_1721_; lean_object* v___x_1722_; 
v___x_1720_ = lean_st_ref_get(v___y_1718_);
v_env_1721_ = lean_ctor_get(v___x_1720_, 0);
lean_inc_ref(v_env_1721_);
lean_dec(v___x_1720_);
lean_inc(v_constName_1714_);
v___x_1722_ = l_Lean_isInductiveCore_x3f(v_env_1721_, v_constName_1714_);
if (lean_obj_tag(v___x_1722_) == 0)
{
lean_object* v___x_1723_; uint8_t v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; 
v___x_1723_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__1, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__1);
v___x_1724_ = 0;
v___x_1725_ = l_Lean_MessageData_ofConstName(v_constName_1714_, v___x_1724_);
v___x_1726_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1726_, 0, v___x_1723_);
lean_ctor_set(v___x_1726_, 1, v___x_1725_);
v___x_1727_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__3, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__3_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__3);
v___x_1728_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1728_, 0, v___x_1726_);
lean_ctor_set(v___x_1728_, 1, v___x_1727_);
v___x_1729_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg(v___x_1728_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_);
return v___x_1729_;
}
else
{
lean_object* v_val_1730_; lean_object* v___x_1732_; uint8_t v_isShared_1733_; uint8_t v_isSharedCheck_1737_; 
lean_dec(v_constName_1714_);
v_val_1730_ = lean_ctor_get(v___x_1722_, 0);
v_isSharedCheck_1737_ = !lean_is_exclusive(v___x_1722_);
if (v_isSharedCheck_1737_ == 0)
{
v___x_1732_ = v___x_1722_;
v_isShared_1733_ = v_isSharedCheck_1737_;
goto v_resetjp_1731_;
}
else
{
lean_inc(v_val_1730_);
lean_dec(v___x_1722_);
v___x_1732_ = lean_box(0);
v_isShared_1733_ = v_isSharedCheck_1737_;
goto v_resetjp_1731_;
}
v_resetjp_1731_:
{
lean_object* v___x_1735_; 
if (v_isShared_1733_ == 0)
{
lean_ctor_set_tag(v___x_1732_, 0);
v___x_1735_ = v___x_1732_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v_val_1730_);
v___x_1735_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
return v___x_1735_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_1714_ = stack[0].m_obj;
lean_object* v___y_1715_ = stack[1].m_obj;
lean_object* v___y_1716_ = stack[2].m_obj;
lean_object* v___y_1717_ = stack[3].m_obj;
lean_object* v___y_1718_ = stack[4].m_obj;
lean_object* v_res_1738_;
v_res_1738_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4(v_constName_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_);
stack->m_obj
 = v_res_1738_;
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___boxed(lean_object* v_constName_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_){
_start:
{
lean_object* v_res_1745_; 
v_res_1745_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4(v_constName_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_);
lean_dec(v___y_1743_);
lean_dec_ref(v___y_1742_);
lean_dec(v___y_1741_);
lean_dec_ref(v___y_1740_);
return v_res_1745_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___redArg(lean_object* v_fixedParamPerms_1746_, lean_object* v_xs_1747_, size_t v_sz_1748_, size_t v_i_1749_, lean_object* v_bs_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_){
_start:
{
uint8_t v___x_1756_; 
v___x_1756_ = lean_usize_dec_lt(v_i_1749_, v_sz_1748_);
if (v___x_1756_ == 0)
{
lean_object* v___x_1757_; 
lean_dec_ref(v_xs_1747_);
v___x_1757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1757_, 0, v_bs_1750_);
return v___x_1757_;
}
else
{
lean_object* v_v_1758_; lean_object* v_perms_1759_; lean_object* v_type_1760_; lean_object* v___x_1761_; lean_object* v_bs_x27_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; 
v_v_1758_ = lean_array_uget_borrowed(v_bs_1750_, v_i_1749_);
v_perms_1759_ = lean_ctor_get(v_fixedParamPerms_1746_, 1);
v_type_1760_ = lean_ctor_get(v_v_1758_, 6);
lean_inc_ref(v_type_1760_);
v___x_1761_ = lean_unsigned_to_nat(0u);
v_bs_x27_1762_ = lean_array_uset(v_bs_1750_, v_i_1749_, v___x_1761_);
v___x_1763_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0);
v___x_1764_ = lean_usize_to_nat(v_i_1749_);
v___x_1765_ = lean_array_get_borrowed(v___x_1763_, v_perms_1759_, v___x_1764_);
lean_dec(v___x_1764_);
lean_inc_ref(v_xs_1747_);
lean_inc(v___x_1765_);
v___x_1766_ = l_Lean_Elab_FixedParamPerm_instantiateForall(v___x_1765_, v_type_1760_, v_xs_1747_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_);
if (lean_obj_tag(v___x_1766_) == 0)
{
lean_object* v_a_1767_; size_t v___x_1768_; size_t v___x_1769_; lean_object* v___x_1770_; 
v_a_1767_ = lean_ctor_get(v___x_1766_, 0);
lean_inc(v_a_1767_);
lean_dec_ref_known(v___x_1766_, 1);
v___x_1768_ = ((size_t)1ULL);
v___x_1769_ = lean_usize_add(v_i_1749_, v___x_1768_);
v___x_1770_ = lean_array_uset(v_bs_x27_1762_, v_i_1749_, v_a_1767_);
v_i_1749_ = v___x_1769_;
v_bs_1750_ = v___x_1770_;
goto _start;
}
else
{
lean_object* v_a_1772_; lean_object* v___x_1774_; uint8_t v_isShared_1775_; uint8_t v_isSharedCheck_1779_; 
lean_dec_ref(v_bs_x27_1762_);
lean_dec_ref(v_xs_1747_);
v_a_1772_ = lean_ctor_get(v___x_1766_, 0);
v_isSharedCheck_1779_ = !lean_is_exclusive(v___x_1766_);
if (v_isSharedCheck_1779_ == 0)
{
v___x_1774_ = v___x_1766_;
v_isShared_1775_ = v_isSharedCheck_1779_;
goto v_resetjp_1773_;
}
else
{
lean_inc(v_a_1772_);
lean_dec(v___x_1766_);
v___x_1774_ = lean_box(0);
v_isShared_1775_ = v_isSharedCheck_1779_;
goto v_resetjp_1773_;
}
v_resetjp_1773_:
{
lean_object* v___x_1777_; 
if (v_isShared_1775_ == 0)
{
v___x_1777_ = v___x_1774_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v_a_1772_);
v___x_1777_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
return v___x_1777_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_fixedParamPerms_1746_ = stack[0].m_obj;
lean_object* v_xs_1747_ = stack[1].m_obj;
size_t v_sz_1748_ = stack[2].m_num;
size_t v_i_1749_ = stack[3].m_num;
lean_object* v_bs_1750_ = stack[4].m_obj;
lean_object* v___y_1751_ = stack[5].m_obj;
lean_object* v___y_1752_ = stack[6].m_obj;
lean_object* v___y_1753_ = stack[7].m_obj;
lean_object* v___y_1754_ = stack[8].m_obj;
lean_object* v_res_1780_;
v_res_1780_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___redArg(v_fixedParamPerms_1746_, v_xs_1747_, v_sz_1748_, v_i_1749_, v_bs_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_);
stack->m_obj
 = v_res_1780_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___redArg___boxed(lean_object* v_fixedParamPerms_1781_, lean_object* v_xs_1782_, lean_object* v_sz_1783_, lean_object* v_i_1784_, lean_object* v_bs_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_){
_start:
{
size_t v_sz_boxed_1791_; size_t v_i_boxed_1792_; lean_object* v_res_1793_; 
v_sz_boxed_1791_ = lean_unbox_usize(v_sz_1783_);
lean_dec(v_sz_1783_);
v_i_boxed_1792_ = lean_unbox_usize(v_i_1784_);
lean_dec(v_i_1784_);
v_res_1793_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___redArg(v_fixedParamPerms_1781_, v_xs_1782_, v_sz_boxed_1791_, v_i_boxed_1792_, v_bs_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_);
lean_dec(v___y_1789_);
lean_dec_ref(v___y_1788_);
lean_dec(v___y_1787_);
lean_dec_ref(v___y_1786_);
lean_dec_ref(v_fixedParamPerms_1781_);
return v_res_1793_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___redArg(lean_object* v_fixedParamPerms_1794_, lean_object* v_xs_1795_, size_t v_sz_1796_, size_t v_i_1797_, lean_object* v_bs_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_){
_start:
{
uint8_t v___x_1804_; 
v___x_1804_ = lean_usize_dec_lt(v_i_1797_, v_sz_1796_);
if (v___x_1804_ == 0)
{
lean_object* v___x_1805_; 
lean_dec_ref(v_xs_1795_);
v___x_1805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1805_, 0, v_bs_1798_);
return v___x_1805_;
}
else
{
lean_object* v_v_1806_; lean_object* v_perms_1807_; lean_object* v_value_1808_; lean_object* v___x_1809_; lean_object* v_bs_x27_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; 
v_v_1806_ = lean_array_uget_borrowed(v_bs_1798_, v_i_1797_);
v_perms_1807_ = lean_ctor_get(v_fixedParamPerms_1794_, 1);
v_value_1808_ = lean_ctor_get(v_v_1806_, 7);
lean_inc_ref(v_value_1808_);
v___x_1809_ = lean_unsigned_to_nat(0u);
v_bs_x27_1810_ = lean_array_uset(v_bs_1798_, v_i_1797_, v___x_1809_);
v___x_1811_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0);
v___x_1812_ = lean_usize_to_nat(v_i_1797_);
v___x_1813_ = lean_array_get_borrowed(v___x_1811_, v_perms_1807_, v___x_1812_);
lean_dec(v___x_1812_);
lean_inc_ref(v_xs_1795_);
lean_inc(v___x_1813_);
v___x_1814_ = l_Lean_Elab_FixedParamPerm_instantiateLambda(v___x_1813_, v_value_1808_, v_xs_1795_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_);
if (lean_obj_tag(v___x_1814_) == 0)
{
lean_object* v_a_1815_; size_t v___x_1816_; size_t v___x_1817_; lean_object* v___x_1818_; 
v_a_1815_ = lean_ctor_get(v___x_1814_, 0);
lean_inc(v_a_1815_);
lean_dec_ref_known(v___x_1814_, 1);
v___x_1816_ = ((size_t)1ULL);
v___x_1817_ = lean_usize_add(v_i_1797_, v___x_1816_);
v___x_1818_ = lean_array_uset(v_bs_x27_1810_, v_i_1797_, v_a_1815_);
v_i_1797_ = v___x_1817_;
v_bs_1798_ = v___x_1818_;
goto _start;
}
else
{
lean_object* v_a_1820_; lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1827_; 
lean_dec_ref(v_bs_x27_1810_);
lean_dec_ref(v_xs_1795_);
v_a_1820_ = lean_ctor_get(v___x_1814_, 0);
v_isSharedCheck_1827_ = !lean_is_exclusive(v___x_1814_);
if (v_isSharedCheck_1827_ == 0)
{
v___x_1822_ = v___x_1814_;
v_isShared_1823_ = v_isSharedCheck_1827_;
goto v_resetjp_1821_;
}
else
{
lean_inc(v_a_1820_);
lean_dec(v___x_1814_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1827_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
lean_object* v___x_1825_; 
if (v_isShared_1823_ == 0)
{
v___x_1825_ = v___x_1822_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v_a_1820_);
v___x_1825_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
return v___x_1825_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_fixedParamPerms_1794_ = stack[0].m_obj;
lean_object* v_xs_1795_ = stack[1].m_obj;
size_t v_sz_1796_ = stack[2].m_num;
size_t v_i_1797_ = stack[3].m_num;
lean_object* v_bs_1798_ = stack[4].m_obj;
lean_object* v___y_1799_ = stack[5].m_obj;
lean_object* v___y_1800_ = stack[6].m_obj;
lean_object* v___y_1801_ = stack[7].m_obj;
lean_object* v___y_1802_ = stack[8].m_obj;
lean_object* v_res_1828_;
v_res_1828_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___redArg(v_fixedParamPerms_1794_, v_xs_1795_, v_sz_1796_, v_i_1797_, v_bs_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_);
stack->m_obj
 = v_res_1828_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___redArg___boxed(lean_object* v_fixedParamPerms_1829_, lean_object* v_xs_1830_, lean_object* v_sz_1831_, lean_object* v_i_1832_, lean_object* v_bs_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_){
_start:
{
size_t v_sz_boxed_1839_; size_t v_i_boxed_1840_; lean_object* v_res_1841_; 
v_sz_boxed_1839_ = lean_unbox_usize(v_sz_1831_);
lean_dec(v_sz_1831_);
v_i_boxed_1840_ = lean_unbox_usize(v_i_1832_);
lean_dec(v_i_1832_);
v_res_1841_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___redArg(v_fixedParamPerms_1829_, v_xs_1830_, v_sz_boxed_1839_, v_i_boxed_1840_, v_bs_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_);
lean_dec(v___y_1837_);
lean_dec_ref(v___y_1836_);
lean_dec(v___y_1835_);
lean_dec_ref(v___y_1834_);
lean_dec_ref(v_fixedParamPerms_1829_);
return v_res_1841_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11___redArg(lean_object* v_hi_1842_, lean_object* v_pivot_1843_, lean_object* v_as_1844_, lean_object* v_i_1845_, lean_object* v_k_1846_){
_start:
{
uint8_t v___x_1847_; 
v___x_1847_ = lean_nat_dec_lt(v_k_1846_, v_hi_1842_);
if (v___x_1847_ == 0)
{
lean_object* v___x_1848_; lean_object* v___x_1849_; 
lean_dec(v_k_1846_);
v___x_1848_ = lean_array_fswap(v_as_1844_, v_i_1845_, v_hi_1842_);
v___x_1849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1849_, 0, v_i_1845_);
lean_ctor_set(v___x_1849_, 1, v___x_1848_);
return v___x_1849_;
}
else
{
lean_object* v___x_1850_; uint8_t v___x_1851_; 
v___x_1850_ = lean_array_fget_borrowed(v_as_1844_, v_k_1846_);
v___x_1851_ = l_Nat_blt(v___x_1850_, v_pivot_1843_);
if (v___x_1851_ == 0)
{
lean_object* v___x_1852_; lean_object* v___x_1853_; 
v___x_1852_ = lean_unsigned_to_nat(1u);
v___x_1853_ = lean_nat_add(v_k_1846_, v___x_1852_);
lean_dec(v_k_1846_);
v_k_1846_ = v___x_1853_;
goto _start;
}
else
{
lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; 
v___x_1855_ = lean_array_fswap(v_as_1844_, v_i_1845_, v_k_1846_);
v___x_1856_ = lean_unsigned_to_nat(1u);
v___x_1857_ = lean_nat_add(v_i_1845_, v___x_1856_);
lean_dec(v_i_1845_);
v___x_1858_ = lean_nat_add(v_k_1846_, v___x_1856_);
lean_dec(v_k_1846_);
v_as_1844_ = v___x_1855_;
v_i_1845_ = v___x_1857_;
v_k_1846_ = v___x_1858_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11___redArg___boxed(lean_object* v_hi_1860_, lean_object* v_pivot_1861_, lean_object* v_as_1862_, lean_object* v_i_1863_, lean_object* v_k_1864_){
_start:
{
lean_object* v_res_1865_; 
v_res_1865_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11___redArg(v_hi_1860_, v_pivot_1861_, v_as_1862_, v_i_1863_, v_k_1864_);
lean_dec(v_pivot_1861_);
lean_dec(v_hi_1860_);
return v_res_1865_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg(lean_object* v_n_1866_, lean_object* v_as_1867_, lean_object* v_lo_1868_, lean_object* v_hi_1869_){
_start:
{
lean_object* v___y_1871_; uint8_t v___x_1881_; 
v___x_1881_ = lean_nat_dec_lt(v_lo_1868_, v_hi_1869_);
if (v___x_1881_ == 0)
{
lean_dec(v_lo_1868_);
return v_as_1867_;
}
else
{
lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v_mid_1884_; lean_object* v___y_1886_; lean_object* v___y_1892_; lean_object* v___x_1897_; lean_object* v___x_1898_; uint8_t v___x_1899_; 
v___x_1882_ = lean_nat_add(v_lo_1868_, v_hi_1869_);
v___x_1883_ = lean_unsigned_to_nat(1u);
v_mid_1884_ = lean_nat_shiftr(v___x_1882_, v___x_1883_);
lean_dec(v___x_1882_);
v___x_1897_ = lean_array_fget_borrowed(v_as_1867_, v_mid_1884_);
v___x_1898_ = lean_array_fget_borrowed(v_as_1867_, v_lo_1868_);
v___x_1899_ = l_Nat_blt(v___x_1897_, v___x_1898_);
if (v___x_1899_ == 0)
{
v___y_1892_ = v_as_1867_;
goto v___jp_1891_;
}
else
{
lean_object* v___x_1900_; 
v___x_1900_ = lean_array_fswap(v_as_1867_, v_lo_1868_, v_mid_1884_);
v___y_1892_ = v___x_1900_;
goto v___jp_1891_;
}
v___jp_1885_:
{
lean_object* v___x_1887_; lean_object* v___x_1888_; uint8_t v___x_1889_; 
v___x_1887_ = lean_array_fget_borrowed(v___y_1886_, v_mid_1884_);
v___x_1888_ = lean_array_fget_borrowed(v___y_1886_, v_hi_1869_);
v___x_1889_ = l_Nat_blt(v___x_1887_, v___x_1888_);
if (v___x_1889_ == 0)
{
lean_dec(v_mid_1884_);
v___y_1871_ = v___y_1886_;
goto v___jp_1870_;
}
else
{
lean_object* v___x_1890_; 
v___x_1890_ = lean_array_fswap(v___y_1886_, v_mid_1884_, v_hi_1869_);
lean_dec(v_mid_1884_);
v___y_1871_ = v___x_1890_;
goto v___jp_1870_;
}
}
v___jp_1891_:
{
lean_object* v___x_1893_; lean_object* v___x_1894_; uint8_t v___x_1895_; 
v___x_1893_ = lean_array_fget_borrowed(v___y_1892_, v_hi_1869_);
v___x_1894_ = lean_array_fget_borrowed(v___y_1892_, v_lo_1868_);
v___x_1895_ = l_Nat_blt(v___x_1893_, v___x_1894_);
if (v___x_1895_ == 0)
{
v___y_1886_ = v___y_1892_;
goto v___jp_1885_;
}
else
{
lean_object* v___x_1896_; 
v___x_1896_ = lean_array_fswap(v___y_1892_, v_lo_1868_, v_hi_1869_);
v___y_1886_ = v___x_1896_;
goto v___jp_1885_;
}
}
}
v___jp_1870_:
{
lean_object* v_pivot_1872_; lean_object* v___x_1873_; lean_object* v_fst_1874_; lean_object* v_snd_1875_; uint8_t v___x_1876_; 
v_pivot_1872_ = lean_array_fget(v___y_1871_, v_hi_1869_);
lean_inc_n(v_lo_1868_, 2);
v___x_1873_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11___redArg(v_hi_1869_, v_pivot_1872_, v___y_1871_, v_lo_1868_, v_lo_1868_);
lean_dec(v_pivot_1872_);
v_fst_1874_ = lean_ctor_get(v___x_1873_, 0);
lean_inc(v_fst_1874_);
v_snd_1875_ = lean_ctor_get(v___x_1873_, 1);
lean_inc(v_snd_1875_);
lean_dec_ref(v___x_1873_);
v___x_1876_ = lean_nat_dec_le(v_hi_1869_, v_fst_1874_);
if (v___x_1876_ == 0)
{
lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; 
v___x_1877_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg(v_n_1866_, v_snd_1875_, v_lo_1868_, v_fst_1874_);
v___x_1878_ = lean_unsigned_to_nat(1u);
v___x_1879_ = lean_nat_add(v_fst_1874_, v___x_1878_);
lean_dec(v_fst_1874_);
v_as_1867_ = v___x_1877_;
v_lo_1868_ = v___x_1879_;
goto _start;
}
else
{
lean_dec(v_fst_1874_);
lean_dec(v_lo_1868_);
return v_snd_1875_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg___boxed(lean_object* v_n_1901_, lean_object* v_as_1902_, lean_object* v_lo_1903_, lean_object* v_hi_1904_){
_start:
{
lean_object* v_res_1905_; 
v_res_1905_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg(v_n_1901_, v_as_1902_, v_lo_1903_, v_hi_1904_);
lean_dec(v_hi_1904_);
lean_dec(v_n_1901_);
return v_res_1905_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__6(lean_object* v_xs_1906_, lean_object* v_f_1907_, lean_object* v_x_1908_, lean_object* v_as_1909_, size_t v_i_1910_, size_t v_stop_1911_, lean_object* v_b_1912_){
_start:
{
lean_object* v___y_1914_; uint8_t v___x_1918_; 
v___x_1918_ = lean_usize_dec_eq(v_i_1910_, v_stop_1911_);
if (v___x_1918_ == 0)
{
lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; uint8_t v___x_1923_; 
v___x_1919_ = l_Lean_Elab_Structural_instInhabitedRecArgInfo_default;
v___x_1920_ = lean_array_uget_borrowed(v_as_1909_, v_i_1910_);
v___x_1921_ = lean_array_get_borrowed(v___x_1919_, v_xs_1906_, v___x_1920_);
lean_inc_ref(v_f_1907_);
lean_inc(v___x_1921_);
v___x_1922_ = lean_apply_1(v_f_1907_, v___x_1921_);
v___x_1923_ = lean_nat_dec_eq(v___x_1922_, v_x_1908_);
lean_dec(v___x_1922_);
if (v___x_1923_ == 0)
{
v___y_1914_ = v_b_1912_;
goto v___jp_1913_;
}
else
{
lean_object* v___x_1924_; 
lean_inc(v___x_1920_);
v___x_1924_ = lean_array_push(v_b_1912_, v___x_1920_);
v___y_1914_ = v___x_1924_;
goto v___jp_1913_;
}
}
else
{
lean_dec_ref(v_f_1907_);
return v_b_1912_;
}
v___jp_1913_:
{
size_t v___x_1915_; size_t v___x_1916_; 
v___x_1915_ = ((size_t)1ULL);
v___x_1916_ = lean_usize_add(v_i_1910_, v___x_1915_);
v_i_1910_ = v___x_1916_;
v_b_1912_ = v___y_1914_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_1906_ = stack[0].m_obj;
lean_object* v_f_1907_ = stack[1].m_obj;
lean_object* v_x_1908_ = stack[2].m_obj;
lean_object* v_as_1909_ = stack[3].m_obj;
size_t v_i_1910_ = stack[4].m_num;
size_t v_stop_1911_ = stack[5].m_num;
lean_object* v_b_1912_ = stack[6].m_obj;
lean_object* v_res_1925_;
v_res_1925_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__6(v_xs_1906_, v_f_1907_, v_x_1908_, v_as_1909_, v_i_1910_, v_stop_1911_, v_b_1912_);
stack->m_obj
 = v_res_1925_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__6___boxed(lean_object* v_xs_1926_, lean_object* v_f_1927_, lean_object* v_x_1928_, lean_object* v_as_1929_, lean_object* v_i_1930_, lean_object* v_stop_1931_, lean_object* v_b_1932_){
_start:
{
size_t v_i_boxed_1933_; size_t v_stop_boxed_1934_; lean_object* v_res_1935_; 
v_i_boxed_1933_ = lean_unbox_usize(v_i_1930_);
lean_dec(v_i_1930_);
v_stop_boxed_1934_ = lean_unbox_usize(v_stop_1931_);
lean_dec(v_stop_1931_);
v_res_1935_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__6(v_xs_1926_, v_f_1927_, v_x_1928_, v_as_1929_, v_i_boxed_1933_, v_stop_boxed_1934_, v_b_1932_);
lean_dec_ref(v_as_1929_);
lean_dec(v_x_1928_);
lean_dec_ref(v_xs_1926_);
return v_res_1935_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8(lean_object* v_xs_1938_, lean_object* v_f_1939_, size_t v_sz_1940_, size_t v_i_1941_, lean_object* v_bs_1942_){
_start:
{
uint8_t v___x_1943_; 
v___x_1943_ = lean_usize_dec_lt(v_i_1941_, v_sz_1940_);
if (v___x_1943_ == 0)
{
lean_dec_ref(v_f_1939_);
return v_bs_1942_;
}
else
{
lean_object* v_v_1944_; lean_object* v___x_1945_; lean_object* v_bs_x27_1946_; lean_object* v___y_1948_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; uint8_t v___x_1957_; 
v_v_1944_ = lean_array_uget(v_bs_1942_, v_i_1941_);
v___x_1945_ = lean_unsigned_to_nat(0u);
v_bs_x27_1946_ = lean_array_uset(v_bs_1942_, v_i_1941_, v___x_1945_);
v___x_1953_ = lean_array_get_size(v_xs_1938_);
v___x_1954_ = l_Array_range(v___x_1953_);
v___x_1955_ = lean_array_get_size(v___x_1954_);
v___x_1956_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8___closed__0));
v___x_1957_ = lean_nat_dec_lt(v___x_1945_, v___x_1955_);
if (v___x_1957_ == 0)
{
lean_dec_ref(v___x_1954_);
lean_dec(v_v_1944_);
v___y_1948_ = v___x_1956_;
goto v___jp_1947_;
}
else
{
size_t v___x_1958_; size_t v___x_1959_; lean_object* v___x_1960_; 
v___x_1958_ = ((size_t)0ULL);
v___x_1959_ = lean_usize_of_nat(v___x_1955_);
lean_inc_ref(v_f_1939_);
v___x_1960_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__6(v_xs_1938_, v_f_1939_, v_v_1944_, v___x_1954_, v___x_1958_, v___x_1959_, v___x_1956_);
lean_dec_ref(v___x_1954_);
lean_dec(v_v_1944_);
v___y_1948_ = v___x_1960_;
goto v___jp_1947_;
}
v___jp_1947_:
{
size_t v___x_1949_; size_t v___x_1950_; lean_object* v___x_1951_; 
v___x_1949_ = ((size_t)1ULL);
v___x_1950_ = lean_usize_add(v_i_1941_, v___x_1949_);
v___x_1951_ = lean_array_uset(v_bs_x27_1946_, v_i_1941_, v___y_1948_);
v_i_1941_ = v___x_1950_;
v_bs_1942_ = v___x_1951_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_1938_ = stack[0].m_obj;
lean_object* v_f_1939_ = stack[1].m_obj;
size_t v_sz_1940_ = stack[2].m_num;
size_t v_i_1941_ = stack[3].m_num;
lean_object* v_bs_1942_ = stack[4].m_obj;
lean_object* v_res_1961_;
v_res_1961_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8(v_xs_1938_, v_f_1939_, v_sz_1940_, v_i_1941_, v_bs_1942_);
stack->m_obj
 = v_res_1961_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8___boxed(lean_object* v_xs_1962_, lean_object* v_f_1963_, lean_object* v_sz_1964_, lean_object* v_i_1965_, lean_object* v_bs_1966_){
_start:
{
size_t v_sz_boxed_1967_; size_t v_i_boxed_1968_; lean_object* v_res_1969_; 
v_sz_boxed_1967_ = lean_unbox_usize(v_sz_1964_);
lean_dec(v_sz_1964_);
v_i_boxed_1968_ = lean_unbox_usize(v_i_1965_);
lean_dec(v_i_1965_);
v_res_1969_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8(v_xs_1962_, v_f_1963_, v_sz_boxed_1967_, v_i_boxed_1968_, v_bs_1966_);
lean_dec_ref(v_xs_1962_);
return v_res_1969_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__11(lean_object* v_as_1970_, size_t v_i_1971_, size_t v_stop_1972_, lean_object* v_b_1973_){
_start:
{
uint8_t v___x_1974_; 
v___x_1974_ = lean_usize_dec_eq(v_i_1971_, v_stop_1972_);
if (v___x_1974_ == 0)
{
lean_object* v___x_1975_; lean_object* v___x_1976_; size_t v___x_1977_; size_t v___x_1978_; 
v___x_1975_ = lean_array_uget_borrowed(v_as_1970_, v_i_1971_);
v___x_1976_ = l_Array_append___redArg(v_b_1973_, v___x_1975_);
v___x_1977_ = ((size_t)1ULL);
v___x_1978_ = lean_usize_add(v_i_1971_, v___x_1977_);
v_i_1971_ = v___x_1978_;
v_b_1973_ = v___x_1976_;
goto _start;
}
else
{
return v_b_1973_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1970_ = stack[0].m_obj;
size_t v_i_1971_ = stack[1].m_num;
size_t v_stop_1972_ = stack[2].m_num;
lean_object* v_b_1973_ = stack[3].m_obj;
lean_object* v_res_1980_;
v_res_1980_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__11(v_as_1970_, v_i_1971_, v_stop_1972_, v_b_1973_);
stack->m_obj
 = v_res_1980_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__11___boxed(lean_object* v_as_1981_, lean_object* v_i_1982_, lean_object* v_stop_1983_, lean_object* v_b_1984_){
_start:
{
size_t v_i_boxed_1985_; size_t v_stop_boxed_1986_; lean_object* v_res_1987_; 
v_i_boxed_1985_ = lean_unbox_usize(v_i_1982_);
lean_dec(v_i_1982_);
v_stop_boxed_1986_ = lean_unbox_usize(v_stop_1983_);
lean_dec(v_stop_1983_);
v_res_1987_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__11(v_as_1981_, v_i_boxed_1985_, v_stop_boxed_1986_, v_b_1984_);
lean_dec_ref(v_as_1981_);
return v_res_1987_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__7(lean_object* v_msg_1988_){
_start:
{
lean_object* v___x_1989_; lean_object* v___x_1990_; 
v___x_1989_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0);
v___x_1990_ = lean_panic_fn_borrowed(v___x_1989_, v_msg_1988_);
return v___x_1990_;
}
}
uint8_t l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9___redArg(lean_object* v_xs_1991_, lean_object* v_ys_1992_, lean_object* v_x_1993_){
_start:
{
lean_object* v_zero_1994_; uint8_t v_isZero_1995_; 
v_zero_1994_ = lean_unsigned_to_nat(0u);
v_isZero_1995_ = lean_nat_dec_eq(v_x_1993_, v_zero_1994_);
if (v_isZero_1995_ == 1)
{
lean_dec(v_x_1993_);
return v_isZero_1995_;
}
else
{
lean_object* v_one_1996_; lean_object* v_n_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; uint8_t v___x_2000_; 
v_one_1996_ = lean_unsigned_to_nat(1u);
v_n_1997_ = lean_nat_sub(v_x_1993_, v_one_1996_);
lean_dec(v_x_1993_);
v___x_1998_ = lean_array_fget_borrowed(v_xs_1991_, v_n_1997_);
v___x_1999_ = lean_array_fget_borrowed(v_ys_1992_, v_n_1997_);
v___x_2000_ = lean_nat_dec_eq(v___x_1998_, v___x_1999_);
if (v___x_2000_ == 0)
{
lean_dec(v_n_1997_);
return v___x_2000_;
}
else
{
v_x_1993_ = v_n_1997_;
goto _start;
}
}
}
}
LEAN_EXPORT void l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_1991_ = stack[0].m_obj;
lean_object* v_ys_1992_ = stack[1].m_obj;
lean_object* v_x_1993_ = stack[2].m_obj;
uint8_t v_res_2002_;
v_res_2002_ = l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9___redArg(v_xs_1991_, v_ys_1992_, v_x_1993_);
stack->m_num = v_res_2002_;
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9___redArg___boxed(lean_object* v_xs_2003_, lean_object* v_ys_2004_, lean_object* v_x_2005_){
_start:
{
uint8_t v_res_2006_; lean_object* v_r_2007_; 
v_res_2006_ = l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9___redArg(v_xs_2003_, v_ys_2004_, v_x_2005_);
lean_dec_ref(v_ys_2004_);
lean_dec_ref(v_xs_2003_);
v_r_2007_ = lean_box(v_res_2006_);
return v_r_2007_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__2(void){
_start:
{
lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; 
v___x_2010_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__1));
v___x_2011_ = lean_unsigned_to_nat(2u);
v___x_2012_ = lean_unsigned_to_nat(63u);
v___x_2013_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__0));
v___x_2014_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__0));
v___x_2015_ = l_mkPanicMessageWithDecl(v___x_2014_, v___x_2013_, v___x_2012_, v___x_2011_, v___x_2010_);
return v___x_2015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5(lean_object* v_f_2018_, lean_object* v_xs_2019_, lean_object* v_ys_2020_){
_start:
{
size_t v_sz_2024_; size_t v___x_2025_; lean_object* v_positions_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___y_2030_; lean_object* v___y_2036_; lean_object* v___y_2037_; lean_object* v___y_2038_; lean_object* v___y_2039_; lean_object* v___y_2042_; lean_object* v___y_2043_; lean_object* v___y_2044_; lean_object* v___y_2045_; lean_object* v___y_2048_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; uint8_t v___x_2058_; 
v_sz_2024_ = lean_array_size(v_ys_2020_);
v___x_2025_ = ((size_t)0ULL);
v_positions_2026_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8(v_xs_2019_, v_f_2018_, v_sz_2024_, v___x_2025_, v_ys_2020_);
v___x_2027_ = lean_array_get_size(v_xs_2019_);
v___x_2028_ = l_Array_range(v___x_2027_);
v___x_2055_ = lean_unsigned_to_nat(0u);
v___x_2056_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__3));
v___x_2057_ = lean_array_get_size(v_positions_2026_);
v___x_2058_ = lean_nat_dec_lt(v___x_2055_, v___x_2057_);
if (v___x_2058_ == 0)
{
v___y_2048_ = v___x_2056_;
goto v___jp_2047_;
}
else
{
size_t v___x_2059_; lean_object* v___x_2060_; 
v___x_2059_ = lean_usize_of_nat(v___x_2057_);
v___x_2060_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__11(v_positions_2026_, v___x_2025_, v___x_2059_, v___x_2056_);
v___y_2048_ = v___x_2060_;
goto v___jp_2047_;
}
v___jp_2021_:
{
lean_object* v___x_2022_; lean_object* v___x_2023_; 
v___x_2022_ = lean_obj_once(&l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__2, &l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__2_once, _init_l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__2);
v___x_2023_ = l_panic___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__7(v___x_2022_);
return v___x_2023_;
}
v___jp_2029_:
{
lean_object* v___x_2031_; lean_object* v___x_2032_; uint8_t v___x_2033_; 
v___x_2031_ = lean_array_get_size(v___x_2028_);
v___x_2032_ = lean_array_get_size(v___y_2030_);
v___x_2033_ = lean_nat_dec_eq(v___x_2031_, v___x_2032_);
if (v___x_2033_ == 0)
{
lean_dec_ref(v___y_2030_);
lean_dec_ref(v___x_2028_);
lean_dec_ref(v_positions_2026_);
goto v___jp_2021_;
}
else
{
uint8_t v___x_2034_; 
v___x_2034_ = l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9___redArg(v___x_2028_, v___y_2030_, v___x_2031_);
lean_dec_ref(v___y_2030_);
lean_dec_ref(v___x_2028_);
if (v___x_2034_ == 0)
{
lean_dec_ref(v_positions_2026_);
goto v___jp_2021_;
}
else
{
return v_positions_2026_;
}
}
}
v___jp_2035_:
{
lean_object* v___x_2040_; 
v___x_2040_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg(v___y_2038_, v___y_2036_, v___y_2037_, v___y_2039_);
lean_dec(v___y_2039_);
lean_dec(v___y_2038_);
v___y_2030_ = v___x_2040_;
goto v___jp_2029_;
}
v___jp_2041_:
{
uint8_t v___x_2046_; 
v___x_2046_ = lean_nat_dec_le(v___y_2045_, v___y_2043_);
if (v___x_2046_ == 0)
{
lean_dec(v___y_2043_);
lean_inc(v___y_2045_);
v___y_2036_ = v___y_2042_;
v___y_2037_ = v___y_2045_;
v___y_2038_ = v___y_2044_;
v___y_2039_ = v___y_2045_;
goto v___jp_2035_;
}
else
{
v___y_2036_ = v___y_2042_;
v___y_2037_ = v___y_2045_;
v___y_2038_ = v___y_2044_;
v___y_2039_ = v___y_2043_;
goto v___jp_2035_;
}
}
v___jp_2047_:
{
lean_object* v___x_2049_; lean_object* v___x_2050_; uint8_t v___x_2051_; 
v___x_2049_ = lean_array_get_size(v___y_2048_);
v___x_2050_ = lean_unsigned_to_nat(0u);
v___x_2051_ = lean_nat_dec_eq(v___x_2049_, v___x_2050_);
if (v___x_2051_ == 0)
{
lean_object* v___x_2052_; lean_object* v___x_2053_; uint8_t v___x_2054_; 
v___x_2052_ = lean_unsigned_to_nat(1u);
v___x_2053_ = lean_nat_sub(v___x_2049_, v___x_2052_);
v___x_2054_ = lean_nat_dec_le(v___x_2050_, v___x_2053_);
if (v___x_2054_ == 0)
{
lean_inc(v___x_2053_);
v___y_2042_ = v___y_2048_;
v___y_2043_ = v___x_2053_;
v___y_2044_ = v___x_2049_;
v___y_2045_ = v___x_2053_;
goto v___jp_2041_;
}
else
{
v___y_2042_ = v___y_2048_;
v___y_2043_ = v___x_2053_;
v___y_2044_ = v___x_2049_;
v___y_2045_ = v___x_2050_;
goto v___jp_2041_;
}
}
else
{
v___y_2030_ = v___y_2048_;
goto v___jp_2029_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___boxed(lean_object* v_f_2061_, lean_object* v_xs_2062_, lean_object* v_ys_2063_){
_start:
{
lean_object* v_res_2064_; 
v_res_2064_ = l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5(v_f_2061_, v_xs_2062_, v_ys_2063_);
lean_dec_ref(v_xs_2062_);
return v_res_2064_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__0(lean_object* v_a_2065_, lean_object* v_a_2066_){
_start:
{
if (lean_obj_tag(v_a_2065_) == 0)
{
lean_object* v___x_2067_; 
v___x_2067_ = l_List_reverse___redArg(v_a_2066_);
return v___x_2067_;
}
else
{
lean_object* v_head_2068_; lean_object* v_tail_2069_; lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2080_; 
v_head_2068_ = lean_ctor_get(v_a_2065_, 0);
v_tail_2069_ = lean_ctor_get(v_a_2065_, 1);
v_isSharedCheck_2080_ = !lean_is_exclusive(v_a_2065_);
if (v_isSharedCheck_2080_ == 0)
{
v___x_2071_ = v_a_2065_;
v_isShared_2072_ = v_isSharedCheck_2080_;
goto v_resetjp_2070_;
}
else
{
lean_inc(v_tail_2069_);
lean_inc(v_head_2068_);
lean_dec(v_a_2065_);
v___x_2071_ = lean_box(0);
v_isShared_2072_ = v_isSharedCheck_2080_;
goto v_resetjp_2070_;
}
v_resetjp_2070_:
{
lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2077_; 
v___x_2073_ = l_Nat_reprFast(v_head_2068_);
v___x_2074_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2074_, 0, v___x_2073_);
v___x_2075_ = l_Lean_MessageData_ofFormat(v___x_2074_);
if (v_isShared_2072_ == 0)
{
lean_ctor_set(v___x_2071_, 1, v_a_2066_);
lean_ctor_set(v___x_2071_, 0, v___x_2075_);
v___x_2077_ = v___x_2071_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v___x_2075_);
lean_ctor_set(v_reuseFailAlloc_2079_, 1, v_a_2066_);
v___x_2077_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
v_a_2065_ = v_tail_2069_;
v_a_2066_ = v___x_2077_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__20(lean_object* v_a_2081_, lean_object* v_a_2082_){
_start:
{
if (lean_obj_tag(v_a_2081_) == 0)
{
lean_object* v___x_2083_; 
v___x_2083_ = l_List_reverse___redArg(v_a_2082_);
return v___x_2083_;
}
else
{
lean_object* v_head_2084_; lean_object* v_tail_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2097_; 
v_head_2084_ = lean_ctor_get(v_a_2081_, 0);
v_tail_2085_ = lean_ctor_get(v_a_2081_, 1);
v_isSharedCheck_2097_ = !lean_is_exclusive(v_a_2081_);
if (v_isSharedCheck_2097_ == 0)
{
v___x_2087_ = v_a_2081_;
v_isShared_2088_ = v_isSharedCheck_2097_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_tail_2085_);
lean_inc(v_head_2084_);
lean_dec(v_a_2081_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2097_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2094_; 
v___x_2089_ = lean_array_to_list(v_head_2084_);
v___x_2090_ = lean_box(0);
v___x_2091_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__0(v___x_2089_, v___x_2090_);
v___x_2092_ = l_Lean_MessageData_ofList(v___x_2091_);
if (v_isShared_2088_ == 0)
{
lean_ctor_set(v___x_2087_, 1, v_a_2082_);
lean_ctor_set(v___x_2087_, 0, v___x_2092_);
v___x_2094_ = v___x_2087_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2096_; 
v_reuseFailAlloc_2096_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2096_, 0, v___x_2092_);
lean_ctor_set(v_reuseFailAlloc_2096_, 1, v_a_2082_);
v___x_2094_ = v_reuseFailAlloc_2096_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
v_a_2081_ = v_tail_2085_;
v_a_2082_ = v___x_2094_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__9(void){
_start:
{
lean_object* v___x_2112_; lean_object* v___x_2113_; 
v___x_2112_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__8));
v___x_2113_ = l_Lean_stringToMessageData(v___x_2112_);
return v___x_2113_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__11(void){
_start:
{
lean_object* v___x_2115_; lean_object* v___x_2116_; 
v___x_2115_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__10));
v___x_2116_ = l_Lean_stringToMessageData(v___x_2115_);
return v___x_2116_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion(lean_object* v_preDefs_2117_, lean_object* v_fixedParamPerms_2118_, lean_object* v_xs_2119_, lean_object* v_recArgInfos_2120_, lean_object* v_a_2121_, lean_object* v_a_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_){
_start:
{
lean_object* v___f_2126_; lean_object* v___f_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; size_t v_sz_2131_; size_t v___x_2132_; lean_object* v___x_2133_; 
v___f_2126_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__0));
v___f_2127_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__1));
v___x_2128_ = lean_box(0);
v___x_2129_ = l_Lean_Elab_Structural_instInhabitedRecArgInfo_default;
v___x_2130_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v_sz_2131_ = lean_array_size(v_preDefs_2117_);
v___x_2132_ = ((size_t)0ULL);
lean_inc_ref(v_preDefs_2117_);
lean_inc_ref(v_xs_2119_);
v___x_2133_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___redArg(v_fixedParamPerms_2118_, v_xs_2119_, v_sz_2131_, v___x_2132_, v_preDefs_2117_, v_a_2121_, v_a_2122_, v_a_2123_, v_a_2124_);
if (lean_obj_tag(v___x_2133_) == 0)
{
lean_object* v_a_2134_; lean_object* v___x_2135_; 
v_a_2134_ = lean_ctor_get(v___x_2133_, 0);
lean_inc(v_a_2134_);
lean_dec_ref_known(v___x_2133_, 1);
lean_inc_ref(v_preDefs_2117_);
lean_inc_ref(v_xs_2119_);
v___x_2135_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___redArg(v_fixedParamPerms_2118_, v_xs_2119_, v_sz_2131_, v___x_2132_, v_preDefs_2117_, v_a_2121_, v_a_2122_, v_a_2123_, v_a_2124_);
if (lean_obj_tag(v___x_2135_) == 0)
{
lean_object* v_a_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v_indGroupInst_2139_; lean_object* v_toIndGroupInfo_2140_; lean_object* v_all_2141_; lean_object* v___x_2143_; uint8_t v_isShared_2144_; uint8_t v_isSharedCheck_2225_; 
v_a_2136_ = lean_ctor_get(v___x_2135_, 0);
lean_inc(v_a_2136_);
lean_dec_ref_known(v___x_2135_, 1);
v___x_2137_ = lean_unsigned_to_nat(0u);
v___x_2138_ = lean_array_get_borrowed(v___x_2129_, v_recArgInfos_2120_, v___x_2137_);
v_indGroupInst_2139_ = lean_ctor_get(v___x_2138_, 4);
v_toIndGroupInfo_2140_ = lean_ctor_get(v_indGroupInst_2139_, 0);
lean_inc_ref(v_toIndGroupInfo_2140_);
v_all_2141_ = lean_ctor_get(v_toIndGroupInfo_2140_, 0);
v_isSharedCheck_2225_ = !lean_is_exclusive(v_toIndGroupInfo_2140_);
if (v_isSharedCheck_2225_ == 0)
{
lean_object* v_unused_2226_; 
v_unused_2226_ = lean_ctor_get(v_toIndGroupInfo_2140_, 1);
lean_dec(v_unused_2226_);
v___x_2143_ = v_toIndGroupInfo_2140_;
v_isShared_2144_ = v_isSharedCheck_2225_;
goto v_resetjp_2142_;
}
else
{
lean_inc(v_all_2141_);
lean_dec(v_toIndGroupInfo_2140_);
v___x_2143_ = lean_box(0);
v_isShared_2144_ = v_isSharedCheck_2225_;
goto v_resetjp_2142_;
}
v_resetjp_2142_:
{
lean_object* v___x_2145_; lean_object* v___x_2146_; 
v___x_2145_ = lean_array_get(v___x_2128_, v_all_2141_, v___x_2137_);
lean_dec_ref(v_all_2141_);
v___x_2146_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4(v___x_2145_, v_a_2121_, v_a_2122_, v_a_2123_, v_a_2124_);
if (lean_obj_tag(v___x_2146_) == 0)
{
lean_object* v_a_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___f_2152_; lean_object* v___y_2154_; lean_object* v___y_2155_; lean_object* v___y_2156_; lean_object* v___y_2157_; lean_object* v___x_2191_; lean_object* v_a_2192_; uint8_t v___x_2193_; 
v_a_2147_ = lean_ctor_get(v___x_2146_, 0);
lean_inc(v_a_2147_);
lean_dec_ref_known(v___x_2146_, 1);
v___x_2148_ = l_Lean_InductiveVal_numTypeFormers(v_a_2147_);
v___x_2149_ = l_Array_range(v___x_2148_);
v___x_2150_ = l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5(v___f_2127_, v_recArgInfos_2120_, v___x_2149_);
v___x_2151_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__5));
v___f_2152_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__6));
v___x_2191_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1(v___x_2151_, v_a_2121_, v_a_2122_, v_a_2123_, v_a_2124_);
v_a_2192_ = lean_ctor_get(v___x_2191_, 0);
lean_inc(v_a_2192_);
lean_dec_ref(v___x_2191_);
v___x_2193_ = lean_unbox(v_a_2192_);
lean_dec(v_a_2192_);
if (v___x_2193_ == 0)
{
lean_del_object(v___x_2143_);
v___y_2154_ = v_a_2121_;
v___y_2155_ = v_a_2122_;
v___y_2156_ = v_a_2123_;
v___y_2157_ = v_a_2124_;
goto v___jp_2153_;
}
else
{
lean_object* v_toConstantVal_2194_; lean_object* v_name_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2199_; 
v_toConstantVal_2194_ = lean_ctor_get(v_a_2147_, 0);
v_name_2195_ = lean_ctor_get(v_toConstantVal_2194_, 0);
v___x_2196_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__9, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__9_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__9);
lean_inc(v_name_2195_);
v___x_2197_ = l_Lean_MessageData_ofName(v_name_2195_);
if (v_isShared_2144_ == 0)
{
lean_ctor_set_tag(v___x_2143_, 7);
lean_ctor_set(v___x_2143_, 1, v___x_2197_);
lean_ctor_set(v___x_2143_, 0, v___x_2196_);
v___x_2199_ = v___x_2143_;
goto v_reusejp_2198_;
}
else
{
lean_object* v_reuseFailAlloc_2216_; 
v_reuseFailAlloc_2216_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2216_, 0, v___x_2196_);
lean_ctor_set(v_reuseFailAlloc_2216_, 1, v___x_2197_);
v___x_2199_ = v_reuseFailAlloc_2216_;
goto v_reusejp_2198_;
}
v_reusejp_2198_:
{
lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; 
v___x_2200_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__11, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__11_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__11);
v___x_2201_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2201_, 0, v___x_2199_);
lean_ctor_set(v___x_2201_, 1, v___x_2200_);
lean_inc_ref(v___x_2150_);
v___x_2202_ = lean_array_to_list(v___x_2150_);
v___x_2203_ = lean_box(0);
v___x_2204_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__20(v___x_2202_, v___x_2203_);
v___x_2205_ = l_Lean_MessageData_ofList(v___x_2204_);
v___x_2206_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2206_, 0, v___x_2201_);
lean_ctor_set(v___x_2206_, 1, v___x_2205_);
v___x_2207_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_2151_, v___x_2206_, v_a_2121_, v_a_2122_, v_a_2123_, v_a_2124_);
if (lean_obj_tag(v___x_2207_) == 0)
{
lean_dec_ref_known(v___x_2207_, 1);
v___y_2154_ = v_a_2121_;
v___y_2155_ = v_a_2122_;
v___y_2156_ = v_a_2123_;
v___y_2157_ = v_a_2124_;
goto v___jp_2153_;
}
else
{
lean_object* v_a_2208_; lean_object* v___x_2210_; uint8_t v_isShared_2211_; uint8_t v_isSharedCheck_2215_; 
lean_dec_ref(v___x_2150_);
lean_dec(v_a_2147_);
lean_dec(v_a_2136_);
lean_dec(v_a_2134_);
lean_dec_ref(v_recArgInfos_2120_);
lean_dec_ref(v_xs_2119_);
lean_dec_ref(v_fixedParamPerms_2118_);
lean_dec_ref(v_preDefs_2117_);
v_a_2208_ = lean_ctor_get(v___x_2207_, 0);
v_isSharedCheck_2215_ = !lean_is_exclusive(v___x_2207_);
if (v_isSharedCheck_2215_ == 0)
{
v___x_2210_ = v___x_2207_;
v_isShared_2211_ = v_isSharedCheck_2215_;
goto v_resetjp_2209_;
}
else
{
lean_inc(v_a_2208_);
lean_dec(v___x_2207_);
v___x_2210_ = lean_box(0);
v_isShared_2211_ = v_isSharedCheck_2215_;
goto v_resetjp_2209_;
}
v_resetjp_2209_:
{
lean_object* v___x_2213_; 
if (v_isShared_2211_ == 0)
{
v___x_2213_ = v___x_2210_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v_a_2208_);
v___x_2213_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
return v___x_2213_;
}
}
}
}
}
v___jp_2153_:
{
lean_object* v_toConstantVal_2158_; lean_object* v_numIndices_2159_; lean_object* v_name_2160_; lean_object* v___x_2161_; 
v_toConstantVal_2158_ = lean_ctor_get(v_a_2147_, 0);
lean_inc_ref(v_toConstantVal_2158_);
v_numIndices_2159_ = lean_ctor_get(v_a_2147_, 2);
lean_inc(v_numIndices_2159_);
lean_dec(v_a_2147_);
v_name_2160_ = lean_ctor_get(v_toConstantVal_2158_, 0);
lean_inc(v_name_2160_);
lean_dec_ref(v_toConstantVal_2158_);
v___x_2161_ = l_Lean_Meta_isInductivePredicate(v_name_2160_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_);
if (lean_obj_tag(v___x_2161_) == 0)
{
lean_object* v_a_2162_; lean_object* v___x_2163_; lean_object* v___f_2164_; uint8_t v___x_2165_; 
v_a_2162_ = lean_ctor_get(v___x_2161_, 0);
lean_inc_n(v_a_2162_, 2);
lean_dec_ref_known(v___x_2161_, 1);
v___x_2163_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___boxed__const__1));
lean_inc(v_numIndices_2159_);
lean_inc_ref(v_preDefs_2117_);
lean_inc_ref(v_xs_2119_);
lean_inc_ref(v_fixedParamPerms_2118_);
lean_inc_ref(v___x_2150_);
lean_inc(v_a_2134_);
lean_inc_ref(v_recArgInfos_2120_);
v___f_2164_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___boxed), 21, 14);
lean_closure_set(v___f_2164_, 0, v_recArgInfos_2120_);
lean_closure_set(v___f_2164_, 1, v_a_2134_);
lean_closure_set(v___f_2164_, 2, v___x_2150_);
lean_closure_set(v___f_2164_, 3, v___x_2163_);
lean_closure_set(v___f_2164_, 4, v_fixedParamPerms_2118_);
lean_closure_set(v___f_2164_, 5, v_xs_2119_);
lean_closure_set(v___f_2164_, 6, v___x_2137_);
lean_closure_set(v___f_2164_, 7, v_preDefs_2117_);
lean_closure_set(v___f_2164_, 8, v_numIndices_2159_);
lean_closure_set(v___f_2164_, 9, v___f_2126_);
lean_closure_set(v___f_2164_, 10, v___x_2151_);
lean_closure_set(v___f_2164_, 11, v_a_2162_);
lean_closure_set(v___f_2164_, 12, v___x_2130_);
lean_closure_set(v___f_2164_, 13, v___f_2152_);
v___x_2165_ = lean_unbox(v_a_2162_);
if (v___x_2165_ == 0)
{
size_t v_sz_2166_; lean_object* v___x_2167_; 
lean_dec_ref(v___f_2164_);
v_sz_2166_ = lean_array_size(v_recArgInfos_2120_);
lean_inc_ref(v_recArgInfos_2120_);
v___x_2167_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___redArg(v_a_2134_, v_a_2136_, v_sz_2166_, v___x_2132_, v_recArgInfos_2120_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_);
lean_dec(v_a_2136_);
if (lean_obj_tag(v___x_2167_) == 0)
{
lean_object* v_a_2168_; lean_object* v___x_2169_; uint8_t v___x_2170_; lean_object* v___x_2171_; 
v_a_2168_ = lean_ctor_get(v___x_2167_, 0);
lean_inc(v_a_2168_);
lean_dec_ref_known(v___x_2167_, 1);
v___x_2169_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__7));
v___x_2170_ = lean_unbox(v_a_2162_);
lean_dec(v_a_2162_);
v___x_2171_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2(v_recArgInfos_2120_, v_a_2134_, v___x_2150_, v___x_2132_, v_fixedParamPerms_2118_, v_xs_2119_, v___x_2137_, v_preDefs_2117_, v_numIndices_2159_, v___f_2126_, v___x_2151_, v___x_2170_, v___x_2130_, v___f_2152_, v___x_2169_, v_a_2168_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_);
lean_dec(v_numIndices_2159_);
lean_dec(v_a_2134_);
return v___x_2171_;
}
else
{
lean_object* v_a_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2179_; 
lean_dec(v_a_2162_);
lean_dec(v_numIndices_2159_);
lean_dec_ref(v___x_2150_);
lean_dec(v_a_2134_);
lean_dec_ref(v_recArgInfos_2120_);
lean_dec_ref(v_xs_2119_);
lean_dec_ref(v_fixedParamPerms_2118_);
lean_dec_ref(v_preDefs_2117_);
v_a_2172_ = lean_ctor_get(v___x_2167_, 0);
v_isSharedCheck_2179_ = !lean_is_exclusive(v___x_2167_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_2174_ = v___x_2167_;
v_isShared_2175_ = v_isSharedCheck_2179_;
goto v_resetjp_2173_;
}
else
{
lean_inc(v_a_2172_);
lean_dec(v___x_2167_);
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
lean_object* v___x_2180_; lean_object* v___f_2181_; lean_object* v___x_2182_; 
lean_dec(v_a_2162_);
lean_dec(v_numIndices_2159_);
lean_dec_ref(v___x_2150_);
lean_dec(v_a_2136_);
lean_dec_ref(v_xs_2119_);
lean_dec_ref(v_fixedParamPerms_2118_);
lean_dec_ref(v_preDefs_2117_);
v___x_2180_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___boxed__const__1));
lean_inc(v_a_2134_);
v___f_2181_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__3___boxed), 10, 4);
lean_closure_set(v___f_2181_, 0, v_recArgInfos_2120_);
lean_closure_set(v___f_2181_, 1, v_a_2134_);
lean_closure_set(v___f_2181_, 2, v___x_2180_);
lean_closure_set(v___f_2181_, 3, v___f_2164_);
v___x_2182_ = l_Lean_Elab_Structural_withFunTypes___redArg(v_a_2134_, v___f_2181_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_);
return v___x_2182_;
}
}
else
{
lean_object* v_a_2183_; lean_object* v___x_2185_; uint8_t v_isShared_2186_; uint8_t v_isSharedCheck_2190_; 
lean_dec(v_numIndices_2159_);
lean_dec_ref(v___x_2150_);
lean_dec(v_a_2136_);
lean_dec(v_a_2134_);
lean_dec_ref(v_recArgInfos_2120_);
lean_dec_ref(v_xs_2119_);
lean_dec_ref(v_fixedParamPerms_2118_);
lean_dec_ref(v_preDefs_2117_);
v_a_2183_ = lean_ctor_get(v___x_2161_, 0);
v_isSharedCheck_2190_ = !lean_is_exclusive(v___x_2161_);
if (v_isSharedCheck_2190_ == 0)
{
v___x_2185_ = v___x_2161_;
v_isShared_2186_ = v_isSharedCheck_2190_;
goto v_resetjp_2184_;
}
else
{
lean_inc(v_a_2183_);
lean_dec(v___x_2161_);
v___x_2185_ = lean_box(0);
v_isShared_2186_ = v_isSharedCheck_2190_;
goto v_resetjp_2184_;
}
v_resetjp_2184_:
{
lean_object* v___x_2188_; 
if (v_isShared_2186_ == 0)
{
v___x_2188_ = v___x_2185_;
goto v_reusejp_2187_;
}
else
{
lean_object* v_reuseFailAlloc_2189_; 
v_reuseFailAlloc_2189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2189_, 0, v_a_2183_);
v___x_2188_ = v_reuseFailAlloc_2189_;
goto v_reusejp_2187_;
}
v_reusejp_2187_:
{
return v___x_2188_;
}
}
}
}
}
else
{
lean_object* v_a_2217_; lean_object* v___x_2219_; uint8_t v_isShared_2220_; uint8_t v_isSharedCheck_2224_; 
lean_del_object(v___x_2143_);
lean_dec(v_a_2136_);
lean_dec(v_a_2134_);
lean_dec_ref(v_recArgInfos_2120_);
lean_dec_ref(v_xs_2119_);
lean_dec_ref(v_fixedParamPerms_2118_);
lean_dec_ref(v_preDefs_2117_);
v_a_2217_ = lean_ctor_get(v___x_2146_, 0);
v_isSharedCheck_2224_ = !lean_is_exclusive(v___x_2146_);
if (v_isSharedCheck_2224_ == 0)
{
v___x_2219_ = v___x_2146_;
v_isShared_2220_ = v_isSharedCheck_2224_;
goto v_resetjp_2218_;
}
else
{
lean_inc(v_a_2217_);
lean_dec(v___x_2146_);
v___x_2219_ = lean_box(0);
v_isShared_2220_ = v_isSharedCheck_2224_;
goto v_resetjp_2218_;
}
v_resetjp_2218_:
{
lean_object* v___x_2222_; 
if (v_isShared_2220_ == 0)
{
v___x_2222_ = v___x_2219_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v_a_2217_);
v___x_2222_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
return v___x_2222_;
}
}
}
}
}
else
{
lean_object* v_a_2227_; lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2234_; 
lean_dec(v_a_2134_);
lean_dec_ref(v_recArgInfos_2120_);
lean_dec_ref(v_xs_2119_);
lean_dec_ref(v_fixedParamPerms_2118_);
lean_dec_ref(v_preDefs_2117_);
v_a_2227_ = lean_ctor_get(v___x_2135_, 0);
v_isSharedCheck_2234_ = !lean_is_exclusive(v___x_2135_);
if (v_isSharedCheck_2234_ == 0)
{
v___x_2229_ = v___x_2135_;
v_isShared_2230_ = v_isSharedCheck_2234_;
goto v_resetjp_2228_;
}
else
{
lean_inc(v_a_2227_);
lean_dec(v___x_2135_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2234_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
lean_object* v___x_2232_; 
if (v_isShared_2230_ == 0)
{
v___x_2232_ = v___x_2229_;
goto v_reusejp_2231_;
}
else
{
lean_object* v_reuseFailAlloc_2233_; 
v_reuseFailAlloc_2233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2233_, 0, v_a_2227_);
v___x_2232_ = v_reuseFailAlloc_2233_;
goto v_reusejp_2231_;
}
v_reusejp_2231_:
{
return v___x_2232_;
}
}
}
}
else
{
lean_object* v_a_2235_; lean_object* v___x_2237_; uint8_t v_isShared_2238_; uint8_t v_isSharedCheck_2242_; 
lean_dec_ref(v_recArgInfos_2120_);
lean_dec_ref(v_xs_2119_);
lean_dec_ref(v_fixedParamPerms_2118_);
lean_dec_ref(v_preDefs_2117_);
v_a_2235_ = lean_ctor_get(v___x_2133_, 0);
v_isSharedCheck_2242_ = !lean_is_exclusive(v___x_2133_);
if (v_isSharedCheck_2242_ == 0)
{
v___x_2237_ = v___x_2133_;
v_isShared_2238_ = v_isSharedCheck_2242_;
goto v_resetjp_2236_;
}
else
{
lean_inc(v_a_2235_);
lean_dec(v___x_2133_);
v___x_2237_ = lean_box(0);
v_isShared_2238_ = v_isSharedCheck_2242_;
goto v_resetjp_2236_;
}
v_resetjp_2236_:
{
lean_object* v___x_2240_; 
if (v_isShared_2238_ == 0)
{
v___x_2240_ = v___x_2237_;
goto v_reusejp_2239_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v_a_2235_);
v___x_2240_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2239_;
}
v_reusejp_2239_:
{
return v___x_2240_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_0interp(lean_interpreter_value* stack)
{
lean_object* v_preDefs_2117_ = stack[0].m_obj;
lean_object* v_fixedParamPerms_2118_ = stack[1].m_obj;
lean_object* v_xs_2119_ = stack[2].m_obj;
lean_object* v_recArgInfos_2120_ = stack[3].m_obj;
lean_object* v_a_2121_ = stack[4].m_obj;
lean_object* v_a_2122_ = stack[5].m_obj;
lean_object* v_a_2123_ = stack[6].m_obj;
lean_object* v_a_2124_ = stack[7].m_obj;
lean_object* v_res_2243_;
v_res_2243_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion(v_preDefs_2117_, v_fixedParamPerms_2118_, v_xs_2119_, v_recArgInfos_2120_, v_a_2121_, v_a_2122_, v_a_2123_, v_a_2124_);
stack->m_obj
 = v_res_2243_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___boxed(lean_object* v_preDefs_2244_, lean_object* v_fixedParamPerms_2245_, lean_object* v_xs_2246_, lean_object* v_recArgInfos_2247_, lean_object* v_a_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_, lean_object* v_a_2251_, lean_object* v_a_2252_){
_start:
{
lean_object* v_res_2253_; 
v_res_2253_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion(v_preDefs_2244_, v_fixedParamPerms_2245_, v_xs_2246_, v_recArgInfos_2247_, v_a_2248_, v_a_2249_, v_a_2250_, v_a_2251_);
lean_dec(v_a_2251_);
lean_dec_ref(v_a_2250_);
lean_dec(v_a_2249_);
lean_dec_ref(v_a_2248_);
return v_res_2253_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2(lean_object* v_fixedParamPerms_2254_, lean_object* v_xs_2255_, lean_object* v_as_2256_, size_t v_sz_2257_, size_t v_i_2258_, lean_object* v_bs_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_){
_start:
{
lean_object* v___x_2265_; 
v___x_2265_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___redArg(v_fixedParamPerms_2254_, v_xs_2255_, v_sz_2257_, v_i_2258_, v_bs_2259_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_);
return v___x_2265_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_fixedParamPerms_2254_ = stack[0].m_obj;
lean_object* v_xs_2255_ = stack[1].m_obj;
lean_object* v_as_2256_ = stack[2].m_obj;
size_t v_sz_2257_ = stack[3].m_num;
size_t v_i_2258_ = stack[4].m_num;
lean_object* v_bs_2259_ = stack[5].m_obj;
lean_object* v___y_2260_ = stack[6].m_obj;
lean_object* v___y_2261_ = stack[7].m_obj;
lean_object* v___y_2262_ = stack[8].m_obj;
lean_object* v___y_2263_ = stack[9].m_obj;
lean_object* v_res_2266_;
v_res_2266_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2(v_fixedParamPerms_2254_, v_xs_2255_, v_as_2256_, v_sz_2257_, v_i_2258_, v_bs_2259_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_);
stack->m_obj
 = v_res_2266_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___boxed(lean_object* v_fixedParamPerms_2267_, lean_object* v_xs_2268_, lean_object* v_as_2269_, lean_object* v_sz_2270_, lean_object* v_i_2271_, lean_object* v_bs_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_){
_start:
{
size_t v_sz_boxed_2278_; size_t v_i_boxed_2279_; lean_object* v_res_2280_; 
v_sz_boxed_2278_ = lean_unbox_usize(v_sz_2270_);
lean_dec(v_sz_2270_);
v_i_boxed_2279_ = lean_unbox_usize(v_i_2271_);
lean_dec(v_i_2271_);
v_res_2280_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2(v_fixedParamPerms_2267_, v_xs_2268_, v_as_2269_, v_sz_boxed_2278_, v_i_boxed_2279_, v_bs_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_);
lean_dec(v___y_2276_);
lean_dec_ref(v___y_2275_);
lean_dec(v___y_2274_);
lean_dec_ref(v___y_2273_);
lean_dec_ref(v_as_2269_);
lean_dec_ref(v_fixedParamPerms_2267_);
return v_res_2280_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3(lean_object* v_fixedParamPerms_2281_, lean_object* v_xs_2282_, lean_object* v_as_2283_, size_t v_sz_2284_, size_t v_i_2285_, lean_object* v_bs_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_){
_start:
{
lean_object* v___x_2292_; 
v___x_2292_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___redArg(v_fixedParamPerms_2281_, v_xs_2282_, v_sz_2284_, v_i_2285_, v_bs_2286_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_);
return v___x_2292_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_fixedParamPerms_2281_ = stack[0].m_obj;
lean_object* v_xs_2282_ = stack[1].m_obj;
lean_object* v_as_2283_ = stack[2].m_obj;
size_t v_sz_2284_ = stack[3].m_num;
size_t v_i_2285_ = stack[4].m_num;
lean_object* v_bs_2286_ = stack[5].m_obj;
lean_object* v___y_2287_ = stack[6].m_obj;
lean_object* v___y_2288_ = stack[7].m_obj;
lean_object* v___y_2289_ = stack[8].m_obj;
lean_object* v___y_2290_ = stack[9].m_obj;
lean_object* v_res_2293_;
v_res_2293_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3(v_fixedParamPerms_2281_, v_xs_2282_, v_as_2283_, v_sz_2284_, v_i_2285_, v_bs_2286_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_);
stack->m_obj
 = v_res_2293_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___boxed(lean_object* v_fixedParamPerms_2294_, lean_object* v_xs_2295_, lean_object* v_as_2296_, lean_object* v_sz_2297_, lean_object* v_i_2298_, lean_object* v_bs_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_){
_start:
{
size_t v_sz_boxed_2305_; size_t v_i_boxed_2306_; lean_object* v_res_2307_; 
v_sz_boxed_2305_ = lean_unbox_usize(v_sz_2297_);
lean_dec(v_sz_2297_);
v_i_boxed_2306_ = lean_unbox_usize(v_i_2298_);
lean_dec(v_i_2298_);
v_res_2307_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3(v_fixedParamPerms_2294_, v_xs_2295_, v_as_2296_, v_sz_boxed_2305_, v_i_boxed_2306_, v_bs_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_);
lean_dec(v___y_2303_);
lean_dec_ref(v___y_2302_);
lean_dec(v___y_2301_);
lean_dec_ref(v___y_2300_);
lean_dec_ref(v_as_2296_);
lean_dec_ref(v_fixedParamPerms_2294_);
return v_res_2307_;
}
}
lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14(lean_object* v_00_u03b3_2308_, lean_object* v_msg_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_){
_start:
{
lean_object* v___x_2315_; 
v___x_2315_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg(v_msg_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_);
return v___x_2315_;
}
}
LEAN_EXPORT void l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2309_ = stack[1].m_obj;
lean_object* v___y_2310_ = stack[2].m_obj;
lean_object* v___y_2311_ = stack[3].m_obj;
lean_object* v___y_2312_ = stack[4].m_obj;
lean_object* v___y_2313_ = stack[5].m_obj;
lean_object* v_res_2316_;
v_res_2316_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14(lean_box(0), v_msg_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_);
stack->m_obj
 = v_res_2316_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___boxed(lean_object* v_00_u03b3_2317_, lean_object* v_msg_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_){
_start:
{
lean_object* v_res_2324_; 
v_res_2324_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14(v_00_u03b3_2317_, v_msg_2318_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_);
lean_dec(v___y_2322_);
lean_dec_ref(v___y_2321_);
lean_dec(v___y_2320_);
lean_dec_ref(v___y_2319_);
return v_res_2324_;
}
}
lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6(lean_object* v_00_u03b3_2325_, lean_object* v_00_u03b1_2326_, lean_object* v_f_2327_, lean_object* v_positions_2328_, lean_object* v_ys_2329_, lean_object* v_xs_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_){
_start:
{
lean_object* v___x_2336_; 
v___x_2336_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg(v_f_2327_, v_positions_2328_, v_ys_2329_, v_xs_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_);
return v___x_2336_;
}
}
LEAN_EXPORT void l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2327_ = stack[2].m_obj;
lean_object* v_positions_2328_ = stack[3].m_obj;
lean_object* v_ys_2329_ = stack[4].m_obj;
lean_object* v_xs_2330_ = stack[5].m_obj;
lean_object* v___y_2331_ = stack[6].m_obj;
lean_object* v___y_2332_ = stack[7].m_obj;
lean_object* v___y_2333_ = stack[8].m_obj;
lean_object* v___y_2334_ = stack[9].m_obj;
lean_object* v_res_2337_;
v_res_2337_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6(lean_box(0), lean_box(0), v_f_2327_, v_positions_2328_, v_ys_2329_, v_xs_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_);
stack->m_obj
 = v_res_2337_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___boxed(lean_object* v_00_u03b3_2338_, lean_object* v_00_u03b1_2339_, lean_object* v_f_2340_, lean_object* v_positions_2341_, lean_object* v_ys_2342_, lean_object* v_xs_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_){
_start:
{
lean_object* v_res_2349_; 
v_res_2349_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6(v_00_u03b3_2338_, v_00_u03b1_2339_, v_f_2340_, v_positions_2341_, v_ys_2342_, v_xs_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_);
lean_dec(v___y_2347_);
lean_dec_ref(v___y_2346_);
lean_dec(v___y_2345_);
lean_dec_ref(v___y_2344_);
lean_dec_ref(v_xs_2343_);
lean_dec_ref(v_ys_2342_);
lean_dec_ref(v_positions_2341_);
return v_res_2349_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7(lean_object* v___x_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_, lean_object* v_funTypes_2353_, lean_object* v_as_2354_, size_t v_sz_2355_, size_t v_i_2356_, lean_object* v_bs_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_){
_start:
{
lean_object* v___x_2363_; 
v___x_2363_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg(v___x_2350_, v_a_2351_, v_a_2352_, v_funTypes_2353_, v_sz_2355_, v_i_2356_, v_bs_2357_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_);
return v___x_2363_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2350_ = stack[0].m_obj;
lean_object* v_a_2351_ = stack[1].m_obj;
lean_object* v_a_2352_ = stack[2].m_obj;
lean_object* v_funTypes_2353_ = stack[3].m_obj;
lean_object* v_as_2354_ = stack[4].m_obj;
size_t v_sz_2355_ = stack[5].m_num;
size_t v_i_2356_ = stack[6].m_num;
lean_object* v_bs_2357_ = stack[7].m_obj;
lean_object* v___y_2358_ = stack[8].m_obj;
lean_object* v___y_2359_ = stack[9].m_obj;
lean_object* v___y_2360_ = stack[10].m_obj;
lean_object* v___y_2361_ = stack[11].m_obj;
lean_object* v_res_2364_;
v_res_2364_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7(v___x_2350_, v_a_2351_, v_a_2352_, v_funTypes_2353_, v_as_2354_, v_sz_2355_, v_i_2356_, v_bs_2357_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_);
stack->m_obj
 = v_res_2364_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___boxed(lean_object* v___x_2365_, lean_object* v_a_2366_, lean_object* v_a_2367_, lean_object* v_funTypes_2368_, lean_object* v_as_2369_, lean_object* v_sz_2370_, lean_object* v_i_2371_, lean_object* v_bs_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_){
_start:
{
size_t v_sz_boxed_2378_; size_t v_i_boxed_2379_; lean_object* v_res_2380_; 
v_sz_boxed_2378_ = lean_unbox_usize(v_sz_2370_);
lean_dec(v_sz_2370_);
v_i_boxed_2379_ = lean_unbox_usize(v_i_2371_);
lean_dec(v_i_2371_);
v_res_2380_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7(v___x_2365_, v_a_2366_, v_a_2367_, v_funTypes_2368_, v_as_2369_, v_sz_boxed_2378_, v_i_boxed_2379_, v_bs_2372_, v___y_2373_, v___y_2374_, v___y_2375_, v___y_2376_);
lean_dec(v___y_2376_);
lean_dec_ref(v___y_2375_);
lean_dec(v___y_2374_);
lean_dec_ref(v___y_2373_);
lean_dec_ref(v_as_2369_);
return v_res_2380_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8(lean_object* v_fixedParamPerms_2381_, lean_object* v_xs_2382_, lean_object* v_as_2383_, size_t v_sz_2384_, size_t v_i_2385_, lean_object* v_bs_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_){
_start:
{
lean_object* v___x_2392_; 
v___x_2392_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg(v_fixedParamPerms_2381_, v_xs_2382_, v_sz_2384_, v_i_2385_, v_bs_2386_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_);
return v___x_2392_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_fixedParamPerms_2381_ = stack[0].m_obj;
lean_object* v_xs_2382_ = stack[1].m_obj;
lean_object* v_as_2383_ = stack[2].m_obj;
size_t v_sz_2384_ = stack[3].m_num;
size_t v_i_2385_ = stack[4].m_num;
lean_object* v_bs_2386_ = stack[5].m_obj;
lean_object* v___y_2387_ = stack[6].m_obj;
lean_object* v___y_2388_ = stack[7].m_obj;
lean_object* v___y_2389_ = stack[8].m_obj;
lean_object* v___y_2390_ = stack[9].m_obj;
lean_object* v_res_2393_;
v_res_2393_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8(v_fixedParamPerms_2381_, v_xs_2382_, v_as_2383_, v_sz_2384_, v_i_2385_, v_bs_2386_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_);
stack->m_obj
 = v_res_2393_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___boxed(lean_object* v_fixedParamPerms_2394_, lean_object* v_xs_2395_, lean_object* v_as_2396_, lean_object* v_sz_2397_, lean_object* v_i_2398_, lean_object* v_bs_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_){
_start:
{
size_t v_sz_boxed_2405_; size_t v_i_boxed_2406_; lean_object* v_res_2407_; 
v_sz_boxed_2405_ = lean_unbox_usize(v_sz_2397_);
lean_dec(v_sz_2397_);
v_i_boxed_2406_ = lean_unbox_usize(v_i_2398_);
lean_dec(v_i_2398_);
v_res_2407_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8(v_fixedParamPerms_2394_, v_xs_2395_, v_as_2396_, v_sz_boxed_2405_, v_i_boxed_2406_, v_bs_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_);
lean_dec(v___y_2403_);
lean_dec_ref(v___y_2402_);
lean_dec(v___y_2401_);
lean_dec_ref(v___y_2400_);
lean_dec_ref(v_as_2396_);
return v_res_2407_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12(lean_object* v_00_u03b1_2408_, lean_object* v_preDefs_2409_, lean_object* v_k_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_){
_start:
{
lean_object* v___x_2416_; 
v___x_2416_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v_preDefs_2409_, v_k_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_);
return v___x_2416_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_0interp(lean_interpreter_value* stack)
{
lean_object* v_preDefs_2409_ = stack[1].m_obj;
lean_object* v_k_2410_ = stack[2].m_obj;
lean_object* v___y_2411_ = stack[3].m_obj;
lean_object* v___y_2412_ = stack[4].m_obj;
lean_object* v___y_2413_ = stack[5].m_obj;
lean_object* v___y_2414_ = stack[6].m_obj;
lean_object* v_res_2417_;
v_res_2417_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12(lean_box(0), v_preDefs_2409_, v_k_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_);
stack->m_obj
 = v_res_2417_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___boxed(lean_object* v_00_u03b1_2418_, lean_object* v_preDefs_2419_, lean_object* v_k_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_){
_start:
{
lean_object* v_res_2426_; 
v_res_2426_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12(v_00_u03b1_2418_, v_preDefs_2419_, v_k_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_);
lean_dec(v___y_2424_);
lean_dec_ref(v___y_2423_);
lean_dec(v___y_2422_);
lean_dec_ref(v___y_2421_);
return v_res_2426_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14(uint8_t v_a_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_, lean_object* v_recArgInfos_2430_, lean_object* v___x_2431_, lean_object* v_preDefs_2432_, lean_object* v_a_2433_, lean_object* v_as_2434_, size_t v_sz_2435_, size_t v_i_2436_, lean_object* v_bs_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_){
_start:
{
lean_object* v___x_2443_; 
v___x_2443_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg(v_a_2427_, v_a_2428_, v_a_2429_, v_recArgInfos_2430_, v___x_2431_, v_preDefs_2432_, v_a_2433_, v_sz_2435_, v_i_2436_, v_bs_2437_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_);
return v___x_2443_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_2427_ = stack[0].m_num;
lean_object* v_a_2428_ = stack[1].m_obj;
lean_object* v_a_2429_ = stack[2].m_obj;
lean_object* v_recArgInfos_2430_ = stack[3].m_obj;
lean_object* v___x_2431_ = stack[4].m_obj;
lean_object* v_preDefs_2432_ = stack[5].m_obj;
lean_object* v_a_2433_ = stack[6].m_obj;
lean_object* v_as_2434_ = stack[7].m_obj;
size_t v_sz_2435_ = stack[8].m_num;
size_t v_i_2436_ = stack[9].m_num;
lean_object* v_bs_2437_ = stack[10].m_obj;
lean_object* v___y_2438_ = stack[11].m_obj;
lean_object* v___y_2439_ = stack[12].m_obj;
lean_object* v___y_2440_ = stack[13].m_obj;
lean_object* v___y_2441_ = stack[14].m_obj;
lean_object* v_res_2444_;
v_res_2444_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14(v_a_2427_, v_a_2428_, v_a_2429_, v_recArgInfos_2430_, v___x_2431_, v_preDefs_2432_, v_a_2433_, v_as_2434_, v_sz_2435_, v_i_2436_, v_bs_2437_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_);
stack->m_obj
 = v_res_2444_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___boxed(lean_object* v_a_2445_, lean_object* v_a_2446_, lean_object* v_a_2447_, lean_object* v_recArgInfos_2448_, lean_object* v___x_2449_, lean_object* v_preDefs_2450_, lean_object* v_a_2451_, lean_object* v_as_2452_, lean_object* v_sz_2453_, lean_object* v_i_2454_, lean_object* v_bs_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_){
_start:
{
uint8_t v_a_29970__boxed_2461_; size_t v_sz_boxed_2462_; size_t v_i_boxed_2463_; lean_object* v_res_2464_; 
v_a_29970__boxed_2461_ = lean_unbox(v_a_2445_);
v_sz_boxed_2462_ = lean_unbox_usize(v_sz_2453_);
lean_dec(v_sz_2453_);
v_i_boxed_2463_ = lean_unbox_usize(v_i_2454_);
lean_dec(v_i_2454_);
v_res_2464_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14(v_a_29970__boxed_2461_, v_a_2446_, v_a_2447_, v_recArgInfos_2448_, v___x_2449_, v_preDefs_2450_, v_a_2451_, v_as_2452_, v_sz_boxed_2462_, v_i_boxed_2463_, v_bs_2455_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_);
lean_dec(v___y_2459_);
lean_dec_ref(v___y_2458_);
lean_dec(v___y_2457_);
lean_dec_ref(v___y_2456_);
lean_dec_ref(v_as_2452_);
lean_dec_ref(v_a_2447_);
lean_dec_ref(v_a_2446_);
return v_res_2464_;
}
}
lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16_spec__29(lean_object* v_declName_2465_, uint8_t v_s_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_){
_start:
{
lean_object* v___x_2472_; 
v___x_2472_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16_spec__29___redArg(v_declName_2465_, v_s_2466_, v___y_2468_, v___y_2470_);
return v___x_2472_;
}
}
LEAN_EXPORT void l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16_spec__29_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_2465_ = stack[0].m_obj;
uint8_t v_s_2466_ = stack[1].m_num;
lean_object* v___y_2467_ = stack[2].m_obj;
lean_object* v___y_2468_ = stack[3].m_obj;
lean_object* v___y_2469_ = stack[4].m_obj;
lean_object* v___y_2470_ = stack[5].m_obj;
lean_object* v_res_2473_;
v_res_2473_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16_spec__29(v_declName_2465_, v_s_2466_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_);
stack->m_obj
 = v_res_2473_;
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16_spec__29___boxed(lean_object* v_declName_2474_, lean_object* v_s_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_){
_start:
{
uint8_t v_s_boxed_2481_; lean_object* v_res_2482_; 
v_s_boxed_2481_ = lean_unbox(v_s_2475_);
v_res_2482_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16_spec__29(v_declName_2474_, v_s_boxed_2481_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_);
lean_dec(v___y_2479_);
lean_dec_ref(v___y_2478_);
lean_dec(v___y_2477_);
lean_dec_ref(v___y_2476_);
return v_res_2482_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17(lean_object* v_preDefs_2483_, lean_object* v_xs_2484_, uint8_t v_a_2485_, lean_object* v___x_2486_, lean_object* v_as_2487_, size_t v_sz_2488_, size_t v_i_2489_, lean_object* v_bs_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_){
_start:
{
lean_object* v___x_2496_; 
v___x_2496_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg(v_preDefs_2483_, v_xs_2484_, v_a_2485_, v___x_2486_, v_sz_2488_, v_i_2489_, v_bs_2490_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_);
return v___x_2496_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17_0interp(lean_interpreter_value* stack)
{
lean_object* v_preDefs_2483_ = stack[0].m_obj;
lean_object* v_xs_2484_ = stack[1].m_obj;
uint8_t v_a_2485_ = stack[2].m_num;
lean_object* v___x_2486_ = stack[3].m_obj;
lean_object* v_as_2487_ = stack[4].m_obj;
size_t v_sz_2488_ = stack[5].m_num;
size_t v_i_2489_ = stack[6].m_num;
lean_object* v_bs_2490_ = stack[7].m_obj;
lean_object* v___y_2491_ = stack[8].m_obj;
lean_object* v___y_2492_ = stack[9].m_obj;
lean_object* v___y_2493_ = stack[10].m_obj;
lean_object* v___y_2494_ = stack[11].m_obj;
lean_object* v_res_2497_;
v_res_2497_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17(v_preDefs_2483_, v_xs_2484_, v_a_2485_, v___x_2486_, v_as_2487_, v_sz_2488_, v_i_2489_, v_bs_2490_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_);
stack->m_obj
 = v_res_2497_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___boxed(lean_object* v_preDefs_2498_, lean_object* v_xs_2499_, lean_object* v_a_2500_, lean_object* v___x_2501_, lean_object* v_as_2502_, lean_object* v_sz_2503_, lean_object* v_i_2504_, lean_object* v_bs_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_){
_start:
{
uint8_t v_a_30051__boxed_2511_; size_t v_sz_boxed_2512_; size_t v_i_boxed_2513_; lean_object* v_res_2514_; 
v_a_30051__boxed_2511_ = lean_unbox(v_a_2500_);
v_sz_boxed_2512_ = lean_unbox_usize(v_sz_2503_);
lean_dec(v_sz_2503_);
v_i_boxed_2513_ = lean_unbox_usize(v_i_2504_);
lean_dec(v_i_2504_);
v_res_2514_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17(v_preDefs_2498_, v_xs_2499_, v_a_30051__boxed_2511_, v___x_2501_, v_as_2502_, v_sz_boxed_2512_, v_i_boxed_2513_, v_bs_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_);
lean_dec(v___y_2509_);
lean_dec_ref(v___y_2508_);
lean_dec(v___y_2507_);
lean_dec_ref(v___y_2506_);
lean_dec_ref(v_as_2502_);
lean_dec_ref(v_xs_2499_);
lean_dec_ref(v_preDefs_2498_);
return v_res_2514_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18(lean_object* v_a_2515_, lean_object* v_funTypes_2516_, lean_object* v_as_2517_, size_t v_sz_2518_, size_t v_i_2519_, lean_object* v_bs_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_){
_start:
{
lean_object* v___x_2526_; 
v___x_2526_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___redArg(v_a_2515_, v_funTypes_2516_, v_sz_2518_, v_i_2519_, v_bs_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_);
return v___x_2526_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2515_ = stack[0].m_obj;
lean_object* v_funTypes_2516_ = stack[1].m_obj;
lean_object* v_as_2517_ = stack[2].m_obj;
size_t v_sz_2518_ = stack[3].m_num;
size_t v_i_2519_ = stack[4].m_num;
lean_object* v_bs_2520_ = stack[5].m_obj;
lean_object* v___y_2521_ = stack[6].m_obj;
lean_object* v___y_2522_ = stack[7].m_obj;
lean_object* v___y_2523_ = stack[8].m_obj;
lean_object* v___y_2524_ = stack[9].m_obj;
lean_object* v_res_2527_;
v_res_2527_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18(v_a_2515_, v_funTypes_2516_, v_as_2517_, v_sz_2518_, v_i_2519_, v_bs_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_);
stack->m_obj
 = v_res_2527_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___boxed(lean_object* v_a_2528_, lean_object* v_funTypes_2529_, lean_object* v_as_2530_, lean_object* v_sz_2531_, lean_object* v_i_2532_, lean_object* v_bs_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_){
_start:
{
size_t v_sz_boxed_2539_; size_t v_i_boxed_2540_; lean_object* v_res_2541_; 
v_sz_boxed_2539_ = lean_unbox_usize(v_sz_2531_);
lean_dec(v_sz_2531_);
v_i_boxed_2540_ = lean_unbox_usize(v_i_2532_);
lean_dec(v_i_2532_);
v_res_2541_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18(v_a_2528_, v_funTypes_2529_, v_as_2530_, v_sz_boxed_2539_, v_i_boxed_2540_, v_bs_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_);
lean_dec(v___y_2537_);
lean_dec_ref(v___y_2536_);
lean_dec(v___y_2535_);
lean_dec_ref(v___y_2534_);
lean_dec_ref(v_as_2530_);
lean_dec_ref(v_funTypes_2529_);
lean_dec_ref(v_a_2528_);
return v_res_2541_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19(lean_object* v_a_2542_, lean_object* v_a_2543_, lean_object* v_as_2544_, size_t v_sz_2545_, size_t v_i_2546_, lean_object* v_bs_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_){
_start:
{
lean_object* v___x_2553_; 
v___x_2553_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___redArg(v_a_2542_, v_a_2543_, v_sz_2545_, v_i_2546_, v_bs_2547_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_);
return v___x_2553_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2542_ = stack[0].m_obj;
lean_object* v_a_2543_ = stack[1].m_obj;
lean_object* v_as_2544_ = stack[2].m_obj;
size_t v_sz_2545_ = stack[3].m_num;
size_t v_i_2546_ = stack[4].m_num;
lean_object* v_bs_2547_ = stack[5].m_obj;
lean_object* v___y_2548_ = stack[6].m_obj;
lean_object* v___y_2549_ = stack[7].m_obj;
lean_object* v___y_2550_ = stack[8].m_obj;
lean_object* v___y_2551_ = stack[9].m_obj;
lean_object* v_res_2554_;
v_res_2554_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19(v_a_2542_, v_a_2543_, v_as_2544_, v_sz_2545_, v_i_2546_, v_bs_2547_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_);
stack->m_obj
 = v_res_2554_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___boxed(lean_object* v_a_2555_, lean_object* v_a_2556_, lean_object* v_as_2557_, lean_object* v_sz_2558_, lean_object* v_i_2559_, lean_object* v_bs_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_){
_start:
{
size_t v_sz_boxed_2566_; size_t v_i_boxed_2567_; lean_object* v_res_2568_; 
v_sz_boxed_2566_ = lean_unbox_usize(v_sz_2558_);
lean_dec(v_sz_2558_);
v_i_boxed_2567_ = lean_unbox_usize(v_i_2559_);
lean_dec(v_i_2559_);
v_res_2568_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19(v_a_2555_, v_a_2556_, v_as_2557_, v_sz_boxed_2566_, v_i_boxed_2567_, v_bs_2560_, v___y_2561_, v___y_2562_, v___y_2563_, v___y_2564_);
lean_dec(v___y_2564_);
lean_dec_ref(v___y_2563_);
lean_dec(v___y_2562_);
lean_dec_ref(v___y_2561_);
lean_dec_ref(v_as_2557_);
lean_dec_ref(v_a_2556_);
lean_dec_ref(v_a_2555_);
return v_res_2568_;
}
}
lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4(lean_object* v_00_u03b1_2569_, lean_object* v_msg_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_){
_start:
{
lean_object* v___x_2576_; 
v___x_2576_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg(v_msg_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_);
return v___x_2576_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2570_ = stack[1].m_obj;
lean_object* v___y_2571_ = stack[2].m_obj;
lean_object* v___y_2572_ = stack[3].m_obj;
lean_object* v___y_2573_ = stack[4].m_obj;
lean_object* v___y_2574_ = stack[5].m_obj;
lean_object* v_res_2577_;
v_res_2577_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4(lean_box(0), v_msg_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_);
stack->m_obj
 = v_res_2577_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___boxed(lean_object* v_00_u03b1_2578_, lean_object* v_msg_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_){
_start:
{
lean_object* v_res_2585_; 
v_res_2585_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4(v_00_u03b1_2578_, v_msg_2579_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_);
lean_dec(v___y_2583_);
lean_dec_ref(v___y_2582_);
lean_dec(v___y_2581_);
lean_dec_ref(v___y_2580_);
return v_res_2585_;
}
}
uint8_t l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9(lean_object* v_xs_2586_, lean_object* v_ys_2587_, lean_object* v_hsz_2588_, lean_object* v_x_2589_, lean_object* v_x_2590_){
_start:
{
uint8_t v___x_2591_; 
v___x_2591_ = l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9___redArg(v_xs_2586_, v_ys_2587_, v_x_2589_);
return v___x_2591_;
}
}
LEAN_EXPORT void l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_2586_ = stack[0].m_obj;
lean_object* v_ys_2587_ = stack[1].m_obj;
lean_object* v_x_2589_ = stack[3].m_obj;
uint8_t v_res_2592_;
v_res_2592_ = l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9(v_xs_2586_, v_ys_2587_, lean_box(0), v_x_2589_, lean_box(0));
stack->m_num = v_res_2592_;
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9___boxed(lean_object* v_xs_2593_, lean_object* v_ys_2594_, lean_object* v_hsz_2595_, lean_object* v_x_2596_, lean_object* v_x_2597_){
_start:
{
uint8_t v_res_2598_; lean_object* v_r_2599_; 
v_res_2598_ = l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9(v_xs_2593_, v_ys_2594_, v_hsz_2595_, v_x_2596_, v_x_2597_);
lean_dec_ref(v_ys_2594_);
lean_dec_ref(v_xs_2593_);
v_r_2599_ = lean_box(v_res_2598_);
return v_r_2599_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10(lean_object* v_n_2600_, lean_object* v_as_2601_, lean_object* v_lo_2602_, lean_object* v_hi_2603_, lean_object* v_w_2604_, lean_object* v_hlo_2605_, lean_object* v_hhi_2606_){
_start:
{
lean_object* v___x_2607_; 
v___x_2607_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg(v_n_2600_, v_as_2601_, v_lo_2602_, v_hi_2603_);
return v___x_2607_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___boxed(lean_object* v_n_2608_, lean_object* v_as_2609_, lean_object* v_lo_2610_, lean_object* v_hi_2611_, lean_object* v_w_2612_, lean_object* v_hlo_2613_, lean_object* v_hhi_2614_){
_start:
{
lean_object* v_res_2615_; 
v_res_2615_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10(v_n_2608_, v_as_2609_, v_lo_2610_, v_hi_2611_, v_w_2612_, v_hlo_2613_, v_hhi_2614_);
lean_dec(v_hi_2611_);
lean_dec(v_n_2608_);
return v_res_2615_;
}
}
lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15(lean_object* v_00_u03b1_2616_, lean_object* v_00_u03b3_2617_, lean_object* v_xs_2618_, lean_object* v_f_2619_, lean_object* v_as_2620_, lean_object* v_bs_2621_, lean_object* v_i_2622_, lean_object* v_cs_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_){
_start:
{
lean_object* v___x_2629_; 
v___x_2629_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15___redArg(v_xs_2618_, v_f_2619_, v_as_2620_, v_bs_2621_, v_i_2622_, v_cs_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_);
return v___x_2629_;
}
}
LEAN_EXPORT void l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_2618_ = stack[2].m_obj;
lean_object* v_f_2619_ = stack[3].m_obj;
lean_object* v_as_2620_ = stack[4].m_obj;
lean_object* v_bs_2621_ = stack[5].m_obj;
lean_object* v_i_2622_ = stack[6].m_obj;
lean_object* v_cs_2623_ = stack[7].m_obj;
lean_object* v___y_2624_ = stack[8].m_obj;
lean_object* v___y_2625_ = stack[9].m_obj;
lean_object* v___y_2626_ = stack[10].m_obj;
lean_object* v___y_2627_ = stack[11].m_obj;
lean_object* v_res_2630_;
v_res_2630_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15(lean_box(0), lean_box(0), v_xs_2618_, v_f_2619_, v_as_2620_, v_bs_2621_, v_i_2622_, v_cs_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_);
stack->m_obj
 = v_res_2630_;
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15___boxed(lean_object* v_00_u03b1_2631_, lean_object* v_00_u03b3_2632_, lean_object* v_xs_2633_, lean_object* v_f_2634_, lean_object* v_as_2635_, lean_object* v_bs_2636_, lean_object* v_i_2637_, lean_object* v_cs_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_){
_start:
{
lean_object* v_res_2644_; 
v_res_2644_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15(v_00_u03b1_2631_, v_00_u03b3_2632_, v_xs_2633_, v_f_2634_, v_as_2635_, v_bs_2636_, v_i_2637_, v_cs_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_);
lean_dec(v___y_2642_);
lean_dec_ref(v___y_2641_);
lean_dec(v___y_2640_);
lean_dec_ref(v___y_2639_);
lean_dec_ref(v_bs_2636_);
lean_dec_ref(v_as_2635_);
lean_dec_ref(v_xs_2633_);
return v_res_2644_;
}
}
lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25(lean_object* v_env_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_){
_start:
{
lean_object* v___x_2651_; 
v___x_2651_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg(v_env_2645_, v___y_2647_, v___y_2649_);
return v___x_2651_;
}
}
LEAN_EXPORT void l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_2645_ = stack[0].m_obj;
lean_object* v___y_2646_ = stack[1].m_obj;
lean_object* v___y_2647_ = stack[2].m_obj;
lean_object* v___y_2648_ = stack[3].m_obj;
lean_object* v___y_2649_ = stack[4].m_obj;
lean_object* v_res_2652_;
v_res_2652_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25(v_env_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_);
stack->m_obj
 = v_res_2652_;
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___boxed(lean_object* v_env_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_){
_start:
{
lean_object* v_res_2659_; 
v_res_2659_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25(v_env_2653_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_);
lean_dec(v___y_2657_);
lean_dec_ref(v___y_2656_);
lean_dec(v___y_2655_);
lean_dec_ref(v___y_2654_);
return v_res_2659_;
}
}
lean_object* l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23(lean_object* v_00_u03b1_2660_, lean_object* v_env_2661_, lean_object* v_x_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_){
_start:
{
lean_object* v___x_2668_; 
v___x_2668_ = l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23___redArg(v_env_2661_, v_x_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_);
return v___x_2668_;
}
}
LEAN_EXPORT void l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_2661_ = stack[1].m_obj;
lean_object* v_x_2662_ = stack[2].m_obj;
lean_object* v___y_2663_ = stack[3].m_obj;
lean_object* v___y_2664_ = stack[4].m_obj;
lean_object* v___y_2665_ = stack[5].m_obj;
lean_object* v___y_2666_ = stack[6].m_obj;
lean_object* v_res_2669_;
v_res_2669_ = l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23(lean_box(0), v_env_2661_, v_x_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_);
stack->m_obj
 = v_res_2669_;
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23___boxed(lean_object* v_00_u03b1_2670_, lean_object* v_env_2671_, lean_object* v_x_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_){
_start:
{
lean_object* v_res_2678_; 
v_res_2678_ = l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23(v_00_u03b1_2670_, v_env_2671_, v_x_2672_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_);
lean_dec(v___y_2676_);
lean_dec_ref(v___y_2675_);
lean_dec(v___y_2674_);
lean_dec_ref(v___y_2673_);
return v_res_2678_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11(lean_object* v_n_2679_, lean_object* v_lo_2680_, lean_object* v_hi_2681_, lean_object* v_hhi_2682_, lean_object* v_pivot_2683_, lean_object* v_as_2684_, lean_object* v_i_2685_, lean_object* v_k_2686_, lean_object* v_ilo_2687_, lean_object* v_ik_2688_, lean_object* v_w_2689_){
_start:
{
lean_object* v___x_2690_; 
v___x_2690_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11___redArg(v_hi_2681_, v_pivot_2683_, v_as_2684_, v_i_2685_, v_k_2686_);
return v___x_2690_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11___boxed(lean_object* v_n_2691_, lean_object* v_lo_2692_, lean_object* v_hi_2693_, lean_object* v_hhi_2694_, lean_object* v_pivot_2695_, lean_object* v_as_2696_, lean_object* v_i_2697_, lean_object* v_k_2698_, lean_object* v_ilo_2699_, lean_object* v_ik_2700_, lean_object* v_w_2701_){
_start:
{
lean_object* v_res_2702_; 
v_res_2702_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11(v_n_2691_, v_lo_2692_, v_hi_2693_, v_hhi_2694_, v_pivot_2695_, v_as_2696_, v_i_2697_, v_k_2698_, v_ilo_2699_, v_ik_2700_, v_w_2701_);
lean_dec(v_pivot_2695_);
lean_dec(v_hi_2693_);
lean_dec(v_lo_2692_);
lean_dec(v_n_2691_);
return v_res_2702_;
}
}
uint8_t l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___lam__0(lean_object* v_x_2703_){
_start:
{
uint8_t v___x_2704_; 
v___x_2704_ = 0;
return v___x_2704_;
}
}
LEAN_EXPORT void l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2703_ = stack[0].m_obj;
uint8_t v_res_2705_;
v_res_2705_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___lam__0(v_x_2703_);
stack->m_num = v_res_2705_;
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___lam__0___boxed(lean_object* v_x_2706_){
_start:
{
uint8_t v_res_2707_; lean_object* v_r_2708_; 
v_res_2707_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___lam__0(v_x_2706_);
lean_dec(v_x_2706_);
v_r_2708_ = lean_box(v_res_2707_);
return v_r_2708_;
}
}
uint8_t l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___lam__1(lean_object* v_fvarId_2709_, lean_object* v_x_2710_){
_start:
{
uint8_t v___x_2711_; 
v___x_2711_ = l_Lean_instBEqFVarId_beq(v_fvarId_2709_, v_x_2710_);
return v___x_2711_;
}
}
LEAN_EXPORT void l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_2709_ = stack[0].m_obj;
lean_object* v_x_2710_ = stack[1].m_obj;
uint8_t v_res_2712_;
v_res_2712_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___lam__1(v_fvarId_2709_, v_x_2710_);
stack->m_num = v_res_2712_;
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___lam__1___boxed(lean_object* v_fvarId_2713_, lean_object* v_x_2714_){
_start:
{
uint8_t v_res_2715_; lean_object* v_r_2716_; 
v_res_2715_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___lam__1(v_fvarId_2713_, v_x_2714_);
lean_dec(v_x_2714_);
lean_dec(v_fvarId_2713_);
v_r_2716_ = lean_box(v_res_2715_);
return v_r_2716_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; 
v___x_2718_ = lean_box(0);
v___x_2719_ = lean_unsigned_to_nat(16u);
v___x_2720_ = lean_mk_array(v___x_2719_, v___x_2718_);
return v___x_2720_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; 
v___x_2721_ = lean_obj_once(&l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__1, &l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__1_once, _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__1);
v___x_2722_ = lean_unsigned_to_nat(0u);
v___x_2723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2723_, 0, v___x_2722_);
lean_ctor_set(v___x_2723_, 1, v___x_2721_);
return v___x_2723_;
}
}
lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg(lean_object* v_e_2724_, lean_object* v_fvarId_2725_, lean_object* v___y_2726_){
_start:
{
lean_object* v___f_2728_; lean_object* v___f_2729_; lean_object* v___x_2730_; uint8_t v_fst_2732_; lean_object* v_mctx_2733_; lean_object* v___y_2751_; lean_object* v_mctx_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; uint8_t v___x_2759_; 
v___f_2728_ = ((lean_object*)(l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__0));
v___f_2729_ = lean_alloc_closure((void*)(l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_2729_, 0, v_fvarId_2725_);
v___x_2730_ = lean_st_ref_get(v___y_2726_);
v_mctx_2756_ = lean_ctor_get(v___x_2730_, 0);
lean_inc_ref_n(v_mctx_2756_, 2);
lean_dec(v___x_2730_);
v___x_2757_ = lean_obj_once(&l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__2, &l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__2_once, _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__2);
v___x_2758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2758_, 0, v___x_2757_);
lean_ctor_set(v___x_2758_, 1, v_mctx_2756_);
v___x_2759_ = l_Lean_Expr_hasFVar(v_e_2724_);
if (v___x_2759_ == 0)
{
uint8_t v___x_2760_; 
v___x_2760_ = l_Lean_Expr_hasMVar(v_e_2724_);
if (v___x_2760_ == 0)
{
lean_dec_ref_known(v___x_2758_, 2);
lean_dec_ref(v___f_2729_);
lean_dec_ref(v_e_2724_);
v_fst_2732_ = v___x_2760_;
v_mctx_2733_ = v_mctx_2756_;
goto v___jp_2731_;
}
else
{
lean_object* v___x_2761_; 
lean_dec_ref(v_mctx_2756_);
v___x_2761_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2729_, v___f_2728_, v_e_2724_, v___x_2758_);
v___y_2751_ = v___x_2761_;
goto v___jp_2750_;
}
}
else
{
lean_object* v___x_2762_; 
lean_dec_ref(v_mctx_2756_);
v___x_2762_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2729_, v___f_2728_, v_e_2724_, v___x_2758_);
v___y_2751_ = v___x_2762_;
goto v___jp_2750_;
}
v___jp_2731_:
{
lean_object* v___x_2734_; lean_object* v_cache_2735_; lean_object* v_zetaDeltaFVarIds_2736_; lean_object* v_postponed_2737_; lean_object* v_diag_2738_; lean_object* v___x_2740_; uint8_t v_isShared_2741_; uint8_t v_isSharedCheck_2748_; 
v___x_2734_ = lean_st_ref_take(v___y_2726_);
v_cache_2735_ = lean_ctor_get(v___x_2734_, 1);
v_zetaDeltaFVarIds_2736_ = lean_ctor_get(v___x_2734_, 2);
v_postponed_2737_ = lean_ctor_get(v___x_2734_, 3);
v_diag_2738_ = lean_ctor_get(v___x_2734_, 4);
v_isSharedCheck_2748_ = !lean_is_exclusive(v___x_2734_);
if (v_isSharedCheck_2748_ == 0)
{
lean_object* v_unused_2749_; 
v_unused_2749_ = lean_ctor_get(v___x_2734_, 0);
lean_dec(v_unused_2749_);
v___x_2740_ = v___x_2734_;
v_isShared_2741_ = v_isSharedCheck_2748_;
goto v_resetjp_2739_;
}
else
{
lean_inc(v_diag_2738_);
lean_inc(v_postponed_2737_);
lean_inc(v_zetaDeltaFVarIds_2736_);
lean_inc(v_cache_2735_);
lean_dec(v___x_2734_);
v___x_2740_ = lean_box(0);
v_isShared_2741_ = v_isSharedCheck_2748_;
goto v_resetjp_2739_;
}
v_resetjp_2739_:
{
lean_object* v___x_2743_; 
if (v_isShared_2741_ == 0)
{
lean_ctor_set(v___x_2740_, 0, v_mctx_2733_);
v___x_2743_ = v___x_2740_;
goto v_reusejp_2742_;
}
else
{
lean_object* v_reuseFailAlloc_2747_; 
v_reuseFailAlloc_2747_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2747_, 0, v_mctx_2733_);
lean_ctor_set(v_reuseFailAlloc_2747_, 1, v_cache_2735_);
lean_ctor_set(v_reuseFailAlloc_2747_, 2, v_zetaDeltaFVarIds_2736_);
lean_ctor_set(v_reuseFailAlloc_2747_, 3, v_postponed_2737_);
lean_ctor_set(v_reuseFailAlloc_2747_, 4, v_diag_2738_);
v___x_2743_ = v_reuseFailAlloc_2747_;
goto v_reusejp_2742_;
}
v_reusejp_2742_:
{
lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; 
v___x_2744_ = lean_st_ref_put(v___y_2726_, v___x_2743_);
v___x_2745_ = lean_box(v_fst_2732_);
v___x_2746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2746_, 0, v___x_2745_);
return v___x_2746_;
}
}
}
v___jp_2750_:
{
lean_object* v_snd_2752_; lean_object* v_fst_2753_; lean_object* v_mctx_2754_; uint8_t v___x_2755_; 
v_snd_2752_ = lean_ctor_get(v___y_2751_, 1);
lean_inc(v_snd_2752_);
v_fst_2753_ = lean_ctor_get(v___y_2751_, 0);
lean_inc(v_fst_2753_);
lean_dec_ref(v___y_2751_);
v_mctx_2754_ = lean_ctor_get(v_snd_2752_, 1);
lean_inc_ref(v_mctx_2754_);
lean_dec(v_snd_2752_);
v___x_2755_ = lean_unbox(v_fst_2753_);
lean_dec(v_fst_2753_);
v_fst_2732_ = v___x_2755_;
v_mctx_2733_ = v_mctx_2754_;
goto v___jp_2731_;
}
}
}
LEAN_EXPORT void l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2724_ = stack[0].m_obj;
lean_object* v_fvarId_2725_ = stack[1].m_obj;
lean_object* v___y_2726_ = stack[2].m_obj;
lean_object* v_res_2763_;
v_res_2763_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg(v_e_2724_, v_fvarId_2725_, v___y_2726_);
stack->m_obj
 = v_res_2763_;
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___boxed(lean_object* v_e_2764_, lean_object* v_fvarId_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_){
_start:
{
lean_object* v_res_2768_; 
v_res_2768_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg(v_e_2764_, v_fvarId_2765_, v___y_2766_);
lean_dec(v___y_2766_);
return v_res_2768_;
}
}
lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5(lean_object* v_e_2769_, lean_object* v_fvarId_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_){
_start:
{
lean_object* v___x_2776_; 
v___x_2776_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg(v_e_2769_, v_fvarId_2770_, v___y_2772_);
return v___x_2776_;
}
}
LEAN_EXPORT void l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2769_ = stack[0].m_obj;
lean_object* v_fvarId_2770_ = stack[1].m_obj;
lean_object* v___y_2771_ = stack[2].m_obj;
lean_object* v___y_2772_ = stack[3].m_obj;
lean_object* v___y_2773_ = stack[4].m_obj;
lean_object* v___y_2774_ = stack[5].m_obj;
lean_object* v_res_2777_;
v_res_2777_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5(v_e_2769_, v_fvarId_2770_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_);
stack->m_obj
 = v_res_2777_;
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___boxed(lean_object* v_e_2778_, lean_object* v_fvarId_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_){
_start:
{
lean_object* v_res_2785_; 
v_res_2785_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5(v_e_2778_, v_fvarId_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_);
lean_dec(v___y_2783_);
lean_dec_ref(v___y_2782_);
lean_dec(v___y_2781_);
lean_dec_ref(v___y_2780_);
return v_res_2785_;
}
}
lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg___lam__0(lean_object* v_k_2786_, lean_object* v_b_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_){
_start:
{
lean_object* v___x_2793_; 
lean_inc(v___y_2791_);
lean_inc_ref(v___y_2790_);
lean_inc(v___y_2789_);
lean_inc_ref(v___y_2788_);
v___x_2793_ = lean_apply_6(v_k_2786_, v_b_2787_, v___y_2788_, v___y_2789_, v___y_2790_, v___y_2791_, lean_box(0));
return v___x_2793_;
}
}
LEAN_EXPORT void l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_2786_ = stack[0].m_obj;
lean_object* v_b_2787_ = stack[1].m_obj;
lean_object* v___y_2788_ = stack[2].m_obj;
lean_object* v___y_2789_ = stack[3].m_obj;
lean_object* v___y_2790_ = stack[4].m_obj;
lean_object* v___y_2791_ = stack[5].m_obj;
lean_object* v_res_2794_;
v_res_2794_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg___lam__0(v_k_2786_, v_b_2787_, v___y_2788_, v___y_2789_, v___y_2790_, v___y_2791_);
stack->m_obj
 = v_res_2794_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg___lam__0___boxed(lean_object* v_k_2795_, lean_object* v_b_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_){
_start:
{
lean_object* v_res_2802_; 
v_res_2802_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg___lam__0(v_k_2795_, v_b_2796_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_);
lean_dec(v___y_2800_);
lean_dec_ref(v___y_2799_);
lean_dec(v___y_2798_);
lean_dec_ref(v___y_2797_);
return v_res_2802_;
}
}
lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg(lean_object* v_perm_2803_, lean_object* v_type_2804_, lean_object* v_k_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_){
_start:
{
lean_object* v___f_2811_; lean_object* v___x_2812_; 
v___f_2811_ = lean_alloc_closure((void*)(l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2811_, 0, v_k_2805_);
v___x_2812_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl(lean_box(0), v_perm_2803_, v_type_2804_, v___f_2811_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_);
if (lean_obj_tag(v___x_2812_) == 0)
{
lean_object* v_a_2813_; lean_object* v___x_2815_; uint8_t v_isShared_2816_; uint8_t v_isSharedCheck_2820_; 
v_a_2813_ = lean_ctor_get(v___x_2812_, 0);
v_isSharedCheck_2820_ = !lean_is_exclusive(v___x_2812_);
if (v_isSharedCheck_2820_ == 0)
{
v___x_2815_ = v___x_2812_;
v_isShared_2816_ = v_isSharedCheck_2820_;
goto v_resetjp_2814_;
}
else
{
lean_inc(v_a_2813_);
lean_dec(v___x_2812_);
v___x_2815_ = lean_box(0);
v_isShared_2816_ = v_isSharedCheck_2820_;
goto v_resetjp_2814_;
}
v_resetjp_2814_:
{
lean_object* v___x_2818_; 
if (v_isShared_2816_ == 0)
{
v___x_2818_ = v___x_2815_;
goto v_reusejp_2817_;
}
else
{
lean_object* v_reuseFailAlloc_2819_; 
v_reuseFailAlloc_2819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2819_, 0, v_a_2813_);
v___x_2818_ = v_reuseFailAlloc_2819_;
goto v_reusejp_2817_;
}
v_reusejp_2817_:
{
return v___x_2818_;
}
}
}
else
{
lean_object* v_a_2821_; lean_object* v___x_2823_; uint8_t v_isShared_2824_; uint8_t v_isSharedCheck_2828_; 
v_a_2821_ = lean_ctor_get(v___x_2812_, 0);
v_isSharedCheck_2828_ = !lean_is_exclusive(v___x_2812_);
if (v_isSharedCheck_2828_ == 0)
{
v___x_2823_ = v___x_2812_;
v_isShared_2824_ = v_isSharedCheck_2828_;
goto v_resetjp_2822_;
}
else
{
lean_inc(v_a_2821_);
lean_dec(v___x_2812_);
v___x_2823_ = lean_box(0);
v_isShared_2824_ = v_isSharedCheck_2828_;
goto v_resetjp_2822_;
}
v_resetjp_2822_:
{
lean_object* v___x_2826_; 
if (v_isShared_2824_ == 0)
{
v___x_2826_ = v___x_2823_;
goto v_reusejp_2825_;
}
else
{
lean_object* v_reuseFailAlloc_2827_; 
v_reuseFailAlloc_2827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2827_, 0, v_a_2821_);
v___x_2826_ = v_reuseFailAlloc_2827_;
goto v_reusejp_2825_;
}
v_reusejp_2825_:
{
return v___x_2826_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_perm_2803_ = stack[0].m_obj;
lean_object* v_type_2804_ = stack[1].m_obj;
lean_object* v_k_2805_ = stack[2].m_obj;
lean_object* v___y_2806_ = stack[3].m_obj;
lean_object* v___y_2807_ = stack[4].m_obj;
lean_object* v___y_2808_ = stack[5].m_obj;
lean_object* v___y_2809_ = stack[6].m_obj;
lean_object* v_res_2829_;
v_res_2829_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg(v_perm_2803_, v_type_2804_, v_k_2805_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_);
stack->m_obj
 = v_res_2829_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg___boxed(lean_object* v_perm_2830_, lean_object* v_type_2831_, lean_object* v_k_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_){
_start:
{
lean_object* v_res_2838_; 
v_res_2838_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg(v_perm_2830_, v_type_2831_, v_k_2832_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_);
lean_dec(v___y_2836_);
lean_dec_ref(v___y_2835_);
lean_dec(v___y_2834_);
lean_dec_ref(v___y_2833_);
return v_res_2838_;
}
}
lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13(lean_object* v_00_u03b1_2839_, lean_object* v_perm_2840_, lean_object* v_type_2841_, lean_object* v_k_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_){
_start:
{
lean_object* v___x_2848_; 
v___x_2848_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg(v_perm_2840_, v_type_2841_, v_k_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_);
return v___x_2848_;
}
}
LEAN_EXPORT void l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13_0interp(lean_interpreter_value* stack)
{
lean_object* v_perm_2840_ = stack[1].m_obj;
lean_object* v_type_2841_ = stack[2].m_obj;
lean_object* v_k_2842_ = stack[3].m_obj;
lean_object* v___y_2843_ = stack[4].m_obj;
lean_object* v___y_2844_ = stack[5].m_obj;
lean_object* v___y_2845_ = stack[6].m_obj;
lean_object* v___y_2846_ = stack[7].m_obj;
lean_object* v_res_2849_;
v_res_2849_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13(lean_box(0), v_perm_2840_, v_type_2841_, v_k_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_);
stack->m_obj
 = v_res_2849_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___boxed(lean_object* v_00_u03b1_2850_, lean_object* v_perm_2851_, lean_object* v_type_2852_, lean_object* v_k_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_){
_start:
{
lean_object* v_res_2859_; 
v_res_2859_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13(v_00_u03b1_2850_, v_perm_2851_, v_type_2852_, v_k_2853_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_);
lean_dec(v___y_2857_);
lean_dec_ref(v___y_2856_);
lean_dec(v___y_2855_);
lean_dec_ref(v___y_2854_);
return v_res_2859_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1(lean_object* v_a_2860_, lean_object* v_fst_2861_, lean_object* v_fst_2862_, lean_object* v___x_2863_, lean_object* v___x_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_){
_start:
{
lean_object* v___x_2870_; 
lean_inc_ref(v_fst_2861_);
v___x_2870_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion(v_a_2860_, v_fst_2861_, v_fst_2862_, v___x_2863_, v___y_2865_, v___y_2866_, v___y_2867_, v___y_2868_);
if (lean_obj_tag(v___x_2870_) == 0)
{
lean_object* v_a_2871_; lean_object* v___x_2873_; uint8_t v_isShared_2874_; uint8_t v_isSharedCheck_2880_; 
v_a_2871_ = lean_ctor_get(v___x_2870_, 0);
v_isSharedCheck_2880_ = !lean_is_exclusive(v___x_2870_);
if (v_isSharedCheck_2880_ == 0)
{
v___x_2873_ = v___x_2870_;
v_isShared_2874_ = v_isSharedCheck_2880_;
goto v_resetjp_2872_;
}
else
{
lean_inc(v_a_2871_);
lean_dec(v___x_2870_);
v___x_2873_ = lean_box(0);
v_isShared_2874_ = v_isSharedCheck_2880_;
goto v_resetjp_2872_;
}
v_resetjp_2872_:
{
lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2878_; 
v___x_2875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2875_, 0, v_a_2871_);
lean_ctor_set(v___x_2875_, 1, v_fst_2861_);
v___x_2876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2876_, 0, v___x_2864_);
lean_ctor_set(v___x_2876_, 1, v___x_2875_);
if (v_isShared_2874_ == 0)
{
lean_ctor_set(v___x_2873_, 0, v___x_2876_);
v___x_2878_ = v___x_2873_;
goto v_reusejp_2877_;
}
else
{
lean_object* v_reuseFailAlloc_2879_; 
v_reuseFailAlloc_2879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2879_, 0, v___x_2876_);
v___x_2878_ = v_reuseFailAlloc_2879_;
goto v_reusejp_2877_;
}
v_reusejp_2877_:
{
return v___x_2878_;
}
}
}
else
{
lean_object* v_a_2881_; lean_object* v___x_2883_; uint8_t v_isShared_2884_; uint8_t v_isSharedCheck_2888_; 
lean_dec_ref(v___x_2864_);
lean_dec_ref(v_fst_2861_);
v_a_2881_ = lean_ctor_get(v___x_2870_, 0);
v_isSharedCheck_2888_ = !lean_is_exclusive(v___x_2870_);
if (v_isSharedCheck_2888_ == 0)
{
v___x_2883_ = v___x_2870_;
v_isShared_2884_ = v_isSharedCheck_2888_;
goto v_resetjp_2882_;
}
else
{
lean_inc(v_a_2881_);
lean_dec(v___x_2870_);
v___x_2883_ = lean_box(0);
v_isShared_2884_ = v_isSharedCheck_2888_;
goto v_resetjp_2882_;
}
v_resetjp_2882_:
{
lean_object* v___x_2886_; 
if (v_isShared_2884_ == 0)
{
v___x_2886_ = v___x_2883_;
goto v_reusejp_2885_;
}
else
{
lean_object* v_reuseFailAlloc_2887_; 
v_reuseFailAlloc_2887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2887_, 0, v_a_2881_);
v___x_2886_ = v_reuseFailAlloc_2887_;
goto v_reusejp_2885_;
}
v_reusejp_2885_:
{
return v___x_2886_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2860_ = stack[0].m_obj;
lean_object* v_fst_2861_ = stack[1].m_obj;
lean_object* v_fst_2862_ = stack[2].m_obj;
lean_object* v___x_2863_ = stack[3].m_obj;
lean_object* v___x_2864_ = stack[4].m_obj;
lean_object* v___y_2865_ = stack[5].m_obj;
lean_object* v___y_2866_ = stack[6].m_obj;
lean_object* v___y_2867_ = stack[7].m_obj;
lean_object* v___y_2868_ = stack[8].m_obj;
lean_object* v_res_2889_;
v_res_2889_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1(v_a_2860_, v_fst_2861_, v_fst_2862_, v___x_2863_, v___x_2864_, v___y_2865_, v___y_2866_, v___y_2867_, v___y_2868_);
stack->m_obj
 = v_res_2889_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___boxed(lean_object* v_a_2890_, lean_object* v_fst_2891_, lean_object* v_fst_2892_, lean_object* v___x_2893_, lean_object* v___x_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_){
_start:
{
lean_object* v_res_2900_; 
v_res_2900_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1(v_a_2890_, v_fst_2891_, v_fst_2892_, v___x_2893_, v___x_2894_, v___y_2895_, v___y_2896_, v___y_2897_, v___y_2898_);
lean_dec(v___y_2898_);
lean_dec_ref(v___y_2897_);
lean_dec(v___y_2896_);
lean_dec_ref(v___y_2895_);
return v_res_2900_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__3(size_t v_sz_2901_, size_t v_i_2902_, lean_object* v_bs_2903_){
_start:
{
uint8_t v___x_2904_; 
v___x_2904_ = lean_usize_dec_lt(v_i_2902_, v_sz_2901_);
if (v___x_2904_ == 0)
{
return v_bs_2903_;
}
else
{
lean_object* v_v_2905_; lean_object* v___x_2906_; lean_object* v_bs_x27_2907_; lean_object* v___x_2908_; size_t v___x_2909_; size_t v___x_2910_; lean_object* v___x_2911_; 
v_v_2905_ = lean_array_uget(v_bs_2903_, v_i_2902_);
v___x_2906_ = lean_unsigned_to_nat(0u);
v_bs_x27_2907_ = lean_array_uset(v_bs_2903_, v_i_2902_, v___x_2906_);
v___x_2908_ = l_Lean_Elab_Structural_RecArgInfo_indicesAndRecArgPos(v_v_2905_);
v___x_2909_ = ((size_t)1ULL);
v___x_2910_ = lean_usize_add(v_i_2902_, v___x_2909_);
v___x_2911_ = lean_array_uset(v_bs_x27_2907_, v_i_2902_, v___x_2908_);
v_i_2902_ = v___x_2910_;
v_bs_2903_ = v___x_2911_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__3_0interp(lean_interpreter_value* stack)
{
size_t v_sz_2901_ = stack[0].m_num;
size_t v_i_2902_ = stack[1].m_num;
lean_object* v_bs_2903_ = stack[2].m_obj;
lean_object* v_res_2913_;
v_res_2913_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__3(v_sz_2901_, v_i_2902_, v_bs_2903_);
stack->m_obj
 = v_res_2913_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__3___boxed(lean_object* v_sz_2914_, lean_object* v_i_2915_, lean_object* v_bs_2916_){
_start:
{
size_t v_sz_boxed_2917_; size_t v_i_boxed_2918_; lean_object* v_res_2919_; 
v_sz_boxed_2917_ = lean_unbox_usize(v_sz_2914_);
lean_dec(v_sz_2914_);
v_i_boxed_2918_ = lean_unbox_usize(v_i_2915_);
lean_dec(v_i_2915_);
v_res_2919_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__3(v_sz_boxed_2917_, v_i_boxed_2918_, v_bs_2916_);
return v_res_2919_;
}
}
lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___redArg(lean_object* v_lctx_2920_, lean_object* v_localInsts_2921_, lean_object* v_x_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_){
_start:
{
lean_object* v___x_2928_; 
v___x_2928_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_2920_, v_localInsts_2921_, v_x_2922_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_);
if (lean_obj_tag(v___x_2928_) == 0)
{
lean_object* v_a_2929_; lean_object* v___x_2931_; uint8_t v_isShared_2932_; uint8_t v_isSharedCheck_2936_; 
v_a_2929_ = lean_ctor_get(v___x_2928_, 0);
v_isSharedCheck_2936_ = !lean_is_exclusive(v___x_2928_);
if (v_isSharedCheck_2936_ == 0)
{
v___x_2931_ = v___x_2928_;
v_isShared_2932_ = v_isSharedCheck_2936_;
goto v_resetjp_2930_;
}
else
{
lean_inc(v_a_2929_);
lean_dec(v___x_2928_);
v___x_2931_ = lean_box(0);
v_isShared_2932_ = v_isSharedCheck_2936_;
goto v_resetjp_2930_;
}
v_resetjp_2930_:
{
lean_object* v___x_2934_; 
if (v_isShared_2932_ == 0)
{
v___x_2934_ = v___x_2931_;
goto v_reusejp_2933_;
}
else
{
lean_object* v_reuseFailAlloc_2935_; 
v_reuseFailAlloc_2935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2935_, 0, v_a_2929_);
v___x_2934_ = v_reuseFailAlloc_2935_;
goto v_reusejp_2933_;
}
v_reusejp_2933_:
{
return v___x_2934_;
}
}
}
else
{
lean_object* v_a_2937_; lean_object* v___x_2939_; uint8_t v_isShared_2940_; uint8_t v_isSharedCheck_2944_; 
v_a_2937_ = lean_ctor_get(v___x_2928_, 0);
v_isSharedCheck_2944_ = !lean_is_exclusive(v___x_2928_);
if (v_isSharedCheck_2944_ == 0)
{
v___x_2939_ = v___x_2928_;
v_isShared_2940_ = v_isSharedCheck_2944_;
goto v_resetjp_2938_;
}
else
{
lean_inc(v_a_2937_);
lean_dec(v___x_2928_);
v___x_2939_ = lean_box(0);
v_isShared_2940_ = v_isSharedCheck_2944_;
goto v_resetjp_2938_;
}
v_resetjp_2938_:
{
lean_object* v___x_2942_; 
if (v_isShared_2940_ == 0)
{
v___x_2942_ = v___x_2939_;
goto v_reusejp_2941_;
}
else
{
lean_object* v_reuseFailAlloc_2943_; 
v_reuseFailAlloc_2943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2943_, 0, v_a_2937_);
v___x_2942_ = v_reuseFailAlloc_2943_;
goto v_reusejp_2941_;
}
v_reusejp_2941_:
{
return v___x_2942_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_lctx_2920_ = stack[0].m_obj;
lean_object* v_localInsts_2921_ = stack[1].m_obj;
lean_object* v_x_2922_ = stack[2].m_obj;
lean_object* v___y_2923_ = stack[3].m_obj;
lean_object* v___y_2924_ = stack[4].m_obj;
lean_object* v___y_2925_ = stack[5].m_obj;
lean_object* v___y_2926_ = stack[6].m_obj;
lean_object* v_res_2945_;
v_res_2945_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___redArg(v_lctx_2920_, v_localInsts_2921_, v_x_2922_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_);
stack->m_obj
 = v_res_2945_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___redArg___boxed(lean_object* v_lctx_2946_, lean_object* v_localInsts_2947_, lean_object* v_x_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_){
_start:
{
lean_object* v_res_2954_; 
v_res_2954_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___redArg(v_lctx_2946_, v_localInsts_2947_, v_x_2948_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_);
lean_dec(v___y_2952_);
lean_dec_ref(v___y_2951_);
lean_dec(v___y_2950_);
lean_dec_ref(v___y_2949_);
return v_res_2954_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__12(lean_object* v_as_2955_, size_t v_i_2956_, size_t v_stop_2957_, lean_object* v_b_2958_){
_start:
{
uint8_t v___x_2959_; 
v___x_2959_ = lean_usize_dec_eq(v_i_2956_, v_stop_2957_);
if (v___x_2959_ == 0)
{
lean_object* v___x_2960_; lean_object* v___x_2961_; size_t v___x_2962_; size_t v___x_2963_; 
v___x_2960_ = lean_array_uget_borrowed(v_as_2955_, v_i_2956_);
v___x_2961_ = l_Lean_LocalContext_erase(v_b_2958_, v___x_2960_);
v___x_2962_ = ((size_t)1ULL);
v___x_2963_ = lean_usize_add(v_i_2956_, v___x_2962_);
v_i_2956_ = v___x_2963_;
v_b_2958_ = v___x_2961_;
goto _start;
}
else
{
return v_b_2958_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__12_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2955_ = stack[0].m_obj;
size_t v_i_2956_ = stack[1].m_num;
size_t v_stop_2957_ = stack[2].m_num;
lean_object* v_b_2958_ = stack[3].m_obj;
lean_object* v_res_2965_;
v_res_2965_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__12(v_as_2955_, v_i_2956_, v_stop_2957_, v_b_2958_);
stack->m_obj
 = v_res_2965_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__12___boxed(lean_object* v_as_2966_, lean_object* v_i_2967_, lean_object* v_stop_2968_, lean_object* v_b_2969_){
_start:
{
size_t v_i_boxed_2970_; size_t v_stop_boxed_2971_; lean_object* v_res_2972_; 
v_i_boxed_2970_ = lean_unbox_usize(v_i_2967_);
lean_dec(v_i_2967_);
v_stop_boxed_2971_ = lean_unbox_usize(v_stop_2968_);
lean_dec(v_stop_2968_);
v_res_2972_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__12(v_as_2966_, v_i_boxed_2970_, v_stop_boxed_2971_, v_b_2969_);
lean_dec_ref(v_as_2966_);
return v_res_2972_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9_spec__11(lean_object* v_a_2973_, lean_object* v_as_2974_, size_t v_i_2975_, size_t v_stop_2976_){
_start:
{
uint8_t v___x_2977_; 
v___x_2977_ = lean_usize_dec_eq(v_i_2975_, v_stop_2976_);
if (v___x_2977_ == 0)
{
lean_object* v___x_2978_; uint8_t v___x_2979_; 
v___x_2978_ = lean_array_uget_borrowed(v_as_2974_, v_i_2975_);
v___x_2979_ = l_Lean_instBEqFVarId_beq(v_a_2973_, v___x_2978_);
if (v___x_2979_ == 0)
{
size_t v___x_2980_; size_t v___x_2981_; 
v___x_2980_ = ((size_t)1ULL);
v___x_2981_ = lean_usize_add(v_i_2975_, v___x_2980_);
v_i_2975_ = v___x_2981_;
goto _start;
}
else
{
return v___x_2979_;
}
}
else
{
uint8_t v___x_2983_; 
v___x_2983_ = 0;
return v___x_2983_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2973_ = stack[0].m_obj;
lean_object* v_as_2974_ = stack[1].m_obj;
size_t v_i_2975_ = stack[2].m_num;
size_t v_stop_2976_ = stack[3].m_num;
uint8_t v_res_2984_;
v_res_2984_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9_spec__11(v_a_2973_, v_as_2974_, v_i_2975_, v_stop_2976_);
stack->m_num = v_res_2984_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9_spec__11___boxed(lean_object* v_a_2985_, lean_object* v_as_2986_, lean_object* v_i_2987_, lean_object* v_stop_2988_){
_start:
{
size_t v_i_boxed_2989_; size_t v_stop_boxed_2990_; uint8_t v_res_2991_; lean_object* v_r_2992_; 
v_i_boxed_2989_ = lean_unbox_usize(v_i_2987_);
lean_dec(v_i_2987_);
v_stop_boxed_2990_ = lean_unbox_usize(v_stop_2988_);
lean_dec(v_stop_2988_);
v_res_2991_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9_spec__11(v_a_2985_, v_as_2986_, v_i_boxed_2989_, v_stop_boxed_2990_);
lean_dec_ref(v_as_2986_);
lean_dec(v_a_2985_);
v_r_2992_ = lean_box(v_res_2991_);
return v_r_2992_;
}
}
uint8_t l_Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9(lean_object* v_as_2993_, lean_object* v_a_2994_){
_start:
{
lean_object* v___x_2995_; lean_object* v___x_2996_; uint8_t v___x_2997_; 
v___x_2995_ = lean_unsigned_to_nat(0u);
v___x_2996_ = lean_array_get_size(v_as_2993_);
v___x_2997_ = lean_nat_dec_lt(v___x_2995_, v___x_2996_);
if (v___x_2997_ == 0)
{
return v___x_2997_;
}
else
{
if (v___x_2997_ == 0)
{
return v___x_2997_;
}
else
{
size_t v___x_2998_; size_t v___x_2999_; uint8_t v___x_3000_; 
v___x_2998_ = ((size_t)0ULL);
v___x_2999_ = lean_usize_of_nat(v___x_2996_);
v___x_3000_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9_spec__11(v_a_2994_, v_as_2993_, v___x_2998_, v___x_2999_);
return v___x_3000_;
}
}
}
}
LEAN_EXPORT void l_Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2993_ = stack[0].m_obj;
lean_object* v_a_2994_ = stack[1].m_obj;
uint8_t v_res_3001_;
v_res_3001_ = l_Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9(v_as_2993_, v_a_2994_);
stack->m_num = v_res_3001_;
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9___boxed(lean_object* v_as_3002_, lean_object* v_a_3003_){
_start:
{
uint8_t v_res_3004_; lean_object* v_r_3005_; 
v_res_3004_ = l_Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9(v_as_3002_, v_a_3003_);
lean_dec(v_a_3003_);
lean_dec_ref(v_as_3002_);
v_r_3005_ = lean_box(v_res_3004_);
return v_r_3005_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__11(lean_object* v_fvarIds_3006_, lean_object* v_as_3007_, size_t v_i_3008_, size_t v_stop_3009_, lean_object* v_b_3010_){
_start:
{
lean_object* v___y_3012_; uint8_t v___x_3016_; 
v___x_3016_ = lean_usize_dec_eq(v_i_3008_, v_stop_3009_);
if (v___x_3016_ == 0)
{
lean_object* v___x_3017_; lean_object* v_fvar_3018_; lean_object* v___x_3019_; uint8_t v___x_3020_; 
v___x_3017_ = lean_array_uget_borrowed(v_as_3007_, v_i_3008_);
v_fvar_3018_ = lean_ctor_get(v___x_3017_, 1);
v___x_3019_ = l_Lean_Expr_fvarId_x21(v_fvar_3018_);
v___x_3020_ = l_Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9(v_fvarIds_3006_, v___x_3019_);
lean_dec(v___x_3019_);
if (v___x_3020_ == 0)
{
lean_object* v___x_3021_; 
lean_inc(v___x_3017_);
v___x_3021_ = lean_array_push(v_b_3010_, v___x_3017_);
v___y_3012_ = v___x_3021_;
goto v___jp_3011_;
}
else
{
v___y_3012_ = v_b_3010_;
goto v___jp_3011_;
}
}
else
{
return v_b_3010_;
}
v___jp_3011_:
{
size_t v___x_3013_; size_t v___x_3014_; 
v___x_3013_ = ((size_t)1ULL);
v___x_3014_ = lean_usize_add(v_i_3008_, v___x_3013_);
v_i_3008_ = v___x_3014_;
v_b_3010_ = v___y_3012_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarIds_3006_ = stack[0].m_obj;
lean_object* v_as_3007_ = stack[1].m_obj;
size_t v_i_3008_ = stack[2].m_num;
size_t v_stop_3009_ = stack[3].m_num;
lean_object* v_b_3010_ = stack[4].m_obj;
lean_object* v_res_3022_;
v_res_3022_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__11(v_fvarIds_3006_, v_as_3007_, v_i_3008_, v_stop_3009_, v_b_3010_);
stack->m_obj
 = v_res_3022_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__11___boxed(lean_object* v_fvarIds_3023_, lean_object* v_as_3024_, lean_object* v_i_3025_, lean_object* v_stop_3026_, lean_object* v_b_3027_){
_start:
{
size_t v_i_boxed_3028_; size_t v_stop_boxed_3029_; lean_object* v_res_3030_; 
v_i_boxed_3028_ = lean_unbox_usize(v_i_3025_);
lean_dec(v_i_3025_);
v_stop_boxed_3029_ = lean_unbox_usize(v_stop_3026_);
lean_dec(v_stop_3026_);
v_res_3030_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__11(v_fvarIds_3023_, v_as_3024_, v_i_boxed_3028_, v_stop_boxed_3029_, v_b_3027_);
lean_dec_ref(v_as_3024_);
lean_dec_ref(v_fvarIds_3023_);
return v_res_3030_;
}
}
lean_object* l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___redArg(lean_object* v_fvarIds_3033_, lean_object* v_k_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_){
_start:
{
lean_object* v_lctx_3040_; lean_object* v_localInstances_3041_; lean_object* v___x_3042_; lean_object* v___y_3044_; lean_object* v___x_3053_; uint8_t v___x_3054_; 
v_lctx_3040_ = lean_ctor_get(v___y_3035_, 2);
v_localInstances_3041_ = lean_ctor_get(v___y_3035_, 3);
v___x_3042_ = lean_unsigned_to_nat(0u);
v___x_3053_ = lean_array_get_size(v_fvarIds_3033_);
v___x_3054_ = lean_nat_dec_lt(v___x_3042_, v___x_3053_);
if (v___x_3054_ == 0)
{
lean_inc_ref(v_lctx_3040_);
v___y_3044_ = v_lctx_3040_;
goto v___jp_3043_;
}
else
{
size_t v___x_3055_; size_t v___x_3056_; lean_object* v___x_3057_; 
v___x_3055_ = ((size_t)0ULL);
v___x_3056_ = lean_usize_of_nat(v___x_3053_);
lean_inc_ref(v_lctx_3040_);
v___x_3057_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__12(v_fvarIds_3033_, v___x_3055_, v___x_3056_, v_lctx_3040_);
v___y_3044_ = v___x_3057_;
goto v___jp_3043_;
}
v___jp_3043_:
{
lean_object* v___x_3045_; lean_object* v___x_3046_; uint8_t v___x_3047_; 
v___x_3045_ = lean_array_get_size(v_localInstances_3041_);
v___x_3046_ = ((lean_object*)(l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___redArg___closed__0));
v___x_3047_ = lean_nat_dec_lt(v___x_3042_, v___x_3045_);
if (v___x_3047_ == 0)
{
lean_object* v___x_3048_; 
v___x_3048_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___redArg(v___y_3044_, v___x_3046_, v_k_3034_, v___y_3035_, v___y_3036_, v___y_3037_, v___y_3038_);
return v___x_3048_;
}
else
{
size_t v___x_3049_; size_t v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; 
v___x_3049_ = ((size_t)0ULL);
v___x_3050_ = lean_usize_of_nat(v___x_3045_);
v___x_3051_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__11(v_fvarIds_3033_, v_localInstances_3041_, v___x_3049_, v___x_3050_, v___x_3046_);
v___x_3052_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___redArg(v___y_3044_, v___x_3051_, v_k_3034_, v___y_3035_, v___y_3036_, v___y_3037_, v___y_3038_);
return v___x_3052_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarIds_3033_ = stack[0].m_obj;
lean_object* v_k_3034_ = stack[1].m_obj;
lean_object* v___y_3035_ = stack[2].m_obj;
lean_object* v___y_3036_ = stack[3].m_obj;
lean_object* v___y_3037_ = stack[4].m_obj;
lean_object* v___y_3038_ = stack[5].m_obj;
lean_object* v_res_3058_;
v_res_3058_ = l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___redArg(v_fvarIds_3033_, v_k_3034_, v___y_3035_, v___y_3036_, v___y_3037_, v___y_3038_);
stack->m_obj
 = v_res_3058_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___redArg___boxed(lean_object* v_fvarIds_3059_, lean_object* v_k_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_){
_start:
{
lean_object* v_res_3066_; 
v_res_3066_ = l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___redArg(v_fvarIds_3059_, v_k_3060_, v___y_3061_, v___y_3062_, v___y_3063_, v___y_3064_);
lean_dec(v___y_3064_);
lean_dec_ref(v___y_3063_);
lean_dec(v___y_3062_);
lean_dec_ref(v___y_3061_);
lean_dec_ref(v_fvarIds_3059_);
return v_res_3066_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__14_spec__17_spec__21(lean_object* v_x_3067_, lean_object* v_x_3068_, lean_object* v_x_3069_){
_start:
{
if (lean_obj_tag(v_x_3069_) == 0)
{
lean_dec(v_x_3067_);
return v_x_3068_;
}
else
{
lean_object* v_head_3070_; lean_object* v_tail_3071_; lean_object* v___x_3073_; uint8_t v_isShared_3074_; uint8_t v_isSharedCheck_3081_; 
v_head_3070_ = lean_ctor_get(v_x_3069_, 0);
v_tail_3071_ = lean_ctor_get(v_x_3069_, 1);
v_isSharedCheck_3081_ = !lean_is_exclusive(v_x_3069_);
if (v_isSharedCheck_3081_ == 0)
{
v___x_3073_ = v_x_3069_;
v_isShared_3074_ = v_isSharedCheck_3081_;
goto v_resetjp_3072_;
}
else
{
lean_inc(v_tail_3071_);
lean_inc(v_head_3070_);
lean_dec(v_x_3069_);
v___x_3073_ = lean_box(0);
v_isShared_3074_ = v_isSharedCheck_3081_;
goto v_resetjp_3072_;
}
v_resetjp_3072_:
{
lean_object* v___x_3076_; 
lean_inc(v_x_3067_);
if (v_isShared_3074_ == 0)
{
lean_ctor_set_tag(v___x_3073_, 5);
lean_ctor_set(v___x_3073_, 1, v_x_3067_);
lean_ctor_set(v___x_3073_, 0, v_x_3068_);
v___x_3076_ = v___x_3073_;
goto v_reusejp_3075_;
}
else
{
lean_object* v_reuseFailAlloc_3080_; 
v_reuseFailAlloc_3080_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3080_, 0, v_x_3068_);
lean_ctor_set(v_reuseFailAlloc_3080_, 1, v_x_3067_);
v___x_3076_ = v_reuseFailAlloc_3080_;
goto v_reusejp_3075_;
}
v_reusejp_3075_:
{
lean_object* v___x_3077_; lean_object* v___x_3078_; 
v___x_3077_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(v_head_3070_);
v___x_3078_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3078_, 0, v___x_3076_);
lean_ctor_set(v___x_3078_, 1, v___x_3077_);
v_x_3068_ = v___x_3078_;
v_x_3069_ = v_tail_3071_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__14_spec__17(lean_object* v_x_3082_, lean_object* v_x_3083_, lean_object* v_x_3084_){
_start:
{
if (lean_obj_tag(v_x_3084_) == 0)
{
lean_dec(v_x_3082_);
return v_x_3083_;
}
else
{
lean_object* v_head_3085_; lean_object* v_tail_3086_; lean_object* v___x_3088_; uint8_t v_isShared_3089_; uint8_t v_isSharedCheck_3096_; 
v_head_3085_ = lean_ctor_get(v_x_3084_, 0);
v_tail_3086_ = lean_ctor_get(v_x_3084_, 1);
v_isSharedCheck_3096_ = !lean_is_exclusive(v_x_3084_);
if (v_isSharedCheck_3096_ == 0)
{
v___x_3088_ = v_x_3084_;
v_isShared_3089_ = v_isSharedCheck_3096_;
goto v_resetjp_3087_;
}
else
{
lean_inc(v_tail_3086_);
lean_inc(v_head_3085_);
lean_dec(v_x_3084_);
v___x_3088_ = lean_box(0);
v_isShared_3089_ = v_isSharedCheck_3096_;
goto v_resetjp_3087_;
}
v_resetjp_3087_:
{
lean_object* v___x_3091_; 
lean_inc(v_x_3082_);
if (v_isShared_3089_ == 0)
{
lean_ctor_set_tag(v___x_3088_, 5);
lean_ctor_set(v___x_3088_, 1, v_x_3082_);
lean_ctor_set(v___x_3088_, 0, v_x_3083_);
v___x_3091_ = v___x_3088_;
goto v_reusejp_3090_;
}
else
{
lean_object* v_reuseFailAlloc_3095_; 
v_reuseFailAlloc_3095_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3095_, 0, v_x_3083_);
lean_ctor_set(v_reuseFailAlloc_3095_, 1, v_x_3082_);
v___x_3091_ = v_reuseFailAlloc_3095_;
goto v_reusejp_3090_;
}
v_reusejp_3090_:
{
lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; 
v___x_3092_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(v_head_3085_);
v___x_3093_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3093_, 0, v___x_3091_);
lean_ctor_set(v___x_3093_, 1, v___x_3092_);
v___x_3094_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__14_spec__17_spec__21(v_x_3082_, v___x_3093_, v_tail_3086_);
return v___x_3094_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__14(lean_object* v_x_3097_, lean_object* v_x_3098_){
_start:
{
if (lean_obj_tag(v_x_3097_) == 0)
{
lean_object* v___x_3099_; 
lean_dec(v_x_3098_);
v___x_3099_ = lean_box(0);
return v___x_3099_;
}
else
{
lean_object* v_tail_3100_; 
v_tail_3100_ = lean_ctor_get(v_x_3097_, 1);
if (lean_obj_tag(v_tail_3100_) == 0)
{
lean_object* v_head_3101_; lean_object* v___x_3102_; 
lean_dec(v_x_3098_);
v_head_3101_ = lean_ctor_get(v_x_3097_, 0);
lean_inc(v_head_3101_);
lean_dec_ref_known(v_x_3097_, 2);
v___x_3102_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(v_head_3101_);
return v___x_3102_;
}
else
{
lean_object* v_head_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; 
lean_inc(v_tail_3100_);
v_head_3103_ = lean_ctor_get(v_x_3097_, 0);
lean_inc(v_head_3103_);
lean_dec_ref_known(v_x_3097_, 2);
v___x_3104_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(v_head_3103_);
v___x_3105_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__14_spec__17(v_x_3098_, v___x_3104_, v_tail_3100_);
return v___x_3105_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__5(void){
_start:
{
lean_object* v___x_3114_; lean_object* v___x_3115_; 
v___x_3114_ = ((lean_object*)(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__0));
v___x_3115_ = lean_string_length(v___x_3114_);
return v___x_3115_;
}
}
static lean_object* _init_l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__6(void){
_start:
{
lean_object* v___x_3116_; lean_object* v___x_3117_; 
v___x_3116_ = lean_obj_once(&l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__5, &l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__5_once, _init_l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__5);
v___x_3117_ = lean_nat_to_int(v___x_3116_);
return v___x_3117_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10(lean_object* v_xs_3125_){
_start:
{
lean_object* v___x_3126_; lean_object* v___x_3127_; uint8_t v___x_3128_; 
v___x_3126_ = lean_array_get_size(v_xs_3125_);
v___x_3127_ = lean_unsigned_to_nat(0u);
v___x_3128_ = lean_nat_dec_eq(v___x_3126_, v___x_3127_);
if (v___x_3128_ == 0)
{
lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; 
v___x_3129_ = lean_array_to_list(v_xs_3125_);
v___x_3130_ = ((lean_object*)(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__3));
v___x_3131_ = l_Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__14(v___x_3129_, v___x_3130_);
v___x_3132_ = lean_obj_once(&l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__6, &l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__6_once, _init_l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__6);
v___x_3133_ = ((lean_object*)(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__7));
v___x_3134_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3134_, 0, v___x_3133_);
lean_ctor_set(v___x_3134_, 1, v___x_3131_);
v___x_3135_ = ((lean_object*)(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__8));
v___x_3136_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3136_, 0, v___x_3134_);
lean_ctor_set(v___x_3136_, 1, v___x_3135_);
v___x_3137_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3137_, 0, v___x_3132_);
lean_ctor_set(v___x_3137_, 1, v___x_3136_);
v___x_3138_ = l_Std_Format_fill(v___x_3137_);
return v___x_3138_;
}
else
{
lean_object* v___x_3139_; 
lean_dec_ref(v_xs_3125_);
v___x_3139_ = ((lean_object*)(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__10));
return v___x_3139_;
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__11(size_t v_sz_3140_, size_t v_i_3141_, lean_object* v_bs_3142_){
_start:
{
uint8_t v___x_3143_; 
v___x_3143_ = lean_usize_dec_lt(v_i_3141_, v_sz_3140_);
if (v___x_3143_ == 0)
{
return v_bs_3142_;
}
else
{
lean_object* v_v_3144_; lean_object* v___x_3145_; lean_object* v_bs_x27_3146_; lean_object* v___x_3147_; size_t v___x_3148_; size_t v___x_3149_; lean_object* v___x_3150_; 
v_v_3144_ = lean_array_uget(v_bs_3142_, v_i_3141_);
v___x_3145_ = lean_unsigned_to_nat(0u);
v_bs_x27_3146_ = lean_array_uset(v_bs_3142_, v_i_3141_, v___x_3145_);
v___x_3147_ = l_Lean_mkFVar(v_v_3144_);
v___x_3148_ = ((size_t)1ULL);
v___x_3149_ = lean_usize_add(v_i_3141_, v___x_3148_);
v___x_3150_ = lean_array_uset(v_bs_x27_3146_, v_i_3141_, v___x_3147_);
v_i_3141_ = v___x_3149_;
v_bs_3142_ = v___x_3150_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__11_0interp(lean_interpreter_value* stack)
{
size_t v_sz_3140_ = stack[0].m_num;
size_t v_i_3141_ = stack[1].m_num;
lean_object* v_bs_3142_ = stack[2].m_obj;
lean_object* v_res_3152_;
v_res_3152_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__11(v_sz_3140_, v_i_3141_, v_bs_3142_);
stack->m_obj
 = v_res_3152_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__11___boxed(lean_object* v_sz_3153_, lean_object* v_i_3154_, lean_object* v_bs_3155_){
_start:
{
size_t v_sz_boxed_3156_; size_t v_i_boxed_3157_; lean_object* v_res_3158_; 
v_sz_boxed_3156_ = lean_unbox_usize(v_sz_3153_);
lean_dec(v_sz_3153_);
v_i_boxed_3157_ = lean_unbox_usize(v_i_3154_);
lean_dec(v_i_3154_);
v_res_3158_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__11(v_sz_boxed_3156_, v_i_boxed_3157_, v_bs_3155_);
return v_res_3158_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__2(size_t v_sz_3159_, size_t v_i_3160_, lean_object* v_bs_3161_){
_start:
{
uint8_t v___x_3162_; 
v___x_3162_ = lean_usize_dec_lt(v_i_3160_, v_sz_3159_);
if (v___x_3162_ == 0)
{
return v_bs_3161_;
}
else
{
lean_object* v_v_3163_; lean_object* v_recArgPos_3164_; lean_object* v___x_3165_; lean_object* v_bs_x27_3166_; size_t v___x_3167_; size_t v___x_3168_; lean_object* v___x_3169_; 
v_v_3163_ = lean_array_uget_borrowed(v_bs_3161_, v_i_3160_);
v_recArgPos_3164_ = lean_ctor_get(v_v_3163_, 2);
lean_inc(v_recArgPos_3164_);
v___x_3165_ = lean_unsigned_to_nat(0u);
v_bs_x27_3166_ = lean_array_uset(v_bs_3161_, v_i_3160_, v___x_3165_);
v___x_3167_ = ((size_t)1ULL);
v___x_3168_ = lean_usize_add(v_i_3160_, v___x_3167_);
v___x_3169_ = lean_array_uset(v_bs_x27_3166_, v_i_3160_, v_recArgPos_3164_);
v_i_3160_ = v___x_3168_;
v_bs_3161_ = v___x_3169_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__2_0interp(lean_interpreter_value* stack)
{
size_t v_sz_3159_ = stack[0].m_num;
size_t v_i_3160_ = stack[1].m_num;
lean_object* v_bs_3161_ = stack[2].m_obj;
lean_object* v_res_3171_;
v_res_3171_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__2(v_sz_3159_, v_i_3160_, v_bs_3161_);
stack->m_obj
 = v_res_3171_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__2___boxed(lean_object* v_sz_3172_, lean_object* v_i_3173_, lean_object* v_bs_3174_){
_start:
{
size_t v_sz_boxed_3175_; size_t v_i_boxed_3176_; lean_object* v_res_3177_; 
v_sz_boxed_3175_ = lean_unbox_usize(v_sz_3172_);
lean_dec(v_sz_3172_);
v_i_boxed_3176_ = lean_unbox_usize(v_i_3173_);
lean_dec(v_i_3173_);
v_res_3177_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__2(v_sz_boxed_3175_, v_i_boxed_3176_, v_bs_3174_);
return v_res_3177_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg(lean_object* v_fst_3178_, size_t v_sz_3179_, size_t v_i_3180_, lean_object* v_bs_3181_){
_start:
{
uint8_t v___x_3182_; 
v___x_3182_ = lean_usize_dec_lt(v_i_3180_, v_sz_3179_);
if (v___x_3182_ == 0)
{
return v_bs_3181_;
}
else
{
lean_object* v_v_3183_; lean_object* v_fnName_3184_; lean_object* v_recArgPos_3185_; lean_object* v_indicesPos_3186_; lean_object* v_indGroupInst_3187_; lean_object* v_indIdx_3188_; lean_object* v___x_3190_; uint8_t v_isShared_3191_; uint8_t v_isSharedCheck_3205_; 
v_v_3183_ = lean_array_uget(v_bs_3181_, v_i_3180_);
v_fnName_3184_ = lean_ctor_get(v_v_3183_, 0);
v_recArgPos_3185_ = lean_ctor_get(v_v_3183_, 2);
v_indicesPos_3186_ = lean_ctor_get(v_v_3183_, 3);
v_indGroupInst_3187_ = lean_ctor_get(v_v_3183_, 4);
v_indIdx_3188_ = lean_ctor_get(v_v_3183_, 5);
v_isSharedCheck_3205_ = !lean_is_exclusive(v_v_3183_);
if (v_isSharedCheck_3205_ == 0)
{
lean_object* v_unused_3206_; 
v_unused_3206_ = lean_ctor_get(v_v_3183_, 1);
lean_dec(v_unused_3206_);
v___x_3190_ = v_v_3183_;
v_isShared_3191_ = v_isSharedCheck_3205_;
goto v_resetjp_3189_;
}
else
{
lean_inc(v_indIdx_3188_);
lean_inc(v_indGroupInst_3187_);
lean_inc(v_indicesPos_3186_);
lean_inc(v_recArgPos_3185_);
lean_inc(v_fnName_3184_);
lean_dec(v_v_3183_);
v___x_3190_ = lean_box(0);
v_isShared_3191_ = v_isSharedCheck_3205_;
goto v_resetjp_3189_;
}
v_resetjp_3189_:
{
lean_object* v_perms_3192_; lean_object* v___x_3193_; lean_object* v_bs_x27_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3199_; 
v_perms_3192_ = lean_ctor_get(v_fst_3178_, 1);
v___x_3193_ = lean_unsigned_to_nat(0u);
v_bs_x27_3194_ = lean_array_uset(v_bs_3181_, v_i_3180_, v___x_3193_);
v___x_3195_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0);
v___x_3196_ = lean_usize_to_nat(v_i_3180_);
v___x_3197_ = lean_array_get_borrowed(v___x_3195_, v_perms_3192_, v___x_3196_);
lean_dec(v___x_3196_);
lean_inc(v___x_3197_);
if (v_isShared_3191_ == 0)
{
lean_ctor_set(v___x_3190_, 1, v___x_3197_);
v___x_3199_ = v___x_3190_;
goto v_reusejp_3198_;
}
else
{
lean_object* v_reuseFailAlloc_3204_; 
v_reuseFailAlloc_3204_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3204_, 0, v_fnName_3184_);
lean_ctor_set(v_reuseFailAlloc_3204_, 1, v___x_3197_);
lean_ctor_set(v_reuseFailAlloc_3204_, 2, v_recArgPos_3185_);
lean_ctor_set(v_reuseFailAlloc_3204_, 3, v_indicesPos_3186_);
lean_ctor_set(v_reuseFailAlloc_3204_, 4, v_indGroupInst_3187_);
lean_ctor_set(v_reuseFailAlloc_3204_, 5, v_indIdx_3188_);
v___x_3199_ = v_reuseFailAlloc_3204_;
goto v_reusejp_3198_;
}
v_reusejp_3198_:
{
size_t v___x_3200_; size_t v___x_3201_; lean_object* v___x_3202_; 
v___x_3200_ = ((size_t)1ULL);
v___x_3201_ = lean_usize_add(v_i_3180_, v___x_3200_);
v___x_3202_ = lean_array_uset(v_bs_x27_3194_, v_i_3180_, v___x_3199_);
v_i_3180_ = v___x_3201_;
v_bs_3181_ = v___x_3202_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_fst_3178_ = stack[0].m_obj;
size_t v_sz_3179_ = stack[1].m_num;
size_t v_i_3180_ = stack[2].m_num;
lean_object* v_bs_3181_ = stack[3].m_obj;
lean_object* v_res_3207_;
v_res_3207_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg(v_fst_3178_, v_sz_3179_, v_i_3180_, v_bs_3181_);
stack->m_obj
 = v_res_3207_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg___boxed(lean_object* v_fst_3208_, lean_object* v_sz_3209_, lean_object* v_i_3210_, lean_object* v_bs_3211_){
_start:
{
size_t v_sz_boxed_3212_; size_t v_i_boxed_3213_; lean_object* v_res_3214_; 
v_sz_boxed_3212_ = lean_unbox_usize(v_sz_3209_);
lean_dec(v_sz_3209_);
v_i_boxed_3213_ = lean_unbox_usize(v_i_3210_);
lean_dec(v_i_3210_);
v_res_3214_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg(v_fst_3208_, v_sz_boxed_3212_, v_i_boxed_3213_, v_bs_3211_);
lean_dec_ref(v_fst_3208_);
return v_res_3214_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__1(void){
_start:
{
lean_object* v___x_3216_; lean_object* v___x_3217_; 
v___x_3216_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__0));
v___x_3217_ = l_Lean_stringToMessageData(v___x_3216_);
return v___x_3217_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__3(void){
_start:
{
lean_object* v___x_3219_; lean_object* v___x_3220_; 
v___x_3219_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__2));
v___x_3220_ = l_Lean_stringToMessageData(v___x_3219_);
return v___x_3220_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__5(void){
_start:
{
lean_object* v___x_3222_; lean_object* v___x_3223_; 
v___x_3222_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__4));
v___x_3223_ = l_Lean_stringToMessageData(v___x_3222_);
return v___x_3223_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6(lean_object* v_a_3224_, lean_object* v_as_3225_, size_t v_sz_3226_, size_t v_i_3227_, lean_object* v_b_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_){
_start:
{
lean_object* v_a_3235_; uint8_t v___x_3239_; 
v___x_3239_ = lean_usize_dec_lt(v_i_3227_, v_sz_3226_);
if (v___x_3239_ == 0)
{
lean_object* v___x_3240_; 
lean_dec_ref(v_a_3224_);
v___x_3240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3240_, 0, v_b_3228_);
return v___x_3240_;
}
else
{
lean_object* v___x_3241_; lean_object* v_a_3242_; lean_object* v___x_3243_; 
v___x_3241_ = lean_box(0);
v_a_3242_ = lean_array_uget_borrowed(v_as_3225_, v_i_3227_);
lean_inc(v_a_3242_);
lean_inc_ref(v_a_3224_);
v___x_3243_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg(v_a_3224_, v_a_3242_, v___y_3230_);
if (lean_obj_tag(v___x_3243_) == 0)
{
lean_object* v_a_3244_; uint8_t v___x_3245_; 
v_a_3244_ = lean_ctor_get(v___x_3243_, 0);
lean_inc(v_a_3244_);
lean_dec_ref_known(v___x_3243_, 1);
v___x_3245_ = lean_unbox(v_a_3244_);
lean_dec(v_a_3244_);
if (v___x_3245_ == 0)
{
v_a_3235_ = v___x_3241_;
goto v___jp_3234_;
}
else
{
uint8_t v___x_3246_; 
v___x_3246_ = l_Lean_Expr_isFVarOf(v_a_3224_, v_a_3242_);
if (v___x_3246_ == 0)
{
lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; 
v___x_3247_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__1);
lean_inc_ref(v_a_3224_);
v___x_3248_ = l_Lean_indentExpr(v_a_3224_);
v___x_3249_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3249_, 0, v___x_3247_);
lean_ctor_set(v___x_3249_, 1, v___x_3248_);
v___x_3250_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__3);
v___x_3251_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3251_, 0, v___x_3249_);
lean_ctor_set(v___x_3251_, 1, v___x_3250_);
lean_inc(v_a_3242_);
v___x_3252_ = l_Lean_mkFVar(v_a_3242_);
v___x_3253_ = l_Lean_indentExpr(v___x_3252_);
v___x_3254_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3254_, 0, v___x_3251_);
lean_ctor_set(v___x_3254_, 1, v___x_3253_);
v___x_3255_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__5);
v___x_3256_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3256_, 0, v___x_3254_);
lean_ctor_set(v___x_3256_, 1, v___x_3255_);
v___x_3257_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg(v___x_3256_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_);
if (lean_obj_tag(v___x_3257_) == 0)
{
lean_dec_ref_known(v___x_3257_, 1);
v_a_3235_ = v___x_3241_;
goto v___jp_3234_;
}
else
{
lean_dec_ref(v_a_3224_);
return v___x_3257_;
}
}
else
{
lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; 
v___x_3258_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__1);
lean_inc_ref(v_a_3224_);
v___x_3259_ = l_Lean_indentExpr(v_a_3224_);
v___x_3260_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3260_, 0, v___x_3258_);
lean_ctor_set(v___x_3260_, 1, v___x_3259_);
v___x_3261_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__5);
v___x_3262_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3262_, 0, v___x_3260_);
lean_ctor_set(v___x_3262_, 1, v___x_3261_);
v___x_3263_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg(v___x_3262_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_);
if (lean_obj_tag(v___x_3263_) == 0)
{
lean_dec_ref_known(v___x_3263_, 1);
v_a_3235_ = v___x_3241_;
goto v___jp_3234_;
}
else
{
lean_dec_ref(v_a_3224_);
return v___x_3263_;
}
}
}
}
else
{
lean_object* v_a_3264_; lean_object* v___x_3266_; uint8_t v_isShared_3267_; uint8_t v_isSharedCheck_3271_; 
lean_dec_ref(v_a_3224_);
v_a_3264_ = lean_ctor_get(v___x_3243_, 0);
v_isSharedCheck_3271_ = !lean_is_exclusive(v___x_3243_);
if (v_isSharedCheck_3271_ == 0)
{
v___x_3266_ = v___x_3243_;
v_isShared_3267_ = v_isSharedCheck_3271_;
goto v_resetjp_3265_;
}
else
{
lean_inc(v_a_3264_);
lean_dec(v___x_3243_);
v___x_3266_ = lean_box(0);
v_isShared_3267_ = v_isSharedCheck_3271_;
goto v_resetjp_3265_;
}
v_resetjp_3265_:
{
lean_object* v___x_3269_; 
if (v_isShared_3267_ == 0)
{
v___x_3269_ = v___x_3266_;
goto v_reusejp_3268_;
}
else
{
lean_object* v_reuseFailAlloc_3270_; 
v_reuseFailAlloc_3270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3270_, 0, v_a_3264_);
v___x_3269_ = v_reuseFailAlloc_3270_;
goto v_reusejp_3268_;
}
v_reusejp_3268_:
{
return v___x_3269_;
}
}
}
}
v___jp_3234_:
{
size_t v___x_3236_; size_t v___x_3237_; 
v___x_3236_ = ((size_t)1ULL);
v___x_3237_ = lean_usize_add(v_i_3227_, v___x_3236_);
v_i_3227_ = v___x_3237_;
v_b_3228_ = v_a_3235_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3224_ = stack[0].m_obj;
lean_object* v_as_3225_ = stack[1].m_obj;
size_t v_sz_3226_ = stack[2].m_num;
size_t v_i_3227_ = stack[3].m_num;
lean_object* v_b_3228_ = stack[4].m_obj;
lean_object* v___y_3229_ = stack[5].m_obj;
lean_object* v___y_3230_ = stack[6].m_obj;
lean_object* v___y_3231_ = stack[7].m_obj;
lean_object* v___y_3232_ = stack[8].m_obj;
lean_object* v_res_3272_;
v_res_3272_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6(v_a_3224_, v_as_3225_, v_sz_3226_, v_i_3227_, v_b_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_);
stack->m_obj
 = v_res_3272_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___boxed(lean_object* v_a_3273_, lean_object* v_as_3274_, lean_object* v_sz_3275_, lean_object* v_i_3276_, lean_object* v_b_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_){
_start:
{
size_t v_sz_boxed_3283_; size_t v_i_boxed_3284_; lean_object* v_res_3285_; 
v_sz_boxed_3283_ = lean_unbox_usize(v_sz_3275_);
lean_dec(v_sz_3275_);
v_i_boxed_3284_ = lean_unbox_usize(v_i_3276_);
lean_dec(v_i_3276_);
v_res_3285_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6(v_a_3273_, v_as_3274_, v_sz_boxed_3283_, v_i_boxed_3284_, v_b_3277_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_);
lean_dec(v___y_3281_);
lean_dec_ref(v___y_3280_);
lean_dec(v___y_3279_);
lean_dec_ref(v___y_3278_);
lean_dec_ref(v_as_3274_);
return v_res_3285_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7(lean_object* v_snd_3286_, lean_object* v_as_3287_, size_t v_sz_3288_, size_t v_i_3289_, lean_object* v_b_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_){
_start:
{
uint8_t v___x_3296_; 
v___x_3296_ = lean_usize_dec_lt(v_i_3289_, v_sz_3288_);
if (v___x_3296_ == 0)
{
lean_object* v___x_3297_; 
v___x_3297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3297_, 0, v_b_3290_);
return v___x_3297_;
}
else
{
lean_object* v___x_3298_; lean_object* v_a_3299_; size_t v_sz_3300_; size_t v___x_3301_; lean_object* v___x_3302_; 
v___x_3298_ = lean_box(0);
v_a_3299_ = lean_array_uget_borrowed(v_as_3287_, v_i_3289_);
v_sz_3300_ = lean_array_size(v_snd_3286_);
v___x_3301_ = ((size_t)0ULL);
lean_inc(v_a_3299_);
v___x_3302_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6(v_a_3299_, v_snd_3286_, v_sz_3300_, v___x_3301_, v___x_3298_, v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_);
if (lean_obj_tag(v___x_3302_) == 0)
{
size_t v___x_3303_; size_t v___x_3304_; 
lean_dec_ref_known(v___x_3302_, 1);
v___x_3303_ = ((size_t)1ULL);
v___x_3304_ = lean_usize_add(v_i_3289_, v___x_3303_);
v_i_3289_ = v___x_3304_;
v_b_3290_ = v___x_3298_;
goto _start;
}
else
{
return v___x_3302_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_snd_3286_ = stack[0].m_obj;
lean_object* v_as_3287_ = stack[1].m_obj;
size_t v_sz_3288_ = stack[2].m_num;
size_t v_i_3289_ = stack[3].m_num;
lean_object* v_b_3290_ = stack[4].m_obj;
lean_object* v___y_3291_ = stack[5].m_obj;
lean_object* v___y_3292_ = stack[6].m_obj;
lean_object* v___y_3293_ = stack[7].m_obj;
lean_object* v___y_3294_ = stack[8].m_obj;
lean_object* v_res_3306_;
v_res_3306_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7(v_snd_3286_, v_as_3287_, v_sz_3288_, v_i_3289_, v_b_3290_, v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_);
stack->m_obj
 = v_res_3306_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7___boxed(lean_object* v_snd_3307_, lean_object* v_as_3308_, lean_object* v_sz_3309_, lean_object* v_i_3310_, lean_object* v_b_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_){
_start:
{
size_t v_sz_boxed_3317_; size_t v_i_boxed_3318_; lean_object* v_res_3319_; 
v_sz_boxed_3317_ = lean_unbox_usize(v_sz_3309_);
lean_dec(v_sz_3309_);
v_i_boxed_3318_ = lean_unbox_usize(v_i_3310_);
lean_dec(v_i_3310_);
v_res_3319_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7(v_snd_3307_, v_as_3308_, v_sz_boxed_3317_, v_i_boxed_3318_, v_b_3311_, v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_);
lean_dec(v___y_3315_);
lean_dec_ref(v___y_3314_);
lean_dec(v___y_3313_);
lean_dec_ref(v___y_3312_);
lean_dec_ref(v_as_3308_);
lean_dec_ref(v_snd_3307_);
return v_res_3319_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8(lean_object* v_snd_3320_, lean_object* v_as_3321_, size_t v_sz_3322_, size_t v_i_3323_, lean_object* v_b_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_){
_start:
{
uint8_t v___x_3330_; 
v___x_3330_ = lean_usize_dec_lt(v_i_3323_, v_sz_3322_);
if (v___x_3330_ == 0)
{
lean_object* v___x_3331_; 
v___x_3331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3331_, 0, v_b_3324_);
return v___x_3331_;
}
else
{
lean_object* v_a_3332_; lean_object* v_indGroupInst_3333_; lean_object* v_params_3334_; lean_object* v___x_3335_; size_t v_sz_3336_; size_t v___x_3337_; lean_object* v___x_3338_; 
v_a_3332_ = lean_array_uget_borrowed(v_as_3321_, v_i_3323_);
v_indGroupInst_3333_ = lean_ctor_get(v_a_3332_, 4);
v_params_3334_ = lean_ctor_get(v_indGroupInst_3333_, 2);
v___x_3335_ = lean_box(0);
v_sz_3336_ = lean_array_size(v_params_3334_);
v___x_3337_ = ((size_t)0ULL);
v___x_3338_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7(v_snd_3320_, v_params_3334_, v_sz_3336_, v___x_3337_, v___x_3335_, v___y_3325_, v___y_3326_, v___y_3327_, v___y_3328_);
if (lean_obj_tag(v___x_3338_) == 0)
{
size_t v___x_3339_; size_t v___x_3340_; 
lean_dec_ref_known(v___x_3338_, 1);
v___x_3339_ = ((size_t)1ULL);
v___x_3340_ = lean_usize_add(v_i_3323_, v___x_3339_);
v_i_3323_ = v___x_3340_;
v_b_3324_ = v___x_3335_;
goto _start;
}
else
{
return v___x_3338_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_snd_3320_ = stack[0].m_obj;
lean_object* v_as_3321_ = stack[1].m_obj;
size_t v_sz_3322_ = stack[2].m_num;
size_t v_i_3323_ = stack[3].m_num;
lean_object* v_b_3324_ = stack[4].m_obj;
lean_object* v___y_3325_ = stack[5].m_obj;
lean_object* v___y_3326_ = stack[6].m_obj;
lean_object* v___y_3327_ = stack[7].m_obj;
lean_object* v___y_3328_ = stack[8].m_obj;
lean_object* v_res_3342_;
v_res_3342_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8(v_snd_3320_, v_as_3321_, v_sz_3322_, v_i_3323_, v_b_3324_, v___y_3325_, v___y_3326_, v___y_3327_, v___y_3328_);
stack->m_obj
 = v_res_3342_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8___boxed(lean_object* v_snd_3343_, lean_object* v_as_3344_, lean_object* v_sz_3345_, lean_object* v_i_3346_, lean_object* v_b_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_){
_start:
{
size_t v_sz_boxed_3353_; size_t v_i_boxed_3354_; lean_object* v_res_3355_; 
v_sz_boxed_3353_ = lean_unbox_usize(v_sz_3345_);
lean_dec(v_sz_3345_);
v_i_boxed_3354_ = lean_unbox_usize(v_i_3346_);
lean_dec(v_i_3346_);
v_res_3355_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8(v_snd_3343_, v_as_3344_, v_sz_boxed_3353_, v_i_boxed_3354_, v_b_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_);
lean_dec(v___y_3351_);
lean_dec_ref(v___y_3350_);
lean_dec(v___y_3349_);
lean_dec_ref(v___y_3348_);
lean_dec_ref(v_as_3344_);
lean_dec_ref(v_snd_3343_);
return v_res_3355_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__0(void){
_start:
{
lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; 
v___x_3356_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__5));
v___x_3357_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___closed__1));
v___x_3358_ = l_Lean_Name_append(v___x_3357_, v___x_3356_);
return v___x_3358_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3360_; lean_object* v___x_3361_; 
v___x_3360_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__1));
v___x_3361_ = l_Lean_stringToMessageData(v___x_3360_);
return v___x_3361_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__4(void){
_start:
{
lean_object* v___x_3363_; lean_object* v___x_3364_; 
v___x_3363_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__3));
v___x_3364_ = l_Lean_stringToMessageData(v___x_3363_);
return v___x_3364_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__6(void){
_start:
{
lean_object* v___x_3366_; lean_object* v___x_3367_; 
v___x_3366_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__5));
v___x_3367_ = l_Lean_stringToMessageData(v___x_3366_);
return v___x_3367_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__8(void){
_start:
{
lean_object* v___x_3369_; lean_object* v___x_3370_; 
v___x_3369_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__7));
v___x_3370_ = l_Lean_stringToMessageData(v___x_3369_);
return v___x_3370_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__10(void){
_start:
{
lean_object* v___x_3372_; lean_object* v___x_3373_; 
v___x_3372_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__9));
v___x_3373_ = l_Lean_stringToMessageData(v___x_3372_);
return v___x_3373_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0(size_t v___x_3374_, lean_object* v_a_3375_, lean_object* v_xs_3376_, lean_object* v_a_3377_, lean_object* v_recArgInfos_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_){
_start:
{
lean_object* v___y_3385_; lean_object* v___y_3386_; lean_object* v___y_3387_; lean_object* v___y_3388_; lean_object* v___y_3389_; lean_object* v___y_3390_; lean_object* v___y_3391_; size_t v_sz_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___y_3408_; lean_object* v___y_3409_; lean_object* v___y_3410_; lean_object* v___y_3411_; lean_object* v___y_3412_; lean_object* v___y_3413_; lean_object* v___y_3414_; lean_object* v___x_3491_; lean_object* v_a_3492_; uint8_t v___x_3493_; 
v_sz_3404_ = lean_array_size(v_recArgInfos_3378_);
lean_inc_ref(v_recArgInfos_3378_);
v___x_3405_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__2(v_sz_3404_, v___x_3374_, v_recArgInfos_3378_);
v___x_3406_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__5));
v___x_3491_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1(v___x_3406_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_);
v_a_3492_ = lean_ctor_get(v___x_3491_, 0);
lean_inc(v_a_3492_);
lean_dec_ref(v___x_3491_);
v___x_3493_ = lean_unbox(v_a_3492_);
lean_dec(v_a_3492_);
if (v___x_3493_ == 0)
{
goto v___jp_3434_;
}
else
{
lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; 
v___x_3494_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__10, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__10);
lean_inc_ref(v___x_3405_);
v___x_3495_ = lean_array_to_list(v___x_3405_);
v___x_3496_ = lean_box(0);
v___x_3497_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__0(v___x_3495_, v___x_3496_);
v___x_3498_ = l_Lean_MessageData_ofList(v___x_3497_);
v___x_3499_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3499_, 0, v___x_3494_);
lean_ctor_set(v___x_3499_, 1, v___x_3498_);
v___x_3500_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_3406_, v___x_3499_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_);
if (lean_obj_tag(v___x_3500_) == 0)
{
lean_dec_ref_known(v___x_3500_, 1);
goto v___jp_3434_;
}
else
{
lean_object* v_a_3501_; lean_object* v___x_3503_; uint8_t v_isShared_3504_; uint8_t v_isSharedCheck_3508_; 
lean_dec_ref(v___x_3405_);
lean_dec_ref(v_recArgInfos_3378_);
lean_dec_ref(v_a_3377_);
lean_dec_ref(v_xs_3376_);
lean_dec_ref(v_a_3375_);
v_a_3501_ = lean_ctor_get(v___x_3500_, 0);
v_isSharedCheck_3508_ = !lean_is_exclusive(v___x_3500_);
if (v_isSharedCheck_3508_ == 0)
{
v___x_3503_ = v___x_3500_;
v_isShared_3504_ = v_isSharedCheck_3508_;
goto v_resetjp_3502_;
}
else
{
lean_inc(v_a_3501_);
lean_dec(v___x_3500_);
v___x_3503_ = lean_box(0);
v_isShared_3504_ = v_isSharedCheck_3508_;
goto v_resetjp_3502_;
}
v_resetjp_3502_:
{
lean_object* v___x_3506_; 
if (v_isShared_3504_ == 0)
{
v___x_3506_ = v___x_3503_;
goto v_reusejp_3505_;
}
else
{
lean_object* v_reuseFailAlloc_3507_; 
v_reuseFailAlloc_3507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3507_, 0, v_a_3501_);
v___x_3506_ = v_reuseFailAlloc_3507_;
goto v_reusejp_3505_;
}
v_reusejp_3505_:
{
return v___x_3506_;
}
}
}
}
v___jp_3384_:
{
lean_object* v___x_3392_; size_t v_sz_3393_; lean_object* v___x_3394_; 
v___x_3392_ = lean_box(0);
v_sz_3393_ = lean_array_size(v___y_3385_);
v___x_3394_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8(v___y_3387_, v___y_3385_, v_sz_3393_, v___x_3374_, v___x_3392_, v___y_3388_, v___y_3389_, v___y_3390_, v___y_3391_);
lean_dec_ref(v___y_3385_);
if (lean_obj_tag(v___x_3394_) == 0)
{
lean_object* v___x_3395_; 
lean_dec_ref_known(v___x_3394_, 1);
v___x_3395_ = l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___redArg(v___y_3387_, v___y_3386_, v___y_3388_, v___y_3389_, v___y_3390_, v___y_3391_);
lean_dec_ref(v___y_3387_);
return v___x_3395_;
}
else
{
lean_object* v_a_3396_; lean_object* v___x_3398_; uint8_t v_isShared_3399_; uint8_t v_isSharedCheck_3403_; 
lean_dec_ref(v___y_3387_);
lean_dec_ref(v___y_3386_);
v_a_3396_ = lean_ctor_get(v___x_3394_, 0);
v_isSharedCheck_3403_ = !lean_is_exclusive(v___x_3394_);
if (v_isSharedCheck_3403_ == 0)
{
v___x_3398_ = v___x_3394_;
v_isShared_3399_ = v_isSharedCheck_3403_;
goto v_resetjp_3397_;
}
else
{
lean_inc(v_a_3396_);
lean_dec(v___x_3394_);
v___x_3398_ = lean_box(0);
v_isShared_3399_ = v_isSharedCheck_3403_;
goto v_resetjp_3397_;
}
v_resetjp_3397_:
{
lean_object* v___x_3401_; 
if (v_isShared_3399_ == 0)
{
v___x_3401_ = v___x_3398_;
goto v_reusejp_3400_;
}
else
{
lean_object* v_reuseFailAlloc_3402_; 
v_reuseFailAlloc_3402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3402_, 0, v_a_3396_);
v___x_3401_ = v_reuseFailAlloc_3402_;
goto v_reusejp_3400_;
}
v_reusejp_3400_:
{
return v___x_3401_;
}
}
}
}
v___jp_3407_:
{
lean_object* v_toCold_3415_; lean_object* v_options_3416_; uint8_t v_hasTrace_3417_; 
v_toCold_3415_ = lean_ctor_get(v___y_3413_, 0);
v_options_3416_ = lean_ctor_get(v_toCold_3415_, 2);
v_hasTrace_3417_ = lean_ctor_get_uint8(v_options_3416_, sizeof(void*)*1);
if (v_hasTrace_3417_ == 0)
{
v___y_3385_ = v___y_3408_;
v___y_3386_ = v___y_3409_;
v___y_3387_ = v___y_3410_;
v___y_3388_ = v___y_3411_;
v___y_3389_ = v___y_3412_;
v___y_3390_ = v___y_3413_;
v___y_3391_ = v___y_3414_;
goto v___jp_3384_;
}
else
{
lean_object* v_inheritedTraceOptions_3418_; lean_object* v___x_3419_; uint8_t v___x_3420_; 
v_inheritedTraceOptions_3418_ = lean_ctor_get(v_toCold_3415_, 11);
v___x_3419_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__0);
v___x_3420_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3418_, v_options_3416_, v___x_3419_);
if (v___x_3420_ == 0)
{
v___y_3385_ = v___y_3408_;
v___y_3386_ = v___y_3409_;
v___y_3387_ = v___y_3410_;
v___y_3388_ = v___y_3411_;
v___y_3389_ = v___y_3412_;
v___y_3390_ = v___y_3413_;
v___y_3391_ = v___y_3414_;
goto v___jp_3384_;
}
else
{
lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; 
v___x_3421_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__2);
lean_inc_ref(v___y_3408_);
v___x_3422_ = l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10(v___y_3408_);
v___x_3423_ = l_Lean_MessageData_ofFormat(v___x_3422_);
v___x_3424_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3424_, 0, v___x_3421_);
lean_ctor_set(v___x_3424_, 1, v___x_3423_);
v___x_3425_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_3406_, v___x_3424_, v___y_3411_, v___y_3412_, v___y_3413_, v___y_3414_);
if (lean_obj_tag(v___x_3425_) == 0)
{
lean_dec_ref_known(v___x_3425_, 1);
v___y_3385_ = v___y_3408_;
v___y_3386_ = v___y_3409_;
v___y_3387_ = v___y_3410_;
v___y_3388_ = v___y_3411_;
v___y_3389_ = v___y_3412_;
v___y_3390_ = v___y_3413_;
v___y_3391_ = v___y_3414_;
goto v___jp_3384_;
}
else
{
lean_object* v_a_3426_; lean_object* v___x_3428_; uint8_t v_isShared_3429_; uint8_t v_isSharedCheck_3433_; 
lean_dec_ref(v___y_3410_);
lean_dec_ref(v___y_3409_);
lean_dec_ref(v___y_3408_);
v_a_3426_ = lean_ctor_get(v___x_3425_, 0);
v_isSharedCheck_3433_ = !lean_is_exclusive(v___x_3425_);
if (v_isSharedCheck_3433_ == 0)
{
v___x_3428_ = v___x_3425_;
v_isShared_3429_ = v_isSharedCheck_3433_;
goto v_resetjp_3427_;
}
else
{
lean_inc(v_a_3426_);
lean_dec(v___x_3425_);
v___x_3428_ = lean_box(0);
v_isShared_3429_ = v_isSharedCheck_3433_;
goto v_resetjp_3427_;
}
v_resetjp_3427_:
{
lean_object* v___x_3431_; 
if (v_isShared_3429_ == 0)
{
v___x_3431_ = v___x_3428_;
goto v_reusejp_3430_;
}
else
{
lean_object* v_reuseFailAlloc_3432_; 
v_reuseFailAlloc_3432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3432_, 0, v_a_3426_);
v___x_3431_ = v_reuseFailAlloc_3432_;
goto v_reusejp_3430_;
}
v_reusejp_3430_:
{
return v___x_3431_;
}
}
}
}
}
}
v___jp_3434_:
{
lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v_snd_3437_; lean_object* v_fst_3438_; lean_object* v___x_3440_; uint8_t v_isShared_3441_; uint8_t v_isSharedCheck_3490_; 
lean_inc_ref(v_recArgInfos_3378_);
v___x_3435_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__3(v_sz_3404_, v___x_3374_, v_recArgInfos_3378_);
lean_inc_ref(v_xs_3376_);
v___x_3436_ = l_Lean_Elab_FixedParamPerms_erase(v_a_3375_, v_xs_3376_, v___x_3435_);
v_snd_3437_ = lean_ctor_get(v___x_3436_, 1);
v_fst_3438_ = lean_ctor_get(v___x_3436_, 0);
v_isSharedCheck_3490_ = !lean_is_exclusive(v___x_3436_);
if (v_isSharedCheck_3490_ == 0)
{
v___x_3440_ = v___x_3436_;
v_isShared_3441_ = v_isSharedCheck_3490_;
goto v_resetjp_3439_;
}
else
{
lean_inc(v_snd_3437_);
lean_inc(v_fst_3438_);
lean_dec(v___x_3436_);
v___x_3440_ = lean_box(0);
v_isShared_3441_ = v_isSharedCheck_3490_;
goto v_resetjp_3439_;
}
v_resetjp_3439_:
{
lean_object* v_fst_3442_; lean_object* v_snd_3443_; lean_object* v___x_3445_; uint8_t v_isShared_3446_; uint8_t v_isSharedCheck_3489_; 
v_fst_3442_ = lean_ctor_get(v_snd_3437_, 0);
v_snd_3443_ = lean_ctor_get(v_snd_3437_, 1);
v_isSharedCheck_3489_ = !lean_is_exclusive(v_snd_3437_);
if (v_isSharedCheck_3489_ == 0)
{
v___x_3445_ = v_snd_3437_;
v_isShared_3446_ = v_isSharedCheck_3489_;
goto v_resetjp_3444_;
}
else
{
lean_inc(v_snd_3443_);
lean_inc(v_fst_3442_);
lean_dec(v_snd_3437_);
v___x_3445_ = lean_box(0);
v_isShared_3446_ = v_isSharedCheck_3489_;
goto v_resetjp_3444_;
}
v_resetjp_3444_:
{
lean_object* v___x_3447_; lean_object* v___f_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; uint8_t v___x_3451_; 
v___x_3447_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg(v_fst_3438_, v_sz_3404_, v___x_3374_, v_recArgInfos_3378_);
lean_inc_ref(v___x_3447_);
lean_inc(v_fst_3442_);
v___f_3448_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___boxed), 10, 5);
lean_closure_set(v___f_3448_, 0, v_a_3377_);
lean_closure_set(v___f_3448_, 1, v_fst_3438_);
lean_closure_set(v___f_3448_, 2, v_fst_3442_);
lean_closure_set(v___f_3448_, 3, v___x_3447_);
lean_closure_set(v___f_3448_, 4, v___x_3405_);
v___x_3449_ = lean_array_get_size(v_fst_3442_);
v___x_3450_ = lean_array_get_size(v_xs_3376_);
v___x_3451_ = lean_nat_dec_eq(v___x_3449_, v___x_3450_);
if (v___x_3451_ == 0)
{
lean_object* v___x_3452_; lean_object* v_a_3453_; uint8_t v___x_3454_; 
v___x_3452_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1(v___x_3406_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_);
v_a_3453_ = lean_ctor_get(v___x_3452_, 0);
lean_inc(v_a_3453_);
lean_dec_ref(v___x_3452_);
v___x_3454_ = lean_unbox(v_a_3453_);
lean_dec(v_a_3453_);
if (v___x_3454_ == 0)
{
lean_del_object(v___x_3445_);
lean_dec(v_fst_3442_);
lean_del_object(v___x_3440_);
lean_dec_ref(v_xs_3376_);
v___y_3408_ = v___x_3447_;
v___y_3409_ = v___f_3448_;
v___y_3410_ = v_snd_3443_;
v___y_3411_ = v___y_3379_;
v___y_3412_ = v___y_3380_;
v___y_3413_ = v___y_3381_;
v___y_3414_ = v___y_3382_;
goto v___jp_3407_;
}
else
{
lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3461_; 
v___x_3455_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__4);
v___x_3456_ = lean_array_to_list(v_xs_3376_);
v___x_3457_ = lean_box(0);
v___x_3458_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_3456_, v___x_3457_);
v___x_3459_ = l_Lean_MessageData_ofList(v___x_3458_);
if (v_isShared_3446_ == 0)
{
lean_ctor_set_tag(v___x_3445_, 7);
lean_ctor_set(v___x_3445_, 1, v___x_3459_);
lean_ctor_set(v___x_3445_, 0, v___x_3455_);
v___x_3461_ = v___x_3445_;
goto v_reusejp_3460_;
}
else
{
lean_object* v_reuseFailAlloc_3487_; 
v_reuseFailAlloc_3487_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3487_, 0, v___x_3455_);
lean_ctor_set(v_reuseFailAlloc_3487_, 1, v___x_3459_);
v___x_3461_ = v_reuseFailAlloc_3487_;
goto v_reusejp_3460_;
}
v_reusejp_3460_:
{
lean_object* v___x_3462_; lean_object* v___x_3464_; 
v___x_3462_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__6, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__6);
if (v_isShared_3441_ == 0)
{
lean_ctor_set_tag(v___x_3440_, 7);
lean_ctor_set(v___x_3440_, 1, v___x_3462_);
lean_ctor_set(v___x_3440_, 0, v___x_3461_);
v___x_3464_ = v___x_3440_;
goto v_reusejp_3463_;
}
else
{
lean_object* v_reuseFailAlloc_3486_; 
v_reuseFailAlloc_3486_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3486_, 0, v___x_3461_);
lean_ctor_set(v_reuseFailAlloc_3486_, 1, v___x_3462_);
v___x_3464_ = v_reuseFailAlloc_3486_;
goto v_reusejp_3463_;
}
v_reusejp_3463_:
{
lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; size_t v_sz_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; 
v___x_3465_ = lean_array_to_list(v_fst_3442_);
v___x_3466_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_3465_, v___x_3457_);
v___x_3467_ = l_Lean_MessageData_ofList(v___x_3466_);
v___x_3468_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3468_, 0, v___x_3464_);
lean_ctor_set(v___x_3468_, 1, v___x_3467_);
v___x_3469_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__8);
v___x_3470_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3470_, 0, v___x_3468_);
lean_ctor_set(v___x_3470_, 1, v___x_3469_);
v_sz_3471_ = lean_array_size(v_snd_3443_);
lean_inc(v_snd_3443_);
v___x_3472_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__11(v_sz_3471_, v___x_3374_, v_snd_3443_);
v___x_3473_ = lean_array_to_list(v___x_3472_);
v___x_3474_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_3473_, v___x_3457_);
v___x_3475_ = l_Lean_MessageData_ofList(v___x_3474_);
v___x_3476_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3476_, 0, v___x_3470_);
lean_ctor_set(v___x_3476_, 1, v___x_3475_);
v___x_3477_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_3406_, v___x_3476_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_);
if (lean_obj_tag(v___x_3477_) == 0)
{
lean_dec_ref_known(v___x_3477_, 1);
v___y_3408_ = v___x_3447_;
v___y_3409_ = v___f_3448_;
v___y_3410_ = v_snd_3443_;
v___y_3411_ = v___y_3379_;
v___y_3412_ = v___y_3380_;
v___y_3413_ = v___y_3381_;
v___y_3414_ = v___y_3382_;
goto v___jp_3407_;
}
else
{
lean_object* v_a_3478_; lean_object* v___x_3480_; uint8_t v_isShared_3481_; uint8_t v_isSharedCheck_3485_; 
lean_dec_ref(v___f_3448_);
lean_dec_ref(v___x_3447_);
lean_dec(v_snd_3443_);
v_a_3478_ = lean_ctor_get(v___x_3477_, 0);
v_isSharedCheck_3485_ = !lean_is_exclusive(v___x_3477_);
if (v_isSharedCheck_3485_ == 0)
{
v___x_3480_ = v___x_3477_;
v_isShared_3481_ = v_isSharedCheck_3485_;
goto v_resetjp_3479_;
}
else
{
lean_inc(v_a_3478_);
lean_dec(v___x_3477_);
v___x_3480_ = lean_box(0);
v_isShared_3481_ = v_isSharedCheck_3485_;
goto v_resetjp_3479_;
}
v_resetjp_3479_:
{
lean_object* v___x_3483_; 
if (v_isShared_3481_ == 0)
{
v___x_3483_ = v___x_3480_;
goto v_reusejp_3482_;
}
else
{
lean_object* v_reuseFailAlloc_3484_; 
v_reuseFailAlloc_3484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3484_, 0, v_a_3478_);
v___x_3483_ = v_reuseFailAlloc_3484_;
goto v_reusejp_3482_;
}
v_reusejp_3482_:
{
return v___x_3483_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3488_; 
lean_dec_ref(v___x_3447_);
lean_del_object(v___x_3445_);
lean_dec(v_fst_3442_);
lean_del_object(v___x_3440_);
lean_dec_ref(v_xs_3376_);
v___x_3488_ = l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___redArg(v_snd_3443_, v___f_3448_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_);
lean_dec(v_snd_3443_);
return v___x_3488_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0_0interp(lean_interpreter_value* stack)
{
size_t v___x_3374_ = stack[0].m_num;
lean_object* v_a_3375_ = stack[1].m_obj;
lean_object* v_xs_3376_ = stack[2].m_obj;
lean_object* v_a_3377_ = stack[3].m_obj;
lean_object* v_recArgInfos_3378_ = stack[4].m_obj;
lean_object* v___y_3379_ = stack[5].m_obj;
lean_object* v___y_3380_ = stack[6].m_obj;
lean_object* v___y_3381_ = stack[7].m_obj;
lean_object* v___y_3382_ = stack[8].m_obj;
lean_object* v_res_3509_;
v_res_3509_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0(v___x_3374_, v_a_3375_, v_xs_3376_, v_a_3377_, v_recArgInfos_3378_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_);
stack->m_obj
 = v_res_3509_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___boxed(lean_object* v___x_3510_, lean_object* v_a_3511_, lean_object* v_xs_3512_, lean_object* v_a_3513_, lean_object* v_recArgInfos_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_){
_start:
{
size_t v___x_13534__boxed_3520_; lean_object* v_res_3521_; 
v___x_13534__boxed_3520_ = lean_unbox_usize(v___x_3510_);
lean_dec(v___x_3510_);
v_res_3521_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0(v___x_13534__boxed_3520_, v_a_3511_, v_xs_3512_, v_a_3513_, v_recArgInfos_3514_, v___y_3515_, v___y_3516_, v___y_3517_, v___y_3518_);
lean_dec(v___y_3518_);
lean_dec_ref(v___y_3517_);
lean_dec(v___y_3516_);
lean_dec_ref(v___y_3515_);
return v_res_3521_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg(lean_object* v___x_3522_, lean_object* v_xs_3523_, size_t v_sz_3524_, size_t v_i_3525_, lean_object* v_bs_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_){
_start:
{
uint8_t v___x_3532_; 
v___x_3532_ = lean_usize_dec_lt(v_i_3525_, v_sz_3524_);
if (v___x_3532_ == 0)
{
lean_object* v___x_3533_; 
lean_dec_ref(v_xs_3523_);
v___x_3533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3533_, 0, v_bs_3526_);
return v___x_3533_;
}
else
{
lean_object* v_v_3534_; lean_object* v_value_3535_; lean_object* v___x_3536_; lean_object* v_bs_x27_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; 
v_v_3534_ = lean_array_uget_borrowed(v_bs_3526_, v_i_3525_);
v_value_3535_ = lean_ctor_get(v_v_3534_, 7);
lean_inc_ref(v_value_3535_);
v___x_3536_ = lean_unsigned_to_nat(0u);
v_bs_x27_3537_ = lean_array_uset(v_bs_3526_, v_i_3525_, v___x_3536_);
v___x_3538_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0);
v___x_3539_ = lean_usize_to_nat(v_i_3525_);
v___x_3540_ = lean_array_get_borrowed(v___x_3538_, v___x_3522_, v___x_3539_);
lean_dec(v___x_3539_);
lean_inc_ref(v_xs_3523_);
lean_inc(v___x_3540_);
v___x_3541_ = l_Lean_Elab_FixedParamPerm_instantiateLambda(v___x_3540_, v_value_3535_, v_xs_3523_, v___y_3527_, v___y_3528_, v___y_3529_, v___y_3530_);
if (lean_obj_tag(v___x_3541_) == 0)
{
lean_object* v_a_3542_; size_t v___x_3543_; size_t v___x_3544_; lean_object* v___x_3545_; 
v_a_3542_ = lean_ctor_get(v___x_3541_, 0);
lean_inc(v_a_3542_);
lean_dec_ref_known(v___x_3541_, 1);
v___x_3543_ = ((size_t)1ULL);
v___x_3544_ = lean_usize_add(v_i_3525_, v___x_3543_);
v___x_3545_ = lean_array_uset(v_bs_x27_3537_, v_i_3525_, v_a_3542_);
v_i_3525_ = v___x_3544_;
v_bs_3526_ = v___x_3545_;
goto _start;
}
else
{
lean_object* v_a_3547_; lean_object* v___x_3549_; uint8_t v_isShared_3550_; uint8_t v_isSharedCheck_3554_; 
lean_dec_ref(v_bs_x27_3537_);
lean_dec_ref(v_xs_3523_);
v_a_3547_ = lean_ctor_get(v___x_3541_, 0);
v_isSharedCheck_3554_ = !lean_is_exclusive(v___x_3541_);
if (v_isSharedCheck_3554_ == 0)
{
v___x_3549_ = v___x_3541_;
v_isShared_3550_ = v_isSharedCheck_3554_;
goto v_resetjp_3548_;
}
else
{
lean_inc(v_a_3547_);
lean_dec(v___x_3541_);
v___x_3549_ = lean_box(0);
v_isShared_3550_ = v_isSharedCheck_3554_;
goto v_resetjp_3548_;
}
v_resetjp_3548_:
{
lean_object* v___x_3552_; 
if (v_isShared_3550_ == 0)
{
v___x_3552_ = v___x_3549_;
goto v_reusejp_3551_;
}
else
{
lean_object* v_reuseFailAlloc_3553_; 
v_reuseFailAlloc_3553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3553_, 0, v_a_3547_);
v___x_3552_ = v_reuseFailAlloc_3553_;
goto v_reusejp_3551_;
}
v_reusejp_3551_:
{
return v___x_3552_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3522_ = stack[0].m_obj;
lean_object* v_xs_3523_ = stack[1].m_obj;
size_t v_sz_3524_ = stack[2].m_num;
size_t v_i_3525_ = stack[3].m_num;
lean_object* v_bs_3526_ = stack[4].m_obj;
lean_object* v___y_3527_ = stack[5].m_obj;
lean_object* v___y_3528_ = stack[6].m_obj;
lean_object* v___y_3529_ = stack[7].m_obj;
lean_object* v___y_3530_ = stack[8].m_obj;
lean_object* v_res_3555_;
v_res_3555_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg(v___x_3522_, v_xs_3523_, v_sz_3524_, v_i_3525_, v_bs_3526_, v___y_3527_, v___y_3528_, v___y_3529_, v___y_3530_);
stack->m_obj
 = v_res_3555_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg___boxed(lean_object* v___x_3556_, lean_object* v_xs_3557_, lean_object* v_sz_3558_, lean_object* v_i_3559_, lean_object* v_bs_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_){
_start:
{
size_t v_sz_boxed_3566_; size_t v_i_boxed_3567_; lean_object* v_res_3568_; 
v_sz_boxed_3566_ = lean_unbox_usize(v_sz_3558_);
lean_dec(v_sz_3558_);
v_i_boxed_3567_ = lean_unbox_usize(v_i_3559_);
lean_dec(v_i_3559_);
v_res_3568_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg(v___x_3556_, v_xs_3557_, v_sz_boxed_3566_, v_i_boxed_3567_, v_bs_3560_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_);
lean_dec(v___y_3564_);
lean_dec_ref(v___y_3563_);
lean_dec(v___y_3562_);
lean_dec_ref(v___y_3561_);
lean_dec_ref(v___x_3556_);
return v_res_3568_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__2(size_t v___x_3569_, lean_object* v_a_3570_, lean_object* v_a_3571_, lean_object* v_perms_3572_, lean_object* v_fnNames_3573_, lean_object* v_termMeasure_x3fs_3574_, lean_object* v_xs_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_){
_start:
{
lean_object* v___x_3581_; lean_object* v___f_3582_; size_t v_sz_3583_; lean_object* v___x_3584_; 
v___x_3581_ = lean_box_usize(v___x_3569_);
lean_inc_ref_n(v_a_3571_, 2);
lean_inc_ref_n(v_xs_3575_, 2);
lean_inc_ref(v_a_3570_);
v___f_3582_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___boxed), 10, 4);
lean_closure_set(v___f_3582_, 0, v___x_3581_);
lean_closure_set(v___f_3582_, 1, v_a_3570_);
lean_closure_set(v___f_3582_, 2, v_xs_3575_);
lean_closure_set(v___f_3582_, 3, v_a_3571_);
v_sz_3583_ = lean_array_size(v_a_3571_);
v___x_3584_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg(v_perms_3572_, v_xs_3575_, v_sz_3583_, v___x_3569_, v_a_3571_, v___y_3576_, v___y_3577_, v___y_3578_, v___y_3579_);
if (lean_obj_tag(v___x_3584_) == 0)
{
lean_object* v_a_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; 
v_a_3585_ = lean_ctor_get(v___x_3584_, 0);
lean_inc_n(v_a_3585_, 2);
lean_dec_ref_known(v___x_3584_, 1);
lean_inc_ref(v_xs_3575_);
lean_inc_ref(v_fnNames_3573_);
v___x_3586_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_findRecArgCandidates___boxed), 10, 5);
lean_closure_set(v___x_3586_, 0, v_fnNames_3573_);
lean_closure_set(v___x_3586_, 1, v_a_3570_);
lean_closure_set(v___x_3586_, 2, v_xs_3575_);
lean_closure_set(v___x_3586_, 3, v_a_3585_);
lean_closure_set(v___x_3586_, 4, v_termMeasure_x3fs_3574_);
v___x_3587_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v_a_3571_, v___x_3586_, v___y_3576_, v___y_3577_, v___y_3578_, v___y_3579_);
if (lean_obj_tag(v___x_3587_) == 0)
{
lean_object* v_a_3588_; lean_object* v___x_3589_; 
v_a_3588_ = lean_ctor_get(v___x_3587_, 0);
lean_inc(v_a_3588_);
lean_dec_ref_known(v___x_3587_, 1);
v___x_3589_ = l_Lean_Elab_Structural_tryCandidates___redArg(v_fnNames_3573_, v_xs_3575_, v_a_3585_, v_a_3588_, v___f_3582_, v___y_3576_, v___y_3577_, v___y_3578_, v___y_3579_);
lean_dec_ref(v_fnNames_3573_);
return v___x_3589_;
}
else
{
lean_object* v_a_3590_; lean_object* v___x_3592_; uint8_t v_isShared_3593_; uint8_t v_isSharedCheck_3597_; 
lean_dec(v_a_3585_);
lean_dec_ref(v___f_3582_);
lean_dec_ref(v_xs_3575_);
lean_dec_ref(v_fnNames_3573_);
v_a_3590_ = lean_ctor_get(v___x_3587_, 0);
v_isSharedCheck_3597_ = !lean_is_exclusive(v___x_3587_);
if (v_isSharedCheck_3597_ == 0)
{
v___x_3592_ = v___x_3587_;
v_isShared_3593_ = v_isSharedCheck_3597_;
goto v_resetjp_3591_;
}
else
{
lean_inc(v_a_3590_);
lean_dec(v___x_3587_);
v___x_3592_ = lean_box(0);
v_isShared_3593_ = v_isSharedCheck_3597_;
goto v_resetjp_3591_;
}
v_resetjp_3591_:
{
lean_object* v___x_3595_; 
if (v_isShared_3593_ == 0)
{
v___x_3595_ = v___x_3592_;
goto v_reusejp_3594_;
}
else
{
lean_object* v_reuseFailAlloc_3596_; 
v_reuseFailAlloc_3596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3596_, 0, v_a_3590_);
v___x_3595_ = v_reuseFailAlloc_3596_;
goto v_reusejp_3594_;
}
v_reusejp_3594_:
{
return v___x_3595_;
}
}
}
}
else
{
lean_object* v_a_3598_; lean_object* v___x_3600_; uint8_t v_isShared_3601_; uint8_t v_isSharedCheck_3605_; 
lean_dec_ref(v___f_3582_);
lean_dec_ref(v_xs_3575_);
lean_dec_ref(v_termMeasure_x3fs_3574_);
lean_dec_ref(v_fnNames_3573_);
lean_dec_ref(v_a_3571_);
lean_dec_ref(v_a_3570_);
v_a_3598_ = lean_ctor_get(v___x_3584_, 0);
v_isSharedCheck_3605_ = !lean_is_exclusive(v___x_3584_);
if (v_isSharedCheck_3605_ == 0)
{
v___x_3600_ = v___x_3584_;
v_isShared_3601_ = v_isSharedCheck_3605_;
goto v_resetjp_3599_;
}
else
{
lean_inc(v_a_3598_);
lean_dec(v___x_3584_);
v___x_3600_ = lean_box(0);
v_isShared_3601_ = v_isSharedCheck_3605_;
goto v_resetjp_3599_;
}
v_resetjp_3599_:
{
lean_object* v___x_3603_; 
if (v_isShared_3601_ == 0)
{
v___x_3603_ = v___x_3600_;
goto v_reusejp_3602_;
}
else
{
lean_object* v_reuseFailAlloc_3604_; 
v_reuseFailAlloc_3604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3604_, 0, v_a_3598_);
v___x_3603_ = v_reuseFailAlloc_3604_;
goto v_reusejp_3602_;
}
v_reusejp_3602_:
{
return v___x_3603_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__2_0interp(lean_interpreter_value* stack)
{
size_t v___x_3569_ = stack[0].m_num;
lean_object* v_a_3570_ = stack[1].m_obj;
lean_object* v_a_3571_ = stack[2].m_obj;
lean_object* v_perms_3572_ = stack[3].m_obj;
lean_object* v_fnNames_3573_ = stack[4].m_obj;
lean_object* v_termMeasure_x3fs_3574_ = stack[5].m_obj;
lean_object* v_xs_3575_ = stack[6].m_obj;
lean_object* v___y_3576_ = stack[7].m_obj;
lean_object* v___y_3577_ = stack[8].m_obj;
lean_object* v___y_3578_ = stack[9].m_obj;
lean_object* v___y_3579_ = stack[10].m_obj;
lean_object* v_res_3606_;
v_res_3606_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__2(v___x_3569_, v_a_3570_, v_a_3571_, v_perms_3572_, v_fnNames_3573_, v_termMeasure_x3fs_3574_, v_xs_3575_, v___y_3576_, v___y_3577_, v___y_3578_, v___y_3579_);
stack->m_obj
 = v_res_3606_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__2___boxed(lean_object* v___x_3607_, lean_object* v_a_3608_, lean_object* v_a_3609_, lean_object* v_perms_3610_, lean_object* v_fnNames_3611_, lean_object* v_termMeasure_x3fs_3612_, lean_object* v_xs_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_){
_start:
{
size_t v___x_14061__boxed_3619_; lean_object* v_res_3620_; 
v___x_14061__boxed_3619_ = lean_unbox_usize(v___x_3607_);
lean_dec(v___x_3607_);
v_res_3620_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__2(v___x_14061__boxed_3619_, v_a_3608_, v_a_3609_, v_perms_3610_, v_fnNames_3611_, v_termMeasure_x3fs_3612_, v_xs_3613_, v___y_3614_, v___y_3615_, v___y_3616_, v___y_3617_);
lean_dec(v___y_3617_);
lean_dec_ref(v___y_3616_);
lean_dec(v___y_3615_);
lean_dec_ref(v___y_3614_);
lean_dec_ref(v_perms_3610_);
return v_res_3620_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0(size_t v_sz_3621_, size_t v_i_3622_, lean_object* v_bs_3623_){
_start:
{
uint8_t v___x_3624_; 
v___x_3624_ = lean_usize_dec_lt(v_i_3622_, v_sz_3621_);
if (v___x_3624_ == 0)
{
return v_bs_3623_;
}
else
{
lean_object* v_v_3625_; lean_object* v_declName_3626_; lean_object* v___x_3627_; lean_object* v_bs_x27_3628_; size_t v___x_3629_; size_t v___x_3630_; lean_object* v___x_3631_; 
v_v_3625_ = lean_array_uget_borrowed(v_bs_3623_, v_i_3622_);
v_declName_3626_ = lean_ctor_get(v_v_3625_, 3);
lean_inc(v_declName_3626_);
v___x_3627_ = lean_unsigned_to_nat(0u);
v_bs_x27_3628_ = lean_array_uset(v_bs_3623_, v_i_3622_, v___x_3627_);
v___x_3629_ = ((size_t)1ULL);
v___x_3630_ = lean_usize_add(v_i_3622_, v___x_3629_);
v___x_3631_ = lean_array_uset(v_bs_x27_3628_, v_i_3622_, v_declName_3626_);
v_i_3622_ = v___x_3630_;
v_bs_3623_ = v___x_3631_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_3621_ = stack[0].m_num;
size_t v_i_3622_ = stack[1].m_num;
lean_object* v_bs_3623_ = stack[2].m_obj;
lean_object* v_res_3633_;
v_res_3633_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0(v_sz_3621_, v_i_3622_, v_bs_3623_);
stack->m_obj
 = v_res_3633_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0___boxed(lean_object* v_sz_3634_, lean_object* v_i_3635_, lean_object* v_bs_3636_){
_start:
{
size_t v_sz_boxed_3637_; size_t v_i_boxed_3638_; lean_object* v_res_3639_; 
v_sz_boxed_3637_ = lean_unbox_usize(v_sz_3634_);
lean_dec(v_sz_3634_);
v_i_boxed_3638_ = lean_unbox_usize(v_i_3635_);
lean_dec(v_i_3635_);
v_res_3639_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0(v_sz_boxed_3637_, v_i_boxed_3638_, v_bs_3636_);
return v_res_3639_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1___redArg(lean_object* v_fnNames_3640_, lean_object* v_numSectionVars_3641_, size_t v_sz_3642_, size_t v_i_3643_, lean_object* v_bs_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_){
_start:
{
uint8_t v___x_3648_; 
v___x_3648_ = lean_usize_dec_lt(v_i_3643_, v_sz_3642_);
if (v___x_3648_ == 0)
{
lean_object* v___x_3649_; 
lean_dec(v_numSectionVars_3641_);
lean_dec_ref(v_fnNames_3640_);
v___x_3649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3649_, 0, v_bs_3644_);
return v___x_3649_;
}
else
{
lean_object* v_v_3650_; lean_object* v_ref_3651_; uint8_t v_kind_3652_; lean_object* v_levelParams_3653_; lean_object* v_modifiers_3654_; lean_object* v_declName_3655_; lean_object* v_binders_3656_; lean_object* v_numSectionVars_3657_; lean_object* v_type_3658_; lean_object* v_value_3659_; lean_object* v_termination_3660_; lean_object* v___x_3662_; uint8_t v_isShared_3663_; uint8_t v_isSharedCheck_3683_; 
v_v_3650_ = lean_array_uget(v_bs_3644_, v_i_3643_);
v_ref_3651_ = lean_ctor_get(v_v_3650_, 0);
v_kind_3652_ = lean_ctor_get_uint8(v_v_3650_, sizeof(void*)*9);
v_levelParams_3653_ = lean_ctor_get(v_v_3650_, 1);
v_modifiers_3654_ = lean_ctor_get(v_v_3650_, 2);
v_declName_3655_ = lean_ctor_get(v_v_3650_, 3);
v_binders_3656_ = lean_ctor_get(v_v_3650_, 4);
v_numSectionVars_3657_ = lean_ctor_get(v_v_3650_, 5);
v_type_3658_ = lean_ctor_get(v_v_3650_, 6);
v_value_3659_ = lean_ctor_get(v_v_3650_, 7);
v_termination_3660_ = lean_ctor_get(v_v_3650_, 8);
v_isSharedCheck_3683_ = !lean_is_exclusive(v_v_3650_);
if (v_isSharedCheck_3683_ == 0)
{
v___x_3662_ = v_v_3650_;
v_isShared_3663_ = v_isSharedCheck_3683_;
goto v_resetjp_3661_;
}
else
{
lean_inc(v_termination_3660_);
lean_inc(v_value_3659_);
lean_inc(v_type_3658_);
lean_inc(v_numSectionVars_3657_);
lean_inc(v_binders_3656_);
lean_inc(v_declName_3655_);
lean_inc(v_modifiers_3654_);
lean_inc(v_levelParams_3653_);
lean_inc(v_ref_3651_);
lean_dec(v_v_3650_);
v___x_3662_ = lean_box(0);
v_isShared_3663_ = v_isSharedCheck_3683_;
goto v_resetjp_3661_;
}
v_resetjp_3661_:
{
lean_object* v___x_3664_; lean_object* v_bs_x27_3665_; lean_object* v___x_3666_; 
v___x_3664_ = lean_unsigned_to_nat(0u);
v_bs_x27_3665_ = lean_array_uset(v_bs_3644_, v_i_3643_, v___x_3664_);
lean_inc(v_numSectionVars_3641_);
lean_inc_ref(v_fnNames_3640_);
v___x_3666_ = l_Lean_Elab_Structural_preprocess(v_value_3659_, v_fnNames_3640_, v_numSectionVars_3641_, v___y_3645_, v___y_3646_);
if (lean_obj_tag(v___x_3666_) == 0)
{
lean_object* v_a_3667_; lean_object* v___x_3669_; 
v_a_3667_ = lean_ctor_get(v___x_3666_, 0);
lean_inc(v_a_3667_);
lean_dec_ref_known(v___x_3666_, 1);
if (v_isShared_3663_ == 0)
{
lean_ctor_set(v___x_3662_, 7, v_a_3667_);
v___x_3669_ = v___x_3662_;
goto v_reusejp_3668_;
}
else
{
lean_object* v_reuseFailAlloc_3674_; 
v_reuseFailAlloc_3674_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_3674_, 0, v_ref_3651_);
lean_ctor_set(v_reuseFailAlloc_3674_, 1, v_levelParams_3653_);
lean_ctor_set(v_reuseFailAlloc_3674_, 2, v_modifiers_3654_);
lean_ctor_set(v_reuseFailAlloc_3674_, 3, v_declName_3655_);
lean_ctor_set(v_reuseFailAlloc_3674_, 4, v_binders_3656_);
lean_ctor_set(v_reuseFailAlloc_3674_, 5, v_numSectionVars_3657_);
lean_ctor_set(v_reuseFailAlloc_3674_, 6, v_type_3658_);
lean_ctor_set(v_reuseFailAlloc_3674_, 7, v_a_3667_);
lean_ctor_set(v_reuseFailAlloc_3674_, 8, v_termination_3660_);
lean_ctor_set_uint8(v_reuseFailAlloc_3674_, sizeof(void*)*9, v_kind_3652_);
v___x_3669_ = v_reuseFailAlloc_3674_;
goto v_reusejp_3668_;
}
v_reusejp_3668_:
{
size_t v___x_3670_; size_t v___x_3671_; lean_object* v___x_3672_; 
v___x_3670_ = ((size_t)1ULL);
v___x_3671_ = lean_usize_add(v_i_3643_, v___x_3670_);
v___x_3672_ = lean_array_uset(v_bs_x27_3665_, v_i_3643_, v___x_3669_);
v_i_3643_ = v___x_3671_;
v_bs_3644_ = v___x_3672_;
goto _start;
}
}
else
{
lean_object* v_a_3675_; lean_object* v___x_3677_; uint8_t v_isShared_3678_; uint8_t v_isSharedCheck_3682_; 
lean_dec_ref(v_bs_x27_3665_);
lean_del_object(v___x_3662_);
lean_dec_ref(v_termination_3660_);
lean_dec_ref(v_type_3658_);
lean_dec(v_numSectionVars_3657_);
lean_dec(v_binders_3656_);
lean_dec(v_declName_3655_);
lean_dec_ref(v_modifiers_3654_);
lean_dec(v_levelParams_3653_);
lean_dec(v_ref_3651_);
lean_dec(v_numSectionVars_3641_);
lean_dec_ref(v_fnNames_3640_);
v_a_3675_ = lean_ctor_get(v___x_3666_, 0);
v_isSharedCheck_3682_ = !lean_is_exclusive(v___x_3666_);
if (v_isSharedCheck_3682_ == 0)
{
v___x_3677_ = v___x_3666_;
v_isShared_3678_ = v_isSharedCheck_3682_;
goto v_resetjp_3676_;
}
else
{
lean_inc(v_a_3675_);
lean_dec(v___x_3666_);
v___x_3677_ = lean_box(0);
v_isShared_3678_ = v_isSharedCheck_3682_;
goto v_resetjp_3676_;
}
v_resetjp_3676_:
{
lean_object* v___x_3680_; 
if (v_isShared_3678_ == 0)
{
v___x_3680_ = v___x_3677_;
goto v_reusejp_3679_;
}
else
{
lean_object* v_reuseFailAlloc_3681_; 
v_reuseFailAlloc_3681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3681_, 0, v_a_3675_);
v___x_3680_ = v_reuseFailAlloc_3681_;
goto v_reusejp_3679_;
}
v_reusejp_3679_:
{
return v___x_3680_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_fnNames_3640_ = stack[0].m_obj;
lean_object* v_numSectionVars_3641_ = stack[1].m_obj;
size_t v_sz_3642_ = stack[2].m_num;
size_t v_i_3643_ = stack[3].m_num;
lean_object* v_bs_3644_ = stack[4].m_obj;
lean_object* v___y_3645_ = stack[5].m_obj;
lean_object* v___y_3646_ = stack[6].m_obj;
lean_object* v_res_3684_;
v_res_3684_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1___redArg(v_fnNames_3640_, v_numSectionVars_3641_, v_sz_3642_, v_i_3643_, v_bs_3644_, v___y_3645_, v___y_3646_);
stack->m_obj
 = v_res_3684_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1___redArg___boxed(lean_object* v_fnNames_3685_, lean_object* v_numSectionVars_3686_, lean_object* v_sz_3687_, lean_object* v_i_3688_, lean_object* v_bs_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_){
_start:
{
size_t v_sz_boxed_3693_; size_t v_i_boxed_3694_; lean_object* v_res_3695_; 
v_sz_boxed_3693_ = lean_unbox_usize(v_sz_3687_);
lean_dec(v_sz_3687_);
v_i_boxed_3694_ = lean_unbox_usize(v_i_3688_);
lean_dec(v_i_3688_);
v_res_3695_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1___redArg(v_fnNames_3685_, v_numSectionVars_3686_, v_sz_boxed_3693_, v_i_boxed_3694_, v_bs_3689_, v___y_3690_, v___y_3691_);
lean_dec(v___y_3691_);
lean_dec_ref(v___y_3690_);
return v_res_3695_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1(lean_object* v_fnNames_3696_, lean_object* v_numSectionVars_3697_, size_t v_sz_3698_, size_t v_i_3699_, lean_object* v_bs_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_){
_start:
{
lean_object* v___x_3706_; 
v___x_3706_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1___redArg(v_fnNames_3696_, v_numSectionVars_3697_, v_sz_3698_, v_i_3699_, v_bs_3700_, v___y_3703_, v___y_3704_);
return v___x_3706_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_fnNames_3696_ = stack[0].m_obj;
lean_object* v_numSectionVars_3697_ = stack[1].m_obj;
size_t v_sz_3698_ = stack[2].m_num;
size_t v_i_3699_ = stack[3].m_num;
lean_object* v_bs_3700_ = stack[4].m_obj;
lean_object* v___y_3701_ = stack[5].m_obj;
lean_object* v___y_3702_ = stack[6].m_obj;
lean_object* v___y_3703_ = stack[7].m_obj;
lean_object* v___y_3704_ = stack[8].m_obj;
lean_object* v_res_3707_;
v_res_3707_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1(v_fnNames_3696_, v_numSectionVars_3697_, v_sz_3698_, v_i_3699_, v_bs_3700_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_);
stack->m_obj
 = v_res_3707_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1___boxed(lean_object* v_fnNames_3708_, lean_object* v_numSectionVars_3709_, lean_object* v_sz_3710_, lean_object* v_i_3711_, lean_object* v_bs_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_){
_start:
{
size_t v_sz_boxed_3718_; size_t v_i_boxed_3719_; lean_object* v_res_3720_; 
v_sz_boxed_3718_ = lean_unbox_usize(v_sz_3710_);
lean_dec(v_sz_3710_);
v_i_boxed_3719_ = lean_unbox_usize(v_i_3711_);
lean_dec(v_i_3711_);
v_res_3720_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1(v_fnNames_3708_, v_numSectionVars_3709_, v_sz_boxed_3718_, v_i_boxed_3719_, v_bs_3712_, v___y_3713_, v___y_3714_, v___y_3715_, v___y_3716_);
lean_dec(v___y_3716_);
lean_dec_ref(v___y_3715_);
lean_dec(v___y_3714_);
lean_dec_ref(v___y_3713_);
return v_res_3720_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos(lean_object* v_preDefs_3721_, lean_object* v_termMeasure_x3fs_3722_, lean_object* v_a_3723_, lean_object* v_a_3724_, lean_object* v_a_3725_, lean_object* v_a_3726_){
_start:
{
lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v_numSectionVars_3731_; size_t v_sz_3732_; lean_object* v___x_3733_; size_t v___x_3734_; lean_object* v_fnNames_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; 
v___x_3728_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_3729_ = lean_unsigned_to_nat(0u);
v___x_3730_ = lean_array_get_borrowed(v___x_3728_, v_preDefs_3721_, v___x_3729_);
v_numSectionVars_3731_ = lean_ctor_get(v___x_3730_, 5);
v_sz_3732_ = lean_array_size(v_preDefs_3721_);
v___x_3733_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0);
v___x_3734_ = ((size_t)0ULL);
lean_inc_ref_n(v_preDefs_3721_, 2);
v_fnNames_3735_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0(v_sz_3732_, v___x_3734_, v_preDefs_3721_);
v___x_3736_ = lean_box_usize(v_sz_3732_);
v___x_3737_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___boxed__const__1));
lean_inc(v_numSectionVars_3731_);
lean_inc_ref(v_fnNames_3735_);
v___x_3738_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1___boxed), 10, 5);
lean_closure_set(v___x_3738_, 0, v_fnNames_3735_);
lean_closure_set(v___x_3738_, 1, v_numSectionVars_3731_);
lean_closure_set(v___x_3738_, 2, v___x_3736_);
lean_closure_set(v___x_3738_, 3, v___x_3737_);
lean_closure_set(v___x_3738_, 4, v_preDefs_3721_);
v___x_3739_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v_preDefs_3721_, v___x_3738_, v_a_3723_, v_a_3724_, v_a_3725_, v_a_3726_);
if (lean_obj_tag(v___x_3739_) == 0)
{
lean_object* v_a_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; 
v_a_3740_ = lean_ctor_get(v___x_3739_, 0);
lean_inc_n(v_a_3740_, 3);
lean_dec_ref_known(v___x_3739_, 1);
v___x_3741_ = lean_alloc_closure((void*)(l_Lean_Elab_getFixedParamPerms___boxed), 6, 1);
lean_closure_set(v___x_3741_, 0, v_a_3740_);
v___x_3742_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v_a_3740_, v___x_3741_, v_a_3723_, v_a_3724_, v_a_3725_, v_a_3726_);
if (lean_obj_tag(v___x_3742_) == 0)
{
lean_object* v_a_3743_; lean_object* v_perms_3744_; lean_object* v___x_3745_; lean_object* v_type_3746_; lean_object* v___x_3747_; lean_object* v___f_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; 
v_a_3743_ = lean_ctor_get(v___x_3742_, 0);
lean_inc(v_a_3743_);
lean_dec_ref_known(v___x_3742_, 1);
v_perms_3744_ = lean_ctor_get(v_a_3743_, 1);
lean_inc_ref_n(v_perms_3744_, 2);
v___x_3745_ = lean_array_get_borrowed(v___x_3728_, v_a_3740_, v___x_3729_);
v_type_3746_ = lean_ctor_get(v___x_3745_, 6);
lean_inc_ref(v_type_3746_);
v___x_3747_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___boxed__const__1));
v___f_3748_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__2___boxed), 12, 6);
lean_closure_set(v___f_3748_, 0, v___x_3747_);
lean_closure_set(v___f_3748_, 1, v_a_3743_);
lean_closure_set(v___f_3748_, 2, v_a_3740_);
lean_closure_set(v___f_3748_, 3, v_perms_3744_);
lean_closure_set(v___f_3748_, 4, v_fnNames_3735_);
lean_closure_set(v___f_3748_, 5, v_termMeasure_x3fs_3722_);
v___x_3749_ = lean_array_get(v___x_3733_, v_perms_3744_, v___x_3729_);
lean_dec_ref(v_perms_3744_);
v___x_3750_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg(v___x_3749_, v_type_3746_, v___f_3748_, v_a_3723_, v_a_3724_, v_a_3725_, v_a_3726_);
return v___x_3750_;
}
else
{
lean_object* v_a_3751_; lean_object* v___x_3753_; uint8_t v_isShared_3754_; uint8_t v_isSharedCheck_3758_; 
lean_dec(v_a_3740_);
lean_dec_ref(v_fnNames_3735_);
lean_dec_ref(v_termMeasure_x3fs_3722_);
v_a_3751_ = lean_ctor_get(v___x_3742_, 0);
v_isSharedCheck_3758_ = !lean_is_exclusive(v___x_3742_);
if (v_isSharedCheck_3758_ == 0)
{
v___x_3753_ = v___x_3742_;
v_isShared_3754_ = v_isSharedCheck_3758_;
goto v_resetjp_3752_;
}
else
{
lean_inc(v_a_3751_);
lean_dec(v___x_3742_);
v___x_3753_ = lean_box(0);
v_isShared_3754_ = v_isSharedCheck_3758_;
goto v_resetjp_3752_;
}
v_resetjp_3752_:
{
lean_object* v___x_3756_; 
if (v_isShared_3754_ == 0)
{
v___x_3756_ = v___x_3753_;
goto v_reusejp_3755_;
}
else
{
lean_object* v_reuseFailAlloc_3757_; 
v_reuseFailAlloc_3757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3757_, 0, v_a_3751_);
v___x_3756_ = v_reuseFailAlloc_3757_;
goto v_reusejp_3755_;
}
v_reusejp_3755_:
{
return v___x_3756_;
}
}
}
}
else
{
lean_object* v_a_3759_; lean_object* v___x_3761_; uint8_t v_isShared_3762_; uint8_t v_isSharedCheck_3766_; 
lean_dec_ref(v_fnNames_3735_);
lean_dec_ref(v_termMeasure_x3fs_3722_);
v_a_3759_ = lean_ctor_get(v___x_3739_, 0);
v_isSharedCheck_3766_ = !lean_is_exclusive(v___x_3739_);
if (v_isSharedCheck_3766_ == 0)
{
v___x_3761_ = v___x_3739_;
v_isShared_3762_ = v_isSharedCheck_3766_;
goto v_resetjp_3760_;
}
else
{
lean_inc(v_a_3759_);
lean_dec(v___x_3739_);
v___x_3761_ = lean_box(0);
v_isShared_3762_ = v_isSharedCheck_3766_;
goto v_resetjp_3760_;
}
v_resetjp_3760_:
{
lean_object* v___x_3764_; 
if (v_isShared_3762_ == 0)
{
v___x_3764_ = v___x_3761_;
goto v_reusejp_3763_;
}
else
{
lean_object* v_reuseFailAlloc_3765_; 
v_reuseFailAlloc_3765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3765_, 0, v_a_3759_);
v___x_3764_ = v_reuseFailAlloc_3765_;
goto v_reusejp_3763_;
}
v_reusejp_3763_:
{
return v___x_3764_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_0interp(lean_interpreter_value* stack)
{
lean_object* v_preDefs_3721_ = stack[0].m_obj;
lean_object* v_termMeasure_x3fs_3722_ = stack[1].m_obj;
lean_object* v_a_3723_ = stack[2].m_obj;
lean_object* v_a_3724_ = stack[3].m_obj;
lean_object* v_a_3725_ = stack[4].m_obj;
lean_object* v_a_3726_ = stack[5].m_obj;
lean_object* v_res_3767_;
v_res_3767_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos(v_preDefs_3721_, v_termMeasure_x3fs_3722_, v_a_3723_, v_a_3724_, v_a_3725_, v_a_3726_);
stack->m_obj
 = v_res_3767_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___boxed(lean_object* v_preDefs_3768_, lean_object* v_termMeasure_x3fs_3769_, lean_object* v_a_3770_, lean_object* v_a_3771_, lean_object* v_a_3772_, lean_object* v_a_3773_, lean_object* v_a_3774_){
_start:
{
lean_object* v_res_3775_; 
v_res_3775_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos(v_preDefs_3768_, v_termMeasure_x3fs_3769_, v_a_3770_, v_a_3771_, v_a_3772_, v_a_3773_);
lean_dec(v_a_3773_);
lean_dec_ref(v_a_3772_);
lean_dec(v_a_3771_);
lean_dec_ref(v_a_3770_);
return v_res_3775_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4(lean_object* v_fst_3776_, lean_object* v_as_3777_, size_t v_sz_3778_, size_t v_i_3779_, lean_object* v_bs_3780_){
_start:
{
lean_object* v___x_3781_; 
v___x_3781_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg(v_fst_3776_, v_sz_3778_, v_i_3779_, v_bs_3780_);
return v___x_3781_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_fst_3776_ = stack[0].m_obj;
lean_object* v_as_3777_ = stack[1].m_obj;
size_t v_sz_3778_ = stack[2].m_num;
size_t v_i_3779_ = stack[3].m_num;
lean_object* v_bs_3780_ = stack[4].m_obj;
lean_object* v_res_3782_;
v_res_3782_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4(v_fst_3776_, v_as_3777_, v_sz_3778_, v_i_3779_, v_bs_3780_);
stack->m_obj
 = v_res_3782_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___boxed(lean_object* v_fst_3783_, lean_object* v_as_3784_, lean_object* v_sz_3785_, lean_object* v_i_3786_, lean_object* v_bs_3787_){
_start:
{
size_t v_sz_boxed_3788_; size_t v_i_boxed_3789_; lean_object* v_res_3790_; 
v_sz_boxed_3788_ = lean_unbox_usize(v_sz_3785_);
lean_dec(v_sz_3785_);
v_i_boxed_3789_ = lean_unbox_usize(v_i_3786_);
lean_dec(v_i_3786_);
v_res_3790_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4(v_fst_3783_, v_as_3784_, v_sz_boxed_3788_, v_i_boxed_3789_, v_bs_3787_);
lean_dec_ref(v_as_3784_);
lean_dec_ref(v_fst_3783_);
return v_res_3790_;
}
}
lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10(lean_object* v_00_u03b1_3791_, lean_object* v_lctx_3792_, lean_object* v_localInsts_3793_, lean_object* v_x_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_){
_start:
{
lean_object* v___x_3800_; 
v___x_3800_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___redArg(v_lctx_3792_, v_localInsts_3793_, v_x_3794_, v___y_3795_, v___y_3796_, v___y_3797_, v___y_3798_);
return v___x_3800_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_lctx_3792_ = stack[1].m_obj;
lean_object* v_localInsts_3793_ = stack[2].m_obj;
lean_object* v_x_3794_ = stack[3].m_obj;
lean_object* v___y_3795_ = stack[4].m_obj;
lean_object* v___y_3796_ = stack[5].m_obj;
lean_object* v___y_3797_ = stack[6].m_obj;
lean_object* v___y_3798_ = stack[7].m_obj;
lean_object* v_res_3801_;
v_res_3801_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10(lean_box(0), v_lctx_3792_, v_localInsts_3793_, v_x_3794_, v___y_3795_, v___y_3796_, v___y_3797_, v___y_3798_);
stack->m_obj
 = v_res_3801_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___boxed(lean_object* v_00_u03b1_3802_, lean_object* v_lctx_3803_, lean_object* v_localInsts_3804_, lean_object* v_x_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_){
_start:
{
lean_object* v_res_3811_; 
v_res_3811_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10(v_00_u03b1_3802_, v_lctx_3803_, v_localInsts_3804_, v_x_3805_, v___y_3806_, v___y_3807_, v___y_3808_, v___y_3809_);
lean_dec(v___y_3809_);
lean_dec_ref(v___y_3808_);
lean_dec(v___y_3807_);
lean_dec_ref(v___y_3806_);
return v_res_3811_;
}
}
lean_object* l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9(lean_object* v_00_u03b1_3812_, lean_object* v_fvarIds_3813_, lean_object* v_k_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_){
_start:
{
lean_object* v___x_3820_; 
v___x_3820_ = l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___redArg(v_fvarIds_3813_, v_k_3814_, v___y_3815_, v___y_3816_, v___y_3817_, v___y_3818_);
return v___x_3820_;
}
}
LEAN_EXPORT void l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarIds_3813_ = stack[1].m_obj;
lean_object* v_k_3814_ = stack[2].m_obj;
lean_object* v___y_3815_ = stack[3].m_obj;
lean_object* v___y_3816_ = stack[4].m_obj;
lean_object* v___y_3817_ = stack[5].m_obj;
lean_object* v___y_3818_ = stack[6].m_obj;
lean_object* v_res_3821_;
v_res_3821_ = l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9(lean_box(0), v_fvarIds_3813_, v_k_3814_, v___y_3815_, v___y_3816_, v___y_3817_, v___y_3818_);
stack->m_obj
 = v_res_3821_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___boxed(lean_object* v_00_u03b1_3822_, lean_object* v_fvarIds_3823_, lean_object* v_k_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_){
_start:
{
lean_object* v_res_3830_; 
v_res_3830_ = l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9(v_00_u03b1_3822_, v_fvarIds_3823_, v_k_3824_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_);
lean_dec(v___y_3828_);
lean_dec_ref(v___y_3827_);
lean_dec(v___y_3826_);
lean_dec_ref(v___y_3825_);
lean_dec_ref(v_fvarIds_3823_);
return v_res_3830_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__15(lean_object* v_a_3831_){
_start:
{
lean_object* v___x_3832_; 
v___x_3832_ = lean_nat_to_int(v_a_3831_);
return v___x_3832_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12(lean_object* v___x_3833_, lean_object* v_xs_3834_, lean_object* v_as_3835_, size_t v_sz_3836_, size_t v_i_3837_, lean_object* v_bs_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_){
_start:
{
lean_object* v___x_3844_; 
v___x_3844_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg(v___x_3833_, v_xs_3834_, v_sz_3836_, v_i_3837_, v_bs_3838_, v___y_3839_, v___y_3840_, v___y_3841_, v___y_3842_);
return v___x_3844_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3833_ = stack[0].m_obj;
lean_object* v_xs_3834_ = stack[1].m_obj;
lean_object* v_as_3835_ = stack[2].m_obj;
size_t v_sz_3836_ = stack[3].m_num;
size_t v_i_3837_ = stack[4].m_num;
lean_object* v_bs_3838_ = stack[5].m_obj;
lean_object* v___y_3839_ = stack[6].m_obj;
lean_object* v___y_3840_ = stack[7].m_obj;
lean_object* v___y_3841_ = stack[8].m_obj;
lean_object* v___y_3842_ = stack[9].m_obj;
lean_object* v_res_3845_;
v_res_3845_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12(v___x_3833_, v_xs_3834_, v_as_3835_, v_sz_3836_, v_i_3837_, v_bs_3838_, v___y_3839_, v___y_3840_, v___y_3841_, v___y_3842_);
stack->m_obj
 = v_res_3845_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___boxed(lean_object* v___x_3846_, lean_object* v_xs_3847_, lean_object* v_as_3848_, lean_object* v_sz_3849_, lean_object* v_i_3850_, lean_object* v_bs_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_){
_start:
{
size_t v_sz_boxed_3857_; size_t v_i_boxed_3858_; lean_object* v_res_3859_; 
v_sz_boxed_3857_ = lean_unbox_usize(v_sz_3849_);
lean_dec(v_sz_3849_);
v_i_boxed_3858_ = lean_unbox_usize(v_i_3850_);
lean_dec(v_i_3850_);
v_res_3859_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12(v___x_3846_, v_xs_3847_, v_as_3848_, v_sz_boxed_3857_, v_i_boxed_3858_, v_bs_3851_, v___y_3852_, v___y_3853_, v___y_3854_, v___y_3855_);
lean_dec(v___y_3855_);
lean_dec_ref(v___y_3854_);
lean_dec(v___y_3853_);
lean_dec_ref(v___y_3852_);
lean_dec_ref(v_as_3848_);
lean_dec_ref(v___x_3846_);
return v_res_3859_;
}
}
lean_object* l_Lean_Elab_Structural_reportTermMeasure___lam__0(lean_object* v_xs_3860_, lean_object* v_x_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_){
_start:
{
lean_object* v___x_3867_; lean_object* v___x_3868_; 
v___x_3867_ = lean_array_get_size(v_xs_3860_);
v___x_3868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3868_, 0, v___x_3867_);
return v___x_3868_;
}
}
LEAN_EXPORT void l_Lean_Elab_Structural_reportTermMeasure___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_3860_ = stack[0].m_obj;
lean_object* v_x_3861_ = stack[1].m_obj;
lean_object* v___y_3862_ = stack[2].m_obj;
lean_object* v___y_3863_ = stack[3].m_obj;
lean_object* v___y_3864_ = stack[4].m_obj;
lean_object* v___y_3865_ = stack[5].m_obj;
lean_object* v_res_3869_;
v_res_3869_ = l_Lean_Elab_Structural_reportTermMeasure___lam__0(v_xs_3860_, v_x_3861_, v___y_3862_, v___y_3863_, v___y_3864_, v___y_3865_);
stack->m_obj
 = v_res_3869_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure___lam__0___boxed(lean_object* v_xs_3870_, lean_object* v_x_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_){
_start:
{
lean_object* v_res_3877_; 
v_res_3877_ = l_Lean_Elab_Structural_reportTermMeasure___lam__0(v_xs_3870_, v_x_3871_, v___y_3872_, v___y_3873_, v___y_3874_, v___y_3875_);
lean_dec(v___y_3875_);
lean_dec_ref(v___y_3874_);
lean_dec(v___y_3873_);
lean_dec_ref(v___y_3872_);
lean_dec_ref(v_x_3871_);
lean_dec_ref(v_xs_3870_);
return v_res_3877_;
}
}
lean_object* l_Lean_Elab_Structural_reportTermMeasure___lam__1(lean_object* v___x_3878_, lean_object* v_recArgPos_3879_, lean_object* v_xs_3880_, lean_object* v_x_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_){
_start:
{
lean_object* v___x_3887_; uint8_t v___x_3888_; uint8_t v___x_3889_; uint8_t v___x_3890_; lean_object* v___x_3891_; 
v___x_3887_ = lean_array_get_borrowed(v___x_3878_, v_xs_3880_, v_recArgPos_3879_);
v___x_3888_ = 0;
v___x_3889_ = 1;
v___x_3890_ = 1;
lean_inc(v___x_3887_);
v___x_3891_ = l_Lean_Meta_mkLambdaFVars(v_xs_3880_, v___x_3887_, v___x_3888_, v___x_3889_, v___x_3888_, v___x_3889_, v___x_3890_, v___y_3882_, v___y_3883_, v___y_3884_, v___y_3885_);
return v___x_3891_;
}
}
LEAN_EXPORT void l_Lean_Elab_Structural_reportTermMeasure___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3878_ = stack[0].m_obj;
lean_object* v_recArgPos_3879_ = stack[1].m_obj;
lean_object* v_xs_3880_ = stack[2].m_obj;
lean_object* v_x_3881_ = stack[3].m_obj;
lean_object* v___y_3882_ = stack[4].m_obj;
lean_object* v___y_3883_ = stack[5].m_obj;
lean_object* v___y_3884_ = stack[6].m_obj;
lean_object* v___y_3885_ = stack[7].m_obj;
lean_object* v_res_3892_;
v_res_3892_ = l_Lean_Elab_Structural_reportTermMeasure___lam__1(v___x_3878_, v_recArgPos_3879_, v_xs_3880_, v_x_3881_, v___y_3882_, v___y_3883_, v___y_3884_, v___y_3885_);
stack->m_obj
 = v_res_3892_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure___lam__1___boxed(lean_object* v___x_3893_, lean_object* v_recArgPos_3894_, lean_object* v_xs_3895_, lean_object* v_x_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_){
_start:
{
lean_object* v_res_3902_; 
v_res_3902_ = l_Lean_Elab_Structural_reportTermMeasure___lam__1(v___x_3893_, v_recArgPos_3894_, v_xs_3895_, v_x_3896_, v___y_3897_, v___y_3898_, v___y_3899_, v___y_3900_);
lean_dec(v___y_3900_);
lean_dec_ref(v___y_3899_);
lean_dec(v___y_3898_);
lean_dec_ref(v___y_3897_);
lean_dec_ref(v_x_3896_);
lean_dec_ref(v_xs_3895_);
lean_dec(v_recArgPos_3894_);
lean_dec_ref(v___x_3893_);
return v_res_3902_;
}
}
lean_object* l_Lean_Elab_Structural_reportTermMeasure(lean_object* v_preDef_3914_, lean_object* v_recArgPos_3915_, lean_object* v_a_3916_, lean_object* v_a_3917_, lean_object* v_a_3918_, lean_object* v_a_3919_){
_start:
{
lean_object* v_termination_3921_; lean_object* v_terminationBy_x3f_x3f_3922_; 
v_termination_3921_ = lean_ctor_get(v_preDef_3914_, 8);
lean_inc_ref(v_termination_3921_);
v_terminationBy_x3f_x3f_3922_ = lean_ctor_get(v_termination_3921_, 1);
lean_inc(v_terminationBy_x3f_x3f_3922_);
if (lean_obj_tag(v_terminationBy_x3f_x3f_3922_) == 1)
{
lean_object* v_value_3923_; lean_object* v_extraParams_3924_; lean_object* v_val_3925_; lean_object* v___f_3926_; lean_object* v___x_3927_; lean_object* v___f_3928_; uint8_t v___x_3929_; lean_object* v___x_3930_; 
v_value_3923_ = lean_ctor_get(v_preDef_3914_, 7);
lean_inc_ref_n(v_value_3923_, 2);
lean_dec_ref(v_preDef_3914_);
v_extraParams_3924_ = lean_ctor_get(v_termination_3921_, 5);
lean_inc(v_extraParams_3924_);
lean_dec_ref(v_termination_3921_);
v_val_3925_ = lean_ctor_get(v_terminationBy_x3f_x3f_3922_, 0);
lean_inc(v_val_3925_);
lean_dec_ref_known(v_terminationBy_x3f_x3f_3922_, 1);
v___f_3926_ = ((lean_object*)(l_Lean_Elab_Structural_reportTermMeasure___closed__0));
v___x_3927_ = l_Lean_instInhabitedExpr;
v___f_3928_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_reportTermMeasure___lam__1___boxed), 9, 2);
lean_closure_set(v___f_3928_, 0, v___x_3927_);
lean_closure_set(v___f_3928_, 1, v_recArgPos_3915_);
v___x_3929_ = 0;
v___x_3930_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg(v_value_3923_, v___f_3928_, v___x_3929_, v_a_3916_, v_a_3917_, v_a_3918_, v_a_3919_);
if (lean_obj_tag(v___x_3930_) == 0)
{
lean_object* v_a_3931_; lean_object* v___x_3932_; uint8_t v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; 
v_a_3931_ = lean_ctor_get(v___x_3930_, 0);
lean_inc(v_a_3931_);
lean_dec_ref_known(v___x_3930_, 1);
v___x_3932_ = lean_box(0);
v___x_3933_ = 1;
v___x_3934_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3934_, 0, v___x_3932_);
lean_ctor_set(v___x_3934_, 1, v_a_3931_);
lean_ctor_set_uint8(v___x_3934_, sizeof(void*)*2, v___x_3933_);
v___x_3935_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg(v_value_3923_, v___f_3926_, v___x_3929_, v_a_3916_, v_a_3917_, v_a_3918_, v_a_3919_);
if (lean_obj_tag(v___x_3935_) == 0)
{
lean_object* v_a_3936_; lean_object* v___x_3937_; 
v_a_3936_ = lean_ctor_get(v___x_3935_, 0);
lean_inc(v_a_3936_);
lean_dec_ref_known(v___x_3935_, 1);
v___x_3937_ = l_Lean_Elab_TerminationMeasure_delab(v_a_3936_, v_extraParams_3924_, v___x_3934_, v_a_3916_, v_a_3917_, v_a_3918_, v_a_3919_);
lean_dec(v_a_3936_);
if (lean_obj_tag(v___x_3937_) == 0)
{
lean_object* v_a_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; uint8_t v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; 
v_a_3938_ = lean_ctor_get(v___x_3937_, 0);
lean_inc(v_a_3938_);
lean_dec_ref_known(v___x_3937_, 1);
v___x_3939_ = ((lean_object*)(l_Lean_Elab_Structural_reportTermMeasure___closed__5));
v___x_3940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3940_, 0, v___x_3939_);
lean_ctor_set(v___x_3940_, 1, v_a_3938_);
v___x_3941_ = lean_box(0);
v___x_3942_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3942_, 0, v___x_3940_);
lean_ctor_set(v___x_3942_, 1, v___x_3941_);
lean_ctor_set(v___x_3942_, 2, v___x_3941_);
lean_ctor_set(v___x_3942_, 3, v___x_3941_);
lean_ctor_set(v___x_3942_, 4, v___x_3941_);
lean_ctor_set(v___x_3942_, 5, v___x_3941_);
v___x_3943_ = ((lean_object*)(l_Lean_Elab_Structural_reportTermMeasure___closed__6));
v___x_3944_ = 4;
v___x_3945_ = l_Lean_MessageData_nil;
v___x_3946_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_val_3925_, v___x_3942_, v___x_3941_, v___x_3943_, v___x_3941_, v___x_3944_, v___x_3945_, v_a_3918_, v_a_3919_);
return v___x_3946_;
}
else
{
lean_object* v_a_3947_; lean_object* v___x_3949_; uint8_t v_isShared_3950_; uint8_t v_isSharedCheck_3954_; 
lean_dec(v_val_3925_);
v_a_3947_ = lean_ctor_get(v___x_3937_, 0);
v_isSharedCheck_3954_ = !lean_is_exclusive(v___x_3937_);
if (v_isSharedCheck_3954_ == 0)
{
v___x_3949_ = v___x_3937_;
v_isShared_3950_ = v_isSharedCheck_3954_;
goto v_resetjp_3948_;
}
else
{
lean_inc(v_a_3947_);
lean_dec(v___x_3937_);
v___x_3949_ = lean_box(0);
v_isShared_3950_ = v_isSharedCheck_3954_;
goto v_resetjp_3948_;
}
v_resetjp_3948_:
{
lean_object* v___x_3952_; 
if (v_isShared_3950_ == 0)
{
v___x_3952_ = v___x_3949_;
goto v_reusejp_3951_;
}
else
{
lean_object* v_reuseFailAlloc_3953_; 
v_reuseFailAlloc_3953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3953_, 0, v_a_3947_);
v___x_3952_ = v_reuseFailAlloc_3953_;
goto v_reusejp_3951_;
}
v_reusejp_3951_:
{
return v___x_3952_;
}
}
}
}
else
{
lean_object* v_a_3955_; lean_object* v___x_3957_; uint8_t v_isShared_3958_; uint8_t v_isSharedCheck_3962_; 
lean_dec_ref_known(v___x_3934_, 2);
lean_dec(v_val_3925_);
lean_dec(v_extraParams_3924_);
v_a_3955_ = lean_ctor_get(v___x_3935_, 0);
v_isSharedCheck_3962_ = !lean_is_exclusive(v___x_3935_);
if (v_isSharedCheck_3962_ == 0)
{
v___x_3957_ = v___x_3935_;
v_isShared_3958_ = v_isSharedCheck_3962_;
goto v_resetjp_3956_;
}
else
{
lean_inc(v_a_3955_);
lean_dec(v___x_3935_);
v___x_3957_ = lean_box(0);
v_isShared_3958_ = v_isSharedCheck_3962_;
goto v_resetjp_3956_;
}
v_resetjp_3956_:
{
lean_object* v___x_3960_; 
if (v_isShared_3958_ == 0)
{
v___x_3960_ = v___x_3957_;
goto v_reusejp_3959_;
}
else
{
lean_object* v_reuseFailAlloc_3961_; 
v_reuseFailAlloc_3961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3961_, 0, v_a_3955_);
v___x_3960_ = v_reuseFailAlloc_3961_;
goto v_reusejp_3959_;
}
v_reusejp_3959_:
{
return v___x_3960_;
}
}
}
}
else
{
lean_object* v_a_3963_; lean_object* v___x_3965_; uint8_t v_isShared_3966_; uint8_t v_isSharedCheck_3970_; 
lean_dec(v_val_3925_);
lean_dec(v_extraParams_3924_);
lean_dec_ref(v_value_3923_);
v_a_3963_ = lean_ctor_get(v___x_3930_, 0);
v_isSharedCheck_3970_ = !lean_is_exclusive(v___x_3930_);
if (v_isSharedCheck_3970_ == 0)
{
v___x_3965_ = v___x_3930_;
v_isShared_3966_ = v_isSharedCheck_3970_;
goto v_resetjp_3964_;
}
else
{
lean_inc(v_a_3963_);
lean_dec(v___x_3930_);
v___x_3965_ = lean_box(0);
v_isShared_3966_ = v_isSharedCheck_3970_;
goto v_resetjp_3964_;
}
v_resetjp_3964_:
{
lean_object* v___x_3968_; 
if (v_isShared_3966_ == 0)
{
v___x_3968_ = v___x_3965_;
goto v_reusejp_3967_;
}
else
{
lean_object* v_reuseFailAlloc_3969_; 
v_reuseFailAlloc_3969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3969_, 0, v_a_3963_);
v___x_3968_ = v_reuseFailAlloc_3969_;
goto v_reusejp_3967_;
}
v_reusejp_3967_:
{
return v___x_3968_;
}
}
}
}
else
{
lean_object* v___x_3971_; lean_object* v___x_3972_; 
lean_dec(v_terminationBy_x3f_x3f_3922_);
lean_dec_ref(v_termination_3921_);
lean_dec(v_recArgPos_3915_);
lean_dec_ref(v_preDef_3914_);
v___x_3971_ = lean_box(0);
v___x_3972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3972_, 0, v___x_3971_);
return v___x_3972_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Structural_reportTermMeasure_0interp(lean_interpreter_value* stack)
{
lean_object* v_preDef_3914_ = stack[0].m_obj;
lean_object* v_recArgPos_3915_ = stack[1].m_obj;
lean_object* v_a_3916_ = stack[2].m_obj;
lean_object* v_a_3917_ = stack[3].m_obj;
lean_object* v_a_3918_ = stack[4].m_obj;
lean_object* v_a_3919_ = stack[5].m_obj;
lean_object* v_res_3973_;
v_res_3973_ = l_Lean_Elab_Structural_reportTermMeasure(v_preDef_3914_, v_recArgPos_3915_, v_a_3916_, v_a_3917_, v_a_3918_, v_a_3919_);
stack->m_obj
 = v_res_3973_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure___boxed(lean_object* v_preDef_3974_, lean_object* v_recArgPos_3975_, lean_object* v_a_3976_, lean_object* v_a_3977_, lean_object* v_a_3978_, lean_object* v_a_3979_, lean_object* v_a_3980_){
_start:
{
lean_object* v_res_3981_; 
v_res_3981_ = l_Lean_Elab_Structural_reportTermMeasure(v_preDef_3974_, v_recArgPos_3975_, v_a_3976_, v_a_3977_, v_a_3978_, v_a_3979_);
lean_dec(v_a_3979_);
lean_dec_ref(v_a_3978_);
lean_dec(v_a_3977_);
lean_dec_ref(v_a_3976_);
return v_res_3981_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___redArg(lean_object* v_as_3982_, size_t v_sz_3983_, size_t v_i_3984_, lean_object* v_b_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_){
_start:
{
uint8_t v___x_3991_; 
v___x_3991_ = lean_usize_dec_lt(v_i_3984_, v_sz_3983_);
if (v___x_3991_ == 0)
{
lean_object* v___x_3992_; 
v___x_3992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3992_, 0, v_b_3985_);
return v___x_3992_;
}
else
{
lean_object* v_a_3993_; lean_object* v_declName_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; 
v_a_3993_ = lean_array_uget_borrowed(v_as_3982_, v_i_3984_);
v_declName_3994_ = lean_ctor_get(v_a_3993_, 3);
v___x_3995_ = lean_box(0);
lean_inc(v_declName_3994_);
v___x_3996_ = l_Lean_Meta_saveEqnAffectingOptions(v_declName_3994_, v___y_3986_, v___y_3987_, v___y_3988_, v___y_3989_);
if (lean_obj_tag(v___x_3996_) == 0)
{
size_t v___x_3997_; size_t v___x_3998_; 
lean_dec_ref_known(v___x_3996_, 1);
v___x_3997_ = ((size_t)1ULL);
v___x_3998_ = lean_usize_add(v_i_3984_, v___x_3997_);
v_i_3984_ = v___x_3998_;
v_b_3985_ = v___x_3995_;
goto _start;
}
else
{
return v___x_3996_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3982_ = stack[0].m_obj;
size_t v_sz_3983_ = stack[1].m_num;
size_t v_i_3984_ = stack[2].m_num;
lean_object* v_b_3985_ = stack[3].m_obj;
lean_object* v___y_3986_ = stack[4].m_obj;
lean_object* v___y_3987_ = stack[5].m_obj;
lean_object* v___y_3988_ = stack[6].m_obj;
lean_object* v___y_3989_ = stack[7].m_obj;
lean_object* v_res_4000_;
v_res_4000_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___redArg(v_as_3982_, v_sz_3983_, v_i_3984_, v_b_3985_, v___y_3986_, v___y_3987_, v___y_3988_, v___y_3989_);
stack->m_obj
 = v_res_4000_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___redArg___boxed(lean_object* v_as_4001_, lean_object* v_sz_4002_, lean_object* v_i_4003_, lean_object* v_b_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_){
_start:
{
size_t v_sz_boxed_4010_; size_t v_i_boxed_4011_; lean_object* v_res_4012_; 
v_sz_boxed_4010_ = lean_unbox_usize(v_sz_4002_);
lean_dec(v_sz_4002_);
v_i_boxed_4011_ = lean_unbox_usize(v_i_4003_);
lean_dec(v_i_4003_);
v_res_4012_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___redArg(v_as_4001_, v_sz_boxed_4010_, v_i_boxed_4011_, v_b_4004_, v___y_4005_, v___y_4006_, v___y_4007_, v___y_4008_);
lean_dec(v___y_4008_);
lean_dec_ref(v___y_4007_);
lean_dec(v___y_4006_);
lean_dec_ref(v___y_4005_);
lean_dec_ref(v_as_4001_);
return v_res_4012_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__1(lean_object* v_docCtx_4013_, lean_object* v_a_4014_, lean_object* v_snd_4015_, lean_object* v_as_4016_, size_t v_sz_4017_, size_t v_i_4018_, lean_object* v_b_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_){
_start:
{
uint8_t v___x_4027_; 
v___x_4027_ = lean_usize_dec_lt(v_i_4018_, v_sz_4017_);
if (v___x_4027_ == 0)
{
lean_object* v___x_4028_; 
lean_dec_ref(v_snd_4015_);
lean_dec_ref(v_a_4014_);
lean_dec_ref(v_docCtx_4013_);
v___x_4028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4028_, 0, v_b_4019_);
return v___x_4028_;
}
else
{
lean_object* v_array_4029_; lean_object* v_start_4030_; lean_object* v_stop_4031_; uint8_t v___x_4032_; 
v_array_4029_ = lean_ctor_get(v_b_4019_, 0);
v_start_4030_ = lean_ctor_get(v_b_4019_, 1);
v_stop_4031_ = lean_ctor_get(v_b_4019_, 2);
v___x_4032_ = lean_nat_dec_lt(v_start_4030_, v_stop_4031_);
if (v___x_4032_ == 0)
{
lean_object* v___x_4033_; 
lean_dec_ref(v_snd_4015_);
lean_dec_ref(v_a_4014_);
lean_dec_ref(v_docCtx_4013_);
v___x_4033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4033_, 0, v_b_4019_);
return v___x_4033_;
}
else
{
lean_object* v___x_4035_; uint8_t v_isShared_4036_; uint8_t v_isSharedCheck_4100_; 
lean_inc(v_stop_4031_);
lean_inc(v_start_4030_);
lean_inc_ref(v_array_4029_);
v_isSharedCheck_4100_ = !lean_is_exclusive(v_b_4019_);
if (v_isSharedCheck_4100_ == 0)
{
lean_object* v_unused_4101_; lean_object* v_unused_4102_; lean_object* v_unused_4103_; 
v_unused_4101_ = lean_ctor_get(v_b_4019_, 2);
lean_dec(v_unused_4101_);
v_unused_4102_ = lean_ctor_get(v_b_4019_, 1);
lean_dec(v_unused_4102_);
v_unused_4103_ = lean_ctor_get(v_b_4019_, 0);
lean_dec(v_unused_4103_);
v___x_4035_ = v_b_4019_;
v_isShared_4036_ = v_isSharedCheck_4100_;
goto v_resetjp_4034_;
}
else
{
lean_dec(v_b_4019_);
v___x_4035_ = lean_box(0);
v_isShared_4036_ = v_isSharedCheck_4100_;
goto v_resetjp_4034_;
}
v_resetjp_4034_:
{
lean_object* v_a_4037_; uint8_t v_kind_4038_; lean_object* v_type_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4044_; 
v_a_4037_ = lean_array_uget_borrowed(v_as_4016_, v_i_4018_);
v_kind_4038_ = lean_ctor_get_uint8(v_a_4037_, sizeof(void*)*9);
v_type_4039_ = lean_ctor_get(v_a_4037_, 6);
v___x_4040_ = lean_array_fget(v_array_4029_, v_start_4030_);
v___x_4041_ = lean_unsigned_to_nat(1u);
v___x_4042_ = lean_nat_add(v_start_4030_, v___x_4041_);
lean_dec(v_start_4030_);
if (v_isShared_4036_ == 0)
{
lean_ctor_set(v___x_4035_, 1, v___x_4042_);
v___x_4044_ = v___x_4035_;
goto v_reusejp_4043_;
}
else
{
lean_object* v_reuseFailAlloc_4099_; 
v_reuseFailAlloc_4099_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4099_, 0, v_array_4029_);
lean_ctor_set(v_reuseFailAlloc_4099_, 1, v___x_4042_);
lean_ctor_set(v_reuseFailAlloc_4099_, 2, v_stop_4031_);
v___x_4044_ = v_reuseFailAlloc_4099_;
goto v_reusejp_4043_;
}
v_reusejp_4043_:
{
lean_object* v_preDef_4046_; lean_object* v___y_4047_; lean_object* v___y_4048_; lean_object* v___y_4049_; lean_object* v___y_4050_; lean_object* v___y_4051_; lean_object* v___y_4052_; uint8_t v___x_4065_; 
v___x_4065_ = l_Lean_Elab_DefKind_isTheorem(v_kind_4038_);
if (v___x_4065_ == 0)
{
lean_object* v___x_4066_; 
lean_inc_ref(v_type_4039_);
v___x_4066_ = l_Lean_Meta_isProp(v_type_4039_, v___y_4022_, v___y_4023_, v___y_4024_, v___y_4025_);
if (lean_obj_tag(v___x_4066_) == 0)
{
lean_object* v_a_4067_; uint8_t v___x_4068_; 
v_a_4067_ = lean_ctor_get(v___x_4066_, 0);
lean_inc(v_a_4067_);
lean_dec_ref_known(v___x_4066_, 1);
v___x_4068_ = lean_unbox(v_a_4067_);
lean_dec(v_a_4067_);
if (v___x_4068_ == 0)
{
lean_object* v___x_4069_; 
lean_inc(v_a_4037_);
v___x_4069_ = l_Lean_Elab_abstractNestedProofs(v_a_4037_, v___x_4032_, v___y_4022_, v___y_4023_, v___y_4024_, v___y_4025_);
if (lean_obj_tag(v___x_4069_) == 0)
{
lean_object* v_a_4070_; size_t v_sz_4071_; size_t v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; 
v_a_4070_ = lean_ctor_get(v___x_4069_, 0);
lean_inc_n(v_a_4070_, 2);
lean_dec_ref_known(v___x_4069_, 1);
v_sz_4071_ = lean_array_size(v_a_4014_);
v___x_4072_ = ((size_t)0ULL);
lean_inc_ref(v_a_4014_);
v___x_4073_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0(v_sz_4071_, v___x_4072_, v_a_4014_);
lean_inc_ref(v_snd_4015_);
lean_inc(v___x_4040_);
v___x_4074_ = l_Lean_Elab_Structural_registerEqnsInfo(v_a_4070_, v___x_4073_, v___x_4040_, v_snd_4015_, v___y_4024_, v___y_4025_);
if (lean_obj_tag(v___x_4074_) == 0)
{
lean_dec_ref_known(v___x_4074_, 1);
v_preDef_4046_ = v_a_4070_;
v___y_4047_ = v___y_4020_;
v___y_4048_ = v___y_4021_;
v___y_4049_ = v___y_4022_;
v___y_4050_ = v___y_4023_;
v___y_4051_ = v___y_4024_;
v___y_4052_ = v___y_4025_;
goto v___jp_4045_;
}
else
{
lean_object* v_a_4075_; lean_object* v___x_4077_; uint8_t v_isShared_4078_; uint8_t v_isSharedCheck_4082_; 
lean_dec(v_a_4070_);
lean_dec_ref(v___x_4044_);
lean_dec(v___x_4040_);
lean_dec_ref(v_snd_4015_);
lean_dec_ref(v_a_4014_);
lean_dec_ref(v_docCtx_4013_);
v_a_4075_ = lean_ctor_get(v___x_4074_, 0);
v_isSharedCheck_4082_ = !lean_is_exclusive(v___x_4074_);
if (v_isSharedCheck_4082_ == 0)
{
v___x_4077_ = v___x_4074_;
v_isShared_4078_ = v_isSharedCheck_4082_;
goto v_resetjp_4076_;
}
else
{
lean_inc(v_a_4075_);
lean_dec(v___x_4074_);
v___x_4077_ = lean_box(0);
v_isShared_4078_ = v_isSharedCheck_4082_;
goto v_resetjp_4076_;
}
v_resetjp_4076_:
{
lean_object* v___x_4080_; 
if (v_isShared_4078_ == 0)
{
v___x_4080_ = v___x_4077_;
goto v_reusejp_4079_;
}
else
{
lean_object* v_reuseFailAlloc_4081_; 
v_reuseFailAlloc_4081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4081_, 0, v_a_4075_);
v___x_4080_ = v_reuseFailAlloc_4081_;
goto v_reusejp_4079_;
}
v_reusejp_4079_:
{
return v___x_4080_;
}
}
}
}
else
{
lean_object* v_a_4083_; lean_object* v___x_4085_; uint8_t v_isShared_4086_; uint8_t v_isSharedCheck_4090_; 
lean_dec_ref(v___x_4044_);
lean_dec(v___x_4040_);
lean_dec_ref(v_snd_4015_);
lean_dec_ref(v_a_4014_);
lean_dec_ref(v_docCtx_4013_);
v_a_4083_ = lean_ctor_get(v___x_4069_, 0);
v_isSharedCheck_4090_ = !lean_is_exclusive(v___x_4069_);
if (v_isSharedCheck_4090_ == 0)
{
v___x_4085_ = v___x_4069_;
v_isShared_4086_ = v_isSharedCheck_4090_;
goto v_resetjp_4084_;
}
else
{
lean_inc(v_a_4083_);
lean_dec(v___x_4069_);
v___x_4085_ = lean_box(0);
v_isShared_4086_ = v_isSharedCheck_4090_;
goto v_resetjp_4084_;
}
v_resetjp_4084_:
{
lean_object* v___x_4088_; 
if (v_isShared_4086_ == 0)
{
v___x_4088_ = v___x_4085_;
goto v_reusejp_4087_;
}
else
{
lean_object* v_reuseFailAlloc_4089_; 
v_reuseFailAlloc_4089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4089_, 0, v_a_4083_);
v___x_4088_ = v_reuseFailAlloc_4089_;
goto v_reusejp_4087_;
}
v_reusejp_4087_:
{
return v___x_4088_;
}
}
}
}
else
{
lean_inc(v_a_4037_);
v_preDef_4046_ = v_a_4037_;
v___y_4047_ = v___y_4020_;
v___y_4048_ = v___y_4021_;
v___y_4049_ = v___y_4022_;
v___y_4050_ = v___y_4023_;
v___y_4051_ = v___y_4024_;
v___y_4052_ = v___y_4025_;
goto v___jp_4045_;
}
}
else
{
lean_object* v_a_4091_; lean_object* v___x_4093_; uint8_t v_isShared_4094_; uint8_t v_isSharedCheck_4098_; 
lean_dec_ref(v___x_4044_);
lean_dec(v___x_4040_);
lean_dec_ref(v_snd_4015_);
lean_dec_ref(v_a_4014_);
lean_dec_ref(v_docCtx_4013_);
v_a_4091_ = lean_ctor_get(v___x_4066_, 0);
v_isSharedCheck_4098_ = !lean_is_exclusive(v___x_4066_);
if (v_isSharedCheck_4098_ == 0)
{
v___x_4093_ = v___x_4066_;
v_isShared_4094_ = v_isSharedCheck_4098_;
goto v_resetjp_4092_;
}
else
{
lean_inc(v_a_4091_);
lean_dec(v___x_4066_);
v___x_4093_ = lean_box(0);
v_isShared_4094_ = v_isSharedCheck_4098_;
goto v_resetjp_4092_;
}
v_resetjp_4092_:
{
lean_object* v___x_4096_; 
if (v_isShared_4094_ == 0)
{
v___x_4096_ = v___x_4093_;
goto v_reusejp_4095_;
}
else
{
lean_object* v_reuseFailAlloc_4097_; 
v_reuseFailAlloc_4097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4097_, 0, v_a_4091_);
v___x_4096_ = v_reuseFailAlloc_4097_;
goto v_reusejp_4095_;
}
v_reusejp_4095_:
{
return v___x_4096_;
}
}
}
}
else
{
lean_inc(v_a_4037_);
v_preDef_4046_ = v_a_4037_;
v___y_4047_ = v___y_4020_;
v___y_4048_ = v___y_4021_;
v___y_4049_ = v___y_4022_;
v___y_4050_ = v___y_4023_;
v___y_4051_ = v___y_4024_;
v___y_4052_ = v___y_4025_;
goto v___jp_4045_;
}
v___jp_4045_:
{
lean_object* v___x_4053_; 
lean_inc_ref(v_docCtx_4013_);
v___x_4053_ = l_Lean_Elab_Structural_addSmartUnfoldingDef(v_docCtx_4013_, v_preDef_4046_, v___x_4040_, v___y_4047_, v___y_4048_, v___y_4049_, v___y_4050_, v___y_4051_, v___y_4052_);
if (lean_obj_tag(v___x_4053_) == 0)
{
size_t v___x_4054_; size_t v___x_4055_; 
lean_dec_ref_known(v___x_4053_, 1);
v___x_4054_ = ((size_t)1ULL);
v___x_4055_ = lean_usize_add(v_i_4018_, v___x_4054_);
v_i_4018_ = v___x_4055_;
v_b_4019_ = v___x_4044_;
goto _start;
}
else
{
lean_object* v_a_4057_; lean_object* v___x_4059_; uint8_t v_isShared_4060_; uint8_t v_isSharedCheck_4064_; 
lean_dec_ref(v___x_4044_);
lean_dec_ref(v_snd_4015_);
lean_dec_ref(v_a_4014_);
lean_dec_ref(v_docCtx_4013_);
v_a_4057_ = lean_ctor_get(v___x_4053_, 0);
v_isSharedCheck_4064_ = !lean_is_exclusive(v___x_4053_);
if (v_isSharedCheck_4064_ == 0)
{
v___x_4059_ = v___x_4053_;
v_isShared_4060_ = v_isSharedCheck_4064_;
goto v_resetjp_4058_;
}
else
{
lean_inc(v_a_4057_);
lean_dec(v___x_4053_);
v___x_4059_ = lean_box(0);
v_isShared_4060_ = v_isSharedCheck_4064_;
goto v_resetjp_4058_;
}
v_resetjp_4058_:
{
lean_object* v___x_4062_; 
if (v_isShared_4060_ == 0)
{
v___x_4062_ = v___x_4059_;
goto v_reusejp_4061_;
}
else
{
lean_object* v_reuseFailAlloc_4063_; 
v_reuseFailAlloc_4063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4063_, 0, v_a_4057_);
v___x_4062_ = v_reuseFailAlloc_4063_;
goto v_reusejp_4061_;
}
v_reusejp_4061_:
{
return v___x_4062_;
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_docCtx_4013_ = stack[0].m_obj;
lean_object* v_a_4014_ = stack[1].m_obj;
lean_object* v_snd_4015_ = stack[2].m_obj;
lean_object* v_as_4016_ = stack[3].m_obj;
size_t v_sz_4017_ = stack[4].m_num;
size_t v_i_4018_ = stack[5].m_num;
lean_object* v_b_4019_ = stack[6].m_obj;
lean_object* v___y_4020_ = stack[7].m_obj;
lean_object* v___y_4021_ = stack[8].m_obj;
lean_object* v___y_4022_ = stack[9].m_obj;
lean_object* v___y_4023_ = stack[10].m_obj;
lean_object* v___y_4024_ = stack[11].m_obj;
lean_object* v___y_4025_ = stack[12].m_obj;
lean_object* v_res_4104_;
v_res_4104_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__1(v_docCtx_4013_, v_a_4014_, v_snd_4015_, v_as_4016_, v_sz_4017_, v_i_4018_, v_b_4019_, v___y_4020_, v___y_4021_, v___y_4022_, v___y_4023_, v___y_4024_, v___y_4025_);
stack->m_obj
 = v_res_4104_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__1___boxed(lean_object* v_docCtx_4105_, lean_object* v_a_4106_, lean_object* v_snd_4107_, lean_object* v_as_4108_, lean_object* v_sz_4109_, lean_object* v_i_4110_, lean_object* v_b_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_){
_start:
{
size_t v_sz_boxed_4119_; size_t v_i_boxed_4120_; lean_object* v_res_4121_; 
v_sz_boxed_4119_ = lean_unbox_usize(v_sz_4109_);
lean_dec(v_sz_4109_);
v_i_boxed_4120_ = lean_unbox_usize(v_i_4110_);
lean_dec(v_i_4110_);
v_res_4121_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__1(v_docCtx_4105_, v_a_4106_, v_snd_4107_, v_as_4108_, v_sz_boxed_4119_, v_i_boxed_4120_, v_b_4111_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_, v___y_4117_);
lean_dec(v___y_4117_);
lean_dec_ref(v___y_4116_);
lean_dec(v___y_4115_);
lean_dec_ref(v___y_4114_);
lean_dec(v___y_4113_);
lean_dec_ref(v___y_4112_);
lean_dec_ref(v_as_4108_);
return v_res_4121_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___lam__0(lean_object* v___x_4122_, lean_object* v_e_4123_){
_start:
{
lean_object* v___x_4124_; lean_object* v___x_4125_; 
v___x_4124_ = l_Lean_indentD(v_e_4123_);
v___x_4125_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4125_, 0, v___x_4122_);
lean_ctor_set(v___x_4125_, 1, v___x_4124_);
return v___x_4125_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___lam__1(lean_object* v_docCtx_4126_, lean_object* v_a_4127_, uint8_t v___x_4128_, lean_object* v___x_4129_, uint8_t v___x_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_){
_start:
{
lean_object* v___x_4138_; 
v___x_4138_ = l_Lean_Elab_addNonRec(v_docCtx_4126_, v_a_4127_, v___x_4128_, v___x_4129_, v___x_4130_, v___x_4128_, v___x_4130_, v___x_4130_, v___y_4131_, v___y_4132_, v___y_4133_, v___y_4134_, v___y_4135_, v___y_4136_);
return v___x_4138_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_docCtx_4126_ = stack[0].m_obj;
lean_object* v_a_4127_ = stack[1].m_obj;
uint8_t v___x_4128_ = stack[2].m_num;
lean_object* v___x_4129_ = stack[3].m_obj;
uint8_t v___x_4130_ = stack[4].m_num;
lean_object* v___y_4131_ = stack[5].m_obj;
lean_object* v___y_4132_ = stack[6].m_obj;
lean_object* v___y_4133_ = stack[7].m_obj;
lean_object* v___y_4134_ = stack[8].m_obj;
lean_object* v___y_4135_ = stack[9].m_obj;
lean_object* v___y_4136_ = stack[10].m_obj;
lean_object* v_res_4139_;
v_res_4139_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___lam__1(v_docCtx_4126_, v_a_4127_, v___x_4128_, v___x_4129_, v___x_4130_, v___y_4131_, v___y_4132_, v___y_4133_, v___y_4134_, v___y_4135_, v___y_4136_);
stack->m_obj
 = v_res_4139_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___lam__1___boxed(lean_object* v_docCtx_4140_, lean_object* v_a_4141_, lean_object* v___x_4142_, lean_object* v___x_4143_, lean_object* v___x_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_){
_start:
{
uint8_t v___x_9299__boxed_4152_; uint8_t v___x_9301__boxed_4153_; lean_object* v_res_4154_; 
v___x_9299__boxed_4152_ = lean_unbox(v___x_4142_);
v___x_9301__boxed_4153_ = lean_unbox(v___x_4144_);
v_res_4154_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___lam__1(v_docCtx_4140_, v_a_4141_, v___x_9299__boxed_4152_, v___x_4143_, v___x_9301__boxed_4153_, v___y_4145_, v___y_4146_, v___y_4147_, v___y_4148_, v___y_4149_, v___y_4150_);
lean_dec(v___y_4150_);
lean_dec_ref(v___y_4149_);
lean_dec(v___y_4148_);
lean_dec_ref(v___y_4147_);
lean_dec(v___y_4146_);
lean_dec_ref(v___y_4145_);
return v_res_4154_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__1(void){
_start:
{
lean_object* v___x_4156_; lean_object* v___x_4157_; 
v___x_4156_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__0));
v___x_4157_ = l_Lean_stringToMessageData(v___x_4156_);
return v___x_4157_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__2(void){
_start:
{
lean_object* v___x_4158_; lean_object* v___f_4159_; 
v___x_4158_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__1);
v___f_4159_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___lam__0), 2, 1);
lean_closure_set(v___f_4159_, 0, v___x_4158_);
return v___f_4159_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5(lean_object* v_names_4160_, lean_object* v_docCtx_4161_, lean_object* v_as_4162_, size_t v_i_4163_, size_t v_stop_4164_, lean_object* v_b_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_){
_start:
{
uint8_t v___x_4173_; 
v___x_4173_ = lean_usize_dec_eq(v_i_4163_, v_stop_4164_);
if (v___x_4173_ == 0)
{
lean_object* v___x_4174_; lean_object* v___x_4175_; 
v___x_4174_ = lean_array_uget_borrowed(v_as_4162_, v_i_4163_);
lean_inc(v___x_4174_);
v___x_4175_ = l_Lean_Elab_eraseRecAppSyntax(v___x_4174_, v___y_4170_, v___y_4171_);
if (lean_obj_tag(v___x_4175_) == 0)
{
lean_object* v_a_4176_; lean_object* v___f_4177_; lean_object* v___x_4178_; uint8_t v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___f_4182_; lean_object* v___x_4183_; 
v_a_4176_ = lean_ctor_get(v___x_4175_, 0);
lean_inc(v_a_4176_);
lean_dec_ref_known(v___x_4175_, 1);
v___f_4177_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__2);
lean_inc_ref(v_names_4160_);
v___x_4178_ = lean_array_to_list(v_names_4160_);
v___x_4179_ = 1;
v___x_4180_ = lean_box(v___x_4173_);
v___x_4181_ = lean_box(v___x_4179_);
lean_inc(v___y_4167_);
lean_inc_ref(v___y_4166_);
lean_inc_ref(v_docCtx_4161_);
v___f_4182_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___lam__1___boxed), 12, 7);
lean_closure_set(v___f_4182_, 0, v_docCtx_4161_);
lean_closure_set(v___f_4182_, 1, v_a_4176_);
lean_closure_set(v___f_4182_, 2, v___x_4180_);
lean_closure_set(v___f_4182_, 3, v___x_4178_);
lean_closure_set(v___f_4182_, 4, v___x_4181_);
lean_closure_set(v___f_4182_, 5, v___y_4166_);
lean_closure_set(v___f_4182_, 6, v___y_4167_);
v___x_4183_ = l_Lean_Meta_mapErrorImp___redArg(v___f_4182_, v___f_4177_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_);
if (lean_obj_tag(v___x_4183_) == 0)
{
if (lean_obj_tag(v___x_4183_) == 0)
{
lean_object* v_a_4184_; size_t v___x_4185_; size_t v___x_4186_; 
v_a_4184_ = lean_ctor_get(v___x_4183_, 0);
lean_inc(v_a_4184_);
lean_dec_ref_known(v___x_4183_, 1);
v___x_4185_ = ((size_t)1ULL);
v___x_4186_ = lean_usize_add(v_i_4163_, v___x_4185_);
v_i_4163_ = v___x_4186_;
v_b_4165_ = v_a_4184_;
goto _start;
}
else
{
lean_dec_ref(v_docCtx_4161_);
lean_dec_ref(v_names_4160_);
return v___x_4183_;
}
}
else
{
lean_object* v_a_4188_; lean_object* v___x_4190_; uint8_t v_isShared_4191_; uint8_t v_isSharedCheck_4195_; 
lean_dec_ref(v_docCtx_4161_);
lean_dec_ref(v_names_4160_);
v_a_4188_ = lean_ctor_get(v___x_4183_, 0);
v_isSharedCheck_4195_ = !lean_is_exclusive(v___x_4183_);
if (v_isSharedCheck_4195_ == 0)
{
v___x_4190_ = v___x_4183_;
v_isShared_4191_ = v_isSharedCheck_4195_;
goto v_resetjp_4189_;
}
else
{
lean_inc(v_a_4188_);
lean_dec(v___x_4183_);
v___x_4190_ = lean_box(0);
v_isShared_4191_ = v_isSharedCheck_4195_;
goto v_resetjp_4189_;
}
v_resetjp_4189_:
{
lean_object* v___x_4193_; 
if (v_isShared_4191_ == 0)
{
v___x_4193_ = v___x_4190_;
goto v_reusejp_4192_;
}
else
{
lean_object* v_reuseFailAlloc_4194_; 
v_reuseFailAlloc_4194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4194_, 0, v_a_4188_);
v___x_4193_ = v_reuseFailAlloc_4194_;
goto v_reusejp_4192_;
}
v_reusejp_4192_:
{
return v___x_4193_;
}
}
}
}
else
{
lean_object* v_a_4196_; lean_object* v___x_4198_; uint8_t v_isShared_4199_; uint8_t v_isSharedCheck_4203_; 
lean_dec_ref(v_docCtx_4161_);
lean_dec_ref(v_names_4160_);
v_a_4196_ = lean_ctor_get(v___x_4175_, 0);
v_isSharedCheck_4203_ = !lean_is_exclusive(v___x_4175_);
if (v_isSharedCheck_4203_ == 0)
{
v___x_4198_ = v___x_4175_;
v_isShared_4199_ = v_isSharedCheck_4203_;
goto v_resetjp_4197_;
}
else
{
lean_inc(v_a_4196_);
lean_dec(v___x_4175_);
v___x_4198_ = lean_box(0);
v_isShared_4199_ = v_isSharedCheck_4203_;
goto v_resetjp_4197_;
}
v_resetjp_4197_:
{
lean_object* v___x_4201_; 
if (v_isShared_4199_ == 0)
{
v___x_4201_ = v___x_4198_;
goto v_reusejp_4200_;
}
else
{
lean_object* v_reuseFailAlloc_4202_; 
v_reuseFailAlloc_4202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4202_, 0, v_a_4196_);
v___x_4201_ = v_reuseFailAlloc_4202_;
goto v_reusejp_4200_;
}
v_reusejp_4200_:
{
return v___x_4201_;
}
}
}
}
else
{
lean_object* v___x_4204_; 
lean_dec_ref(v_docCtx_4161_);
lean_dec_ref(v_names_4160_);
v___x_4204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4204_, 0, v_b_4165_);
return v___x_4204_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_names_4160_ = stack[0].m_obj;
lean_object* v_docCtx_4161_ = stack[1].m_obj;
lean_object* v_as_4162_ = stack[2].m_obj;
size_t v_i_4163_ = stack[3].m_num;
size_t v_stop_4164_ = stack[4].m_num;
lean_object* v_b_4165_ = stack[5].m_obj;
lean_object* v___y_4166_ = stack[6].m_obj;
lean_object* v___y_4167_ = stack[7].m_obj;
lean_object* v___y_4168_ = stack[8].m_obj;
lean_object* v___y_4169_ = stack[9].m_obj;
lean_object* v___y_4170_ = stack[10].m_obj;
lean_object* v___y_4171_ = stack[11].m_obj;
lean_object* v_res_4205_;
v_res_4205_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5(v_names_4160_, v_docCtx_4161_, v_as_4162_, v_i_4163_, v_stop_4164_, v_b_4165_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_);
stack->m_obj
 = v_res_4205_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___boxed(lean_object* v_names_4206_, lean_object* v_docCtx_4207_, lean_object* v_as_4208_, lean_object* v_i_4209_, lean_object* v_stop_4210_, lean_object* v_b_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_){
_start:
{
size_t v_i_boxed_4219_; size_t v_stop_boxed_4220_; lean_object* v_res_4221_; 
v_i_boxed_4219_ = lean_unbox_usize(v_i_4209_);
lean_dec(v_i_4209_);
v_stop_boxed_4220_ = lean_unbox_usize(v_stop_4210_);
lean_dec(v_stop_4210_);
v_res_4221_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5(v_names_4206_, v_docCtx_4207_, v_as_4208_, v_i_boxed_4219_, v_stop_boxed_4220_, v_b_4211_, v___y_4212_, v___y_4213_, v___y_4214_, v___y_4215_, v___y_4216_, v___y_4217_);
lean_dec(v___y_4217_);
lean_dec_ref(v___y_4216_);
lean_dec(v___y_4215_);
lean_dec_ref(v___y_4214_);
lean_dec(v___y_4213_);
lean_dec_ref(v___y_4212_);
lean_dec_ref(v_as_4208_);
return v_res_4221_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4___redArg(lean_object* v_as_4222_, size_t v_sz_4223_, size_t v_i_4224_, lean_object* v_b_4225_, lean_object* v___y_4226_, lean_object* v___y_4227_, lean_object* v___y_4228_, lean_object* v___y_4229_){
_start:
{
uint8_t v___x_4231_; 
v___x_4231_ = lean_usize_dec_lt(v_i_4224_, v_sz_4223_);
if (v___x_4231_ == 0)
{
lean_object* v___x_4232_; 
v___x_4232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4232_, 0, v_b_4225_);
return v___x_4232_;
}
else
{
lean_object* v_array_4233_; lean_object* v_start_4234_; lean_object* v_stop_4235_; uint8_t v___x_4236_; 
v_array_4233_ = lean_ctor_get(v_b_4225_, 0);
v_start_4234_ = lean_ctor_get(v_b_4225_, 1);
v_stop_4235_ = lean_ctor_get(v_b_4225_, 2);
v___x_4236_ = lean_nat_dec_lt(v_start_4234_, v_stop_4235_);
if (v___x_4236_ == 0)
{
lean_object* v___x_4237_; 
v___x_4237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4237_, 0, v_b_4225_);
return v___x_4237_;
}
else
{
lean_object* v___x_4239_; uint8_t v_isShared_4240_; uint8_t v_isSharedCheck_4260_; 
lean_inc(v_stop_4235_);
lean_inc(v_start_4234_);
lean_inc_ref(v_array_4233_);
v_isSharedCheck_4260_ = !lean_is_exclusive(v_b_4225_);
if (v_isSharedCheck_4260_ == 0)
{
lean_object* v_unused_4261_; lean_object* v_unused_4262_; lean_object* v_unused_4263_; 
v_unused_4261_ = lean_ctor_get(v_b_4225_, 2);
lean_dec(v_unused_4261_);
v_unused_4262_ = lean_ctor_get(v_b_4225_, 1);
lean_dec(v_unused_4262_);
v_unused_4263_ = lean_ctor_get(v_b_4225_, 0);
lean_dec(v_unused_4263_);
v___x_4239_ = v_b_4225_;
v_isShared_4240_ = v_isSharedCheck_4260_;
goto v_resetjp_4238_;
}
else
{
lean_dec(v_b_4225_);
v___x_4239_ = lean_box(0);
v_isShared_4240_ = v_isSharedCheck_4260_;
goto v_resetjp_4238_;
}
v_resetjp_4238_:
{
lean_object* v_a_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4246_; 
v_a_4241_ = lean_array_uget_borrowed(v_as_4222_, v_i_4224_);
v___x_4242_ = lean_array_fget(v_array_4233_, v_start_4234_);
v___x_4243_ = lean_unsigned_to_nat(1u);
v___x_4244_ = lean_nat_add(v_start_4234_, v___x_4243_);
lean_dec(v_start_4234_);
if (v_isShared_4240_ == 0)
{
lean_ctor_set(v___x_4239_, 1, v___x_4244_);
v___x_4246_ = v___x_4239_;
goto v_reusejp_4245_;
}
else
{
lean_object* v_reuseFailAlloc_4259_; 
v_reuseFailAlloc_4259_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4259_, 0, v_array_4233_);
lean_ctor_set(v_reuseFailAlloc_4259_, 1, v___x_4244_);
lean_ctor_set(v_reuseFailAlloc_4259_, 2, v_stop_4235_);
v___x_4246_ = v_reuseFailAlloc_4259_;
goto v_reusejp_4245_;
}
v_reusejp_4245_:
{
lean_object* v___x_4247_; 
lean_inc(v_a_4241_);
v___x_4247_ = l_Lean_Elab_Structural_reportTermMeasure(v___x_4242_, v_a_4241_, v___y_4226_, v___y_4227_, v___y_4228_, v___y_4229_);
if (lean_obj_tag(v___x_4247_) == 0)
{
size_t v___x_4248_; size_t v___x_4249_; 
lean_dec_ref_known(v___x_4247_, 1);
v___x_4248_ = ((size_t)1ULL);
v___x_4249_ = lean_usize_add(v_i_4224_, v___x_4248_);
v_i_4224_ = v___x_4249_;
v_b_4225_ = v___x_4246_;
goto _start;
}
else
{
lean_object* v_a_4251_; lean_object* v___x_4253_; uint8_t v_isShared_4254_; uint8_t v_isSharedCheck_4258_; 
lean_dec_ref(v___x_4246_);
v_a_4251_ = lean_ctor_get(v___x_4247_, 0);
v_isSharedCheck_4258_ = !lean_is_exclusive(v___x_4247_);
if (v_isSharedCheck_4258_ == 0)
{
v___x_4253_ = v___x_4247_;
v_isShared_4254_ = v_isSharedCheck_4258_;
goto v_resetjp_4252_;
}
else
{
lean_inc(v_a_4251_);
lean_dec(v___x_4247_);
v___x_4253_ = lean_box(0);
v_isShared_4254_ = v_isSharedCheck_4258_;
goto v_resetjp_4252_;
}
v_resetjp_4252_:
{
lean_object* v___x_4256_; 
if (v_isShared_4254_ == 0)
{
v___x_4256_ = v___x_4253_;
goto v_reusejp_4255_;
}
else
{
lean_object* v_reuseFailAlloc_4257_; 
v_reuseFailAlloc_4257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4257_, 0, v_a_4251_);
v___x_4256_ = v_reuseFailAlloc_4257_;
goto v_reusejp_4255_;
}
v_reusejp_4255_:
{
return v___x_4256_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_4222_ = stack[0].m_obj;
size_t v_sz_4223_ = stack[1].m_num;
size_t v_i_4224_ = stack[2].m_num;
lean_object* v_b_4225_ = stack[3].m_obj;
lean_object* v___y_4226_ = stack[4].m_obj;
lean_object* v___y_4227_ = stack[5].m_obj;
lean_object* v___y_4228_ = stack[6].m_obj;
lean_object* v___y_4229_ = stack[7].m_obj;
lean_object* v_res_4264_;
v_res_4264_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4___redArg(v_as_4222_, v_sz_4223_, v_i_4224_, v_b_4225_, v___y_4226_, v___y_4227_, v___y_4228_, v___y_4229_);
stack->m_obj
 = v_res_4264_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4___redArg___boxed(lean_object* v_as_4265_, lean_object* v_sz_4266_, lean_object* v_i_4267_, lean_object* v_b_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_, lean_object* v___y_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_){
_start:
{
size_t v_sz_boxed_4274_; size_t v_i_boxed_4275_; lean_object* v_res_4276_; 
v_sz_boxed_4274_ = lean_unbox_usize(v_sz_4266_);
lean_dec(v_sz_4266_);
v_i_boxed_4275_ = lean_unbox_usize(v_i_4267_);
lean_dec(v_i_4267_);
v_res_4276_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4___redArg(v_as_4265_, v_sz_boxed_4274_, v_i_boxed_4275_, v_b_4268_, v___y_4269_, v___y_4270_, v___y_4271_, v___y_4272_);
lean_dec(v___y_4272_);
lean_dec_ref(v___y_4271_);
lean_dec(v___y_4270_);
lean_dec_ref(v___y_4269_);
lean_dec_ref(v_as_4265_);
return v_res_4276_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___redArg(size_t v_sz_4277_, size_t v_i_4278_, lean_object* v_bs_4279_, lean_object* v___y_4280_, lean_object* v___y_4281_){
_start:
{
uint8_t v___x_4283_; 
v___x_4283_ = lean_usize_dec_lt(v_i_4278_, v_sz_4277_);
if (v___x_4283_ == 0)
{
lean_object* v___x_4284_; 
v___x_4284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4284_, 0, v_bs_4279_);
return v___x_4284_;
}
else
{
lean_object* v_v_4285_; lean_object* v___x_4286_; lean_object* v_bs_x27_4287_; lean_object* v___x_4288_; 
v_v_4285_ = lean_array_uget(v_bs_4279_, v_i_4278_);
v___x_4286_ = lean_unsigned_to_nat(0u);
v_bs_x27_4287_ = lean_array_uset(v_bs_4279_, v_i_4278_, v___x_4286_);
v___x_4288_ = l_Lean_Elab_eraseRecAppSyntax(v_v_4285_, v___y_4280_, v___y_4281_);
if (lean_obj_tag(v___x_4288_) == 0)
{
lean_object* v_a_4289_; size_t v___x_4290_; size_t v___x_4291_; lean_object* v___x_4292_; 
v_a_4289_ = lean_ctor_get(v___x_4288_, 0);
lean_inc(v_a_4289_);
lean_dec_ref_known(v___x_4288_, 1);
v___x_4290_ = ((size_t)1ULL);
v___x_4291_ = lean_usize_add(v_i_4278_, v___x_4290_);
v___x_4292_ = lean_array_uset(v_bs_x27_4287_, v_i_4278_, v_a_4289_);
v_i_4278_ = v___x_4291_;
v_bs_4279_ = v___x_4292_;
goto _start;
}
else
{
lean_object* v_a_4294_; lean_object* v___x_4296_; uint8_t v_isShared_4297_; uint8_t v_isSharedCheck_4301_; 
lean_dec_ref(v_bs_x27_4287_);
v_a_4294_ = lean_ctor_get(v___x_4288_, 0);
v_isSharedCheck_4301_ = !lean_is_exclusive(v___x_4288_);
if (v_isSharedCheck_4301_ == 0)
{
v___x_4296_ = v___x_4288_;
v_isShared_4297_ = v_isSharedCheck_4301_;
goto v_resetjp_4295_;
}
else
{
lean_inc(v_a_4294_);
lean_dec(v___x_4288_);
v___x_4296_ = lean_box(0);
v_isShared_4297_ = v_isSharedCheck_4301_;
goto v_resetjp_4295_;
}
v_resetjp_4295_:
{
lean_object* v___x_4299_; 
if (v_isShared_4297_ == 0)
{
v___x_4299_ = v___x_4296_;
goto v_reusejp_4298_;
}
else
{
lean_object* v_reuseFailAlloc_4300_; 
v_reuseFailAlloc_4300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4300_, 0, v_a_4294_);
v___x_4299_ = v_reuseFailAlloc_4300_;
goto v_reusejp_4298_;
}
v_reusejp_4298_:
{
return v___x_4299_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_sz_4277_ = stack[0].m_num;
size_t v_i_4278_ = stack[1].m_num;
lean_object* v_bs_4279_ = stack[2].m_obj;
lean_object* v___y_4280_ = stack[3].m_obj;
lean_object* v___y_4281_ = stack[4].m_obj;
lean_object* v_res_4302_;
v_res_4302_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___redArg(v_sz_4277_, v_i_4278_, v_bs_4279_, v___y_4280_, v___y_4281_);
stack->m_obj
 = v_res_4302_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___redArg___boxed(lean_object* v_sz_4303_, lean_object* v_i_4304_, lean_object* v_bs_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_, lean_object* v___y_4308_){
_start:
{
size_t v_sz_boxed_4309_; size_t v_i_boxed_4310_; lean_object* v_res_4311_; 
v_sz_boxed_4309_ = lean_unbox_usize(v_sz_4303_);
lean_dec(v_sz_4303_);
v_i_boxed_4310_ = lean_unbox_usize(v_i_4304_);
lean_dec(v_i_4304_);
v_res_4311_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___redArg(v_sz_boxed_4309_, v_i_boxed_4310_, v_bs_4305_, v___y_4306_, v___y_4307_);
lean_dec(v___y_4307_);
lean_dec_ref(v___y_4306_);
return v_res_4311_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___redArg(lean_object* v_as_4312_, size_t v_sz_4313_, size_t v_i_4314_, lean_object* v_b_4315_, lean_object* v___y_4316_, lean_object* v___y_4317_){
_start:
{
uint8_t v___x_4319_; 
v___x_4319_ = lean_usize_dec_lt(v_i_4314_, v_sz_4313_);
if (v___x_4319_ == 0)
{
lean_object* v___x_4320_; 
v___x_4320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4320_, 0, v_b_4315_);
return v___x_4320_;
}
else
{
lean_object* v_a_4321_; lean_object* v_declName_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; 
v_a_4321_ = lean_array_uget_borrowed(v_as_4312_, v_i_4314_);
v_declName_4322_ = lean_ctor_get(v_a_4321_, 3);
v___x_4323_ = lean_box(0);
lean_inc(v_declName_4322_);
v___x_4324_ = l_Lean_enableRealizationsForConst(v_declName_4322_, v___y_4316_, v___y_4317_);
if (lean_obj_tag(v___x_4324_) == 0)
{
size_t v___x_4325_; size_t v___x_4326_; 
lean_dec_ref_known(v___x_4324_, 1);
v___x_4325_ = ((size_t)1ULL);
v___x_4326_ = lean_usize_add(v_i_4314_, v___x_4325_);
v_i_4314_ = v___x_4326_;
v_b_4315_ = v___x_4323_;
goto _start;
}
else
{
return v___x_4324_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_4312_ = stack[0].m_obj;
size_t v_sz_4313_ = stack[1].m_num;
size_t v_i_4314_ = stack[2].m_num;
lean_object* v_b_4315_ = stack[3].m_obj;
lean_object* v___y_4316_ = stack[4].m_obj;
lean_object* v___y_4317_ = stack[5].m_obj;
lean_object* v_res_4328_;
v_res_4328_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___redArg(v_as_4312_, v_sz_4313_, v_i_4314_, v_b_4315_, v___y_4316_, v___y_4317_);
stack->m_obj
 = v_res_4328_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___redArg___boxed(lean_object* v_as_4329_, lean_object* v_sz_4330_, lean_object* v_i_4331_, lean_object* v_b_4332_, lean_object* v___y_4333_, lean_object* v___y_4334_, lean_object* v___y_4335_){
_start:
{
size_t v_sz_boxed_4336_; size_t v_i_boxed_4337_; lean_object* v_res_4338_; 
v_sz_boxed_4336_ = lean_unbox_usize(v_sz_4330_);
lean_dec(v_sz_4330_);
v_i_boxed_4337_ = lean_unbox_usize(v_i_4331_);
lean_dec(v_i_4331_);
v_res_4338_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___redArg(v_as_4329_, v_sz_boxed_4336_, v_i_boxed_4337_, v_b_4332_, v___y_4333_, v___y_4334_);
lean_dec(v___y_4334_);
lean_dec_ref(v___y_4333_);
lean_dec_ref(v_as_4329_);
return v_res_4338_;
}
}
lean_object* l_Lean_Elab_Structural_structuralRecursion(lean_object* v_docCtx_4339_, lean_object* v_preDefs_4340_, lean_object* v_termMeasure_x3fs_4341_, lean_object* v_a_4342_, lean_object* v_a_4343_, lean_object* v_a_4344_, lean_object* v_a_4345_, lean_object* v_a_4346_, lean_object* v_a_4347_){
_start:
{
size_t v_sz_4349_; size_t v___x_4350_; lean_object* v_names_4351_; lean_object* v___x_4352_; 
v_sz_4349_ = lean_array_size(v_preDefs_4340_);
v___x_4350_ = ((size_t)0ULL);
lean_inc_ref_n(v_preDefs_4340_, 2);
v_names_4351_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0(v_sz_4349_, v___x_4350_, v_preDefs_4340_);
v___x_4352_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos(v_preDefs_4340_, v_termMeasure_x3fs_4341_, v_a_4344_, v_a_4345_, v_a_4346_, v_a_4347_);
if (lean_obj_tag(v___x_4352_) == 0)
{
lean_object* v_a_4353_; lean_object* v_snd_4354_; lean_object* v_fst_4355_; lean_object* v_fst_4356_; lean_object* v_snd_4357_; lean_object* v___y_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; size_t v_sz_4393_; lean_object* v___x_4394_; 
v_a_4353_ = lean_ctor_get(v___x_4352_, 0);
lean_inc(v_a_4353_);
lean_dec_ref_known(v___x_4352_, 1);
v_snd_4354_ = lean_ctor_get(v_a_4353_, 1);
lean_inc(v_snd_4354_);
v_fst_4355_ = lean_ctor_get(v_a_4353_, 0);
lean_inc(v_fst_4355_);
lean_dec(v_a_4353_);
v_fst_4356_ = lean_ctor_get(v_snd_4354_, 0);
lean_inc(v_fst_4356_);
v_snd_4357_ = lean_ctor_get(v_snd_4354_, 1);
lean_inc(v_snd_4357_);
lean_dec(v_snd_4354_);
v___x_4390_ = lean_unsigned_to_nat(0u);
v___x_4391_ = lean_array_get_size(v_preDefs_4340_);
lean_inc_ref(v_preDefs_4340_);
v___x_4392_ = l_Array_toSubarray___redArg(v_preDefs_4340_, v___x_4390_, v___x_4391_);
v_sz_4393_ = lean_array_size(v_fst_4355_);
v___x_4394_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4___redArg(v_fst_4355_, v_sz_4393_, v___x_4350_, v___x_4392_, v_a_4344_, v_a_4345_, v_a_4346_, v_a_4347_);
if (lean_obj_tag(v___x_4394_) == 0)
{
lean_object* v___x_4395_; uint8_t v___x_4396_; 
lean_dec_ref_known(v___x_4394_, 1);
v___x_4395_ = lean_array_get_size(v_fst_4356_);
v___x_4396_ = lean_nat_dec_lt(v___x_4390_, v___x_4395_);
if (v___x_4396_ == 0)
{
lean_dec_ref(v_names_4351_);
goto v___jp_4358_;
}
else
{
lean_object* v___x_4397_; uint8_t v___x_4398_; 
v___x_4397_ = lean_box(0);
v___x_4398_ = lean_nat_dec_le(v___x_4395_, v___x_4395_);
if (v___x_4398_ == 0)
{
if (v___x_4396_ == 0)
{
lean_dec_ref(v_names_4351_);
goto v___jp_4358_;
}
else
{
size_t v___x_4399_; lean_object* v___x_4400_; 
v___x_4399_ = lean_usize_of_nat(v___x_4395_);
lean_inc_ref(v_docCtx_4339_);
v___x_4400_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5(v_names_4351_, v_docCtx_4339_, v_fst_4356_, v___x_4350_, v___x_4399_, v___x_4397_, v_a_4342_, v_a_4343_, v_a_4344_, v_a_4345_, v_a_4346_, v_a_4347_);
v___y_4389_ = v___x_4400_;
goto v___jp_4388_;
}
}
else
{
size_t v___x_4401_; lean_object* v___x_4402_; 
v___x_4401_ = lean_usize_of_nat(v___x_4395_);
lean_inc_ref(v_docCtx_4339_);
v___x_4402_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5(v_names_4351_, v_docCtx_4339_, v_fst_4356_, v___x_4350_, v___x_4401_, v___x_4397_, v_a_4342_, v_a_4343_, v_a_4344_, v_a_4345_, v_a_4346_, v_a_4347_);
v___y_4389_ = v___x_4402_;
goto v___jp_4388_;
}
}
}
else
{
lean_object* v_a_4403_; lean_object* v___x_4405_; uint8_t v_isShared_4406_; uint8_t v_isSharedCheck_4410_; 
lean_dec(v_snd_4357_);
lean_dec(v_fst_4356_);
lean_dec(v_fst_4355_);
lean_dec_ref(v_names_4351_);
lean_dec_ref(v_preDefs_4340_);
lean_dec_ref(v_docCtx_4339_);
v_a_4403_ = lean_ctor_get(v___x_4394_, 0);
v_isSharedCheck_4410_ = !lean_is_exclusive(v___x_4394_);
if (v_isSharedCheck_4410_ == 0)
{
v___x_4405_ = v___x_4394_;
v_isShared_4406_ = v_isSharedCheck_4410_;
goto v_resetjp_4404_;
}
else
{
lean_inc(v_a_4403_);
lean_dec(v___x_4394_);
v___x_4405_ = lean_box(0);
v_isShared_4406_ = v_isSharedCheck_4410_;
goto v_resetjp_4404_;
}
v_resetjp_4404_:
{
lean_object* v___x_4408_; 
if (v_isShared_4406_ == 0)
{
v___x_4408_ = v___x_4405_;
goto v_reusejp_4407_;
}
else
{
lean_object* v_reuseFailAlloc_4409_; 
v_reuseFailAlloc_4409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4409_, 0, v_a_4403_);
v___x_4408_ = v_reuseFailAlloc_4409_;
goto v_reusejp_4407_;
}
v_reusejp_4407_:
{
return v___x_4408_;
}
}
}
v___jp_4358_:
{
lean_object* v___x_4359_; 
v___x_4359_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___redArg(v_sz_4349_, v___x_4350_, v_preDefs_4340_, v_a_4346_, v_a_4347_);
if (lean_obj_tag(v___x_4359_) == 0)
{
lean_object* v_a_4360_; lean_object* v___x_4361_; 
v_a_4360_ = lean_ctor_get(v___x_4359_, 0);
lean_inc_n(v_a_4360_, 2);
lean_dec_ref_known(v___x_4359_, 1);
lean_inc_ref(v_docCtx_4339_);
v___x_4361_ = l_Lean_Elab_addAndCompilePartialRec(v_docCtx_4339_, v_a_4360_, v_a_4342_, v_a_4343_, v_a_4344_, v_a_4345_, v_a_4346_, v_a_4347_);
if (lean_obj_tag(v___x_4361_) == 0)
{
lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; size_t v_sz_4365_; lean_object* v___x_4366_; 
lean_dec_ref_known(v___x_4361_, 1);
v___x_4362_ = lean_unsigned_to_nat(0u);
v___x_4363_ = lean_array_get_size(v_fst_4355_);
v___x_4364_ = l_Array_toSubarray___redArg(v_fst_4355_, v___x_4362_, v___x_4363_);
v_sz_4365_ = lean_array_size(v_a_4360_);
lean_inc(v_a_4360_);
v___x_4366_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__1(v_docCtx_4339_, v_a_4360_, v_snd_4357_, v_a_4360_, v_sz_4365_, v___x_4350_, v___x_4364_, v_a_4342_, v_a_4343_, v_a_4344_, v_a_4345_, v_a_4346_, v_a_4347_);
if (lean_obj_tag(v___x_4366_) == 0)
{
lean_object* v___x_4367_; lean_object* v___x_4368_; 
lean_dec_ref_known(v___x_4366_, 1);
v___x_4367_ = lean_box(0);
v___x_4368_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___redArg(v_a_4360_, v_sz_4365_, v___x_4350_, v___x_4367_, v_a_4344_, v_a_4345_, v_a_4346_, v_a_4347_);
if (lean_obj_tag(v___x_4368_) == 0)
{
lean_object* v___x_4369_; 
lean_dec_ref_known(v___x_4368_, 1);
v___x_4369_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___redArg(v_a_4360_, v_sz_4365_, v___x_4350_, v___x_4367_, v_a_4346_, v_a_4347_);
lean_dec(v_a_4360_);
if (lean_obj_tag(v___x_4369_) == 0)
{
uint8_t v___x_4370_; lean_object* v___x_4371_; 
lean_dec_ref_known(v___x_4369_, 1);
v___x_4370_ = 1;
v___x_4371_ = l_Lean_Elab_applyAttributesOf(v_fst_4356_, v___x_4370_, v_a_4342_, v_a_4343_, v_a_4344_, v_a_4345_, v_a_4346_, v_a_4347_);
lean_dec(v_fst_4356_);
return v___x_4371_;
}
else
{
lean_dec(v_fst_4356_);
return v___x_4369_;
}
}
else
{
lean_dec(v_a_4360_);
lean_dec(v_fst_4356_);
return v___x_4368_;
}
}
else
{
lean_object* v_a_4372_; lean_object* v___x_4374_; uint8_t v_isShared_4375_; uint8_t v_isSharedCheck_4379_; 
lean_dec(v_a_4360_);
lean_dec(v_fst_4356_);
v_a_4372_ = lean_ctor_get(v___x_4366_, 0);
v_isSharedCheck_4379_ = !lean_is_exclusive(v___x_4366_);
if (v_isSharedCheck_4379_ == 0)
{
v___x_4374_ = v___x_4366_;
v_isShared_4375_ = v_isSharedCheck_4379_;
goto v_resetjp_4373_;
}
else
{
lean_inc(v_a_4372_);
lean_dec(v___x_4366_);
v___x_4374_ = lean_box(0);
v_isShared_4375_ = v_isSharedCheck_4379_;
goto v_resetjp_4373_;
}
v_resetjp_4373_:
{
lean_object* v___x_4377_; 
if (v_isShared_4375_ == 0)
{
v___x_4377_ = v___x_4374_;
goto v_reusejp_4376_;
}
else
{
lean_object* v_reuseFailAlloc_4378_; 
v_reuseFailAlloc_4378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4378_, 0, v_a_4372_);
v___x_4377_ = v_reuseFailAlloc_4378_;
goto v_reusejp_4376_;
}
v_reusejp_4376_:
{
return v___x_4377_;
}
}
}
}
else
{
lean_dec(v_a_4360_);
lean_dec(v_snd_4357_);
lean_dec(v_fst_4356_);
lean_dec(v_fst_4355_);
lean_dec_ref(v_docCtx_4339_);
return v___x_4361_;
}
}
else
{
lean_object* v_a_4380_; lean_object* v___x_4382_; uint8_t v_isShared_4383_; uint8_t v_isSharedCheck_4387_; 
lean_dec(v_snd_4357_);
lean_dec(v_fst_4356_);
lean_dec(v_fst_4355_);
lean_dec_ref(v_docCtx_4339_);
v_a_4380_ = lean_ctor_get(v___x_4359_, 0);
v_isSharedCheck_4387_ = !lean_is_exclusive(v___x_4359_);
if (v_isSharedCheck_4387_ == 0)
{
v___x_4382_ = v___x_4359_;
v_isShared_4383_ = v_isSharedCheck_4387_;
goto v_resetjp_4381_;
}
else
{
lean_inc(v_a_4380_);
lean_dec(v___x_4359_);
v___x_4382_ = lean_box(0);
v_isShared_4383_ = v_isSharedCheck_4387_;
goto v_resetjp_4381_;
}
v_resetjp_4381_:
{
lean_object* v___x_4385_; 
if (v_isShared_4383_ == 0)
{
v___x_4385_ = v___x_4382_;
goto v_reusejp_4384_;
}
else
{
lean_object* v_reuseFailAlloc_4386_; 
v_reuseFailAlloc_4386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4386_, 0, v_a_4380_);
v___x_4385_ = v_reuseFailAlloc_4386_;
goto v_reusejp_4384_;
}
v_reusejp_4384_:
{
return v___x_4385_;
}
}
}
}
v___jp_4388_:
{
if (lean_obj_tag(v___y_4389_) == 0)
{
lean_dec_ref_known(v___y_4389_, 1);
goto v___jp_4358_;
}
else
{
lean_dec(v_snd_4357_);
lean_dec(v_fst_4356_);
lean_dec(v_fst_4355_);
lean_dec_ref(v_preDefs_4340_);
lean_dec_ref(v_docCtx_4339_);
return v___y_4389_;
}
}
}
else
{
lean_object* v_a_4411_; lean_object* v___x_4413_; uint8_t v_isShared_4414_; uint8_t v_isSharedCheck_4418_; 
lean_dec_ref(v_names_4351_);
lean_dec_ref(v_preDefs_4340_);
lean_dec_ref(v_docCtx_4339_);
v_a_4411_ = lean_ctor_get(v___x_4352_, 0);
v_isSharedCheck_4418_ = !lean_is_exclusive(v___x_4352_);
if (v_isSharedCheck_4418_ == 0)
{
v___x_4413_ = v___x_4352_;
v_isShared_4414_ = v_isSharedCheck_4418_;
goto v_resetjp_4412_;
}
else
{
lean_inc(v_a_4411_);
lean_dec(v___x_4352_);
v___x_4413_ = lean_box(0);
v_isShared_4414_ = v_isSharedCheck_4418_;
goto v_resetjp_4412_;
}
v_resetjp_4412_:
{
lean_object* v___x_4416_; 
if (v_isShared_4414_ == 0)
{
v___x_4416_ = v___x_4413_;
goto v_reusejp_4415_;
}
else
{
lean_object* v_reuseFailAlloc_4417_; 
v_reuseFailAlloc_4417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4417_, 0, v_a_4411_);
v___x_4416_ = v_reuseFailAlloc_4417_;
goto v_reusejp_4415_;
}
v_reusejp_4415_:
{
return v___x_4416_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Structural_structuralRecursion_0interp(lean_interpreter_value* stack)
{
lean_object* v_docCtx_4339_ = stack[0].m_obj;
lean_object* v_preDefs_4340_ = stack[1].m_obj;
lean_object* v_termMeasure_x3fs_4341_ = stack[2].m_obj;
lean_object* v_a_4342_ = stack[3].m_obj;
lean_object* v_a_4343_ = stack[4].m_obj;
lean_object* v_a_4344_ = stack[5].m_obj;
lean_object* v_a_4345_ = stack[6].m_obj;
lean_object* v_a_4346_ = stack[7].m_obj;
lean_object* v_a_4347_ = stack[8].m_obj;
lean_object* v_res_4419_;
v_res_4419_ = l_Lean_Elab_Structural_structuralRecursion(v_docCtx_4339_, v_preDefs_4340_, v_termMeasure_x3fs_4341_, v_a_4342_, v_a_4343_, v_a_4344_, v_a_4345_, v_a_4346_, v_a_4347_);
stack->m_obj
 = v_res_4419_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_structuralRecursion___boxed(lean_object* v_docCtx_4420_, lean_object* v_preDefs_4421_, lean_object* v_termMeasure_x3fs_4422_, lean_object* v_a_4423_, lean_object* v_a_4424_, lean_object* v_a_4425_, lean_object* v_a_4426_, lean_object* v_a_4427_, lean_object* v_a_4428_, lean_object* v_a_4429_){
_start:
{
lean_object* v_res_4430_; 
v_res_4430_ = l_Lean_Elab_Structural_structuralRecursion(v_docCtx_4420_, v_preDefs_4421_, v_termMeasure_x3fs_4422_, v_a_4423_, v_a_4424_, v_a_4425_, v_a_4426_, v_a_4427_, v_a_4428_);
lean_dec(v_a_4428_);
lean_dec_ref(v_a_4427_);
lean_dec(v_a_4426_);
lean_dec_ref(v_a_4425_);
lean_dec(v_a_4424_);
lean_dec_ref(v_a_4423_);
return v_res_4430_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0(size_t v_sz_4431_, size_t v_i_4432_, lean_object* v_bs_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_){
_start:
{
lean_object* v___x_4441_; 
v___x_4441_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___redArg(v_sz_4431_, v_i_4432_, v_bs_4433_, v___y_4438_, v___y_4439_);
return v___x_4441_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_4431_ = stack[0].m_num;
size_t v_i_4432_ = stack[1].m_num;
lean_object* v_bs_4433_ = stack[2].m_obj;
lean_object* v___y_4434_ = stack[3].m_obj;
lean_object* v___y_4435_ = stack[4].m_obj;
lean_object* v___y_4436_ = stack[5].m_obj;
lean_object* v___y_4437_ = stack[6].m_obj;
lean_object* v___y_4438_ = stack[7].m_obj;
lean_object* v___y_4439_ = stack[8].m_obj;
lean_object* v_res_4442_;
v_res_4442_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0(v_sz_4431_, v_i_4432_, v_bs_4433_, v___y_4434_, v___y_4435_, v___y_4436_, v___y_4437_, v___y_4438_, v___y_4439_);
stack->m_obj
 = v_res_4442_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___boxed(lean_object* v_sz_4443_, lean_object* v_i_4444_, lean_object* v_bs_4445_, lean_object* v___y_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_, lean_object* v___y_4452_){
_start:
{
size_t v_sz_boxed_4453_; size_t v_i_boxed_4454_; lean_object* v_res_4455_; 
v_sz_boxed_4453_ = lean_unbox_usize(v_sz_4443_);
lean_dec(v_sz_4443_);
v_i_boxed_4454_ = lean_unbox_usize(v_i_4444_);
lean_dec(v_i_4444_);
v_res_4455_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0(v_sz_boxed_4453_, v_i_boxed_4454_, v_bs_4445_, v___y_4446_, v___y_4447_, v___y_4448_, v___y_4449_, v___y_4450_, v___y_4451_);
lean_dec(v___y_4451_);
lean_dec_ref(v___y_4450_);
lean_dec(v___y_4449_);
lean_dec_ref(v___y_4448_);
lean_dec(v___y_4447_);
lean_dec_ref(v___y_4446_);
return v_res_4455_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2(lean_object* v_as_4456_, size_t v_sz_4457_, size_t v_i_4458_, lean_object* v_b_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_, lean_object* v___y_4463_, lean_object* v___y_4464_, lean_object* v___y_4465_){
_start:
{
lean_object* v___x_4467_; 
v___x_4467_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___redArg(v_as_4456_, v_sz_4457_, v_i_4458_, v_b_4459_, v___y_4462_, v___y_4463_, v___y_4464_, v___y_4465_);
return v___x_4467_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_4456_ = stack[0].m_obj;
size_t v_sz_4457_ = stack[1].m_num;
size_t v_i_4458_ = stack[2].m_num;
lean_object* v_b_4459_ = stack[3].m_obj;
lean_object* v___y_4460_ = stack[4].m_obj;
lean_object* v___y_4461_ = stack[5].m_obj;
lean_object* v___y_4462_ = stack[6].m_obj;
lean_object* v___y_4463_ = stack[7].m_obj;
lean_object* v___y_4464_ = stack[8].m_obj;
lean_object* v___y_4465_ = stack[9].m_obj;
lean_object* v_res_4468_;
v_res_4468_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2(v_as_4456_, v_sz_4457_, v_i_4458_, v_b_4459_, v___y_4460_, v___y_4461_, v___y_4462_, v___y_4463_, v___y_4464_, v___y_4465_);
stack->m_obj
 = v_res_4468_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___boxed(lean_object* v_as_4469_, lean_object* v_sz_4470_, lean_object* v_i_4471_, lean_object* v_b_4472_, lean_object* v___y_4473_, lean_object* v___y_4474_, lean_object* v___y_4475_, lean_object* v___y_4476_, lean_object* v___y_4477_, lean_object* v___y_4478_, lean_object* v___y_4479_){
_start:
{
size_t v_sz_boxed_4480_; size_t v_i_boxed_4481_; lean_object* v_res_4482_; 
v_sz_boxed_4480_ = lean_unbox_usize(v_sz_4470_);
lean_dec(v_sz_4470_);
v_i_boxed_4481_ = lean_unbox_usize(v_i_4471_);
lean_dec(v_i_4471_);
v_res_4482_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2(v_as_4469_, v_sz_boxed_4480_, v_i_boxed_4481_, v_b_4472_, v___y_4473_, v___y_4474_, v___y_4475_, v___y_4476_, v___y_4477_, v___y_4478_);
lean_dec(v___y_4478_);
lean_dec_ref(v___y_4477_);
lean_dec(v___y_4476_);
lean_dec_ref(v___y_4475_);
lean_dec(v___y_4474_);
lean_dec_ref(v___y_4473_);
lean_dec_ref(v_as_4469_);
return v_res_4482_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3(lean_object* v_as_4483_, size_t v_sz_4484_, size_t v_i_4485_, lean_object* v_b_4486_, lean_object* v___y_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_, lean_object* v___y_4492_){
_start:
{
lean_object* v___x_4494_; 
v___x_4494_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___redArg(v_as_4483_, v_sz_4484_, v_i_4485_, v_b_4486_, v___y_4491_, v___y_4492_);
return v___x_4494_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_4483_ = stack[0].m_obj;
size_t v_sz_4484_ = stack[1].m_num;
size_t v_i_4485_ = stack[2].m_num;
lean_object* v_b_4486_ = stack[3].m_obj;
lean_object* v___y_4487_ = stack[4].m_obj;
lean_object* v___y_4488_ = stack[5].m_obj;
lean_object* v___y_4489_ = stack[6].m_obj;
lean_object* v___y_4490_ = stack[7].m_obj;
lean_object* v___y_4491_ = stack[8].m_obj;
lean_object* v___y_4492_ = stack[9].m_obj;
lean_object* v_res_4495_;
v_res_4495_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3(v_as_4483_, v_sz_4484_, v_i_4485_, v_b_4486_, v___y_4487_, v___y_4488_, v___y_4489_, v___y_4490_, v___y_4491_, v___y_4492_);
stack->m_obj
 = v_res_4495_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___boxed(lean_object* v_as_4496_, lean_object* v_sz_4497_, lean_object* v_i_4498_, lean_object* v_b_4499_, lean_object* v___y_4500_, lean_object* v___y_4501_, lean_object* v___y_4502_, lean_object* v___y_4503_, lean_object* v___y_4504_, lean_object* v___y_4505_, lean_object* v___y_4506_){
_start:
{
size_t v_sz_boxed_4507_; size_t v_i_boxed_4508_; lean_object* v_res_4509_; 
v_sz_boxed_4507_ = lean_unbox_usize(v_sz_4497_);
lean_dec(v_sz_4497_);
v_i_boxed_4508_ = lean_unbox_usize(v_i_4498_);
lean_dec(v_i_4498_);
v_res_4509_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3(v_as_4496_, v_sz_boxed_4507_, v_i_boxed_4508_, v_b_4499_, v___y_4500_, v___y_4501_, v___y_4502_, v___y_4503_, v___y_4504_, v___y_4505_);
lean_dec(v___y_4505_);
lean_dec_ref(v___y_4504_);
lean_dec(v___y_4503_);
lean_dec_ref(v___y_4502_);
lean_dec(v___y_4501_);
lean_dec_ref(v___y_4500_);
lean_dec_ref(v_as_4496_);
return v_res_4509_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4(lean_object* v_as_4510_, size_t v_sz_4511_, size_t v_i_4512_, lean_object* v_b_4513_, lean_object* v___y_4514_, lean_object* v___y_4515_, lean_object* v___y_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_){
_start:
{
lean_object* v___x_4521_; 
v___x_4521_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4___redArg(v_as_4510_, v_sz_4511_, v_i_4512_, v_b_4513_, v___y_4516_, v___y_4517_, v___y_4518_, v___y_4519_);
return v___x_4521_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_4510_ = stack[0].m_obj;
size_t v_sz_4511_ = stack[1].m_num;
size_t v_i_4512_ = stack[2].m_num;
lean_object* v_b_4513_ = stack[3].m_obj;
lean_object* v___y_4514_ = stack[4].m_obj;
lean_object* v___y_4515_ = stack[5].m_obj;
lean_object* v___y_4516_ = stack[6].m_obj;
lean_object* v___y_4517_ = stack[7].m_obj;
lean_object* v___y_4518_ = stack[8].m_obj;
lean_object* v___y_4519_ = stack[9].m_obj;
lean_object* v_res_4522_;
v_res_4522_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4(v_as_4510_, v_sz_4511_, v_i_4512_, v_b_4513_, v___y_4514_, v___y_4515_, v___y_4516_, v___y_4517_, v___y_4518_, v___y_4519_);
stack->m_obj
 = v_res_4522_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4___boxed(lean_object* v_as_4523_, lean_object* v_sz_4524_, lean_object* v_i_4525_, lean_object* v_b_4526_, lean_object* v___y_4527_, lean_object* v___y_4528_, lean_object* v___y_4529_, lean_object* v___y_4530_, lean_object* v___y_4531_, lean_object* v___y_4532_, lean_object* v___y_4533_){
_start:
{
size_t v_sz_boxed_4534_; size_t v_i_boxed_4535_; lean_object* v_res_4536_; 
v_sz_boxed_4534_ = lean_unbox_usize(v_sz_4524_);
lean_dec(v_sz_4524_);
v_i_boxed_4535_ = lean_unbox_usize(v_i_4525_);
lean_dec(v_i_4525_);
v_res_4536_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4(v_as_4523_, v_sz_boxed_4534_, v_i_boxed_4535_, v_b_4526_, v___y_4527_, v___y_4528_, v___y_4529_, v___y_4530_, v___y_4531_, v___y_4532_);
lean_dec(v___y_4532_);
lean_dec_ref(v___y_4531_);
lean_dec(v___y_4530_);
lean_dec_ref(v___y_4529_);
lean_dec(v___y_4528_);
lean_dec_ref(v___y_4527_);
lean_dec_ref(v_as_4523_);
return v_res_4536_;
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
