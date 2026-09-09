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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(lean_object*, lean_object*, lean_object*, lean_object*);
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
extern lean_object* l_Lean_Elab_instInhabitedPreDefinition_default;
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg___lam__0(lean_object* v_k_57_, lean_object* v_b_58_, lean_object* v_c_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg___lam__0___boxed(lean_object* v_k_66_, lean_object* v_b_67_, lean_object* v_c_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg___lam__0(v_k_66_, v_b_67_, v_c_68_, v___y_69_, v___y_70_, v___y_71_, v___y_72_);
lean_dec(v___y_72_);
lean_dec_ref(v___y_71_);
lean_dec(v___y_70_);
lean_dec_ref(v___y_69_);
return v_res_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg(lean_object* v_e_75_, lean_object* v_k_76_, uint8_t v_cleanupAnnotations_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_){
_start:
{
lean_object* v___f_83_; uint8_t v___x_84_; uint8_t v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v___f_83_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_83_, 0, v_k_76_);
v___x_84_ = 1;
v___x_85_ = 0;
v___x_86_ = lean_box(0);
v___x_87_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_75_, v___x_84_, v___x_85_, v___x_84_, v___x_85_, v___x_86_, v___f_83_, v_cleanupAnnotations_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_);
if (lean_obj_tag(v___x_87_) == 0)
{
lean_object* v_a_88_; lean_object* v___x_90_; uint8_t v_isShared_91_; uint8_t v_isSharedCheck_95_; 
v_a_88_ = lean_ctor_get(v___x_87_, 0);
v_isSharedCheck_95_ = !lean_is_exclusive(v___x_87_);
if (v_isSharedCheck_95_ == 0)
{
v___x_90_ = v___x_87_;
v_isShared_91_ = v_isSharedCheck_95_;
goto v_resetjp_89_;
}
else
{
lean_inc(v_a_88_);
lean_dec(v___x_87_);
v___x_90_ = lean_box(0);
v_isShared_91_ = v_isSharedCheck_95_;
goto v_resetjp_89_;
}
v_resetjp_89_:
{
lean_object* v___x_93_; 
if (v_isShared_91_ == 0)
{
v___x_93_ = v___x_90_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_94_; 
v_reuseFailAlloc_94_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_94_, 0, v_a_88_);
v___x_93_ = v_reuseFailAlloc_94_;
goto v_reusejp_92_;
}
v_reusejp_92_:
{
return v___x_93_;
}
}
}
else
{
lean_object* v_a_96_; lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_103_; 
v_a_96_ = lean_ctor_get(v___x_87_, 0);
v_isSharedCheck_103_ = !lean_is_exclusive(v___x_87_);
if (v_isSharedCheck_103_ == 0)
{
v___x_98_ = v___x_87_;
v_isShared_99_ = v_isSharedCheck_103_;
goto v_resetjp_97_;
}
else
{
lean_inc(v_a_96_);
lean_dec(v___x_87_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_103_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
lean_object* v___x_101_; 
if (v_isShared_99_ == 0)
{
v___x_101_ = v___x_98_;
goto v_reusejp_100_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v_a_96_);
v___x_101_ = v_reuseFailAlloc_102_;
goto v_reusejp_100_;
}
v_reusejp_100_:
{
return v___x_101_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg___boxed(lean_object* v_e_104_, lean_object* v_k_105_, lean_object* v_cleanupAnnotations_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_112_; lean_object* v_res_113_; 
v_cleanupAnnotations_boxed_112_ = lean_unbox(v_cleanupAnnotations_106_);
v_res_113_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg(v_e_104_, v_k_105_, v_cleanupAnnotations_boxed_112_, v___y_107_, v___y_108_, v___y_109_, v___y_110_);
lean_dec(v___y_110_);
lean_dec_ref(v___y_109_);
lean_dec(v___y_108_);
lean_dec_ref(v___y_107_);
return v_res_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1(lean_object* v_00_u03b1_114_, lean_object* v_e_115_, lean_object* v_k_116_, uint8_t v_cleanupAnnotations_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg(v_e_115_, v_k_116_, v_cleanupAnnotations_117_, v___y_118_, v___y_119_, v___y_120_, v___y_121_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___boxed(lean_object* v_00_u03b1_124_, lean_object* v_e_125_, lean_object* v_k_126_, lean_object* v_cleanupAnnotations_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_133_; lean_object* v_res_134_; 
v_cleanupAnnotations_boxed_133_ = lean_unbox(v_cleanupAnnotations_127_);
v_res_134_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1(v_00_u03b1_124_, v_e_125_, v_k_126_, v_cleanupAnnotations_boxed_133_, v___y_128_, v___y_129_, v___y_130_, v___y_131_);
lean_dec(v___y_131_);
lean_dec_ref(v___y_130_);
lean_dec(v___y_129_);
lean_dec_ref(v___y_128_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0(lean_object* v___x_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_){
_start:
{
lean_object* v_toCold_144_; lean_object* v_options_145_; uint8_t v_hasTrace_146_; 
v_toCold_144_ = lean_ctor_get(v___y_141_, 0);
v_options_145_ = lean_ctor_get(v_toCold_144_, 2);
v_hasTrace_146_ = lean_ctor_get_uint8(v_options_145_, sizeof(void*)*1);
if (v_hasTrace_146_ == 0)
{
lean_object* v___x_147_; lean_object* v___x_148_; 
lean_dec(v___x_138_);
v___x_147_ = lean_box(v_hasTrace_146_);
v___x_148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_148_, 0, v___x_147_);
return v___x_148_;
}
else
{
lean_object* v_inheritedTraceOptions_149_; lean_object* v___x_150_; lean_object* v___x_151_; uint8_t v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v_inheritedTraceOptions_149_ = lean_ctor_get(v_toCold_144_, 11);
v___x_150_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0___closed__1));
v___x_151_ = l_Lean_Name_append(v___x_150_, v___x_138_);
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
lean_object* v___x_19368__overap_176_; lean_object* v___x_177_; 
v___x_19368__overap_176_ = lean_array_uget_borrowed(v_as_166_, v_i_167_);
lean_inc(v___x_19368__overap_176_);
lean_inc(v___y_173_);
lean_inc_ref(v___y_172_);
lean_inc(v___y_171_);
lean_inc_ref(v___y_170_);
v___x_177_ = lean_apply_5(v___x_19368__overap_176_, v___y_170_, v___y_171_, v___y_172_, v___y_173_, lean_box(0));
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
v___x_267_ = lean_st_ref_put(v___y_251_, v___x_266_);
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
v___x_279_ = lean_st_ref_put(v___y_250_, v___x_278_);
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
size_t v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_397_ = lean_usize_of_nat(v___x_393_);
v___x_398_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___boxed__const__1));
v___x_399_ = lean_box_usize(v___x_397_);
v___x_400_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__24___boxed), 9, 4);
lean_closure_set(v___x_400_, 0, v_preDefs_378_);
lean_closure_set(v___x_400_, 1, v___x_398_);
lean_closure_set(v___x_400_, 2, v___x_399_);
lean_closure_set(v___x_400_, 3, v___x_394_);
v___y_386_ = v___x_400_;
goto v___jp_385_;
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___boxed(lean_object* v_preDefs_401_, lean_object* v_k_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v_preDefs_401_, v_k_402_, v___y_403_, v___y_404_, v___y_405_, v___y_406_);
lean_dec(v___y_406_);
lean_dec_ref(v___y_405_);
lean_dec(v___y_404_);
lean_dec_ref(v___y_403_);
return v_res_408_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg___closed__0(void){
_start:
{
lean_object* v___x_409_; lean_object* v_dummy_410_; 
v___x_409_ = lean_box(0);
v_dummy_410_ = l_Lean_Expr_sort___override(v___x_409_);
return v_dummy_410_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg(uint8_t v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_recArgInfos_414_, lean_object* v___x_415_, lean_object* v_preDefs_416_, lean_object* v_a_417_, size_t v_sz_418_, size_t v_i_419_, lean_object* v_bs_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_){
_start:
{
uint8_t v___x_426_; 
v___x_426_ = lean_usize_dec_lt(v_i_419_, v_sz_418_);
if (v___x_426_ == 0)
{
lean_object* v___x_427_; 
lean_dec_ref(v_a_417_);
lean_dec_ref(v_preDefs_416_);
lean_dec_ref(v___x_415_);
lean_dec_ref(v_recArgInfos_414_);
v___x_427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_427_, 0, v_bs_420_);
return v___x_427_;
}
else
{
lean_object* v___x_428_; lean_object* v_v_429_; lean_object* v___x_430_; lean_object* v_bs_x27_431_; lean_object* v_a_433_; lean_object* v___x_438_; 
v___x_428_ = l_Lean_instInhabitedExpr;
v_v_429_ = lean_array_uget(v_bs_420_, v_i_419_);
v___x_430_ = lean_unsigned_to_nat(0u);
v_bs_x27_431_ = lean_array_uset(v_bs_420_, v_i_419_, v___x_430_);
v___x_438_ = lean_usize_to_nat(v_i_419_);
if (v_a_411_ == 0)
{
lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_439_ = lean_array_get_borrowed(v___x_428_, v_a_412_, v___x_438_);
v___x_440_ = lean_array_get_borrowed(v___x_428_, v_a_413_, v___x_438_);
lean_dec(v___x_438_);
lean_inc(v___x_440_);
lean_inc(v___x_439_);
lean_inc_ref(v___x_415_);
lean_inc_ref(v_recArgInfos_414_);
v___x_441_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnF___boxed), 10, 5);
lean_closure_set(v___x_441_, 0, v_recArgInfos_414_);
lean_closure_set(v___x_441_, 1, v___x_415_);
lean_closure_set(v___x_441_, 2, v_v_429_);
lean_closure_set(v___x_441_, 3, v___x_439_);
lean_closure_set(v___x_441_, 4, v___x_440_);
lean_inc_ref(v_preDefs_416_);
v___x_442_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v_preDefs_416_, v___x_441_, v___y_421_, v___y_422_, v___y_423_, v___y_424_);
if (lean_obj_tag(v___x_442_) == 0)
{
lean_object* v_a_443_; 
v_a_443_ = lean_ctor_get(v___x_442_, 0);
lean_inc(v_a_443_);
lean_dec_ref_known(v___x_442_, 1);
v_a_433_ = v_a_443_;
goto v___jp_432_;
}
else
{
lean_object* v_a_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_451_; 
lean_dec_ref(v_bs_x27_431_);
lean_dec_ref(v_a_417_);
lean_dec_ref(v_preDefs_416_);
lean_dec_ref(v___x_415_);
lean_dec_ref(v_recArgInfos_414_);
v_a_444_ = lean_ctor_get(v___x_442_, 0);
v_isSharedCheck_451_ = !lean_is_exclusive(v___x_442_);
if (v_isSharedCheck_451_ == 0)
{
v___x_446_ = v___x_442_;
v_isShared_447_ = v_isSharedCheck_451_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_a_444_);
lean_dec(v___x_442_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_451_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
lean_object* v___x_449_; 
if (v_isShared_447_ == 0)
{
v___x_449_ = v___x_446_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v_a_444_);
v___x_449_ = v_reuseFailAlloc_450_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
return v___x_449_;
}
}
}
}
else
{
lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v_dummy_455_; lean_object* v_nargs_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_452_ = lean_array_get_borrowed(v___x_428_, v_a_412_, v___x_438_);
v___x_453_ = lean_array_get_borrowed(v___x_428_, v_a_413_, v___x_438_);
lean_dec(v___x_438_);
lean_inc_ref(v_a_417_);
v___x_454_ = lean_apply_1(v_a_417_, v___x_430_);
v_dummy_455_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg___closed__0);
v_nargs_456_ = l_Lean_Expr_getAppNumArgs(v___x_454_);
lean_inc(v_nargs_456_);
v___x_457_ = lean_mk_array(v_nargs_456_, v_dummy_455_);
v___x_458_ = lean_unsigned_to_nat(1u);
v___x_459_ = lean_nat_sub(v_nargs_456_, v___x_458_);
lean_dec(v_nargs_456_);
v___x_460_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___x_454_, v___x_457_, v___x_459_);
lean_inc(v___x_453_);
lean_inc(v___x_452_);
lean_inc_ref(v___x_415_);
lean_inc_ref(v_recArgInfos_414_);
v___x_461_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkIndPredBRecOnF___boxed), 11, 6);
lean_closure_set(v___x_461_, 0, v_recArgInfos_414_);
lean_closure_set(v___x_461_, 1, v___x_415_);
lean_closure_set(v___x_461_, 2, v_v_429_);
lean_closure_set(v___x_461_, 3, v___x_452_);
lean_closure_set(v___x_461_, 4, v___x_453_);
lean_closure_set(v___x_461_, 5, v___x_460_);
lean_inc_ref(v_preDefs_416_);
v___x_462_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v_preDefs_416_, v___x_461_, v___y_421_, v___y_422_, v___y_423_, v___y_424_);
if (lean_obj_tag(v___x_462_) == 0)
{
lean_object* v_a_463_; lean_object* v_fst_464_; lean_object* v_snd_465_; lean_object* v___y_467_; lean_object* v___x_476_; uint8_t v___x_477_; 
v_a_463_ = lean_ctor_get(v___x_462_, 0);
lean_inc(v_a_463_);
lean_dec_ref_known(v___x_462_, 1);
v_fst_464_ = lean_ctor_get(v_a_463_, 0);
lean_inc(v_fst_464_);
v_snd_465_ = lean_ctor_get(v_a_463_, 1);
lean_inc(v_snd_465_);
lean_dec(v_a_463_);
v___x_476_ = lean_array_get_size(v_snd_465_);
v___x_477_ = lean_nat_dec_lt(v___x_430_, v___x_476_);
if (v___x_477_ == 0)
{
lean_dec(v_snd_465_);
v_a_433_ = v_fst_464_;
goto v___jp_432_;
}
else
{
lean_object* v___x_478_; uint8_t v___x_479_; 
v___x_478_ = lean_box(0);
v___x_479_ = lean_nat_dec_le(v___x_476_, v___x_476_);
if (v___x_479_ == 0)
{
if (v___x_477_ == 0)
{
lean_dec(v_snd_465_);
v_a_433_ = v_fst_464_;
goto v___jp_432_;
}
else
{
size_t v___x_480_; size_t v___x_481_; lean_object* v___x_482_; 
v___x_480_ = ((size_t)0ULL);
v___x_481_ = lean_usize_of_nat(v___x_476_);
v___x_482_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13(v_snd_465_, v___x_480_, v___x_481_, v___x_478_, v___y_421_, v___y_422_, v___y_423_, v___y_424_);
lean_dec(v_snd_465_);
v___y_467_ = v___x_482_;
goto v___jp_466_;
}
}
else
{
size_t v___x_483_; size_t v___x_484_; lean_object* v___x_485_; 
v___x_483_ = ((size_t)0ULL);
v___x_484_ = lean_usize_of_nat(v___x_476_);
v___x_485_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13(v_snd_465_, v___x_483_, v___x_484_, v___x_478_, v___y_421_, v___y_422_, v___y_423_, v___y_424_);
lean_dec(v_snd_465_);
v___y_467_ = v___x_485_;
goto v___jp_466_;
}
}
v___jp_466_:
{
if (lean_obj_tag(v___y_467_) == 0)
{
lean_dec_ref_known(v___y_467_, 1);
v_a_433_ = v_fst_464_;
goto v___jp_432_;
}
else
{
lean_object* v_a_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_475_; 
lean_dec(v_fst_464_);
lean_dec_ref(v_bs_x27_431_);
lean_dec_ref(v_a_417_);
lean_dec_ref(v_preDefs_416_);
lean_dec_ref(v___x_415_);
lean_dec_ref(v_recArgInfos_414_);
v_a_468_ = lean_ctor_get(v___y_467_, 0);
v_isSharedCheck_475_ = !lean_is_exclusive(v___y_467_);
if (v_isSharedCheck_475_ == 0)
{
v___x_470_ = v___y_467_;
v_isShared_471_ = v_isSharedCheck_475_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_a_468_);
lean_dec(v___y_467_);
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
lean_object* v_a_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_493_; 
lean_dec_ref(v_bs_x27_431_);
lean_dec_ref(v_a_417_);
lean_dec_ref(v_preDefs_416_);
lean_dec_ref(v___x_415_);
lean_dec_ref(v_recArgInfos_414_);
v_a_486_ = lean_ctor_get(v___x_462_, 0);
v_isSharedCheck_493_ = !lean_is_exclusive(v___x_462_);
if (v_isSharedCheck_493_ == 0)
{
v___x_488_ = v___x_462_;
v_isShared_489_ = v_isSharedCheck_493_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_a_486_);
lean_dec(v___x_462_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_493_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v___x_491_; 
if (v_isShared_489_ == 0)
{
v___x_491_ = v___x_488_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v_a_486_);
v___x_491_ = v_reuseFailAlloc_492_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
return v___x_491_;
}
}
}
}
v___jp_432_:
{
size_t v___x_434_; size_t v___x_435_; lean_object* v___x_436_; 
v___x_434_ = ((size_t)1ULL);
v___x_435_ = lean_usize_add(v_i_419_, v___x_434_);
v___x_436_ = lean_array_uset(v_bs_x27_431_, v_i_419_, v_a_433_);
v_i_419_ = v___x_435_;
v_bs_420_ = v___x_436_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg___boxed(lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_recArgInfos_497_, lean_object* v___x_498_, lean_object* v_preDefs_499_, lean_object* v_a_500_, lean_object* v_sz_501_, lean_object* v_i_502_, lean_object* v_bs_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_){
_start:
{
uint8_t v_a_25206__boxed_509_; size_t v_sz_boxed_510_; size_t v_i_boxed_511_; lean_object* v_res_512_; 
v_a_25206__boxed_509_ = lean_unbox(v_a_494_);
v_sz_boxed_510_ = lean_unbox_usize(v_sz_501_);
lean_dec(v_sz_501_);
v_i_boxed_511_ = lean_unbox_usize(v_i_502_);
lean_dec(v_i_502_);
v_res_512_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg(v_a_25206__boxed_509_, v_a_495_, v_a_496_, v_recArgInfos_497_, v___x_498_, v_preDefs_499_, v_a_500_, v_sz_boxed_510_, v_i_boxed_511_, v_bs_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_);
lean_dec(v___y_507_);
lean_dec_ref(v___y_506_);
lean_dec(v___y_505_);
lean_dec_ref(v___y_504_);
lean_dec_ref(v_a_496_);
lean_dec_ref(v_a_495_);
return v_res_512_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11_spec__21(lean_object* v_msgData_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_){
_start:
{
lean_object* v___x_519_; lean_object* v_env_520_; lean_object* v___x_521_; lean_object* v_toCold_522_; lean_object* v_mctx_523_; lean_object* v_lctx_524_; lean_object* v_options_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_519_ = lean_st_ref_get(v___y_517_);
v_env_520_ = lean_ctor_get(v___x_519_, 0);
lean_inc_ref(v_env_520_);
lean_dec(v___x_519_);
v___x_521_ = lean_st_ref_get(v___y_515_);
v_toCold_522_ = lean_ctor_get(v___y_516_, 0);
v_mctx_523_ = lean_ctor_get(v___x_521_, 0);
lean_inc_ref(v_mctx_523_);
lean_dec(v___x_521_);
v_lctx_524_ = lean_ctor_get(v___y_514_, 2);
v_options_525_ = lean_ctor_get(v_toCold_522_, 2);
lean_inc_ref(v_options_525_);
lean_inc_ref(v_lctx_524_);
v___x_526_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_526_, 0, v_env_520_);
lean_ctor_set(v___x_526_, 1, v_mctx_523_);
lean_ctor_set(v___x_526_, 2, v_lctx_524_);
lean_ctor_set(v___x_526_, 3, v_options_525_);
v___x_527_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_527_, 0, v___x_526_);
lean_ctor_set(v___x_527_, 1, v_msgData_513_);
v___x_528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_528_, 0, v___x_527_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11_spec__21___boxed(lean_object* v_msgData_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_){
_start:
{
lean_object* v_res_535_; 
v_res_535_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11_spec__21(v_msgData_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_);
lean_dec(v___y_533_);
lean_dec_ref(v___y_532_);
lean_dec(v___y_531_);
lean_dec_ref(v___y_530_);
return v_res_535_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___closed__0(void){
_start:
{
lean_object* v___x_536_; double v___x_537_; 
v___x_536_ = lean_unsigned_to_nat(0u);
v___x_537_ = lean_float_of_nat(v___x_536_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(lean_object* v_cls_541_, lean_object* v_msg_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_){
_start:
{
lean_object* v_ref_548_; lean_object* v___x_549_; lean_object* v_a_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_594_; 
v_ref_548_ = lean_ctor_get(v___y_545_, 2);
v___x_549_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11_spec__21(v_msg_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_);
v_a_550_ = lean_ctor_get(v___x_549_, 0);
v_isSharedCheck_594_ = !lean_is_exclusive(v___x_549_);
if (v_isSharedCheck_594_ == 0)
{
v___x_552_ = v___x_549_;
v_isShared_553_ = v_isSharedCheck_594_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_a_550_);
lean_dec(v___x_549_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_594_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_554_; lean_object* v_traceState_555_; lean_object* v_env_556_; lean_object* v_nextMacroScope_557_; lean_object* v_ngen_558_; lean_object* v_auxDeclNGen_559_; lean_object* v_cache_560_; lean_object* v_messages_561_; lean_object* v_infoState_562_; lean_object* v_snapshotTasks_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_593_; 
v___x_554_ = lean_st_ref_take(v___y_546_);
v_traceState_555_ = lean_ctor_get(v___x_554_, 4);
v_env_556_ = lean_ctor_get(v___x_554_, 0);
v_nextMacroScope_557_ = lean_ctor_get(v___x_554_, 1);
v_ngen_558_ = lean_ctor_get(v___x_554_, 2);
v_auxDeclNGen_559_ = lean_ctor_get(v___x_554_, 3);
v_cache_560_ = lean_ctor_get(v___x_554_, 5);
v_messages_561_ = lean_ctor_get(v___x_554_, 6);
v_infoState_562_ = lean_ctor_get(v___x_554_, 7);
v_snapshotTasks_563_ = lean_ctor_get(v___x_554_, 8);
v_isSharedCheck_593_ = !lean_is_exclusive(v___x_554_);
if (v_isSharedCheck_593_ == 0)
{
v___x_565_ = v___x_554_;
v_isShared_566_ = v_isSharedCheck_593_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_snapshotTasks_563_);
lean_inc(v_infoState_562_);
lean_inc(v_messages_561_);
lean_inc(v_cache_560_);
lean_inc(v_traceState_555_);
lean_inc(v_auxDeclNGen_559_);
lean_inc(v_ngen_558_);
lean_inc(v_nextMacroScope_557_);
lean_inc(v_env_556_);
lean_dec(v___x_554_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_593_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
uint64_t v_tid_567_; lean_object* v_traces_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_592_; 
v_tid_567_ = lean_ctor_get_uint64(v_traceState_555_, sizeof(void*)*1);
v_traces_568_ = lean_ctor_get(v_traceState_555_, 0);
v_isSharedCheck_592_ = !lean_is_exclusive(v_traceState_555_);
if (v_isSharedCheck_592_ == 0)
{
v___x_570_ = v_traceState_555_;
v_isShared_571_ = v_isSharedCheck_592_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_traces_568_);
lean_dec(v_traceState_555_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_592_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___x_572_; double v___x_573_; uint8_t v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_582_; 
v___x_572_ = lean_box(0);
v___x_573_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___closed__0);
v___x_574_ = 0;
v___x_575_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___closed__1));
v___x_576_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_576_, 0, v_cls_541_);
lean_ctor_set(v___x_576_, 1, v___x_572_);
lean_ctor_set(v___x_576_, 2, v___x_575_);
lean_ctor_set_float(v___x_576_, sizeof(void*)*3, v___x_573_);
lean_ctor_set_float(v___x_576_, sizeof(void*)*3 + 8, v___x_573_);
lean_ctor_set_uint8(v___x_576_, sizeof(void*)*3 + 16, v___x_574_);
v___x_577_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___closed__2));
v___x_578_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_578_, 0, v___x_576_);
lean_ctor_set(v___x_578_, 1, v_a_550_);
lean_ctor_set(v___x_578_, 2, v___x_577_);
lean_inc(v_ref_548_);
v___x_579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_579_, 0, v_ref_548_);
lean_ctor_set(v___x_579_, 1, v___x_578_);
v___x_580_ = l_Lean_PersistentArray_push___redArg(v_traces_568_, v___x_579_);
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 0, v___x_580_);
v___x_582_ = v___x_570_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v___x_580_);
lean_ctor_set_uint64(v_reuseFailAlloc_591_, sizeof(void*)*1, v_tid_567_);
v___x_582_ = v_reuseFailAlloc_591_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
lean_object* v___x_584_; 
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 4, v___x_582_);
v___x_584_ = v___x_565_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v_env_556_);
lean_ctor_set(v_reuseFailAlloc_590_, 1, v_nextMacroScope_557_);
lean_ctor_set(v_reuseFailAlloc_590_, 2, v_ngen_558_);
lean_ctor_set(v_reuseFailAlloc_590_, 3, v_auxDeclNGen_559_);
lean_ctor_set(v_reuseFailAlloc_590_, 4, v___x_582_);
lean_ctor_set(v_reuseFailAlloc_590_, 5, v_cache_560_);
lean_ctor_set(v_reuseFailAlloc_590_, 6, v_messages_561_);
lean_ctor_set(v_reuseFailAlloc_590_, 7, v_infoState_562_);
lean_ctor_set(v_reuseFailAlloc_590_, 8, v_snapshotTasks_563_);
v___x_584_ = v_reuseFailAlloc_590_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_588_; 
v___x_585_ = lean_st_ref_put(v___y_546_, v___x_584_);
v___x_586_ = lean_box(0);
if (v_isShared_553_ == 0)
{
lean_ctor_set(v___x_552_, 0, v___x_586_);
v___x_588_ = v___x_552_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v___x_586_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
return v___x_588_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___boxed(lean_object* v_cls_595_, lean_object* v_msg_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v_cls_595_, v_msg_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_);
lean_dec(v___y_600_);
lean_dec_ref(v___y_599_);
lean_dec(v___y_598_);
lean_dec_ref(v___y_597_);
return v_res_602_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9(lean_object* v_as_603_, lean_object* v_bs_604_, lean_object* v_i_605_, lean_object* v_cs_606_){
_start:
{
lean_object* v___x_607_; uint8_t v___x_608_; 
v___x_607_ = lean_array_get_size(v_as_603_);
v___x_608_ = lean_nat_dec_lt(v_i_605_, v___x_607_);
if (v___x_608_ == 0)
{
lean_dec(v_i_605_);
return v_cs_606_;
}
else
{
lean_object* v___x_609_; uint8_t v___x_610_; 
v___x_609_ = lean_array_get_size(v_bs_604_);
v___x_610_ = lean_nat_dec_lt(v_i_605_, v___x_609_);
if (v___x_610_ == 0)
{
lean_dec(v_i_605_);
return v_cs_606_;
}
else
{
lean_object* v_a_611_; lean_object* v_ref_612_; uint8_t v_kind_613_; lean_object* v_levelParams_614_; lean_object* v_modifiers_615_; lean_object* v_declName_616_; lean_object* v_binders_617_; lean_object* v_numSectionVars_618_; lean_object* v_type_619_; lean_object* v_termination_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_632_; 
v_a_611_ = lean_array_fget(v_as_603_, v_i_605_);
v_ref_612_ = lean_ctor_get(v_a_611_, 0);
v_kind_613_ = lean_ctor_get_uint8(v_a_611_, sizeof(void*)*9);
v_levelParams_614_ = lean_ctor_get(v_a_611_, 1);
v_modifiers_615_ = lean_ctor_get(v_a_611_, 2);
v_declName_616_ = lean_ctor_get(v_a_611_, 3);
v_binders_617_ = lean_ctor_get(v_a_611_, 4);
v_numSectionVars_618_ = lean_ctor_get(v_a_611_, 5);
v_type_619_ = lean_ctor_get(v_a_611_, 6);
v_termination_620_ = lean_ctor_get(v_a_611_, 8);
v_isSharedCheck_632_ = !lean_is_exclusive(v_a_611_);
if (v_isSharedCheck_632_ == 0)
{
lean_object* v_unused_633_; 
v_unused_633_ = lean_ctor_get(v_a_611_, 7);
lean_dec(v_unused_633_);
v___x_622_ = v_a_611_;
v_isShared_623_ = v_isSharedCheck_632_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_termination_620_);
lean_inc(v_type_619_);
lean_inc(v_numSectionVars_618_);
lean_inc(v_binders_617_);
lean_inc(v_declName_616_);
lean_inc(v_modifiers_615_);
lean_inc(v_levelParams_614_);
lean_inc(v_ref_612_);
lean_dec(v_a_611_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_632_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v_b_624_; lean_object* v___x_626_; 
v_b_624_ = lean_array_fget_borrowed(v_bs_604_, v_i_605_);
lean_inc(v_b_624_);
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 7, v_b_624_);
v___x_626_ = v___x_622_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v_ref_612_);
lean_ctor_set(v_reuseFailAlloc_631_, 1, v_levelParams_614_);
lean_ctor_set(v_reuseFailAlloc_631_, 2, v_modifiers_615_);
lean_ctor_set(v_reuseFailAlloc_631_, 3, v_declName_616_);
lean_ctor_set(v_reuseFailAlloc_631_, 4, v_binders_617_);
lean_ctor_set(v_reuseFailAlloc_631_, 5, v_numSectionVars_618_);
lean_ctor_set(v_reuseFailAlloc_631_, 6, v_type_619_);
lean_ctor_set(v_reuseFailAlloc_631_, 7, v_b_624_);
lean_ctor_set(v_reuseFailAlloc_631_, 8, v_termination_620_);
lean_ctor_set_uint8(v_reuseFailAlloc_631_, sizeof(void*)*9, v_kind_613_);
v___x_626_ = v_reuseFailAlloc_631_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_627_ = lean_unsigned_to_nat(1u);
v___x_628_ = lean_nat_add(v_i_605_, v___x_627_);
lean_dec(v_i_605_);
v___x_629_ = lean_array_push(v_cs_606_, v___x_626_);
v_i_605_ = v___x_628_;
v_cs_606_ = v___x_629_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9___boxed(lean_object* v_as_634_, lean_object* v_bs_635_, lean_object* v_i_636_, lean_object* v_cs_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9(v_as_634_, v_bs_635_, v_i_636_, v_cs_637_);
lean_dec_ref(v_bs_635_);
lean_dec_ref(v_as_634_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16_spec__29___redArg(lean_object* v_declName_639_, uint8_t v_s_640_, lean_object* v___y_641_, lean_object* v___y_642_){
_start:
{
lean_object* v___x_644_; lean_object* v_env_645_; lean_object* v_nextMacroScope_646_; lean_object* v_ngen_647_; lean_object* v_auxDeclNGen_648_; lean_object* v_traceState_649_; lean_object* v_messages_650_; lean_object* v_infoState_651_; lean_object* v_snapshotTasks_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_681_; 
v___x_644_ = lean_st_ref_take(v___y_642_);
v_env_645_ = lean_ctor_get(v___x_644_, 0);
v_nextMacroScope_646_ = lean_ctor_get(v___x_644_, 1);
v_ngen_647_ = lean_ctor_get(v___x_644_, 2);
v_auxDeclNGen_648_ = lean_ctor_get(v___x_644_, 3);
v_traceState_649_ = lean_ctor_get(v___x_644_, 4);
v_messages_650_ = lean_ctor_get(v___x_644_, 6);
v_infoState_651_ = lean_ctor_get(v___x_644_, 7);
v_snapshotTasks_652_ = lean_ctor_get(v___x_644_, 8);
v_isSharedCheck_681_ = !lean_is_exclusive(v___x_644_);
if (v_isSharedCheck_681_ == 0)
{
lean_object* v_unused_682_; 
v_unused_682_ = lean_ctor_get(v___x_644_, 5);
lean_dec(v_unused_682_);
v___x_654_ = v___x_644_;
v_isShared_655_ = v_isSharedCheck_681_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_snapshotTasks_652_);
lean_inc(v_infoState_651_);
lean_inc(v_messages_650_);
lean_inc(v_traceState_649_);
lean_inc(v_auxDeclNGen_648_);
lean_inc(v_ngen_647_);
lean_inc(v_nextMacroScope_646_);
lean_inc(v_env_645_);
lean_dec(v___x_644_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_681_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
uint8_t v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_661_; 
v___x_656_ = 0;
v___x_657_ = lean_box(0);
v___x_658_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_645_, v_declName_639_, v_s_640_, v___x_656_, v___x_657_);
v___x_659_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__2);
if (v_isShared_655_ == 0)
{
lean_ctor_set(v___x_654_, 5, v___x_659_);
lean_ctor_set(v___x_654_, 0, v___x_658_);
v___x_661_ = v___x_654_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v___x_658_);
lean_ctor_set(v_reuseFailAlloc_680_, 1, v_nextMacroScope_646_);
lean_ctor_set(v_reuseFailAlloc_680_, 2, v_ngen_647_);
lean_ctor_set(v_reuseFailAlloc_680_, 3, v_auxDeclNGen_648_);
lean_ctor_set(v_reuseFailAlloc_680_, 4, v_traceState_649_);
lean_ctor_set(v_reuseFailAlloc_680_, 5, v___x_659_);
lean_ctor_set(v_reuseFailAlloc_680_, 6, v_messages_650_);
lean_ctor_set(v_reuseFailAlloc_680_, 7, v_infoState_651_);
lean_ctor_set(v_reuseFailAlloc_680_, 8, v_snapshotTasks_652_);
v___x_661_ = v_reuseFailAlloc_680_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v_mctx_664_; lean_object* v_zetaDeltaFVarIds_665_; lean_object* v_postponed_666_; lean_object* v_diag_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_678_; 
v___x_662_ = lean_st_ref_put(v___y_642_, v___x_661_);
v___x_663_ = lean_st_ref_take(v___y_641_);
v_mctx_664_ = lean_ctor_get(v___x_663_, 0);
v_zetaDeltaFVarIds_665_ = lean_ctor_get(v___x_663_, 2);
v_postponed_666_ = lean_ctor_get(v___x_663_, 3);
v_diag_667_ = lean_ctor_get(v___x_663_, 4);
v_isSharedCheck_678_ = !lean_is_exclusive(v___x_663_);
if (v_isSharedCheck_678_ == 0)
{
lean_object* v_unused_679_; 
v_unused_679_ = lean_ctor_get(v___x_663_, 1);
lean_dec(v_unused_679_);
v___x_669_ = v___x_663_;
v_isShared_670_ = v_isSharedCheck_678_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_diag_667_);
lean_inc(v_postponed_666_);
lean_inc(v_zetaDeltaFVarIds_665_);
lean_inc(v_mctx_664_);
lean_dec(v___x_663_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_678_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v___x_671_; lean_object* v___x_673_; 
v___x_671_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__3, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__3);
if (v_isShared_670_ == 0)
{
lean_ctor_set(v___x_669_, 1, v___x_671_);
v___x_673_ = v___x_669_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v_mctx_664_);
lean_ctor_set(v_reuseFailAlloc_677_, 1, v___x_671_);
lean_ctor_set(v_reuseFailAlloc_677_, 2, v_zetaDeltaFVarIds_665_);
lean_ctor_set(v_reuseFailAlloc_677_, 3, v_postponed_666_);
lean_ctor_set(v_reuseFailAlloc_677_, 4, v_diag_667_);
v___x_673_ = v_reuseFailAlloc_677_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_674_ = lean_st_ref_put(v___y_641_, v___x_673_);
v___x_675_ = lean_box(0);
v___x_676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_676_, 0, v___x_675_);
return v___x_676_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16_spec__29___redArg___boxed(lean_object* v_declName_683_, lean_object* v_s_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_){
_start:
{
uint8_t v_s_boxed_688_; lean_object* v_res_689_; 
v_s_boxed_688_ = lean_unbox(v_s_684_);
v_res_689_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16_spec__29___redArg(v_declName_683_, v_s_boxed_688_, v___y_685_, v___y_686_);
lean_dec(v___y_686_);
lean_dec(v___y_685_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16(lean_object* v_declName_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_){
_start:
{
uint8_t v___x_696_; lean_object* v___x_697_; 
v___x_696_ = 0;
v___x_697_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16_spec__29___redArg(v_declName_690_, v___x_696_, v___y_692_, v___y_694_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16___boxed(lean_object* v_declName_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16(v_declName_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_);
lean_dec(v___y_702_);
lean_dec_ref(v___y_701_);
lean_dec(v___y_700_);
lean_dec_ref(v___y_699_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg(lean_object* v_xs_708_, uint8_t v_a_709_, lean_object* v_preDefs_710_, lean_object* v___x_711_, size_t v_sz_712_, size_t v_i_713_, lean_object* v_bs_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_){
_start:
{
uint8_t v___x_720_; 
v___x_720_ = lean_usize_dec_lt(v_i_713_, v_sz_712_);
if (v___x_720_ == 0)
{
lean_object* v___x_721_; 
lean_dec(v___x_711_);
v___x_721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_721_, 0, v_bs_714_);
return v___x_721_;
}
else
{
lean_object* v_v_722_; lean_object* v___x_723_; lean_object* v_bs_x27_724_; lean_object* v_a_726_; lean_object* v___y_732_; uint8_t v___x_742_; lean_object* v___x_743_; 
v_v_722_ = lean_array_uget(v_bs_714_, v_i_713_);
v___x_723_ = lean_unsigned_to_nat(0u);
v_bs_x27_724_ = lean_array_uset(v_bs_714_, v_i_713_, v___x_723_);
v___x_742_ = 1;
v___x_743_ = l_Lean_Meta_mkLambdaFVars(v_xs_708_, v_v_722_, v_a_709_, v___x_720_, v_a_709_, v___x_720_, v___x_742_, v___y_715_, v___y_716_, v___y_717_, v___y_718_);
if (lean_obj_tag(v___x_743_) == 0)
{
lean_object* v_a_744_; lean_object* v___x_745_; 
v_a_744_ = lean_ctor_get(v___x_743_, 0);
lean_inc(v_a_744_);
lean_dec_ref_known(v___x_743_, 1);
v___x_745_ = l_Lean_Elab_eraseRecAppSyntaxExpr(v_a_744_, v___y_717_, v___y_718_);
if (lean_obj_tag(v___x_745_) == 0)
{
lean_object* v_a_746_; lean_object* v___x_747_; 
v_a_746_ = lean_ctor_get(v___x_745_, 0);
lean_inc_n(v_a_746_, 2);
lean_dec_ref_known(v___x_745_, 1);
lean_inc(v___y_718_);
lean_inc_ref(v___y_717_);
lean_inc(v___y_716_);
lean_inc_ref(v___y_715_);
v___x_747_ = lean_infer_type(v_a_746_, v___y_715_, v___y_716_, v___y_717_, v___y_718_);
if (lean_obj_tag(v___x_747_) == 0)
{
lean_object* v_a_748_; lean_object* v___x_749_; 
v_a_748_ = lean_ctor_get(v___x_747_, 0);
lean_inc(v_a_748_);
lean_dec_ref_known(v___x_747_, 1);
v___x_749_ = l_Lean_Meta_letToHave(v_a_748_, v___y_715_, v___y_716_, v___y_717_, v___y_718_);
if (lean_obj_tag(v___x_749_) == 0)
{
lean_object* v_a_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_833_; 
v_a_750_ = lean_ctor_get(v___x_749_, 0);
v_isSharedCheck_833_ = !lean_is_exclusive(v___x_749_);
if (v_isSharedCheck_833_ == 0)
{
v___x_752_ = v___x_749_;
v_isShared_753_ = v_isSharedCheck_833_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_a_750_);
lean_dec(v___x_749_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_833_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v_modifiers_758_; lean_object* v_levelParams_759_; lean_object* v_declName_760_; lean_object* v_env_761_; uint8_t v_isUnsafe_762_; lean_object* v___x_763_; lean_object* v___x_764_; uint32_t v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; uint8_t v___y_769_; 
v___x_754_ = lean_st_ref_get(v___y_718_);
v___x_755_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_756_ = lean_usize_to_nat(v_i_713_);
v___x_757_ = lean_array_get_borrowed(v___x_755_, v_preDefs_710_, v___x_756_);
lean_dec(v___x_756_);
v_modifiers_758_ = lean_ctor_get(v___x_757_, 2);
v_levelParams_759_ = lean_ctor_get(v___x_757_, 1);
v_declName_760_ = lean_ctor_get(v___x_757_, 3);
v_env_761_ = lean_ctor_get(v___x_754_, 0);
lean_inc_ref(v_env_761_);
lean_dec(v___x_754_);
v_isUnsafe_762_ = lean_ctor_get_uint8(v_modifiers_758_, sizeof(void*)*3 + 4);
v___x_763_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg___closed__1));
lean_inc(v_declName_760_);
v___x_764_ = l_Lean_Name_append(v_declName_760_, v___x_763_);
lean_inc(v_a_746_);
v___x_765_ = l_Lean_getMaxHeight(v_env_761_, v_a_746_);
lean_inc(v_levelParams_759_);
lean_inc(v___x_764_);
v___x_766_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_766_, 0, v___x_764_);
lean_ctor_set(v___x_766_, 1, v_levelParams_759_);
lean_ctor_set(v___x_766_, 2, v_a_750_);
v___x_767_ = lean_box(1);
if (v_isUnsafe_762_ == 0)
{
uint8_t v___x_831_; 
v___x_831_ = 1;
v___y_769_ = v___x_831_;
goto v___jp_768_;
}
else
{
uint8_t v___x_832_; 
v___x_832_ = 0;
v___y_769_ = v___x_832_;
goto v___jp_768_;
}
v___jp_768_:
{
lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_774_; 
v___x_770_ = lean_box(0);
lean_inc(v___x_764_);
v___x_771_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_771_, 0, v___x_764_);
lean_ctor_set(v___x_771_, 1, v___x_770_);
v___x_772_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_772_, 0, v___x_766_);
lean_ctor_set(v___x_772_, 1, v_a_746_);
lean_ctor_set(v___x_772_, 2, v___x_767_);
lean_ctor_set(v___x_772_, 3, v___x_771_);
lean_ctor_set_uint8(v___x_772_, sizeof(void*)*4, v___y_769_);
if (v_isShared_753_ == 0)
{
lean_ctor_set_tag(v___x_752_, 1);
lean_ctor_set(v___x_752_, 0, v___x_772_);
v___x_774_ = v___x_752_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v___x_772_);
v___x_774_ = v_reuseFailAlloc_830_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
lean_object* v___x_775_; 
v___x_775_ = l_Lean_addDecl(v___x_774_, v_a_709_, v___y_717_, v___y_718_);
if (lean_obj_tag(v___x_775_) == 0)
{
lean_object* v___x_776_; lean_object* v_env_777_; lean_object* v_nextMacroScope_778_; lean_object* v_ngen_779_; lean_object* v_auxDeclNGen_780_; lean_object* v_traceState_781_; lean_object* v_messages_782_; lean_object* v_infoState_783_; lean_object* v_snapshotTasks_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_820_; 
lean_dec_ref_known(v___x_775_, 1);
v___x_776_ = lean_st_ref_take(v___y_718_);
v_env_777_ = lean_ctor_get(v___x_776_, 0);
v_nextMacroScope_778_ = lean_ctor_get(v___x_776_, 1);
v_ngen_779_ = lean_ctor_get(v___x_776_, 2);
v_auxDeclNGen_780_ = lean_ctor_get(v___x_776_, 3);
v_traceState_781_ = lean_ctor_get(v___x_776_, 4);
v_messages_782_ = lean_ctor_get(v___x_776_, 6);
v_infoState_783_ = lean_ctor_get(v___x_776_, 7);
v_snapshotTasks_784_ = lean_ctor_get(v___x_776_, 8);
v_isSharedCheck_820_ = !lean_is_exclusive(v___x_776_);
if (v_isSharedCheck_820_ == 0)
{
lean_object* v_unused_821_; 
v_unused_821_ = lean_ctor_get(v___x_776_, 5);
lean_dec(v_unused_821_);
v___x_786_ = v___x_776_;
v_isShared_787_ = v_isSharedCheck_820_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_snapshotTasks_784_);
lean_inc(v_infoState_783_);
lean_inc(v_messages_782_);
lean_inc(v_traceState_781_);
lean_inc(v_auxDeclNGen_780_);
lean_inc(v_ngen_779_);
lean_inc(v_nextMacroScope_778_);
lean_inc(v_env_777_);
lean_dec(v___x_776_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_820_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_791_; 
lean_inc(v___x_764_);
v___x_788_ = l_Lean_setDefHeightOverride(v_env_777_, v___x_764_, v___x_765_);
v___x_789_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__2);
if (v_isShared_787_ == 0)
{
lean_ctor_set(v___x_786_, 5, v___x_789_);
lean_ctor_set(v___x_786_, 0, v___x_788_);
v___x_791_ = v___x_786_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v___x_788_);
lean_ctor_set(v_reuseFailAlloc_819_, 1, v_nextMacroScope_778_);
lean_ctor_set(v_reuseFailAlloc_819_, 2, v_ngen_779_);
lean_ctor_set(v_reuseFailAlloc_819_, 3, v_auxDeclNGen_780_);
lean_ctor_set(v_reuseFailAlloc_819_, 4, v_traceState_781_);
lean_ctor_set(v_reuseFailAlloc_819_, 5, v___x_789_);
lean_ctor_set(v_reuseFailAlloc_819_, 6, v_messages_782_);
lean_ctor_set(v_reuseFailAlloc_819_, 7, v_infoState_783_);
lean_ctor_set(v_reuseFailAlloc_819_, 8, v_snapshotTasks_784_);
v___x_791_ = v_reuseFailAlloc_819_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v_mctx_794_; lean_object* v_zetaDeltaFVarIds_795_; lean_object* v_postponed_796_; lean_object* v_diag_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_817_; 
v___x_792_ = lean_st_ref_put(v___y_718_, v___x_791_);
v___x_793_ = lean_st_ref_take(v___y_716_);
v_mctx_794_ = lean_ctor_get(v___x_793_, 0);
v_zetaDeltaFVarIds_795_ = lean_ctor_get(v___x_793_, 2);
v_postponed_796_ = lean_ctor_get(v___x_793_, 3);
v_diag_797_ = lean_ctor_get(v___x_793_, 4);
v_isSharedCheck_817_ = !lean_is_exclusive(v___x_793_);
if (v_isSharedCheck_817_ == 0)
{
lean_object* v_unused_818_; 
v_unused_818_ = lean_ctor_get(v___x_793_, 1);
lean_dec(v_unused_818_);
v___x_799_ = v___x_793_;
v_isShared_800_ = v_isSharedCheck_817_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_diag_797_);
lean_inc(v_postponed_796_);
lean_inc(v_zetaDeltaFVarIds_795_);
lean_inc(v_mctx_794_);
lean_dec(v___x_793_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_817_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v___x_801_; lean_object* v___x_803_; 
v___x_801_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__3, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__3);
if (v_isShared_800_ == 0)
{
lean_ctor_set(v___x_799_, 1, v___x_801_);
v___x_803_ = v___x_799_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_mctx_794_);
lean_ctor_set(v_reuseFailAlloc_816_, 1, v___x_801_);
lean_ctor_set(v_reuseFailAlloc_816_, 2, v_zetaDeltaFVarIds_795_);
lean_ctor_set(v_reuseFailAlloc_816_, 3, v_postponed_796_);
lean_ctor_set(v_reuseFailAlloc_816_, 4, v_diag_797_);
v___x_803_ = v_reuseFailAlloc_816_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
lean_object* v___x_804_; lean_object* v___x_805_; 
v___x_804_ = lean_st_ref_put(v___y_716_, v___x_803_);
lean_inc(v___x_764_);
v___x_805_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16(v___x_764_, v___y_715_, v___y_716_, v___y_717_, v___y_718_);
if (lean_obj_tag(v___x_805_) == 0)
{
lean_object* v___x_806_; lean_object* v___x_807_; 
lean_dec_ref_known(v___x_805_, 1);
lean_inc(v___x_711_);
v___x_806_ = l_Lean_mkConst(v___x_764_, v___x_711_);
v___x_807_ = l_Lean_mkAppN(v___x_806_, v_xs_708_);
v_a_726_ = v___x_807_;
goto v___jp_725_;
}
else
{
lean_object* v_a_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_815_; 
lean_dec(v___x_764_);
lean_dec_ref(v_bs_x27_724_);
lean_dec(v___x_711_);
v_a_808_ = lean_ctor_get(v___x_805_, 0);
v_isSharedCheck_815_ = !lean_is_exclusive(v___x_805_);
if (v_isSharedCheck_815_ == 0)
{
v___x_810_ = v___x_805_;
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_a_808_);
lean_dec(v___x_805_);
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
lean_dec(v___x_764_);
lean_dec_ref(v_bs_x27_724_);
lean_dec(v___x_711_);
v_a_822_ = lean_ctor_get(v___x_775_, 0);
v_isSharedCheck_829_ = !lean_is_exclusive(v___x_775_);
if (v_isSharedCheck_829_ == 0)
{
v___x_824_ = v___x_775_;
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_a_822_);
lean_dec(v___x_775_);
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
}
}
else
{
lean_dec(v_a_746_);
v___y_732_ = v___x_749_;
goto v___jp_731_;
}
}
else
{
lean_dec(v_a_746_);
v___y_732_ = v___x_747_;
goto v___jp_731_;
}
}
else
{
v___y_732_ = v___x_745_;
goto v___jp_731_;
}
}
else
{
v___y_732_ = v___x_743_;
goto v___jp_731_;
}
v___jp_725_:
{
size_t v___x_727_; size_t v___x_728_; lean_object* v___x_729_; 
v___x_727_ = ((size_t)1ULL);
v___x_728_ = lean_usize_add(v_i_713_, v___x_727_);
v___x_729_ = lean_array_uset(v_bs_x27_724_, v_i_713_, v_a_726_);
v_i_713_ = v___x_728_;
v_bs_714_ = v___x_729_;
goto _start;
}
v___jp_731_:
{
if (lean_obj_tag(v___y_732_) == 0)
{
lean_object* v_a_733_; 
v_a_733_ = lean_ctor_get(v___y_732_, 0);
lean_inc(v_a_733_);
lean_dec_ref_known(v___y_732_, 1);
v_a_726_ = v_a_733_;
goto v___jp_725_;
}
else
{
lean_object* v_a_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_741_; 
lean_dec_ref(v_bs_x27_724_);
lean_dec(v___x_711_);
v_a_734_ = lean_ctor_get(v___y_732_, 0);
v_isSharedCheck_741_ = !lean_is_exclusive(v___y_732_);
if (v_isSharedCheck_741_ == 0)
{
v___x_736_ = v___y_732_;
v_isShared_737_ = v_isSharedCheck_741_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_a_734_);
lean_dec(v___y_732_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_741_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v___x_739_; 
if (v_isShared_737_ == 0)
{
v___x_739_ = v___x_736_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v_a_734_);
v___x_739_ = v_reuseFailAlloc_740_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
return v___x_739_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg___boxed(lean_object* v_xs_834_, lean_object* v_a_835_, lean_object* v_preDefs_836_, lean_object* v___x_837_, lean_object* v_sz_838_, lean_object* v_i_839_, lean_object* v_bs_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_){
_start:
{
uint8_t v_a_25640__boxed_846_; size_t v_sz_boxed_847_; size_t v_i_boxed_848_; lean_object* v_res_849_; 
v_a_25640__boxed_846_ = lean_unbox(v_a_835_);
v_sz_boxed_847_ = lean_unbox_usize(v_sz_838_);
lean_dec(v_sz_838_);
v_i_boxed_848_ = lean_unbox_usize(v_i_839_);
lean_dec(v_i_839_);
v_res_849_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg(v_xs_834_, v_a_25640__boxed_846_, v_preDefs_836_, v___x_837_, v_sz_boxed_847_, v_i_boxed_848_, v_bs_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_);
lean_dec(v___y_844_);
lean_dec_ref(v___y_843_);
lean_dec(v___y_842_);
lean_dec_ref(v___y_841_);
lean_dec_ref(v_preDefs_836_);
lean_dec_ref(v_xs_834_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___lam__0(lean_object* v_fixedParamPerms_850_, lean_object* v___x_851_, lean_object* v___x_852_, lean_object* v_xs_853_, lean_object* v_snd_854_, uint8_t v___x_855_, lean_object* v_ys_856_, lean_object* v_x_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_){
_start:
{
lean_object* v_perms_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; uint8_t v___x_867_; uint8_t v___x_868_; lean_object* v___x_869_; 
v_perms_863_ = lean_ctor_get(v_fixedParamPerms_850_, 1);
v___x_864_ = lean_array_get_borrowed(v___x_851_, v_perms_863_, v___x_852_);
lean_inc_ref(v_ys_856_);
lean_inc(v___x_864_);
v___x_865_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v___x_864_, v_xs_853_, v_ys_856_);
v___x_866_ = l_Lean_Expr_beta(v_snd_854_, v_ys_856_);
v___x_867_ = 0;
v___x_868_ = 1;
v___x_869_ = l_Lean_Meta_mkLambdaFVars(v___x_865_, v___x_866_, v___x_867_, v___x_855_, v___x_867_, v___x_855_, v___x_868_, v___y_858_, v___y_859_, v___y_860_, v___y_861_);
lean_dec_ref(v___x_865_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___lam__0___boxed(lean_object* v_fixedParamPerms_870_, lean_object* v___x_871_, lean_object* v___x_872_, lean_object* v_xs_873_, lean_object* v_snd_874_, lean_object* v___x_875_, lean_object* v_ys_876_, lean_object* v_x_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_){
_start:
{
uint8_t v___x_25863__boxed_883_; lean_object* v_res_884_; 
v___x_25863__boxed_883_ = lean_unbox(v___x_875_);
v_res_884_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___lam__0(v_fixedParamPerms_870_, v___x_871_, v___x_872_, v_xs_873_, v_snd_874_, v___x_25863__boxed_883_, v_ys_876_, v_x_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_);
lean_dec(v___y_881_);
lean_dec_ref(v___y_880_);
lean_dec(v___y_879_);
lean_dec_ref(v___y_878_);
lean_dec_ref(v_x_877_);
lean_dec_ref(v_xs_873_);
lean_dec(v___x_872_);
lean_dec_ref(v___x_871_);
lean_dec_ref(v_fixedParamPerms_870_);
return v_res_884_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_885_; 
v___x_885_ = l_Array_instInhabited(lean_box(0));
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg(lean_object* v_fixedParamPerms_886_, lean_object* v_xs_887_, size_t v_sz_888_, size_t v_i_889_, lean_object* v_bs_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_){
_start:
{
uint8_t v___x_896_; 
v___x_896_ = lean_usize_dec_lt(v_i_889_, v_sz_888_);
if (v___x_896_ == 0)
{
lean_object* v___x_897_; 
lean_dec_ref(v_xs_887_);
lean_dec_ref(v_fixedParamPerms_886_);
v___x_897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_897_, 0, v_bs_890_);
return v___x_897_;
}
else
{
lean_object* v_v_898_; lean_object* v_fst_899_; lean_object* v_snd_900_; lean_object* v___x_901_; lean_object* v_bs_x27_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___f_906_; uint8_t v___x_907_; lean_object* v___x_908_; 
v_v_898_ = lean_array_uget_borrowed(v_bs_890_, v_i_889_);
v_fst_899_ = lean_ctor_get(v_v_898_, 0);
lean_inc(v_fst_899_);
v_snd_900_ = lean_ctor_get(v_v_898_, 1);
lean_inc(v_snd_900_);
v___x_901_ = lean_unsigned_to_nat(0u);
v_bs_x27_902_ = lean_array_uset(v_bs_890_, v_i_889_, v___x_901_);
v___x_903_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0);
v___x_904_ = lean_usize_to_nat(v_i_889_);
v___x_905_ = lean_box(v___x_896_);
lean_inc_ref(v_xs_887_);
lean_inc_ref(v_fixedParamPerms_886_);
v___f_906_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___lam__0___boxed), 13, 6);
lean_closure_set(v___f_906_, 0, v_fixedParamPerms_886_);
lean_closure_set(v___f_906_, 1, v___x_903_);
lean_closure_set(v___f_906_, 2, v___x_904_);
lean_closure_set(v___f_906_, 3, v_xs_887_);
lean_closure_set(v___f_906_, 4, v_snd_900_);
lean_closure_set(v___f_906_, 5, v___x_905_);
v___x_907_ = 0;
v___x_908_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg(v_fst_899_, v___f_906_, v___x_907_, v___y_891_, v___y_892_, v___y_893_, v___y_894_);
if (lean_obj_tag(v___x_908_) == 0)
{
lean_object* v_a_909_; size_t v___x_910_; size_t v___x_911_; lean_object* v___x_912_; 
v_a_909_ = lean_ctor_get(v___x_908_, 0);
lean_inc(v_a_909_);
lean_dec_ref_known(v___x_908_, 1);
v___x_910_ = ((size_t)1ULL);
v___x_911_ = lean_usize_add(v_i_889_, v___x_910_);
v___x_912_ = lean_array_uset(v_bs_x27_902_, v_i_889_, v_a_909_);
v_i_889_ = v___x_911_;
v_bs_890_ = v___x_912_;
goto _start;
}
else
{
lean_object* v_a_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_921_; 
lean_dec_ref(v_bs_x27_902_);
lean_dec_ref(v_xs_887_);
lean_dec_ref(v_fixedParamPerms_886_);
v_a_914_ = lean_ctor_get(v___x_908_, 0);
v_isSharedCheck_921_ = !lean_is_exclusive(v___x_908_);
if (v_isSharedCheck_921_ == 0)
{
v___x_916_ = v___x_908_;
v_isShared_917_ = v_isSharedCheck_921_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_a_914_);
lean_dec(v___x_908_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_921_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v___x_919_; 
if (v_isShared_917_ == 0)
{
v___x_919_ = v___x_916_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v_a_914_);
v___x_919_ = v_reuseFailAlloc_920_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
return v___x_919_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___boxed(lean_object* v_fixedParamPerms_922_, lean_object* v_xs_923_, lean_object* v_sz_924_, lean_object* v_i_925_, lean_object* v_bs_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_){
_start:
{
size_t v_sz_boxed_932_; size_t v_i_boxed_933_; lean_object* v_res_934_; 
v_sz_boxed_932_ = lean_unbox_usize(v_sz_924_);
lean_dec(v_sz_924_);
v_i_boxed_933_ = lean_unbox_usize(v_i_925_);
lean_dec(v_i_925_);
v_res_934_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg(v_fixedParamPerms_922_, v_xs_923_, v_sz_boxed_932_, v_i_boxed_933_, v_bs_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_);
lean_dec(v___y_930_);
lean_dec_ref(v___y_929_);
lean_dec(v___y_928_);
lean_dec_ref(v___y_927_);
return v_res_934_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(lean_object* v_a_935_, lean_object* v_a_936_){
_start:
{
if (lean_obj_tag(v_a_935_) == 0)
{
lean_object* v___x_937_; 
v___x_937_ = l_List_reverse___redArg(v_a_936_);
return v___x_937_;
}
else
{
lean_object* v_head_938_; lean_object* v_tail_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_948_; 
v_head_938_ = lean_ctor_get(v_a_935_, 0);
v_tail_939_ = lean_ctor_get(v_a_935_, 1);
v_isSharedCheck_948_ = !lean_is_exclusive(v_a_935_);
if (v_isSharedCheck_948_ == 0)
{
v___x_941_ = v_a_935_;
v_isShared_942_ = v_isSharedCheck_948_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_tail_939_);
lean_inc(v_head_938_);
lean_dec(v_a_935_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_948_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v___x_943_; lean_object* v___x_945_; 
v___x_943_ = l_Lean_MessageData_ofExpr(v_head_938_);
if (v_isShared_942_ == 0)
{
lean_ctor_set(v___x_941_, 1, v_a_936_);
lean_ctor_set(v___x_941_, 0, v___x_943_);
v___x_945_ = v___x_941_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v___x_943_);
lean_ctor_set(v_reuseFailAlloc_947_, 1, v_a_936_);
v___x_945_ = v_reuseFailAlloc_947_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
v_a_935_ = v_tail_939_;
v_a_936_ = v___x_945_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__15(lean_object* v_a_949_, lean_object* v_a_950_){
_start:
{
if (lean_obj_tag(v_a_949_) == 0)
{
lean_object* v___x_951_; 
v___x_951_ = l_List_reverse___redArg(v_a_950_);
return v___x_951_;
}
else
{
lean_object* v_head_952_; lean_object* v_tail_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_962_; 
v_head_952_ = lean_ctor_get(v_a_949_, 0);
v_tail_953_ = lean_ctor_get(v_a_949_, 1);
v_isSharedCheck_962_ = !lean_is_exclusive(v_a_949_);
if (v_isSharedCheck_962_ == 0)
{
v___x_955_ = v_a_949_;
v_isShared_956_ = v_isSharedCheck_962_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_tail_953_);
lean_inc(v_head_952_);
lean_dec(v_a_949_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_962_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v___x_957_; lean_object* v___x_959_; 
v___x_957_ = l_Lean_mkLevelParam(v_head_952_);
if (v_isShared_956_ == 0)
{
lean_ctor_set(v___x_955_, 1, v_a_950_);
lean_ctor_set(v___x_955_, 0, v___x_957_);
v___x_959_ = v___x_955_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v___x_957_);
lean_ctor_set(v_reuseFailAlloc_961_, 1, v_a_950_);
v___x_959_ = v_reuseFailAlloc_961_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
v_a_949_ = v_tail_953_;
v_a_950_ = v___x_959_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__0(void){
_start:
{
lean_object* v___x_963_; 
v___x_963_ = l_instMonadEIO(lean_box(0));
return v___x_963_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__5(void){
_start:
{
lean_object* v___x_968_; 
v___x_968_ = l_Array_instInhabited(lean_box(0));
return v___x_968_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg(lean_object* v_msg_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_){
_start:
{
lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v_toApplicative_977_; lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_1038_; 
v___x_975_ = lean_obj_once(&l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__0, &l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__0_once, _init_l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__0);
v___x_976_ = l_StateRefT_x27_instMonad___redArg(v___x_975_);
v_toApplicative_977_ = lean_ctor_get(v___x_976_, 0);
v_isSharedCheck_1038_ = !lean_is_exclusive(v___x_976_);
if (v_isSharedCheck_1038_ == 0)
{
lean_object* v_unused_1039_; 
v_unused_1039_ = lean_ctor_get(v___x_976_, 1);
lean_dec(v_unused_1039_);
v___x_979_ = v___x_976_;
v_isShared_980_ = v_isSharedCheck_1038_;
goto v_resetjp_978_;
}
else
{
lean_inc(v_toApplicative_977_);
lean_dec(v___x_976_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_1038_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v_toFunctor_981_; lean_object* v_toSeq_982_; lean_object* v_toSeqLeft_983_; lean_object* v_toSeqRight_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_1036_; 
v_toFunctor_981_ = lean_ctor_get(v_toApplicative_977_, 0);
v_toSeq_982_ = lean_ctor_get(v_toApplicative_977_, 2);
v_toSeqLeft_983_ = lean_ctor_get(v_toApplicative_977_, 3);
v_toSeqRight_984_ = lean_ctor_get(v_toApplicative_977_, 4);
v_isSharedCheck_1036_ = !lean_is_exclusive(v_toApplicative_977_);
if (v_isSharedCheck_1036_ == 0)
{
lean_object* v_unused_1037_; 
v_unused_1037_ = lean_ctor_get(v_toApplicative_977_, 1);
lean_dec(v_unused_1037_);
v___x_986_ = v_toApplicative_977_;
v_isShared_987_ = v_isSharedCheck_1036_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_toSeqRight_984_);
lean_inc(v_toSeqLeft_983_);
lean_inc(v_toSeq_982_);
lean_inc(v_toFunctor_981_);
lean_dec(v_toApplicative_977_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_1036_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v___f_988_; lean_object* v___f_989_; lean_object* v___f_990_; lean_object* v___f_991_; lean_object* v___x_992_; lean_object* v___f_993_; lean_object* v___f_994_; lean_object* v___f_995_; lean_object* v___x_997_; 
v___f_988_ = ((lean_object*)(l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__1));
v___f_989_ = ((lean_object*)(l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__2));
lean_inc_ref(v_toFunctor_981_);
v___f_990_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_990_, 0, v_toFunctor_981_);
v___f_991_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_991_, 0, v_toFunctor_981_);
v___x_992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_992_, 0, v___f_990_);
lean_ctor_set(v___x_992_, 1, v___f_991_);
v___f_993_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_993_, 0, v_toSeqRight_984_);
v___f_994_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_994_, 0, v_toSeqLeft_983_);
v___f_995_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_995_, 0, v_toSeq_982_);
if (v_isShared_987_ == 0)
{
lean_ctor_set(v___x_986_, 4, v___f_993_);
lean_ctor_set(v___x_986_, 3, v___f_994_);
lean_ctor_set(v___x_986_, 2, v___f_995_);
lean_ctor_set(v___x_986_, 1, v___f_988_);
lean_ctor_set(v___x_986_, 0, v___x_992_);
v___x_997_ = v___x_986_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v___x_992_);
lean_ctor_set(v_reuseFailAlloc_1035_, 1, v___f_988_);
lean_ctor_set(v_reuseFailAlloc_1035_, 2, v___f_995_);
lean_ctor_set(v_reuseFailAlloc_1035_, 3, v___f_994_);
lean_ctor_set(v_reuseFailAlloc_1035_, 4, v___f_993_);
v___x_997_ = v_reuseFailAlloc_1035_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
lean_object* v___x_999_; 
if (v_isShared_980_ == 0)
{
lean_ctor_set(v___x_979_, 1, v___f_989_);
lean_ctor_set(v___x_979_, 0, v___x_997_);
v___x_999_ = v___x_979_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v___x_997_);
lean_ctor_set(v_reuseFailAlloc_1034_, 1, v___f_989_);
v___x_999_ = v_reuseFailAlloc_1034_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
lean_object* v___x_1000_; lean_object* v_toApplicative_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1032_; 
v___x_1000_ = l_StateRefT_x27_instMonad___redArg(v___x_999_);
v_toApplicative_1001_ = lean_ctor_get(v___x_1000_, 0);
v_isSharedCheck_1032_ = !lean_is_exclusive(v___x_1000_);
if (v_isSharedCheck_1032_ == 0)
{
lean_object* v_unused_1033_; 
v_unused_1033_ = lean_ctor_get(v___x_1000_, 1);
lean_dec(v_unused_1033_);
v___x_1003_ = v___x_1000_;
v_isShared_1004_ = v_isSharedCheck_1032_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_toApplicative_1001_);
lean_dec(v___x_1000_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1032_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v_toFunctor_1005_; lean_object* v_toSeq_1006_; lean_object* v_toSeqLeft_1007_; lean_object* v_toSeqRight_1008_; lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1030_; 
v_toFunctor_1005_ = lean_ctor_get(v_toApplicative_1001_, 0);
v_toSeq_1006_ = lean_ctor_get(v_toApplicative_1001_, 2);
v_toSeqLeft_1007_ = lean_ctor_get(v_toApplicative_1001_, 3);
v_toSeqRight_1008_ = lean_ctor_get(v_toApplicative_1001_, 4);
v_isSharedCheck_1030_ = !lean_is_exclusive(v_toApplicative_1001_);
if (v_isSharedCheck_1030_ == 0)
{
lean_object* v_unused_1031_; 
v_unused_1031_ = lean_ctor_get(v_toApplicative_1001_, 1);
lean_dec(v_unused_1031_);
v___x_1010_ = v_toApplicative_1001_;
v_isShared_1011_ = v_isSharedCheck_1030_;
goto v_resetjp_1009_;
}
else
{
lean_inc(v_toSeqRight_1008_);
lean_inc(v_toSeqLeft_1007_);
lean_inc(v_toSeq_1006_);
lean_inc(v_toFunctor_1005_);
lean_dec(v_toApplicative_1001_);
v___x_1010_ = lean_box(0);
v_isShared_1011_ = v_isSharedCheck_1030_;
goto v_resetjp_1009_;
}
v_resetjp_1009_:
{
lean_object* v___f_1012_; lean_object* v___f_1013_; lean_object* v___f_1014_; lean_object* v___f_1015_; lean_object* v___x_1016_; lean_object* v___f_1017_; lean_object* v___f_1018_; lean_object* v___f_1019_; lean_object* v___x_1021_; 
v___f_1012_ = ((lean_object*)(l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__3));
v___f_1013_ = ((lean_object*)(l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__4));
lean_inc_ref(v_toFunctor_1005_);
v___f_1014_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1014_, 0, v_toFunctor_1005_);
v___f_1015_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1015_, 0, v_toFunctor_1005_);
v___x_1016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1016_, 0, v___f_1014_);
lean_ctor_set(v___x_1016_, 1, v___f_1015_);
v___f_1017_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1017_, 0, v_toSeqRight_1008_);
v___f_1018_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1018_, 0, v_toSeqLeft_1007_);
v___f_1019_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1019_, 0, v_toSeq_1006_);
if (v_isShared_1011_ == 0)
{
lean_ctor_set(v___x_1010_, 4, v___f_1017_);
lean_ctor_set(v___x_1010_, 3, v___f_1018_);
lean_ctor_set(v___x_1010_, 2, v___f_1019_);
lean_ctor_set(v___x_1010_, 1, v___f_1012_);
lean_ctor_set(v___x_1010_, 0, v___x_1016_);
v___x_1021_ = v___x_1010_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v___x_1016_);
lean_ctor_set(v_reuseFailAlloc_1029_, 1, v___f_1012_);
lean_ctor_set(v_reuseFailAlloc_1029_, 2, v___f_1019_);
lean_ctor_set(v_reuseFailAlloc_1029_, 3, v___f_1018_);
lean_ctor_set(v_reuseFailAlloc_1029_, 4, v___f_1017_);
v___x_1021_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
lean_object* v___x_1023_; 
if (v_isShared_1004_ == 0)
{
lean_ctor_set(v___x_1003_, 1, v___f_1013_);
lean_ctor_set(v___x_1003_, 0, v___x_1021_);
v___x_1023_ = v___x_1003_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v___x_1021_);
lean_ctor_set(v_reuseFailAlloc_1028_, 1, v___f_1013_);
v___x_1023_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_21492__overap_1026_; lean_object* v___x_1027_; 
v___x_1024_ = lean_obj_once(&l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__5, &l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__5_once, _init_l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__5);
v___x_1025_ = l_instInhabitedOfMonad___redArg(v___x_1023_, v___x_1024_);
v___x_21492__overap_1026_ = lean_panic_fn_borrowed(v___x_1025_, v_msg_969_);
lean_dec(v___x_1025_);
lean_inc(v___y_973_);
lean_inc_ref(v___y_972_);
lean_inc(v___y_971_);
lean_inc_ref(v___y_970_);
v___x_1027_ = lean_apply_5(v___x_21492__overap_1026_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, lean_box(0));
return v___x_1027_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___boxed(lean_object* v_msg_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_){
_start:
{
lean_object* v_res_1046_; 
v_res_1046_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg(v_msg_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_);
lean_dec(v___y_1044_);
lean_dec_ref(v___y_1043_);
lean_dec(v___y_1042_);
lean_dec_ref(v___y_1041_);
return v_res_1046_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__13(lean_object* v_xs_1047_, size_t v_sz_1048_, size_t v_i_1049_, lean_object* v_bs_1050_){
_start:
{
uint8_t v___x_1051_; 
v___x_1051_ = lean_usize_dec_lt(v_i_1049_, v_sz_1048_);
if (v___x_1051_ == 0)
{
return v_bs_1050_;
}
else
{
lean_object* v___x_1052_; lean_object* v_v_1053_; lean_object* v___x_1054_; lean_object* v_bs_x27_1055_; lean_object* v___x_1056_; size_t v___x_1057_; size_t v___x_1058_; lean_object* v___x_1059_; 
v___x_1052_ = l_Lean_instInhabitedExpr;
v_v_1053_ = lean_array_uget(v_bs_1050_, v_i_1049_);
v___x_1054_ = lean_unsigned_to_nat(0u);
v_bs_x27_1055_ = lean_array_uset(v_bs_1050_, v_i_1049_, v___x_1054_);
v___x_1056_ = lean_array_get_borrowed(v___x_1052_, v_xs_1047_, v_v_1053_);
lean_dec(v_v_1053_);
v___x_1057_ = ((size_t)1ULL);
v___x_1058_ = lean_usize_add(v_i_1049_, v___x_1057_);
lean_inc(v___x_1056_);
v___x_1059_ = lean_array_uset(v_bs_x27_1055_, v_i_1049_, v___x_1056_);
v_i_1049_ = v___x_1058_;
v_bs_1050_ = v___x_1059_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__13___boxed(lean_object* v_xs_1061_, lean_object* v_sz_1062_, lean_object* v_i_1063_, lean_object* v_bs_1064_){
_start:
{
size_t v_sz_boxed_1065_; size_t v_i_boxed_1066_; lean_object* v_res_1067_; 
v_sz_boxed_1065_ = lean_unbox_usize(v_sz_1062_);
lean_dec(v_sz_1062_);
v_i_boxed_1066_ = lean_unbox_usize(v_i_1063_);
lean_dec(v_i_1063_);
v_res_1067_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__13(v_xs_1061_, v_sz_boxed_1065_, v_i_boxed_1066_, v_bs_1064_);
lean_dec_ref(v_xs_1061_);
return v_res_1067_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15___redArg(lean_object* v_xs_1068_, lean_object* v_f_1069_, lean_object* v_as_1070_, lean_object* v_bs_1071_, lean_object* v_i_1072_, lean_object* v_cs_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_){
_start:
{
lean_object* v___x_1079_; uint8_t v___x_1080_; 
v___x_1079_ = lean_array_get_size(v_as_1070_);
v___x_1080_ = lean_nat_dec_lt(v_i_1072_, v___x_1079_);
if (v___x_1080_ == 0)
{
lean_object* v___x_1081_; 
lean_dec(v_i_1072_);
lean_dec_ref(v_f_1069_);
v___x_1081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1081_, 0, v_cs_1073_);
return v___x_1081_;
}
else
{
lean_object* v___x_1082_; uint8_t v___x_1083_; 
v___x_1082_ = lean_array_get_size(v_bs_1071_);
v___x_1083_ = lean_nat_dec_lt(v_i_1072_, v___x_1082_);
if (v___x_1083_ == 0)
{
lean_object* v___x_1084_; 
lean_dec(v_i_1072_);
lean_dec_ref(v_f_1069_);
v___x_1084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1084_, 0, v_cs_1073_);
return v___x_1084_;
}
else
{
lean_object* v_a_1085_; lean_object* v_b_1086_; size_t v_sz_1087_; size_t v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; 
v_a_1085_ = lean_array_fget_borrowed(v_as_1070_, v_i_1072_);
v_b_1086_ = lean_array_fget_borrowed(v_bs_1071_, v_i_1072_);
v_sz_1087_ = lean_array_size(v_b_1086_);
v___x_1088_ = ((size_t)0ULL);
lean_inc(v_b_1086_);
v___x_1089_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__13(v_xs_1068_, v_sz_1087_, v___x_1088_, v_b_1086_);
lean_inc_ref(v_f_1069_);
lean_inc(v___y_1077_);
lean_inc_ref(v___y_1076_);
lean_inc(v___y_1075_);
lean_inc_ref(v___y_1074_);
lean_inc(v_a_1085_);
v___x_1090_ = lean_apply_7(v_f_1069_, v_a_1085_, v___x_1089_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, lean_box(0));
if (lean_obj_tag(v___x_1090_) == 0)
{
lean_object* v_a_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; 
v_a_1091_ = lean_ctor_get(v___x_1090_, 0);
lean_inc(v_a_1091_);
lean_dec_ref_known(v___x_1090_, 1);
v___x_1092_ = lean_unsigned_to_nat(1u);
v___x_1093_ = lean_nat_add(v_i_1072_, v___x_1092_);
lean_dec(v_i_1072_);
v___x_1094_ = lean_array_push(v_cs_1073_, v_a_1091_);
v_i_1072_ = v___x_1093_;
v_cs_1073_ = v___x_1094_;
goto _start;
}
else
{
lean_object* v_a_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1103_; 
lean_dec_ref(v_cs_1073_);
lean_dec(v_i_1072_);
lean_dec_ref(v_f_1069_);
v_a_1096_ = lean_ctor_get(v___x_1090_, 0);
v_isSharedCheck_1103_ = !lean_is_exclusive(v___x_1090_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1098_ = v___x_1090_;
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_a_1096_);
lean_dec(v___x_1090_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v___x_1101_; 
if (v_isShared_1099_ == 0)
{
v___x_1101_ = v___x_1098_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v_a_1096_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
return v___x_1101_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15___redArg___boxed(lean_object* v_xs_1104_, lean_object* v_f_1105_, lean_object* v_as_1106_, lean_object* v_bs_1107_, lean_object* v_i_1108_, lean_object* v_cs_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_){
_start:
{
lean_object* v_res_1115_; 
v_res_1115_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15___redArg(v_xs_1104_, v_f_1105_, v_as_1106_, v_bs_1107_, v_i_1108_, v_cs_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_);
lean_dec(v___y_1113_);
lean_dec_ref(v___y_1112_);
lean_dec(v___y_1111_);
lean_dec_ref(v___y_1110_);
lean_dec_ref(v_bs_1107_);
lean_dec_ref(v_as_1106_);
lean_dec_ref(v_xs_1104_);
return v_res_1115_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; 
v___x_1119_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__2));
v___x_1120_ = lean_unsigned_to_nat(2u);
v___x_1121_ = lean_unsigned_to_nat(73u);
v___x_1122_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__1));
v___x_1123_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__0));
v___x_1124_ = l_mkPanicMessageWithDecl(v___x_1123_, v___x_1122_, v___x_1121_, v___x_1120_, v___x_1119_);
return v___x_1124_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; 
v___x_1126_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__4));
v___x_1127_ = lean_unsigned_to_nat(2u);
v___x_1128_ = lean_unsigned_to_nat(74u);
v___x_1129_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__1));
v___x_1130_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__0));
v___x_1131_ = l_mkPanicMessageWithDecl(v___x_1130_, v___x_1129_, v___x_1128_, v___x_1127_, v___x_1126_);
return v___x_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg(lean_object* v_f_1134_, lean_object* v_positions_1135_, lean_object* v_ys_1136_, lean_object* v_xs_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_){
_start:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; uint8_t v___x_1145_; 
v___x_1143_ = lean_array_get_size(v_positions_1135_);
v___x_1144_ = lean_array_get_size(v_ys_1136_);
v___x_1145_ = lean_nat_dec_eq(v___x_1143_, v___x_1144_);
if (v___x_1145_ == 0)
{
lean_object* v___x_1146_; lean_object* v___x_1147_; 
lean_dec_ref(v_f_1134_);
v___x_1146_ = lean_obj_once(&l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__3, &l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__3_once, _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__3);
v___x_1147_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg(v___x_1146_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_);
return v___x_1147_;
}
else
{
lean_object* v___x_1148_; lean_object* v___x_1149_; uint8_t v___x_1150_; 
v___x_1148_ = l_Lean_Elab_Structural_Positions_numIndices(v_positions_1135_);
v___x_1149_ = lean_array_get_size(v_xs_1137_);
v___x_1150_ = lean_nat_dec_eq(v___x_1148_, v___x_1149_);
lean_dec(v___x_1148_);
if (v___x_1150_ == 0)
{
lean_object* v___x_1151_; lean_object* v___x_1152_; 
lean_dec_ref(v_f_1134_);
v___x_1151_ = lean_obj_once(&l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__5, &l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__5_once, _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__5);
v___x_1152_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg(v___x_1151_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_);
return v___x_1152_;
}
else
{
lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; 
v___x_1153_ = lean_unsigned_to_nat(0u);
v___x_1154_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__6));
v___x_1155_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15___redArg(v_xs_1137_, v_f_1134_, v_ys_1136_, v_positions_1135_, v___x_1153_, v___x_1154_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_);
return v___x_1155_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___boxed(lean_object* v_f_1156_, lean_object* v_positions_1157_, lean_object* v_ys_1158_, lean_object* v_xs_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_){
_start:
{
lean_object* v_res_1165_; 
v_res_1165_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg(v_f_1156_, v_positions_1157_, v_ys_1158_, v_xs_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_);
lean_dec(v___y_1163_);
lean_dec_ref(v___y_1162_);
lean_dec(v___y_1161_);
lean_dec_ref(v___y_1160_);
lean_dec_ref(v_xs_1159_);
lean_dec_ref(v_ys_1158_);
lean_dec_ref(v_positions_1157_);
return v_res_1165_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg(lean_object* v___x_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_, lean_object* v_funTypes_1169_, size_t v_sz_1170_, size_t v_i_1171_, lean_object* v_bs_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_){
_start:
{
uint8_t v___x_1178_; 
v___x_1178_ = lean_usize_dec_lt(v_i_1171_, v_sz_1170_);
if (v___x_1178_ == 0)
{
lean_object* v___x_1179_; 
lean_dec_ref(v_funTypes_1169_);
lean_dec_ref(v_a_1168_);
lean_dec_ref(v_a_1167_);
lean_dec_ref(v___x_1166_);
v___x_1179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1179_, 0, v_bs_1172_);
return v___x_1179_;
}
else
{
lean_object* v_v_1180_; lean_object* v_fst_1181_; lean_object* v_snd_1182_; lean_object* v___x_1183_; lean_object* v_bs_x27_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; 
v_v_1180_ = lean_array_uget_borrowed(v_bs_1172_, v_i_1171_);
v_fst_1181_ = lean_ctor_get(v_v_1180_, 0);
lean_inc(v_fst_1181_);
v_snd_1182_ = lean_ctor_get(v_v_1180_, 1);
lean_inc(v_snd_1182_);
v___x_1183_ = lean_unsigned_to_nat(0u);
v_bs_x27_1184_ = lean_array_uset(v_bs_1172_, v_i_1171_, v___x_1183_);
v___x_1185_ = lean_usize_to_nat(v_i_1171_);
lean_inc_ref(v_funTypes_1169_);
lean_inc_ref(v_a_1168_);
lean_inc_ref(v_a_1167_);
lean_inc_ref(v___x_1166_);
v___x_1186_ = l_Lean_Elab_Structural_mkBRecOnApp(v___x_1166_, v___x_1185_, v_a_1167_, v_a_1168_, v_funTypes_1169_, v_fst_1181_, v_snd_1182_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_);
if (lean_obj_tag(v___x_1186_) == 0)
{
lean_object* v_a_1187_; size_t v___x_1188_; size_t v___x_1189_; lean_object* v___x_1190_; 
v_a_1187_ = lean_ctor_get(v___x_1186_, 0);
lean_inc(v_a_1187_);
lean_dec_ref_known(v___x_1186_, 1);
v___x_1188_ = ((size_t)1ULL);
v___x_1189_ = lean_usize_add(v_i_1171_, v___x_1188_);
v___x_1190_ = lean_array_uset(v_bs_x27_1184_, v_i_1171_, v_a_1187_);
v_i_1171_ = v___x_1189_;
v_bs_1172_ = v___x_1190_;
goto _start;
}
else
{
lean_object* v_a_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1199_; 
lean_dec_ref(v_bs_x27_1184_);
lean_dec_ref(v_funTypes_1169_);
lean_dec_ref(v_a_1168_);
lean_dec_ref(v_a_1167_);
lean_dec_ref(v___x_1166_);
v_a_1192_ = lean_ctor_get(v___x_1186_, 0);
v_isSharedCheck_1199_ = !lean_is_exclusive(v___x_1186_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1194_ = v___x_1186_;
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_a_1192_);
lean_dec(v___x_1186_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v___x_1197_; 
if (v_isShared_1195_ == 0)
{
v___x_1197_ = v___x_1194_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v_a_1192_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg___boxed(lean_object* v___x_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_funTypes_1203_, lean_object* v_sz_1204_, lean_object* v_i_1205_, lean_object* v_bs_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_){
_start:
{
size_t v_sz_boxed_1212_; size_t v_i_boxed_1213_; lean_object* v_res_1214_; 
v_sz_boxed_1212_ = lean_unbox_usize(v_sz_1204_);
lean_dec(v_sz_1204_);
v_i_boxed_1213_ = lean_unbox_usize(v_i_1205_);
lean_dec(v_i_1205_);
v_res_1214_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg(v___x_1200_, v_a_1201_, v_a_1202_, v_funTypes_1203_, v_sz_boxed_1212_, v_i_boxed_1213_, v_bs_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_);
lean_dec(v___y_1210_);
lean_dec_ref(v___y_1209_);
lean_dec(v___y_1208_);
lean_dec_ref(v___y_1207_);
return v_res_1214_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__2(void){
_start:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1218_ = lean_box(0);
v___x_1219_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__1));
v___x_1220_ = l_Lean_Expr_const___override(v___x_1219_, v___x_1218_);
return v___x_1220_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__4(void){
_start:
{
lean_object* v___x_1222_; lean_object* v___x_1223_; 
v___x_1222_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__3));
v___x_1223_ = l_Lean_stringToMessageData(v___x_1222_);
return v___x_1223_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__6(void){
_start:
{
lean_object* v___x_1225_; lean_object* v___x_1226_; 
v___x_1225_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__5));
v___x_1226_ = l_Lean_stringToMessageData(v___x_1225_);
return v___x_1226_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__8(void){
_start:
{
lean_object* v___x_1228_; lean_object* v___x_1229_; 
v___x_1228_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__7));
v___x_1229_ = l_Lean_stringToMessageData(v___x_1228_);
return v___x_1229_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__10(void){
_start:
{
lean_object* v___x_1231_; lean_object* v___x_1232_; 
v___x_1231_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__9));
v___x_1232_ = l_Lean_stringToMessageData(v___x_1231_);
return v___x_1232_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__12(void){
_start:
{
lean_object* v___x_1234_; lean_object* v___x_1235_; 
v___x_1234_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__11));
v___x_1235_ = l_Lean_stringToMessageData(v___x_1234_);
return v___x_1235_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2(lean_object* v___f_1236_, lean_object* v_recArgInfos_1237_, lean_object* v_a_1238_, lean_object* v___x_1239_, size_t v___x_1240_, lean_object* v_fixedParamPerms_1241_, lean_object* v_xs_1242_, lean_object* v___x_1243_, lean_object* v_preDefs_1244_, lean_object* v_numIndices_1245_, lean_object* v___f_1246_, lean_object* v___x_1247_, uint8_t v_a_1248_, lean_object* v___x_1249_, lean_object* v_funTypes_1250_, lean_object* v_motives_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_){
_start:
{
lean_object* v___y_1258_; lean_object* v___y_1259_; lean_object* v___y_1260_; lean_object* v___y_1261_; lean_object* v___y_1262_; lean_object* v___y_1263_; lean_object* v___y_1298_; lean_object* v_FArgs_1299_; lean_object* v___y_1300_; lean_object* v___y_1301_; lean_object* v___y_1302_; lean_object* v___y_1303_; lean_object* v___y_1355_; lean_object* v___y_1356_; lean_object* v___y_1357_; lean_object* v___y_1358_; lean_object* v___y_1359_; lean_object* v___y_1360_; lean_object* v___y_1377_; lean_object* v___y_1378_; lean_object* v___y_1379_; lean_object* v___y_1380_; lean_object* v___y_1381_; lean_object* v___y_1382_; lean_object* v___y_1421_; lean_object* v___y_1422_; lean_object* v___y_1423_; lean_object* v___y_1424_; lean_object* v___x_1471_; 
lean_inc_ref(v___f_1236_);
lean_inc(v___y_1255_);
lean_inc_ref(v___y_1254_);
lean_inc(v___y_1253_);
lean_inc_ref(v___y_1252_);
v___x_1471_ = lean_apply_5(v___f_1236_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, lean_box(0));
if (lean_obj_tag(v___x_1471_) == 0)
{
lean_object* v_a_1472_; uint8_t v___x_1473_; 
v_a_1472_ = lean_ctor_get(v___x_1471_, 0);
lean_inc(v_a_1472_);
lean_dec_ref_known(v___x_1471_, 1);
v___x_1473_ = lean_unbox(v_a_1472_);
lean_dec(v_a_1472_);
if (v___x_1473_ == 0)
{
v___y_1421_ = v___y_1252_;
v___y_1422_ = v___y_1253_;
v___y_1423_ = v___y_1254_;
v___y_1424_ = v___y_1255_;
goto v___jp_1420_;
}
else
{
lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; 
v___x_1474_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__10, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__10);
lean_inc_ref(v_funTypes_1250_);
v___x_1475_ = lean_array_to_list(v_funTypes_1250_);
v___x_1476_ = lean_box(0);
v___x_1477_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_1475_, v___x_1476_);
v___x_1478_ = l_Lean_MessageData_ofList(v___x_1477_);
v___x_1479_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1479_, 0, v___x_1474_);
lean_ctor_set(v___x_1479_, 1, v___x_1478_);
v___x_1480_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__12, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__12_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__12);
v___x_1481_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1481_, 0, v___x_1479_);
lean_ctor_set(v___x_1481_, 1, v___x_1480_);
lean_inc_ref(v_motives_1251_);
v___x_1482_ = lean_array_to_list(v_motives_1251_);
v___x_1483_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_1482_, v___x_1476_);
v___x_1484_ = l_Lean_MessageData_ofList(v___x_1483_);
v___x_1485_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1485_, 0, v___x_1481_);
lean_ctor_set(v___x_1485_, 1, v___x_1484_);
lean_inc(v___x_1247_);
v___x_1486_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_1247_, v___x_1485_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_);
if (lean_obj_tag(v___x_1486_) == 0)
{
lean_dec_ref_known(v___x_1486_, 1);
v___y_1421_ = v___y_1252_;
v___y_1422_ = v___y_1253_;
v___y_1423_ = v___y_1254_;
v___y_1424_ = v___y_1255_;
goto v___jp_1420_;
}
else
{
lean_object* v_a_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1494_; 
lean_dec_ref(v_motives_1251_);
lean_dec_ref(v_funTypes_1250_);
lean_dec(v___x_1247_);
lean_dec_ref(v___f_1246_);
lean_dec_ref(v_preDefs_1244_);
lean_dec(v___x_1243_);
lean_dec_ref(v_xs_1242_);
lean_dec_ref(v_fixedParamPerms_1241_);
lean_dec_ref(v___x_1239_);
lean_dec_ref(v_recArgInfos_1237_);
lean_dec_ref(v___f_1236_);
v_a_1487_ = lean_ctor_get(v___x_1486_, 0);
v_isSharedCheck_1494_ = !lean_is_exclusive(v___x_1486_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1489_ = v___x_1486_;
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_a_1487_);
lean_dec(v___x_1486_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v___x_1492_; 
if (v_isShared_1490_ == 0)
{
v___x_1492_ = v___x_1489_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v_a_1487_);
v___x_1492_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
return v___x_1492_;
}
}
}
}
}
else
{
lean_object* v_a_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1502_; 
lean_dec_ref(v_motives_1251_);
lean_dec_ref(v_funTypes_1250_);
lean_dec(v___x_1247_);
lean_dec_ref(v___f_1246_);
lean_dec_ref(v_preDefs_1244_);
lean_dec(v___x_1243_);
lean_dec_ref(v_xs_1242_);
lean_dec_ref(v_fixedParamPerms_1241_);
lean_dec_ref(v___x_1239_);
lean_dec_ref(v_recArgInfos_1237_);
lean_dec_ref(v___f_1236_);
v_a_1495_ = lean_ctor_get(v___x_1471_, 0);
v_isSharedCheck_1502_ = !lean_is_exclusive(v___x_1471_);
if (v_isSharedCheck_1502_ == 0)
{
v___x_1497_ = v___x_1471_;
v_isShared_1498_ = v_isSharedCheck_1502_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_a_1495_);
lean_dec(v___x_1471_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1502_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
lean_object* v___x_1500_; 
if (v_isShared_1498_ == 0)
{
v___x_1500_ = v___x_1497_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v_a_1495_);
v___x_1500_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
return v___x_1500_;
}
}
}
v___jp_1257_:
{
lean_object* v___x_1264_; size_t v_sz_1265_; lean_object* v___x_1266_; 
v___x_1264_ = l_Array_zip___redArg(v_recArgInfos_1237_, v_a_1238_);
lean_dec_ref(v_recArgInfos_1237_);
v_sz_1265_ = lean_array_size(v___x_1264_);
v___x_1266_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg(v___x_1239_, v___y_1258_, v___y_1259_, v_funTypes_1250_, v_sz_1265_, v___x_1240_, v___x_1264_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_);
if (lean_obj_tag(v___x_1266_) == 0)
{
lean_object* v_a_1267_; lean_object* v___x_1268_; size_t v_sz_1269_; lean_object* v___x_1270_; 
v_a_1267_ = lean_ctor_get(v___x_1266_, 0);
lean_inc(v_a_1267_);
lean_dec_ref_known(v___x_1266_, 1);
v___x_1268_ = l_Array_zip___redArg(v_a_1238_, v_a_1267_);
lean_dec(v_a_1267_);
v_sz_1269_ = lean_array_size(v___x_1268_);
v___x_1270_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg(v_fixedParamPerms_1241_, v_xs_1242_, v_sz_1269_, v___x_1240_, v___x_1268_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_);
if (lean_obj_tag(v___x_1270_) == 0)
{
lean_object* v_a_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1280_; 
v_a_1271_ = lean_ctor_get(v___x_1270_, 0);
v_isSharedCheck_1280_ = !lean_is_exclusive(v___x_1270_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1273_ = v___x_1270_;
v_isShared_1274_ = v_isSharedCheck_1280_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_a_1271_);
lean_dec(v___x_1270_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1280_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1278_; 
v___x_1275_ = lean_mk_empty_array_with_capacity(v___x_1243_);
v___x_1276_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9(v_preDefs_1244_, v_a_1271_, v___x_1243_, v___x_1275_);
lean_dec(v_a_1271_);
lean_dec_ref(v_preDefs_1244_);
if (v_isShared_1274_ == 0)
{
lean_ctor_set(v___x_1273_, 0, v___x_1276_);
v___x_1278_ = v___x_1273_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v___x_1276_);
v___x_1278_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
return v___x_1278_;
}
}
}
else
{
lean_object* v_a_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1288_; 
lean_dec_ref(v_preDefs_1244_);
lean_dec(v___x_1243_);
v_a_1281_ = lean_ctor_get(v___x_1270_, 0);
v_isSharedCheck_1288_ = !lean_is_exclusive(v___x_1270_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1283_ = v___x_1270_;
v_isShared_1284_ = v_isSharedCheck_1288_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_a_1281_);
lean_dec(v___x_1270_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1288_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v___x_1286_; 
if (v_isShared_1284_ == 0)
{
v___x_1286_ = v___x_1283_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v_a_1281_);
v___x_1286_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
return v___x_1286_;
}
}
}
}
else
{
lean_object* v_a_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1296_; 
lean_dec_ref(v_preDefs_1244_);
lean_dec(v___x_1243_);
lean_dec_ref(v_xs_1242_);
lean_dec_ref(v_fixedParamPerms_1241_);
v_a_1289_ = lean_ctor_get(v___x_1266_, 0);
v_isSharedCheck_1296_ = !lean_is_exclusive(v___x_1266_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1291_ = v___x_1266_;
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_a_1289_);
lean_dec(v___x_1266_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
lean_object* v___x_1294_; 
if (v_isShared_1292_ == 0)
{
v___x_1294_ = v___x_1291_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v_a_1289_);
v___x_1294_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
return v___x_1294_;
}
}
}
}
v___jp_1297_:
{
lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; 
lean_inc_ref(v___y_1298_);
lean_inc(v___x_1243_);
v___x_1304_ = lean_apply_1(v___y_1298_, v___x_1243_);
v___x_1305_ = lean_unsigned_to_nat(1u);
v___x_1306_ = lean_nat_add(v_numIndices_1245_, v___x_1305_);
v___x_1307_ = lean_box(0);
v___x_1308_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__2);
v___x_1309_ = lean_mk_array(v___x_1306_, v___x_1308_);
v___x_1310_ = l_Lean_mkAppN(v___x_1304_, v___x_1309_);
lean_dec_ref(v___x_1309_);
v___x_1311_ = lean_array_get_size(v___x_1239_);
v___x_1312_ = l_Lean_Meta_inferArgumentTypesN(v___x_1311_, v___x_1310_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_);
if (lean_obj_tag(v___x_1312_) == 0)
{
lean_object* v_a_1313_; lean_object* v___x_1314_; 
v_a_1313_ = lean_ctor_get(v___x_1312_, 0);
lean_inc(v_a_1313_);
lean_dec_ref_known(v___x_1312_, 1);
v___x_1314_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg(v___f_1246_, v___x_1239_, v_a_1313_, v_FArgs_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_);
lean_dec_ref(v_FArgs_1299_);
lean_dec(v_a_1313_);
if (lean_obj_tag(v___x_1314_) == 0)
{
lean_object* v_toCold_1315_; lean_object* v_options_1316_; uint8_t v_hasTrace_1317_; 
v_toCold_1315_ = lean_ctor_get(v___y_1302_, 0);
v_options_1316_ = lean_ctor_get(v_toCold_1315_, 2);
v_hasTrace_1317_ = lean_ctor_get_uint8(v_options_1316_, sizeof(void*)*1);
if (v_hasTrace_1317_ == 0)
{
lean_object* v_a_1318_; 
lean_dec(v___x_1247_);
v_a_1318_ = lean_ctor_get(v___x_1314_, 0);
lean_inc(v_a_1318_);
lean_dec_ref_known(v___x_1314_, 1);
v___y_1258_ = v___y_1298_;
v___y_1259_ = v_a_1318_;
v___y_1260_ = v___y_1300_;
v___y_1261_ = v___y_1301_;
v___y_1262_ = v___y_1302_;
v___y_1263_ = v___y_1303_;
goto v___jp_1257_;
}
else
{
lean_object* v_a_1319_; lean_object* v_inheritedTraceOptions_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; uint8_t v___x_1323_; 
v_a_1319_ = lean_ctor_get(v___x_1314_, 0);
lean_inc(v_a_1319_);
lean_dec_ref_known(v___x_1314_, 1);
v_inheritedTraceOptions_1320_ = lean_ctor_get(v_toCold_1315_, 11);
v___x_1321_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0___closed__1));
lean_inc(v___x_1247_);
v___x_1322_ = l_Lean_Name_append(v___x_1321_, v___x_1247_);
v___x_1323_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1320_, v_options_1316_, v___x_1322_);
lean_dec(v___x_1322_);
if (v___x_1323_ == 0)
{
lean_dec(v___x_1247_);
v___y_1258_ = v___y_1298_;
v___y_1259_ = v_a_1319_;
v___y_1260_ = v___y_1300_;
v___y_1261_ = v___y_1301_;
v___y_1262_ = v___y_1302_;
v___y_1263_ = v___y_1303_;
goto v___jp_1257_;
}
else
{
lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; 
v___x_1324_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__4);
lean_inc(v_a_1319_);
v___x_1325_ = lean_array_to_list(v_a_1319_);
v___x_1326_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_1325_, v___x_1307_);
v___x_1327_ = l_Lean_MessageData_ofList(v___x_1326_);
v___x_1328_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1328_, 0, v___x_1324_);
lean_ctor_set(v___x_1328_, 1, v___x_1327_);
v___x_1329_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_1247_, v___x_1328_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_);
if (lean_obj_tag(v___x_1329_) == 0)
{
lean_dec_ref_known(v___x_1329_, 1);
v___y_1258_ = v___y_1298_;
v___y_1259_ = v_a_1319_;
v___y_1260_ = v___y_1300_;
v___y_1261_ = v___y_1301_;
v___y_1262_ = v___y_1302_;
v___y_1263_ = v___y_1303_;
goto v___jp_1257_;
}
else
{
lean_object* v_a_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1337_; 
lean_dec(v_a_1319_);
lean_dec_ref(v___y_1298_);
lean_dec_ref(v_funTypes_1250_);
lean_dec_ref(v_preDefs_1244_);
lean_dec(v___x_1243_);
lean_dec_ref(v_xs_1242_);
lean_dec_ref(v_fixedParamPerms_1241_);
lean_dec_ref(v___x_1239_);
lean_dec_ref(v_recArgInfos_1237_);
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
}
else
{
lean_object* v_a_1338_; lean_object* v___x_1340_; uint8_t v_isShared_1341_; uint8_t v_isSharedCheck_1345_; 
lean_dec_ref(v___y_1298_);
lean_dec_ref(v_funTypes_1250_);
lean_dec(v___x_1247_);
lean_dec_ref(v_preDefs_1244_);
lean_dec(v___x_1243_);
lean_dec_ref(v_xs_1242_);
lean_dec_ref(v_fixedParamPerms_1241_);
lean_dec_ref(v___x_1239_);
lean_dec_ref(v_recArgInfos_1237_);
v_a_1338_ = lean_ctor_get(v___x_1314_, 0);
v_isSharedCheck_1345_ = !lean_is_exclusive(v___x_1314_);
if (v_isSharedCheck_1345_ == 0)
{
v___x_1340_ = v___x_1314_;
v_isShared_1341_ = v_isSharedCheck_1345_;
goto v_resetjp_1339_;
}
else
{
lean_inc(v_a_1338_);
lean_dec(v___x_1314_);
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
lean_dec_ref(v_FArgs_1299_);
lean_dec_ref(v___y_1298_);
lean_dec_ref(v_funTypes_1250_);
lean_dec(v___x_1247_);
lean_dec_ref(v___f_1246_);
lean_dec_ref(v_preDefs_1244_);
lean_dec(v___x_1243_);
lean_dec_ref(v_xs_1242_);
lean_dec_ref(v_fixedParamPerms_1241_);
lean_dec_ref(v___x_1239_);
lean_dec_ref(v_recArgInfos_1237_);
v_a_1346_ = lean_ctor_get(v___x_1312_, 0);
v_isSharedCheck_1353_ = !lean_is_exclusive(v___x_1312_);
if (v_isSharedCheck_1353_ == 0)
{
v___x_1348_ = v___x_1312_;
v_isShared_1349_ = v_isSharedCheck_1353_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_a_1346_);
lean_dec(v___x_1312_);
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
if (v_a_1248_ == 0)
{
lean_object* v___x_1361_; lean_object* v_levelParams_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; size_t v_sz_1365_; lean_object* v___x_1366_; 
v___x_1361_ = lean_array_get_borrowed(v___x_1249_, v_preDefs_1244_, v___x_1243_);
v_levelParams_1362_ = lean_ctor_get(v___x_1361_, 1);
v___x_1363_ = lean_box(0);
lean_inc(v_levelParams_1362_);
v___x_1364_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__15(v_levelParams_1362_, v___x_1363_);
v_sz_1365_ = lean_array_size(v___y_1356_);
v___x_1366_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg(v_xs_1242_, v_a_1248_, v_preDefs_1244_, v___x_1364_, v_sz_1365_, v___x_1240_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_);
if (lean_obj_tag(v___x_1366_) == 0)
{
lean_object* v_a_1367_; 
v_a_1367_ = lean_ctor_get(v___x_1366_, 0);
lean_inc(v_a_1367_);
lean_dec_ref_known(v___x_1366_, 1);
v___y_1298_ = v___y_1355_;
v_FArgs_1299_ = v_a_1367_;
v___y_1300_ = v___y_1357_;
v___y_1301_ = v___y_1358_;
v___y_1302_ = v___y_1359_;
v___y_1303_ = v___y_1360_;
goto v___jp_1297_;
}
else
{
lean_object* v_a_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1375_; 
lean_dec_ref(v___y_1355_);
lean_dec_ref(v_funTypes_1250_);
lean_dec(v___x_1247_);
lean_dec_ref(v___f_1246_);
lean_dec_ref(v_preDefs_1244_);
lean_dec(v___x_1243_);
lean_dec_ref(v_xs_1242_);
lean_dec_ref(v_fixedParamPerms_1241_);
lean_dec_ref(v___x_1239_);
lean_dec_ref(v_recArgInfos_1237_);
v_a_1368_ = lean_ctor_get(v___x_1366_, 0);
v_isSharedCheck_1375_ = !lean_is_exclusive(v___x_1366_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1370_ = v___x_1366_;
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_a_1368_);
lean_dec(v___x_1366_);
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
v___y_1298_ = v___y_1355_;
v_FArgs_1299_ = v___y_1356_;
v___y_1300_ = v___y_1357_;
v___y_1301_ = v___y_1358_;
v___y_1302_ = v___y_1359_;
v___y_1303_ = v___y_1360_;
goto v___jp_1297_;
}
}
v___jp_1376_:
{
size_t v_sz_1383_; lean_object* v___x_1384_; 
v_sz_1383_ = lean_array_size(v_recArgInfos_1237_);
lean_inc_ref(v___y_1377_);
lean_inc_ref(v_preDefs_1244_);
lean_inc_ref(v___x_1239_);
lean_inc_ref_n(v_recArgInfos_1237_, 2);
v___x_1384_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg(v_a_1248_, v_a_1238_, v___y_1378_, v_recArgInfos_1237_, v___x_1239_, v_preDefs_1244_, v___y_1377_, v_sz_1383_, v___x_1240_, v_recArgInfos_1237_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_);
lean_dec_ref(v___y_1378_);
if (lean_obj_tag(v___x_1384_) == 0)
{
lean_object* v_a_1385_; lean_object* v___x_1386_; 
v_a_1385_ = lean_ctor_get(v___x_1384_, 0);
lean_inc(v_a_1385_);
lean_dec_ref_known(v___x_1384_, 1);
lean_inc(v___y_1382_);
lean_inc_ref(v___y_1381_);
lean_inc(v___y_1380_);
lean_inc_ref(v___y_1379_);
v___x_1386_ = lean_apply_5(v___f_1236_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, lean_box(0));
if (lean_obj_tag(v___x_1386_) == 0)
{
lean_object* v_a_1387_; uint8_t v___x_1388_; 
v_a_1387_ = lean_ctor_get(v___x_1386_, 0);
lean_inc(v_a_1387_);
lean_dec_ref_known(v___x_1386_, 1);
v___x_1388_ = lean_unbox(v_a_1387_);
lean_dec(v_a_1387_);
if (v___x_1388_ == 0)
{
v___y_1355_ = v___y_1377_;
v___y_1356_ = v_a_1385_;
v___y_1357_ = v___y_1379_;
v___y_1358_ = v___y_1380_;
v___y_1359_ = v___y_1381_;
v___y_1360_ = v___y_1382_;
goto v___jp_1354_;
}
else
{
lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; 
v___x_1389_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__6, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__6);
lean_inc(v_a_1385_);
v___x_1390_ = lean_array_to_list(v_a_1385_);
v___x_1391_ = lean_box(0);
v___x_1392_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_1390_, v___x_1391_);
v___x_1393_ = l_Lean_MessageData_ofList(v___x_1392_);
v___x_1394_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1394_, 0, v___x_1389_);
lean_ctor_set(v___x_1394_, 1, v___x_1393_);
lean_inc(v___x_1247_);
v___x_1395_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_1247_, v___x_1394_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_);
if (lean_obj_tag(v___x_1395_) == 0)
{
lean_dec_ref_known(v___x_1395_, 1);
v___y_1355_ = v___y_1377_;
v___y_1356_ = v_a_1385_;
v___y_1357_ = v___y_1379_;
v___y_1358_ = v___y_1380_;
v___y_1359_ = v___y_1381_;
v___y_1360_ = v___y_1382_;
goto v___jp_1354_;
}
else
{
lean_object* v_a_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1403_; 
lean_dec(v_a_1385_);
lean_dec_ref(v___y_1377_);
lean_dec_ref(v_funTypes_1250_);
lean_dec(v___x_1247_);
lean_dec_ref(v___f_1246_);
lean_dec_ref(v_preDefs_1244_);
lean_dec(v___x_1243_);
lean_dec_ref(v_xs_1242_);
lean_dec_ref(v_fixedParamPerms_1241_);
lean_dec_ref(v___x_1239_);
lean_dec_ref(v_recArgInfos_1237_);
v_a_1396_ = lean_ctor_get(v___x_1395_, 0);
v_isSharedCheck_1403_ = !lean_is_exclusive(v___x_1395_);
if (v_isSharedCheck_1403_ == 0)
{
v___x_1398_ = v___x_1395_;
v_isShared_1399_ = v_isSharedCheck_1403_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_a_1396_);
lean_dec(v___x_1395_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1403_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v___x_1401_; 
if (v_isShared_1399_ == 0)
{
v___x_1401_ = v___x_1398_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v_a_1396_);
v___x_1401_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
return v___x_1401_;
}
}
}
}
}
else
{
lean_object* v_a_1404_; lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1411_; 
lean_dec(v_a_1385_);
lean_dec_ref(v___y_1377_);
lean_dec_ref(v_funTypes_1250_);
lean_dec(v___x_1247_);
lean_dec_ref(v___f_1246_);
lean_dec_ref(v_preDefs_1244_);
lean_dec(v___x_1243_);
lean_dec_ref(v_xs_1242_);
lean_dec_ref(v_fixedParamPerms_1241_);
lean_dec_ref(v___x_1239_);
lean_dec_ref(v_recArgInfos_1237_);
v_a_1404_ = lean_ctor_get(v___x_1386_, 0);
v_isSharedCheck_1411_ = !lean_is_exclusive(v___x_1386_);
if (v_isSharedCheck_1411_ == 0)
{
v___x_1406_ = v___x_1386_;
v_isShared_1407_ = v_isSharedCheck_1411_;
goto v_resetjp_1405_;
}
else
{
lean_inc(v_a_1404_);
lean_dec(v___x_1386_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1411_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v___x_1409_; 
if (v_isShared_1407_ == 0)
{
v___x_1409_ = v___x_1406_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v_a_1404_);
v___x_1409_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
return v___x_1409_;
}
}
}
}
else
{
lean_object* v_a_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1419_; 
lean_dec_ref(v___y_1377_);
lean_dec_ref(v_funTypes_1250_);
lean_dec(v___x_1247_);
lean_dec_ref(v___f_1246_);
lean_dec_ref(v_preDefs_1244_);
lean_dec(v___x_1243_);
lean_dec_ref(v_xs_1242_);
lean_dec_ref(v_fixedParamPerms_1241_);
lean_dec_ref(v___x_1239_);
lean_dec_ref(v_recArgInfos_1237_);
lean_dec_ref(v___f_1236_);
v_a_1412_ = lean_ctor_get(v___x_1384_, 0);
v_isSharedCheck_1419_ = !lean_is_exclusive(v___x_1384_);
if (v_isSharedCheck_1419_ == 0)
{
v___x_1414_ = v___x_1384_;
v_isShared_1415_ = v_isSharedCheck_1419_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_a_1412_);
lean_dec(v___x_1384_);
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
v___jp_1420_:
{
lean_object* v___x_1425_; 
v___x_1425_ = l_Lean_Elab_Structural_mkBRecOnConst(v_recArgInfos_1237_, v___x_1239_, v_motives_1251_, v_a_1248_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_);
lean_dec_ref(v_motives_1251_);
if (lean_obj_tag(v___x_1425_) == 0)
{
lean_object* v_a_1426_; lean_object* v___x_1427_; 
v_a_1426_ = lean_ctor_get(v___x_1425_, 0);
lean_inc_n(v_a_1426_, 2);
lean_dec_ref_known(v___x_1425_, 1);
lean_inc_ref(v___x_1239_);
v___x_1427_ = l_Lean_Elab_Structural_inferBRecOnFTypes(v_recArgInfos_1237_, v___x_1239_, v_a_1426_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_);
if (lean_obj_tag(v___x_1427_) == 0)
{
lean_object* v_a_1428_; lean_object* v___x_1429_; 
v_a_1428_ = lean_ctor_get(v___x_1427_, 0);
lean_inc(v_a_1428_);
lean_dec_ref_known(v___x_1427_, 1);
lean_inc_ref(v___f_1236_);
lean_inc(v___y_1424_);
lean_inc_ref(v___y_1423_);
lean_inc(v___y_1422_);
lean_inc_ref(v___y_1421_);
v___x_1429_ = lean_apply_5(v___f_1236_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_, lean_box(0));
if (lean_obj_tag(v___x_1429_) == 0)
{
lean_object* v_a_1430_; uint8_t v___x_1431_; 
v_a_1430_ = lean_ctor_get(v___x_1429_, 0);
lean_inc(v_a_1430_);
lean_dec_ref_known(v___x_1429_, 1);
v___x_1431_ = lean_unbox(v_a_1430_);
lean_dec(v_a_1430_);
if (v___x_1431_ == 0)
{
v___y_1377_ = v_a_1426_;
v___y_1378_ = v_a_1428_;
v___y_1379_ = v___y_1421_;
v___y_1380_ = v___y_1422_;
v___y_1381_ = v___y_1423_;
v___y_1382_ = v___y_1424_;
goto v___jp_1376_;
}
else
{
lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; 
v___x_1432_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__8);
lean_inc(v_a_1428_);
v___x_1433_ = lean_array_to_list(v_a_1428_);
v___x_1434_ = lean_box(0);
v___x_1435_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_1433_, v___x_1434_);
v___x_1436_ = l_Lean_MessageData_ofList(v___x_1435_);
v___x_1437_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1437_, 0, v___x_1432_);
lean_ctor_set(v___x_1437_, 1, v___x_1436_);
lean_inc(v___x_1247_);
v___x_1438_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_1247_, v___x_1437_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_);
if (lean_obj_tag(v___x_1438_) == 0)
{
lean_dec_ref_known(v___x_1438_, 1);
v___y_1377_ = v_a_1426_;
v___y_1378_ = v_a_1428_;
v___y_1379_ = v___y_1421_;
v___y_1380_ = v___y_1422_;
v___y_1381_ = v___y_1423_;
v___y_1382_ = v___y_1424_;
goto v___jp_1376_;
}
else
{
lean_object* v_a_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1446_; 
lean_dec(v_a_1428_);
lean_dec(v_a_1426_);
lean_dec_ref(v_funTypes_1250_);
lean_dec(v___x_1247_);
lean_dec_ref(v___f_1246_);
lean_dec_ref(v_preDefs_1244_);
lean_dec(v___x_1243_);
lean_dec_ref(v_xs_1242_);
lean_dec_ref(v_fixedParamPerms_1241_);
lean_dec_ref(v___x_1239_);
lean_dec_ref(v_recArgInfos_1237_);
lean_dec_ref(v___f_1236_);
v_a_1439_ = lean_ctor_get(v___x_1438_, 0);
v_isSharedCheck_1446_ = !lean_is_exclusive(v___x_1438_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1441_ = v___x_1438_;
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_a_1439_);
lean_dec(v___x_1438_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v___x_1444_; 
if (v_isShared_1442_ == 0)
{
v___x_1444_ = v___x_1441_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v_a_1439_);
v___x_1444_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
return v___x_1444_;
}
}
}
}
}
else
{
lean_object* v_a_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1454_; 
lean_dec(v_a_1428_);
lean_dec(v_a_1426_);
lean_dec_ref(v_funTypes_1250_);
lean_dec(v___x_1247_);
lean_dec_ref(v___f_1246_);
lean_dec_ref(v_preDefs_1244_);
lean_dec(v___x_1243_);
lean_dec_ref(v_xs_1242_);
lean_dec_ref(v_fixedParamPerms_1241_);
lean_dec_ref(v___x_1239_);
lean_dec_ref(v_recArgInfos_1237_);
lean_dec_ref(v___f_1236_);
v_a_1447_ = lean_ctor_get(v___x_1429_, 0);
v_isSharedCheck_1454_ = !lean_is_exclusive(v___x_1429_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1449_ = v___x_1429_;
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
else
{
lean_inc(v_a_1447_);
lean_dec(v___x_1429_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v___x_1452_; 
if (v_isShared_1450_ == 0)
{
v___x_1452_ = v___x_1449_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v_a_1447_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
return v___x_1452_;
}
}
}
}
else
{
lean_object* v_a_1455_; lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1462_; 
lean_dec(v_a_1426_);
lean_dec_ref(v_funTypes_1250_);
lean_dec(v___x_1247_);
lean_dec_ref(v___f_1246_);
lean_dec_ref(v_preDefs_1244_);
lean_dec(v___x_1243_);
lean_dec_ref(v_xs_1242_);
lean_dec_ref(v_fixedParamPerms_1241_);
lean_dec_ref(v___x_1239_);
lean_dec_ref(v_recArgInfos_1237_);
lean_dec_ref(v___f_1236_);
v_a_1455_ = lean_ctor_get(v___x_1427_, 0);
v_isSharedCheck_1462_ = !lean_is_exclusive(v___x_1427_);
if (v_isSharedCheck_1462_ == 0)
{
v___x_1457_ = v___x_1427_;
v_isShared_1458_ = v_isSharedCheck_1462_;
goto v_resetjp_1456_;
}
else
{
lean_inc(v_a_1455_);
lean_dec(v___x_1427_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1462_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
lean_object* v___x_1460_; 
if (v_isShared_1458_ == 0)
{
v___x_1460_ = v___x_1457_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v_a_1455_);
v___x_1460_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
return v___x_1460_;
}
}
}
}
else
{
lean_object* v_a_1463_; lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1470_; 
lean_dec_ref(v_funTypes_1250_);
lean_dec(v___x_1247_);
lean_dec_ref(v___f_1246_);
lean_dec_ref(v_preDefs_1244_);
lean_dec(v___x_1243_);
lean_dec_ref(v_xs_1242_);
lean_dec_ref(v_fixedParamPerms_1241_);
lean_dec_ref(v___x_1239_);
lean_dec_ref(v_recArgInfos_1237_);
lean_dec_ref(v___f_1236_);
v_a_1463_ = lean_ctor_get(v___x_1425_, 0);
v_isSharedCheck_1470_ = !lean_is_exclusive(v___x_1425_);
if (v_isSharedCheck_1470_ == 0)
{
v___x_1465_ = v___x_1425_;
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
else
{
lean_inc(v_a_1463_);
lean_dec(v___x_1425_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
lean_object* v___x_1468_; 
if (v_isShared_1466_ == 0)
{
v___x_1468_ = v___x_1465_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v_a_1463_);
v___x_1468_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
return v___x_1468_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___boxed(lean_object** _args){
lean_object* v___f_1503_ = _args[0];
lean_object* v_recArgInfos_1504_ = _args[1];
lean_object* v_a_1505_ = _args[2];
lean_object* v___x_1506_ = _args[3];
lean_object* v___x_1507_ = _args[4];
lean_object* v_fixedParamPerms_1508_ = _args[5];
lean_object* v_xs_1509_ = _args[6];
lean_object* v___x_1510_ = _args[7];
lean_object* v_preDefs_1511_ = _args[8];
lean_object* v_numIndices_1512_ = _args[9];
lean_object* v___f_1513_ = _args[10];
lean_object* v___x_1514_ = _args[11];
lean_object* v_a_1515_ = _args[12];
lean_object* v___x_1516_ = _args[13];
lean_object* v_funTypes_1517_ = _args[14];
lean_object* v_motives_1518_ = _args[15];
lean_object* v___y_1519_ = _args[16];
lean_object* v___y_1520_ = _args[17];
lean_object* v___y_1521_ = _args[18];
lean_object* v___y_1522_ = _args[19];
lean_object* v___y_1523_ = _args[20];
_start:
{
size_t v___x_26449__boxed_1524_; uint8_t v_a_26453__boxed_1525_; lean_object* v_res_1526_; 
v___x_26449__boxed_1524_ = lean_unbox_usize(v___x_1507_);
lean_dec(v___x_1507_);
v_a_26453__boxed_1525_ = lean_unbox(v_a_1515_);
v_res_1526_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2(v___f_1503_, v_recArgInfos_1504_, v_a_1505_, v___x_1506_, v___x_26449__boxed_1524_, v_fixedParamPerms_1508_, v_xs_1509_, v___x_1510_, v_preDefs_1511_, v_numIndices_1512_, v___f_1513_, v___x_1514_, v_a_26453__boxed_1525_, v___x_1516_, v_funTypes_1517_, v_motives_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_);
lean_dec(v___y_1522_);
lean_dec_ref(v___y_1521_);
lean_dec(v___y_1520_);
lean_dec_ref(v___y_1519_);
lean_dec_ref(v___x_1516_);
lean_dec(v_numIndices_1512_);
lean_dec_ref(v_a_1505_);
return v_res_1526_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___redArg(lean_object* v_a_1527_, lean_object* v_funTypes_1528_, size_t v_sz_1529_, size_t v_i_1530_, lean_object* v_bs_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_){
_start:
{
uint8_t v___x_1537_; 
v___x_1537_ = lean_usize_dec_lt(v_i_1530_, v_sz_1529_);
if (v___x_1537_ == 0)
{
lean_object* v___x_1538_; 
v___x_1538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1538_, 0, v_bs_1531_);
return v___x_1538_;
}
else
{
lean_object* v___x_1539_; lean_object* v_v_1540_; lean_object* v___x_1541_; lean_object* v_bs_x27_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; 
v___x_1539_ = l_Lean_instInhabitedExpr;
v_v_1540_ = lean_array_uget(v_bs_1531_, v_i_1530_);
v___x_1541_ = lean_unsigned_to_nat(0u);
v_bs_x27_1542_ = lean_array_uset(v_bs_1531_, v_i_1530_, v___x_1541_);
v___x_1543_ = lean_usize_to_nat(v_i_1530_);
v___x_1544_ = lean_array_get_borrowed(v___x_1539_, v_a_1527_, v___x_1543_);
v___x_1545_ = lean_array_get_borrowed(v___x_1539_, v_funTypes_1528_, v___x_1543_);
lean_dec(v___x_1543_);
lean_inc(v___x_1545_);
lean_inc(v___x_1544_);
v___x_1546_ = l_Lean_Elab_Structural_mkIndPredBRecOnMotive(v_v_1540_, v___x_1544_, v___x_1545_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_);
if (lean_obj_tag(v___x_1546_) == 0)
{
lean_object* v_a_1547_; size_t v___x_1548_; size_t v___x_1549_; lean_object* v___x_1550_; 
v_a_1547_ = lean_ctor_get(v___x_1546_, 0);
lean_inc(v_a_1547_);
lean_dec_ref_known(v___x_1546_, 1);
v___x_1548_ = ((size_t)1ULL);
v___x_1549_ = lean_usize_add(v_i_1530_, v___x_1548_);
v___x_1550_ = lean_array_uset(v_bs_x27_1542_, v_i_1530_, v_a_1547_);
v_i_1530_ = v___x_1549_;
v_bs_1531_ = v___x_1550_;
goto _start;
}
else
{
lean_object* v_a_1552_; lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1559_; 
lean_dec_ref(v_bs_x27_1542_);
v_a_1552_ = lean_ctor_get(v___x_1546_, 0);
v_isSharedCheck_1559_ = !lean_is_exclusive(v___x_1546_);
if (v_isSharedCheck_1559_ == 0)
{
v___x_1554_ = v___x_1546_;
v_isShared_1555_ = v_isSharedCheck_1559_;
goto v_resetjp_1553_;
}
else
{
lean_inc(v_a_1552_);
lean_dec(v___x_1546_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1559_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
lean_object* v___x_1557_; 
if (v_isShared_1555_ == 0)
{
v___x_1557_ = v___x_1554_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v_a_1552_);
v___x_1557_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
return v___x_1557_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___redArg___boxed(lean_object* v_a_1560_, lean_object* v_funTypes_1561_, lean_object* v_sz_1562_, lean_object* v_i_1563_, lean_object* v_bs_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_){
_start:
{
size_t v_sz_boxed_1570_; size_t v_i_boxed_1571_; lean_object* v_res_1572_; 
v_sz_boxed_1570_ = lean_unbox_usize(v_sz_1562_);
lean_dec(v_sz_1562_);
v_i_boxed_1571_ = lean_unbox_usize(v_i_1563_);
lean_dec(v_i_1563_);
v_res_1572_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___redArg(v_a_1560_, v_funTypes_1561_, v_sz_boxed_1570_, v_i_boxed_1571_, v_bs_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_);
lean_dec(v___y_1568_);
lean_dec_ref(v___y_1567_);
lean_dec(v___y_1566_);
lean_dec_ref(v___y_1565_);
lean_dec_ref(v_funTypes_1561_);
lean_dec_ref(v_a_1560_);
return v_res_1572_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__3(lean_object* v_recArgInfos_1573_, lean_object* v_a_1574_, size_t v___x_1575_, lean_object* v___f_1576_, lean_object* v_funTypes_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_){
_start:
{
size_t v_sz_1583_; lean_object* v___x_1584_; 
v_sz_1583_ = lean_array_size(v_recArgInfos_1573_);
v___x_1584_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___redArg(v_a_1574_, v_funTypes_1577_, v_sz_1583_, v___x_1575_, v_recArgInfos_1573_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v_a_1585_; lean_object* v___x_1586_; 
v_a_1585_ = lean_ctor_get(v___x_1584_, 0);
lean_inc(v_a_1585_);
lean_dec_ref_known(v___x_1584_, 1);
lean_inc(v___y_1581_);
lean_inc_ref(v___y_1580_);
lean_inc(v___y_1579_);
lean_inc_ref(v___y_1578_);
v___x_1586_ = lean_apply_7(v___f_1576_, v_funTypes_1577_, v_a_1585_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_, lean_box(0));
return v___x_1586_;
}
else
{
lean_object* v_a_1587_; lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1594_; 
lean_dec_ref(v_funTypes_1577_);
lean_dec_ref(v___f_1576_);
v_a_1587_ = lean_ctor_get(v___x_1584_, 0);
v_isSharedCheck_1594_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1594_ == 0)
{
v___x_1589_ = v___x_1584_;
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
else
{
lean_inc(v_a_1587_);
lean_dec(v___x_1584_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
lean_object* v___x_1592_; 
if (v_isShared_1590_ == 0)
{
v___x_1592_ = v___x_1589_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v_a_1587_);
v___x_1592_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
return v___x_1592_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__3___boxed(lean_object* v_recArgInfos_1595_, lean_object* v_a_1596_, lean_object* v___x_1597_, lean_object* v___f_1598_, lean_object* v_funTypes_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_){
_start:
{
size_t v___x_27046__boxed_1605_; lean_object* v_res_1606_; 
v___x_27046__boxed_1605_ = lean_unbox_usize(v___x_1597_);
lean_dec(v___x_1597_);
v_res_1606_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__3(v_recArgInfos_1595_, v_a_1596_, v___x_27046__boxed_1605_, v___f_1598_, v_funTypes_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_);
lean_dec(v___y_1603_);
lean_dec_ref(v___y_1602_);
lean_dec(v___y_1601_);
lean_dec_ref(v___y_1600_);
lean_dec_ref(v_a_1596_);
return v_res_1606_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___redArg(lean_object* v_a_1607_, lean_object* v_a_1608_, size_t v_sz_1609_, size_t v_i_1610_, lean_object* v_bs_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_){
_start:
{
uint8_t v___x_1617_; 
v___x_1617_ = lean_usize_dec_lt(v_i_1610_, v_sz_1609_);
if (v___x_1617_ == 0)
{
lean_object* v___x_1618_; 
v___x_1618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1618_, 0, v_bs_1611_);
return v___x_1618_;
}
else
{
lean_object* v___x_1619_; lean_object* v_v_1620_; lean_object* v___x_1621_; lean_object* v_bs_x27_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; 
v___x_1619_ = l_Lean_instInhabitedExpr;
v_v_1620_ = lean_array_uget(v_bs_1611_, v_i_1610_);
v___x_1621_ = lean_unsigned_to_nat(0u);
v_bs_x27_1622_ = lean_array_uset(v_bs_1611_, v_i_1610_, v___x_1621_);
v___x_1623_ = lean_usize_to_nat(v_i_1610_);
v___x_1624_ = lean_array_get_borrowed(v___x_1619_, v_a_1607_, v___x_1623_);
v___x_1625_ = lean_array_get_borrowed(v___x_1619_, v_a_1608_, v___x_1623_);
lean_dec(v___x_1623_);
lean_inc(v___x_1625_);
lean_inc(v___x_1624_);
v___x_1626_ = l_Lean_Elab_Structural_mkBRecOnMotive(v_v_1620_, v___x_1624_, v___x_1625_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_);
if (lean_obj_tag(v___x_1626_) == 0)
{
lean_object* v_a_1627_; size_t v___x_1628_; size_t v___x_1629_; lean_object* v___x_1630_; 
v_a_1627_ = lean_ctor_get(v___x_1626_, 0);
lean_inc(v_a_1627_);
lean_dec_ref_known(v___x_1626_, 1);
v___x_1628_ = ((size_t)1ULL);
v___x_1629_ = lean_usize_add(v_i_1610_, v___x_1628_);
v___x_1630_ = lean_array_uset(v_bs_x27_1622_, v_i_1610_, v_a_1627_);
v_i_1610_ = v___x_1629_;
v_bs_1611_ = v___x_1630_;
goto _start;
}
else
{
lean_object* v_a_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1639_; 
lean_dec_ref(v_bs_x27_1622_);
v_a_1632_ = lean_ctor_get(v___x_1626_, 0);
v_isSharedCheck_1639_ = !lean_is_exclusive(v___x_1626_);
if (v_isSharedCheck_1639_ == 0)
{
v___x_1634_ = v___x_1626_;
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_a_1632_);
lean_dec(v___x_1626_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
lean_object* v___x_1637_; 
if (v_isShared_1635_ == 0)
{
v___x_1637_ = v___x_1634_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v_a_1632_);
v___x_1637_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
return v___x_1637_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___redArg___boxed(lean_object* v_a_1640_, lean_object* v_a_1641_, lean_object* v_sz_1642_, lean_object* v_i_1643_, lean_object* v_bs_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_){
_start:
{
size_t v_sz_boxed_1650_; size_t v_i_boxed_1651_; lean_object* v_res_1652_; 
v_sz_boxed_1650_ = lean_unbox_usize(v_sz_1642_);
lean_dec(v_sz_1642_);
v_i_boxed_1651_ = lean_unbox_usize(v_i_1643_);
lean_dec(v_i_1643_);
v_res_1652_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___redArg(v_a_1640_, v_a_1641_, v_sz_boxed_1650_, v_i_boxed_1651_, v_bs_1644_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_);
lean_dec(v___y_1648_);
lean_dec_ref(v___y_1647_);
lean_dec(v___y_1646_);
lean_dec_ref(v___y_1645_);
lean_dec_ref(v_a_1641_);
lean_dec_ref(v_a_1640_);
return v_res_1652_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg(lean_object* v_msg_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_){
_start:
{
lean_object* v_ref_1659_; lean_object* v___x_1660_; lean_object* v_a_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1669_; 
v_ref_1659_ = lean_ctor_get(v___y_1656_, 2);
v___x_1660_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11_spec__21(v_msg_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_);
v_a_1661_ = lean_ctor_get(v___x_1660_, 0);
v_isSharedCheck_1669_ = !lean_is_exclusive(v___x_1660_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1663_ = v___x_1660_;
v_isShared_1664_ = v_isSharedCheck_1669_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_a_1661_);
lean_dec(v___x_1660_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1669_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v___x_1665_; lean_object* v___x_1667_; 
lean_inc(v_ref_1659_);
v___x_1665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1665_, 0, v_ref_1659_);
lean_ctor_set(v___x_1665_, 1, v_a_1661_);
if (v_isShared_1664_ == 0)
{
lean_ctor_set_tag(v___x_1663_, 1);
lean_ctor_set(v___x_1663_, 0, v___x_1665_);
v___x_1667_ = v___x_1663_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v___x_1665_);
v___x_1667_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
return v___x_1667_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg___boxed(lean_object* v_msg_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_){
_start:
{
lean_object* v_res_1676_; 
v_res_1676_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg(v_msg_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_);
lean_dec(v___y_1674_);
lean_dec_ref(v___y_1673_);
lean_dec(v___y_1672_);
lean_dec_ref(v___y_1671_);
return v_res_1676_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1678_; lean_object* v___x_1679_; 
v___x_1678_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__0));
v___x_1679_ = l_Lean_stringToMessageData(v___x_1678_);
return v___x_1679_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__3(void){
_start:
{
lean_object* v___x_1681_; lean_object* v___x_1682_; 
v___x_1681_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__2));
v___x_1682_ = l_Lean_stringToMessageData(v___x_1681_);
return v___x_1682_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4(lean_object* v_constName_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_){
_start:
{
lean_object* v___x_1689_; lean_object* v_env_1690_; lean_object* v___x_1691_; 
v___x_1689_ = lean_st_ref_get(v___y_1687_);
v_env_1690_ = lean_ctor_get(v___x_1689_, 0);
lean_inc_ref(v_env_1690_);
lean_dec(v___x_1689_);
lean_inc(v_constName_1683_);
v___x_1691_ = l_Lean_isInductiveCore_x3f(v_env_1690_, v_constName_1683_);
if (lean_obj_tag(v___x_1691_) == 0)
{
lean_object* v___x_1692_; uint8_t v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; 
v___x_1692_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__1, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__1);
v___x_1693_ = 0;
v___x_1694_ = l_Lean_MessageData_ofConstName(v_constName_1683_, v___x_1693_);
v___x_1695_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1695_, 0, v___x_1692_);
lean_ctor_set(v___x_1695_, 1, v___x_1694_);
v___x_1696_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__3, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__3_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__3);
v___x_1697_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1697_, 0, v___x_1695_);
lean_ctor_set(v___x_1697_, 1, v___x_1696_);
v___x_1698_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg(v___x_1697_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
return v___x_1698_;
}
else
{
lean_object* v_val_1699_; lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1706_; 
lean_dec(v_constName_1683_);
v_val_1699_ = lean_ctor_get(v___x_1691_, 0);
v_isSharedCheck_1706_ = !lean_is_exclusive(v___x_1691_);
if (v_isSharedCheck_1706_ == 0)
{
v___x_1701_ = v___x_1691_;
v_isShared_1702_ = v_isSharedCheck_1706_;
goto v_resetjp_1700_;
}
else
{
lean_inc(v_val_1699_);
lean_dec(v___x_1691_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1706_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
lean_object* v___x_1704_; 
if (v_isShared_1702_ == 0)
{
lean_ctor_set_tag(v___x_1701_, 0);
v___x_1704_ = v___x_1701_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v_val_1699_);
v___x_1704_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
return v___x_1704_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___boxed(lean_object* v_constName_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_){
_start:
{
lean_object* v_res_1713_; 
v_res_1713_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4(v_constName_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_);
lean_dec(v___y_1711_);
lean_dec_ref(v___y_1710_);
lean_dec(v___y_1709_);
lean_dec_ref(v___y_1708_);
return v_res_1713_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___redArg(lean_object* v_fixedParamPerms_1714_, lean_object* v_xs_1715_, size_t v_sz_1716_, size_t v_i_1717_, lean_object* v_bs_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_){
_start:
{
uint8_t v___x_1724_; 
v___x_1724_ = lean_usize_dec_lt(v_i_1717_, v_sz_1716_);
if (v___x_1724_ == 0)
{
lean_object* v___x_1725_; 
lean_dec_ref(v_xs_1715_);
v___x_1725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1725_, 0, v_bs_1718_);
return v___x_1725_;
}
else
{
lean_object* v_v_1726_; lean_object* v_perms_1727_; lean_object* v_type_1728_; lean_object* v___x_1729_; lean_object* v_bs_x27_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; 
v_v_1726_ = lean_array_uget_borrowed(v_bs_1718_, v_i_1717_);
v_perms_1727_ = lean_ctor_get(v_fixedParamPerms_1714_, 1);
v_type_1728_ = lean_ctor_get(v_v_1726_, 6);
lean_inc_ref(v_type_1728_);
v___x_1729_ = lean_unsigned_to_nat(0u);
v_bs_x27_1730_ = lean_array_uset(v_bs_1718_, v_i_1717_, v___x_1729_);
v___x_1731_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0);
v___x_1732_ = lean_usize_to_nat(v_i_1717_);
v___x_1733_ = lean_array_get_borrowed(v___x_1731_, v_perms_1727_, v___x_1732_);
lean_dec(v___x_1732_);
lean_inc_ref(v_xs_1715_);
lean_inc(v___x_1733_);
v___x_1734_ = l_Lean_Elab_FixedParamPerm_instantiateForall(v___x_1733_, v_type_1728_, v_xs_1715_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_);
if (lean_obj_tag(v___x_1734_) == 0)
{
lean_object* v_a_1735_; size_t v___x_1736_; size_t v___x_1737_; lean_object* v___x_1738_; 
v_a_1735_ = lean_ctor_get(v___x_1734_, 0);
lean_inc(v_a_1735_);
lean_dec_ref_known(v___x_1734_, 1);
v___x_1736_ = ((size_t)1ULL);
v___x_1737_ = lean_usize_add(v_i_1717_, v___x_1736_);
v___x_1738_ = lean_array_uset(v_bs_x27_1730_, v_i_1717_, v_a_1735_);
v_i_1717_ = v___x_1737_;
v_bs_1718_ = v___x_1738_;
goto _start;
}
else
{
lean_object* v_a_1740_; lean_object* v___x_1742_; uint8_t v_isShared_1743_; uint8_t v_isSharedCheck_1747_; 
lean_dec_ref(v_bs_x27_1730_);
lean_dec_ref(v_xs_1715_);
v_a_1740_ = lean_ctor_get(v___x_1734_, 0);
v_isSharedCheck_1747_ = !lean_is_exclusive(v___x_1734_);
if (v_isSharedCheck_1747_ == 0)
{
v___x_1742_ = v___x_1734_;
v_isShared_1743_ = v_isSharedCheck_1747_;
goto v_resetjp_1741_;
}
else
{
lean_inc(v_a_1740_);
lean_dec(v___x_1734_);
v___x_1742_ = lean_box(0);
v_isShared_1743_ = v_isSharedCheck_1747_;
goto v_resetjp_1741_;
}
v_resetjp_1741_:
{
lean_object* v___x_1745_; 
if (v_isShared_1743_ == 0)
{
v___x_1745_ = v___x_1742_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1746_; 
v_reuseFailAlloc_1746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1746_, 0, v_a_1740_);
v___x_1745_ = v_reuseFailAlloc_1746_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
return v___x_1745_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___redArg___boxed(lean_object* v_fixedParamPerms_1748_, lean_object* v_xs_1749_, lean_object* v_sz_1750_, lean_object* v_i_1751_, lean_object* v_bs_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_){
_start:
{
size_t v_sz_boxed_1758_; size_t v_i_boxed_1759_; lean_object* v_res_1760_; 
v_sz_boxed_1758_ = lean_unbox_usize(v_sz_1750_);
lean_dec(v_sz_1750_);
v_i_boxed_1759_ = lean_unbox_usize(v_i_1751_);
lean_dec(v_i_1751_);
v_res_1760_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___redArg(v_fixedParamPerms_1748_, v_xs_1749_, v_sz_boxed_1758_, v_i_boxed_1759_, v_bs_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_);
lean_dec(v___y_1756_);
lean_dec_ref(v___y_1755_);
lean_dec(v___y_1754_);
lean_dec_ref(v___y_1753_);
lean_dec_ref(v_fixedParamPerms_1748_);
return v_res_1760_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___redArg(lean_object* v_fixedParamPerms_1761_, lean_object* v_xs_1762_, size_t v_sz_1763_, size_t v_i_1764_, lean_object* v_bs_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_){
_start:
{
uint8_t v___x_1771_; 
v___x_1771_ = lean_usize_dec_lt(v_i_1764_, v_sz_1763_);
if (v___x_1771_ == 0)
{
lean_object* v___x_1772_; 
lean_dec_ref(v_xs_1762_);
v___x_1772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1772_, 0, v_bs_1765_);
return v___x_1772_;
}
else
{
lean_object* v_v_1773_; lean_object* v_perms_1774_; lean_object* v_value_1775_; lean_object* v___x_1776_; lean_object* v_bs_x27_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; 
v_v_1773_ = lean_array_uget_borrowed(v_bs_1765_, v_i_1764_);
v_perms_1774_ = lean_ctor_get(v_fixedParamPerms_1761_, 1);
v_value_1775_ = lean_ctor_get(v_v_1773_, 7);
lean_inc_ref(v_value_1775_);
v___x_1776_ = lean_unsigned_to_nat(0u);
v_bs_x27_1777_ = lean_array_uset(v_bs_1765_, v_i_1764_, v___x_1776_);
v___x_1778_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0);
v___x_1779_ = lean_usize_to_nat(v_i_1764_);
v___x_1780_ = lean_array_get_borrowed(v___x_1778_, v_perms_1774_, v___x_1779_);
lean_dec(v___x_1779_);
lean_inc_ref(v_xs_1762_);
lean_inc(v___x_1780_);
v___x_1781_ = l_Lean_Elab_FixedParamPerm_instantiateLambda(v___x_1780_, v_value_1775_, v_xs_1762_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_);
if (lean_obj_tag(v___x_1781_) == 0)
{
lean_object* v_a_1782_; size_t v___x_1783_; size_t v___x_1784_; lean_object* v___x_1785_; 
v_a_1782_ = lean_ctor_get(v___x_1781_, 0);
lean_inc(v_a_1782_);
lean_dec_ref_known(v___x_1781_, 1);
v___x_1783_ = ((size_t)1ULL);
v___x_1784_ = lean_usize_add(v_i_1764_, v___x_1783_);
v___x_1785_ = lean_array_uset(v_bs_x27_1777_, v_i_1764_, v_a_1782_);
v_i_1764_ = v___x_1784_;
v_bs_1765_ = v___x_1785_;
goto _start;
}
else
{
lean_object* v_a_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1794_; 
lean_dec_ref(v_bs_x27_1777_);
lean_dec_ref(v_xs_1762_);
v_a_1787_ = lean_ctor_get(v___x_1781_, 0);
v_isSharedCheck_1794_ = !lean_is_exclusive(v___x_1781_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1789_ = v___x_1781_;
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_a_1787_);
lean_dec(v___x_1781_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v___x_1792_; 
if (v_isShared_1790_ == 0)
{
v___x_1792_ = v___x_1789_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v_a_1787_);
v___x_1792_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
return v___x_1792_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___redArg___boxed(lean_object* v_fixedParamPerms_1795_, lean_object* v_xs_1796_, lean_object* v_sz_1797_, lean_object* v_i_1798_, lean_object* v_bs_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_){
_start:
{
size_t v_sz_boxed_1805_; size_t v_i_boxed_1806_; lean_object* v_res_1807_; 
v_sz_boxed_1805_ = lean_unbox_usize(v_sz_1797_);
lean_dec(v_sz_1797_);
v_i_boxed_1806_ = lean_unbox_usize(v_i_1798_);
lean_dec(v_i_1798_);
v_res_1807_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___redArg(v_fixedParamPerms_1795_, v_xs_1796_, v_sz_boxed_1805_, v_i_boxed_1806_, v_bs_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_);
lean_dec(v___y_1803_);
lean_dec_ref(v___y_1802_);
lean_dec(v___y_1801_);
lean_dec_ref(v___y_1800_);
lean_dec_ref(v_fixedParamPerms_1795_);
return v_res_1807_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11___redArg(lean_object* v_hi_1808_, lean_object* v_pivot_1809_, lean_object* v_as_1810_, lean_object* v_i_1811_, lean_object* v_k_1812_){
_start:
{
uint8_t v___x_1813_; 
v___x_1813_ = lean_nat_dec_lt(v_k_1812_, v_hi_1808_);
if (v___x_1813_ == 0)
{
lean_object* v___x_1814_; lean_object* v___x_1815_; 
lean_dec(v_k_1812_);
v___x_1814_ = lean_array_fswap(v_as_1810_, v_i_1811_, v_hi_1808_);
v___x_1815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1815_, 0, v_i_1811_);
lean_ctor_set(v___x_1815_, 1, v___x_1814_);
return v___x_1815_;
}
else
{
lean_object* v___x_1816_; uint8_t v___x_1817_; 
v___x_1816_ = lean_array_fget_borrowed(v_as_1810_, v_k_1812_);
v___x_1817_ = l_Nat_blt(v___x_1816_, v_pivot_1809_);
if (v___x_1817_ == 0)
{
lean_object* v___x_1818_; lean_object* v___x_1819_; 
v___x_1818_ = lean_unsigned_to_nat(1u);
v___x_1819_ = lean_nat_add(v_k_1812_, v___x_1818_);
lean_dec(v_k_1812_);
v_k_1812_ = v___x_1819_;
goto _start;
}
else
{
lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; 
v___x_1821_ = lean_array_fswap(v_as_1810_, v_i_1811_, v_k_1812_);
v___x_1822_ = lean_unsigned_to_nat(1u);
v___x_1823_ = lean_nat_add(v_i_1811_, v___x_1822_);
lean_dec(v_i_1811_);
v___x_1824_ = lean_nat_add(v_k_1812_, v___x_1822_);
lean_dec(v_k_1812_);
v_as_1810_ = v___x_1821_;
v_i_1811_ = v___x_1823_;
v_k_1812_ = v___x_1824_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11___redArg___boxed(lean_object* v_hi_1826_, lean_object* v_pivot_1827_, lean_object* v_as_1828_, lean_object* v_i_1829_, lean_object* v_k_1830_){
_start:
{
lean_object* v_res_1831_; 
v_res_1831_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11___redArg(v_hi_1826_, v_pivot_1827_, v_as_1828_, v_i_1829_, v_k_1830_);
lean_dec(v_pivot_1827_);
lean_dec(v_hi_1826_);
return v_res_1831_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg(lean_object* v_n_1832_, lean_object* v_as_1833_, lean_object* v_lo_1834_, lean_object* v_hi_1835_){
_start:
{
lean_object* v___y_1837_; uint8_t v___x_1847_; 
v___x_1847_ = lean_nat_dec_lt(v_lo_1834_, v_hi_1835_);
if (v___x_1847_ == 0)
{
lean_dec(v_lo_1834_);
return v_as_1833_;
}
else
{
lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v_mid_1850_; lean_object* v___y_1852_; lean_object* v___y_1858_; lean_object* v___x_1863_; lean_object* v___x_1864_; uint8_t v___x_1865_; 
v___x_1848_ = lean_nat_add(v_lo_1834_, v_hi_1835_);
v___x_1849_ = lean_unsigned_to_nat(1u);
v_mid_1850_ = lean_nat_shiftr(v___x_1848_, v___x_1849_);
lean_dec(v___x_1848_);
v___x_1863_ = lean_array_fget_borrowed(v_as_1833_, v_mid_1850_);
v___x_1864_ = lean_array_fget_borrowed(v_as_1833_, v_lo_1834_);
v___x_1865_ = l_Nat_blt(v___x_1863_, v___x_1864_);
if (v___x_1865_ == 0)
{
v___y_1858_ = v_as_1833_;
goto v___jp_1857_;
}
else
{
lean_object* v___x_1866_; 
v___x_1866_ = lean_array_fswap(v_as_1833_, v_lo_1834_, v_mid_1850_);
v___y_1858_ = v___x_1866_;
goto v___jp_1857_;
}
v___jp_1851_:
{
lean_object* v___x_1853_; lean_object* v___x_1854_; uint8_t v___x_1855_; 
v___x_1853_ = lean_array_fget_borrowed(v___y_1852_, v_mid_1850_);
v___x_1854_ = lean_array_fget_borrowed(v___y_1852_, v_hi_1835_);
v___x_1855_ = l_Nat_blt(v___x_1853_, v___x_1854_);
if (v___x_1855_ == 0)
{
lean_dec(v_mid_1850_);
v___y_1837_ = v___y_1852_;
goto v___jp_1836_;
}
else
{
lean_object* v___x_1856_; 
v___x_1856_ = lean_array_fswap(v___y_1852_, v_mid_1850_, v_hi_1835_);
lean_dec(v_mid_1850_);
v___y_1837_ = v___x_1856_;
goto v___jp_1836_;
}
}
v___jp_1857_:
{
lean_object* v___x_1859_; lean_object* v___x_1860_; uint8_t v___x_1861_; 
v___x_1859_ = lean_array_fget_borrowed(v___y_1858_, v_hi_1835_);
v___x_1860_ = lean_array_fget_borrowed(v___y_1858_, v_lo_1834_);
v___x_1861_ = l_Nat_blt(v___x_1859_, v___x_1860_);
if (v___x_1861_ == 0)
{
v___y_1852_ = v___y_1858_;
goto v___jp_1851_;
}
else
{
lean_object* v___x_1862_; 
v___x_1862_ = lean_array_fswap(v___y_1858_, v_lo_1834_, v_hi_1835_);
v___y_1852_ = v___x_1862_;
goto v___jp_1851_;
}
}
}
v___jp_1836_:
{
lean_object* v_pivot_1838_; lean_object* v___x_1839_; lean_object* v_fst_1840_; lean_object* v_snd_1841_; uint8_t v___x_1842_; 
v_pivot_1838_ = lean_array_fget(v___y_1837_, v_hi_1835_);
lean_inc_n(v_lo_1834_, 2);
v___x_1839_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11___redArg(v_hi_1835_, v_pivot_1838_, v___y_1837_, v_lo_1834_, v_lo_1834_);
lean_dec(v_pivot_1838_);
v_fst_1840_ = lean_ctor_get(v___x_1839_, 0);
lean_inc(v_fst_1840_);
v_snd_1841_ = lean_ctor_get(v___x_1839_, 1);
lean_inc(v_snd_1841_);
lean_dec_ref(v___x_1839_);
v___x_1842_ = lean_nat_dec_le(v_hi_1835_, v_fst_1840_);
if (v___x_1842_ == 0)
{
lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; 
v___x_1843_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg(v_n_1832_, v_snd_1841_, v_lo_1834_, v_fst_1840_);
v___x_1844_ = lean_unsigned_to_nat(1u);
v___x_1845_ = lean_nat_add(v_fst_1840_, v___x_1844_);
lean_dec(v_fst_1840_);
v_as_1833_ = v___x_1843_;
v_lo_1834_ = v___x_1845_;
goto _start;
}
else
{
lean_dec(v_fst_1840_);
lean_dec(v_lo_1834_);
return v_snd_1841_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg___boxed(lean_object* v_n_1867_, lean_object* v_as_1868_, lean_object* v_lo_1869_, lean_object* v_hi_1870_){
_start:
{
lean_object* v_res_1871_; 
v_res_1871_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg(v_n_1867_, v_as_1868_, v_lo_1869_, v_hi_1870_);
lean_dec(v_hi_1870_);
lean_dec(v_n_1867_);
return v_res_1871_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__6(lean_object* v_xs_1872_, lean_object* v_f_1873_, lean_object* v_x_1874_, lean_object* v_as_1875_, size_t v_i_1876_, size_t v_stop_1877_, lean_object* v_b_1878_){
_start:
{
lean_object* v___y_1880_; uint8_t v___x_1884_; 
v___x_1884_ = lean_usize_dec_eq(v_i_1876_, v_stop_1877_);
if (v___x_1884_ == 0)
{
lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; uint8_t v___x_1889_; 
v___x_1885_ = l_Lean_Elab_Structural_instInhabitedRecArgInfo_default;
v___x_1886_ = lean_array_uget_borrowed(v_as_1875_, v_i_1876_);
v___x_1887_ = lean_array_get_borrowed(v___x_1885_, v_xs_1872_, v___x_1886_);
lean_inc_ref(v_f_1873_);
lean_inc(v___x_1887_);
v___x_1888_ = lean_apply_1(v_f_1873_, v___x_1887_);
v___x_1889_ = lean_nat_dec_eq(v___x_1888_, v_x_1874_);
lean_dec(v___x_1888_);
if (v___x_1889_ == 0)
{
v___y_1880_ = v_b_1878_;
goto v___jp_1879_;
}
else
{
lean_object* v___x_1890_; 
lean_inc(v___x_1886_);
v___x_1890_ = lean_array_push(v_b_1878_, v___x_1886_);
v___y_1880_ = v___x_1890_;
goto v___jp_1879_;
}
}
else
{
lean_dec_ref(v_f_1873_);
return v_b_1878_;
}
v___jp_1879_:
{
size_t v___x_1881_; size_t v___x_1882_; 
v___x_1881_ = ((size_t)1ULL);
v___x_1882_ = lean_usize_add(v_i_1876_, v___x_1881_);
v_i_1876_ = v___x_1882_;
v_b_1878_ = v___y_1880_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__6___boxed(lean_object* v_xs_1891_, lean_object* v_f_1892_, lean_object* v_x_1893_, lean_object* v_as_1894_, lean_object* v_i_1895_, lean_object* v_stop_1896_, lean_object* v_b_1897_){
_start:
{
size_t v_i_boxed_1898_; size_t v_stop_boxed_1899_; lean_object* v_res_1900_; 
v_i_boxed_1898_ = lean_unbox_usize(v_i_1895_);
lean_dec(v_i_1895_);
v_stop_boxed_1899_ = lean_unbox_usize(v_stop_1896_);
lean_dec(v_stop_1896_);
v_res_1900_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__6(v_xs_1891_, v_f_1892_, v_x_1893_, v_as_1894_, v_i_boxed_1898_, v_stop_boxed_1899_, v_b_1897_);
lean_dec_ref(v_as_1894_);
lean_dec(v_x_1893_);
lean_dec_ref(v_xs_1891_);
return v_res_1900_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8(lean_object* v_xs_1903_, lean_object* v_f_1904_, size_t v_sz_1905_, size_t v_i_1906_, lean_object* v_bs_1907_){
_start:
{
uint8_t v___x_1908_; 
v___x_1908_ = lean_usize_dec_lt(v_i_1906_, v_sz_1905_);
if (v___x_1908_ == 0)
{
lean_dec_ref(v_f_1904_);
return v_bs_1907_;
}
else
{
lean_object* v_v_1909_; lean_object* v___x_1910_; lean_object* v_bs_x27_1911_; lean_object* v___y_1913_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; uint8_t v___x_1922_; 
v_v_1909_ = lean_array_uget(v_bs_1907_, v_i_1906_);
v___x_1910_ = lean_unsigned_to_nat(0u);
v_bs_x27_1911_ = lean_array_uset(v_bs_1907_, v_i_1906_, v___x_1910_);
v___x_1918_ = lean_array_get_size(v_xs_1903_);
v___x_1919_ = l_Array_range(v___x_1918_);
v___x_1920_ = lean_array_get_size(v___x_1919_);
v___x_1921_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8___closed__0));
v___x_1922_ = lean_nat_dec_lt(v___x_1910_, v___x_1920_);
if (v___x_1922_ == 0)
{
lean_dec_ref(v___x_1919_);
lean_dec(v_v_1909_);
v___y_1913_ = v___x_1921_;
goto v___jp_1912_;
}
else
{
size_t v___x_1923_; size_t v___x_1924_; lean_object* v___x_1925_; 
v___x_1923_ = ((size_t)0ULL);
v___x_1924_ = lean_usize_of_nat(v___x_1920_);
lean_inc_ref(v_f_1904_);
v___x_1925_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__6(v_xs_1903_, v_f_1904_, v_v_1909_, v___x_1919_, v___x_1923_, v___x_1924_, v___x_1921_);
lean_dec_ref(v___x_1919_);
lean_dec(v_v_1909_);
v___y_1913_ = v___x_1925_;
goto v___jp_1912_;
}
v___jp_1912_:
{
size_t v___x_1914_; size_t v___x_1915_; lean_object* v___x_1916_; 
v___x_1914_ = ((size_t)1ULL);
v___x_1915_ = lean_usize_add(v_i_1906_, v___x_1914_);
v___x_1916_ = lean_array_uset(v_bs_x27_1911_, v_i_1906_, v___y_1913_);
v_i_1906_ = v___x_1915_;
v_bs_1907_ = v___x_1916_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8___boxed(lean_object* v_xs_1926_, lean_object* v_f_1927_, lean_object* v_sz_1928_, lean_object* v_i_1929_, lean_object* v_bs_1930_){
_start:
{
size_t v_sz_boxed_1931_; size_t v_i_boxed_1932_; lean_object* v_res_1933_; 
v_sz_boxed_1931_ = lean_unbox_usize(v_sz_1928_);
lean_dec(v_sz_1928_);
v_i_boxed_1932_ = lean_unbox_usize(v_i_1929_);
lean_dec(v_i_1929_);
v_res_1933_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8(v_xs_1926_, v_f_1927_, v_sz_boxed_1931_, v_i_boxed_1932_, v_bs_1930_);
lean_dec_ref(v_xs_1926_);
return v_res_1933_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__11(lean_object* v_as_1934_, size_t v_i_1935_, size_t v_stop_1936_, lean_object* v_b_1937_){
_start:
{
uint8_t v___x_1938_; 
v___x_1938_ = lean_usize_dec_eq(v_i_1935_, v_stop_1936_);
if (v___x_1938_ == 0)
{
lean_object* v___x_1939_; lean_object* v___x_1940_; size_t v___x_1941_; size_t v___x_1942_; 
v___x_1939_ = lean_array_uget_borrowed(v_as_1934_, v_i_1935_);
v___x_1940_ = l_Array_append___redArg(v_b_1937_, v___x_1939_);
v___x_1941_ = ((size_t)1ULL);
v___x_1942_ = lean_usize_add(v_i_1935_, v___x_1941_);
v_i_1935_ = v___x_1942_;
v_b_1937_ = v___x_1940_;
goto _start;
}
else
{
return v_b_1937_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__11___boxed(lean_object* v_as_1944_, lean_object* v_i_1945_, lean_object* v_stop_1946_, lean_object* v_b_1947_){
_start:
{
size_t v_i_boxed_1948_; size_t v_stop_boxed_1949_; lean_object* v_res_1950_; 
v_i_boxed_1948_ = lean_unbox_usize(v_i_1945_);
lean_dec(v_i_1945_);
v_stop_boxed_1949_ = lean_unbox_usize(v_stop_1946_);
lean_dec(v_stop_1946_);
v_res_1950_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__11(v_as_1944_, v_i_boxed_1948_, v_stop_boxed_1949_, v_b_1947_);
lean_dec_ref(v_as_1944_);
return v_res_1950_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__7___closed__0(void){
_start:
{
lean_object* v___x_1951_; 
v___x_1951_ = l_Array_instInhabited(lean_box(0));
return v___x_1951_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__7(lean_object* v_msg_1952_){
_start:
{
lean_object* v___x_1953_; lean_object* v___x_1954_; 
v___x_1953_ = lean_obj_once(&l_panic___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__7___closed__0, &l_panic___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__7___closed__0_once, _init_l_panic___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__7___closed__0);
v___x_1954_ = lean_panic_fn_borrowed(v___x_1953_, v_msg_1952_);
return v___x_1954_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9___redArg(lean_object* v_xs_1955_, lean_object* v_ys_1956_, lean_object* v_x_1957_){
_start:
{
lean_object* v_zero_1958_; uint8_t v_isZero_1959_; 
v_zero_1958_ = lean_unsigned_to_nat(0u);
v_isZero_1959_ = lean_nat_dec_eq(v_x_1957_, v_zero_1958_);
if (v_isZero_1959_ == 1)
{
lean_dec(v_x_1957_);
return v_isZero_1959_;
}
else
{
lean_object* v_one_1960_; lean_object* v_n_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; uint8_t v___x_1964_; 
v_one_1960_ = lean_unsigned_to_nat(1u);
v_n_1961_ = lean_nat_sub(v_x_1957_, v_one_1960_);
lean_dec(v_x_1957_);
v___x_1962_ = lean_array_fget_borrowed(v_xs_1955_, v_n_1961_);
v___x_1963_ = lean_array_fget_borrowed(v_ys_1956_, v_n_1961_);
v___x_1964_ = lean_nat_dec_eq(v___x_1962_, v___x_1963_);
if (v___x_1964_ == 0)
{
lean_dec(v_n_1961_);
return v___x_1964_;
}
else
{
v_x_1957_ = v_n_1961_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9___redArg___boxed(lean_object* v_xs_1966_, lean_object* v_ys_1967_, lean_object* v_x_1968_){
_start:
{
uint8_t v_res_1969_; lean_object* v_r_1970_; 
v_res_1969_ = l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9___redArg(v_xs_1966_, v_ys_1967_, v_x_1968_);
lean_dec_ref(v_ys_1967_);
lean_dec_ref(v_xs_1966_);
v_r_1970_ = lean_box(v_res_1969_);
return v_r_1970_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__2(void){
_start:
{
lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; 
v___x_1973_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__1));
v___x_1974_ = lean_unsigned_to_nat(2u);
v___x_1975_ = lean_unsigned_to_nat(63u);
v___x_1976_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__0));
v___x_1977_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__0));
v___x_1978_ = l_mkPanicMessageWithDecl(v___x_1977_, v___x_1976_, v___x_1975_, v___x_1974_, v___x_1973_);
return v___x_1978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5(lean_object* v_f_1981_, lean_object* v_xs_1982_, lean_object* v_ys_1983_){
_start:
{
size_t v_sz_1987_; size_t v___x_1988_; lean_object* v_positions_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___y_1993_; lean_object* v___y_1999_; lean_object* v___y_2000_; lean_object* v___y_2001_; lean_object* v___y_2002_; lean_object* v___y_2005_; lean_object* v___y_2006_; lean_object* v___y_2007_; lean_object* v___y_2008_; lean_object* v___y_2011_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; uint8_t v___x_2021_; 
v_sz_1987_ = lean_array_size(v_ys_1983_);
v___x_1988_ = ((size_t)0ULL);
v_positions_1989_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8(v_xs_1982_, v_f_1981_, v_sz_1987_, v___x_1988_, v_ys_1983_);
v___x_1990_ = lean_array_get_size(v_xs_1982_);
v___x_1991_ = l_Array_range(v___x_1990_);
v___x_2018_ = lean_unsigned_to_nat(0u);
v___x_2019_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__3));
v___x_2020_ = lean_array_get_size(v_positions_1989_);
v___x_2021_ = lean_nat_dec_lt(v___x_2018_, v___x_2020_);
if (v___x_2021_ == 0)
{
v___y_2011_ = v___x_2019_;
goto v___jp_2010_;
}
else
{
size_t v___x_2022_; lean_object* v___x_2023_; 
v___x_2022_ = lean_usize_of_nat(v___x_2020_);
v___x_2023_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__11(v_positions_1989_, v___x_1988_, v___x_2022_, v___x_2019_);
v___y_2011_ = v___x_2023_;
goto v___jp_2010_;
}
v___jp_1984_:
{
lean_object* v___x_1985_; lean_object* v___x_1986_; 
v___x_1985_ = lean_obj_once(&l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__2, &l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__2_once, _init_l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__2);
v___x_1986_ = l_panic___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__7(v___x_1985_);
return v___x_1986_;
}
v___jp_1992_:
{
lean_object* v___x_1994_; lean_object* v___x_1995_; uint8_t v___x_1996_; 
v___x_1994_ = lean_array_get_size(v___x_1991_);
v___x_1995_ = lean_array_get_size(v___y_1993_);
v___x_1996_ = lean_nat_dec_eq(v___x_1994_, v___x_1995_);
if (v___x_1996_ == 0)
{
lean_dec_ref(v___y_1993_);
lean_dec_ref(v___x_1991_);
lean_dec_ref(v_positions_1989_);
goto v___jp_1984_;
}
else
{
uint8_t v___x_1997_; 
v___x_1997_ = l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9___redArg(v___x_1991_, v___y_1993_, v___x_1994_);
lean_dec_ref(v___y_1993_);
lean_dec_ref(v___x_1991_);
if (v___x_1997_ == 0)
{
lean_dec_ref(v_positions_1989_);
goto v___jp_1984_;
}
else
{
return v_positions_1989_;
}
}
}
v___jp_1998_:
{
lean_object* v___x_2003_; 
v___x_2003_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg(v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_);
lean_dec(v___y_2002_);
lean_dec(v___y_1999_);
v___y_1993_ = v___x_2003_;
goto v___jp_1992_;
}
v___jp_2004_:
{
uint8_t v___x_2009_; 
v___x_2009_ = lean_nat_dec_le(v___y_2008_, v___y_2005_);
if (v___x_2009_ == 0)
{
lean_dec(v___y_2005_);
lean_inc(v___y_2008_);
v___y_1999_ = v___y_2006_;
v___y_2000_ = v___y_2007_;
v___y_2001_ = v___y_2008_;
v___y_2002_ = v___y_2008_;
goto v___jp_1998_;
}
else
{
v___y_1999_ = v___y_2006_;
v___y_2000_ = v___y_2007_;
v___y_2001_ = v___y_2008_;
v___y_2002_ = v___y_2005_;
goto v___jp_1998_;
}
}
v___jp_2010_:
{
lean_object* v___x_2012_; lean_object* v___x_2013_; uint8_t v___x_2014_; 
v___x_2012_ = lean_array_get_size(v___y_2011_);
v___x_2013_ = lean_unsigned_to_nat(0u);
v___x_2014_ = lean_nat_dec_eq(v___x_2012_, v___x_2013_);
if (v___x_2014_ == 0)
{
lean_object* v___x_2015_; lean_object* v___x_2016_; uint8_t v___x_2017_; 
v___x_2015_ = lean_unsigned_to_nat(1u);
v___x_2016_ = lean_nat_sub(v___x_2012_, v___x_2015_);
v___x_2017_ = lean_nat_dec_le(v___x_2013_, v___x_2016_);
if (v___x_2017_ == 0)
{
lean_inc(v___x_2016_);
v___y_2005_ = v___x_2016_;
v___y_2006_ = v___x_2012_;
v___y_2007_ = v___y_2011_;
v___y_2008_ = v___x_2016_;
goto v___jp_2004_;
}
else
{
v___y_2005_ = v___x_2016_;
v___y_2006_ = v___x_2012_;
v___y_2007_ = v___y_2011_;
v___y_2008_ = v___x_2013_;
goto v___jp_2004_;
}
}
else
{
v___y_1993_ = v___y_2011_;
goto v___jp_1992_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___boxed(lean_object* v_f_2024_, lean_object* v_xs_2025_, lean_object* v_ys_2026_){
_start:
{
lean_object* v_res_2027_; 
v_res_2027_ = l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5(v_f_2024_, v_xs_2025_, v_ys_2026_);
lean_dec_ref(v_xs_2025_);
return v_res_2027_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__0(lean_object* v_a_2028_, lean_object* v_a_2029_){
_start:
{
if (lean_obj_tag(v_a_2028_) == 0)
{
lean_object* v___x_2030_; 
v___x_2030_ = l_List_reverse___redArg(v_a_2029_);
return v___x_2030_;
}
else
{
lean_object* v_head_2031_; lean_object* v_tail_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2043_; 
v_head_2031_ = lean_ctor_get(v_a_2028_, 0);
v_tail_2032_ = lean_ctor_get(v_a_2028_, 1);
v_isSharedCheck_2043_ = !lean_is_exclusive(v_a_2028_);
if (v_isSharedCheck_2043_ == 0)
{
v___x_2034_ = v_a_2028_;
v_isShared_2035_ = v_isSharedCheck_2043_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_tail_2032_);
lean_inc(v_head_2031_);
lean_dec(v_a_2028_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2043_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2040_; 
v___x_2036_ = l_Nat_reprFast(v_head_2031_);
v___x_2037_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2037_, 0, v___x_2036_);
v___x_2038_ = l_Lean_MessageData_ofFormat(v___x_2037_);
if (v_isShared_2035_ == 0)
{
lean_ctor_set(v___x_2034_, 1, v_a_2029_);
lean_ctor_set(v___x_2034_, 0, v___x_2038_);
v___x_2040_ = v___x_2034_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2042_; 
v_reuseFailAlloc_2042_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2042_, 0, v___x_2038_);
lean_ctor_set(v_reuseFailAlloc_2042_, 1, v_a_2029_);
v___x_2040_ = v_reuseFailAlloc_2042_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
v_a_2028_ = v_tail_2032_;
v_a_2029_ = v___x_2040_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__20(lean_object* v_a_2044_, lean_object* v_a_2045_){
_start:
{
if (lean_obj_tag(v_a_2044_) == 0)
{
lean_object* v___x_2046_; 
v___x_2046_ = l_List_reverse___redArg(v_a_2045_);
return v___x_2046_;
}
else
{
lean_object* v_head_2047_; lean_object* v_tail_2048_; lean_object* v___x_2050_; uint8_t v_isShared_2051_; uint8_t v_isSharedCheck_2060_; 
v_head_2047_ = lean_ctor_get(v_a_2044_, 0);
v_tail_2048_ = lean_ctor_get(v_a_2044_, 1);
v_isSharedCheck_2060_ = !lean_is_exclusive(v_a_2044_);
if (v_isSharedCheck_2060_ == 0)
{
v___x_2050_ = v_a_2044_;
v_isShared_2051_ = v_isSharedCheck_2060_;
goto v_resetjp_2049_;
}
else
{
lean_inc(v_tail_2048_);
lean_inc(v_head_2047_);
lean_dec(v_a_2044_);
v___x_2050_ = lean_box(0);
v_isShared_2051_ = v_isSharedCheck_2060_;
goto v_resetjp_2049_;
}
v_resetjp_2049_:
{
lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2057_; 
v___x_2052_ = lean_array_to_list(v_head_2047_);
v___x_2053_ = lean_box(0);
v___x_2054_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__0(v___x_2052_, v___x_2053_);
v___x_2055_ = l_Lean_MessageData_ofList(v___x_2054_);
if (v_isShared_2051_ == 0)
{
lean_ctor_set(v___x_2050_, 1, v_a_2045_);
lean_ctor_set(v___x_2050_, 0, v___x_2055_);
v___x_2057_ = v___x_2050_;
goto v_reusejp_2056_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v___x_2055_);
lean_ctor_set(v_reuseFailAlloc_2059_, 1, v_a_2045_);
v___x_2057_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2056_;
}
v_reusejp_2056_:
{
v_a_2044_ = v_tail_2048_;
v_a_2045_ = v___x_2057_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__9(void){
_start:
{
lean_object* v___x_2075_; lean_object* v___x_2076_; 
v___x_2075_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__8));
v___x_2076_ = l_Lean_stringToMessageData(v___x_2075_);
return v___x_2076_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__11(void){
_start:
{
lean_object* v___x_2078_; lean_object* v___x_2079_; 
v___x_2078_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__10));
v___x_2079_ = l_Lean_stringToMessageData(v___x_2078_);
return v___x_2079_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion(lean_object* v_preDefs_2080_, lean_object* v_fixedParamPerms_2081_, lean_object* v_xs_2082_, lean_object* v_recArgInfos_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_, lean_object* v_a_2086_, lean_object* v_a_2087_){
_start:
{
size_t v_sz_2089_; size_t v___x_2090_; lean_object* v___x_2091_; 
v_sz_2089_ = lean_array_size(v_preDefs_2080_);
v___x_2090_ = ((size_t)0ULL);
lean_inc_ref(v_preDefs_2080_);
lean_inc_ref(v_xs_2082_);
v___x_2091_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___redArg(v_fixedParamPerms_2081_, v_xs_2082_, v_sz_2089_, v___x_2090_, v_preDefs_2080_, v_a_2084_, v_a_2085_, v_a_2086_, v_a_2087_);
if (lean_obj_tag(v___x_2091_) == 0)
{
lean_object* v_a_2092_; lean_object* v___x_2093_; 
v_a_2092_ = lean_ctor_get(v___x_2091_, 0);
lean_inc(v_a_2092_);
lean_dec_ref_known(v___x_2091_, 1);
lean_inc_ref(v_preDefs_2080_);
lean_inc_ref(v_xs_2082_);
v___x_2093_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___redArg(v_fixedParamPerms_2081_, v_xs_2082_, v_sz_2089_, v___x_2090_, v_preDefs_2080_, v_a_2084_, v_a_2085_, v_a_2086_, v_a_2087_);
if (lean_obj_tag(v___x_2093_) == 0)
{
lean_object* v_a_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v_indGroupInst_2098_; lean_object* v_toIndGroupInfo_2099_; lean_object* v_all_2100_; lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2188_; 
v_a_2094_ = lean_ctor_get(v___x_2093_, 0);
lean_inc(v_a_2094_);
lean_dec_ref_known(v___x_2093_, 1);
v___x_2095_ = l_Lean_Elab_Structural_instInhabitedRecArgInfo_default;
v___x_2096_ = lean_unsigned_to_nat(0u);
v___x_2097_ = lean_array_get_borrowed(v___x_2095_, v_recArgInfos_2083_, v___x_2096_);
v_indGroupInst_2098_ = lean_ctor_get(v___x_2097_, 4);
v_toIndGroupInfo_2099_ = lean_ctor_get(v_indGroupInst_2098_, 0);
lean_inc_ref(v_toIndGroupInfo_2099_);
v_all_2100_ = lean_ctor_get(v_toIndGroupInfo_2099_, 0);
v_isSharedCheck_2188_ = !lean_is_exclusive(v_toIndGroupInfo_2099_);
if (v_isSharedCheck_2188_ == 0)
{
lean_object* v_unused_2189_; 
v_unused_2189_ = lean_ctor_get(v_toIndGroupInfo_2099_, 1);
lean_dec(v_unused_2189_);
v___x_2102_ = v_toIndGroupInfo_2099_;
v_isShared_2103_ = v_isSharedCheck_2188_;
goto v_resetjp_2101_;
}
else
{
lean_inc(v_all_2100_);
lean_dec(v_toIndGroupInfo_2099_);
v___x_2102_ = lean_box(0);
v_isShared_2103_ = v_isSharedCheck_2188_;
goto v_resetjp_2101_;
}
v_resetjp_2101_:
{
lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; 
v___x_2104_ = lean_box(0);
v___x_2105_ = lean_array_get(v___x_2104_, v_all_2100_, v___x_2096_);
lean_dec_ref(v_all_2100_);
v___x_2106_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4(v___x_2105_, v_a_2084_, v_a_2085_, v_a_2086_, v_a_2087_);
if (lean_obj_tag(v___x_2106_) == 0)
{
lean_object* v_a_2107_; lean_object* v___x_2108_; lean_object* v___f_2109_; lean_object* v___x_2110_; lean_object* v_a_2111_; lean_object* v___f_2112_; lean_object* v___f_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___y_2119_; lean_object* v___y_2120_; lean_object* v___y_2121_; lean_object* v___y_2122_; uint8_t v___x_2156_; 
v_a_2107_ = lean_ctor_get(v___x_2106_, 0);
lean_inc(v_a_2107_);
lean_dec_ref_known(v___x_2106_, 1);
v___x_2108_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__3));
v___f_2109_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__4));
v___x_2110_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0(v___x_2108_, v_a_2084_, v_a_2085_, v_a_2086_, v_a_2087_);
v_a_2111_ = lean_ctor_get(v___x_2110_, 0);
lean_inc(v_a_2111_);
lean_dec_ref(v___x_2110_);
v___f_2112_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__5));
v___f_2113_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__6));
v___x_2114_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_2115_ = l_Lean_InductiveVal_numTypeFormers(v_a_2107_);
v___x_2116_ = l_Array_range(v___x_2115_);
v___x_2117_ = l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5(v___f_2113_, v_recArgInfos_2083_, v___x_2116_);
v___x_2156_ = lean_unbox(v_a_2111_);
lean_dec(v_a_2111_);
if (v___x_2156_ == 0)
{
lean_del_object(v___x_2102_);
v___y_2119_ = v_a_2084_;
v___y_2120_ = v_a_2085_;
v___y_2121_ = v_a_2086_;
v___y_2122_ = v_a_2087_;
goto v___jp_2118_;
}
else
{
lean_object* v_toConstantVal_2157_; lean_object* v_name_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2162_; 
v_toConstantVal_2157_ = lean_ctor_get(v_a_2107_, 0);
v_name_2158_ = lean_ctor_get(v_toConstantVal_2157_, 0);
v___x_2159_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__9, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__9_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__9);
lean_inc(v_name_2158_);
v___x_2160_ = l_Lean_MessageData_ofName(v_name_2158_);
if (v_isShared_2103_ == 0)
{
lean_ctor_set_tag(v___x_2102_, 7);
lean_ctor_set(v___x_2102_, 1, v___x_2160_);
lean_ctor_set(v___x_2102_, 0, v___x_2159_);
v___x_2162_ = v___x_2102_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v___x_2159_);
lean_ctor_set(v_reuseFailAlloc_2179_, 1, v___x_2160_);
v___x_2162_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; 
v___x_2163_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__11, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__11_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__11);
v___x_2164_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2164_, 0, v___x_2162_);
lean_ctor_set(v___x_2164_, 1, v___x_2163_);
lean_inc_ref(v___x_2117_);
v___x_2165_ = lean_array_to_list(v___x_2117_);
v___x_2166_ = lean_box(0);
v___x_2167_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__20(v___x_2165_, v___x_2166_);
v___x_2168_ = l_Lean_MessageData_ofList(v___x_2167_);
v___x_2169_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2169_, 0, v___x_2164_);
lean_ctor_set(v___x_2169_, 1, v___x_2168_);
v___x_2170_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_2108_, v___x_2169_, v_a_2084_, v_a_2085_, v_a_2086_, v_a_2087_);
if (lean_obj_tag(v___x_2170_) == 0)
{
lean_dec_ref_known(v___x_2170_, 1);
v___y_2119_ = v_a_2084_;
v___y_2120_ = v_a_2085_;
v___y_2121_ = v_a_2086_;
v___y_2122_ = v_a_2087_;
goto v___jp_2118_;
}
else
{
lean_object* v_a_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2178_; 
lean_dec_ref(v___x_2117_);
lean_dec(v_a_2107_);
lean_dec(v_a_2094_);
lean_dec(v_a_2092_);
lean_dec_ref(v_recArgInfos_2083_);
lean_dec_ref(v_xs_2082_);
lean_dec_ref(v_fixedParamPerms_2081_);
lean_dec_ref(v_preDefs_2080_);
v_a_2171_ = lean_ctor_get(v___x_2170_, 0);
v_isSharedCheck_2178_ = !lean_is_exclusive(v___x_2170_);
if (v_isSharedCheck_2178_ == 0)
{
v___x_2173_ = v___x_2170_;
v_isShared_2174_ = v_isSharedCheck_2178_;
goto v_resetjp_2172_;
}
else
{
lean_inc(v_a_2171_);
lean_dec(v___x_2170_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2178_;
goto v_resetjp_2172_;
}
v_resetjp_2172_:
{
lean_object* v___x_2176_; 
if (v_isShared_2174_ == 0)
{
v___x_2176_ = v___x_2173_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v_a_2171_);
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
}
v___jp_2118_:
{
lean_object* v_toConstantVal_2123_; lean_object* v_numIndices_2124_; lean_object* v_name_2125_; lean_object* v___x_2126_; 
v_toConstantVal_2123_ = lean_ctor_get(v_a_2107_, 0);
lean_inc_ref(v_toConstantVal_2123_);
v_numIndices_2124_ = lean_ctor_get(v_a_2107_, 2);
lean_inc(v_numIndices_2124_);
lean_dec(v_a_2107_);
v_name_2125_ = lean_ctor_get(v_toConstantVal_2123_, 0);
lean_inc(v_name_2125_);
lean_dec_ref(v_toConstantVal_2123_);
v___x_2126_ = l_Lean_Meta_isInductivePredicate(v_name_2125_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_);
if (lean_obj_tag(v___x_2126_) == 0)
{
lean_object* v_a_2127_; lean_object* v___x_2128_; lean_object* v___f_2129_; uint8_t v___x_2130_; 
v_a_2127_ = lean_ctor_get(v___x_2126_, 0);
lean_inc_n(v_a_2127_, 2);
lean_dec_ref_known(v___x_2126_, 1);
v___x_2128_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___boxed__const__1));
lean_inc(v_numIndices_2124_);
lean_inc_ref(v_preDefs_2080_);
lean_inc_ref(v_xs_2082_);
lean_inc_ref(v_fixedParamPerms_2081_);
lean_inc_ref(v___x_2117_);
lean_inc(v_a_2092_);
lean_inc_ref(v_recArgInfos_2083_);
v___f_2129_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___boxed), 21, 14);
lean_closure_set(v___f_2129_, 0, v___f_2109_);
lean_closure_set(v___f_2129_, 1, v_recArgInfos_2083_);
lean_closure_set(v___f_2129_, 2, v_a_2092_);
lean_closure_set(v___f_2129_, 3, v___x_2117_);
lean_closure_set(v___f_2129_, 4, v___x_2128_);
lean_closure_set(v___f_2129_, 5, v_fixedParamPerms_2081_);
lean_closure_set(v___f_2129_, 6, v_xs_2082_);
lean_closure_set(v___f_2129_, 7, v___x_2096_);
lean_closure_set(v___f_2129_, 8, v_preDefs_2080_);
lean_closure_set(v___f_2129_, 9, v_numIndices_2124_);
lean_closure_set(v___f_2129_, 10, v___f_2112_);
lean_closure_set(v___f_2129_, 11, v___x_2108_);
lean_closure_set(v___f_2129_, 12, v_a_2127_);
lean_closure_set(v___f_2129_, 13, v___x_2114_);
v___x_2130_ = lean_unbox(v_a_2127_);
if (v___x_2130_ == 0)
{
size_t v_sz_2131_; lean_object* v___x_2132_; 
lean_dec_ref(v___f_2129_);
v_sz_2131_ = lean_array_size(v_recArgInfos_2083_);
lean_inc_ref(v_recArgInfos_2083_);
v___x_2132_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___redArg(v_a_2092_, v_a_2094_, v_sz_2131_, v___x_2090_, v_recArgInfos_2083_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_);
lean_dec(v_a_2094_);
if (lean_obj_tag(v___x_2132_) == 0)
{
lean_object* v_a_2133_; lean_object* v___x_2134_; uint8_t v___x_2135_; lean_object* v___x_2136_; 
v_a_2133_ = lean_ctor_get(v___x_2132_, 0);
lean_inc(v_a_2133_);
lean_dec_ref_known(v___x_2132_, 1);
v___x_2134_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__7));
v___x_2135_ = lean_unbox(v_a_2127_);
lean_dec(v_a_2127_);
v___x_2136_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2(v___f_2109_, v_recArgInfos_2083_, v_a_2092_, v___x_2117_, v___x_2090_, v_fixedParamPerms_2081_, v_xs_2082_, v___x_2096_, v_preDefs_2080_, v_numIndices_2124_, v___f_2112_, v___x_2108_, v___x_2135_, v___x_2114_, v___x_2134_, v_a_2133_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_);
lean_dec(v_numIndices_2124_);
lean_dec(v_a_2092_);
return v___x_2136_;
}
else
{
lean_object* v_a_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2144_; 
lean_dec(v_a_2127_);
lean_dec(v_numIndices_2124_);
lean_dec_ref(v___x_2117_);
lean_dec(v_a_2092_);
lean_dec_ref(v_recArgInfos_2083_);
lean_dec_ref(v_xs_2082_);
lean_dec_ref(v_fixedParamPerms_2081_);
lean_dec_ref(v_preDefs_2080_);
v_a_2137_ = lean_ctor_get(v___x_2132_, 0);
v_isSharedCheck_2144_ = !lean_is_exclusive(v___x_2132_);
if (v_isSharedCheck_2144_ == 0)
{
v___x_2139_ = v___x_2132_;
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_a_2137_);
lean_dec(v___x_2132_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v___x_2142_; 
if (v_isShared_2140_ == 0)
{
v___x_2142_ = v___x_2139_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v_a_2137_);
v___x_2142_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
return v___x_2142_;
}
}
}
}
else
{
lean_object* v___x_2145_; lean_object* v___f_2146_; lean_object* v___x_2147_; 
lean_dec(v_a_2127_);
lean_dec(v_numIndices_2124_);
lean_dec_ref(v___x_2117_);
lean_dec(v_a_2094_);
lean_dec_ref(v_xs_2082_);
lean_dec_ref(v_fixedParamPerms_2081_);
lean_dec_ref(v_preDefs_2080_);
v___x_2145_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___boxed__const__1));
lean_inc(v_a_2092_);
v___f_2146_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__3___boxed), 10, 4);
lean_closure_set(v___f_2146_, 0, v_recArgInfos_2083_);
lean_closure_set(v___f_2146_, 1, v_a_2092_);
lean_closure_set(v___f_2146_, 2, v___x_2145_);
lean_closure_set(v___f_2146_, 3, v___f_2129_);
v___x_2147_ = l_Lean_Elab_Structural_withFunTypes___redArg(v_a_2092_, v___f_2146_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_);
return v___x_2147_;
}
}
else
{
lean_object* v_a_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2155_; 
lean_dec(v_numIndices_2124_);
lean_dec_ref(v___x_2117_);
lean_dec(v_a_2094_);
lean_dec(v_a_2092_);
lean_dec_ref(v_recArgInfos_2083_);
lean_dec_ref(v_xs_2082_);
lean_dec_ref(v_fixedParamPerms_2081_);
lean_dec_ref(v_preDefs_2080_);
v_a_2148_ = lean_ctor_get(v___x_2126_, 0);
v_isSharedCheck_2155_ = !lean_is_exclusive(v___x_2126_);
if (v_isSharedCheck_2155_ == 0)
{
v___x_2150_ = v___x_2126_;
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_a_2148_);
lean_dec(v___x_2126_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v___x_2153_; 
if (v_isShared_2151_ == 0)
{
v___x_2153_ = v___x_2150_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v_a_2148_);
v___x_2153_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
return v___x_2153_;
}
}
}
}
}
else
{
lean_object* v_a_2180_; lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2187_; 
lean_del_object(v___x_2102_);
lean_dec(v_a_2094_);
lean_dec(v_a_2092_);
lean_dec_ref(v_recArgInfos_2083_);
lean_dec_ref(v_xs_2082_);
lean_dec_ref(v_fixedParamPerms_2081_);
lean_dec_ref(v_preDefs_2080_);
v_a_2180_ = lean_ctor_get(v___x_2106_, 0);
v_isSharedCheck_2187_ = !lean_is_exclusive(v___x_2106_);
if (v_isSharedCheck_2187_ == 0)
{
v___x_2182_ = v___x_2106_;
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
else
{
lean_inc(v_a_2180_);
lean_dec(v___x_2106_);
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
else
{
lean_object* v_a_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2197_; 
lean_dec(v_a_2092_);
lean_dec_ref(v_recArgInfos_2083_);
lean_dec_ref(v_xs_2082_);
lean_dec_ref(v_fixedParamPerms_2081_);
lean_dec_ref(v_preDefs_2080_);
v_a_2190_ = lean_ctor_get(v___x_2093_, 0);
v_isSharedCheck_2197_ = !lean_is_exclusive(v___x_2093_);
if (v_isSharedCheck_2197_ == 0)
{
v___x_2192_ = v___x_2093_;
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_a_2190_);
lean_dec(v___x_2093_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v___x_2195_; 
if (v_isShared_2193_ == 0)
{
v___x_2195_ = v___x_2192_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v_a_2190_);
v___x_2195_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
return v___x_2195_;
}
}
}
}
else
{
lean_object* v_a_2198_; lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2205_; 
lean_dec_ref(v_recArgInfos_2083_);
lean_dec_ref(v_xs_2082_);
lean_dec_ref(v_fixedParamPerms_2081_);
lean_dec_ref(v_preDefs_2080_);
v_a_2198_ = lean_ctor_get(v___x_2091_, 0);
v_isSharedCheck_2205_ = !lean_is_exclusive(v___x_2091_);
if (v_isSharedCheck_2205_ == 0)
{
v___x_2200_ = v___x_2091_;
v_isShared_2201_ = v_isSharedCheck_2205_;
goto v_resetjp_2199_;
}
else
{
lean_inc(v_a_2198_);
lean_dec(v___x_2091_);
v___x_2200_ = lean_box(0);
v_isShared_2201_ = v_isSharedCheck_2205_;
goto v_resetjp_2199_;
}
v_resetjp_2199_:
{
lean_object* v___x_2203_; 
if (v_isShared_2201_ == 0)
{
v___x_2203_ = v___x_2200_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v_a_2198_);
v___x_2203_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
return v___x_2203_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___boxed(lean_object* v_preDefs_2206_, lean_object* v_fixedParamPerms_2207_, lean_object* v_xs_2208_, lean_object* v_recArgInfos_2209_, lean_object* v_a_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_){
_start:
{
lean_object* v_res_2215_; 
v_res_2215_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion(v_preDefs_2206_, v_fixedParamPerms_2207_, v_xs_2208_, v_recArgInfos_2209_, v_a_2210_, v_a_2211_, v_a_2212_, v_a_2213_);
lean_dec(v_a_2213_);
lean_dec_ref(v_a_2212_);
lean_dec(v_a_2211_);
lean_dec_ref(v_a_2210_);
return v_res_2215_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2(lean_object* v_fixedParamPerms_2216_, lean_object* v_xs_2217_, lean_object* v_as_2218_, size_t v_sz_2219_, size_t v_i_2220_, lean_object* v_bs_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_){
_start:
{
lean_object* v___x_2227_; 
v___x_2227_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___redArg(v_fixedParamPerms_2216_, v_xs_2217_, v_sz_2219_, v_i_2220_, v_bs_2221_, v___y_2222_, v___y_2223_, v___y_2224_, v___y_2225_);
return v___x_2227_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___boxed(lean_object* v_fixedParamPerms_2228_, lean_object* v_xs_2229_, lean_object* v_as_2230_, lean_object* v_sz_2231_, lean_object* v_i_2232_, lean_object* v_bs_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_){
_start:
{
size_t v_sz_boxed_2239_; size_t v_i_boxed_2240_; lean_object* v_res_2241_; 
v_sz_boxed_2239_ = lean_unbox_usize(v_sz_2231_);
lean_dec(v_sz_2231_);
v_i_boxed_2240_ = lean_unbox_usize(v_i_2232_);
lean_dec(v_i_2232_);
v_res_2241_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2(v_fixedParamPerms_2228_, v_xs_2229_, v_as_2230_, v_sz_boxed_2239_, v_i_boxed_2240_, v_bs_2233_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_);
lean_dec(v___y_2237_);
lean_dec_ref(v___y_2236_);
lean_dec(v___y_2235_);
lean_dec_ref(v___y_2234_);
lean_dec_ref(v_as_2230_);
lean_dec_ref(v_fixedParamPerms_2228_);
return v_res_2241_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3(lean_object* v_fixedParamPerms_2242_, lean_object* v_xs_2243_, lean_object* v_as_2244_, size_t v_sz_2245_, size_t v_i_2246_, lean_object* v_bs_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_){
_start:
{
lean_object* v___x_2253_; 
v___x_2253_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___redArg(v_fixedParamPerms_2242_, v_xs_2243_, v_sz_2245_, v_i_2246_, v_bs_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_);
return v___x_2253_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___boxed(lean_object* v_fixedParamPerms_2254_, lean_object* v_xs_2255_, lean_object* v_as_2256_, lean_object* v_sz_2257_, lean_object* v_i_2258_, lean_object* v_bs_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_){
_start:
{
size_t v_sz_boxed_2265_; size_t v_i_boxed_2266_; lean_object* v_res_2267_; 
v_sz_boxed_2265_ = lean_unbox_usize(v_sz_2257_);
lean_dec(v_sz_2257_);
v_i_boxed_2266_ = lean_unbox_usize(v_i_2258_);
lean_dec(v_i_2258_);
v_res_2267_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3(v_fixedParamPerms_2254_, v_xs_2255_, v_as_2256_, v_sz_boxed_2265_, v_i_boxed_2266_, v_bs_2259_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_);
lean_dec(v___y_2263_);
lean_dec_ref(v___y_2262_);
lean_dec(v___y_2261_);
lean_dec_ref(v___y_2260_);
lean_dec_ref(v_as_2256_);
lean_dec_ref(v_fixedParamPerms_2254_);
return v_res_2267_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14(lean_object* v_00_u03b3_2268_, lean_object* v_msg_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_){
_start:
{
lean_object* v___x_2275_; 
v___x_2275_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg(v_msg_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_);
return v___x_2275_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___boxed(lean_object* v_00_u03b3_2276_, lean_object* v_msg_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_){
_start:
{
lean_object* v_res_2283_; 
v_res_2283_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14(v_00_u03b3_2276_, v_msg_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_);
lean_dec(v___y_2281_);
lean_dec_ref(v___y_2280_);
lean_dec(v___y_2279_);
lean_dec_ref(v___y_2278_);
return v_res_2283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6(lean_object* v_00_u03b3_2284_, lean_object* v_00_u03b1_2285_, lean_object* v_f_2286_, lean_object* v_positions_2287_, lean_object* v_ys_2288_, lean_object* v_xs_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_){
_start:
{
lean_object* v___x_2295_; 
v___x_2295_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg(v_f_2286_, v_positions_2287_, v_ys_2288_, v_xs_2289_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_);
return v___x_2295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___boxed(lean_object* v_00_u03b3_2296_, lean_object* v_00_u03b1_2297_, lean_object* v_f_2298_, lean_object* v_positions_2299_, lean_object* v_ys_2300_, lean_object* v_xs_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_){
_start:
{
lean_object* v_res_2307_; 
v_res_2307_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6(v_00_u03b3_2296_, v_00_u03b1_2297_, v_f_2298_, v_positions_2299_, v_ys_2300_, v_xs_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_);
lean_dec(v___y_2305_);
lean_dec_ref(v___y_2304_);
lean_dec(v___y_2303_);
lean_dec_ref(v___y_2302_);
lean_dec_ref(v_xs_2301_);
lean_dec_ref(v_ys_2300_);
lean_dec_ref(v_positions_2299_);
return v_res_2307_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7(lean_object* v___x_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_, lean_object* v_funTypes_2311_, lean_object* v_as_2312_, size_t v_sz_2313_, size_t v_i_2314_, lean_object* v_bs_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_){
_start:
{
lean_object* v___x_2321_; 
v___x_2321_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg(v___x_2308_, v_a_2309_, v_a_2310_, v_funTypes_2311_, v_sz_2313_, v_i_2314_, v_bs_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_);
return v___x_2321_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___boxed(lean_object* v___x_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_, lean_object* v_funTypes_2325_, lean_object* v_as_2326_, lean_object* v_sz_2327_, lean_object* v_i_2328_, lean_object* v_bs_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_){
_start:
{
size_t v_sz_boxed_2335_; size_t v_i_boxed_2336_; lean_object* v_res_2337_; 
v_sz_boxed_2335_ = lean_unbox_usize(v_sz_2327_);
lean_dec(v_sz_2327_);
v_i_boxed_2336_ = lean_unbox_usize(v_i_2328_);
lean_dec(v_i_2328_);
v_res_2337_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7(v___x_2322_, v_a_2323_, v_a_2324_, v_funTypes_2325_, v_as_2326_, v_sz_boxed_2335_, v_i_boxed_2336_, v_bs_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_);
lean_dec(v___y_2333_);
lean_dec_ref(v___y_2332_);
lean_dec(v___y_2331_);
lean_dec_ref(v___y_2330_);
lean_dec_ref(v_as_2326_);
return v_res_2337_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8(lean_object* v_fixedParamPerms_2338_, lean_object* v_xs_2339_, lean_object* v_as_2340_, size_t v_sz_2341_, size_t v_i_2342_, lean_object* v_bs_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_){
_start:
{
lean_object* v___x_2349_; 
v___x_2349_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg(v_fixedParamPerms_2338_, v_xs_2339_, v_sz_2341_, v_i_2342_, v_bs_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_);
return v___x_2349_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___boxed(lean_object* v_fixedParamPerms_2350_, lean_object* v_xs_2351_, lean_object* v_as_2352_, lean_object* v_sz_2353_, lean_object* v_i_2354_, lean_object* v_bs_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_){
_start:
{
size_t v_sz_boxed_2361_; size_t v_i_boxed_2362_; lean_object* v_res_2363_; 
v_sz_boxed_2361_ = lean_unbox_usize(v_sz_2353_);
lean_dec(v_sz_2353_);
v_i_boxed_2362_ = lean_unbox_usize(v_i_2354_);
lean_dec(v_i_2354_);
v_res_2363_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8(v_fixedParamPerms_2350_, v_xs_2351_, v_as_2352_, v_sz_boxed_2361_, v_i_boxed_2362_, v_bs_2355_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_);
lean_dec(v___y_2359_);
lean_dec_ref(v___y_2358_);
lean_dec(v___y_2357_);
lean_dec_ref(v___y_2356_);
lean_dec_ref(v_as_2352_);
return v_res_2363_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12(lean_object* v_00_u03b1_2364_, lean_object* v_preDefs_2365_, lean_object* v_k_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_){
_start:
{
lean_object* v___x_2372_; 
v___x_2372_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v_preDefs_2365_, v_k_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_);
return v___x_2372_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___boxed(lean_object* v_00_u03b1_2373_, lean_object* v_preDefs_2374_, lean_object* v_k_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_){
_start:
{
lean_object* v_res_2381_; 
v_res_2381_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12(v_00_u03b1_2373_, v_preDefs_2374_, v_k_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_);
lean_dec(v___y_2379_);
lean_dec_ref(v___y_2378_);
lean_dec(v___y_2377_);
lean_dec_ref(v___y_2376_);
return v_res_2381_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14(uint8_t v_a_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_, lean_object* v_recArgInfos_2385_, lean_object* v___x_2386_, lean_object* v_preDefs_2387_, lean_object* v_a_2388_, lean_object* v_as_2389_, size_t v_sz_2390_, size_t v_i_2391_, lean_object* v_bs_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_){
_start:
{
lean_object* v___x_2398_; 
v___x_2398_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg(v_a_2382_, v_a_2383_, v_a_2384_, v_recArgInfos_2385_, v___x_2386_, v_preDefs_2387_, v_a_2388_, v_sz_2390_, v_i_2391_, v_bs_2392_, v___y_2393_, v___y_2394_, v___y_2395_, v___y_2396_);
return v___x_2398_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___boxed(lean_object* v_a_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_, lean_object* v_recArgInfos_2402_, lean_object* v___x_2403_, lean_object* v_preDefs_2404_, lean_object* v_a_2405_, lean_object* v_as_2406_, lean_object* v_sz_2407_, lean_object* v_i_2408_, lean_object* v_bs_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_){
_start:
{
uint8_t v_a_28131__boxed_2415_; size_t v_sz_boxed_2416_; size_t v_i_boxed_2417_; lean_object* v_res_2418_; 
v_a_28131__boxed_2415_ = lean_unbox(v_a_2399_);
v_sz_boxed_2416_ = lean_unbox_usize(v_sz_2407_);
lean_dec(v_sz_2407_);
v_i_boxed_2417_ = lean_unbox_usize(v_i_2408_);
lean_dec(v_i_2408_);
v_res_2418_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14(v_a_28131__boxed_2415_, v_a_2400_, v_a_2401_, v_recArgInfos_2402_, v___x_2403_, v_preDefs_2404_, v_a_2405_, v_as_2406_, v_sz_boxed_2416_, v_i_boxed_2417_, v_bs_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_);
lean_dec(v___y_2413_);
lean_dec_ref(v___y_2412_);
lean_dec(v___y_2411_);
lean_dec_ref(v___y_2410_);
lean_dec_ref(v_as_2406_);
lean_dec_ref(v_a_2401_);
lean_dec_ref(v_a_2400_);
return v_res_2418_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16_spec__29(lean_object* v_declName_2419_, uint8_t v_s_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_){
_start:
{
lean_object* v___x_2426_; 
v___x_2426_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16_spec__29___redArg(v_declName_2419_, v_s_2420_, v___y_2422_, v___y_2424_);
return v___x_2426_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16_spec__29___boxed(lean_object* v_declName_2427_, lean_object* v_s_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_){
_start:
{
uint8_t v_s_boxed_2434_; lean_object* v_res_2435_; 
v_s_boxed_2434_ = lean_unbox(v_s_2428_);
v_res_2435_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16_spec__29(v_declName_2427_, v_s_boxed_2434_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_);
lean_dec(v___y_2432_);
lean_dec_ref(v___y_2431_);
lean_dec(v___y_2430_);
lean_dec_ref(v___y_2429_);
return v_res_2435_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17(lean_object* v_xs_2436_, uint8_t v_a_2437_, lean_object* v_preDefs_2438_, lean_object* v___x_2439_, lean_object* v_as_2440_, size_t v_sz_2441_, size_t v_i_2442_, lean_object* v_bs_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_){
_start:
{
lean_object* v___x_2449_; 
v___x_2449_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg(v_xs_2436_, v_a_2437_, v_preDefs_2438_, v___x_2439_, v_sz_2441_, v_i_2442_, v_bs_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_);
return v___x_2449_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___boxed(lean_object* v_xs_2450_, lean_object* v_a_2451_, lean_object* v_preDefs_2452_, lean_object* v___x_2453_, lean_object* v_as_2454_, lean_object* v_sz_2455_, lean_object* v_i_2456_, lean_object* v_bs_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_){
_start:
{
uint8_t v_a_28180__boxed_2463_; size_t v_sz_boxed_2464_; size_t v_i_boxed_2465_; lean_object* v_res_2466_; 
v_a_28180__boxed_2463_ = lean_unbox(v_a_2451_);
v_sz_boxed_2464_ = lean_unbox_usize(v_sz_2455_);
lean_dec(v_sz_2455_);
v_i_boxed_2465_ = lean_unbox_usize(v_i_2456_);
lean_dec(v_i_2456_);
v_res_2466_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17(v_xs_2450_, v_a_28180__boxed_2463_, v_preDefs_2452_, v___x_2453_, v_as_2454_, v_sz_boxed_2464_, v_i_boxed_2465_, v_bs_2457_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_);
lean_dec(v___y_2461_);
lean_dec_ref(v___y_2460_);
lean_dec(v___y_2459_);
lean_dec_ref(v___y_2458_);
lean_dec_ref(v_as_2454_);
lean_dec_ref(v_preDefs_2452_);
lean_dec_ref(v_xs_2450_);
return v_res_2466_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18(lean_object* v_a_2467_, lean_object* v_funTypes_2468_, lean_object* v_as_2469_, size_t v_sz_2470_, size_t v_i_2471_, lean_object* v_bs_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_){
_start:
{
lean_object* v___x_2478_; 
v___x_2478_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___redArg(v_a_2467_, v_funTypes_2468_, v_sz_2470_, v_i_2471_, v_bs_2472_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_);
return v___x_2478_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___boxed(lean_object* v_a_2479_, lean_object* v_funTypes_2480_, lean_object* v_as_2481_, lean_object* v_sz_2482_, lean_object* v_i_2483_, lean_object* v_bs_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_){
_start:
{
size_t v_sz_boxed_2490_; size_t v_i_boxed_2491_; lean_object* v_res_2492_; 
v_sz_boxed_2490_ = lean_unbox_usize(v_sz_2482_);
lean_dec(v_sz_2482_);
v_i_boxed_2491_ = lean_unbox_usize(v_i_2483_);
lean_dec(v_i_2483_);
v_res_2492_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18(v_a_2479_, v_funTypes_2480_, v_as_2481_, v_sz_boxed_2490_, v_i_boxed_2491_, v_bs_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_);
lean_dec(v___y_2488_);
lean_dec_ref(v___y_2487_);
lean_dec(v___y_2486_);
lean_dec_ref(v___y_2485_);
lean_dec_ref(v_as_2481_);
lean_dec_ref(v_funTypes_2480_);
lean_dec_ref(v_a_2479_);
return v_res_2492_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19(lean_object* v_a_2493_, lean_object* v_a_2494_, lean_object* v_as_2495_, size_t v_sz_2496_, size_t v_i_2497_, lean_object* v_bs_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_){
_start:
{
lean_object* v___x_2504_; 
v___x_2504_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___redArg(v_a_2493_, v_a_2494_, v_sz_2496_, v_i_2497_, v_bs_2498_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_);
return v___x_2504_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___boxed(lean_object* v_a_2505_, lean_object* v_a_2506_, lean_object* v_as_2507_, lean_object* v_sz_2508_, lean_object* v_i_2509_, lean_object* v_bs_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_){
_start:
{
size_t v_sz_boxed_2516_; size_t v_i_boxed_2517_; lean_object* v_res_2518_; 
v_sz_boxed_2516_ = lean_unbox_usize(v_sz_2508_);
lean_dec(v_sz_2508_);
v_i_boxed_2517_ = lean_unbox_usize(v_i_2509_);
lean_dec(v_i_2509_);
v_res_2518_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19(v_a_2505_, v_a_2506_, v_as_2507_, v_sz_boxed_2516_, v_i_boxed_2517_, v_bs_2510_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_);
lean_dec(v___y_2514_);
lean_dec_ref(v___y_2513_);
lean_dec(v___y_2512_);
lean_dec_ref(v___y_2511_);
lean_dec_ref(v_as_2507_);
lean_dec_ref(v_a_2506_);
lean_dec_ref(v_a_2505_);
return v_res_2518_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4(lean_object* v_00_u03b1_2519_, lean_object* v_msg_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_){
_start:
{
lean_object* v___x_2526_; 
v___x_2526_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg(v_msg_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_);
return v___x_2526_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___boxed(lean_object* v_00_u03b1_2527_, lean_object* v_msg_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_){
_start:
{
lean_object* v_res_2534_; 
v_res_2534_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4(v_00_u03b1_2527_, v_msg_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_);
lean_dec(v___y_2532_);
lean_dec_ref(v___y_2531_);
lean_dec(v___y_2530_);
lean_dec_ref(v___y_2529_);
return v_res_2534_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9(lean_object* v_xs_2535_, lean_object* v_ys_2536_, lean_object* v_hsz_2537_, lean_object* v_x_2538_, lean_object* v_x_2539_){
_start:
{
uint8_t v___x_2540_; 
v___x_2540_ = l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9___redArg(v_xs_2535_, v_ys_2536_, v_x_2538_);
return v___x_2540_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9___boxed(lean_object* v_xs_2541_, lean_object* v_ys_2542_, lean_object* v_hsz_2543_, lean_object* v_x_2544_, lean_object* v_x_2545_){
_start:
{
uint8_t v_res_2546_; lean_object* v_r_2547_; 
v_res_2546_ = l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9(v_xs_2541_, v_ys_2542_, v_hsz_2543_, v_x_2544_, v_x_2545_);
lean_dec_ref(v_ys_2542_);
lean_dec_ref(v_xs_2541_);
v_r_2547_ = lean_box(v_res_2546_);
return v_r_2547_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10(lean_object* v_n_2548_, lean_object* v_as_2549_, lean_object* v_lo_2550_, lean_object* v_hi_2551_, lean_object* v_w_2552_, lean_object* v_hlo_2553_, lean_object* v_hhi_2554_){
_start:
{
lean_object* v___x_2555_; 
v___x_2555_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg(v_n_2548_, v_as_2549_, v_lo_2550_, v_hi_2551_);
return v___x_2555_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___boxed(lean_object* v_n_2556_, lean_object* v_as_2557_, lean_object* v_lo_2558_, lean_object* v_hi_2559_, lean_object* v_w_2560_, lean_object* v_hlo_2561_, lean_object* v_hhi_2562_){
_start:
{
lean_object* v_res_2563_; 
v_res_2563_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10(v_n_2556_, v_as_2557_, v_lo_2558_, v_hi_2559_, v_w_2560_, v_hlo_2561_, v_hhi_2562_);
lean_dec(v_hi_2559_);
lean_dec(v_n_2556_);
return v_res_2563_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15(lean_object* v_00_u03b1_2564_, lean_object* v_00_u03b3_2565_, lean_object* v_xs_2566_, lean_object* v_f_2567_, lean_object* v_as_2568_, lean_object* v_bs_2569_, lean_object* v_i_2570_, lean_object* v_cs_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_){
_start:
{
lean_object* v___x_2577_; 
v___x_2577_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15___redArg(v_xs_2566_, v_f_2567_, v_as_2568_, v_bs_2569_, v_i_2570_, v_cs_2571_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_);
return v___x_2577_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15___boxed(lean_object* v_00_u03b1_2578_, lean_object* v_00_u03b3_2579_, lean_object* v_xs_2580_, lean_object* v_f_2581_, lean_object* v_as_2582_, lean_object* v_bs_2583_, lean_object* v_i_2584_, lean_object* v_cs_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_){
_start:
{
lean_object* v_res_2591_; 
v_res_2591_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15(v_00_u03b1_2578_, v_00_u03b3_2579_, v_xs_2580_, v_f_2581_, v_as_2582_, v_bs_2583_, v_i_2584_, v_cs_2585_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_);
lean_dec(v___y_2589_);
lean_dec_ref(v___y_2588_);
lean_dec(v___y_2587_);
lean_dec_ref(v___y_2586_);
lean_dec_ref(v_bs_2583_);
lean_dec_ref(v_as_2582_);
lean_dec_ref(v_xs_2580_);
return v_res_2591_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25(lean_object* v_env_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_){
_start:
{
lean_object* v___x_2598_; 
v___x_2598_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg(v_env_2592_, v___y_2594_, v___y_2596_);
return v___x_2598_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___boxed(lean_object* v_env_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_){
_start:
{
lean_object* v_res_2605_; 
v_res_2605_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25(v_env_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_);
lean_dec(v___y_2603_);
lean_dec_ref(v___y_2602_);
lean_dec(v___y_2601_);
lean_dec_ref(v___y_2600_);
return v_res_2605_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23(lean_object* v_00_u03b1_2606_, lean_object* v_env_2607_, lean_object* v_x_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_){
_start:
{
lean_object* v___x_2614_; 
v___x_2614_ = l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23___redArg(v_env_2607_, v_x_2608_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_);
return v___x_2614_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23___boxed(lean_object* v_00_u03b1_2615_, lean_object* v_env_2616_, lean_object* v_x_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_){
_start:
{
lean_object* v_res_2623_; 
v_res_2623_ = l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23(v_00_u03b1_2615_, v_env_2616_, v_x_2617_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_);
lean_dec(v___y_2621_);
lean_dec_ref(v___y_2620_);
lean_dec(v___y_2619_);
lean_dec_ref(v___y_2618_);
return v_res_2623_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11(lean_object* v_n_2624_, lean_object* v_lo_2625_, lean_object* v_hi_2626_, lean_object* v_hhi_2627_, lean_object* v_pivot_2628_, lean_object* v_as_2629_, lean_object* v_i_2630_, lean_object* v_k_2631_, lean_object* v_ilo_2632_, lean_object* v_ik_2633_, lean_object* v_w_2634_){
_start:
{
lean_object* v___x_2635_; 
v___x_2635_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11___redArg(v_hi_2626_, v_pivot_2628_, v_as_2629_, v_i_2630_, v_k_2631_);
return v___x_2635_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11___boxed(lean_object* v_n_2636_, lean_object* v_lo_2637_, lean_object* v_hi_2638_, lean_object* v_hhi_2639_, lean_object* v_pivot_2640_, lean_object* v_as_2641_, lean_object* v_i_2642_, lean_object* v_k_2643_, lean_object* v_ilo_2644_, lean_object* v_ik_2645_, lean_object* v_w_2646_){
_start:
{
lean_object* v_res_2647_; 
v_res_2647_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11(v_n_2636_, v_lo_2637_, v_hi_2638_, v_hhi_2639_, v_pivot_2640_, v_as_2641_, v_i_2642_, v_k_2643_, v_ilo_2644_, v_ik_2645_, v_w_2646_);
lean_dec(v_pivot_2640_);
lean_dec(v_hi_2638_);
lean_dec(v_lo_2637_);
lean_dec(v_n_2636_);
return v_res_2647_;
}
}
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___lam__0(lean_object* v_x_2648_){
_start:
{
uint8_t v___x_2649_; 
v___x_2649_ = 0;
return v___x_2649_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___lam__0___boxed(lean_object* v_x_2650_){
_start:
{
uint8_t v_res_2651_; lean_object* v_r_2652_; 
v_res_2651_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___lam__0(v_x_2650_);
lean_dec(v_x_2650_);
v_r_2652_ = lean_box(v_res_2651_);
return v_r_2652_;
}
}
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___lam__1(lean_object* v_fvarId_2653_, lean_object* v_x_2654_){
_start:
{
uint8_t v___x_2655_; 
v___x_2655_ = l_Lean_instBEqFVarId_beq(v_fvarId_2653_, v_x_2654_);
return v___x_2655_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___lam__1___boxed(lean_object* v_fvarId_2656_, lean_object* v_x_2657_){
_start:
{
uint8_t v_res_2658_; lean_object* v_r_2659_; 
v_res_2658_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___lam__1(v_fvarId_2656_, v_x_2657_);
lean_dec(v_x_2657_);
lean_dec(v_fvarId_2656_);
v_r_2659_ = lean_box(v_res_2658_);
return v_r_2659_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; 
v___x_2661_ = lean_box(0);
v___x_2662_ = lean_unsigned_to_nat(16u);
v___x_2663_ = lean_mk_array(v___x_2662_, v___x_2661_);
return v___x_2663_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; 
v___x_2664_ = lean_obj_once(&l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__1, &l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__1_once, _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__1);
v___x_2665_ = lean_unsigned_to_nat(0u);
v___x_2666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2666_, 0, v___x_2665_);
lean_ctor_set(v___x_2666_, 1, v___x_2664_);
return v___x_2666_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg(lean_object* v_e_2667_, lean_object* v_fvarId_2668_, lean_object* v___y_2669_){
_start:
{
lean_object* v___x_2671_; uint8_t v_fst_2673_; lean_object* v_mctx_2674_; lean_object* v___y_2692_; lean_object* v_mctx_2697_; lean_object* v___f_2698_; lean_object* v___f_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; uint8_t v___x_2702_; 
v___x_2671_ = lean_st_ref_get(v___y_2669_);
v_mctx_2697_ = lean_ctor_get(v___x_2671_, 0);
lean_inc_ref_n(v_mctx_2697_, 2);
lean_dec(v___x_2671_);
v___f_2698_ = ((lean_object*)(l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__0));
v___f_2699_ = lean_alloc_closure((void*)(l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_2699_, 0, v_fvarId_2668_);
v___x_2700_ = lean_obj_once(&l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__2, &l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__2_once, _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__2);
v___x_2701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2701_, 0, v___x_2700_);
lean_ctor_set(v___x_2701_, 1, v_mctx_2697_);
v___x_2702_ = l_Lean_Expr_hasFVar(v_e_2667_);
if (v___x_2702_ == 0)
{
uint8_t v___x_2703_; 
v___x_2703_ = l_Lean_Expr_hasMVar(v_e_2667_);
if (v___x_2703_ == 0)
{
lean_dec_ref_known(v___x_2701_, 2);
lean_dec_ref(v___f_2699_);
lean_dec_ref(v_e_2667_);
v_fst_2673_ = v___x_2703_;
v_mctx_2674_ = v_mctx_2697_;
goto v___jp_2672_;
}
else
{
lean_object* v___x_2704_; 
lean_dec_ref(v_mctx_2697_);
v___x_2704_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2699_, v___f_2698_, v_e_2667_, v___x_2701_);
v___y_2692_ = v___x_2704_;
goto v___jp_2691_;
}
}
else
{
lean_object* v___x_2705_; 
lean_dec_ref(v_mctx_2697_);
v___x_2705_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2699_, v___f_2698_, v_e_2667_, v___x_2701_);
v___y_2692_ = v___x_2705_;
goto v___jp_2691_;
}
v___jp_2672_:
{
lean_object* v___x_2675_; lean_object* v_cache_2676_; lean_object* v_zetaDeltaFVarIds_2677_; lean_object* v_postponed_2678_; lean_object* v_diag_2679_; lean_object* v___x_2681_; uint8_t v_isShared_2682_; uint8_t v_isSharedCheck_2689_; 
v___x_2675_ = lean_st_ref_take(v___y_2669_);
v_cache_2676_ = lean_ctor_get(v___x_2675_, 1);
v_zetaDeltaFVarIds_2677_ = lean_ctor_get(v___x_2675_, 2);
v_postponed_2678_ = lean_ctor_get(v___x_2675_, 3);
v_diag_2679_ = lean_ctor_get(v___x_2675_, 4);
v_isSharedCheck_2689_ = !lean_is_exclusive(v___x_2675_);
if (v_isSharedCheck_2689_ == 0)
{
lean_object* v_unused_2690_; 
v_unused_2690_ = lean_ctor_get(v___x_2675_, 0);
lean_dec(v_unused_2690_);
v___x_2681_ = v___x_2675_;
v_isShared_2682_ = v_isSharedCheck_2689_;
goto v_resetjp_2680_;
}
else
{
lean_inc(v_diag_2679_);
lean_inc(v_postponed_2678_);
lean_inc(v_zetaDeltaFVarIds_2677_);
lean_inc(v_cache_2676_);
lean_dec(v___x_2675_);
v___x_2681_ = lean_box(0);
v_isShared_2682_ = v_isSharedCheck_2689_;
goto v_resetjp_2680_;
}
v_resetjp_2680_:
{
lean_object* v___x_2684_; 
if (v_isShared_2682_ == 0)
{
lean_ctor_set(v___x_2681_, 0, v_mctx_2674_);
v___x_2684_ = v___x_2681_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2688_; 
v_reuseFailAlloc_2688_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2688_, 0, v_mctx_2674_);
lean_ctor_set(v_reuseFailAlloc_2688_, 1, v_cache_2676_);
lean_ctor_set(v_reuseFailAlloc_2688_, 2, v_zetaDeltaFVarIds_2677_);
lean_ctor_set(v_reuseFailAlloc_2688_, 3, v_postponed_2678_);
lean_ctor_set(v_reuseFailAlloc_2688_, 4, v_diag_2679_);
v___x_2684_ = v_reuseFailAlloc_2688_;
goto v_reusejp_2683_;
}
v_reusejp_2683_:
{
lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; 
v___x_2685_ = lean_st_ref_put(v___y_2669_, v___x_2684_);
v___x_2686_ = lean_box(v_fst_2673_);
v___x_2687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2687_, 0, v___x_2686_);
return v___x_2687_;
}
}
}
v___jp_2691_:
{
lean_object* v_snd_2693_; lean_object* v_fst_2694_; lean_object* v_mctx_2695_; uint8_t v___x_2696_; 
v_snd_2693_ = lean_ctor_get(v___y_2692_, 1);
lean_inc(v_snd_2693_);
v_fst_2694_ = lean_ctor_get(v___y_2692_, 0);
lean_inc(v_fst_2694_);
lean_dec_ref(v___y_2692_);
v_mctx_2695_ = lean_ctor_get(v_snd_2693_, 1);
lean_inc_ref(v_mctx_2695_);
lean_dec(v_snd_2693_);
v___x_2696_ = lean_unbox(v_fst_2694_);
lean_dec(v_fst_2694_);
v_fst_2673_ = v___x_2696_;
v_mctx_2674_ = v_mctx_2695_;
goto v___jp_2672_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___boxed(lean_object* v_e_2706_, lean_object* v_fvarId_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_){
_start:
{
lean_object* v_res_2710_; 
v_res_2710_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg(v_e_2706_, v_fvarId_2707_, v___y_2708_);
lean_dec(v___y_2708_);
return v_res_2710_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5(lean_object* v_e_2711_, lean_object* v_fvarId_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_){
_start:
{
lean_object* v___x_2718_; 
v___x_2718_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg(v_e_2711_, v_fvarId_2712_, v___y_2714_);
return v___x_2718_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___boxed(lean_object* v_e_2719_, lean_object* v_fvarId_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_){
_start:
{
lean_object* v_res_2726_; 
v_res_2726_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5(v_e_2719_, v_fvarId_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_);
lean_dec(v___y_2724_);
lean_dec_ref(v___y_2723_);
lean_dec(v___y_2722_);
lean_dec_ref(v___y_2721_);
return v_res_2726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg___lam__0(lean_object* v_k_2727_, lean_object* v_b_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_){
_start:
{
lean_object* v___x_2734_; 
lean_inc(v___y_2732_);
lean_inc_ref(v___y_2731_);
lean_inc(v___y_2730_);
lean_inc_ref(v___y_2729_);
v___x_2734_ = lean_apply_6(v_k_2727_, v_b_2728_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_, lean_box(0));
return v___x_2734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg___lam__0___boxed(lean_object* v_k_2735_, lean_object* v_b_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_){
_start:
{
lean_object* v_res_2742_; 
v_res_2742_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg___lam__0(v_k_2735_, v_b_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_);
lean_dec(v___y_2740_);
lean_dec_ref(v___y_2739_);
lean_dec(v___y_2738_);
lean_dec_ref(v___y_2737_);
return v_res_2742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg(lean_object* v_perm_2743_, lean_object* v_type_2744_, lean_object* v_k_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_){
_start:
{
lean_object* v___f_2751_; lean_object* v___x_2752_; 
v___f_2751_ = lean_alloc_closure((void*)(l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2751_, 0, v_k_2745_);
v___x_2752_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl(lean_box(0), v_perm_2743_, v_type_2744_, v___f_2751_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_);
if (lean_obj_tag(v___x_2752_) == 0)
{
lean_object* v_a_2753_; lean_object* v___x_2755_; uint8_t v_isShared_2756_; uint8_t v_isSharedCheck_2760_; 
v_a_2753_ = lean_ctor_get(v___x_2752_, 0);
v_isSharedCheck_2760_ = !lean_is_exclusive(v___x_2752_);
if (v_isSharedCheck_2760_ == 0)
{
v___x_2755_ = v___x_2752_;
v_isShared_2756_ = v_isSharedCheck_2760_;
goto v_resetjp_2754_;
}
else
{
lean_inc(v_a_2753_);
lean_dec(v___x_2752_);
v___x_2755_ = lean_box(0);
v_isShared_2756_ = v_isSharedCheck_2760_;
goto v_resetjp_2754_;
}
v_resetjp_2754_:
{
lean_object* v___x_2758_; 
if (v_isShared_2756_ == 0)
{
v___x_2758_ = v___x_2755_;
goto v_reusejp_2757_;
}
else
{
lean_object* v_reuseFailAlloc_2759_; 
v_reuseFailAlloc_2759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2759_, 0, v_a_2753_);
v___x_2758_ = v_reuseFailAlloc_2759_;
goto v_reusejp_2757_;
}
v_reusejp_2757_:
{
return v___x_2758_;
}
}
}
else
{
lean_object* v_a_2761_; lean_object* v___x_2763_; uint8_t v_isShared_2764_; uint8_t v_isSharedCheck_2768_; 
v_a_2761_ = lean_ctor_get(v___x_2752_, 0);
v_isSharedCheck_2768_ = !lean_is_exclusive(v___x_2752_);
if (v_isSharedCheck_2768_ == 0)
{
v___x_2763_ = v___x_2752_;
v_isShared_2764_ = v_isSharedCheck_2768_;
goto v_resetjp_2762_;
}
else
{
lean_inc(v_a_2761_);
lean_dec(v___x_2752_);
v___x_2763_ = lean_box(0);
v_isShared_2764_ = v_isSharedCheck_2768_;
goto v_resetjp_2762_;
}
v_resetjp_2762_:
{
lean_object* v___x_2766_; 
if (v_isShared_2764_ == 0)
{
v___x_2766_ = v___x_2763_;
goto v_reusejp_2765_;
}
else
{
lean_object* v_reuseFailAlloc_2767_; 
v_reuseFailAlloc_2767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2767_, 0, v_a_2761_);
v___x_2766_ = v_reuseFailAlloc_2767_;
goto v_reusejp_2765_;
}
v_reusejp_2765_:
{
return v___x_2766_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg___boxed(lean_object* v_perm_2769_, lean_object* v_type_2770_, lean_object* v_k_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_){
_start:
{
lean_object* v_res_2777_; 
v_res_2777_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg(v_perm_2769_, v_type_2770_, v_k_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_);
lean_dec(v___y_2775_);
lean_dec_ref(v___y_2774_);
lean_dec(v___y_2773_);
lean_dec_ref(v___y_2772_);
return v_res_2777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13(lean_object* v_00_u03b1_2778_, lean_object* v_perm_2779_, lean_object* v_type_2780_, lean_object* v_k_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_){
_start:
{
lean_object* v___x_2787_; 
v___x_2787_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg(v_perm_2779_, v_type_2780_, v_k_2781_, v___y_2782_, v___y_2783_, v___y_2784_, v___y_2785_);
return v___x_2787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___boxed(lean_object* v_00_u03b1_2788_, lean_object* v_perm_2789_, lean_object* v_type_2790_, lean_object* v_k_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_){
_start:
{
lean_object* v_res_2797_; 
v_res_2797_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13(v_00_u03b1_2788_, v_perm_2789_, v_type_2790_, v_k_2791_, v___y_2792_, v___y_2793_, v___y_2794_, v___y_2795_);
lean_dec(v___y_2795_);
lean_dec_ref(v___y_2794_);
lean_dec(v___y_2793_);
lean_dec_ref(v___y_2792_);
return v_res_2797_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1(lean_object* v_a_2798_, lean_object* v_fst_2799_, lean_object* v_fst_2800_, lean_object* v___x_2801_, lean_object* v___x_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_){
_start:
{
lean_object* v___x_2808_; 
lean_inc_ref(v_fst_2799_);
v___x_2808_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion(v_a_2798_, v_fst_2799_, v_fst_2800_, v___x_2801_, v___y_2803_, v___y_2804_, v___y_2805_, v___y_2806_);
if (lean_obj_tag(v___x_2808_) == 0)
{
lean_object* v_a_2809_; lean_object* v___x_2811_; uint8_t v_isShared_2812_; uint8_t v_isSharedCheck_2818_; 
v_a_2809_ = lean_ctor_get(v___x_2808_, 0);
v_isSharedCheck_2818_ = !lean_is_exclusive(v___x_2808_);
if (v_isSharedCheck_2818_ == 0)
{
v___x_2811_ = v___x_2808_;
v_isShared_2812_ = v_isSharedCheck_2818_;
goto v_resetjp_2810_;
}
else
{
lean_inc(v_a_2809_);
lean_dec(v___x_2808_);
v___x_2811_ = lean_box(0);
v_isShared_2812_ = v_isSharedCheck_2818_;
goto v_resetjp_2810_;
}
v_resetjp_2810_:
{
lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2816_; 
v___x_2813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2813_, 0, v_a_2809_);
lean_ctor_set(v___x_2813_, 1, v_fst_2799_);
v___x_2814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2814_, 0, v___x_2802_);
lean_ctor_set(v___x_2814_, 1, v___x_2813_);
if (v_isShared_2812_ == 0)
{
lean_ctor_set(v___x_2811_, 0, v___x_2814_);
v___x_2816_ = v___x_2811_;
goto v_reusejp_2815_;
}
else
{
lean_object* v_reuseFailAlloc_2817_; 
v_reuseFailAlloc_2817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2817_, 0, v___x_2814_);
v___x_2816_ = v_reuseFailAlloc_2817_;
goto v_reusejp_2815_;
}
v_reusejp_2815_:
{
return v___x_2816_;
}
}
}
else
{
lean_object* v_a_2819_; lean_object* v___x_2821_; uint8_t v_isShared_2822_; uint8_t v_isSharedCheck_2826_; 
lean_dec_ref(v___x_2802_);
lean_dec_ref(v_fst_2799_);
v_a_2819_ = lean_ctor_get(v___x_2808_, 0);
v_isSharedCheck_2826_ = !lean_is_exclusive(v___x_2808_);
if (v_isSharedCheck_2826_ == 0)
{
v___x_2821_ = v___x_2808_;
v_isShared_2822_ = v_isSharedCheck_2826_;
goto v_resetjp_2820_;
}
else
{
lean_inc(v_a_2819_);
lean_dec(v___x_2808_);
v___x_2821_ = lean_box(0);
v_isShared_2822_ = v_isSharedCheck_2826_;
goto v_resetjp_2820_;
}
v_resetjp_2820_:
{
lean_object* v___x_2824_; 
if (v_isShared_2822_ == 0)
{
v___x_2824_ = v___x_2821_;
goto v_reusejp_2823_;
}
else
{
lean_object* v_reuseFailAlloc_2825_; 
v_reuseFailAlloc_2825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2825_, 0, v_a_2819_);
v___x_2824_ = v_reuseFailAlloc_2825_;
goto v_reusejp_2823_;
}
v_reusejp_2823_:
{
return v___x_2824_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___boxed(lean_object* v_a_2827_, lean_object* v_fst_2828_, lean_object* v_fst_2829_, lean_object* v___x_2830_, lean_object* v___x_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_){
_start:
{
lean_object* v_res_2837_; 
v_res_2837_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1(v_a_2827_, v_fst_2828_, v_fst_2829_, v___x_2830_, v___x_2831_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_);
lean_dec(v___y_2835_);
lean_dec_ref(v___y_2834_);
lean_dec(v___y_2833_);
lean_dec_ref(v___y_2832_);
return v_res_2837_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__3(size_t v_sz_2838_, size_t v_i_2839_, lean_object* v_bs_2840_){
_start:
{
uint8_t v___x_2841_; 
v___x_2841_ = lean_usize_dec_lt(v_i_2839_, v_sz_2838_);
if (v___x_2841_ == 0)
{
return v_bs_2840_;
}
else
{
lean_object* v_v_2842_; lean_object* v___x_2843_; lean_object* v_bs_x27_2844_; lean_object* v___x_2845_; size_t v___x_2846_; size_t v___x_2847_; lean_object* v___x_2848_; 
v_v_2842_ = lean_array_uget(v_bs_2840_, v_i_2839_);
v___x_2843_ = lean_unsigned_to_nat(0u);
v_bs_x27_2844_ = lean_array_uset(v_bs_2840_, v_i_2839_, v___x_2843_);
v___x_2845_ = l_Lean_Elab_Structural_RecArgInfo_indicesAndRecArgPos(v_v_2842_);
v___x_2846_ = ((size_t)1ULL);
v___x_2847_ = lean_usize_add(v_i_2839_, v___x_2846_);
v___x_2848_ = lean_array_uset(v_bs_x27_2844_, v_i_2839_, v___x_2845_);
v_i_2839_ = v___x_2847_;
v_bs_2840_ = v___x_2848_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__3___boxed(lean_object* v_sz_2850_, lean_object* v_i_2851_, lean_object* v_bs_2852_){
_start:
{
size_t v_sz_boxed_2853_; size_t v_i_boxed_2854_; lean_object* v_res_2855_; 
v_sz_boxed_2853_ = lean_unbox_usize(v_sz_2850_);
lean_dec(v_sz_2850_);
v_i_boxed_2854_ = lean_unbox_usize(v_i_2851_);
lean_dec(v_i_2851_);
v_res_2855_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__3(v_sz_boxed_2853_, v_i_boxed_2854_, v_bs_2852_);
return v_res_2855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___redArg(lean_object* v_lctx_2856_, lean_object* v_localInsts_2857_, lean_object* v_x_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_){
_start:
{
lean_object* v___x_2864_; 
v___x_2864_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_2856_, v_localInsts_2857_, v_x_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_);
if (lean_obj_tag(v___x_2864_) == 0)
{
lean_object* v_a_2865_; lean_object* v___x_2867_; uint8_t v_isShared_2868_; uint8_t v_isSharedCheck_2872_; 
v_a_2865_ = lean_ctor_get(v___x_2864_, 0);
v_isSharedCheck_2872_ = !lean_is_exclusive(v___x_2864_);
if (v_isSharedCheck_2872_ == 0)
{
v___x_2867_ = v___x_2864_;
v_isShared_2868_ = v_isSharedCheck_2872_;
goto v_resetjp_2866_;
}
else
{
lean_inc(v_a_2865_);
lean_dec(v___x_2864_);
v___x_2867_ = lean_box(0);
v_isShared_2868_ = v_isSharedCheck_2872_;
goto v_resetjp_2866_;
}
v_resetjp_2866_:
{
lean_object* v___x_2870_; 
if (v_isShared_2868_ == 0)
{
v___x_2870_ = v___x_2867_;
goto v_reusejp_2869_;
}
else
{
lean_object* v_reuseFailAlloc_2871_; 
v_reuseFailAlloc_2871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2871_, 0, v_a_2865_);
v___x_2870_ = v_reuseFailAlloc_2871_;
goto v_reusejp_2869_;
}
v_reusejp_2869_:
{
return v___x_2870_;
}
}
}
else
{
lean_object* v_a_2873_; lean_object* v___x_2875_; uint8_t v_isShared_2876_; uint8_t v_isSharedCheck_2880_; 
v_a_2873_ = lean_ctor_get(v___x_2864_, 0);
v_isSharedCheck_2880_ = !lean_is_exclusive(v___x_2864_);
if (v_isSharedCheck_2880_ == 0)
{
v___x_2875_ = v___x_2864_;
v_isShared_2876_ = v_isSharedCheck_2880_;
goto v_resetjp_2874_;
}
else
{
lean_inc(v_a_2873_);
lean_dec(v___x_2864_);
v___x_2875_ = lean_box(0);
v_isShared_2876_ = v_isSharedCheck_2880_;
goto v_resetjp_2874_;
}
v_resetjp_2874_:
{
lean_object* v___x_2878_; 
if (v_isShared_2876_ == 0)
{
v___x_2878_ = v___x_2875_;
goto v_reusejp_2877_;
}
else
{
lean_object* v_reuseFailAlloc_2879_; 
v_reuseFailAlloc_2879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2879_, 0, v_a_2873_);
v___x_2878_ = v_reuseFailAlloc_2879_;
goto v_reusejp_2877_;
}
v_reusejp_2877_:
{
return v___x_2878_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___redArg___boxed(lean_object* v_lctx_2881_, lean_object* v_localInsts_2882_, lean_object* v_x_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_){
_start:
{
lean_object* v_res_2889_; 
v_res_2889_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___redArg(v_lctx_2881_, v_localInsts_2882_, v_x_2883_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_);
lean_dec(v___y_2887_);
lean_dec_ref(v___y_2886_);
lean_dec(v___y_2885_);
lean_dec_ref(v___y_2884_);
return v_res_2889_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__12(lean_object* v_as_2890_, size_t v_i_2891_, size_t v_stop_2892_, lean_object* v_b_2893_){
_start:
{
uint8_t v___x_2894_; 
v___x_2894_ = lean_usize_dec_eq(v_i_2891_, v_stop_2892_);
if (v___x_2894_ == 0)
{
lean_object* v___x_2895_; lean_object* v___x_2896_; size_t v___x_2897_; size_t v___x_2898_; 
v___x_2895_ = lean_array_uget_borrowed(v_as_2890_, v_i_2891_);
lean_inc(v___x_2895_);
v___x_2896_ = lean_local_ctx_erase(v_b_2893_, v___x_2895_);
v___x_2897_ = ((size_t)1ULL);
v___x_2898_ = lean_usize_add(v_i_2891_, v___x_2897_);
v_i_2891_ = v___x_2898_;
v_b_2893_ = v___x_2896_;
goto _start;
}
else
{
return v_b_2893_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__12___boxed(lean_object* v_as_2900_, lean_object* v_i_2901_, lean_object* v_stop_2902_, lean_object* v_b_2903_){
_start:
{
size_t v_i_boxed_2904_; size_t v_stop_boxed_2905_; lean_object* v_res_2906_; 
v_i_boxed_2904_ = lean_unbox_usize(v_i_2901_);
lean_dec(v_i_2901_);
v_stop_boxed_2905_ = lean_unbox_usize(v_stop_2902_);
lean_dec(v_stop_2902_);
v_res_2906_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__12(v_as_2900_, v_i_boxed_2904_, v_stop_boxed_2905_, v_b_2903_);
lean_dec_ref(v_as_2900_);
return v_res_2906_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9_spec__11(lean_object* v_a_2907_, lean_object* v_as_2908_, size_t v_i_2909_, size_t v_stop_2910_){
_start:
{
uint8_t v___x_2911_; 
v___x_2911_ = lean_usize_dec_eq(v_i_2909_, v_stop_2910_);
if (v___x_2911_ == 0)
{
lean_object* v___x_2912_; uint8_t v___x_2913_; 
v___x_2912_ = lean_array_uget_borrowed(v_as_2908_, v_i_2909_);
v___x_2913_ = l_Lean_instBEqFVarId_beq(v_a_2907_, v___x_2912_);
if (v___x_2913_ == 0)
{
size_t v___x_2914_; size_t v___x_2915_; 
v___x_2914_ = ((size_t)1ULL);
v___x_2915_ = lean_usize_add(v_i_2909_, v___x_2914_);
v_i_2909_ = v___x_2915_;
goto _start;
}
else
{
return v___x_2913_;
}
}
else
{
uint8_t v___x_2917_; 
v___x_2917_ = 0;
return v___x_2917_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9_spec__11___boxed(lean_object* v_a_2918_, lean_object* v_as_2919_, lean_object* v_i_2920_, lean_object* v_stop_2921_){
_start:
{
size_t v_i_boxed_2922_; size_t v_stop_boxed_2923_; uint8_t v_res_2924_; lean_object* v_r_2925_; 
v_i_boxed_2922_ = lean_unbox_usize(v_i_2920_);
lean_dec(v_i_2920_);
v_stop_boxed_2923_ = lean_unbox_usize(v_stop_2921_);
lean_dec(v_stop_2921_);
v_res_2924_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9_spec__11(v_a_2918_, v_as_2919_, v_i_boxed_2922_, v_stop_boxed_2923_);
lean_dec_ref(v_as_2919_);
lean_dec(v_a_2918_);
v_r_2925_ = lean_box(v_res_2924_);
return v_r_2925_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9(lean_object* v_as_2926_, lean_object* v_a_2927_){
_start:
{
lean_object* v___x_2928_; lean_object* v___x_2929_; uint8_t v___x_2930_; 
v___x_2928_ = lean_unsigned_to_nat(0u);
v___x_2929_ = lean_array_get_size(v_as_2926_);
v___x_2930_ = lean_nat_dec_lt(v___x_2928_, v___x_2929_);
if (v___x_2930_ == 0)
{
return v___x_2930_;
}
else
{
if (v___x_2930_ == 0)
{
return v___x_2930_;
}
else
{
size_t v___x_2931_; size_t v___x_2932_; uint8_t v___x_2933_; 
v___x_2931_ = ((size_t)0ULL);
v___x_2932_ = lean_usize_of_nat(v___x_2929_);
v___x_2933_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9_spec__11(v_a_2927_, v_as_2926_, v___x_2931_, v___x_2932_);
return v___x_2933_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9___boxed(lean_object* v_as_2934_, lean_object* v_a_2935_){
_start:
{
uint8_t v_res_2936_; lean_object* v_r_2937_; 
v_res_2936_ = l_Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9(v_as_2934_, v_a_2935_);
lean_dec(v_a_2935_);
lean_dec_ref(v_as_2934_);
v_r_2937_ = lean_box(v_res_2936_);
return v_r_2937_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__11(lean_object* v_fvarIds_2938_, lean_object* v_as_2939_, size_t v_i_2940_, size_t v_stop_2941_, lean_object* v_b_2942_){
_start:
{
lean_object* v___y_2944_; uint8_t v___x_2948_; 
v___x_2948_ = lean_usize_dec_eq(v_i_2940_, v_stop_2941_);
if (v___x_2948_ == 0)
{
lean_object* v___x_2949_; lean_object* v_fvar_2950_; lean_object* v___x_2951_; uint8_t v___x_2952_; 
v___x_2949_ = lean_array_uget_borrowed(v_as_2939_, v_i_2940_);
v_fvar_2950_ = lean_ctor_get(v___x_2949_, 1);
v___x_2951_ = l_Lean_Expr_fvarId_x21(v_fvar_2950_);
v___x_2952_ = l_Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9(v_fvarIds_2938_, v___x_2951_);
lean_dec(v___x_2951_);
if (v___x_2952_ == 0)
{
lean_object* v___x_2953_; 
lean_inc(v___x_2949_);
v___x_2953_ = lean_array_push(v_b_2942_, v___x_2949_);
v___y_2944_ = v___x_2953_;
goto v___jp_2943_;
}
else
{
v___y_2944_ = v_b_2942_;
goto v___jp_2943_;
}
}
else
{
return v_b_2942_;
}
v___jp_2943_:
{
size_t v___x_2945_; size_t v___x_2946_; 
v___x_2945_ = ((size_t)1ULL);
v___x_2946_ = lean_usize_add(v_i_2940_, v___x_2945_);
v_i_2940_ = v___x_2946_;
v_b_2942_ = v___y_2944_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__11___boxed(lean_object* v_fvarIds_2954_, lean_object* v_as_2955_, lean_object* v_i_2956_, lean_object* v_stop_2957_, lean_object* v_b_2958_){
_start:
{
size_t v_i_boxed_2959_; size_t v_stop_boxed_2960_; lean_object* v_res_2961_; 
v_i_boxed_2959_ = lean_unbox_usize(v_i_2956_);
lean_dec(v_i_2956_);
v_stop_boxed_2960_ = lean_unbox_usize(v_stop_2957_);
lean_dec(v_stop_2957_);
v_res_2961_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__11(v_fvarIds_2954_, v_as_2955_, v_i_boxed_2959_, v_stop_boxed_2960_, v_b_2958_);
lean_dec_ref(v_as_2955_);
lean_dec_ref(v_fvarIds_2954_);
return v_res_2961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___redArg(lean_object* v_fvarIds_2964_, lean_object* v_k_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_){
_start:
{
lean_object* v_lctx_2971_; lean_object* v_localInstances_2972_; lean_object* v___x_2973_; lean_object* v___y_2975_; lean_object* v___x_2984_; uint8_t v___x_2985_; 
v_lctx_2971_ = lean_ctor_get(v___y_2966_, 2);
v_localInstances_2972_ = lean_ctor_get(v___y_2966_, 3);
v___x_2973_ = lean_unsigned_to_nat(0u);
v___x_2984_ = lean_array_get_size(v_fvarIds_2964_);
v___x_2985_ = lean_nat_dec_lt(v___x_2973_, v___x_2984_);
if (v___x_2985_ == 0)
{
lean_inc_ref(v_lctx_2971_);
v___y_2975_ = v_lctx_2971_;
goto v___jp_2974_;
}
else
{
size_t v___x_2986_; size_t v___x_2987_; lean_object* v___x_2988_; 
v___x_2986_ = ((size_t)0ULL);
v___x_2987_ = lean_usize_of_nat(v___x_2984_);
lean_inc_ref(v_lctx_2971_);
v___x_2988_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__12(v_fvarIds_2964_, v___x_2986_, v___x_2987_, v_lctx_2971_);
v___y_2975_ = v___x_2988_;
goto v___jp_2974_;
}
v___jp_2974_:
{
lean_object* v___x_2976_; lean_object* v___x_2977_; uint8_t v___x_2978_; 
v___x_2976_ = lean_array_get_size(v_localInstances_2972_);
v___x_2977_ = ((lean_object*)(l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___redArg___closed__0));
v___x_2978_ = lean_nat_dec_lt(v___x_2973_, v___x_2976_);
if (v___x_2978_ == 0)
{
lean_object* v___x_2979_; 
v___x_2979_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___redArg(v___y_2975_, v___x_2977_, v_k_2965_, v___y_2966_, v___y_2967_, v___y_2968_, v___y_2969_);
return v___x_2979_;
}
else
{
size_t v___x_2980_; size_t v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; 
v___x_2980_ = ((size_t)0ULL);
v___x_2981_ = lean_usize_of_nat(v___x_2976_);
v___x_2982_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__11(v_fvarIds_2964_, v_localInstances_2972_, v___x_2980_, v___x_2981_, v___x_2977_);
v___x_2983_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___redArg(v___y_2975_, v___x_2982_, v_k_2965_, v___y_2966_, v___y_2967_, v___y_2968_, v___y_2969_);
return v___x_2983_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___redArg___boxed(lean_object* v_fvarIds_2989_, lean_object* v_k_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_){
_start:
{
lean_object* v_res_2996_; 
v_res_2996_ = l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___redArg(v_fvarIds_2989_, v_k_2990_, v___y_2991_, v___y_2992_, v___y_2993_, v___y_2994_);
lean_dec(v___y_2994_);
lean_dec_ref(v___y_2993_);
lean_dec(v___y_2992_);
lean_dec_ref(v___y_2991_);
lean_dec_ref(v_fvarIds_2989_);
return v_res_2996_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__14_spec__17_spec__21(lean_object* v_x_2997_, lean_object* v_x_2998_, lean_object* v_x_2999_){
_start:
{
if (lean_obj_tag(v_x_2999_) == 0)
{
lean_dec(v_x_2997_);
return v_x_2998_;
}
else
{
lean_object* v_head_3000_; lean_object* v_tail_3001_; lean_object* v___x_3003_; uint8_t v_isShared_3004_; uint8_t v_isSharedCheck_3011_; 
v_head_3000_ = lean_ctor_get(v_x_2999_, 0);
v_tail_3001_ = lean_ctor_get(v_x_2999_, 1);
v_isSharedCheck_3011_ = !lean_is_exclusive(v_x_2999_);
if (v_isSharedCheck_3011_ == 0)
{
v___x_3003_ = v_x_2999_;
v_isShared_3004_ = v_isSharedCheck_3011_;
goto v_resetjp_3002_;
}
else
{
lean_inc(v_tail_3001_);
lean_inc(v_head_3000_);
lean_dec(v_x_2999_);
v___x_3003_ = lean_box(0);
v_isShared_3004_ = v_isSharedCheck_3011_;
goto v_resetjp_3002_;
}
v_resetjp_3002_:
{
lean_object* v___x_3006_; 
lean_inc(v_x_2997_);
if (v_isShared_3004_ == 0)
{
lean_ctor_set_tag(v___x_3003_, 5);
lean_ctor_set(v___x_3003_, 1, v_x_2997_);
lean_ctor_set(v___x_3003_, 0, v_x_2998_);
v___x_3006_ = v___x_3003_;
goto v_reusejp_3005_;
}
else
{
lean_object* v_reuseFailAlloc_3010_; 
v_reuseFailAlloc_3010_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3010_, 0, v_x_2998_);
lean_ctor_set(v_reuseFailAlloc_3010_, 1, v_x_2997_);
v___x_3006_ = v_reuseFailAlloc_3010_;
goto v_reusejp_3005_;
}
v_reusejp_3005_:
{
lean_object* v___x_3007_; lean_object* v___x_3008_; 
v___x_3007_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(v_head_3000_);
v___x_3008_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3008_, 0, v___x_3006_);
lean_ctor_set(v___x_3008_, 1, v___x_3007_);
v_x_2998_ = v___x_3008_;
v_x_2999_ = v_tail_3001_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__14_spec__17(lean_object* v_x_3012_, lean_object* v_x_3013_, lean_object* v_x_3014_){
_start:
{
if (lean_obj_tag(v_x_3014_) == 0)
{
lean_dec(v_x_3012_);
return v_x_3013_;
}
else
{
lean_object* v_head_3015_; lean_object* v_tail_3016_; lean_object* v___x_3018_; uint8_t v_isShared_3019_; uint8_t v_isSharedCheck_3026_; 
v_head_3015_ = lean_ctor_get(v_x_3014_, 0);
v_tail_3016_ = lean_ctor_get(v_x_3014_, 1);
v_isSharedCheck_3026_ = !lean_is_exclusive(v_x_3014_);
if (v_isSharedCheck_3026_ == 0)
{
v___x_3018_ = v_x_3014_;
v_isShared_3019_ = v_isSharedCheck_3026_;
goto v_resetjp_3017_;
}
else
{
lean_inc(v_tail_3016_);
lean_inc(v_head_3015_);
lean_dec(v_x_3014_);
v___x_3018_ = lean_box(0);
v_isShared_3019_ = v_isSharedCheck_3026_;
goto v_resetjp_3017_;
}
v_resetjp_3017_:
{
lean_object* v___x_3021_; 
lean_inc(v_x_3012_);
if (v_isShared_3019_ == 0)
{
lean_ctor_set_tag(v___x_3018_, 5);
lean_ctor_set(v___x_3018_, 1, v_x_3012_);
lean_ctor_set(v___x_3018_, 0, v_x_3013_);
v___x_3021_ = v___x_3018_;
goto v_reusejp_3020_;
}
else
{
lean_object* v_reuseFailAlloc_3025_; 
v_reuseFailAlloc_3025_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3025_, 0, v_x_3013_);
lean_ctor_set(v_reuseFailAlloc_3025_, 1, v_x_3012_);
v___x_3021_ = v_reuseFailAlloc_3025_;
goto v_reusejp_3020_;
}
v_reusejp_3020_:
{
lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; 
v___x_3022_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(v_head_3015_);
v___x_3023_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3023_, 0, v___x_3021_);
lean_ctor_set(v___x_3023_, 1, v___x_3022_);
v___x_3024_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__14_spec__17_spec__21(v_x_3012_, v___x_3023_, v_tail_3016_);
return v___x_3024_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__14(lean_object* v_x_3027_, lean_object* v_x_3028_){
_start:
{
if (lean_obj_tag(v_x_3027_) == 0)
{
lean_object* v___x_3029_; 
lean_dec(v_x_3028_);
v___x_3029_ = lean_box(0);
return v___x_3029_;
}
else
{
lean_object* v_tail_3030_; 
v_tail_3030_ = lean_ctor_get(v_x_3027_, 1);
if (lean_obj_tag(v_tail_3030_) == 0)
{
lean_object* v_head_3031_; lean_object* v___x_3032_; 
lean_dec(v_x_3028_);
v_head_3031_ = lean_ctor_get(v_x_3027_, 0);
lean_inc(v_head_3031_);
lean_dec_ref_known(v_x_3027_, 2);
v___x_3032_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(v_head_3031_);
return v___x_3032_;
}
else
{
lean_object* v_head_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; 
lean_inc(v_tail_3030_);
v_head_3033_ = lean_ctor_get(v_x_3027_, 0);
lean_inc(v_head_3033_);
lean_dec_ref_known(v_x_3027_, 2);
v___x_3034_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(v_head_3033_);
v___x_3035_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__14_spec__17(v_x_3028_, v___x_3034_, v_tail_3030_);
return v___x_3035_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__5(void){
_start:
{
lean_object* v___x_3044_; lean_object* v___x_3045_; 
v___x_3044_ = ((lean_object*)(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__0));
v___x_3045_ = lean_string_length(v___x_3044_);
return v___x_3045_;
}
}
static lean_object* _init_l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__6(void){
_start:
{
lean_object* v___x_3046_; lean_object* v___x_3047_; 
v___x_3046_ = lean_obj_once(&l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__5, &l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__5_once, _init_l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__5);
v___x_3047_ = lean_nat_to_int(v___x_3046_);
return v___x_3047_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10(lean_object* v_xs_3055_){
_start:
{
lean_object* v___x_3056_; lean_object* v___x_3057_; uint8_t v___x_3058_; 
v___x_3056_ = lean_array_get_size(v_xs_3055_);
v___x_3057_ = lean_unsigned_to_nat(0u);
v___x_3058_ = lean_nat_dec_eq(v___x_3056_, v___x_3057_);
if (v___x_3058_ == 0)
{
lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; 
v___x_3059_ = lean_array_to_list(v_xs_3055_);
v___x_3060_ = ((lean_object*)(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__3));
v___x_3061_ = l_Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__14(v___x_3059_, v___x_3060_);
v___x_3062_ = lean_obj_once(&l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__6, &l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__6_once, _init_l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__6);
v___x_3063_ = ((lean_object*)(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__7));
v___x_3064_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3064_, 0, v___x_3063_);
lean_ctor_set(v___x_3064_, 1, v___x_3061_);
v___x_3065_ = ((lean_object*)(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__8));
v___x_3066_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3066_, 0, v___x_3064_);
lean_ctor_set(v___x_3066_, 1, v___x_3065_);
v___x_3067_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3067_, 0, v___x_3062_);
lean_ctor_set(v___x_3067_, 1, v___x_3066_);
v___x_3068_ = l_Std_Format_fill(v___x_3067_);
return v___x_3068_;
}
else
{
lean_object* v___x_3069_; 
lean_dec_ref(v_xs_3055_);
v___x_3069_ = ((lean_object*)(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__10));
return v___x_3069_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__11(size_t v_sz_3070_, size_t v_i_3071_, lean_object* v_bs_3072_){
_start:
{
uint8_t v___x_3073_; 
v___x_3073_ = lean_usize_dec_lt(v_i_3071_, v_sz_3070_);
if (v___x_3073_ == 0)
{
return v_bs_3072_;
}
else
{
lean_object* v_v_3074_; lean_object* v___x_3075_; lean_object* v_bs_x27_3076_; lean_object* v___x_3077_; size_t v___x_3078_; size_t v___x_3079_; lean_object* v___x_3080_; 
v_v_3074_ = lean_array_uget(v_bs_3072_, v_i_3071_);
v___x_3075_ = lean_unsigned_to_nat(0u);
v_bs_x27_3076_ = lean_array_uset(v_bs_3072_, v_i_3071_, v___x_3075_);
v___x_3077_ = l_Lean_mkFVar(v_v_3074_);
v___x_3078_ = ((size_t)1ULL);
v___x_3079_ = lean_usize_add(v_i_3071_, v___x_3078_);
v___x_3080_ = lean_array_uset(v_bs_x27_3076_, v_i_3071_, v___x_3077_);
v_i_3071_ = v___x_3079_;
v_bs_3072_ = v___x_3080_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__11___boxed(lean_object* v_sz_3082_, lean_object* v_i_3083_, lean_object* v_bs_3084_){
_start:
{
size_t v_sz_boxed_3085_; size_t v_i_boxed_3086_; lean_object* v_res_3087_; 
v_sz_boxed_3085_ = lean_unbox_usize(v_sz_3082_);
lean_dec(v_sz_3082_);
v_i_boxed_3086_ = lean_unbox_usize(v_i_3083_);
lean_dec(v_i_3083_);
v_res_3087_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__11(v_sz_boxed_3085_, v_i_boxed_3086_, v_bs_3084_);
return v_res_3087_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__2(size_t v_sz_3088_, size_t v_i_3089_, lean_object* v_bs_3090_){
_start:
{
uint8_t v___x_3091_; 
v___x_3091_ = lean_usize_dec_lt(v_i_3089_, v_sz_3088_);
if (v___x_3091_ == 0)
{
return v_bs_3090_;
}
else
{
lean_object* v_v_3092_; lean_object* v_recArgPos_3093_; lean_object* v___x_3094_; lean_object* v_bs_x27_3095_; size_t v___x_3096_; size_t v___x_3097_; lean_object* v___x_3098_; 
v_v_3092_ = lean_array_uget_borrowed(v_bs_3090_, v_i_3089_);
v_recArgPos_3093_ = lean_ctor_get(v_v_3092_, 2);
lean_inc(v_recArgPos_3093_);
v___x_3094_ = lean_unsigned_to_nat(0u);
v_bs_x27_3095_ = lean_array_uset(v_bs_3090_, v_i_3089_, v___x_3094_);
v___x_3096_ = ((size_t)1ULL);
v___x_3097_ = lean_usize_add(v_i_3089_, v___x_3096_);
v___x_3098_ = lean_array_uset(v_bs_x27_3095_, v_i_3089_, v_recArgPos_3093_);
v_i_3089_ = v___x_3097_;
v_bs_3090_ = v___x_3098_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__2___boxed(lean_object* v_sz_3100_, lean_object* v_i_3101_, lean_object* v_bs_3102_){
_start:
{
size_t v_sz_boxed_3103_; size_t v_i_boxed_3104_; lean_object* v_res_3105_; 
v_sz_boxed_3103_ = lean_unbox_usize(v_sz_3100_);
lean_dec(v_sz_3100_);
v_i_boxed_3104_ = lean_unbox_usize(v_i_3101_);
lean_dec(v_i_3101_);
v_res_3105_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__2(v_sz_boxed_3103_, v_i_boxed_3104_, v_bs_3102_);
return v_res_3105_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg(lean_object* v_fst_3106_, size_t v_sz_3107_, size_t v_i_3108_, lean_object* v_bs_3109_){
_start:
{
uint8_t v___x_3110_; 
v___x_3110_ = lean_usize_dec_lt(v_i_3108_, v_sz_3107_);
if (v___x_3110_ == 0)
{
return v_bs_3109_;
}
else
{
lean_object* v_v_3111_; lean_object* v_fnName_3112_; lean_object* v_recArgPos_3113_; lean_object* v_indicesPos_3114_; lean_object* v_indGroupInst_3115_; lean_object* v_indIdx_3116_; lean_object* v___x_3118_; uint8_t v_isShared_3119_; uint8_t v_isSharedCheck_3133_; 
v_v_3111_ = lean_array_uget(v_bs_3109_, v_i_3108_);
v_fnName_3112_ = lean_ctor_get(v_v_3111_, 0);
v_recArgPos_3113_ = lean_ctor_get(v_v_3111_, 2);
v_indicesPos_3114_ = lean_ctor_get(v_v_3111_, 3);
v_indGroupInst_3115_ = lean_ctor_get(v_v_3111_, 4);
v_indIdx_3116_ = lean_ctor_get(v_v_3111_, 5);
v_isSharedCheck_3133_ = !lean_is_exclusive(v_v_3111_);
if (v_isSharedCheck_3133_ == 0)
{
lean_object* v_unused_3134_; 
v_unused_3134_ = lean_ctor_get(v_v_3111_, 1);
lean_dec(v_unused_3134_);
v___x_3118_ = v_v_3111_;
v_isShared_3119_ = v_isSharedCheck_3133_;
goto v_resetjp_3117_;
}
else
{
lean_inc(v_indIdx_3116_);
lean_inc(v_indGroupInst_3115_);
lean_inc(v_indicesPos_3114_);
lean_inc(v_recArgPos_3113_);
lean_inc(v_fnName_3112_);
lean_dec(v_v_3111_);
v___x_3118_ = lean_box(0);
v_isShared_3119_ = v_isSharedCheck_3133_;
goto v_resetjp_3117_;
}
v_resetjp_3117_:
{
lean_object* v_perms_3120_; lean_object* v___x_3121_; lean_object* v_bs_x27_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3127_; 
v_perms_3120_ = lean_ctor_get(v_fst_3106_, 1);
v___x_3121_ = lean_unsigned_to_nat(0u);
v_bs_x27_3122_ = lean_array_uset(v_bs_3109_, v_i_3108_, v___x_3121_);
v___x_3123_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0);
v___x_3124_ = lean_usize_to_nat(v_i_3108_);
v___x_3125_ = lean_array_get_borrowed(v___x_3123_, v_perms_3120_, v___x_3124_);
lean_dec(v___x_3124_);
lean_inc(v___x_3125_);
if (v_isShared_3119_ == 0)
{
lean_ctor_set(v___x_3118_, 1, v___x_3125_);
v___x_3127_ = v___x_3118_;
goto v_reusejp_3126_;
}
else
{
lean_object* v_reuseFailAlloc_3132_; 
v_reuseFailAlloc_3132_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3132_, 0, v_fnName_3112_);
lean_ctor_set(v_reuseFailAlloc_3132_, 1, v___x_3125_);
lean_ctor_set(v_reuseFailAlloc_3132_, 2, v_recArgPos_3113_);
lean_ctor_set(v_reuseFailAlloc_3132_, 3, v_indicesPos_3114_);
lean_ctor_set(v_reuseFailAlloc_3132_, 4, v_indGroupInst_3115_);
lean_ctor_set(v_reuseFailAlloc_3132_, 5, v_indIdx_3116_);
v___x_3127_ = v_reuseFailAlloc_3132_;
goto v_reusejp_3126_;
}
v_reusejp_3126_:
{
size_t v___x_3128_; size_t v___x_3129_; lean_object* v___x_3130_; 
v___x_3128_ = ((size_t)1ULL);
v___x_3129_ = lean_usize_add(v_i_3108_, v___x_3128_);
v___x_3130_ = lean_array_uset(v_bs_x27_3122_, v_i_3108_, v___x_3127_);
v_i_3108_ = v___x_3129_;
v_bs_3109_ = v___x_3130_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg___boxed(lean_object* v_fst_3135_, lean_object* v_sz_3136_, lean_object* v_i_3137_, lean_object* v_bs_3138_){
_start:
{
size_t v_sz_boxed_3139_; size_t v_i_boxed_3140_; lean_object* v_res_3141_; 
v_sz_boxed_3139_ = lean_unbox_usize(v_sz_3136_);
lean_dec(v_sz_3136_);
v_i_boxed_3140_ = lean_unbox_usize(v_i_3137_);
lean_dec(v_i_3137_);
v_res_3141_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg(v_fst_3135_, v_sz_boxed_3139_, v_i_boxed_3140_, v_bs_3138_);
lean_dec_ref(v_fst_3135_);
return v_res_3141_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__1(void){
_start:
{
lean_object* v___x_3143_; lean_object* v___x_3144_; 
v___x_3143_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__0));
v___x_3144_ = l_Lean_stringToMessageData(v___x_3143_);
return v___x_3144_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__3(void){
_start:
{
lean_object* v___x_3146_; lean_object* v___x_3147_; 
v___x_3146_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__2));
v___x_3147_ = l_Lean_stringToMessageData(v___x_3146_);
return v___x_3147_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__5(void){
_start:
{
lean_object* v___x_3149_; lean_object* v___x_3150_; 
v___x_3149_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__4));
v___x_3150_ = l_Lean_stringToMessageData(v___x_3149_);
return v___x_3150_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6(lean_object* v_a_3151_, lean_object* v_as_3152_, size_t v_sz_3153_, size_t v_i_3154_, lean_object* v_b_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_){
_start:
{
lean_object* v_a_3162_; uint8_t v___x_3166_; 
v___x_3166_ = lean_usize_dec_lt(v_i_3154_, v_sz_3153_);
if (v___x_3166_ == 0)
{
lean_object* v___x_3167_; 
lean_dec_ref(v_a_3151_);
v___x_3167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3167_, 0, v_b_3155_);
return v___x_3167_;
}
else
{
lean_object* v_a_3168_; lean_object* v___x_3169_; 
v_a_3168_ = lean_array_uget_borrowed(v_as_3152_, v_i_3154_);
lean_inc(v_a_3168_);
lean_inc_ref(v_a_3151_);
v___x_3169_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg(v_a_3151_, v_a_3168_, v___y_3157_);
if (lean_obj_tag(v___x_3169_) == 0)
{
lean_object* v_a_3170_; lean_object* v___x_3171_; uint8_t v___x_3172_; 
v_a_3170_ = lean_ctor_get(v___x_3169_, 0);
lean_inc(v_a_3170_);
lean_dec_ref_known(v___x_3169_, 1);
v___x_3171_ = lean_box(0);
v___x_3172_ = lean_unbox(v_a_3170_);
lean_dec(v_a_3170_);
if (v___x_3172_ == 0)
{
v_a_3162_ = v___x_3171_;
goto v___jp_3161_;
}
else
{
uint8_t v___x_3173_; 
v___x_3173_ = l_Lean_Expr_isFVarOf(v_a_3151_, v_a_3168_);
if (v___x_3173_ == 0)
{
lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; 
v___x_3174_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__1);
lean_inc_ref(v_a_3151_);
v___x_3175_ = l_Lean_indentExpr(v_a_3151_);
v___x_3176_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3176_, 0, v___x_3174_);
lean_ctor_set(v___x_3176_, 1, v___x_3175_);
v___x_3177_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__3);
v___x_3178_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3178_, 0, v___x_3176_);
lean_ctor_set(v___x_3178_, 1, v___x_3177_);
lean_inc(v_a_3168_);
v___x_3179_ = l_Lean_mkFVar(v_a_3168_);
v___x_3180_ = l_Lean_indentExpr(v___x_3179_);
v___x_3181_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3181_, 0, v___x_3178_);
lean_ctor_set(v___x_3181_, 1, v___x_3180_);
v___x_3182_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__5);
v___x_3183_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3183_, 0, v___x_3181_);
lean_ctor_set(v___x_3183_, 1, v___x_3182_);
v___x_3184_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg(v___x_3183_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_);
if (lean_obj_tag(v___x_3184_) == 0)
{
lean_dec_ref_known(v___x_3184_, 1);
v_a_3162_ = v___x_3171_;
goto v___jp_3161_;
}
else
{
lean_dec_ref(v_a_3151_);
return v___x_3184_;
}
}
else
{
lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; 
v___x_3185_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__1);
lean_inc_ref(v_a_3151_);
v___x_3186_ = l_Lean_indentExpr(v_a_3151_);
v___x_3187_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3187_, 0, v___x_3185_);
lean_ctor_set(v___x_3187_, 1, v___x_3186_);
v___x_3188_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__5);
v___x_3189_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3189_, 0, v___x_3187_);
lean_ctor_set(v___x_3189_, 1, v___x_3188_);
v___x_3190_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg(v___x_3189_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_);
if (lean_obj_tag(v___x_3190_) == 0)
{
lean_dec_ref_known(v___x_3190_, 1);
v_a_3162_ = v___x_3171_;
goto v___jp_3161_;
}
else
{
lean_dec_ref(v_a_3151_);
return v___x_3190_;
}
}
}
}
else
{
lean_object* v_a_3191_; lean_object* v___x_3193_; uint8_t v_isShared_3194_; uint8_t v_isSharedCheck_3198_; 
lean_dec_ref(v_a_3151_);
v_a_3191_ = lean_ctor_get(v___x_3169_, 0);
v_isSharedCheck_3198_ = !lean_is_exclusive(v___x_3169_);
if (v_isSharedCheck_3198_ == 0)
{
v___x_3193_ = v___x_3169_;
v_isShared_3194_ = v_isSharedCheck_3198_;
goto v_resetjp_3192_;
}
else
{
lean_inc(v_a_3191_);
lean_dec(v___x_3169_);
v___x_3193_ = lean_box(0);
v_isShared_3194_ = v_isSharedCheck_3198_;
goto v_resetjp_3192_;
}
v_resetjp_3192_:
{
lean_object* v___x_3196_; 
if (v_isShared_3194_ == 0)
{
v___x_3196_ = v___x_3193_;
goto v_reusejp_3195_;
}
else
{
lean_object* v_reuseFailAlloc_3197_; 
v_reuseFailAlloc_3197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3197_, 0, v_a_3191_);
v___x_3196_ = v_reuseFailAlloc_3197_;
goto v_reusejp_3195_;
}
v_reusejp_3195_:
{
return v___x_3196_;
}
}
}
}
v___jp_3161_:
{
size_t v___x_3163_; size_t v___x_3164_; 
v___x_3163_ = ((size_t)1ULL);
v___x_3164_ = lean_usize_add(v_i_3154_, v___x_3163_);
v_i_3154_ = v___x_3164_;
v_b_3155_ = v_a_3162_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___boxed(lean_object* v_a_3199_, lean_object* v_as_3200_, lean_object* v_sz_3201_, lean_object* v_i_3202_, lean_object* v_b_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_){
_start:
{
size_t v_sz_boxed_3209_; size_t v_i_boxed_3210_; lean_object* v_res_3211_; 
v_sz_boxed_3209_ = lean_unbox_usize(v_sz_3201_);
lean_dec(v_sz_3201_);
v_i_boxed_3210_ = lean_unbox_usize(v_i_3202_);
lean_dec(v_i_3202_);
v_res_3211_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6(v_a_3199_, v_as_3200_, v_sz_boxed_3209_, v_i_boxed_3210_, v_b_3203_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_);
lean_dec(v___y_3207_);
lean_dec_ref(v___y_3206_);
lean_dec(v___y_3205_);
lean_dec_ref(v___y_3204_);
lean_dec_ref(v_as_3200_);
return v_res_3211_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7(lean_object* v_snd_3212_, lean_object* v_as_3213_, size_t v_sz_3214_, size_t v_i_3215_, lean_object* v_b_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_){
_start:
{
uint8_t v___x_3222_; 
v___x_3222_ = lean_usize_dec_lt(v_i_3215_, v_sz_3214_);
if (v___x_3222_ == 0)
{
lean_object* v___x_3223_; 
v___x_3223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3223_, 0, v_b_3216_);
return v___x_3223_;
}
else
{
lean_object* v___x_3224_; lean_object* v_a_3225_; size_t v_sz_3226_; size_t v___x_3227_; lean_object* v___x_3228_; 
v___x_3224_ = lean_box(0);
v_a_3225_ = lean_array_uget_borrowed(v_as_3213_, v_i_3215_);
v_sz_3226_ = lean_array_size(v_snd_3212_);
v___x_3227_ = ((size_t)0ULL);
lean_inc(v_a_3225_);
v___x_3228_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6(v_a_3225_, v_snd_3212_, v_sz_3226_, v___x_3227_, v___x_3224_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_);
if (lean_obj_tag(v___x_3228_) == 0)
{
size_t v___x_3229_; size_t v___x_3230_; 
lean_dec_ref_known(v___x_3228_, 1);
v___x_3229_ = ((size_t)1ULL);
v___x_3230_ = lean_usize_add(v_i_3215_, v___x_3229_);
v_i_3215_ = v___x_3230_;
v_b_3216_ = v___x_3224_;
goto _start;
}
else
{
return v___x_3228_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7___boxed(lean_object* v_snd_3232_, lean_object* v_as_3233_, lean_object* v_sz_3234_, lean_object* v_i_3235_, lean_object* v_b_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_){
_start:
{
size_t v_sz_boxed_3242_; size_t v_i_boxed_3243_; lean_object* v_res_3244_; 
v_sz_boxed_3242_ = lean_unbox_usize(v_sz_3234_);
lean_dec(v_sz_3234_);
v_i_boxed_3243_ = lean_unbox_usize(v_i_3235_);
lean_dec(v_i_3235_);
v_res_3244_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7(v_snd_3232_, v_as_3233_, v_sz_boxed_3242_, v_i_boxed_3243_, v_b_3236_, v___y_3237_, v___y_3238_, v___y_3239_, v___y_3240_);
lean_dec(v___y_3240_);
lean_dec_ref(v___y_3239_);
lean_dec(v___y_3238_);
lean_dec_ref(v___y_3237_);
lean_dec_ref(v_as_3233_);
lean_dec_ref(v_snd_3232_);
return v_res_3244_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8(lean_object* v_snd_3245_, lean_object* v_as_3246_, size_t v_sz_3247_, size_t v_i_3248_, lean_object* v_b_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_){
_start:
{
uint8_t v___x_3255_; 
v___x_3255_ = lean_usize_dec_lt(v_i_3248_, v_sz_3247_);
if (v___x_3255_ == 0)
{
lean_object* v___x_3256_; 
v___x_3256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3256_, 0, v_b_3249_);
return v___x_3256_;
}
else
{
lean_object* v_a_3257_; lean_object* v_indGroupInst_3258_; lean_object* v_params_3259_; lean_object* v___x_3260_; size_t v_sz_3261_; size_t v___x_3262_; lean_object* v___x_3263_; 
v_a_3257_ = lean_array_uget_borrowed(v_as_3246_, v_i_3248_);
v_indGroupInst_3258_ = lean_ctor_get(v_a_3257_, 4);
v_params_3259_ = lean_ctor_get(v_indGroupInst_3258_, 2);
v___x_3260_ = lean_box(0);
v_sz_3261_ = lean_array_size(v_params_3259_);
v___x_3262_ = ((size_t)0ULL);
v___x_3263_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7(v_snd_3245_, v_params_3259_, v_sz_3261_, v___x_3262_, v___x_3260_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_);
if (lean_obj_tag(v___x_3263_) == 0)
{
size_t v___x_3264_; size_t v___x_3265_; 
lean_dec_ref_known(v___x_3263_, 1);
v___x_3264_ = ((size_t)1ULL);
v___x_3265_ = lean_usize_add(v_i_3248_, v___x_3264_);
v_i_3248_ = v___x_3265_;
v_b_3249_ = v___x_3260_;
goto _start;
}
else
{
return v___x_3263_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8___boxed(lean_object* v_snd_3267_, lean_object* v_as_3268_, lean_object* v_sz_3269_, lean_object* v_i_3270_, lean_object* v_b_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_){
_start:
{
size_t v_sz_boxed_3277_; size_t v_i_boxed_3278_; lean_object* v_res_3279_; 
v_sz_boxed_3277_ = lean_unbox_usize(v_sz_3269_);
lean_dec(v_sz_3269_);
v_i_boxed_3278_ = lean_unbox_usize(v_i_3270_);
lean_dec(v_i_3270_);
v_res_3279_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8(v_snd_3267_, v_as_3268_, v_sz_boxed_3277_, v_i_boxed_3278_, v_b_3271_, v___y_3272_, v___y_3273_, v___y_3274_, v___y_3275_);
lean_dec(v___y_3275_);
lean_dec_ref(v___y_3274_);
lean_dec(v___y_3273_);
lean_dec_ref(v___y_3272_);
lean_dec_ref(v_as_3268_);
lean_dec_ref(v_snd_3267_);
return v_res_3279_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__0(void){
_start:
{
lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; 
v___x_3280_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__3));
v___x_3281_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0___closed__1));
v___x_3282_ = l_Lean_Name_append(v___x_3281_, v___x_3280_);
return v___x_3282_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3284_; lean_object* v___x_3285_; 
v___x_3284_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__1));
v___x_3285_ = l_Lean_stringToMessageData(v___x_3284_);
return v___x_3285_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__4(void){
_start:
{
lean_object* v___x_3287_; lean_object* v___x_3288_; 
v___x_3287_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__3));
v___x_3288_ = l_Lean_stringToMessageData(v___x_3287_);
return v___x_3288_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__6(void){
_start:
{
lean_object* v___x_3290_; lean_object* v___x_3291_; 
v___x_3290_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__5));
v___x_3291_ = l_Lean_stringToMessageData(v___x_3290_);
return v___x_3291_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__8(void){
_start:
{
lean_object* v___x_3293_; lean_object* v___x_3294_; 
v___x_3293_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__7));
v___x_3294_ = l_Lean_stringToMessageData(v___x_3293_);
return v___x_3294_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__10(void){
_start:
{
lean_object* v___x_3296_; lean_object* v___x_3297_; 
v___x_3296_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__9));
v___x_3297_ = l_Lean_stringToMessageData(v___x_3296_);
return v___x_3297_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0(size_t v___x_3298_, lean_object* v_a_3299_, lean_object* v_xs_3300_, lean_object* v_a_3301_, lean_object* v_recArgInfos_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_){
_start:
{
lean_object* v___y_3309_; lean_object* v___y_3310_; lean_object* v___y_3311_; lean_object* v___y_3312_; lean_object* v___y_3313_; lean_object* v___y_3314_; lean_object* v___y_3315_; lean_object* v___x_3328_; lean_object* v___y_3330_; lean_object* v___y_3331_; lean_object* v___y_3332_; lean_object* v___y_3333_; lean_object* v___y_3334_; lean_object* v___y_3335_; lean_object* v___y_3336_; lean_object* v___x_3356_; lean_object* v_a_3357_; size_t v_sz_3358_; lean_object* v___x_3359_; lean_object* v___y_3361_; lean_object* v___y_3362_; lean_object* v___y_3363_; lean_object* v___y_3364_; uint8_t v___x_3421_; 
v___x_3328_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__3));
v___x_3356_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0(v___x_3328_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_);
v_a_3357_ = lean_ctor_get(v___x_3356_, 0);
lean_inc(v_a_3357_);
lean_dec_ref(v___x_3356_);
v_sz_3358_ = lean_array_size(v_recArgInfos_3302_);
lean_inc_ref(v_recArgInfos_3302_);
v___x_3359_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__2(v_sz_3358_, v___x_3298_, v_recArgInfos_3302_);
v___x_3421_ = lean_unbox(v_a_3357_);
lean_dec(v_a_3357_);
if (v___x_3421_ == 0)
{
v___y_3361_ = v___y_3303_;
v___y_3362_ = v___y_3304_;
v___y_3363_ = v___y_3305_;
v___y_3364_ = v___y_3306_;
goto v___jp_3360_;
}
else
{
lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; 
v___x_3422_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__10, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__10);
lean_inc_ref(v___x_3359_);
v___x_3423_ = lean_array_to_list(v___x_3359_);
v___x_3424_ = lean_box(0);
v___x_3425_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__0(v___x_3423_, v___x_3424_);
v___x_3426_ = l_Lean_MessageData_ofList(v___x_3425_);
v___x_3427_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3427_, 0, v___x_3422_);
lean_ctor_set(v___x_3427_, 1, v___x_3426_);
v___x_3428_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_3328_, v___x_3427_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_);
if (lean_obj_tag(v___x_3428_) == 0)
{
lean_dec_ref_known(v___x_3428_, 1);
v___y_3361_ = v___y_3303_;
v___y_3362_ = v___y_3304_;
v___y_3363_ = v___y_3305_;
v___y_3364_ = v___y_3306_;
goto v___jp_3360_;
}
else
{
lean_object* v_a_3429_; lean_object* v___x_3431_; uint8_t v_isShared_3432_; uint8_t v_isSharedCheck_3436_; 
lean_dec_ref(v___x_3359_);
lean_dec_ref(v_recArgInfos_3302_);
lean_dec_ref(v_a_3301_);
lean_dec_ref(v_xs_3300_);
lean_dec_ref(v_a_3299_);
v_a_3429_ = lean_ctor_get(v___x_3428_, 0);
v_isSharedCheck_3436_ = !lean_is_exclusive(v___x_3428_);
if (v_isSharedCheck_3436_ == 0)
{
v___x_3431_ = v___x_3428_;
v_isShared_3432_ = v_isSharedCheck_3436_;
goto v_resetjp_3430_;
}
else
{
lean_inc(v_a_3429_);
lean_dec(v___x_3428_);
v___x_3431_ = lean_box(0);
v_isShared_3432_ = v_isSharedCheck_3436_;
goto v_resetjp_3430_;
}
v_resetjp_3430_:
{
lean_object* v___x_3434_; 
if (v_isShared_3432_ == 0)
{
v___x_3434_ = v___x_3431_;
goto v_reusejp_3433_;
}
else
{
lean_object* v_reuseFailAlloc_3435_; 
v_reuseFailAlloc_3435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3435_, 0, v_a_3429_);
v___x_3434_ = v_reuseFailAlloc_3435_;
goto v_reusejp_3433_;
}
v_reusejp_3433_:
{
return v___x_3434_;
}
}
}
}
v___jp_3308_:
{
lean_object* v___x_3316_; size_t v_sz_3317_; lean_object* v___x_3318_; 
v___x_3316_ = lean_box(0);
v_sz_3317_ = lean_array_size(v___y_3310_);
v___x_3318_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8(v___y_3311_, v___y_3310_, v_sz_3317_, v___x_3298_, v___x_3316_, v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_);
lean_dec_ref(v___y_3310_);
if (lean_obj_tag(v___x_3318_) == 0)
{
lean_object* v___x_3319_; 
lean_dec_ref_known(v___x_3318_, 1);
v___x_3319_ = l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___redArg(v___y_3311_, v___y_3309_, v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_);
lean_dec_ref(v___y_3311_);
return v___x_3319_;
}
else
{
lean_object* v_a_3320_; lean_object* v___x_3322_; uint8_t v_isShared_3323_; uint8_t v_isSharedCheck_3327_; 
lean_dec_ref(v___y_3311_);
lean_dec_ref(v___y_3309_);
v_a_3320_ = lean_ctor_get(v___x_3318_, 0);
v_isSharedCheck_3327_ = !lean_is_exclusive(v___x_3318_);
if (v_isSharedCheck_3327_ == 0)
{
v___x_3322_ = v___x_3318_;
v_isShared_3323_ = v_isSharedCheck_3327_;
goto v_resetjp_3321_;
}
else
{
lean_inc(v_a_3320_);
lean_dec(v___x_3318_);
v___x_3322_ = lean_box(0);
v_isShared_3323_ = v_isSharedCheck_3327_;
goto v_resetjp_3321_;
}
v_resetjp_3321_:
{
lean_object* v___x_3325_; 
if (v_isShared_3323_ == 0)
{
v___x_3325_ = v___x_3322_;
goto v_reusejp_3324_;
}
else
{
lean_object* v_reuseFailAlloc_3326_; 
v_reuseFailAlloc_3326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3326_, 0, v_a_3320_);
v___x_3325_ = v_reuseFailAlloc_3326_;
goto v_reusejp_3324_;
}
v_reusejp_3324_:
{
return v___x_3325_;
}
}
}
}
v___jp_3329_:
{
lean_object* v_toCold_3337_; lean_object* v_options_3338_; uint8_t v_hasTrace_3339_; 
v_toCold_3337_ = lean_ctor_get(v___y_3335_, 0);
v_options_3338_ = lean_ctor_get(v_toCold_3337_, 2);
v_hasTrace_3339_ = lean_ctor_get_uint8(v_options_3338_, sizeof(void*)*1);
if (v_hasTrace_3339_ == 0)
{
v___y_3309_ = v___y_3331_;
v___y_3310_ = v___y_3330_;
v___y_3311_ = v___y_3332_;
v___y_3312_ = v___y_3333_;
v___y_3313_ = v___y_3334_;
v___y_3314_ = v___y_3335_;
v___y_3315_ = v___y_3336_;
goto v___jp_3308_;
}
else
{
lean_object* v_inheritedTraceOptions_3340_; lean_object* v___x_3341_; uint8_t v___x_3342_; 
v_inheritedTraceOptions_3340_ = lean_ctor_get(v_toCold_3337_, 11);
v___x_3341_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__0);
v___x_3342_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3340_, v_options_3338_, v___x_3341_);
if (v___x_3342_ == 0)
{
v___y_3309_ = v___y_3331_;
v___y_3310_ = v___y_3330_;
v___y_3311_ = v___y_3332_;
v___y_3312_ = v___y_3333_;
v___y_3313_ = v___y_3334_;
v___y_3314_ = v___y_3335_;
v___y_3315_ = v___y_3336_;
goto v___jp_3308_;
}
else
{
lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; 
v___x_3343_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__2);
lean_inc_ref(v___y_3330_);
v___x_3344_ = l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10(v___y_3330_);
v___x_3345_ = l_Lean_MessageData_ofFormat(v___x_3344_);
v___x_3346_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3346_, 0, v___x_3343_);
lean_ctor_set(v___x_3346_, 1, v___x_3345_);
v___x_3347_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_3328_, v___x_3346_, v___y_3333_, v___y_3334_, v___y_3335_, v___y_3336_);
if (lean_obj_tag(v___x_3347_) == 0)
{
lean_dec_ref_known(v___x_3347_, 1);
v___y_3309_ = v___y_3331_;
v___y_3310_ = v___y_3330_;
v___y_3311_ = v___y_3332_;
v___y_3312_ = v___y_3333_;
v___y_3313_ = v___y_3334_;
v___y_3314_ = v___y_3335_;
v___y_3315_ = v___y_3336_;
goto v___jp_3308_;
}
else
{
lean_object* v_a_3348_; lean_object* v___x_3350_; uint8_t v_isShared_3351_; uint8_t v_isSharedCheck_3355_; 
lean_dec_ref(v___y_3332_);
lean_dec_ref(v___y_3331_);
lean_dec_ref(v___y_3330_);
v_a_3348_ = lean_ctor_get(v___x_3347_, 0);
v_isSharedCheck_3355_ = !lean_is_exclusive(v___x_3347_);
if (v_isSharedCheck_3355_ == 0)
{
v___x_3350_ = v___x_3347_;
v_isShared_3351_ = v_isSharedCheck_3355_;
goto v_resetjp_3349_;
}
else
{
lean_inc(v_a_3348_);
lean_dec(v___x_3347_);
v___x_3350_ = lean_box(0);
v_isShared_3351_ = v_isSharedCheck_3355_;
goto v_resetjp_3349_;
}
v_resetjp_3349_:
{
lean_object* v___x_3353_; 
if (v_isShared_3351_ == 0)
{
v___x_3353_ = v___x_3350_;
goto v_reusejp_3352_;
}
else
{
lean_object* v_reuseFailAlloc_3354_; 
v_reuseFailAlloc_3354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3354_, 0, v_a_3348_);
v___x_3353_ = v_reuseFailAlloc_3354_;
goto v_reusejp_3352_;
}
v_reusejp_3352_:
{
return v___x_3353_;
}
}
}
}
}
}
v___jp_3360_:
{
lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v_snd_3367_; lean_object* v_fst_3368_; lean_object* v___x_3370_; uint8_t v_isShared_3371_; uint8_t v_isSharedCheck_3420_; 
lean_inc_ref(v_recArgInfos_3302_);
v___x_3365_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__3(v_sz_3358_, v___x_3298_, v_recArgInfos_3302_);
lean_inc_ref(v_xs_3300_);
v___x_3366_ = l_Lean_Elab_FixedParamPerms_erase(v_a_3299_, v_xs_3300_, v___x_3365_);
v_snd_3367_ = lean_ctor_get(v___x_3366_, 1);
v_fst_3368_ = lean_ctor_get(v___x_3366_, 0);
v_isSharedCheck_3420_ = !lean_is_exclusive(v___x_3366_);
if (v_isSharedCheck_3420_ == 0)
{
v___x_3370_ = v___x_3366_;
v_isShared_3371_ = v_isSharedCheck_3420_;
goto v_resetjp_3369_;
}
else
{
lean_inc(v_snd_3367_);
lean_inc(v_fst_3368_);
lean_dec(v___x_3366_);
v___x_3370_ = lean_box(0);
v_isShared_3371_ = v_isSharedCheck_3420_;
goto v_resetjp_3369_;
}
v_resetjp_3369_:
{
lean_object* v_fst_3372_; lean_object* v_snd_3373_; lean_object* v___x_3375_; uint8_t v_isShared_3376_; uint8_t v_isSharedCheck_3419_; 
v_fst_3372_ = lean_ctor_get(v_snd_3367_, 0);
v_snd_3373_ = lean_ctor_get(v_snd_3367_, 1);
v_isSharedCheck_3419_ = !lean_is_exclusive(v_snd_3367_);
if (v_isSharedCheck_3419_ == 0)
{
v___x_3375_ = v_snd_3367_;
v_isShared_3376_ = v_isSharedCheck_3419_;
goto v_resetjp_3374_;
}
else
{
lean_inc(v_snd_3373_);
lean_inc(v_fst_3372_);
lean_dec(v_snd_3367_);
v___x_3375_ = lean_box(0);
v_isShared_3376_ = v_isSharedCheck_3419_;
goto v_resetjp_3374_;
}
v_resetjp_3374_:
{
lean_object* v___x_3377_; lean_object* v___f_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; uint8_t v___x_3381_; 
v___x_3377_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg(v_fst_3368_, v_sz_3358_, v___x_3298_, v_recArgInfos_3302_);
lean_inc_ref(v___x_3377_);
lean_inc(v_fst_3372_);
v___f_3378_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___boxed), 10, 5);
lean_closure_set(v___f_3378_, 0, v_a_3301_);
lean_closure_set(v___f_3378_, 1, v_fst_3368_);
lean_closure_set(v___f_3378_, 2, v_fst_3372_);
lean_closure_set(v___f_3378_, 3, v___x_3377_);
lean_closure_set(v___f_3378_, 4, v___x_3359_);
v___x_3379_ = lean_array_get_size(v_fst_3372_);
v___x_3380_ = lean_array_get_size(v_xs_3300_);
v___x_3381_ = lean_nat_dec_eq(v___x_3379_, v___x_3380_);
if (v___x_3381_ == 0)
{
lean_object* v___x_3382_; lean_object* v_a_3383_; uint8_t v___x_3384_; 
v___x_3382_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0(v___x_3328_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_);
v_a_3383_ = lean_ctor_get(v___x_3382_, 0);
lean_inc(v_a_3383_);
lean_dec_ref(v___x_3382_);
v___x_3384_ = lean_unbox(v_a_3383_);
lean_dec(v_a_3383_);
if (v___x_3384_ == 0)
{
lean_del_object(v___x_3375_);
lean_dec(v_fst_3372_);
lean_del_object(v___x_3370_);
lean_dec_ref(v_xs_3300_);
v___y_3330_ = v___x_3377_;
v___y_3331_ = v___f_3378_;
v___y_3332_ = v_snd_3373_;
v___y_3333_ = v___y_3361_;
v___y_3334_ = v___y_3362_;
v___y_3335_ = v___y_3363_;
v___y_3336_ = v___y_3364_;
goto v___jp_3329_;
}
else
{
lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3391_; 
v___x_3385_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__4);
v___x_3386_ = lean_array_to_list(v_xs_3300_);
v___x_3387_ = lean_box(0);
v___x_3388_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_3386_, v___x_3387_);
v___x_3389_ = l_Lean_MessageData_ofList(v___x_3388_);
if (v_isShared_3376_ == 0)
{
lean_ctor_set_tag(v___x_3375_, 7);
lean_ctor_set(v___x_3375_, 1, v___x_3389_);
lean_ctor_set(v___x_3375_, 0, v___x_3385_);
v___x_3391_ = v___x_3375_;
goto v_reusejp_3390_;
}
else
{
lean_object* v_reuseFailAlloc_3417_; 
v_reuseFailAlloc_3417_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3417_, 0, v___x_3385_);
lean_ctor_set(v_reuseFailAlloc_3417_, 1, v___x_3389_);
v___x_3391_ = v_reuseFailAlloc_3417_;
goto v_reusejp_3390_;
}
v_reusejp_3390_:
{
lean_object* v___x_3392_; lean_object* v___x_3394_; 
v___x_3392_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__6, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__6);
if (v_isShared_3371_ == 0)
{
lean_ctor_set_tag(v___x_3370_, 7);
lean_ctor_set(v___x_3370_, 1, v___x_3392_);
lean_ctor_set(v___x_3370_, 0, v___x_3391_);
v___x_3394_ = v___x_3370_;
goto v_reusejp_3393_;
}
else
{
lean_object* v_reuseFailAlloc_3416_; 
v_reuseFailAlloc_3416_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3416_, 0, v___x_3391_);
lean_ctor_set(v_reuseFailAlloc_3416_, 1, v___x_3392_);
v___x_3394_ = v_reuseFailAlloc_3416_;
goto v_reusejp_3393_;
}
v_reusejp_3393_:
{
lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; size_t v_sz_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; 
v___x_3395_ = lean_array_to_list(v_fst_3372_);
v___x_3396_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_3395_, v___x_3387_);
v___x_3397_ = l_Lean_MessageData_ofList(v___x_3396_);
v___x_3398_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3398_, 0, v___x_3394_);
lean_ctor_set(v___x_3398_, 1, v___x_3397_);
v___x_3399_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__8);
v___x_3400_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3400_, 0, v___x_3398_);
lean_ctor_set(v___x_3400_, 1, v___x_3399_);
v_sz_3401_ = lean_array_size(v_snd_3373_);
lean_inc(v_snd_3373_);
v___x_3402_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__11(v_sz_3401_, v___x_3298_, v_snd_3373_);
v___x_3403_ = lean_array_to_list(v___x_3402_);
v___x_3404_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_3403_, v___x_3387_);
v___x_3405_ = l_Lean_MessageData_ofList(v___x_3404_);
v___x_3406_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3406_, 0, v___x_3400_);
lean_ctor_set(v___x_3406_, 1, v___x_3405_);
v___x_3407_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_3328_, v___x_3406_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_);
if (lean_obj_tag(v___x_3407_) == 0)
{
lean_dec_ref_known(v___x_3407_, 1);
v___y_3330_ = v___x_3377_;
v___y_3331_ = v___f_3378_;
v___y_3332_ = v_snd_3373_;
v___y_3333_ = v___y_3361_;
v___y_3334_ = v___y_3362_;
v___y_3335_ = v___y_3363_;
v___y_3336_ = v___y_3364_;
goto v___jp_3329_;
}
else
{
lean_object* v_a_3408_; lean_object* v___x_3410_; uint8_t v_isShared_3411_; uint8_t v_isSharedCheck_3415_; 
lean_dec_ref(v___f_3378_);
lean_dec_ref(v___x_3377_);
lean_dec(v_snd_3373_);
v_a_3408_ = lean_ctor_get(v___x_3407_, 0);
v_isSharedCheck_3415_ = !lean_is_exclusive(v___x_3407_);
if (v_isSharedCheck_3415_ == 0)
{
v___x_3410_ = v___x_3407_;
v_isShared_3411_ = v_isSharedCheck_3415_;
goto v_resetjp_3409_;
}
else
{
lean_inc(v_a_3408_);
lean_dec(v___x_3407_);
v___x_3410_ = lean_box(0);
v_isShared_3411_ = v_isSharedCheck_3415_;
goto v_resetjp_3409_;
}
v_resetjp_3409_:
{
lean_object* v___x_3413_; 
if (v_isShared_3411_ == 0)
{
v___x_3413_ = v___x_3410_;
goto v_reusejp_3412_;
}
else
{
lean_object* v_reuseFailAlloc_3414_; 
v_reuseFailAlloc_3414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3414_, 0, v_a_3408_);
v___x_3413_ = v_reuseFailAlloc_3414_;
goto v_reusejp_3412_;
}
v_reusejp_3412_:
{
return v___x_3413_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3418_; 
lean_dec_ref(v___x_3377_);
lean_del_object(v___x_3375_);
lean_dec(v_fst_3372_);
lean_del_object(v___x_3370_);
lean_dec_ref(v_xs_3300_);
v___x_3418_ = l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___redArg(v_snd_3373_, v___f_3378_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_);
lean_dec(v_snd_3373_);
return v___x_3418_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___boxed(lean_object* v___x_3437_, lean_object* v_a_3438_, lean_object* v_xs_3439_, lean_object* v_a_3440_, lean_object* v_recArgInfos_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_){
_start:
{
size_t v___x_13071__boxed_3447_; lean_object* v_res_3448_; 
v___x_13071__boxed_3447_ = lean_unbox_usize(v___x_3437_);
lean_dec(v___x_3437_);
v_res_3448_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0(v___x_13071__boxed_3447_, v_a_3438_, v_xs_3439_, v_a_3440_, v_recArgInfos_3441_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_);
lean_dec(v___y_3445_);
lean_dec_ref(v___y_3444_);
lean_dec(v___y_3443_);
lean_dec_ref(v___y_3442_);
return v_res_3448_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg(lean_object* v___x_3449_, lean_object* v_xs_3450_, size_t v_sz_3451_, size_t v_i_3452_, lean_object* v_bs_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_){
_start:
{
uint8_t v___x_3459_; 
v___x_3459_ = lean_usize_dec_lt(v_i_3452_, v_sz_3451_);
if (v___x_3459_ == 0)
{
lean_object* v___x_3460_; 
lean_dec_ref(v_xs_3450_);
v___x_3460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3460_, 0, v_bs_3453_);
return v___x_3460_;
}
else
{
lean_object* v_v_3461_; lean_object* v_value_3462_; lean_object* v___x_3463_; lean_object* v_bs_x27_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; 
v_v_3461_ = lean_array_uget_borrowed(v_bs_3453_, v_i_3452_);
v_value_3462_ = lean_ctor_get(v_v_3461_, 7);
lean_inc_ref(v_value_3462_);
v___x_3463_ = lean_unsigned_to_nat(0u);
v_bs_x27_3464_ = lean_array_uset(v_bs_3453_, v_i_3452_, v___x_3463_);
v___x_3465_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0);
v___x_3466_ = lean_usize_to_nat(v_i_3452_);
v___x_3467_ = lean_array_get_borrowed(v___x_3465_, v___x_3449_, v___x_3466_);
lean_dec(v___x_3466_);
lean_inc_ref(v_xs_3450_);
lean_inc(v___x_3467_);
v___x_3468_ = l_Lean_Elab_FixedParamPerm_instantiateLambda(v___x_3467_, v_value_3462_, v_xs_3450_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_);
if (lean_obj_tag(v___x_3468_) == 0)
{
lean_object* v_a_3469_; size_t v___x_3470_; size_t v___x_3471_; lean_object* v___x_3472_; 
v_a_3469_ = lean_ctor_get(v___x_3468_, 0);
lean_inc(v_a_3469_);
lean_dec_ref_known(v___x_3468_, 1);
v___x_3470_ = ((size_t)1ULL);
v___x_3471_ = lean_usize_add(v_i_3452_, v___x_3470_);
v___x_3472_ = lean_array_uset(v_bs_x27_3464_, v_i_3452_, v_a_3469_);
v_i_3452_ = v___x_3471_;
v_bs_3453_ = v___x_3472_;
goto _start;
}
else
{
lean_object* v_a_3474_; lean_object* v___x_3476_; uint8_t v_isShared_3477_; uint8_t v_isSharedCheck_3481_; 
lean_dec_ref(v_bs_x27_3464_);
lean_dec_ref(v_xs_3450_);
v_a_3474_ = lean_ctor_get(v___x_3468_, 0);
v_isSharedCheck_3481_ = !lean_is_exclusive(v___x_3468_);
if (v_isSharedCheck_3481_ == 0)
{
v___x_3476_ = v___x_3468_;
v_isShared_3477_ = v_isSharedCheck_3481_;
goto v_resetjp_3475_;
}
else
{
lean_inc(v_a_3474_);
lean_dec(v___x_3468_);
v___x_3476_ = lean_box(0);
v_isShared_3477_ = v_isSharedCheck_3481_;
goto v_resetjp_3475_;
}
v_resetjp_3475_:
{
lean_object* v___x_3479_; 
if (v_isShared_3477_ == 0)
{
v___x_3479_ = v___x_3476_;
goto v_reusejp_3478_;
}
else
{
lean_object* v_reuseFailAlloc_3480_; 
v_reuseFailAlloc_3480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3480_, 0, v_a_3474_);
v___x_3479_ = v_reuseFailAlloc_3480_;
goto v_reusejp_3478_;
}
v_reusejp_3478_:
{
return v___x_3479_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg___boxed(lean_object* v___x_3482_, lean_object* v_xs_3483_, lean_object* v_sz_3484_, lean_object* v_i_3485_, lean_object* v_bs_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_){
_start:
{
size_t v_sz_boxed_3492_; size_t v_i_boxed_3493_; lean_object* v_res_3494_; 
v_sz_boxed_3492_ = lean_unbox_usize(v_sz_3484_);
lean_dec(v_sz_3484_);
v_i_boxed_3493_ = lean_unbox_usize(v_i_3485_);
lean_dec(v_i_3485_);
v_res_3494_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg(v___x_3482_, v_xs_3483_, v_sz_boxed_3492_, v_i_boxed_3493_, v_bs_3486_, v___y_3487_, v___y_3488_, v___y_3489_, v___y_3490_);
lean_dec(v___y_3490_);
lean_dec_ref(v___y_3489_);
lean_dec(v___y_3488_);
lean_dec_ref(v___y_3487_);
lean_dec_ref(v___x_3482_);
return v_res_3494_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__2(lean_object* v_a_3495_, lean_object* v_perms_3496_, size_t v___x_3497_, lean_object* v_fnNames_3498_, lean_object* v_a_3499_, lean_object* v_termMeasure_x3fs_3500_, lean_object* v_xs_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_){
_start:
{
size_t v_sz_3507_; lean_object* v___x_3508_; 
v_sz_3507_ = lean_array_size(v_a_3495_);
lean_inc_ref(v_a_3495_);
lean_inc_ref(v_xs_3501_);
v___x_3508_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg(v_perms_3496_, v_xs_3501_, v_sz_3507_, v___x_3497_, v_a_3495_, v___y_3502_, v___y_3503_, v___y_3504_, v___y_3505_);
if (lean_obj_tag(v___x_3508_) == 0)
{
lean_object* v_a_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; 
v_a_3509_ = lean_ctor_get(v___x_3508_, 0);
lean_inc_n(v_a_3509_, 2);
lean_dec_ref_known(v___x_3508_, 1);
lean_inc_ref(v_xs_3501_);
lean_inc_ref(v_a_3499_);
lean_inc_ref(v_fnNames_3498_);
v___x_3510_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_findRecArgCandidates___boxed), 10, 5);
lean_closure_set(v___x_3510_, 0, v_fnNames_3498_);
lean_closure_set(v___x_3510_, 1, v_a_3499_);
lean_closure_set(v___x_3510_, 2, v_xs_3501_);
lean_closure_set(v___x_3510_, 3, v_a_3509_);
lean_closure_set(v___x_3510_, 4, v_termMeasure_x3fs_3500_);
lean_inc_ref(v_a_3495_);
v___x_3511_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v_a_3495_, v___x_3510_, v___y_3502_, v___y_3503_, v___y_3504_, v___y_3505_);
if (lean_obj_tag(v___x_3511_) == 0)
{
lean_object* v_a_3512_; lean_object* v___x_3513_; lean_object* v___f_3514_; lean_object* v___x_3515_; 
v_a_3512_ = lean_ctor_get(v___x_3511_, 0);
lean_inc(v_a_3512_);
lean_dec_ref_known(v___x_3511_, 1);
v___x_3513_ = lean_box_usize(v___x_3497_);
lean_inc_ref(v_xs_3501_);
v___f_3514_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___boxed), 10, 4);
lean_closure_set(v___f_3514_, 0, v___x_3513_);
lean_closure_set(v___f_3514_, 1, v_a_3499_);
lean_closure_set(v___f_3514_, 2, v_xs_3501_);
lean_closure_set(v___f_3514_, 3, v_a_3495_);
v___x_3515_ = l_Lean_Elab_Structural_tryCandidates___redArg(v_fnNames_3498_, v_xs_3501_, v_a_3509_, v_a_3512_, v___f_3514_, v___y_3502_, v___y_3503_, v___y_3504_, v___y_3505_);
lean_dec_ref(v_fnNames_3498_);
return v___x_3515_;
}
else
{
lean_object* v_a_3516_; lean_object* v___x_3518_; uint8_t v_isShared_3519_; uint8_t v_isSharedCheck_3523_; 
lean_dec(v_a_3509_);
lean_dec_ref(v_xs_3501_);
lean_dec_ref(v_a_3499_);
lean_dec_ref(v_fnNames_3498_);
lean_dec_ref(v_a_3495_);
v_a_3516_ = lean_ctor_get(v___x_3511_, 0);
v_isSharedCheck_3523_ = !lean_is_exclusive(v___x_3511_);
if (v_isSharedCheck_3523_ == 0)
{
v___x_3518_ = v___x_3511_;
v_isShared_3519_ = v_isSharedCheck_3523_;
goto v_resetjp_3517_;
}
else
{
lean_inc(v_a_3516_);
lean_dec(v___x_3511_);
v___x_3518_ = lean_box(0);
v_isShared_3519_ = v_isSharedCheck_3523_;
goto v_resetjp_3517_;
}
v_resetjp_3517_:
{
lean_object* v___x_3521_; 
if (v_isShared_3519_ == 0)
{
v___x_3521_ = v___x_3518_;
goto v_reusejp_3520_;
}
else
{
lean_object* v_reuseFailAlloc_3522_; 
v_reuseFailAlloc_3522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3522_, 0, v_a_3516_);
v___x_3521_ = v_reuseFailAlloc_3522_;
goto v_reusejp_3520_;
}
v_reusejp_3520_:
{
return v___x_3521_;
}
}
}
}
else
{
lean_object* v_a_3524_; lean_object* v___x_3526_; uint8_t v_isShared_3527_; uint8_t v_isSharedCheck_3531_; 
lean_dec_ref(v_xs_3501_);
lean_dec_ref(v_termMeasure_x3fs_3500_);
lean_dec_ref(v_a_3499_);
lean_dec_ref(v_fnNames_3498_);
lean_dec_ref(v_a_3495_);
v_a_3524_ = lean_ctor_get(v___x_3508_, 0);
v_isSharedCheck_3531_ = !lean_is_exclusive(v___x_3508_);
if (v_isSharedCheck_3531_ == 0)
{
v___x_3526_ = v___x_3508_;
v_isShared_3527_ = v_isSharedCheck_3531_;
goto v_resetjp_3525_;
}
else
{
lean_inc(v_a_3524_);
lean_dec(v___x_3508_);
v___x_3526_ = lean_box(0);
v_isShared_3527_ = v_isSharedCheck_3531_;
goto v_resetjp_3525_;
}
v_resetjp_3525_:
{
lean_object* v___x_3529_; 
if (v_isShared_3527_ == 0)
{
v___x_3529_ = v___x_3526_;
goto v_reusejp_3528_;
}
else
{
lean_object* v_reuseFailAlloc_3530_; 
v_reuseFailAlloc_3530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3530_, 0, v_a_3524_);
v___x_3529_ = v_reuseFailAlloc_3530_;
goto v_reusejp_3528_;
}
v_reusejp_3528_:
{
return v___x_3529_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__2___boxed(lean_object* v_a_3532_, lean_object* v_perms_3533_, lean_object* v___x_3534_, lean_object* v_fnNames_3535_, lean_object* v_a_3536_, lean_object* v_termMeasure_x3fs_3537_, lean_object* v_xs_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_){
_start:
{
size_t v___x_13423__boxed_3544_; lean_object* v_res_3545_; 
v___x_13423__boxed_3544_ = lean_unbox_usize(v___x_3534_);
lean_dec(v___x_3534_);
v_res_3545_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__2(v_a_3532_, v_perms_3533_, v___x_13423__boxed_3544_, v_fnNames_3535_, v_a_3536_, v_termMeasure_x3fs_3537_, v_xs_3538_, v___y_3539_, v___y_3540_, v___y_3541_, v___y_3542_);
lean_dec(v___y_3542_);
lean_dec_ref(v___y_3541_);
lean_dec(v___y_3540_);
lean_dec_ref(v___y_3539_);
lean_dec_ref(v_perms_3533_);
return v_res_3545_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0(size_t v_sz_3546_, size_t v_i_3547_, lean_object* v_bs_3548_){
_start:
{
uint8_t v___x_3549_; 
v___x_3549_ = lean_usize_dec_lt(v_i_3547_, v_sz_3546_);
if (v___x_3549_ == 0)
{
return v_bs_3548_;
}
else
{
lean_object* v_v_3550_; lean_object* v_declName_3551_; lean_object* v___x_3552_; lean_object* v_bs_x27_3553_; size_t v___x_3554_; size_t v___x_3555_; lean_object* v___x_3556_; 
v_v_3550_ = lean_array_uget_borrowed(v_bs_3548_, v_i_3547_);
v_declName_3551_ = lean_ctor_get(v_v_3550_, 3);
lean_inc(v_declName_3551_);
v___x_3552_ = lean_unsigned_to_nat(0u);
v_bs_x27_3553_ = lean_array_uset(v_bs_3548_, v_i_3547_, v___x_3552_);
v___x_3554_ = ((size_t)1ULL);
v___x_3555_ = lean_usize_add(v_i_3547_, v___x_3554_);
v___x_3556_ = lean_array_uset(v_bs_x27_3553_, v_i_3547_, v_declName_3551_);
v_i_3547_ = v___x_3555_;
v_bs_3548_ = v___x_3556_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0___boxed(lean_object* v_sz_3558_, lean_object* v_i_3559_, lean_object* v_bs_3560_){
_start:
{
size_t v_sz_boxed_3561_; size_t v_i_boxed_3562_; lean_object* v_res_3563_; 
v_sz_boxed_3561_ = lean_unbox_usize(v_sz_3558_);
lean_dec(v_sz_3558_);
v_i_boxed_3562_ = lean_unbox_usize(v_i_3559_);
lean_dec(v_i_3559_);
v_res_3563_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0(v_sz_boxed_3561_, v_i_boxed_3562_, v_bs_3560_);
return v_res_3563_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1___redArg(lean_object* v_fnNames_3564_, lean_object* v_numSectionVars_3565_, size_t v_sz_3566_, size_t v_i_3567_, lean_object* v_bs_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_){
_start:
{
uint8_t v___x_3572_; 
v___x_3572_ = lean_usize_dec_lt(v_i_3567_, v_sz_3566_);
if (v___x_3572_ == 0)
{
lean_object* v___x_3573_; 
lean_dec(v_numSectionVars_3565_);
lean_dec_ref(v_fnNames_3564_);
v___x_3573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3573_, 0, v_bs_3568_);
return v___x_3573_;
}
else
{
lean_object* v_v_3574_; lean_object* v_ref_3575_; uint8_t v_kind_3576_; lean_object* v_levelParams_3577_; lean_object* v_modifiers_3578_; lean_object* v_declName_3579_; lean_object* v_binders_3580_; lean_object* v_numSectionVars_3581_; lean_object* v_type_3582_; lean_object* v_value_3583_; lean_object* v_termination_3584_; lean_object* v___x_3586_; uint8_t v_isShared_3587_; uint8_t v_isSharedCheck_3607_; 
v_v_3574_ = lean_array_uget(v_bs_3568_, v_i_3567_);
v_ref_3575_ = lean_ctor_get(v_v_3574_, 0);
v_kind_3576_ = lean_ctor_get_uint8(v_v_3574_, sizeof(void*)*9);
v_levelParams_3577_ = lean_ctor_get(v_v_3574_, 1);
v_modifiers_3578_ = lean_ctor_get(v_v_3574_, 2);
v_declName_3579_ = lean_ctor_get(v_v_3574_, 3);
v_binders_3580_ = lean_ctor_get(v_v_3574_, 4);
v_numSectionVars_3581_ = lean_ctor_get(v_v_3574_, 5);
v_type_3582_ = lean_ctor_get(v_v_3574_, 6);
v_value_3583_ = lean_ctor_get(v_v_3574_, 7);
v_termination_3584_ = lean_ctor_get(v_v_3574_, 8);
v_isSharedCheck_3607_ = !lean_is_exclusive(v_v_3574_);
if (v_isSharedCheck_3607_ == 0)
{
v___x_3586_ = v_v_3574_;
v_isShared_3587_ = v_isSharedCheck_3607_;
goto v_resetjp_3585_;
}
else
{
lean_inc(v_termination_3584_);
lean_inc(v_value_3583_);
lean_inc(v_type_3582_);
lean_inc(v_numSectionVars_3581_);
lean_inc(v_binders_3580_);
lean_inc(v_declName_3579_);
lean_inc(v_modifiers_3578_);
lean_inc(v_levelParams_3577_);
lean_inc(v_ref_3575_);
lean_dec(v_v_3574_);
v___x_3586_ = lean_box(0);
v_isShared_3587_ = v_isSharedCheck_3607_;
goto v_resetjp_3585_;
}
v_resetjp_3585_:
{
lean_object* v___x_3588_; 
lean_inc(v_numSectionVars_3565_);
lean_inc_ref(v_fnNames_3564_);
v___x_3588_ = l_Lean_Elab_Structural_preprocess(v_value_3583_, v_fnNames_3564_, v_numSectionVars_3565_, v___y_3569_, v___y_3570_);
if (lean_obj_tag(v___x_3588_) == 0)
{
lean_object* v_a_3589_; lean_object* v___x_3590_; lean_object* v_bs_x27_3591_; lean_object* v___x_3593_; 
v_a_3589_ = lean_ctor_get(v___x_3588_, 0);
lean_inc(v_a_3589_);
lean_dec_ref_known(v___x_3588_, 1);
v___x_3590_ = lean_unsigned_to_nat(0u);
v_bs_x27_3591_ = lean_array_uset(v_bs_3568_, v_i_3567_, v___x_3590_);
if (v_isShared_3587_ == 0)
{
lean_ctor_set(v___x_3586_, 7, v_a_3589_);
v___x_3593_ = v___x_3586_;
goto v_reusejp_3592_;
}
else
{
lean_object* v_reuseFailAlloc_3598_; 
v_reuseFailAlloc_3598_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_3598_, 0, v_ref_3575_);
lean_ctor_set(v_reuseFailAlloc_3598_, 1, v_levelParams_3577_);
lean_ctor_set(v_reuseFailAlloc_3598_, 2, v_modifiers_3578_);
lean_ctor_set(v_reuseFailAlloc_3598_, 3, v_declName_3579_);
lean_ctor_set(v_reuseFailAlloc_3598_, 4, v_binders_3580_);
lean_ctor_set(v_reuseFailAlloc_3598_, 5, v_numSectionVars_3581_);
lean_ctor_set(v_reuseFailAlloc_3598_, 6, v_type_3582_);
lean_ctor_set(v_reuseFailAlloc_3598_, 7, v_a_3589_);
lean_ctor_set(v_reuseFailAlloc_3598_, 8, v_termination_3584_);
lean_ctor_set_uint8(v_reuseFailAlloc_3598_, sizeof(void*)*9, v_kind_3576_);
v___x_3593_ = v_reuseFailAlloc_3598_;
goto v_reusejp_3592_;
}
v_reusejp_3592_:
{
size_t v___x_3594_; size_t v___x_3595_; lean_object* v___x_3596_; 
v___x_3594_ = ((size_t)1ULL);
v___x_3595_ = lean_usize_add(v_i_3567_, v___x_3594_);
v___x_3596_ = lean_array_uset(v_bs_x27_3591_, v_i_3567_, v___x_3593_);
v_i_3567_ = v___x_3595_;
v_bs_3568_ = v___x_3596_;
goto _start;
}
}
else
{
lean_object* v_a_3599_; lean_object* v___x_3601_; uint8_t v_isShared_3602_; uint8_t v_isSharedCheck_3606_; 
lean_del_object(v___x_3586_);
lean_dec_ref(v_termination_3584_);
lean_dec_ref(v_type_3582_);
lean_dec(v_numSectionVars_3581_);
lean_dec(v_binders_3580_);
lean_dec(v_declName_3579_);
lean_dec_ref(v_modifiers_3578_);
lean_dec(v_levelParams_3577_);
lean_dec(v_ref_3575_);
lean_dec_ref(v_bs_3568_);
lean_dec(v_numSectionVars_3565_);
lean_dec_ref(v_fnNames_3564_);
v_a_3599_ = lean_ctor_get(v___x_3588_, 0);
v_isSharedCheck_3606_ = !lean_is_exclusive(v___x_3588_);
if (v_isSharedCheck_3606_ == 0)
{
v___x_3601_ = v___x_3588_;
v_isShared_3602_ = v_isSharedCheck_3606_;
goto v_resetjp_3600_;
}
else
{
lean_inc(v_a_3599_);
lean_dec(v___x_3588_);
v___x_3601_ = lean_box(0);
v_isShared_3602_ = v_isSharedCheck_3606_;
goto v_resetjp_3600_;
}
v_resetjp_3600_:
{
lean_object* v___x_3604_; 
if (v_isShared_3602_ == 0)
{
v___x_3604_ = v___x_3601_;
goto v_reusejp_3603_;
}
else
{
lean_object* v_reuseFailAlloc_3605_; 
v_reuseFailAlloc_3605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3605_, 0, v_a_3599_);
v___x_3604_ = v_reuseFailAlloc_3605_;
goto v_reusejp_3603_;
}
v_reusejp_3603_:
{
return v___x_3604_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1___redArg___boxed(lean_object* v_fnNames_3608_, lean_object* v_numSectionVars_3609_, lean_object* v_sz_3610_, lean_object* v_i_3611_, lean_object* v_bs_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_){
_start:
{
size_t v_sz_boxed_3616_; size_t v_i_boxed_3617_; lean_object* v_res_3618_; 
v_sz_boxed_3616_ = lean_unbox_usize(v_sz_3610_);
lean_dec(v_sz_3610_);
v_i_boxed_3617_ = lean_unbox_usize(v_i_3611_);
lean_dec(v_i_3611_);
v_res_3618_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1___redArg(v_fnNames_3608_, v_numSectionVars_3609_, v_sz_boxed_3616_, v_i_boxed_3617_, v_bs_3612_, v___y_3613_, v___y_3614_);
lean_dec(v___y_3614_);
lean_dec_ref(v___y_3613_);
return v_res_3618_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1(lean_object* v_fnNames_3619_, lean_object* v_numSectionVars_3620_, size_t v_sz_3621_, size_t v_i_3622_, lean_object* v_bs_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_){
_start:
{
lean_object* v___x_3629_; 
v___x_3629_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1___redArg(v_fnNames_3619_, v_numSectionVars_3620_, v_sz_3621_, v_i_3622_, v_bs_3623_, v___y_3626_, v___y_3627_);
return v___x_3629_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1___boxed(lean_object* v_fnNames_3630_, lean_object* v_numSectionVars_3631_, lean_object* v_sz_3632_, lean_object* v_i_3633_, lean_object* v_bs_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_){
_start:
{
size_t v_sz_boxed_3640_; size_t v_i_boxed_3641_; lean_object* v_res_3642_; 
v_sz_boxed_3640_ = lean_unbox_usize(v_sz_3632_);
lean_dec(v_sz_3632_);
v_i_boxed_3641_ = lean_unbox_usize(v_i_3633_);
lean_dec(v_i_3633_);
v_res_3642_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1(v_fnNames_3630_, v_numSectionVars_3631_, v_sz_boxed_3640_, v_i_boxed_3641_, v_bs_3634_, v___y_3635_, v___y_3636_, v___y_3637_, v___y_3638_);
lean_dec(v___y_3638_);
lean_dec_ref(v___y_3637_);
lean_dec(v___y_3636_);
lean_dec_ref(v___y_3635_);
return v_res_3642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos(lean_object* v_preDefs_3643_, lean_object* v_termMeasure_x3fs_3644_, lean_object* v_a_3645_, lean_object* v_a_3646_, lean_object* v_a_3647_, lean_object* v_a_3648_){
_start:
{
lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v_numSectionVars_3653_; size_t v_sz_3654_; size_t v___x_3655_; lean_object* v_fnNames_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; 
v___x_3650_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_3651_ = lean_unsigned_to_nat(0u);
v___x_3652_ = lean_array_get_borrowed(v___x_3650_, v_preDefs_3643_, v___x_3651_);
v_numSectionVars_3653_ = lean_ctor_get(v___x_3652_, 5);
v_sz_3654_ = lean_array_size(v_preDefs_3643_);
v___x_3655_ = ((size_t)0ULL);
lean_inc_ref_n(v_preDefs_3643_, 2);
v_fnNames_3656_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0(v_sz_3654_, v___x_3655_, v_preDefs_3643_);
v___x_3657_ = lean_box_usize(v_sz_3654_);
v___x_3658_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___boxed__const__1));
lean_inc(v_numSectionVars_3653_);
lean_inc_ref(v_fnNames_3656_);
v___x_3659_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1___boxed), 10, 5);
lean_closure_set(v___x_3659_, 0, v_fnNames_3656_);
lean_closure_set(v___x_3659_, 1, v_numSectionVars_3653_);
lean_closure_set(v___x_3659_, 2, v___x_3657_);
lean_closure_set(v___x_3659_, 3, v___x_3658_);
lean_closure_set(v___x_3659_, 4, v_preDefs_3643_);
v___x_3660_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v_preDefs_3643_, v___x_3659_, v_a_3645_, v_a_3646_, v_a_3647_, v_a_3648_);
if (lean_obj_tag(v___x_3660_) == 0)
{
lean_object* v_a_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; 
v_a_3661_ = lean_ctor_get(v___x_3660_, 0);
lean_inc_n(v_a_3661_, 3);
lean_dec_ref_known(v___x_3660_, 1);
v___x_3662_ = lean_alloc_closure((void*)(l_Lean_Elab_getFixedParamPerms___boxed), 6, 1);
lean_closure_set(v___x_3662_, 0, v_a_3661_);
v___x_3663_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v_a_3661_, v___x_3662_, v_a_3645_, v_a_3646_, v_a_3647_, v_a_3648_);
if (lean_obj_tag(v___x_3663_) == 0)
{
lean_object* v_a_3664_; lean_object* v_perms_3665_; lean_object* v___x_3666_; lean_object* v_type_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___f_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; 
v_a_3664_ = lean_ctor_get(v___x_3663_, 0);
lean_inc(v_a_3664_);
lean_dec_ref_known(v___x_3663_, 1);
v_perms_3665_ = lean_ctor_get(v_a_3664_, 1);
lean_inc_ref_n(v_perms_3665_, 2);
v___x_3666_ = lean_array_get_borrowed(v___x_3650_, v_a_3661_, v___x_3651_);
v_type_3667_ = lean_ctor_get(v___x_3666_, 6);
lean_inc_ref(v_type_3667_);
v___x_3668_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0);
v___x_3669_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___boxed__const__1));
v___f_3670_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__2___boxed), 12, 6);
lean_closure_set(v___f_3670_, 0, v_a_3661_);
lean_closure_set(v___f_3670_, 1, v_perms_3665_);
lean_closure_set(v___f_3670_, 2, v___x_3669_);
lean_closure_set(v___f_3670_, 3, v_fnNames_3656_);
lean_closure_set(v___f_3670_, 4, v_a_3664_);
lean_closure_set(v___f_3670_, 5, v_termMeasure_x3fs_3644_);
v___x_3671_ = lean_array_get(v___x_3668_, v_perms_3665_, v___x_3651_);
lean_dec_ref(v_perms_3665_);
v___x_3672_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg(v___x_3671_, v_type_3667_, v___f_3670_, v_a_3645_, v_a_3646_, v_a_3647_, v_a_3648_);
return v___x_3672_;
}
else
{
lean_object* v_a_3673_; lean_object* v___x_3675_; uint8_t v_isShared_3676_; uint8_t v_isSharedCheck_3680_; 
lean_dec(v_a_3661_);
lean_dec_ref(v_fnNames_3656_);
lean_dec_ref(v_termMeasure_x3fs_3644_);
v_a_3673_ = lean_ctor_get(v___x_3663_, 0);
v_isSharedCheck_3680_ = !lean_is_exclusive(v___x_3663_);
if (v_isSharedCheck_3680_ == 0)
{
v___x_3675_ = v___x_3663_;
v_isShared_3676_ = v_isSharedCheck_3680_;
goto v_resetjp_3674_;
}
else
{
lean_inc(v_a_3673_);
lean_dec(v___x_3663_);
v___x_3675_ = lean_box(0);
v_isShared_3676_ = v_isSharedCheck_3680_;
goto v_resetjp_3674_;
}
v_resetjp_3674_:
{
lean_object* v___x_3678_; 
if (v_isShared_3676_ == 0)
{
v___x_3678_ = v___x_3675_;
goto v_reusejp_3677_;
}
else
{
lean_object* v_reuseFailAlloc_3679_; 
v_reuseFailAlloc_3679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3679_, 0, v_a_3673_);
v___x_3678_ = v_reuseFailAlloc_3679_;
goto v_reusejp_3677_;
}
v_reusejp_3677_:
{
return v___x_3678_;
}
}
}
}
else
{
lean_object* v_a_3681_; lean_object* v___x_3683_; uint8_t v_isShared_3684_; uint8_t v_isSharedCheck_3688_; 
lean_dec_ref(v_fnNames_3656_);
lean_dec_ref(v_termMeasure_x3fs_3644_);
v_a_3681_ = lean_ctor_get(v___x_3660_, 0);
v_isSharedCheck_3688_ = !lean_is_exclusive(v___x_3660_);
if (v_isSharedCheck_3688_ == 0)
{
v___x_3683_ = v___x_3660_;
v_isShared_3684_ = v_isSharedCheck_3688_;
goto v_resetjp_3682_;
}
else
{
lean_inc(v_a_3681_);
lean_dec(v___x_3660_);
v___x_3683_ = lean_box(0);
v_isShared_3684_ = v_isSharedCheck_3688_;
goto v_resetjp_3682_;
}
v_resetjp_3682_:
{
lean_object* v___x_3686_; 
if (v_isShared_3684_ == 0)
{
v___x_3686_ = v___x_3683_;
goto v_reusejp_3685_;
}
else
{
lean_object* v_reuseFailAlloc_3687_; 
v_reuseFailAlloc_3687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3687_, 0, v_a_3681_);
v___x_3686_ = v_reuseFailAlloc_3687_;
goto v_reusejp_3685_;
}
v_reusejp_3685_:
{
return v___x_3686_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___boxed(lean_object* v_preDefs_3689_, lean_object* v_termMeasure_x3fs_3690_, lean_object* v_a_3691_, lean_object* v_a_3692_, lean_object* v_a_3693_, lean_object* v_a_3694_, lean_object* v_a_3695_){
_start:
{
lean_object* v_res_3696_; 
v_res_3696_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos(v_preDefs_3689_, v_termMeasure_x3fs_3690_, v_a_3691_, v_a_3692_, v_a_3693_, v_a_3694_);
lean_dec(v_a_3694_);
lean_dec_ref(v_a_3693_);
lean_dec(v_a_3692_);
lean_dec_ref(v_a_3691_);
return v_res_3696_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4(lean_object* v_fst_3697_, lean_object* v_as_3698_, size_t v_sz_3699_, size_t v_i_3700_, lean_object* v_bs_3701_){
_start:
{
lean_object* v___x_3702_; 
v___x_3702_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg(v_fst_3697_, v_sz_3699_, v_i_3700_, v_bs_3701_);
return v___x_3702_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___boxed(lean_object* v_fst_3703_, lean_object* v_as_3704_, lean_object* v_sz_3705_, lean_object* v_i_3706_, lean_object* v_bs_3707_){
_start:
{
size_t v_sz_boxed_3708_; size_t v_i_boxed_3709_; lean_object* v_res_3710_; 
v_sz_boxed_3708_ = lean_unbox_usize(v_sz_3705_);
lean_dec(v_sz_3705_);
v_i_boxed_3709_ = lean_unbox_usize(v_i_3706_);
lean_dec(v_i_3706_);
v_res_3710_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4(v_fst_3703_, v_as_3704_, v_sz_boxed_3708_, v_i_boxed_3709_, v_bs_3707_);
lean_dec_ref(v_as_3704_);
lean_dec_ref(v_fst_3703_);
return v_res_3710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10(lean_object* v_00_u03b1_3711_, lean_object* v_lctx_3712_, lean_object* v_localInsts_3713_, lean_object* v_x_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_){
_start:
{
lean_object* v___x_3720_; 
v___x_3720_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___redArg(v_lctx_3712_, v_localInsts_3713_, v_x_3714_, v___y_3715_, v___y_3716_, v___y_3717_, v___y_3718_);
return v___x_3720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___boxed(lean_object* v_00_u03b1_3721_, lean_object* v_lctx_3722_, lean_object* v_localInsts_3723_, lean_object* v_x_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_){
_start:
{
lean_object* v_res_3730_; 
v_res_3730_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10(v_00_u03b1_3721_, v_lctx_3722_, v_localInsts_3723_, v_x_3724_, v___y_3725_, v___y_3726_, v___y_3727_, v___y_3728_);
lean_dec(v___y_3728_);
lean_dec_ref(v___y_3727_);
lean_dec(v___y_3726_);
lean_dec_ref(v___y_3725_);
return v_res_3730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9(lean_object* v_00_u03b1_3731_, lean_object* v_fvarIds_3732_, lean_object* v_k_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_){
_start:
{
lean_object* v___x_3739_; 
v___x_3739_ = l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___redArg(v_fvarIds_3732_, v_k_3733_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_);
return v___x_3739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___boxed(lean_object* v_00_u03b1_3740_, lean_object* v_fvarIds_3741_, lean_object* v_k_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_){
_start:
{
lean_object* v_res_3748_; 
v_res_3748_ = l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9(v_00_u03b1_3740_, v_fvarIds_3741_, v_k_3742_, v___y_3743_, v___y_3744_, v___y_3745_, v___y_3746_);
lean_dec(v___y_3746_);
lean_dec_ref(v___y_3745_);
lean_dec(v___y_3744_);
lean_dec_ref(v___y_3743_);
lean_dec_ref(v_fvarIds_3741_);
return v_res_3748_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__15(lean_object* v_a_3749_){
_start:
{
lean_object* v___x_3750_; 
v___x_3750_ = lean_nat_to_int(v_a_3749_);
return v___x_3750_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12(lean_object* v___x_3751_, lean_object* v_xs_3752_, lean_object* v_as_3753_, size_t v_sz_3754_, size_t v_i_3755_, lean_object* v_bs_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_){
_start:
{
lean_object* v___x_3762_; 
v___x_3762_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg(v___x_3751_, v_xs_3752_, v_sz_3754_, v_i_3755_, v_bs_3756_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_);
return v___x_3762_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___boxed(lean_object* v___x_3763_, lean_object* v_xs_3764_, lean_object* v_as_3765_, lean_object* v_sz_3766_, lean_object* v_i_3767_, lean_object* v_bs_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_){
_start:
{
size_t v_sz_boxed_3774_; size_t v_i_boxed_3775_; lean_object* v_res_3776_; 
v_sz_boxed_3774_ = lean_unbox_usize(v_sz_3766_);
lean_dec(v_sz_3766_);
v_i_boxed_3775_ = lean_unbox_usize(v_i_3767_);
lean_dec(v_i_3767_);
v_res_3776_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12(v___x_3763_, v_xs_3764_, v_as_3765_, v_sz_boxed_3774_, v_i_boxed_3775_, v_bs_3768_, v___y_3769_, v___y_3770_, v___y_3771_, v___y_3772_);
lean_dec(v___y_3772_);
lean_dec_ref(v___y_3771_);
lean_dec(v___y_3770_);
lean_dec_ref(v___y_3769_);
lean_dec_ref(v_as_3765_);
lean_dec_ref(v___x_3763_);
return v_res_3776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure___lam__0(lean_object* v___x_3777_, lean_object* v_recArgPos_3778_, lean_object* v_xs_3779_, lean_object* v_x_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_){
_start:
{
lean_object* v___x_3786_; uint8_t v___x_3787_; uint8_t v___x_3788_; uint8_t v___x_3789_; lean_object* v___x_3790_; 
v___x_3786_ = lean_array_get_borrowed(v___x_3777_, v_xs_3779_, v_recArgPos_3778_);
v___x_3787_ = 0;
v___x_3788_ = 1;
v___x_3789_ = 1;
lean_inc(v___x_3786_);
v___x_3790_ = l_Lean_Meta_mkLambdaFVars(v_xs_3779_, v___x_3786_, v___x_3787_, v___x_3788_, v___x_3787_, v___x_3788_, v___x_3789_, v___y_3781_, v___y_3782_, v___y_3783_, v___y_3784_);
return v___x_3790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure___lam__0___boxed(lean_object* v___x_3791_, lean_object* v_recArgPos_3792_, lean_object* v_xs_3793_, lean_object* v_x_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_){
_start:
{
lean_object* v_res_3800_; 
v_res_3800_ = l_Lean_Elab_Structural_reportTermMeasure___lam__0(v___x_3791_, v_recArgPos_3792_, v_xs_3793_, v_x_3794_, v___y_3795_, v___y_3796_, v___y_3797_, v___y_3798_);
lean_dec(v___y_3798_);
lean_dec_ref(v___y_3797_);
lean_dec(v___y_3796_);
lean_dec_ref(v___y_3795_);
lean_dec_ref(v_x_3794_);
lean_dec_ref(v_xs_3793_);
lean_dec(v_recArgPos_3792_);
lean_dec_ref(v___x_3791_);
return v_res_3800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure___lam__1(lean_object* v_xs_3801_, lean_object* v_x_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_){
_start:
{
lean_object* v___x_3808_; lean_object* v___x_3809_; 
v___x_3808_ = lean_array_get_size(v_xs_3801_);
v___x_3809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3809_, 0, v___x_3808_);
return v___x_3809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure___lam__1___boxed(lean_object* v_xs_3810_, lean_object* v_x_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_){
_start:
{
lean_object* v_res_3817_; 
v_res_3817_ = l_Lean_Elab_Structural_reportTermMeasure___lam__1(v_xs_3810_, v_x_3811_, v___y_3812_, v___y_3813_, v___y_3814_, v___y_3815_);
lean_dec(v___y_3815_);
lean_dec_ref(v___y_3814_);
lean_dec(v___y_3813_);
lean_dec_ref(v___y_3812_);
lean_dec_ref(v_x_3811_);
lean_dec_ref(v_xs_3810_);
return v_res_3817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure(lean_object* v_preDef_3829_, lean_object* v_recArgPos_3830_, lean_object* v_a_3831_, lean_object* v_a_3832_, lean_object* v_a_3833_, lean_object* v_a_3834_){
_start:
{
lean_object* v_termination_3836_; lean_object* v_terminationBy_x3f_x3f_3837_; 
v_termination_3836_ = lean_ctor_get(v_preDef_3829_, 8);
lean_inc_ref(v_termination_3836_);
v_terminationBy_x3f_x3f_3837_ = lean_ctor_get(v_termination_3836_, 1);
lean_inc(v_terminationBy_x3f_x3f_3837_);
if (lean_obj_tag(v_terminationBy_x3f_x3f_3837_) == 1)
{
lean_object* v_value_3838_; lean_object* v_extraParams_3839_; lean_object* v_val_3840_; lean_object* v___x_3841_; lean_object* v___f_3842_; uint8_t v___x_3843_; lean_object* v___x_3844_; 
v_value_3838_ = lean_ctor_get(v_preDef_3829_, 7);
lean_inc_ref_n(v_value_3838_, 2);
lean_dec_ref(v_preDef_3829_);
v_extraParams_3839_ = lean_ctor_get(v_termination_3836_, 5);
lean_inc(v_extraParams_3839_);
lean_dec_ref(v_termination_3836_);
v_val_3840_ = lean_ctor_get(v_terminationBy_x3f_x3f_3837_, 0);
lean_inc(v_val_3840_);
lean_dec_ref_known(v_terminationBy_x3f_x3f_3837_, 1);
v___x_3841_ = l_Lean_instInhabitedExpr;
v___f_3842_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_reportTermMeasure___lam__0___boxed), 9, 2);
lean_closure_set(v___f_3842_, 0, v___x_3841_);
lean_closure_set(v___f_3842_, 1, v_recArgPos_3830_);
v___x_3843_ = 0;
v___x_3844_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg(v_value_3838_, v___f_3842_, v___x_3843_, v_a_3831_, v_a_3832_, v_a_3833_, v_a_3834_);
if (lean_obj_tag(v___x_3844_) == 0)
{
lean_object* v_a_3845_; lean_object* v___f_3846_; lean_object* v___x_3847_; 
v_a_3845_ = lean_ctor_get(v___x_3844_, 0);
lean_inc(v_a_3845_);
lean_dec_ref_known(v___x_3844_, 1);
v___f_3846_ = ((lean_object*)(l_Lean_Elab_Structural_reportTermMeasure___closed__0));
v___x_3847_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg(v_value_3838_, v___f_3846_, v___x_3843_, v_a_3831_, v_a_3832_, v_a_3833_, v_a_3834_);
if (lean_obj_tag(v___x_3847_) == 0)
{
lean_object* v_a_3848_; lean_object* v___x_3849_; uint8_t v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; 
v_a_3848_ = lean_ctor_get(v___x_3847_, 0);
lean_inc(v_a_3848_);
lean_dec_ref_known(v___x_3847_, 1);
v___x_3849_ = lean_box(0);
v___x_3850_ = 1;
v___x_3851_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3851_, 0, v___x_3849_);
lean_ctor_set(v___x_3851_, 1, v_a_3845_);
lean_ctor_set_uint8(v___x_3851_, sizeof(void*)*2, v___x_3850_);
v___x_3852_ = l_Lean_Elab_TerminationMeasure_delab(v_a_3848_, v_extraParams_3839_, v___x_3851_, v_a_3831_, v_a_3832_, v_a_3833_, v_a_3834_);
lean_dec(v_a_3848_);
if (lean_obj_tag(v___x_3852_) == 0)
{
lean_object* v_a_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; uint8_t v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; 
v_a_3853_ = lean_ctor_get(v___x_3852_, 0);
lean_inc(v_a_3853_);
lean_dec_ref_known(v___x_3852_, 1);
v___x_3854_ = ((lean_object*)(l_Lean_Elab_Structural_reportTermMeasure___closed__5));
v___x_3855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3855_, 0, v___x_3854_);
lean_ctor_set(v___x_3855_, 1, v_a_3853_);
v___x_3856_ = lean_box(0);
v___x_3857_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3857_, 0, v___x_3855_);
lean_ctor_set(v___x_3857_, 1, v___x_3856_);
lean_ctor_set(v___x_3857_, 2, v___x_3856_);
lean_ctor_set(v___x_3857_, 3, v___x_3856_);
lean_ctor_set(v___x_3857_, 4, v___x_3856_);
lean_ctor_set(v___x_3857_, 5, v___x_3856_);
v___x_3858_ = ((lean_object*)(l_Lean_Elab_Structural_reportTermMeasure___closed__6));
v___x_3859_ = 4;
v___x_3860_ = l_Lean_MessageData_nil;
v___x_3861_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_val_3840_, v___x_3857_, v___x_3856_, v___x_3858_, v___x_3856_, v___x_3859_, v___x_3860_, v_a_3833_, v_a_3834_);
return v___x_3861_;
}
else
{
lean_object* v_a_3862_; lean_object* v___x_3864_; uint8_t v_isShared_3865_; uint8_t v_isSharedCheck_3869_; 
lean_dec(v_val_3840_);
v_a_3862_ = lean_ctor_get(v___x_3852_, 0);
v_isSharedCheck_3869_ = !lean_is_exclusive(v___x_3852_);
if (v_isSharedCheck_3869_ == 0)
{
v___x_3864_ = v___x_3852_;
v_isShared_3865_ = v_isSharedCheck_3869_;
goto v_resetjp_3863_;
}
else
{
lean_inc(v_a_3862_);
lean_dec(v___x_3852_);
v___x_3864_ = lean_box(0);
v_isShared_3865_ = v_isSharedCheck_3869_;
goto v_resetjp_3863_;
}
v_resetjp_3863_:
{
lean_object* v___x_3867_; 
if (v_isShared_3865_ == 0)
{
v___x_3867_ = v___x_3864_;
goto v_reusejp_3866_;
}
else
{
lean_object* v_reuseFailAlloc_3868_; 
v_reuseFailAlloc_3868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3868_, 0, v_a_3862_);
v___x_3867_ = v_reuseFailAlloc_3868_;
goto v_reusejp_3866_;
}
v_reusejp_3866_:
{
return v___x_3867_;
}
}
}
}
else
{
lean_object* v_a_3870_; lean_object* v___x_3872_; uint8_t v_isShared_3873_; uint8_t v_isSharedCheck_3877_; 
lean_dec(v_a_3845_);
lean_dec(v_val_3840_);
lean_dec(v_extraParams_3839_);
v_a_3870_ = lean_ctor_get(v___x_3847_, 0);
v_isSharedCheck_3877_ = !lean_is_exclusive(v___x_3847_);
if (v_isSharedCheck_3877_ == 0)
{
v___x_3872_ = v___x_3847_;
v_isShared_3873_ = v_isSharedCheck_3877_;
goto v_resetjp_3871_;
}
else
{
lean_inc(v_a_3870_);
lean_dec(v___x_3847_);
v___x_3872_ = lean_box(0);
v_isShared_3873_ = v_isSharedCheck_3877_;
goto v_resetjp_3871_;
}
v_resetjp_3871_:
{
lean_object* v___x_3875_; 
if (v_isShared_3873_ == 0)
{
v___x_3875_ = v___x_3872_;
goto v_reusejp_3874_;
}
else
{
lean_object* v_reuseFailAlloc_3876_; 
v_reuseFailAlloc_3876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3876_, 0, v_a_3870_);
v___x_3875_ = v_reuseFailAlloc_3876_;
goto v_reusejp_3874_;
}
v_reusejp_3874_:
{
return v___x_3875_;
}
}
}
}
else
{
lean_object* v_a_3878_; lean_object* v___x_3880_; uint8_t v_isShared_3881_; uint8_t v_isSharedCheck_3885_; 
lean_dec(v_val_3840_);
lean_dec(v_extraParams_3839_);
lean_dec_ref(v_value_3838_);
v_a_3878_ = lean_ctor_get(v___x_3844_, 0);
v_isSharedCheck_3885_ = !lean_is_exclusive(v___x_3844_);
if (v_isSharedCheck_3885_ == 0)
{
v___x_3880_ = v___x_3844_;
v_isShared_3881_ = v_isSharedCheck_3885_;
goto v_resetjp_3879_;
}
else
{
lean_inc(v_a_3878_);
lean_dec(v___x_3844_);
v___x_3880_ = lean_box(0);
v_isShared_3881_ = v_isSharedCheck_3885_;
goto v_resetjp_3879_;
}
v_resetjp_3879_:
{
lean_object* v___x_3883_; 
if (v_isShared_3881_ == 0)
{
v___x_3883_ = v___x_3880_;
goto v_reusejp_3882_;
}
else
{
lean_object* v_reuseFailAlloc_3884_; 
v_reuseFailAlloc_3884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3884_, 0, v_a_3878_);
v___x_3883_ = v_reuseFailAlloc_3884_;
goto v_reusejp_3882_;
}
v_reusejp_3882_:
{
return v___x_3883_;
}
}
}
}
else
{
lean_object* v___x_3886_; lean_object* v___x_3887_; 
lean_dec(v_terminationBy_x3f_x3f_3837_);
lean_dec_ref(v_termination_3836_);
lean_dec(v_recArgPos_3830_);
lean_dec_ref(v_preDef_3829_);
v___x_3886_ = lean_box(0);
v___x_3887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3887_, 0, v___x_3886_);
return v___x_3887_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure___boxed(lean_object* v_preDef_3888_, lean_object* v_recArgPos_3889_, lean_object* v_a_3890_, lean_object* v_a_3891_, lean_object* v_a_3892_, lean_object* v_a_3893_, lean_object* v_a_3894_){
_start:
{
lean_object* v_res_3895_; 
v_res_3895_ = l_Lean_Elab_Structural_reportTermMeasure(v_preDef_3888_, v_recArgPos_3889_, v_a_3890_, v_a_3891_, v_a_3892_, v_a_3893_);
lean_dec(v_a_3893_);
lean_dec_ref(v_a_3892_);
lean_dec(v_a_3891_);
lean_dec_ref(v_a_3890_);
return v_res_3895_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___redArg(lean_object* v_as_3896_, size_t v_sz_3897_, size_t v_i_3898_, lean_object* v_b_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_){
_start:
{
uint8_t v___x_3905_; 
v___x_3905_ = lean_usize_dec_lt(v_i_3898_, v_sz_3897_);
if (v___x_3905_ == 0)
{
lean_object* v___x_3906_; 
v___x_3906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3906_, 0, v_b_3899_);
return v___x_3906_;
}
else
{
lean_object* v_a_3907_; lean_object* v_declName_3908_; lean_object* v___x_3909_; 
v_a_3907_ = lean_array_uget_borrowed(v_as_3896_, v_i_3898_);
v_declName_3908_ = lean_ctor_get(v_a_3907_, 3);
lean_inc(v_declName_3908_);
v___x_3909_ = l_Lean_Meta_saveEqnAffectingOptions(v_declName_3908_, v___y_3900_, v___y_3901_, v___y_3902_, v___y_3903_);
if (lean_obj_tag(v___x_3909_) == 0)
{
lean_object* v___x_3910_; size_t v___x_3911_; size_t v___x_3912_; 
lean_dec_ref_known(v___x_3909_, 1);
v___x_3910_ = lean_box(0);
v___x_3911_ = ((size_t)1ULL);
v___x_3912_ = lean_usize_add(v_i_3898_, v___x_3911_);
v_i_3898_ = v___x_3912_;
v_b_3899_ = v___x_3910_;
goto _start;
}
else
{
return v___x_3909_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___redArg___boxed(lean_object* v_as_3914_, lean_object* v_sz_3915_, lean_object* v_i_3916_, lean_object* v_b_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_){
_start:
{
size_t v_sz_boxed_3923_; size_t v_i_boxed_3924_; lean_object* v_res_3925_; 
v_sz_boxed_3923_ = lean_unbox_usize(v_sz_3915_);
lean_dec(v_sz_3915_);
v_i_boxed_3924_ = lean_unbox_usize(v_i_3916_);
lean_dec(v_i_3916_);
v_res_3925_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___redArg(v_as_3914_, v_sz_boxed_3923_, v_i_boxed_3924_, v_b_3917_, v___y_3918_, v___y_3919_, v___y_3920_, v___y_3921_);
lean_dec(v___y_3921_);
lean_dec_ref(v___y_3920_);
lean_dec(v___y_3919_);
lean_dec_ref(v___y_3918_);
lean_dec_ref(v_as_3914_);
return v_res_3925_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__1(lean_object* v_docCtx_3926_, lean_object* v_a_3927_, lean_object* v_snd_3928_, lean_object* v_as_3929_, size_t v_sz_3930_, size_t v_i_3931_, lean_object* v_b_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_){
_start:
{
uint8_t v___x_3940_; 
v___x_3940_ = lean_usize_dec_lt(v_i_3931_, v_sz_3930_);
if (v___x_3940_ == 0)
{
lean_object* v___x_3941_; 
lean_dec_ref(v_snd_3928_);
lean_dec_ref(v_a_3927_);
lean_dec_ref(v_docCtx_3926_);
v___x_3941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3941_, 0, v_b_3932_);
return v___x_3941_;
}
else
{
lean_object* v_array_3942_; lean_object* v_start_3943_; lean_object* v_stop_3944_; uint8_t v___x_3945_; 
v_array_3942_ = lean_ctor_get(v_b_3932_, 0);
v_start_3943_ = lean_ctor_get(v_b_3932_, 1);
v_stop_3944_ = lean_ctor_get(v_b_3932_, 2);
v___x_3945_ = lean_nat_dec_lt(v_start_3943_, v_stop_3944_);
if (v___x_3945_ == 0)
{
lean_object* v___x_3946_; 
lean_dec_ref(v_snd_3928_);
lean_dec_ref(v_a_3927_);
lean_dec_ref(v_docCtx_3926_);
v___x_3946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3946_, 0, v_b_3932_);
return v___x_3946_;
}
else
{
lean_object* v___x_3948_; uint8_t v_isShared_3949_; uint8_t v_isSharedCheck_4013_; 
lean_inc(v_stop_3944_);
lean_inc(v_start_3943_);
lean_inc_ref(v_array_3942_);
v_isSharedCheck_4013_ = !lean_is_exclusive(v_b_3932_);
if (v_isSharedCheck_4013_ == 0)
{
lean_object* v_unused_4014_; lean_object* v_unused_4015_; lean_object* v_unused_4016_; 
v_unused_4014_ = lean_ctor_get(v_b_3932_, 2);
lean_dec(v_unused_4014_);
v_unused_4015_ = lean_ctor_get(v_b_3932_, 1);
lean_dec(v_unused_4015_);
v_unused_4016_ = lean_ctor_get(v_b_3932_, 0);
lean_dec(v_unused_4016_);
v___x_3948_ = v_b_3932_;
v_isShared_3949_ = v_isSharedCheck_4013_;
goto v_resetjp_3947_;
}
else
{
lean_dec(v_b_3932_);
v___x_3948_ = lean_box(0);
v_isShared_3949_ = v_isSharedCheck_4013_;
goto v_resetjp_3947_;
}
v_resetjp_3947_:
{
lean_object* v_a_3950_; uint8_t v_kind_3951_; lean_object* v_type_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3957_; 
v_a_3950_ = lean_array_uget_borrowed(v_as_3929_, v_i_3931_);
v_kind_3951_ = lean_ctor_get_uint8(v_a_3950_, sizeof(void*)*9);
v_type_3952_ = lean_ctor_get(v_a_3950_, 6);
v___x_3953_ = lean_array_fget(v_array_3942_, v_start_3943_);
v___x_3954_ = lean_unsigned_to_nat(1u);
v___x_3955_ = lean_nat_add(v_start_3943_, v___x_3954_);
lean_dec(v_start_3943_);
if (v_isShared_3949_ == 0)
{
lean_ctor_set(v___x_3948_, 1, v___x_3955_);
v___x_3957_ = v___x_3948_;
goto v_reusejp_3956_;
}
else
{
lean_object* v_reuseFailAlloc_4012_; 
v_reuseFailAlloc_4012_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4012_, 0, v_array_3942_);
lean_ctor_set(v_reuseFailAlloc_4012_, 1, v___x_3955_);
lean_ctor_set(v_reuseFailAlloc_4012_, 2, v_stop_3944_);
v___x_3957_ = v_reuseFailAlloc_4012_;
goto v_reusejp_3956_;
}
v_reusejp_3956_:
{
lean_object* v_preDef_3959_; lean_object* v___y_3960_; lean_object* v___y_3961_; lean_object* v___y_3962_; lean_object* v___y_3963_; lean_object* v___y_3964_; lean_object* v___y_3965_; uint8_t v___x_3978_; 
v___x_3978_ = l_Lean_Elab_DefKind_isTheorem(v_kind_3951_);
if (v___x_3978_ == 0)
{
lean_object* v___x_3979_; 
lean_inc_ref(v_type_3952_);
v___x_3979_ = l_Lean_Meta_isProp(v_type_3952_, v___y_3935_, v___y_3936_, v___y_3937_, v___y_3938_);
if (lean_obj_tag(v___x_3979_) == 0)
{
lean_object* v_a_3980_; uint8_t v___x_3981_; 
v_a_3980_ = lean_ctor_get(v___x_3979_, 0);
lean_inc(v_a_3980_);
lean_dec_ref_known(v___x_3979_, 1);
v___x_3981_ = lean_unbox(v_a_3980_);
lean_dec(v_a_3980_);
if (v___x_3981_ == 0)
{
lean_object* v___x_3982_; 
lean_inc(v_a_3950_);
v___x_3982_ = l_Lean_Elab_abstractNestedProofs(v_a_3950_, v___x_3945_, v___y_3935_, v___y_3936_, v___y_3937_, v___y_3938_);
if (lean_obj_tag(v___x_3982_) == 0)
{
lean_object* v_a_3983_; size_t v_sz_3984_; size_t v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; 
v_a_3983_ = lean_ctor_get(v___x_3982_, 0);
lean_inc_n(v_a_3983_, 2);
lean_dec_ref_known(v___x_3982_, 1);
v_sz_3984_ = lean_array_size(v_a_3927_);
v___x_3985_ = ((size_t)0ULL);
lean_inc_ref(v_a_3927_);
v___x_3986_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0(v_sz_3984_, v___x_3985_, v_a_3927_);
lean_inc_ref(v_snd_3928_);
lean_inc(v___x_3953_);
v___x_3987_ = l_Lean_Elab_Structural_registerEqnsInfo(v_a_3983_, v___x_3986_, v___x_3953_, v_snd_3928_, v___y_3937_, v___y_3938_);
if (lean_obj_tag(v___x_3987_) == 0)
{
lean_dec_ref_known(v___x_3987_, 1);
v_preDef_3959_ = v_a_3983_;
v___y_3960_ = v___y_3933_;
v___y_3961_ = v___y_3934_;
v___y_3962_ = v___y_3935_;
v___y_3963_ = v___y_3936_;
v___y_3964_ = v___y_3937_;
v___y_3965_ = v___y_3938_;
goto v___jp_3958_;
}
else
{
lean_object* v_a_3988_; lean_object* v___x_3990_; uint8_t v_isShared_3991_; uint8_t v_isSharedCheck_3995_; 
lean_dec(v_a_3983_);
lean_dec_ref(v___x_3957_);
lean_dec(v___x_3953_);
lean_dec_ref(v_snd_3928_);
lean_dec_ref(v_a_3927_);
lean_dec_ref(v_docCtx_3926_);
v_a_3988_ = lean_ctor_get(v___x_3987_, 0);
v_isSharedCheck_3995_ = !lean_is_exclusive(v___x_3987_);
if (v_isSharedCheck_3995_ == 0)
{
v___x_3990_ = v___x_3987_;
v_isShared_3991_ = v_isSharedCheck_3995_;
goto v_resetjp_3989_;
}
else
{
lean_inc(v_a_3988_);
lean_dec(v___x_3987_);
v___x_3990_ = lean_box(0);
v_isShared_3991_ = v_isSharedCheck_3995_;
goto v_resetjp_3989_;
}
v_resetjp_3989_:
{
lean_object* v___x_3993_; 
if (v_isShared_3991_ == 0)
{
v___x_3993_ = v___x_3990_;
goto v_reusejp_3992_;
}
else
{
lean_object* v_reuseFailAlloc_3994_; 
v_reuseFailAlloc_3994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3994_, 0, v_a_3988_);
v___x_3993_ = v_reuseFailAlloc_3994_;
goto v_reusejp_3992_;
}
v_reusejp_3992_:
{
return v___x_3993_;
}
}
}
}
else
{
lean_object* v_a_3996_; lean_object* v___x_3998_; uint8_t v_isShared_3999_; uint8_t v_isSharedCheck_4003_; 
lean_dec_ref(v___x_3957_);
lean_dec(v___x_3953_);
lean_dec_ref(v_snd_3928_);
lean_dec_ref(v_a_3927_);
lean_dec_ref(v_docCtx_3926_);
v_a_3996_ = lean_ctor_get(v___x_3982_, 0);
v_isSharedCheck_4003_ = !lean_is_exclusive(v___x_3982_);
if (v_isSharedCheck_4003_ == 0)
{
v___x_3998_ = v___x_3982_;
v_isShared_3999_ = v_isSharedCheck_4003_;
goto v_resetjp_3997_;
}
else
{
lean_inc(v_a_3996_);
lean_dec(v___x_3982_);
v___x_3998_ = lean_box(0);
v_isShared_3999_ = v_isSharedCheck_4003_;
goto v_resetjp_3997_;
}
v_resetjp_3997_:
{
lean_object* v___x_4001_; 
if (v_isShared_3999_ == 0)
{
v___x_4001_ = v___x_3998_;
goto v_reusejp_4000_;
}
else
{
lean_object* v_reuseFailAlloc_4002_; 
v_reuseFailAlloc_4002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4002_, 0, v_a_3996_);
v___x_4001_ = v_reuseFailAlloc_4002_;
goto v_reusejp_4000_;
}
v_reusejp_4000_:
{
return v___x_4001_;
}
}
}
}
else
{
lean_inc(v_a_3950_);
v_preDef_3959_ = v_a_3950_;
v___y_3960_ = v___y_3933_;
v___y_3961_ = v___y_3934_;
v___y_3962_ = v___y_3935_;
v___y_3963_ = v___y_3936_;
v___y_3964_ = v___y_3937_;
v___y_3965_ = v___y_3938_;
goto v___jp_3958_;
}
}
else
{
lean_object* v_a_4004_; lean_object* v___x_4006_; uint8_t v_isShared_4007_; uint8_t v_isSharedCheck_4011_; 
lean_dec_ref(v___x_3957_);
lean_dec(v___x_3953_);
lean_dec_ref(v_snd_3928_);
lean_dec_ref(v_a_3927_);
lean_dec_ref(v_docCtx_3926_);
v_a_4004_ = lean_ctor_get(v___x_3979_, 0);
v_isSharedCheck_4011_ = !lean_is_exclusive(v___x_3979_);
if (v_isSharedCheck_4011_ == 0)
{
v___x_4006_ = v___x_3979_;
v_isShared_4007_ = v_isSharedCheck_4011_;
goto v_resetjp_4005_;
}
else
{
lean_inc(v_a_4004_);
lean_dec(v___x_3979_);
v___x_4006_ = lean_box(0);
v_isShared_4007_ = v_isSharedCheck_4011_;
goto v_resetjp_4005_;
}
v_resetjp_4005_:
{
lean_object* v___x_4009_; 
if (v_isShared_4007_ == 0)
{
v___x_4009_ = v___x_4006_;
goto v_reusejp_4008_;
}
else
{
lean_object* v_reuseFailAlloc_4010_; 
v_reuseFailAlloc_4010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4010_, 0, v_a_4004_);
v___x_4009_ = v_reuseFailAlloc_4010_;
goto v_reusejp_4008_;
}
v_reusejp_4008_:
{
return v___x_4009_;
}
}
}
}
else
{
lean_inc(v_a_3950_);
v_preDef_3959_ = v_a_3950_;
v___y_3960_ = v___y_3933_;
v___y_3961_ = v___y_3934_;
v___y_3962_ = v___y_3935_;
v___y_3963_ = v___y_3936_;
v___y_3964_ = v___y_3937_;
v___y_3965_ = v___y_3938_;
goto v___jp_3958_;
}
v___jp_3958_:
{
lean_object* v___x_3966_; 
lean_inc_ref(v_docCtx_3926_);
v___x_3966_ = l_Lean_Elab_Structural_addSmartUnfoldingDef(v_docCtx_3926_, v_preDef_3959_, v___x_3953_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_, v___y_3965_);
if (lean_obj_tag(v___x_3966_) == 0)
{
size_t v___x_3967_; size_t v___x_3968_; 
lean_dec_ref_known(v___x_3966_, 1);
v___x_3967_ = ((size_t)1ULL);
v___x_3968_ = lean_usize_add(v_i_3931_, v___x_3967_);
v_i_3931_ = v___x_3968_;
v_b_3932_ = v___x_3957_;
goto _start;
}
else
{
lean_object* v_a_3970_; lean_object* v___x_3972_; uint8_t v_isShared_3973_; uint8_t v_isSharedCheck_3977_; 
lean_dec_ref(v___x_3957_);
lean_dec_ref(v_snd_3928_);
lean_dec_ref(v_a_3927_);
lean_dec_ref(v_docCtx_3926_);
v_a_3970_ = lean_ctor_get(v___x_3966_, 0);
v_isSharedCheck_3977_ = !lean_is_exclusive(v___x_3966_);
if (v_isSharedCheck_3977_ == 0)
{
v___x_3972_ = v___x_3966_;
v_isShared_3973_ = v_isSharedCheck_3977_;
goto v_resetjp_3971_;
}
else
{
lean_inc(v_a_3970_);
lean_dec(v___x_3966_);
v___x_3972_ = lean_box(0);
v_isShared_3973_ = v_isSharedCheck_3977_;
goto v_resetjp_3971_;
}
v_resetjp_3971_:
{
lean_object* v___x_3975_; 
if (v_isShared_3973_ == 0)
{
v___x_3975_ = v___x_3972_;
goto v_reusejp_3974_;
}
else
{
lean_object* v_reuseFailAlloc_3976_; 
v_reuseFailAlloc_3976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3976_, 0, v_a_3970_);
v___x_3975_ = v_reuseFailAlloc_3976_;
goto v_reusejp_3974_;
}
v_reusejp_3974_:
{
return v___x_3975_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__1___boxed(lean_object* v_docCtx_4017_, lean_object* v_a_4018_, lean_object* v_snd_4019_, lean_object* v_as_4020_, lean_object* v_sz_4021_, lean_object* v_i_4022_, lean_object* v_b_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_){
_start:
{
size_t v_sz_boxed_4031_; size_t v_i_boxed_4032_; lean_object* v_res_4033_; 
v_sz_boxed_4031_ = lean_unbox_usize(v_sz_4021_);
lean_dec(v_sz_4021_);
v_i_boxed_4032_ = lean_unbox_usize(v_i_4022_);
lean_dec(v_i_4022_);
v_res_4033_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__1(v_docCtx_4017_, v_a_4018_, v_snd_4019_, v_as_4020_, v_sz_boxed_4031_, v_i_boxed_4032_, v_b_4023_, v___y_4024_, v___y_4025_, v___y_4026_, v___y_4027_, v___y_4028_, v___y_4029_);
lean_dec(v___y_4029_);
lean_dec_ref(v___y_4028_);
lean_dec(v___y_4027_);
lean_dec_ref(v___y_4026_);
lean_dec(v___y_4025_);
lean_dec_ref(v___y_4024_);
lean_dec_ref(v_as_4020_);
return v_res_4033_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___lam__0(lean_object* v___x_4034_, lean_object* v_e_4035_){
_start:
{
lean_object* v___x_4036_; lean_object* v___x_4037_; 
v___x_4036_ = l_Lean_indentD(v_e_4035_);
v___x_4037_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4037_, 0, v___x_4034_);
lean_ctor_set(v___x_4037_, 1, v___x_4036_);
return v___x_4037_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___lam__1(lean_object* v_docCtx_4038_, lean_object* v_a_4039_, uint8_t v___x_4040_, lean_object* v___x_4041_, uint8_t v___x_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_){
_start:
{
lean_object* v___x_4050_; 
v___x_4050_ = l_Lean_Elab_addNonRec(v_docCtx_4038_, v_a_4039_, v___x_4040_, v___x_4041_, v___x_4042_, v___x_4040_, v___x_4042_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_, v___y_4048_);
return v___x_4050_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___lam__1___boxed(lean_object* v_docCtx_4051_, lean_object* v_a_4052_, lean_object* v___x_4053_, lean_object* v___x_4054_, lean_object* v___x_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_){
_start:
{
uint8_t v___x_9188__boxed_4063_; uint8_t v___x_9190__boxed_4064_; lean_object* v_res_4065_; 
v___x_9188__boxed_4063_ = lean_unbox(v___x_4053_);
v___x_9190__boxed_4064_ = lean_unbox(v___x_4055_);
v_res_4065_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___lam__1(v_docCtx_4051_, v_a_4052_, v___x_9188__boxed_4063_, v___x_4054_, v___x_9190__boxed_4064_, v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_);
lean_dec(v___y_4061_);
lean_dec_ref(v___y_4060_);
lean_dec(v___y_4059_);
lean_dec_ref(v___y_4058_);
lean_dec(v___y_4057_);
lean_dec_ref(v___y_4056_);
return v_res_4065_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__1(void){
_start:
{
lean_object* v___x_4067_; lean_object* v___x_4068_; 
v___x_4067_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__0));
v___x_4068_ = l_Lean_stringToMessageData(v___x_4067_);
return v___x_4068_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__2(void){
_start:
{
lean_object* v___x_4069_; lean_object* v___f_4070_; 
v___x_4069_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__1);
v___f_4070_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___lam__0), 2, 1);
lean_closure_set(v___f_4070_, 0, v___x_4069_);
return v___f_4070_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5(lean_object* v_names_4071_, lean_object* v_docCtx_4072_, lean_object* v_as_4073_, size_t v_i_4074_, size_t v_stop_4075_, lean_object* v_b_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_){
_start:
{
uint8_t v___x_4084_; 
v___x_4084_ = lean_usize_dec_eq(v_i_4074_, v_stop_4075_);
if (v___x_4084_ == 0)
{
lean_object* v___x_4085_; lean_object* v___x_4086_; 
v___x_4085_ = lean_array_uget_borrowed(v_as_4073_, v_i_4074_);
lean_inc(v___x_4085_);
v___x_4086_ = l_Lean_Elab_eraseRecAppSyntax(v___x_4085_, v___y_4081_, v___y_4082_);
if (lean_obj_tag(v___x_4086_) == 0)
{
lean_object* v_a_4087_; lean_object* v___f_4088_; lean_object* v___x_4089_; uint8_t v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___f_4093_; lean_object* v___x_4094_; 
v_a_4087_ = lean_ctor_get(v___x_4086_, 0);
lean_inc(v_a_4087_);
lean_dec_ref_known(v___x_4086_, 1);
v___f_4088_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__2);
lean_inc_ref(v_names_4071_);
v___x_4089_ = lean_array_to_list(v_names_4071_);
v___x_4090_ = 1;
v___x_4091_ = lean_box(v___x_4084_);
v___x_4092_ = lean_box(v___x_4090_);
lean_inc(v___y_4078_);
lean_inc_ref(v___y_4077_);
lean_inc_ref(v_docCtx_4072_);
v___f_4093_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___lam__1___boxed), 12, 7);
lean_closure_set(v___f_4093_, 0, v_docCtx_4072_);
lean_closure_set(v___f_4093_, 1, v_a_4087_);
lean_closure_set(v___f_4093_, 2, v___x_4091_);
lean_closure_set(v___f_4093_, 3, v___x_4089_);
lean_closure_set(v___f_4093_, 4, v___x_4092_);
lean_closure_set(v___f_4093_, 5, v___y_4077_);
lean_closure_set(v___f_4093_, 6, v___y_4078_);
v___x_4094_ = l_Lean_Meta_mapErrorImp___redArg(v___f_4093_, v___f_4088_, v___y_4079_, v___y_4080_, v___y_4081_, v___y_4082_);
if (lean_obj_tag(v___x_4094_) == 0)
{
if (lean_obj_tag(v___x_4094_) == 0)
{
lean_object* v_a_4095_; size_t v___x_4096_; size_t v___x_4097_; 
v_a_4095_ = lean_ctor_get(v___x_4094_, 0);
lean_inc(v_a_4095_);
lean_dec_ref_known(v___x_4094_, 1);
v___x_4096_ = ((size_t)1ULL);
v___x_4097_ = lean_usize_add(v_i_4074_, v___x_4096_);
v_i_4074_ = v___x_4097_;
v_b_4076_ = v_a_4095_;
goto _start;
}
else
{
lean_dec_ref(v_docCtx_4072_);
lean_dec_ref(v_names_4071_);
return v___x_4094_;
}
}
else
{
lean_object* v_a_4099_; lean_object* v___x_4101_; uint8_t v_isShared_4102_; uint8_t v_isSharedCheck_4106_; 
lean_dec_ref(v_docCtx_4072_);
lean_dec_ref(v_names_4071_);
v_a_4099_ = lean_ctor_get(v___x_4094_, 0);
v_isSharedCheck_4106_ = !lean_is_exclusive(v___x_4094_);
if (v_isSharedCheck_4106_ == 0)
{
v___x_4101_ = v___x_4094_;
v_isShared_4102_ = v_isSharedCheck_4106_;
goto v_resetjp_4100_;
}
else
{
lean_inc(v_a_4099_);
lean_dec(v___x_4094_);
v___x_4101_ = lean_box(0);
v_isShared_4102_ = v_isSharedCheck_4106_;
goto v_resetjp_4100_;
}
v_resetjp_4100_:
{
lean_object* v___x_4104_; 
if (v_isShared_4102_ == 0)
{
v___x_4104_ = v___x_4101_;
goto v_reusejp_4103_;
}
else
{
lean_object* v_reuseFailAlloc_4105_; 
v_reuseFailAlloc_4105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4105_, 0, v_a_4099_);
v___x_4104_ = v_reuseFailAlloc_4105_;
goto v_reusejp_4103_;
}
v_reusejp_4103_:
{
return v___x_4104_;
}
}
}
}
else
{
lean_object* v_a_4107_; lean_object* v___x_4109_; uint8_t v_isShared_4110_; uint8_t v_isSharedCheck_4114_; 
lean_dec_ref(v_docCtx_4072_);
lean_dec_ref(v_names_4071_);
v_a_4107_ = lean_ctor_get(v___x_4086_, 0);
v_isSharedCheck_4114_ = !lean_is_exclusive(v___x_4086_);
if (v_isSharedCheck_4114_ == 0)
{
v___x_4109_ = v___x_4086_;
v_isShared_4110_ = v_isSharedCheck_4114_;
goto v_resetjp_4108_;
}
else
{
lean_inc(v_a_4107_);
lean_dec(v___x_4086_);
v___x_4109_ = lean_box(0);
v_isShared_4110_ = v_isSharedCheck_4114_;
goto v_resetjp_4108_;
}
v_resetjp_4108_:
{
lean_object* v___x_4112_; 
if (v_isShared_4110_ == 0)
{
v___x_4112_ = v___x_4109_;
goto v_reusejp_4111_;
}
else
{
lean_object* v_reuseFailAlloc_4113_; 
v_reuseFailAlloc_4113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4113_, 0, v_a_4107_);
v___x_4112_ = v_reuseFailAlloc_4113_;
goto v_reusejp_4111_;
}
v_reusejp_4111_:
{
return v___x_4112_;
}
}
}
}
else
{
lean_object* v___x_4115_; 
lean_dec_ref(v_docCtx_4072_);
lean_dec_ref(v_names_4071_);
v___x_4115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4115_, 0, v_b_4076_);
return v___x_4115_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___boxed(lean_object* v_names_4116_, lean_object* v_docCtx_4117_, lean_object* v_as_4118_, lean_object* v_i_4119_, lean_object* v_stop_4120_, lean_object* v_b_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_){
_start:
{
size_t v_i_boxed_4129_; size_t v_stop_boxed_4130_; lean_object* v_res_4131_; 
v_i_boxed_4129_ = lean_unbox_usize(v_i_4119_);
lean_dec(v_i_4119_);
v_stop_boxed_4130_ = lean_unbox_usize(v_stop_4120_);
lean_dec(v_stop_4120_);
v_res_4131_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5(v_names_4116_, v_docCtx_4117_, v_as_4118_, v_i_boxed_4129_, v_stop_boxed_4130_, v_b_4121_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_);
lean_dec(v___y_4127_);
lean_dec_ref(v___y_4126_);
lean_dec(v___y_4125_);
lean_dec_ref(v___y_4124_);
lean_dec(v___y_4123_);
lean_dec_ref(v___y_4122_);
lean_dec_ref(v_as_4118_);
return v_res_4131_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4___redArg(lean_object* v_as_4132_, size_t v_sz_4133_, size_t v_i_4134_, lean_object* v_b_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_){
_start:
{
uint8_t v___x_4141_; 
v___x_4141_ = lean_usize_dec_lt(v_i_4134_, v_sz_4133_);
if (v___x_4141_ == 0)
{
lean_object* v___x_4142_; 
v___x_4142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4142_, 0, v_b_4135_);
return v___x_4142_;
}
else
{
lean_object* v_array_4143_; lean_object* v_start_4144_; lean_object* v_stop_4145_; uint8_t v___x_4146_; 
v_array_4143_ = lean_ctor_get(v_b_4135_, 0);
v_start_4144_ = lean_ctor_get(v_b_4135_, 1);
v_stop_4145_ = lean_ctor_get(v_b_4135_, 2);
v___x_4146_ = lean_nat_dec_lt(v_start_4144_, v_stop_4145_);
if (v___x_4146_ == 0)
{
lean_object* v___x_4147_; 
v___x_4147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4147_, 0, v_b_4135_);
return v___x_4147_;
}
else
{
lean_object* v___x_4149_; uint8_t v_isShared_4150_; uint8_t v_isSharedCheck_4170_; 
lean_inc(v_stop_4145_);
lean_inc(v_start_4144_);
lean_inc_ref(v_array_4143_);
v_isSharedCheck_4170_ = !lean_is_exclusive(v_b_4135_);
if (v_isSharedCheck_4170_ == 0)
{
lean_object* v_unused_4171_; lean_object* v_unused_4172_; lean_object* v_unused_4173_; 
v_unused_4171_ = lean_ctor_get(v_b_4135_, 2);
lean_dec(v_unused_4171_);
v_unused_4172_ = lean_ctor_get(v_b_4135_, 1);
lean_dec(v_unused_4172_);
v_unused_4173_ = lean_ctor_get(v_b_4135_, 0);
lean_dec(v_unused_4173_);
v___x_4149_ = v_b_4135_;
v_isShared_4150_ = v_isSharedCheck_4170_;
goto v_resetjp_4148_;
}
else
{
lean_dec(v_b_4135_);
v___x_4149_ = lean_box(0);
v_isShared_4150_ = v_isSharedCheck_4170_;
goto v_resetjp_4148_;
}
v_resetjp_4148_:
{
lean_object* v_a_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; 
v_a_4151_ = lean_array_uget_borrowed(v_as_4132_, v_i_4134_);
v___x_4152_ = lean_array_fget_borrowed(v_array_4143_, v_start_4144_);
lean_inc(v_a_4151_);
lean_inc(v___x_4152_);
v___x_4153_ = l_Lean_Elab_Structural_reportTermMeasure(v___x_4152_, v_a_4151_, v___y_4136_, v___y_4137_, v___y_4138_, v___y_4139_);
if (lean_obj_tag(v___x_4153_) == 0)
{
lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4157_; 
lean_dec_ref_known(v___x_4153_, 1);
v___x_4154_ = lean_unsigned_to_nat(1u);
v___x_4155_ = lean_nat_add(v_start_4144_, v___x_4154_);
lean_dec(v_start_4144_);
if (v_isShared_4150_ == 0)
{
lean_ctor_set(v___x_4149_, 1, v___x_4155_);
v___x_4157_ = v___x_4149_;
goto v_reusejp_4156_;
}
else
{
lean_object* v_reuseFailAlloc_4161_; 
v_reuseFailAlloc_4161_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4161_, 0, v_array_4143_);
lean_ctor_set(v_reuseFailAlloc_4161_, 1, v___x_4155_);
lean_ctor_set(v_reuseFailAlloc_4161_, 2, v_stop_4145_);
v___x_4157_ = v_reuseFailAlloc_4161_;
goto v_reusejp_4156_;
}
v_reusejp_4156_:
{
size_t v___x_4158_; size_t v___x_4159_; 
v___x_4158_ = ((size_t)1ULL);
v___x_4159_ = lean_usize_add(v_i_4134_, v___x_4158_);
v_i_4134_ = v___x_4159_;
v_b_4135_ = v___x_4157_;
goto _start;
}
}
else
{
lean_object* v_a_4162_; lean_object* v___x_4164_; uint8_t v_isShared_4165_; uint8_t v_isSharedCheck_4169_; 
lean_del_object(v___x_4149_);
lean_dec(v_stop_4145_);
lean_dec(v_start_4144_);
lean_dec_ref(v_array_4143_);
v_a_4162_ = lean_ctor_get(v___x_4153_, 0);
v_isSharedCheck_4169_ = !lean_is_exclusive(v___x_4153_);
if (v_isSharedCheck_4169_ == 0)
{
v___x_4164_ = v___x_4153_;
v_isShared_4165_ = v_isSharedCheck_4169_;
goto v_resetjp_4163_;
}
else
{
lean_inc(v_a_4162_);
lean_dec(v___x_4153_);
v___x_4164_ = lean_box(0);
v_isShared_4165_ = v_isSharedCheck_4169_;
goto v_resetjp_4163_;
}
v_resetjp_4163_:
{
lean_object* v___x_4167_; 
if (v_isShared_4165_ == 0)
{
v___x_4167_ = v___x_4164_;
goto v_reusejp_4166_;
}
else
{
lean_object* v_reuseFailAlloc_4168_; 
v_reuseFailAlloc_4168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4168_, 0, v_a_4162_);
v___x_4167_ = v_reuseFailAlloc_4168_;
goto v_reusejp_4166_;
}
v_reusejp_4166_:
{
return v___x_4167_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4___redArg___boxed(lean_object* v_as_4174_, lean_object* v_sz_4175_, lean_object* v_i_4176_, lean_object* v_b_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_, lean_object* v___y_4182_){
_start:
{
size_t v_sz_boxed_4183_; size_t v_i_boxed_4184_; lean_object* v_res_4185_; 
v_sz_boxed_4183_ = lean_unbox_usize(v_sz_4175_);
lean_dec(v_sz_4175_);
v_i_boxed_4184_ = lean_unbox_usize(v_i_4176_);
lean_dec(v_i_4176_);
v_res_4185_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4___redArg(v_as_4174_, v_sz_boxed_4183_, v_i_boxed_4184_, v_b_4177_, v___y_4178_, v___y_4179_, v___y_4180_, v___y_4181_);
lean_dec(v___y_4181_);
lean_dec_ref(v___y_4180_);
lean_dec(v___y_4179_);
lean_dec_ref(v___y_4178_);
lean_dec_ref(v_as_4174_);
return v_res_4185_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___redArg(size_t v_sz_4186_, size_t v_i_4187_, lean_object* v_bs_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_){
_start:
{
uint8_t v___x_4192_; 
v___x_4192_ = lean_usize_dec_lt(v_i_4187_, v_sz_4186_);
if (v___x_4192_ == 0)
{
lean_object* v___x_4193_; 
v___x_4193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4193_, 0, v_bs_4188_);
return v___x_4193_;
}
else
{
lean_object* v_v_4194_; lean_object* v___x_4195_; 
v_v_4194_ = lean_array_uget_borrowed(v_bs_4188_, v_i_4187_);
lean_inc(v_v_4194_);
v___x_4195_ = l_Lean_Elab_eraseRecAppSyntax(v_v_4194_, v___y_4189_, v___y_4190_);
if (lean_obj_tag(v___x_4195_) == 0)
{
lean_object* v_a_4196_; lean_object* v___x_4197_; lean_object* v_bs_x27_4198_; size_t v___x_4199_; size_t v___x_4200_; lean_object* v___x_4201_; 
v_a_4196_ = lean_ctor_get(v___x_4195_, 0);
lean_inc(v_a_4196_);
lean_dec_ref_known(v___x_4195_, 1);
v___x_4197_ = lean_unsigned_to_nat(0u);
v_bs_x27_4198_ = lean_array_uset(v_bs_4188_, v_i_4187_, v___x_4197_);
v___x_4199_ = ((size_t)1ULL);
v___x_4200_ = lean_usize_add(v_i_4187_, v___x_4199_);
v___x_4201_ = lean_array_uset(v_bs_x27_4198_, v_i_4187_, v_a_4196_);
v_i_4187_ = v___x_4200_;
v_bs_4188_ = v___x_4201_;
goto _start;
}
else
{
lean_object* v_a_4203_; lean_object* v___x_4205_; uint8_t v_isShared_4206_; uint8_t v_isSharedCheck_4210_; 
lean_dec_ref(v_bs_4188_);
v_a_4203_ = lean_ctor_get(v___x_4195_, 0);
v_isSharedCheck_4210_ = !lean_is_exclusive(v___x_4195_);
if (v_isSharedCheck_4210_ == 0)
{
v___x_4205_ = v___x_4195_;
v_isShared_4206_ = v_isSharedCheck_4210_;
goto v_resetjp_4204_;
}
else
{
lean_inc(v_a_4203_);
lean_dec(v___x_4195_);
v___x_4205_ = lean_box(0);
v_isShared_4206_ = v_isSharedCheck_4210_;
goto v_resetjp_4204_;
}
v_resetjp_4204_:
{
lean_object* v___x_4208_; 
if (v_isShared_4206_ == 0)
{
v___x_4208_ = v___x_4205_;
goto v_reusejp_4207_;
}
else
{
lean_object* v_reuseFailAlloc_4209_; 
v_reuseFailAlloc_4209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4209_, 0, v_a_4203_);
v___x_4208_ = v_reuseFailAlloc_4209_;
goto v_reusejp_4207_;
}
v_reusejp_4207_:
{
return v___x_4208_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___redArg___boxed(lean_object* v_sz_4211_, lean_object* v_i_4212_, lean_object* v_bs_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_){
_start:
{
size_t v_sz_boxed_4217_; size_t v_i_boxed_4218_; lean_object* v_res_4219_; 
v_sz_boxed_4217_ = lean_unbox_usize(v_sz_4211_);
lean_dec(v_sz_4211_);
v_i_boxed_4218_ = lean_unbox_usize(v_i_4212_);
lean_dec(v_i_4212_);
v_res_4219_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___redArg(v_sz_boxed_4217_, v_i_boxed_4218_, v_bs_4213_, v___y_4214_, v___y_4215_);
lean_dec(v___y_4215_);
lean_dec_ref(v___y_4214_);
return v_res_4219_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___redArg(lean_object* v_as_4220_, size_t v_sz_4221_, size_t v_i_4222_, lean_object* v_b_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_){
_start:
{
uint8_t v___x_4227_; 
v___x_4227_ = lean_usize_dec_lt(v_i_4222_, v_sz_4221_);
if (v___x_4227_ == 0)
{
lean_object* v___x_4228_; 
v___x_4228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4228_, 0, v_b_4223_);
return v___x_4228_;
}
else
{
lean_object* v_a_4229_; lean_object* v_declName_4230_; lean_object* v___x_4231_; 
v_a_4229_ = lean_array_uget_borrowed(v_as_4220_, v_i_4222_);
v_declName_4230_ = lean_ctor_get(v_a_4229_, 3);
lean_inc(v_declName_4230_);
v___x_4231_ = l_Lean_enableRealizationsForConst(v_declName_4230_, v___y_4224_, v___y_4225_);
if (lean_obj_tag(v___x_4231_) == 0)
{
lean_object* v___x_4232_; size_t v___x_4233_; size_t v___x_4234_; 
lean_dec_ref_known(v___x_4231_, 1);
v___x_4232_ = lean_box(0);
v___x_4233_ = ((size_t)1ULL);
v___x_4234_ = lean_usize_add(v_i_4222_, v___x_4233_);
v_i_4222_ = v___x_4234_;
v_b_4223_ = v___x_4232_;
goto _start;
}
else
{
return v___x_4231_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___redArg___boxed(lean_object* v_as_4236_, lean_object* v_sz_4237_, lean_object* v_i_4238_, lean_object* v_b_4239_, lean_object* v___y_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_){
_start:
{
size_t v_sz_boxed_4243_; size_t v_i_boxed_4244_; lean_object* v_res_4245_; 
v_sz_boxed_4243_ = lean_unbox_usize(v_sz_4237_);
lean_dec(v_sz_4237_);
v_i_boxed_4244_ = lean_unbox_usize(v_i_4238_);
lean_dec(v_i_4238_);
v_res_4245_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___redArg(v_as_4236_, v_sz_boxed_4243_, v_i_boxed_4244_, v_b_4239_, v___y_4240_, v___y_4241_);
lean_dec(v___y_4241_);
lean_dec_ref(v___y_4240_);
lean_dec_ref(v_as_4236_);
return v_res_4245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_structuralRecursion(lean_object* v_docCtx_4246_, lean_object* v_preDefs_4247_, lean_object* v_termMeasure_x3fs_4248_, lean_object* v_a_4249_, lean_object* v_a_4250_, lean_object* v_a_4251_, lean_object* v_a_4252_, lean_object* v_a_4253_, lean_object* v_a_4254_){
_start:
{
size_t v_sz_4256_; size_t v___x_4257_; lean_object* v_names_4258_; lean_object* v___x_4259_; 
v_sz_4256_ = lean_array_size(v_preDefs_4247_);
v___x_4257_ = ((size_t)0ULL);
lean_inc_ref_n(v_preDefs_4247_, 2);
v_names_4258_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0(v_sz_4256_, v___x_4257_, v_preDefs_4247_);
v___x_4259_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos(v_preDefs_4247_, v_termMeasure_x3fs_4248_, v_a_4251_, v_a_4252_, v_a_4253_, v_a_4254_);
if (lean_obj_tag(v___x_4259_) == 0)
{
lean_object* v_a_4260_; lean_object* v_snd_4261_; lean_object* v_fst_4262_; lean_object* v_fst_4263_; lean_object* v_snd_4264_; lean_object* v___y_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; size_t v_sz_4300_; lean_object* v___x_4301_; 
v_a_4260_ = lean_ctor_get(v___x_4259_, 0);
lean_inc(v_a_4260_);
lean_dec_ref_known(v___x_4259_, 1);
v_snd_4261_ = lean_ctor_get(v_a_4260_, 1);
lean_inc(v_snd_4261_);
v_fst_4262_ = lean_ctor_get(v_a_4260_, 0);
lean_inc(v_fst_4262_);
lean_dec(v_a_4260_);
v_fst_4263_ = lean_ctor_get(v_snd_4261_, 0);
lean_inc(v_fst_4263_);
v_snd_4264_ = lean_ctor_get(v_snd_4261_, 1);
lean_inc(v_snd_4264_);
lean_dec(v_snd_4261_);
v___x_4297_ = lean_unsigned_to_nat(0u);
v___x_4298_ = lean_array_get_size(v_preDefs_4247_);
lean_inc_ref(v_preDefs_4247_);
v___x_4299_ = l_Array_toSubarray___redArg(v_preDefs_4247_, v___x_4297_, v___x_4298_);
v_sz_4300_ = lean_array_size(v_fst_4262_);
v___x_4301_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4___redArg(v_fst_4262_, v_sz_4300_, v___x_4257_, v___x_4299_, v_a_4251_, v_a_4252_, v_a_4253_, v_a_4254_);
if (lean_obj_tag(v___x_4301_) == 0)
{
lean_object* v___x_4302_; uint8_t v___x_4303_; 
lean_dec_ref_known(v___x_4301_, 1);
v___x_4302_ = lean_array_get_size(v_fst_4263_);
v___x_4303_ = lean_nat_dec_lt(v___x_4297_, v___x_4302_);
if (v___x_4303_ == 0)
{
lean_dec_ref(v_names_4258_);
goto v___jp_4265_;
}
else
{
lean_object* v___x_4304_; uint8_t v___x_4305_; 
v___x_4304_ = lean_box(0);
v___x_4305_ = lean_nat_dec_le(v___x_4302_, v___x_4302_);
if (v___x_4305_ == 0)
{
if (v___x_4303_ == 0)
{
lean_dec_ref(v_names_4258_);
goto v___jp_4265_;
}
else
{
size_t v___x_4306_; lean_object* v___x_4307_; 
v___x_4306_ = lean_usize_of_nat(v___x_4302_);
lean_inc_ref(v_docCtx_4246_);
v___x_4307_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5(v_names_4258_, v_docCtx_4246_, v_fst_4263_, v___x_4257_, v___x_4306_, v___x_4304_, v_a_4249_, v_a_4250_, v_a_4251_, v_a_4252_, v_a_4253_, v_a_4254_);
v___y_4296_ = v___x_4307_;
goto v___jp_4295_;
}
}
else
{
size_t v___x_4308_; lean_object* v___x_4309_; 
v___x_4308_ = lean_usize_of_nat(v___x_4302_);
lean_inc_ref(v_docCtx_4246_);
v___x_4309_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5(v_names_4258_, v_docCtx_4246_, v_fst_4263_, v___x_4257_, v___x_4308_, v___x_4304_, v_a_4249_, v_a_4250_, v_a_4251_, v_a_4252_, v_a_4253_, v_a_4254_);
v___y_4296_ = v___x_4309_;
goto v___jp_4295_;
}
}
}
else
{
lean_object* v_a_4310_; lean_object* v___x_4312_; uint8_t v_isShared_4313_; uint8_t v_isSharedCheck_4317_; 
lean_dec(v_snd_4264_);
lean_dec(v_fst_4263_);
lean_dec(v_fst_4262_);
lean_dec_ref(v_names_4258_);
lean_dec_ref(v_preDefs_4247_);
lean_dec_ref(v_docCtx_4246_);
v_a_4310_ = lean_ctor_get(v___x_4301_, 0);
v_isSharedCheck_4317_ = !lean_is_exclusive(v___x_4301_);
if (v_isSharedCheck_4317_ == 0)
{
v___x_4312_ = v___x_4301_;
v_isShared_4313_ = v_isSharedCheck_4317_;
goto v_resetjp_4311_;
}
else
{
lean_inc(v_a_4310_);
lean_dec(v___x_4301_);
v___x_4312_ = lean_box(0);
v_isShared_4313_ = v_isSharedCheck_4317_;
goto v_resetjp_4311_;
}
v_resetjp_4311_:
{
lean_object* v___x_4315_; 
if (v_isShared_4313_ == 0)
{
v___x_4315_ = v___x_4312_;
goto v_reusejp_4314_;
}
else
{
lean_object* v_reuseFailAlloc_4316_; 
v_reuseFailAlloc_4316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4316_, 0, v_a_4310_);
v___x_4315_ = v_reuseFailAlloc_4316_;
goto v_reusejp_4314_;
}
v_reusejp_4314_:
{
return v___x_4315_;
}
}
}
v___jp_4265_:
{
lean_object* v___x_4266_; 
v___x_4266_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___redArg(v_sz_4256_, v___x_4257_, v_preDefs_4247_, v_a_4253_, v_a_4254_);
if (lean_obj_tag(v___x_4266_) == 0)
{
lean_object* v_a_4267_; lean_object* v___x_4268_; 
v_a_4267_ = lean_ctor_get(v___x_4266_, 0);
lean_inc_n(v_a_4267_, 2);
lean_dec_ref_known(v___x_4266_, 1);
lean_inc_ref(v_docCtx_4246_);
v___x_4268_ = l_Lean_Elab_addAndCompilePartialRec(v_docCtx_4246_, v_a_4267_, v_a_4249_, v_a_4250_, v_a_4251_, v_a_4252_, v_a_4253_, v_a_4254_);
if (lean_obj_tag(v___x_4268_) == 0)
{
lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; size_t v_sz_4272_; lean_object* v___x_4273_; 
lean_dec_ref_known(v___x_4268_, 1);
v___x_4269_ = lean_unsigned_to_nat(0u);
v___x_4270_ = lean_array_get_size(v_fst_4262_);
v___x_4271_ = l_Array_toSubarray___redArg(v_fst_4262_, v___x_4269_, v___x_4270_);
v_sz_4272_ = lean_array_size(v_a_4267_);
lean_inc(v_a_4267_);
v___x_4273_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__1(v_docCtx_4246_, v_a_4267_, v_snd_4264_, v_a_4267_, v_sz_4272_, v___x_4257_, v___x_4271_, v_a_4249_, v_a_4250_, v_a_4251_, v_a_4252_, v_a_4253_, v_a_4254_);
if (lean_obj_tag(v___x_4273_) == 0)
{
lean_object* v___x_4274_; lean_object* v___x_4275_; 
lean_dec_ref_known(v___x_4273_, 1);
v___x_4274_ = lean_box(0);
v___x_4275_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___redArg(v_a_4267_, v_sz_4272_, v___x_4257_, v___x_4274_, v_a_4251_, v_a_4252_, v_a_4253_, v_a_4254_);
if (lean_obj_tag(v___x_4275_) == 0)
{
lean_object* v___x_4276_; 
lean_dec_ref_known(v___x_4275_, 1);
v___x_4276_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___redArg(v_a_4267_, v_sz_4272_, v___x_4257_, v___x_4274_, v_a_4253_, v_a_4254_);
lean_dec(v_a_4267_);
if (lean_obj_tag(v___x_4276_) == 0)
{
uint8_t v___x_4277_; lean_object* v___x_4278_; 
lean_dec_ref_known(v___x_4276_, 1);
v___x_4277_ = 1;
v___x_4278_ = l_Lean_Elab_applyAttributesOf(v_fst_4263_, v___x_4277_, v_a_4249_, v_a_4250_, v_a_4251_, v_a_4252_, v_a_4253_, v_a_4254_);
lean_dec(v_fst_4263_);
return v___x_4278_;
}
else
{
lean_dec(v_fst_4263_);
return v___x_4276_;
}
}
else
{
lean_dec(v_a_4267_);
lean_dec(v_fst_4263_);
return v___x_4275_;
}
}
else
{
lean_object* v_a_4279_; lean_object* v___x_4281_; uint8_t v_isShared_4282_; uint8_t v_isSharedCheck_4286_; 
lean_dec(v_a_4267_);
lean_dec(v_fst_4263_);
v_a_4279_ = lean_ctor_get(v___x_4273_, 0);
v_isSharedCheck_4286_ = !lean_is_exclusive(v___x_4273_);
if (v_isSharedCheck_4286_ == 0)
{
v___x_4281_ = v___x_4273_;
v_isShared_4282_ = v_isSharedCheck_4286_;
goto v_resetjp_4280_;
}
else
{
lean_inc(v_a_4279_);
lean_dec(v___x_4273_);
v___x_4281_ = lean_box(0);
v_isShared_4282_ = v_isSharedCheck_4286_;
goto v_resetjp_4280_;
}
v_resetjp_4280_:
{
lean_object* v___x_4284_; 
if (v_isShared_4282_ == 0)
{
v___x_4284_ = v___x_4281_;
goto v_reusejp_4283_;
}
else
{
lean_object* v_reuseFailAlloc_4285_; 
v_reuseFailAlloc_4285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4285_, 0, v_a_4279_);
v___x_4284_ = v_reuseFailAlloc_4285_;
goto v_reusejp_4283_;
}
v_reusejp_4283_:
{
return v___x_4284_;
}
}
}
}
else
{
lean_dec(v_a_4267_);
lean_dec(v_snd_4264_);
lean_dec(v_fst_4263_);
lean_dec(v_fst_4262_);
lean_dec_ref(v_docCtx_4246_);
return v___x_4268_;
}
}
else
{
lean_object* v_a_4287_; lean_object* v___x_4289_; uint8_t v_isShared_4290_; uint8_t v_isSharedCheck_4294_; 
lean_dec(v_snd_4264_);
lean_dec(v_fst_4263_);
lean_dec(v_fst_4262_);
lean_dec_ref(v_docCtx_4246_);
v_a_4287_ = lean_ctor_get(v___x_4266_, 0);
v_isSharedCheck_4294_ = !lean_is_exclusive(v___x_4266_);
if (v_isSharedCheck_4294_ == 0)
{
v___x_4289_ = v___x_4266_;
v_isShared_4290_ = v_isSharedCheck_4294_;
goto v_resetjp_4288_;
}
else
{
lean_inc(v_a_4287_);
lean_dec(v___x_4266_);
v___x_4289_ = lean_box(0);
v_isShared_4290_ = v_isSharedCheck_4294_;
goto v_resetjp_4288_;
}
v_resetjp_4288_:
{
lean_object* v___x_4292_; 
if (v_isShared_4290_ == 0)
{
v___x_4292_ = v___x_4289_;
goto v_reusejp_4291_;
}
else
{
lean_object* v_reuseFailAlloc_4293_; 
v_reuseFailAlloc_4293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4293_, 0, v_a_4287_);
v___x_4292_ = v_reuseFailAlloc_4293_;
goto v_reusejp_4291_;
}
v_reusejp_4291_:
{
return v___x_4292_;
}
}
}
}
v___jp_4295_:
{
if (lean_obj_tag(v___y_4296_) == 0)
{
lean_dec_ref_known(v___y_4296_, 1);
goto v___jp_4265_;
}
else
{
lean_dec(v_snd_4264_);
lean_dec(v_fst_4263_);
lean_dec(v_fst_4262_);
lean_dec_ref(v_preDefs_4247_);
lean_dec_ref(v_docCtx_4246_);
return v___y_4296_;
}
}
}
else
{
lean_object* v_a_4318_; lean_object* v___x_4320_; uint8_t v_isShared_4321_; uint8_t v_isSharedCheck_4325_; 
lean_dec_ref(v_names_4258_);
lean_dec_ref(v_preDefs_4247_);
lean_dec_ref(v_docCtx_4246_);
v_a_4318_ = lean_ctor_get(v___x_4259_, 0);
v_isSharedCheck_4325_ = !lean_is_exclusive(v___x_4259_);
if (v_isSharedCheck_4325_ == 0)
{
v___x_4320_ = v___x_4259_;
v_isShared_4321_ = v_isSharedCheck_4325_;
goto v_resetjp_4319_;
}
else
{
lean_inc(v_a_4318_);
lean_dec(v___x_4259_);
v___x_4320_ = lean_box(0);
v_isShared_4321_ = v_isSharedCheck_4325_;
goto v_resetjp_4319_;
}
v_resetjp_4319_:
{
lean_object* v___x_4323_; 
if (v_isShared_4321_ == 0)
{
v___x_4323_ = v___x_4320_;
goto v_reusejp_4322_;
}
else
{
lean_object* v_reuseFailAlloc_4324_; 
v_reuseFailAlloc_4324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4324_, 0, v_a_4318_);
v___x_4323_ = v_reuseFailAlloc_4324_;
goto v_reusejp_4322_;
}
v_reusejp_4322_:
{
return v___x_4323_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_structuralRecursion___boxed(lean_object* v_docCtx_4326_, lean_object* v_preDefs_4327_, lean_object* v_termMeasure_x3fs_4328_, lean_object* v_a_4329_, lean_object* v_a_4330_, lean_object* v_a_4331_, lean_object* v_a_4332_, lean_object* v_a_4333_, lean_object* v_a_4334_, lean_object* v_a_4335_){
_start:
{
lean_object* v_res_4336_; 
v_res_4336_ = l_Lean_Elab_Structural_structuralRecursion(v_docCtx_4326_, v_preDefs_4327_, v_termMeasure_x3fs_4328_, v_a_4329_, v_a_4330_, v_a_4331_, v_a_4332_, v_a_4333_, v_a_4334_);
lean_dec(v_a_4334_);
lean_dec_ref(v_a_4333_);
lean_dec(v_a_4332_);
lean_dec_ref(v_a_4331_);
lean_dec(v_a_4330_);
lean_dec_ref(v_a_4329_);
return v_res_4336_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0(size_t v_sz_4337_, size_t v_i_4338_, lean_object* v_bs_4339_, lean_object* v___y_4340_, lean_object* v___y_4341_, lean_object* v___y_4342_, lean_object* v___y_4343_, lean_object* v___y_4344_, lean_object* v___y_4345_){
_start:
{
lean_object* v___x_4347_; 
v___x_4347_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___redArg(v_sz_4337_, v_i_4338_, v_bs_4339_, v___y_4344_, v___y_4345_);
return v___x_4347_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___boxed(lean_object* v_sz_4348_, lean_object* v_i_4349_, lean_object* v_bs_4350_, lean_object* v___y_4351_, lean_object* v___y_4352_, lean_object* v___y_4353_, lean_object* v___y_4354_, lean_object* v___y_4355_, lean_object* v___y_4356_, lean_object* v___y_4357_){
_start:
{
size_t v_sz_boxed_4358_; size_t v_i_boxed_4359_; lean_object* v_res_4360_; 
v_sz_boxed_4358_ = lean_unbox_usize(v_sz_4348_);
lean_dec(v_sz_4348_);
v_i_boxed_4359_ = lean_unbox_usize(v_i_4349_);
lean_dec(v_i_4349_);
v_res_4360_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0(v_sz_boxed_4358_, v_i_boxed_4359_, v_bs_4350_, v___y_4351_, v___y_4352_, v___y_4353_, v___y_4354_, v___y_4355_, v___y_4356_);
lean_dec(v___y_4356_);
lean_dec_ref(v___y_4355_);
lean_dec(v___y_4354_);
lean_dec_ref(v___y_4353_);
lean_dec(v___y_4352_);
lean_dec_ref(v___y_4351_);
return v_res_4360_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2(lean_object* v_as_4361_, size_t v_sz_4362_, size_t v_i_4363_, lean_object* v_b_4364_, lean_object* v___y_4365_, lean_object* v___y_4366_, lean_object* v___y_4367_, lean_object* v___y_4368_, lean_object* v___y_4369_, lean_object* v___y_4370_){
_start:
{
lean_object* v___x_4372_; 
v___x_4372_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___redArg(v_as_4361_, v_sz_4362_, v_i_4363_, v_b_4364_, v___y_4367_, v___y_4368_, v___y_4369_, v___y_4370_);
return v___x_4372_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___boxed(lean_object* v_as_4373_, lean_object* v_sz_4374_, lean_object* v_i_4375_, lean_object* v_b_4376_, lean_object* v___y_4377_, lean_object* v___y_4378_, lean_object* v___y_4379_, lean_object* v___y_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_, lean_object* v___y_4383_){
_start:
{
size_t v_sz_boxed_4384_; size_t v_i_boxed_4385_; lean_object* v_res_4386_; 
v_sz_boxed_4384_ = lean_unbox_usize(v_sz_4374_);
lean_dec(v_sz_4374_);
v_i_boxed_4385_ = lean_unbox_usize(v_i_4375_);
lean_dec(v_i_4375_);
v_res_4386_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2(v_as_4373_, v_sz_boxed_4384_, v_i_boxed_4385_, v_b_4376_, v___y_4377_, v___y_4378_, v___y_4379_, v___y_4380_, v___y_4381_, v___y_4382_);
lean_dec(v___y_4382_);
lean_dec_ref(v___y_4381_);
lean_dec(v___y_4380_);
lean_dec_ref(v___y_4379_);
lean_dec(v___y_4378_);
lean_dec_ref(v___y_4377_);
lean_dec_ref(v_as_4373_);
return v_res_4386_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3(lean_object* v_as_4387_, size_t v_sz_4388_, size_t v_i_4389_, lean_object* v_b_4390_, lean_object* v___y_4391_, lean_object* v___y_4392_, lean_object* v___y_4393_, lean_object* v___y_4394_, lean_object* v___y_4395_, lean_object* v___y_4396_){
_start:
{
lean_object* v___x_4398_; 
v___x_4398_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___redArg(v_as_4387_, v_sz_4388_, v_i_4389_, v_b_4390_, v___y_4395_, v___y_4396_);
return v___x_4398_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___boxed(lean_object* v_as_4399_, lean_object* v_sz_4400_, lean_object* v_i_4401_, lean_object* v_b_4402_, lean_object* v___y_4403_, lean_object* v___y_4404_, lean_object* v___y_4405_, lean_object* v___y_4406_, lean_object* v___y_4407_, lean_object* v___y_4408_, lean_object* v___y_4409_){
_start:
{
size_t v_sz_boxed_4410_; size_t v_i_boxed_4411_; lean_object* v_res_4412_; 
v_sz_boxed_4410_ = lean_unbox_usize(v_sz_4400_);
lean_dec(v_sz_4400_);
v_i_boxed_4411_ = lean_unbox_usize(v_i_4401_);
lean_dec(v_i_4401_);
v_res_4412_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3(v_as_4399_, v_sz_boxed_4410_, v_i_boxed_4411_, v_b_4402_, v___y_4403_, v___y_4404_, v___y_4405_, v___y_4406_, v___y_4407_, v___y_4408_);
lean_dec(v___y_4408_);
lean_dec_ref(v___y_4407_);
lean_dec(v___y_4406_);
lean_dec_ref(v___y_4405_);
lean_dec(v___y_4404_);
lean_dec_ref(v___y_4403_);
lean_dec_ref(v_as_4399_);
return v_res_4412_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4(lean_object* v_as_4413_, size_t v_sz_4414_, size_t v_i_4415_, lean_object* v_b_4416_, lean_object* v___y_4417_, lean_object* v___y_4418_, lean_object* v___y_4419_, lean_object* v___y_4420_, lean_object* v___y_4421_, lean_object* v___y_4422_){
_start:
{
lean_object* v___x_4424_; 
v___x_4424_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4___redArg(v_as_4413_, v_sz_4414_, v_i_4415_, v_b_4416_, v___y_4419_, v___y_4420_, v___y_4421_, v___y_4422_);
return v___x_4424_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4___boxed(lean_object* v_as_4425_, lean_object* v_sz_4426_, lean_object* v_i_4427_, lean_object* v_b_4428_, lean_object* v___y_4429_, lean_object* v___y_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_){
_start:
{
size_t v_sz_boxed_4436_; size_t v_i_boxed_4437_; lean_object* v_res_4438_; 
v_sz_boxed_4436_ = lean_unbox_usize(v_sz_4426_);
lean_dec(v_sz_4426_);
v_i_boxed_4437_ = lean_unbox_usize(v_i_4427_);
lean_dec(v_i_4427_);
v_res_4438_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4(v_as_4425_, v_sz_boxed_4436_, v_i_boxed_4437_, v_b_4428_, v___y_4429_, v___y_4430_, v___y_4431_, v___y_4432_, v___y_4433_, v___y_4434_);
lean_dec(v___y_4434_);
lean_dec_ref(v___y_4433_);
lean_dec(v___y_4432_);
lean_dec_ref(v___y_4431_);
lean_dec(v___y_4430_);
lean_dec_ref(v___y_4429_);
lean_dec_ref(v_as_4425_);
return v_res_4438_;
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
