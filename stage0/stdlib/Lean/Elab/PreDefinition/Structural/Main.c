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
lean_object* v_options_144_; uint8_t v_hasTrace_145_; 
v_options_144_ = lean_ctor_get(v___y_141_, 1);
v_hasTrace_145_ = lean_ctor_get_uint8(v_options_144_, sizeof(void*)*1);
if (v_hasTrace_145_ == 0)
{
lean_object* v___x_146_; lean_object* v___x_147_; 
lean_dec(v___x_138_);
v___x_146_ = lean_box(v_hasTrace_145_);
v___x_147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_147_, 0, v___x_146_);
return v___x_147_;
}
else
{
lean_object* v_toCold_148_; lean_object* v_inheritedTraceOptions_149_; lean_object* v___x_150_; lean_object* v___x_151_; uint8_t v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v_toCold_148_ = lean_ctor_get(v___y_141_, 0);
v_inheritedTraceOptions_149_ = lean_ctor_get(v_toCold_148_, 4);
v___x_150_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0___closed__1));
v___x_151_ = l_Lean_Name_append(v___x_150_, v___x_138_);
v___x_152_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_149_, v_options_144_, v___x_151_);
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
lean_object* v___x_19336__overap_176_; lean_object* v___x_177_; 
v___x_19336__overap_176_ = lean_array_uget_borrowed(v_as_166_, v_i_167_);
lean_inc(v___x_19336__overap_176_);
lean_inc(v___y_173_);
lean_inc_ref(v___y_172_);
lean_inc(v___y_171_);
lean_inc_ref(v___y_170_);
v___x_177_ = lean_apply_5(v___x_19336__overap_176_, v___y_170_, v___y_171_, v___y_172_, v___y_173_, lean_box(0));
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
uint8_t v_a_25173__boxed_509_; size_t v_sz_boxed_510_; size_t v_i_boxed_511_; lean_object* v_res_512_; 
v_a_25173__boxed_509_ = lean_unbox(v_a_494_);
v_sz_boxed_510_ = lean_unbox_usize(v_sz_501_);
lean_dec(v_sz_501_);
v_i_boxed_511_ = lean_unbox_usize(v_i_502_);
lean_dec(v_i_502_);
v_res_512_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg(v_a_25173__boxed_509_, v_a_495_, v_a_496_, v_recArgInfos_497_, v___x_498_, v_preDefs_499_, v_a_500_, v_sz_boxed_510_, v_i_boxed_511_, v_bs_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_);
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
lean_object* v___x_519_; lean_object* v_env_520_; lean_object* v___x_521_; lean_object* v_mctx_522_; lean_object* v_lctx_523_; lean_object* v_options_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_519_ = lean_st_ref_get(v___y_517_);
v_env_520_ = lean_ctor_get(v___x_519_, 0);
lean_inc_ref(v_env_520_);
lean_dec(v___x_519_);
v___x_521_ = lean_st_ref_get(v___y_515_);
v_mctx_522_ = lean_ctor_get(v___x_521_, 0);
lean_inc_ref(v_mctx_522_);
lean_dec(v___x_521_);
v_lctx_523_ = lean_ctor_get(v___y_514_, 2);
v_options_524_ = lean_ctor_get(v___y_516_, 1);
lean_inc_ref(v_options_524_);
lean_inc_ref(v_lctx_523_);
v___x_525_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_525_, 0, v_env_520_);
lean_ctor_set(v___x_525_, 1, v_mctx_522_);
lean_ctor_set(v___x_525_, 2, v_lctx_523_);
lean_ctor_set(v___x_525_, 3, v_options_524_);
v___x_526_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_526_, 0, v___x_525_);
lean_ctor_set(v___x_526_, 1, v_msgData_513_);
v___x_527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_527_, 0, v___x_526_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11_spec__21___boxed(lean_object* v_msgData_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11_spec__21(v_msgData_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_);
lean_dec(v___y_532_);
lean_dec_ref(v___y_531_);
lean_dec(v___y_530_);
lean_dec_ref(v___y_529_);
return v_res_534_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___closed__0(void){
_start:
{
lean_object* v___x_535_; double v___x_536_; 
v___x_535_ = lean_unsigned_to_nat(0u);
v___x_536_ = lean_float_of_nat(v___x_535_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(lean_object* v_cls_540_, lean_object* v_msg_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_){
_start:
{
lean_object* v_ref_547_; lean_object* v___x_548_; lean_object* v_a_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_593_; 
v_ref_547_ = lean_ctor_get(v___y_544_, 4);
v___x_548_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11_spec__21(v_msg_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_);
v_a_549_ = lean_ctor_get(v___x_548_, 0);
v_isSharedCheck_593_ = !lean_is_exclusive(v___x_548_);
if (v_isSharedCheck_593_ == 0)
{
v___x_551_ = v___x_548_;
v_isShared_552_ = v_isSharedCheck_593_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_a_549_);
lean_dec(v___x_548_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_593_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v___x_553_; lean_object* v_traceState_554_; lean_object* v_env_555_; lean_object* v_nextMacroScope_556_; lean_object* v_ngen_557_; lean_object* v_auxDeclNGen_558_; lean_object* v_cache_559_; lean_object* v_messages_560_; lean_object* v_infoState_561_; lean_object* v_snapshotTasks_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_592_; 
v___x_553_ = lean_st_ref_take(v___y_545_);
v_traceState_554_ = lean_ctor_get(v___x_553_, 4);
v_env_555_ = lean_ctor_get(v___x_553_, 0);
v_nextMacroScope_556_ = lean_ctor_get(v___x_553_, 1);
v_ngen_557_ = lean_ctor_get(v___x_553_, 2);
v_auxDeclNGen_558_ = lean_ctor_get(v___x_553_, 3);
v_cache_559_ = lean_ctor_get(v___x_553_, 5);
v_messages_560_ = lean_ctor_get(v___x_553_, 6);
v_infoState_561_ = lean_ctor_get(v___x_553_, 7);
v_snapshotTasks_562_ = lean_ctor_get(v___x_553_, 8);
v_isSharedCheck_592_ = !lean_is_exclusive(v___x_553_);
if (v_isSharedCheck_592_ == 0)
{
v___x_564_ = v___x_553_;
v_isShared_565_ = v_isSharedCheck_592_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_snapshotTasks_562_);
lean_inc(v_infoState_561_);
lean_inc(v_messages_560_);
lean_inc(v_cache_559_);
lean_inc(v_traceState_554_);
lean_inc(v_auxDeclNGen_558_);
lean_inc(v_ngen_557_);
lean_inc(v_nextMacroScope_556_);
lean_inc(v_env_555_);
lean_dec(v___x_553_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_592_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
uint64_t v_tid_566_; lean_object* v_traces_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_591_; 
v_tid_566_ = lean_ctor_get_uint64(v_traceState_554_, sizeof(void*)*1);
v_traces_567_ = lean_ctor_get(v_traceState_554_, 0);
v_isSharedCheck_591_ = !lean_is_exclusive(v_traceState_554_);
if (v_isSharedCheck_591_ == 0)
{
v___x_569_ = v_traceState_554_;
v_isShared_570_ = v_isSharedCheck_591_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_traces_567_);
lean_dec(v_traceState_554_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_591_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v___x_571_; double v___x_572_; uint8_t v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_581_; 
v___x_571_ = lean_box(0);
v___x_572_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___closed__0);
v___x_573_ = 0;
v___x_574_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___closed__1));
v___x_575_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_575_, 0, v_cls_540_);
lean_ctor_set(v___x_575_, 1, v___x_571_);
lean_ctor_set(v___x_575_, 2, v___x_574_);
lean_ctor_set_float(v___x_575_, sizeof(void*)*3, v___x_572_);
lean_ctor_set_float(v___x_575_, sizeof(void*)*3 + 8, v___x_572_);
lean_ctor_set_uint8(v___x_575_, sizeof(void*)*3 + 16, v___x_573_);
v___x_576_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___closed__2));
v___x_577_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_577_, 0, v___x_575_);
lean_ctor_set(v___x_577_, 1, v_a_549_);
lean_ctor_set(v___x_577_, 2, v___x_576_);
lean_inc(v_ref_547_);
v___x_578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_578_, 0, v_ref_547_);
lean_ctor_set(v___x_578_, 1, v___x_577_);
v___x_579_ = l_Lean_PersistentArray_push___redArg(v_traces_567_, v___x_578_);
if (v_isShared_570_ == 0)
{
lean_ctor_set(v___x_569_, 0, v___x_579_);
v___x_581_ = v___x_569_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v___x_579_);
lean_ctor_set_uint64(v_reuseFailAlloc_590_, sizeof(void*)*1, v_tid_566_);
v___x_581_ = v_reuseFailAlloc_590_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
lean_object* v___x_583_; 
if (v_isShared_565_ == 0)
{
lean_ctor_set(v___x_564_, 4, v___x_581_);
v___x_583_ = v___x_564_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v_env_555_);
lean_ctor_set(v_reuseFailAlloc_589_, 1, v_nextMacroScope_556_);
lean_ctor_set(v_reuseFailAlloc_589_, 2, v_ngen_557_);
lean_ctor_set(v_reuseFailAlloc_589_, 3, v_auxDeclNGen_558_);
lean_ctor_set(v_reuseFailAlloc_589_, 4, v___x_581_);
lean_ctor_set(v_reuseFailAlloc_589_, 5, v_cache_559_);
lean_ctor_set(v_reuseFailAlloc_589_, 6, v_messages_560_);
lean_ctor_set(v_reuseFailAlloc_589_, 7, v_infoState_561_);
lean_ctor_set(v_reuseFailAlloc_589_, 8, v_snapshotTasks_562_);
v___x_583_ = v_reuseFailAlloc_589_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_587_; 
v___x_584_ = lean_st_ref_put(v___y_545_, v___x_583_);
v___x_585_ = lean_box(0);
if (v_isShared_552_ == 0)
{
lean_ctor_set(v___x_551_, 0, v___x_585_);
v___x_587_ = v___x_551_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v___x_585_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
return v___x_587_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___boxed(lean_object* v_cls_594_, lean_object* v_msg_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v_cls_594_, v_msg_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_);
lean_dec(v___y_599_);
lean_dec_ref(v___y_598_);
lean_dec(v___y_597_);
lean_dec_ref(v___y_596_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9(lean_object* v_as_602_, lean_object* v_bs_603_, lean_object* v_i_604_, lean_object* v_cs_605_){
_start:
{
lean_object* v___x_606_; uint8_t v___x_607_; 
v___x_606_ = lean_array_get_size(v_as_602_);
v___x_607_ = lean_nat_dec_lt(v_i_604_, v___x_606_);
if (v___x_607_ == 0)
{
lean_dec(v_i_604_);
return v_cs_605_;
}
else
{
lean_object* v___x_608_; uint8_t v___x_609_; 
v___x_608_ = lean_array_get_size(v_bs_603_);
v___x_609_ = lean_nat_dec_lt(v_i_604_, v___x_608_);
if (v___x_609_ == 0)
{
lean_dec(v_i_604_);
return v_cs_605_;
}
else
{
lean_object* v_a_610_; lean_object* v_ref_611_; uint8_t v_kind_612_; lean_object* v_levelParams_613_; lean_object* v_modifiers_614_; lean_object* v_declName_615_; lean_object* v_binders_616_; lean_object* v_numSectionVars_617_; lean_object* v_type_618_; lean_object* v_termination_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_631_; 
v_a_610_ = lean_array_fget(v_as_602_, v_i_604_);
v_ref_611_ = lean_ctor_get(v_a_610_, 0);
v_kind_612_ = lean_ctor_get_uint8(v_a_610_, sizeof(void*)*9);
v_levelParams_613_ = lean_ctor_get(v_a_610_, 1);
v_modifiers_614_ = lean_ctor_get(v_a_610_, 2);
v_declName_615_ = lean_ctor_get(v_a_610_, 3);
v_binders_616_ = lean_ctor_get(v_a_610_, 4);
v_numSectionVars_617_ = lean_ctor_get(v_a_610_, 5);
v_type_618_ = lean_ctor_get(v_a_610_, 6);
v_termination_619_ = lean_ctor_get(v_a_610_, 8);
v_isSharedCheck_631_ = !lean_is_exclusive(v_a_610_);
if (v_isSharedCheck_631_ == 0)
{
lean_object* v_unused_632_; 
v_unused_632_ = lean_ctor_get(v_a_610_, 7);
lean_dec(v_unused_632_);
v___x_621_ = v_a_610_;
v_isShared_622_ = v_isSharedCheck_631_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_termination_619_);
lean_inc(v_type_618_);
lean_inc(v_numSectionVars_617_);
lean_inc(v_binders_616_);
lean_inc(v_declName_615_);
lean_inc(v_modifiers_614_);
lean_inc(v_levelParams_613_);
lean_inc(v_ref_611_);
lean_dec(v_a_610_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_631_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v_b_623_; lean_object* v___x_625_; 
v_b_623_ = lean_array_fget_borrowed(v_bs_603_, v_i_604_);
lean_inc(v_b_623_);
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 7, v_b_623_);
v___x_625_ = v___x_621_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v_ref_611_);
lean_ctor_set(v_reuseFailAlloc_630_, 1, v_levelParams_613_);
lean_ctor_set(v_reuseFailAlloc_630_, 2, v_modifiers_614_);
lean_ctor_set(v_reuseFailAlloc_630_, 3, v_declName_615_);
lean_ctor_set(v_reuseFailAlloc_630_, 4, v_binders_616_);
lean_ctor_set(v_reuseFailAlloc_630_, 5, v_numSectionVars_617_);
lean_ctor_set(v_reuseFailAlloc_630_, 6, v_type_618_);
lean_ctor_set(v_reuseFailAlloc_630_, 7, v_b_623_);
lean_ctor_set(v_reuseFailAlloc_630_, 8, v_termination_619_);
lean_ctor_set_uint8(v_reuseFailAlloc_630_, sizeof(void*)*9, v_kind_612_);
v___x_625_ = v_reuseFailAlloc_630_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_626_ = lean_unsigned_to_nat(1u);
v___x_627_ = lean_nat_add(v_i_604_, v___x_626_);
lean_dec(v_i_604_);
v___x_628_ = lean_array_push(v_cs_605_, v___x_625_);
v_i_604_ = v___x_627_;
v_cs_605_ = v___x_628_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9___boxed(lean_object* v_as_633_, lean_object* v_bs_634_, lean_object* v_i_635_, lean_object* v_cs_636_){
_start:
{
lean_object* v_res_637_; 
v_res_637_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9(v_as_633_, v_bs_634_, v_i_635_, v_cs_636_);
lean_dec_ref(v_bs_634_);
lean_dec_ref(v_as_633_);
return v_res_637_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16_spec__29___redArg(lean_object* v_declName_638_, uint8_t v_s_639_, lean_object* v___y_640_, lean_object* v___y_641_){
_start:
{
lean_object* v___x_643_; lean_object* v_env_644_; lean_object* v_nextMacroScope_645_; lean_object* v_ngen_646_; lean_object* v_auxDeclNGen_647_; lean_object* v_traceState_648_; lean_object* v_messages_649_; lean_object* v_infoState_650_; lean_object* v_snapshotTasks_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_680_; 
v___x_643_ = lean_st_ref_take(v___y_641_);
v_env_644_ = lean_ctor_get(v___x_643_, 0);
v_nextMacroScope_645_ = lean_ctor_get(v___x_643_, 1);
v_ngen_646_ = lean_ctor_get(v___x_643_, 2);
v_auxDeclNGen_647_ = lean_ctor_get(v___x_643_, 3);
v_traceState_648_ = lean_ctor_get(v___x_643_, 4);
v_messages_649_ = lean_ctor_get(v___x_643_, 6);
v_infoState_650_ = lean_ctor_get(v___x_643_, 7);
v_snapshotTasks_651_ = lean_ctor_get(v___x_643_, 8);
v_isSharedCheck_680_ = !lean_is_exclusive(v___x_643_);
if (v_isSharedCheck_680_ == 0)
{
lean_object* v_unused_681_; 
v_unused_681_ = lean_ctor_get(v___x_643_, 5);
lean_dec(v_unused_681_);
v___x_653_ = v___x_643_;
v_isShared_654_ = v_isSharedCheck_680_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_snapshotTasks_651_);
lean_inc(v_infoState_650_);
lean_inc(v_messages_649_);
lean_inc(v_traceState_648_);
lean_inc(v_auxDeclNGen_647_);
lean_inc(v_ngen_646_);
lean_inc(v_nextMacroScope_645_);
lean_inc(v_env_644_);
lean_dec(v___x_643_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_680_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
uint8_t v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_660_; 
v___x_655_ = 0;
v___x_656_ = lean_box(0);
v___x_657_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_644_, v_declName_638_, v_s_639_, v___x_655_, v___x_656_);
v___x_658_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__2);
if (v_isShared_654_ == 0)
{
lean_ctor_set(v___x_653_, 5, v___x_658_);
lean_ctor_set(v___x_653_, 0, v___x_657_);
v___x_660_ = v___x_653_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v___x_657_);
lean_ctor_set(v_reuseFailAlloc_679_, 1, v_nextMacroScope_645_);
lean_ctor_set(v_reuseFailAlloc_679_, 2, v_ngen_646_);
lean_ctor_set(v_reuseFailAlloc_679_, 3, v_auxDeclNGen_647_);
lean_ctor_set(v_reuseFailAlloc_679_, 4, v_traceState_648_);
lean_ctor_set(v_reuseFailAlloc_679_, 5, v___x_658_);
lean_ctor_set(v_reuseFailAlloc_679_, 6, v_messages_649_);
lean_ctor_set(v_reuseFailAlloc_679_, 7, v_infoState_650_);
lean_ctor_set(v_reuseFailAlloc_679_, 8, v_snapshotTasks_651_);
v___x_660_ = v_reuseFailAlloc_679_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v_mctx_663_; lean_object* v_zetaDeltaFVarIds_664_; lean_object* v_postponed_665_; lean_object* v_diag_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_677_; 
v___x_661_ = lean_st_ref_put(v___y_641_, v___x_660_);
v___x_662_ = lean_st_ref_take(v___y_640_);
v_mctx_663_ = lean_ctor_get(v___x_662_, 0);
v_zetaDeltaFVarIds_664_ = lean_ctor_get(v___x_662_, 2);
v_postponed_665_ = lean_ctor_get(v___x_662_, 3);
v_diag_666_ = lean_ctor_get(v___x_662_, 4);
v_isSharedCheck_677_ = !lean_is_exclusive(v___x_662_);
if (v_isSharedCheck_677_ == 0)
{
lean_object* v_unused_678_; 
v_unused_678_ = lean_ctor_get(v___x_662_, 1);
lean_dec(v_unused_678_);
v___x_668_ = v___x_662_;
v_isShared_669_ = v_isSharedCheck_677_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_diag_666_);
lean_inc(v_postponed_665_);
lean_inc(v_zetaDeltaFVarIds_664_);
lean_inc(v_mctx_663_);
lean_dec(v___x_662_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_677_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_670_; lean_object* v___x_672_; 
v___x_670_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__3, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__3);
if (v_isShared_669_ == 0)
{
lean_ctor_set(v___x_668_, 1, v___x_670_);
v___x_672_ = v___x_668_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v_mctx_663_);
lean_ctor_set(v_reuseFailAlloc_676_, 1, v___x_670_);
lean_ctor_set(v_reuseFailAlloc_676_, 2, v_zetaDeltaFVarIds_664_);
lean_ctor_set(v_reuseFailAlloc_676_, 3, v_postponed_665_);
lean_ctor_set(v_reuseFailAlloc_676_, 4, v_diag_666_);
v___x_672_ = v_reuseFailAlloc_676_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_673_ = lean_st_ref_put(v___y_640_, v___x_672_);
v___x_674_ = lean_box(0);
v___x_675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_675_, 0, v___x_674_);
return v___x_675_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16_spec__29___redArg___boxed(lean_object* v_declName_682_, lean_object* v_s_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_){
_start:
{
uint8_t v_s_boxed_687_; lean_object* v_res_688_; 
v_s_boxed_687_ = lean_unbox(v_s_683_);
v_res_688_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16_spec__29___redArg(v_declName_682_, v_s_boxed_687_, v___y_684_, v___y_685_);
lean_dec(v___y_685_);
lean_dec(v___y_684_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16(lean_object* v_declName_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_){
_start:
{
uint8_t v___x_695_; lean_object* v___x_696_; 
v___x_695_ = 0;
v___x_696_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16_spec__29___redArg(v_declName_689_, v___x_695_, v___y_691_, v___y_693_);
return v___x_696_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16___boxed(lean_object* v_declName_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_){
_start:
{
lean_object* v_res_703_; 
v_res_703_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16(v_declName_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
lean_dec(v___y_701_);
lean_dec_ref(v___y_700_);
lean_dec(v___y_699_);
lean_dec_ref(v___y_698_);
return v_res_703_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg(lean_object* v_xs_707_, uint8_t v_a_708_, lean_object* v_preDefs_709_, lean_object* v___x_710_, size_t v_sz_711_, size_t v_i_712_, lean_object* v_bs_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_){
_start:
{
uint8_t v___x_719_; 
v___x_719_ = lean_usize_dec_lt(v_i_712_, v_sz_711_);
if (v___x_719_ == 0)
{
lean_object* v___x_720_; 
lean_dec(v___x_710_);
v___x_720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_720_, 0, v_bs_713_);
return v___x_720_;
}
else
{
lean_object* v_v_721_; lean_object* v___x_722_; lean_object* v_bs_x27_723_; lean_object* v_a_725_; lean_object* v___y_731_; uint8_t v___x_741_; lean_object* v___x_742_; 
v_v_721_ = lean_array_uget(v_bs_713_, v_i_712_);
v___x_722_ = lean_unsigned_to_nat(0u);
v_bs_x27_723_ = lean_array_uset(v_bs_713_, v_i_712_, v___x_722_);
v___x_741_ = 1;
v___x_742_ = l_Lean_Meta_mkLambdaFVars(v_xs_707_, v_v_721_, v_a_708_, v___x_719_, v_a_708_, v___x_719_, v___x_741_, v___y_714_, v___y_715_, v___y_716_, v___y_717_);
if (lean_obj_tag(v___x_742_) == 0)
{
lean_object* v_a_743_; lean_object* v___x_744_; 
v_a_743_ = lean_ctor_get(v___x_742_, 0);
lean_inc(v_a_743_);
lean_dec_ref_known(v___x_742_, 1);
v___x_744_ = l_Lean_Elab_eraseRecAppSyntaxExpr(v_a_743_, v___y_716_, v___y_717_);
if (lean_obj_tag(v___x_744_) == 0)
{
lean_object* v_a_745_; lean_object* v___x_746_; 
v_a_745_ = lean_ctor_get(v___x_744_, 0);
lean_inc_n(v_a_745_, 2);
lean_dec_ref_known(v___x_744_, 1);
lean_inc(v___y_717_);
lean_inc_ref(v___y_716_);
lean_inc(v___y_715_);
lean_inc_ref(v___y_714_);
v___x_746_ = lean_infer_type(v_a_745_, v___y_714_, v___y_715_, v___y_716_, v___y_717_);
if (lean_obj_tag(v___x_746_) == 0)
{
lean_object* v_a_747_; lean_object* v___x_748_; 
v_a_747_ = lean_ctor_get(v___x_746_, 0);
lean_inc(v_a_747_);
lean_dec_ref_known(v___x_746_, 1);
v___x_748_ = l_Lean_Meta_letToHave(v_a_747_, v___y_714_, v___y_715_, v___y_716_, v___y_717_);
if (lean_obj_tag(v___x_748_) == 0)
{
lean_object* v_a_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_832_; 
v_a_749_ = lean_ctor_get(v___x_748_, 0);
v_isSharedCheck_832_ = !lean_is_exclusive(v___x_748_);
if (v_isSharedCheck_832_ == 0)
{
v___x_751_ = v___x_748_;
v_isShared_752_ = v_isSharedCheck_832_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_a_749_);
lean_dec(v___x_748_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_832_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v_modifiers_757_; lean_object* v_levelParams_758_; lean_object* v_declName_759_; lean_object* v_env_760_; uint8_t v_isUnsafe_761_; lean_object* v___x_762_; lean_object* v___x_763_; uint32_t v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; uint8_t v___y_768_; 
v___x_753_ = lean_st_ref_get(v___y_717_);
v___x_754_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_755_ = lean_usize_to_nat(v_i_712_);
v___x_756_ = lean_array_get_borrowed(v___x_754_, v_preDefs_709_, v___x_755_);
lean_dec(v___x_755_);
v_modifiers_757_ = lean_ctor_get(v___x_756_, 2);
v_levelParams_758_ = lean_ctor_get(v___x_756_, 1);
v_declName_759_ = lean_ctor_get(v___x_756_, 3);
v_env_760_ = lean_ctor_get(v___x_753_, 0);
lean_inc_ref(v_env_760_);
lean_dec(v___x_753_);
v_isUnsafe_761_ = lean_ctor_get_uint8(v_modifiers_757_, sizeof(void*)*3 + 4);
v___x_762_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg___closed__1));
lean_inc(v_declName_759_);
v___x_763_ = l_Lean_Name_append(v_declName_759_, v___x_762_);
lean_inc(v_a_745_);
v___x_764_ = l_Lean_getMaxHeight(v_env_760_, v_a_745_);
lean_inc(v_levelParams_758_);
lean_inc(v___x_763_);
v___x_765_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_765_, 0, v___x_763_);
lean_ctor_set(v___x_765_, 1, v_levelParams_758_);
lean_ctor_set(v___x_765_, 2, v_a_749_);
v___x_766_ = lean_box(1);
if (v_isUnsafe_761_ == 0)
{
uint8_t v___x_830_; 
v___x_830_ = 1;
v___y_768_ = v___x_830_;
goto v___jp_767_;
}
else
{
uint8_t v___x_831_; 
v___x_831_ = 0;
v___y_768_ = v___x_831_;
goto v___jp_767_;
}
v___jp_767_:
{
lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_773_; 
v___x_769_ = lean_box(0);
lean_inc(v___x_763_);
v___x_770_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_770_, 0, v___x_763_);
lean_ctor_set(v___x_770_, 1, v___x_769_);
v___x_771_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_771_, 0, v___x_765_);
lean_ctor_set(v___x_771_, 1, v_a_745_);
lean_ctor_set(v___x_771_, 2, v___x_766_);
lean_ctor_set(v___x_771_, 3, v___x_770_);
lean_ctor_set_uint8(v___x_771_, sizeof(void*)*4, v___y_768_);
if (v_isShared_752_ == 0)
{
lean_ctor_set_tag(v___x_751_, 1);
lean_ctor_set(v___x_751_, 0, v___x_771_);
v___x_773_ = v___x_751_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v___x_771_);
v___x_773_ = v_reuseFailAlloc_829_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
lean_object* v___x_774_; 
v___x_774_ = l_Lean_addDecl(v___x_773_, v_a_708_, v___y_716_, v___y_717_);
if (lean_obj_tag(v___x_774_) == 0)
{
lean_object* v___x_775_; lean_object* v_env_776_; lean_object* v_nextMacroScope_777_; lean_object* v_ngen_778_; lean_object* v_auxDeclNGen_779_; lean_object* v_traceState_780_; lean_object* v_messages_781_; lean_object* v_infoState_782_; lean_object* v_snapshotTasks_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_819_; 
lean_dec_ref_known(v___x_774_, 1);
v___x_775_ = lean_st_ref_take(v___y_717_);
v_env_776_ = lean_ctor_get(v___x_775_, 0);
v_nextMacroScope_777_ = lean_ctor_get(v___x_775_, 1);
v_ngen_778_ = lean_ctor_get(v___x_775_, 2);
v_auxDeclNGen_779_ = lean_ctor_get(v___x_775_, 3);
v_traceState_780_ = lean_ctor_get(v___x_775_, 4);
v_messages_781_ = lean_ctor_get(v___x_775_, 6);
v_infoState_782_ = lean_ctor_get(v___x_775_, 7);
v_snapshotTasks_783_ = lean_ctor_get(v___x_775_, 8);
v_isSharedCheck_819_ = !lean_is_exclusive(v___x_775_);
if (v_isSharedCheck_819_ == 0)
{
lean_object* v_unused_820_; 
v_unused_820_ = lean_ctor_get(v___x_775_, 5);
lean_dec(v_unused_820_);
v___x_785_ = v___x_775_;
v_isShared_786_ = v_isSharedCheck_819_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_snapshotTasks_783_);
lean_inc(v_infoState_782_);
lean_inc(v_messages_781_);
lean_inc(v_traceState_780_);
lean_inc(v_auxDeclNGen_779_);
lean_inc(v_ngen_778_);
lean_inc(v_nextMacroScope_777_);
lean_inc(v_env_776_);
lean_dec(v___x_775_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_819_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_790_; 
lean_inc(v___x_763_);
v___x_787_ = l_Lean_setDefHeightOverride(v_env_776_, v___x_763_, v___x_764_);
v___x_788_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__2);
if (v_isShared_786_ == 0)
{
lean_ctor_set(v___x_785_, 5, v___x_788_);
lean_ctor_set(v___x_785_, 0, v___x_787_);
v___x_790_ = v___x_785_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v___x_787_);
lean_ctor_set(v_reuseFailAlloc_818_, 1, v_nextMacroScope_777_);
lean_ctor_set(v_reuseFailAlloc_818_, 2, v_ngen_778_);
lean_ctor_set(v_reuseFailAlloc_818_, 3, v_auxDeclNGen_779_);
lean_ctor_set(v_reuseFailAlloc_818_, 4, v_traceState_780_);
lean_ctor_set(v_reuseFailAlloc_818_, 5, v___x_788_);
lean_ctor_set(v_reuseFailAlloc_818_, 6, v_messages_781_);
lean_ctor_set(v_reuseFailAlloc_818_, 7, v_infoState_782_);
lean_ctor_set(v_reuseFailAlloc_818_, 8, v_snapshotTasks_783_);
v___x_790_ = v_reuseFailAlloc_818_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v_mctx_793_; lean_object* v_zetaDeltaFVarIds_794_; lean_object* v_postponed_795_; lean_object* v_diag_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_816_; 
v___x_791_ = lean_st_ref_put(v___y_717_, v___x_790_);
v___x_792_ = lean_st_ref_take(v___y_715_);
v_mctx_793_ = lean_ctor_get(v___x_792_, 0);
v_zetaDeltaFVarIds_794_ = lean_ctor_get(v___x_792_, 2);
v_postponed_795_ = lean_ctor_get(v___x_792_, 3);
v_diag_796_ = lean_ctor_get(v___x_792_, 4);
v_isSharedCheck_816_ = !lean_is_exclusive(v___x_792_);
if (v_isSharedCheck_816_ == 0)
{
lean_object* v_unused_817_; 
v_unused_817_ = lean_ctor_get(v___x_792_, 1);
lean_dec(v_unused_817_);
v___x_798_ = v___x_792_;
v_isShared_799_ = v_isSharedCheck_816_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_diag_796_);
lean_inc(v_postponed_795_);
lean_inc(v_zetaDeltaFVarIds_794_);
lean_inc(v_mctx_793_);
lean_dec(v___x_792_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_816_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_800_; lean_object* v___x_802_; 
v___x_800_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__3, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__3);
if (v_isShared_799_ == 0)
{
lean_ctor_set(v___x_798_, 1, v___x_800_);
v___x_802_ = v___x_798_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_mctx_793_);
lean_ctor_set(v_reuseFailAlloc_815_, 1, v___x_800_);
lean_ctor_set(v_reuseFailAlloc_815_, 2, v_zetaDeltaFVarIds_794_);
lean_ctor_set(v_reuseFailAlloc_815_, 3, v_postponed_795_);
lean_ctor_set(v_reuseFailAlloc_815_, 4, v_diag_796_);
v___x_802_ = v_reuseFailAlloc_815_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
lean_object* v___x_803_; lean_object* v___x_804_; 
v___x_803_ = lean_st_ref_put(v___y_715_, v___x_802_);
lean_inc(v___x_763_);
v___x_804_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16(v___x_763_, v___y_714_, v___y_715_, v___y_716_, v___y_717_);
if (lean_obj_tag(v___x_804_) == 0)
{
lean_object* v___x_805_; lean_object* v___x_806_; 
lean_dec_ref_known(v___x_804_, 1);
lean_inc(v___x_710_);
v___x_805_ = l_Lean_mkConst(v___x_763_, v___x_710_);
v___x_806_ = l_Lean_mkAppN(v___x_805_, v_xs_707_);
v_a_725_ = v___x_806_;
goto v___jp_724_;
}
else
{
lean_object* v_a_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_814_; 
lean_dec(v___x_763_);
lean_dec_ref(v_bs_x27_723_);
lean_dec(v___x_710_);
v_a_807_ = lean_ctor_get(v___x_804_, 0);
v_isSharedCheck_814_ = !lean_is_exclusive(v___x_804_);
if (v_isSharedCheck_814_ == 0)
{
v___x_809_ = v___x_804_;
v_isShared_810_ = v_isSharedCheck_814_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_a_807_);
lean_dec(v___x_804_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_814_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v___x_812_; 
if (v_isShared_810_ == 0)
{
v___x_812_ = v___x_809_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v_a_807_);
v___x_812_ = v_reuseFailAlloc_813_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
return v___x_812_;
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
lean_object* v_a_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_828_; 
lean_dec(v___x_763_);
lean_dec_ref(v_bs_x27_723_);
lean_dec(v___x_710_);
v_a_821_ = lean_ctor_get(v___x_774_, 0);
v_isSharedCheck_828_ = !lean_is_exclusive(v___x_774_);
if (v_isSharedCheck_828_ == 0)
{
v___x_823_ = v___x_774_;
v_isShared_824_ = v_isSharedCheck_828_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_a_821_);
lean_dec(v___x_774_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_828_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v___x_826_; 
if (v_isShared_824_ == 0)
{
v___x_826_ = v___x_823_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v_a_821_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
return v___x_826_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_745_);
v___y_731_ = v___x_748_;
goto v___jp_730_;
}
}
else
{
lean_dec(v_a_745_);
v___y_731_ = v___x_746_;
goto v___jp_730_;
}
}
else
{
v___y_731_ = v___x_744_;
goto v___jp_730_;
}
}
else
{
v___y_731_ = v___x_742_;
goto v___jp_730_;
}
v___jp_724_:
{
size_t v___x_726_; size_t v___x_727_; lean_object* v___x_728_; 
v___x_726_ = ((size_t)1ULL);
v___x_727_ = lean_usize_add(v_i_712_, v___x_726_);
v___x_728_ = lean_array_uset(v_bs_x27_723_, v_i_712_, v_a_725_);
v_i_712_ = v___x_727_;
v_bs_713_ = v___x_728_;
goto _start;
}
v___jp_730_:
{
if (lean_obj_tag(v___y_731_) == 0)
{
lean_object* v_a_732_; 
v_a_732_ = lean_ctor_get(v___y_731_, 0);
lean_inc(v_a_732_);
lean_dec_ref_known(v___y_731_, 1);
v_a_725_ = v_a_732_;
goto v___jp_724_;
}
else
{
lean_object* v_a_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_740_; 
lean_dec_ref(v_bs_x27_723_);
lean_dec(v___x_710_);
v_a_733_ = lean_ctor_get(v___y_731_, 0);
v_isSharedCheck_740_ = !lean_is_exclusive(v___y_731_);
if (v_isSharedCheck_740_ == 0)
{
v___x_735_ = v___y_731_;
v_isShared_736_ = v_isSharedCheck_740_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_a_733_);
lean_dec(v___y_731_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_740_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v___x_738_; 
if (v_isShared_736_ == 0)
{
v___x_738_ = v___x_735_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v_a_733_);
v___x_738_ = v_reuseFailAlloc_739_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
return v___x_738_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg___boxed(lean_object* v_xs_833_, lean_object* v_a_834_, lean_object* v_preDefs_835_, lean_object* v___x_836_, lean_object* v_sz_837_, lean_object* v_i_838_, lean_object* v_bs_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_){
_start:
{
uint8_t v_a_25607__boxed_845_; size_t v_sz_boxed_846_; size_t v_i_boxed_847_; lean_object* v_res_848_; 
v_a_25607__boxed_845_ = lean_unbox(v_a_834_);
v_sz_boxed_846_ = lean_unbox_usize(v_sz_837_);
lean_dec(v_sz_837_);
v_i_boxed_847_ = lean_unbox_usize(v_i_838_);
lean_dec(v_i_838_);
v_res_848_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg(v_xs_833_, v_a_25607__boxed_845_, v_preDefs_835_, v___x_836_, v_sz_boxed_846_, v_i_boxed_847_, v_bs_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_);
lean_dec(v___y_843_);
lean_dec_ref(v___y_842_);
lean_dec(v___y_841_);
lean_dec_ref(v___y_840_);
lean_dec_ref(v_preDefs_835_);
lean_dec_ref(v_xs_833_);
return v_res_848_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___lam__0(lean_object* v_fixedParamPerms_849_, lean_object* v___x_850_, lean_object* v___x_851_, lean_object* v_xs_852_, lean_object* v_snd_853_, uint8_t v___x_854_, lean_object* v_ys_855_, lean_object* v_x_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_){
_start:
{
lean_object* v_perms_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; uint8_t v___x_866_; uint8_t v___x_867_; lean_object* v___x_868_; 
v_perms_862_ = lean_ctor_get(v_fixedParamPerms_849_, 1);
v___x_863_ = lean_array_get_borrowed(v___x_850_, v_perms_862_, v___x_851_);
lean_inc_ref(v_ys_855_);
lean_inc(v___x_863_);
v___x_864_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v___x_863_, v_xs_852_, v_ys_855_);
v___x_865_ = l_Lean_Expr_beta(v_snd_853_, v_ys_855_);
v___x_866_ = 0;
v___x_867_ = 1;
v___x_868_ = l_Lean_Meta_mkLambdaFVars(v___x_864_, v___x_865_, v___x_866_, v___x_854_, v___x_866_, v___x_854_, v___x_867_, v___y_857_, v___y_858_, v___y_859_, v___y_860_);
lean_dec_ref(v___x_864_);
return v___x_868_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___lam__0___boxed(lean_object* v_fixedParamPerms_869_, lean_object* v___x_870_, lean_object* v___x_871_, lean_object* v_xs_872_, lean_object* v_snd_873_, lean_object* v___x_874_, lean_object* v_ys_875_, lean_object* v_x_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_){
_start:
{
uint8_t v___x_25830__boxed_882_; lean_object* v_res_883_; 
v___x_25830__boxed_882_ = lean_unbox(v___x_874_);
v_res_883_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___lam__0(v_fixedParamPerms_869_, v___x_870_, v___x_871_, v_xs_872_, v_snd_873_, v___x_25830__boxed_882_, v_ys_875_, v_x_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_);
lean_dec(v___y_880_);
lean_dec_ref(v___y_879_);
lean_dec(v___y_878_);
lean_dec_ref(v___y_877_);
lean_dec_ref(v_x_876_);
lean_dec_ref(v_xs_872_);
lean_dec(v___x_871_);
lean_dec_ref(v___x_870_);
lean_dec_ref(v_fixedParamPerms_869_);
return v_res_883_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_884_; 
v___x_884_ = l_Array_instInhabited(lean_box(0));
return v___x_884_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg(lean_object* v_fixedParamPerms_885_, lean_object* v_xs_886_, size_t v_sz_887_, size_t v_i_888_, lean_object* v_bs_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_){
_start:
{
uint8_t v___x_895_; 
v___x_895_ = lean_usize_dec_lt(v_i_888_, v_sz_887_);
if (v___x_895_ == 0)
{
lean_object* v___x_896_; 
lean_dec_ref(v_xs_886_);
lean_dec_ref(v_fixedParamPerms_885_);
v___x_896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_896_, 0, v_bs_889_);
return v___x_896_;
}
else
{
lean_object* v_v_897_; lean_object* v_fst_898_; lean_object* v_snd_899_; lean_object* v___x_900_; lean_object* v_bs_x27_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___f_905_; uint8_t v___x_906_; lean_object* v___x_907_; 
v_v_897_ = lean_array_uget_borrowed(v_bs_889_, v_i_888_);
v_fst_898_ = lean_ctor_get(v_v_897_, 0);
lean_inc(v_fst_898_);
v_snd_899_ = lean_ctor_get(v_v_897_, 1);
lean_inc(v_snd_899_);
v___x_900_ = lean_unsigned_to_nat(0u);
v_bs_x27_901_ = lean_array_uset(v_bs_889_, v_i_888_, v___x_900_);
v___x_902_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0);
v___x_903_ = lean_usize_to_nat(v_i_888_);
v___x_904_ = lean_box(v___x_895_);
lean_inc_ref(v_xs_886_);
lean_inc_ref(v_fixedParamPerms_885_);
v___f_905_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___lam__0___boxed), 13, 6);
lean_closure_set(v___f_905_, 0, v_fixedParamPerms_885_);
lean_closure_set(v___f_905_, 1, v___x_902_);
lean_closure_set(v___f_905_, 2, v___x_903_);
lean_closure_set(v___f_905_, 3, v_xs_886_);
lean_closure_set(v___f_905_, 4, v_snd_899_);
lean_closure_set(v___f_905_, 5, v___x_904_);
v___x_906_ = 0;
v___x_907_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg(v_fst_898_, v___f_905_, v___x_906_, v___y_890_, v___y_891_, v___y_892_, v___y_893_);
if (lean_obj_tag(v___x_907_) == 0)
{
lean_object* v_a_908_; size_t v___x_909_; size_t v___x_910_; lean_object* v___x_911_; 
v_a_908_ = lean_ctor_get(v___x_907_, 0);
lean_inc(v_a_908_);
lean_dec_ref_known(v___x_907_, 1);
v___x_909_ = ((size_t)1ULL);
v___x_910_ = lean_usize_add(v_i_888_, v___x_909_);
v___x_911_ = lean_array_uset(v_bs_x27_901_, v_i_888_, v_a_908_);
v_i_888_ = v___x_910_;
v_bs_889_ = v___x_911_;
goto _start;
}
else
{
lean_object* v_a_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_920_; 
lean_dec_ref(v_bs_x27_901_);
lean_dec_ref(v_xs_886_);
lean_dec_ref(v_fixedParamPerms_885_);
v_a_913_ = lean_ctor_get(v___x_907_, 0);
v_isSharedCheck_920_ = !lean_is_exclusive(v___x_907_);
if (v_isSharedCheck_920_ == 0)
{
v___x_915_ = v___x_907_;
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_a_913_);
lean_dec(v___x_907_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v___x_918_; 
if (v_isShared_916_ == 0)
{
v___x_918_ = v___x_915_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v_a_913_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
return v___x_918_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___boxed(lean_object* v_fixedParamPerms_921_, lean_object* v_xs_922_, lean_object* v_sz_923_, lean_object* v_i_924_, lean_object* v_bs_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_){
_start:
{
size_t v_sz_boxed_931_; size_t v_i_boxed_932_; lean_object* v_res_933_; 
v_sz_boxed_931_ = lean_unbox_usize(v_sz_923_);
lean_dec(v_sz_923_);
v_i_boxed_932_ = lean_unbox_usize(v_i_924_);
lean_dec(v_i_924_);
v_res_933_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg(v_fixedParamPerms_921_, v_xs_922_, v_sz_boxed_931_, v_i_boxed_932_, v_bs_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_);
lean_dec(v___y_929_);
lean_dec_ref(v___y_928_);
lean_dec(v___y_927_);
lean_dec_ref(v___y_926_);
return v_res_933_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(lean_object* v_a_934_, lean_object* v_a_935_){
_start:
{
if (lean_obj_tag(v_a_934_) == 0)
{
lean_object* v___x_936_; 
v___x_936_ = l_List_reverse___redArg(v_a_935_);
return v___x_936_;
}
else
{
lean_object* v_head_937_; lean_object* v_tail_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_947_; 
v_head_937_ = lean_ctor_get(v_a_934_, 0);
v_tail_938_ = lean_ctor_get(v_a_934_, 1);
v_isSharedCheck_947_ = !lean_is_exclusive(v_a_934_);
if (v_isSharedCheck_947_ == 0)
{
v___x_940_ = v_a_934_;
v_isShared_941_ = v_isSharedCheck_947_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_tail_938_);
lean_inc(v_head_937_);
lean_dec(v_a_934_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_947_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v___x_942_; lean_object* v___x_944_; 
v___x_942_ = l_Lean_MessageData_ofExpr(v_head_937_);
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 1, v_a_935_);
lean_ctor_set(v___x_940_, 0, v___x_942_);
v___x_944_ = v___x_940_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v___x_942_);
lean_ctor_set(v_reuseFailAlloc_946_, 1, v_a_935_);
v___x_944_ = v_reuseFailAlloc_946_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
v_a_934_ = v_tail_938_;
v_a_935_ = v___x_944_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__15(lean_object* v_a_948_, lean_object* v_a_949_){
_start:
{
if (lean_obj_tag(v_a_948_) == 0)
{
lean_object* v___x_950_; 
v___x_950_ = l_List_reverse___redArg(v_a_949_);
return v___x_950_;
}
else
{
lean_object* v_head_951_; lean_object* v_tail_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_961_; 
v_head_951_ = lean_ctor_get(v_a_948_, 0);
v_tail_952_ = lean_ctor_get(v_a_948_, 1);
v_isSharedCheck_961_ = !lean_is_exclusive(v_a_948_);
if (v_isSharedCheck_961_ == 0)
{
v___x_954_ = v_a_948_;
v_isShared_955_ = v_isSharedCheck_961_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_tail_952_);
lean_inc(v_head_951_);
lean_dec(v_a_948_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_961_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v___x_956_; lean_object* v___x_958_; 
v___x_956_ = l_Lean_mkLevelParam(v_head_951_);
if (v_isShared_955_ == 0)
{
lean_ctor_set(v___x_954_, 1, v_a_949_);
lean_ctor_set(v___x_954_, 0, v___x_956_);
v___x_958_ = v___x_954_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v___x_956_);
lean_ctor_set(v_reuseFailAlloc_960_, 1, v_a_949_);
v___x_958_ = v_reuseFailAlloc_960_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
v_a_948_ = v_tail_952_;
v_a_949_ = v___x_958_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__0(void){
_start:
{
lean_object* v___x_962_; 
v___x_962_ = l_instMonadEIO(lean_box(0));
return v___x_962_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__5(void){
_start:
{
lean_object* v___x_967_; 
v___x_967_ = l_Array_instInhabited(lean_box(0));
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg(lean_object* v_msg_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_){
_start:
{
lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v_toApplicative_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_1037_; 
v___x_974_ = lean_obj_once(&l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__0, &l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__0_once, _init_l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__0);
v___x_975_ = l_StateRefT_x27_instMonad___redArg(v___x_974_);
v_toApplicative_976_ = lean_ctor_get(v___x_975_, 0);
v_isSharedCheck_1037_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_1037_ == 0)
{
lean_object* v_unused_1038_; 
v_unused_1038_ = lean_ctor_get(v___x_975_, 1);
lean_dec(v_unused_1038_);
v___x_978_ = v___x_975_;
v_isShared_979_ = v_isSharedCheck_1037_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_toApplicative_976_);
lean_dec(v___x_975_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_1037_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v_toFunctor_980_; lean_object* v_toSeq_981_; lean_object* v_toSeqLeft_982_; lean_object* v_toSeqRight_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_1035_; 
v_toFunctor_980_ = lean_ctor_get(v_toApplicative_976_, 0);
v_toSeq_981_ = lean_ctor_get(v_toApplicative_976_, 2);
v_toSeqLeft_982_ = lean_ctor_get(v_toApplicative_976_, 3);
v_toSeqRight_983_ = lean_ctor_get(v_toApplicative_976_, 4);
v_isSharedCheck_1035_ = !lean_is_exclusive(v_toApplicative_976_);
if (v_isSharedCheck_1035_ == 0)
{
lean_object* v_unused_1036_; 
v_unused_1036_ = lean_ctor_get(v_toApplicative_976_, 1);
lean_dec(v_unused_1036_);
v___x_985_ = v_toApplicative_976_;
v_isShared_986_ = v_isSharedCheck_1035_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_toSeqRight_983_);
lean_inc(v_toSeqLeft_982_);
lean_inc(v_toSeq_981_);
lean_inc(v_toFunctor_980_);
lean_dec(v_toApplicative_976_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_1035_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
lean_object* v___f_987_; lean_object* v___f_988_; lean_object* v___f_989_; lean_object* v___f_990_; lean_object* v___x_991_; lean_object* v___f_992_; lean_object* v___f_993_; lean_object* v___f_994_; lean_object* v___x_996_; 
v___f_987_ = ((lean_object*)(l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__1));
v___f_988_ = ((lean_object*)(l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__2));
lean_inc_ref(v_toFunctor_980_);
v___f_989_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_989_, 0, v_toFunctor_980_);
v___f_990_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_990_, 0, v_toFunctor_980_);
v___x_991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_991_, 0, v___f_989_);
lean_ctor_set(v___x_991_, 1, v___f_990_);
v___f_992_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_992_, 0, v_toSeqRight_983_);
v___f_993_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_993_, 0, v_toSeqLeft_982_);
v___f_994_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_994_, 0, v_toSeq_981_);
if (v_isShared_986_ == 0)
{
lean_ctor_set(v___x_985_, 4, v___f_992_);
lean_ctor_set(v___x_985_, 3, v___f_993_);
lean_ctor_set(v___x_985_, 2, v___f_994_);
lean_ctor_set(v___x_985_, 1, v___f_987_);
lean_ctor_set(v___x_985_, 0, v___x_991_);
v___x_996_ = v___x_985_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v___x_991_);
lean_ctor_set(v_reuseFailAlloc_1034_, 1, v___f_987_);
lean_ctor_set(v_reuseFailAlloc_1034_, 2, v___f_994_);
lean_ctor_set(v_reuseFailAlloc_1034_, 3, v___f_993_);
lean_ctor_set(v_reuseFailAlloc_1034_, 4, v___f_992_);
v___x_996_ = v_reuseFailAlloc_1034_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
lean_object* v___x_998_; 
if (v_isShared_979_ == 0)
{
lean_ctor_set(v___x_978_, 1, v___f_988_);
lean_ctor_set(v___x_978_, 0, v___x_996_);
v___x_998_ = v___x_978_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v___x_996_);
lean_ctor_set(v_reuseFailAlloc_1033_, 1, v___f_988_);
v___x_998_ = v_reuseFailAlloc_1033_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
lean_object* v___x_999_; lean_object* v_toApplicative_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1031_; 
v___x_999_ = l_StateRefT_x27_instMonad___redArg(v___x_998_);
v_toApplicative_1000_ = lean_ctor_get(v___x_999_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1031_ == 0)
{
lean_object* v_unused_1032_; 
v_unused_1032_ = lean_ctor_get(v___x_999_, 1);
lean_dec(v_unused_1032_);
v___x_1002_ = v___x_999_;
v_isShared_1003_ = v_isSharedCheck_1031_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_toApplicative_1000_);
lean_dec(v___x_999_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1031_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v_toFunctor_1004_; lean_object* v_toSeq_1005_; lean_object* v_toSeqLeft_1006_; lean_object* v_toSeqRight_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1029_; 
v_toFunctor_1004_ = lean_ctor_get(v_toApplicative_1000_, 0);
v_toSeq_1005_ = lean_ctor_get(v_toApplicative_1000_, 2);
v_toSeqLeft_1006_ = lean_ctor_get(v_toApplicative_1000_, 3);
v_toSeqRight_1007_ = lean_ctor_get(v_toApplicative_1000_, 4);
v_isSharedCheck_1029_ = !lean_is_exclusive(v_toApplicative_1000_);
if (v_isSharedCheck_1029_ == 0)
{
lean_object* v_unused_1030_; 
v_unused_1030_ = lean_ctor_get(v_toApplicative_1000_, 1);
lean_dec(v_unused_1030_);
v___x_1009_ = v_toApplicative_1000_;
v_isShared_1010_ = v_isSharedCheck_1029_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_toSeqRight_1007_);
lean_inc(v_toSeqLeft_1006_);
lean_inc(v_toSeq_1005_);
lean_inc(v_toFunctor_1004_);
lean_dec(v_toApplicative_1000_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1029_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___f_1011_; lean_object* v___f_1012_; lean_object* v___f_1013_; lean_object* v___f_1014_; lean_object* v___x_1015_; lean_object* v___f_1016_; lean_object* v___f_1017_; lean_object* v___f_1018_; lean_object* v___x_1020_; 
v___f_1011_ = ((lean_object*)(l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__3));
v___f_1012_ = ((lean_object*)(l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__4));
lean_inc_ref(v_toFunctor_1004_);
v___f_1013_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1013_, 0, v_toFunctor_1004_);
v___f_1014_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1014_, 0, v_toFunctor_1004_);
v___x_1015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1015_, 0, v___f_1013_);
lean_ctor_set(v___x_1015_, 1, v___f_1014_);
v___f_1016_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1016_, 0, v_toSeqRight_1007_);
v___f_1017_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1017_, 0, v_toSeqLeft_1006_);
v___f_1018_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1018_, 0, v_toSeq_1005_);
if (v_isShared_1010_ == 0)
{
lean_ctor_set(v___x_1009_, 4, v___f_1016_);
lean_ctor_set(v___x_1009_, 3, v___f_1017_);
lean_ctor_set(v___x_1009_, 2, v___f_1018_);
lean_ctor_set(v___x_1009_, 1, v___f_1011_);
lean_ctor_set(v___x_1009_, 0, v___x_1015_);
v___x_1020_ = v___x_1009_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v___x_1015_);
lean_ctor_set(v_reuseFailAlloc_1028_, 1, v___f_1011_);
lean_ctor_set(v_reuseFailAlloc_1028_, 2, v___f_1018_);
lean_ctor_set(v_reuseFailAlloc_1028_, 3, v___f_1017_);
lean_ctor_set(v_reuseFailAlloc_1028_, 4, v___f_1016_);
v___x_1020_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
lean_object* v___x_1022_; 
if (v_isShared_1003_ == 0)
{
lean_ctor_set(v___x_1002_, 1, v___f_1012_);
lean_ctor_set(v___x_1002_, 0, v___x_1020_);
v___x_1022_ = v___x_1002_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v___x_1020_);
lean_ctor_set(v_reuseFailAlloc_1027_, 1, v___f_1012_);
v___x_1022_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_21466__overap_1025_; lean_object* v___x_1026_; 
v___x_1023_ = lean_obj_once(&l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__5, &l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__5_once, _init_l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__5);
v___x_1024_ = l_instInhabitedOfMonad___redArg(v___x_1022_, v___x_1023_);
v___x_21466__overap_1025_ = lean_panic_fn_borrowed(v___x_1024_, v_msg_968_);
lean_dec(v___x_1024_);
lean_inc(v___y_972_);
lean_inc_ref(v___y_971_);
lean_inc(v___y_970_);
lean_inc_ref(v___y_969_);
v___x_1026_ = lean_apply_5(v___x_21466__overap_1025_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, lean_box(0));
return v___x_1026_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___boxed(lean_object* v_msg_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_){
_start:
{
lean_object* v_res_1045_; 
v_res_1045_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg(v_msg_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_);
lean_dec(v___y_1043_);
lean_dec_ref(v___y_1042_);
lean_dec(v___y_1041_);
lean_dec_ref(v___y_1040_);
return v_res_1045_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__13(lean_object* v_xs_1046_, size_t v_sz_1047_, size_t v_i_1048_, lean_object* v_bs_1049_){
_start:
{
uint8_t v___x_1050_; 
v___x_1050_ = lean_usize_dec_lt(v_i_1048_, v_sz_1047_);
if (v___x_1050_ == 0)
{
return v_bs_1049_;
}
else
{
lean_object* v___x_1051_; lean_object* v_v_1052_; lean_object* v___x_1053_; lean_object* v_bs_x27_1054_; lean_object* v___x_1055_; size_t v___x_1056_; size_t v___x_1057_; lean_object* v___x_1058_; 
v___x_1051_ = l_Lean_instInhabitedExpr;
v_v_1052_ = lean_array_uget(v_bs_1049_, v_i_1048_);
v___x_1053_ = lean_unsigned_to_nat(0u);
v_bs_x27_1054_ = lean_array_uset(v_bs_1049_, v_i_1048_, v___x_1053_);
v___x_1055_ = lean_array_get_borrowed(v___x_1051_, v_xs_1046_, v_v_1052_);
lean_dec(v_v_1052_);
v___x_1056_ = ((size_t)1ULL);
v___x_1057_ = lean_usize_add(v_i_1048_, v___x_1056_);
lean_inc(v___x_1055_);
v___x_1058_ = lean_array_uset(v_bs_x27_1054_, v_i_1048_, v___x_1055_);
v_i_1048_ = v___x_1057_;
v_bs_1049_ = v___x_1058_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__13___boxed(lean_object* v_xs_1060_, lean_object* v_sz_1061_, lean_object* v_i_1062_, lean_object* v_bs_1063_){
_start:
{
size_t v_sz_boxed_1064_; size_t v_i_boxed_1065_; lean_object* v_res_1066_; 
v_sz_boxed_1064_ = lean_unbox_usize(v_sz_1061_);
lean_dec(v_sz_1061_);
v_i_boxed_1065_ = lean_unbox_usize(v_i_1062_);
lean_dec(v_i_1062_);
v_res_1066_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__13(v_xs_1060_, v_sz_boxed_1064_, v_i_boxed_1065_, v_bs_1063_);
lean_dec_ref(v_xs_1060_);
return v_res_1066_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15___redArg(lean_object* v_xs_1067_, lean_object* v_f_1068_, lean_object* v_as_1069_, lean_object* v_bs_1070_, lean_object* v_i_1071_, lean_object* v_cs_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_){
_start:
{
lean_object* v___x_1078_; uint8_t v___x_1079_; 
v___x_1078_ = lean_array_get_size(v_as_1069_);
v___x_1079_ = lean_nat_dec_lt(v_i_1071_, v___x_1078_);
if (v___x_1079_ == 0)
{
lean_object* v___x_1080_; 
lean_dec(v_i_1071_);
lean_dec_ref(v_f_1068_);
v___x_1080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1080_, 0, v_cs_1072_);
return v___x_1080_;
}
else
{
lean_object* v___x_1081_; uint8_t v___x_1082_; 
v___x_1081_ = lean_array_get_size(v_bs_1070_);
v___x_1082_ = lean_nat_dec_lt(v_i_1071_, v___x_1081_);
if (v___x_1082_ == 0)
{
lean_object* v___x_1083_; 
lean_dec(v_i_1071_);
lean_dec_ref(v_f_1068_);
v___x_1083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1083_, 0, v_cs_1072_);
return v___x_1083_;
}
else
{
lean_object* v_a_1084_; lean_object* v_b_1085_; size_t v_sz_1086_; size_t v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; 
v_a_1084_ = lean_array_fget_borrowed(v_as_1069_, v_i_1071_);
v_b_1085_ = lean_array_fget_borrowed(v_bs_1070_, v_i_1071_);
v_sz_1086_ = lean_array_size(v_b_1085_);
v___x_1087_ = ((size_t)0ULL);
lean_inc(v_b_1085_);
v___x_1088_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__13(v_xs_1067_, v_sz_1086_, v___x_1087_, v_b_1085_);
lean_inc_ref(v_f_1068_);
lean_inc(v___y_1076_);
lean_inc_ref(v___y_1075_);
lean_inc(v___y_1074_);
lean_inc_ref(v___y_1073_);
lean_inc(v_a_1084_);
v___x_1089_ = lean_apply_7(v_f_1068_, v_a_1084_, v___x_1088_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, lean_box(0));
if (lean_obj_tag(v___x_1089_) == 0)
{
lean_object* v_a_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; 
v_a_1090_ = lean_ctor_get(v___x_1089_, 0);
lean_inc(v_a_1090_);
lean_dec_ref_known(v___x_1089_, 1);
v___x_1091_ = lean_unsigned_to_nat(1u);
v___x_1092_ = lean_nat_add(v_i_1071_, v___x_1091_);
lean_dec(v_i_1071_);
v___x_1093_ = lean_array_push(v_cs_1072_, v_a_1090_);
v_i_1071_ = v___x_1092_;
v_cs_1072_ = v___x_1093_;
goto _start;
}
else
{
lean_object* v_a_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1102_; 
lean_dec_ref(v_cs_1072_);
lean_dec(v_i_1071_);
lean_dec_ref(v_f_1068_);
v_a_1095_ = lean_ctor_get(v___x_1089_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v___x_1089_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1097_ = v___x_1089_;
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_a_1095_);
lean_dec(v___x_1089_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
lean_object* v___x_1100_; 
if (v_isShared_1098_ == 0)
{
v___x_1100_ = v___x_1097_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v_a_1095_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
return v___x_1100_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15___redArg___boxed(lean_object* v_xs_1103_, lean_object* v_f_1104_, lean_object* v_as_1105_, lean_object* v_bs_1106_, lean_object* v_i_1107_, lean_object* v_cs_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_){
_start:
{
lean_object* v_res_1114_; 
v_res_1114_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15___redArg(v_xs_1103_, v_f_1104_, v_as_1105_, v_bs_1106_, v_i_1107_, v_cs_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_);
lean_dec(v___y_1112_);
lean_dec_ref(v___y_1111_);
lean_dec(v___y_1110_);
lean_dec_ref(v___y_1109_);
lean_dec_ref(v_bs_1106_);
lean_dec_ref(v_as_1105_);
lean_dec_ref(v_xs_1103_);
return v_res_1114_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; 
v___x_1118_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__2));
v___x_1119_ = lean_unsigned_to_nat(2u);
v___x_1120_ = lean_unsigned_to_nat(73u);
v___x_1121_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__1));
v___x_1122_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__0));
v___x_1123_ = l_mkPanicMessageWithDecl(v___x_1122_, v___x_1121_, v___x_1120_, v___x_1119_, v___x_1118_);
return v___x_1123_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; 
v___x_1125_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__4));
v___x_1126_ = lean_unsigned_to_nat(2u);
v___x_1127_ = lean_unsigned_to_nat(74u);
v___x_1128_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__1));
v___x_1129_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__0));
v___x_1130_ = l_mkPanicMessageWithDecl(v___x_1129_, v___x_1128_, v___x_1127_, v___x_1126_, v___x_1125_);
return v___x_1130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg(lean_object* v_f_1133_, lean_object* v_positions_1134_, lean_object* v_ys_1135_, lean_object* v_xs_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_){
_start:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; uint8_t v___x_1144_; 
v___x_1142_ = lean_array_get_size(v_positions_1134_);
v___x_1143_ = lean_array_get_size(v_ys_1135_);
v___x_1144_ = lean_nat_dec_eq(v___x_1142_, v___x_1143_);
if (v___x_1144_ == 0)
{
lean_object* v___x_1145_; lean_object* v___x_1146_; 
lean_dec_ref(v_f_1133_);
v___x_1145_ = lean_obj_once(&l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__3, &l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__3_once, _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__3);
v___x_1146_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg(v___x_1145_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_);
return v___x_1146_;
}
else
{
lean_object* v___x_1147_; lean_object* v___x_1148_; uint8_t v___x_1149_; 
v___x_1147_ = l_Lean_Elab_Structural_Positions_numIndices(v_positions_1134_);
v___x_1148_ = lean_array_get_size(v_xs_1136_);
v___x_1149_ = lean_nat_dec_eq(v___x_1147_, v___x_1148_);
lean_dec(v___x_1147_);
if (v___x_1149_ == 0)
{
lean_object* v___x_1150_; lean_object* v___x_1151_; 
lean_dec_ref(v_f_1133_);
v___x_1150_ = lean_obj_once(&l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__5, &l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__5_once, _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__5);
v___x_1151_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg(v___x_1150_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_);
return v___x_1151_;
}
else
{
lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1152_ = lean_unsigned_to_nat(0u);
v___x_1153_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__6));
v___x_1154_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15___redArg(v_xs_1136_, v_f_1133_, v_ys_1135_, v_positions_1134_, v___x_1152_, v___x_1153_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_);
return v___x_1154_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___boxed(lean_object* v_f_1155_, lean_object* v_positions_1156_, lean_object* v_ys_1157_, lean_object* v_xs_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_){
_start:
{
lean_object* v_res_1164_; 
v_res_1164_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg(v_f_1155_, v_positions_1156_, v_ys_1157_, v_xs_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_);
lean_dec(v___y_1162_);
lean_dec_ref(v___y_1161_);
lean_dec(v___y_1160_);
lean_dec_ref(v___y_1159_);
lean_dec_ref(v_xs_1158_);
lean_dec_ref(v_ys_1157_);
lean_dec_ref(v_positions_1156_);
return v_res_1164_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg(lean_object* v___x_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_funTypes_1168_, size_t v_sz_1169_, size_t v_i_1170_, lean_object* v_bs_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_){
_start:
{
uint8_t v___x_1177_; 
v___x_1177_ = lean_usize_dec_lt(v_i_1170_, v_sz_1169_);
if (v___x_1177_ == 0)
{
lean_object* v___x_1178_; 
lean_dec_ref(v_funTypes_1168_);
lean_dec_ref(v_a_1167_);
lean_dec_ref(v_a_1166_);
lean_dec_ref(v___x_1165_);
v___x_1178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1178_, 0, v_bs_1171_);
return v___x_1178_;
}
else
{
lean_object* v_v_1179_; lean_object* v_fst_1180_; lean_object* v_snd_1181_; lean_object* v___x_1182_; lean_object* v_bs_x27_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; 
v_v_1179_ = lean_array_uget_borrowed(v_bs_1171_, v_i_1170_);
v_fst_1180_ = lean_ctor_get(v_v_1179_, 0);
lean_inc(v_fst_1180_);
v_snd_1181_ = lean_ctor_get(v_v_1179_, 1);
lean_inc(v_snd_1181_);
v___x_1182_ = lean_unsigned_to_nat(0u);
v_bs_x27_1183_ = lean_array_uset(v_bs_1171_, v_i_1170_, v___x_1182_);
v___x_1184_ = lean_usize_to_nat(v_i_1170_);
lean_inc_ref(v_funTypes_1168_);
lean_inc_ref(v_a_1167_);
lean_inc_ref(v_a_1166_);
lean_inc_ref(v___x_1165_);
v___x_1185_ = l_Lean_Elab_Structural_mkBRecOnApp(v___x_1165_, v___x_1184_, v_a_1166_, v_a_1167_, v_funTypes_1168_, v_fst_1180_, v_snd_1181_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_);
if (lean_obj_tag(v___x_1185_) == 0)
{
lean_object* v_a_1186_; size_t v___x_1187_; size_t v___x_1188_; lean_object* v___x_1189_; 
v_a_1186_ = lean_ctor_get(v___x_1185_, 0);
lean_inc(v_a_1186_);
lean_dec_ref_known(v___x_1185_, 1);
v___x_1187_ = ((size_t)1ULL);
v___x_1188_ = lean_usize_add(v_i_1170_, v___x_1187_);
v___x_1189_ = lean_array_uset(v_bs_x27_1183_, v_i_1170_, v_a_1186_);
v_i_1170_ = v___x_1188_;
v_bs_1171_ = v___x_1189_;
goto _start;
}
else
{
lean_object* v_a_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1198_; 
lean_dec_ref(v_bs_x27_1183_);
lean_dec_ref(v_funTypes_1168_);
lean_dec_ref(v_a_1167_);
lean_dec_ref(v_a_1166_);
lean_dec_ref(v___x_1165_);
v_a_1191_ = lean_ctor_get(v___x_1185_, 0);
v_isSharedCheck_1198_ = !lean_is_exclusive(v___x_1185_);
if (v_isSharedCheck_1198_ == 0)
{
v___x_1193_ = v___x_1185_;
v_isShared_1194_ = v_isSharedCheck_1198_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_a_1191_);
lean_dec(v___x_1185_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1198_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v___x_1196_; 
if (v_isShared_1194_ == 0)
{
v___x_1196_ = v___x_1193_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v_a_1191_);
v___x_1196_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
return v___x_1196_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg___boxed(lean_object* v___x_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_funTypes_1202_, lean_object* v_sz_1203_, lean_object* v_i_1204_, lean_object* v_bs_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_){
_start:
{
size_t v_sz_boxed_1211_; size_t v_i_boxed_1212_; lean_object* v_res_1213_; 
v_sz_boxed_1211_ = lean_unbox_usize(v_sz_1203_);
lean_dec(v_sz_1203_);
v_i_boxed_1212_ = lean_unbox_usize(v_i_1204_);
lean_dec(v_i_1204_);
v_res_1213_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg(v___x_1199_, v_a_1200_, v_a_1201_, v_funTypes_1202_, v_sz_boxed_1211_, v_i_boxed_1212_, v_bs_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_);
lean_dec(v___y_1209_);
lean_dec_ref(v___y_1208_);
lean_dec(v___y_1207_);
lean_dec_ref(v___y_1206_);
return v_res_1213_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__2(void){
_start:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; 
v___x_1217_ = lean_box(0);
v___x_1218_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__1));
v___x_1219_ = l_Lean_Expr_const___override(v___x_1218_, v___x_1217_);
return v___x_1219_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__4(void){
_start:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; 
v___x_1221_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__3));
v___x_1222_ = l_Lean_stringToMessageData(v___x_1221_);
return v___x_1222_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__6(void){
_start:
{
lean_object* v___x_1224_; lean_object* v___x_1225_; 
v___x_1224_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__5));
v___x_1225_ = l_Lean_stringToMessageData(v___x_1224_);
return v___x_1225_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__8(void){
_start:
{
lean_object* v___x_1227_; lean_object* v___x_1228_; 
v___x_1227_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__7));
v___x_1228_ = l_Lean_stringToMessageData(v___x_1227_);
return v___x_1228_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__10(void){
_start:
{
lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___x_1230_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__9));
v___x_1231_ = l_Lean_stringToMessageData(v___x_1230_);
return v___x_1231_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__12(void){
_start:
{
lean_object* v___x_1233_; lean_object* v___x_1234_; 
v___x_1233_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__11));
v___x_1234_ = l_Lean_stringToMessageData(v___x_1233_);
return v___x_1234_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2(lean_object* v___f_1235_, lean_object* v_recArgInfos_1236_, lean_object* v_a_1237_, lean_object* v___x_1238_, size_t v___x_1239_, lean_object* v_fixedParamPerms_1240_, lean_object* v_xs_1241_, lean_object* v___x_1242_, lean_object* v_preDefs_1243_, lean_object* v_numIndices_1244_, lean_object* v___f_1245_, lean_object* v___x_1246_, uint8_t v_a_1247_, lean_object* v___x_1248_, lean_object* v_funTypes_1249_, lean_object* v_motives_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_){
_start:
{
lean_object* v___y_1257_; lean_object* v___y_1258_; lean_object* v___y_1259_; lean_object* v___y_1260_; lean_object* v___y_1261_; lean_object* v___y_1262_; lean_object* v___y_1297_; lean_object* v_FArgs_1298_; lean_object* v___y_1299_; lean_object* v___y_1300_; lean_object* v___y_1301_; lean_object* v___y_1302_; lean_object* v___y_1354_; lean_object* v___y_1355_; lean_object* v___y_1356_; lean_object* v___y_1357_; lean_object* v___y_1358_; lean_object* v___y_1359_; lean_object* v___y_1376_; lean_object* v___y_1377_; lean_object* v___y_1378_; lean_object* v___y_1379_; lean_object* v___y_1380_; lean_object* v___y_1381_; lean_object* v___y_1420_; lean_object* v___y_1421_; lean_object* v___y_1422_; lean_object* v___y_1423_; lean_object* v___x_1470_; 
lean_inc_ref(v___f_1235_);
lean_inc(v___y_1254_);
lean_inc_ref(v___y_1253_);
lean_inc(v___y_1252_);
lean_inc_ref(v___y_1251_);
v___x_1470_ = lean_apply_5(v___f_1235_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, lean_box(0));
if (lean_obj_tag(v___x_1470_) == 0)
{
lean_object* v_a_1471_; uint8_t v___x_1472_; 
v_a_1471_ = lean_ctor_get(v___x_1470_, 0);
lean_inc(v_a_1471_);
lean_dec_ref_known(v___x_1470_, 1);
v___x_1472_ = lean_unbox(v_a_1471_);
lean_dec(v_a_1471_);
if (v___x_1472_ == 0)
{
v___y_1420_ = v___y_1251_;
v___y_1421_ = v___y_1252_;
v___y_1422_ = v___y_1253_;
v___y_1423_ = v___y_1254_;
goto v___jp_1419_;
}
else
{
lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; 
v___x_1473_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__10, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__10);
lean_inc_ref(v_funTypes_1249_);
v___x_1474_ = lean_array_to_list(v_funTypes_1249_);
v___x_1475_ = lean_box(0);
v___x_1476_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_1474_, v___x_1475_);
v___x_1477_ = l_Lean_MessageData_ofList(v___x_1476_);
v___x_1478_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1478_, 0, v___x_1473_);
lean_ctor_set(v___x_1478_, 1, v___x_1477_);
v___x_1479_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__12, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__12_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__12);
v___x_1480_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1480_, 0, v___x_1478_);
lean_ctor_set(v___x_1480_, 1, v___x_1479_);
lean_inc_ref(v_motives_1250_);
v___x_1481_ = lean_array_to_list(v_motives_1250_);
v___x_1482_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_1481_, v___x_1475_);
v___x_1483_ = l_Lean_MessageData_ofList(v___x_1482_);
v___x_1484_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1484_, 0, v___x_1480_);
lean_ctor_set(v___x_1484_, 1, v___x_1483_);
lean_inc(v___x_1246_);
v___x_1485_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_1246_, v___x_1484_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_);
if (lean_obj_tag(v___x_1485_) == 0)
{
lean_dec_ref_known(v___x_1485_, 1);
v___y_1420_ = v___y_1251_;
v___y_1421_ = v___y_1252_;
v___y_1422_ = v___y_1253_;
v___y_1423_ = v___y_1254_;
goto v___jp_1419_;
}
else
{
lean_object* v_a_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1493_; 
lean_dec_ref(v_motives_1250_);
lean_dec_ref(v_funTypes_1249_);
lean_dec(v___x_1246_);
lean_dec_ref(v___f_1245_);
lean_dec_ref(v_preDefs_1243_);
lean_dec(v___x_1242_);
lean_dec_ref(v_xs_1241_);
lean_dec_ref(v_fixedParamPerms_1240_);
lean_dec_ref(v___x_1238_);
lean_dec_ref(v_recArgInfos_1236_);
lean_dec_ref(v___f_1235_);
v_a_1486_ = lean_ctor_get(v___x_1485_, 0);
v_isSharedCheck_1493_ = !lean_is_exclusive(v___x_1485_);
if (v_isSharedCheck_1493_ == 0)
{
v___x_1488_ = v___x_1485_;
v_isShared_1489_ = v_isSharedCheck_1493_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_a_1486_);
lean_dec(v___x_1485_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1493_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
lean_object* v___x_1491_; 
if (v_isShared_1489_ == 0)
{
v___x_1491_ = v___x_1488_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v_a_1486_);
v___x_1491_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
return v___x_1491_;
}
}
}
}
}
else
{
lean_object* v_a_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1501_; 
lean_dec_ref(v_motives_1250_);
lean_dec_ref(v_funTypes_1249_);
lean_dec(v___x_1246_);
lean_dec_ref(v___f_1245_);
lean_dec_ref(v_preDefs_1243_);
lean_dec(v___x_1242_);
lean_dec_ref(v_xs_1241_);
lean_dec_ref(v_fixedParamPerms_1240_);
lean_dec_ref(v___x_1238_);
lean_dec_ref(v_recArgInfos_1236_);
lean_dec_ref(v___f_1235_);
v_a_1494_ = lean_ctor_get(v___x_1470_, 0);
v_isSharedCheck_1501_ = !lean_is_exclusive(v___x_1470_);
if (v_isSharedCheck_1501_ == 0)
{
v___x_1496_ = v___x_1470_;
v_isShared_1497_ = v_isSharedCheck_1501_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_a_1494_);
lean_dec(v___x_1470_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1501_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
lean_object* v___x_1499_; 
if (v_isShared_1497_ == 0)
{
v___x_1499_ = v___x_1496_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v_a_1494_);
v___x_1499_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
return v___x_1499_;
}
}
}
v___jp_1256_:
{
lean_object* v___x_1263_; size_t v_sz_1264_; lean_object* v___x_1265_; 
v___x_1263_ = l_Array_zip___redArg(v_recArgInfos_1236_, v_a_1237_);
lean_dec_ref(v_recArgInfos_1236_);
v_sz_1264_ = lean_array_size(v___x_1263_);
v___x_1265_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg(v___x_1238_, v___y_1258_, v___y_1257_, v_funTypes_1249_, v_sz_1264_, v___x_1239_, v___x_1263_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_);
if (lean_obj_tag(v___x_1265_) == 0)
{
lean_object* v_a_1266_; lean_object* v___x_1267_; size_t v_sz_1268_; lean_object* v___x_1269_; 
v_a_1266_ = lean_ctor_get(v___x_1265_, 0);
lean_inc(v_a_1266_);
lean_dec_ref_known(v___x_1265_, 1);
v___x_1267_ = l_Array_zip___redArg(v_a_1237_, v_a_1266_);
lean_dec(v_a_1266_);
v_sz_1268_ = lean_array_size(v___x_1267_);
v___x_1269_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg(v_fixedParamPerms_1240_, v_xs_1241_, v_sz_1268_, v___x_1239_, v___x_1267_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_);
if (lean_obj_tag(v___x_1269_) == 0)
{
lean_object* v_a_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1279_; 
v_a_1270_ = lean_ctor_get(v___x_1269_, 0);
v_isSharedCheck_1279_ = !lean_is_exclusive(v___x_1269_);
if (v_isSharedCheck_1279_ == 0)
{
v___x_1272_ = v___x_1269_;
v_isShared_1273_ = v_isSharedCheck_1279_;
goto v_resetjp_1271_;
}
else
{
lean_inc(v_a_1270_);
lean_dec(v___x_1269_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1279_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1277_; 
v___x_1274_ = lean_mk_empty_array_with_capacity(v___x_1242_);
v___x_1275_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9(v_preDefs_1243_, v_a_1270_, v___x_1242_, v___x_1274_);
lean_dec(v_a_1270_);
lean_dec_ref(v_preDefs_1243_);
if (v_isShared_1273_ == 0)
{
lean_ctor_set(v___x_1272_, 0, v___x_1275_);
v___x_1277_ = v___x_1272_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v___x_1275_);
v___x_1277_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
return v___x_1277_;
}
}
}
else
{
lean_object* v_a_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1287_; 
lean_dec_ref(v_preDefs_1243_);
lean_dec(v___x_1242_);
v_a_1280_ = lean_ctor_get(v___x_1269_, 0);
v_isSharedCheck_1287_ = !lean_is_exclusive(v___x_1269_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1282_ = v___x_1269_;
v_isShared_1283_ = v_isSharedCheck_1287_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_a_1280_);
lean_dec(v___x_1269_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1287_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
lean_object* v___x_1285_; 
if (v_isShared_1283_ == 0)
{
v___x_1285_ = v___x_1282_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v_a_1280_);
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
else
{
lean_object* v_a_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1295_; 
lean_dec_ref(v_preDefs_1243_);
lean_dec(v___x_1242_);
lean_dec_ref(v_xs_1241_);
lean_dec_ref(v_fixedParamPerms_1240_);
v_a_1288_ = lean_ctor_get(v___x_1265_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1265_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1290_ = v___x_1265_;
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_a_1288_);
lean_dec(v___x_1265_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___x_1293_; 
if (v_isShared_1291_ == 0)
{
v___x_1293_ = v___x_1290_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v_a_1288_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
}
}
v___jp_1296_:
{
lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; 
lean_inc_ref(v___y_1297_);
lean_inc(v___x_1242_);
v___x_1303_ = lean_apply_1(v___y_1297_, v___x_1242_);
v___x_1304_ = lean_unsigned_to_nat(1u);
v___x_1305_ = lean_nat_add(v_numIndices_1244_, v___x_1304_);
v___x_1306_ = lean_box(0);
v___x_1307_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__2);
v___x_1308_ = lean_mk_array(v___x_1305_, v___x_1307_);
v___x_1309_ = l_Lean_mkAppN(v___x_1303_, v___x_1308_);
lean_dec_ref(v___x_1308_);
v___x_1310_ = lean_array_get_size(v___x_1238_);
v___x_1311_ = l_Lean_Meta_inferArgumentTypesN(v___x_1310_, v___x_1309_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_);
if (lean_obj_tag(v___x_1311_) == 0)
{
lean_object* v_a_1312_; lean_object* v___x_1313_; 
v_a_1312_ = lean_ctor_get(v___x_1311_, 0);
lean_inc(v_a_1312_);
lean_dec_ref_known(v___x_1311_, 1);
v___x_1313_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg(v___f_1245_, v___x_1238_, v_a_1312_, v_FArgs_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_);
lean_dec_ref(v_FArgs_1298_);
lean_dec(v_a_1312_);
if (lean_obj_tag(v___x_1313_) == 0)
{
lean_object* v_options_1314_; uint8_t v_hasTrace_1315_; 
v_options_1314_ = lean_ctor_get(v___y_1301_, 1);
v_hasTrace_1315_ = lean_ctor_get_uint8(v_options_1314_, sizeof(void*)*1);
if (v_hasTrace_1315_ == 0)
{
lean_object* v_a_1316_; 
lean_dec(v___x_1246_);
v_a_1316_ = lean_ctor_get(v___x_1313_, 0);
lean_inc(v_a_1316_);
lean_dec_ref_known(v___x_1313_, 1);
v___y_1257_ = v_a_1316_;
v___y_1258_ = v___y_1297_;
v___y_1259_ = v___y_1299_;
v___y_1260_ = v___y_1300_;
v___y_1261_ = v___y_1301_;
v___y_1262_ = v___y_1302_;
goto v___jp_1256_;
}
else
{
lean_object* v_toCold_1317_; lean_object* v_a_1318_; lean_object* v_inheritedTraceOptions_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; uint8_t v___x_1322_; 
v_toCold_1317_ = lean_ctor_get(v___y_1301_, 0);
v_a_1318_ = lean_ctor_get(v___x_1313_, 0);
lean_inc(v_a_1318_);
lean_dec_ref_known(v___x_1313_, 1);
v_inheritedTraceOptions_1319_ = lean_ctor_get(v_toCold_1317_, 4);
v___x_1320_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0___closed__1));
lean_inc(v___x_1246_);
v___x_1321_ = l_Lean_Name_append(v___x_1320_, v___x_1246_);
v___x_1322_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1319_, v_options_1314_, v___x_1321_);
lean_dec(v___x_1321_);
if (v___x_1322_ == 0)
{
lean_dec(v___x_1246_);
v___y_1257_ = v_a_1318_;
v___y_1258_ = v___y_1297_;
v___y_1259_ = v___y_1299_;
v___y_1260_ = v___y_1300_;
v___y_1261_ = v___y_1301_;
v___y_1262_ = v___y_1302_;
goto v___jp_1256_;
}
else
{
lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; 
v___x_1323_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__4);
lean_inc(v_a_1318_);
v___x_1324_ = lean_array_to_list(v_a_1318_);
v___x_1325_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_1324_, v___x_1306_);
v___x_1326_ = l_Lean_MessageData_ofList(v___x_1325_);
v___x_1327_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1327_, 0, v___x_1323_);
lean_ctor_set(v___x_1327_, 1, v___x_1326_);
v___x_1328_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_1246_, v___x_1327_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_);
if (lean_obj_tag(v___x_1328_) == 0)
{
lean_dec_ref_known(v___x_1328_, 1);
v___y_1257_ = v_a_1318_;
v___y_1258_ = v___y_1297_;
v___y_1259_ = v___y_1299_;
v___y_1260_ = v___y_1300_;
v___y_1261_ = v___y_1301_;
v___y_1262_ = v___y_1302_;
goto v___jp_1256_;
}
else
{
lean_object* v_a_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1336_; 
lean_dec(v_a_1318_);
lean_dec_ref(v___y_1297_);
lean_dec_ref(v_funTypes_1249_);
lean_dec_ref(v_preDefs_1243_);
lean_dec(v___x_1242_);
lean_dec_ref(v_xs_1241_);
lean_dec_ref(v_fixedParamPerms_1240_);
lean_dec_ref(v___x_1238_);
lean_dec_ref(v_recArgInfos_1236_);
v_a_1329_ = lean_ctor_get(v___x_1328_, 0);
v_isSharedCheck_1336_ = !lean_is_exclusive(v___x_1328_);
if (v_isSharedCheck_1336_ == 0)
{
v___x_1331_ = v___x_1328_;
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_a_1329_);
lean_dec(v___x_1328_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
lean_object* v___x_1334_; 
if (v_isShared_1332_ == 0)
{
v___x_1334_ = v___x_1331_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v_a_1329_);
v___x_1334_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
return v___x_1334_;
}
}
}
}
}
}
else
{
lean_object* v_a_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1344_; 
lean_dec_ref(v___y_1297_);
lean_dec_ref(v_funTypes_1249_);
lean_dec(v___x_1246_);
lean_dec_ref(v_preDefs_1243_);
lean_dec(v___x_1242_);
lean_dec_ref(v_xs_1241_);
lean_dec_ref(v_fixedParamPerms_1240_);
lean_dec_ref(v___x_1238_);
lean_dec_ref(v_recArgInfos_1236_);
v_a_1337_ = lean_ctor_get(v___x_1313_, 0);
v_isSharedCheck_1344_ = !lean_is_exclusive(v___x_1313_);
if (v_isSharedCheck_1344_ == 0)
{
v___x_1339_ = v___x_1313_;
v_isShared_1340_ = v_isSharedCheck_1344_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_a_1337_);
lean_dec(v___x_1313_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1344_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
lean_object* v___x_1342_; 
if (v_isShared_1340_ == 0)
{
v___x_1342_ = v___x_1339_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v_a_1337_);
v___x_1342_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
return v___x_1342_;
}
}
}
}
else
{
lean_object* v_a_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1352_; 
lean_dec_ref(v_FArgs_1298_);
lean_dec_ref(v___y_1297_);
lean_dec_ref(v_funTypes_1249_);
lean_dec(v___x_1246_);
lean_dec_ref(v___f_1245_);
lean_dec_ref(v_preDefs_1243_);
lean_dec(v___x_1242_);
lean_dec_ref(v_xs_1241_);
lean_dec_ref(v_fixedParamPerms_1240_);
lean_dec_ref(v___x_1238_);
lean_dec_ref(v_recArgInfos_1236_);
v_a_1345_ = lean_ctor_get(v___x_1311_, 0);
v_isSharedCheck_1352_ = !lean_is_exclusive(v___x_1311_);
if (v_isSharedCheck_1352_ == 0)
{
v___x_1347_ = v___x_1311_;
v_isShared_1348_ = v_isSharedCheck_1352_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_a_1345_);
lean_dec(v___x_1311_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1352_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
lean_object* v___x_1350_; 
if (v_isShared_1348_ == 0)
{
v___x_1350_ = v___x_1347_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v_a_1345_);
v___x_1350_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
return v___x_1350_;
}
}
}
}
v___jp_1353_:
{
if (v_a_1247_ == 0)
{
lean_object* v___x_1360_; lean_object* v_levelParams_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; size_t v_sz_1364_; lean_object* v___x_1365_; 
v___x_1360_ = lean_array_get_borrowed(v___x_1248_, v_preDefs_1243_, v___x_1242_);
v_levelParams_1361_ = lean_ctor_get(v___x_1360_, 1);
v___x_1362_ = lean_box(0);
lean_inc(v_levelParams_1361_);
v___x_1363_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__15(v_levelParams_1361_, v___x_1362_);
v_sz_1364_ = lean_array_size(v___y_1354_);
v___x_1365_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg(v_xs_1241_, v_a_1247_, v_preDefs_1243_, v___x_1363_, v_sz_1364_, v___x_1239_, v___y_1354_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_);
if (lean_obj_tag(v___x_1365_) == 0)
{
lean_object* v_a_1366_; 
v_a_1366_ = lean_ctor_get(v___x_1365_, 0);
lean_inc(v_a_1366_);
lean_dec_ref_known(v___x_1365_, 1);
v___y_1297_ = v___y_1355_;
v_FArgs_1298_ = v_a_1366_;
v___y_1299_ = v___y_1356_;
v___y_1300_ = v___y_1357_;
v___y_1301_ = v___y_1358_;
v___y_1302_ = v___y_1359_;
goto v___jp_1296_;
}
else
{
lean_object* v_a_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1374_; 
lean_dec_ref(v___y_1355_);
lean_dec_ref(v_funTypes_1249_);
lean_dec(v___x_1246_);
lean_dec_ref(v___f_1245_);
lean_dec_ref(v_preDefs_1243_);
lean_dec(v___x_1242_);
lean_dec_ref(v_xs_1241_);
lean_dec_ref(v_fixedParamPerms_1240_);
lean_dec_ref(v___x_1238_);
lean_dec_ref(v_recArgInfos_1236_);
v_a_1367_ = lean_ctor_get(v___x_1365_, 0);
v_isSharedCheck_1374_ = !lean_is_exclusive(v___x_1365_);
if (v_isSharedCheck_1374_ == 0)
{
v___x_1369_ = v___x_1365_;
v_isShared_1370_ = v_isSharedCheck_1374_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_a_1367_);
lean_dec(v___x_1365_);
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
else
{
v___y_1297_ = v___y_1355_;
v_FArgs_1298_ = v___y_1354_;
v___y_1299_ = v___y_1356_;
v___y_1300_ = v___y_1357_;
v___y_1301_ = v___y_1358_;
v___y_1302_ = v___y_1359_;
goto v___jp_1296_;
}
}
v___jp_1375_:
{
size_t v_sz_1382_; lean_object* v___x_1383_; 
v_sz_1382_ = lean_array_size(v_recArgInfos_1236_);
lean_inc_ref(v___y_1377_);
lean_inc_ref(v_preDefs_1243_);
lean_inc_ref(v___x_1238_);
lean_inc_ref_n(v_recArgInfos_1236_, 2);
v___x_1383_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg(v_a_1247_, v_a_1237_, v___y_1376_, v_recArgInfos_1236_, v___x_1238_, v_preDefs_1243_, v___y_1377_, v_sz_1382_, v___x_1239_, v_recArgInfos_1236_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_);
lean_dec_ref(v___y_1376_);
if (lean_obj_tag(v___x_1383_) == 0)
{
lean_object* v_a_1384_; lean_object* v___x_1385_; 
v_a_1384_ = lean_ctor_get(v___x_1383_, 0);
lean_inc(v_a_1384_);
lean_dec_ref_known(v___x_1383_, 1);
lean_inc(v___y_1381_);
lean_inc_ref(v___y_1380_);
lean_inc(v___y_1379_);
lean_inc_ref(v___y_1378_);
v___x_1385_ = lean_apply_5(v___f_1235_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_, lean_box(0));
if (lean_obj_tag(v___x_1385_) == 0)
{
lean_object* v_a_1386_; uint8_t v___x_1387_; 
v_a_1386_ = lean_ctor_get(v___x_1385_, 0);
lean_inc(v_a_1386_);
lean_dec_ref_known(v___x_1385_, 1);
v___x_1387_ = lean_unbox(v_a_1386_);
lean_dec(v_a_1386_);
if (v___x_1387_ == 0)
{
v___y_1354_ = v_a_1384_;
v___y_1355_ = v___y_1377_;
v___y_1356_ = v___y_1378_;
v___y_1357_ = v___y_1379_;
v___y_1358_ = v___y_1380_;
v___y_1359_ = v___y_1381_;
goto v___jp_1353_;
}
else
{
lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; 
v___x_1388_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__6, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__6);
lean_inc(v_a_1384_);
v___x_1389_ = lean_array_to_list(v_a_1384_);
v___x_1390_ = lean_box(0);
v___x_1391_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_1389_, v___x_1390_);
v___x_1392_ = l_Lean_MessageData_ofList(v___x_1391_);
v___x_1393_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1393_, 0, v___x_1388_);
lean_ctor_set(v___x_1393_, 1, v___x_1392_);
lean_inc(v___x_1246_);
v___x_1394_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_1246_, v___x_1393_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_);
if (lean_obj_tag(v___x_1394_) == 0)
{
lean_dec_ref_known(v___x_1394_, 1);
v___y_1354_ = v_a_1384_;
v___y_1355_ = v___y_1377_;
v___y_1356_ = v___y_1378_;
v___y_1357_ = v___y_1379_;
v___y_1358_ = v___y_1380_;
v___y_1359_ = v___y_1381_;
goto v___jp_1353_;
}
else
{
lean_object* v_a_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1402_; 
lean_dec(v_a_1384_);
lean_dec_ref(v___y_1377_);
lean_dec_ref(v_funTypes_1249_);
lean_dec(v___x_1246_);
lean_dec_ref(v___f_1245_);
lean_dec_ref(v_preDefs_1243_);
lean_dec(v___x_1242_);
lean_dec_ref(v_xs_1241_);
lean_dec_ref(v_fixedParamPerms_1240_);
lean_dec_ref(v___x_1238_);
lean_dec_ref(v_recArgInfos_1236_);
v_a_1395_ = lean_ctor_get(v___x_1394_, 0);
v_isSharedCheck_1402_ = !lean_is_exclusive(v___x_1394_);
if (v_isSharedCheck_1402_ == 0)
{
v___x_1397_ = v___x_1394_;
v_isShared_1398_ = v_isSharedCheck_1402_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_a_1395_);
lean_dec(v___x_1394_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1402_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
lean_object* v___x_1400_; 
if (v_isShared_1398_ == 0)
{
v___x_1400_ = v___x_1397_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v_a_1395_);
v___x_1400_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
return v___x_1400_;
}
}
}
}
}
else
{
lean_object* v_a_1403_; lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1410_; 
lean_dec(v_a_1384_);
lean_dec_ref(v___y_1377_);
lean_dec_ref(v_funTypes_1249_);
lean_dec(v___x_1246_);
lean_dec_ref(v___f_1245_);
lean_dec_ref(v_preDefs_1243_);
lean_dec(v___x_1242_);
lean_dec_ref(v_xs_1241_);
lean_dec_ref(v_fixedParamPerms_1240_);
lean_dec_ref(v___x_1238_);
lean_dec_ref(v_recArgInfos_1236_);
v_a_1403_ = lean_ctor_get(v___x_1385_, 0);
v_isSharedCheck_1410_ = !lean_is_exclusive(v___x_1385_);
if (v_isSharedCheck_1410_ == 0)
{
v___x_1405_ = v___x_1385_;
v_isShared_1406_ = v_isSharedCheck_1410_;
goto v_resetjp_1404_;
}
else
{
lean_inc(v_a_1403_);
lean_dec(v___x_1385_);
v___x_1405_ = lean_box(0);
v_isShared_1406_ = v_isSharedCheck_1410_;
goto v_resetjp_1404_;
}
v_resetjp_1404_:
{
lean_object* v___x_1408_; 
if (v_isShared_1406_ == 0)
{
v___x_1408_ = v___x_1405_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v_a_1403_);
v___x_1408_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
return v___x_1408_;
}
}
}
}
else
{
lean_object* v_a_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1418_; 
lean_dec_ref(v___y_1377_);
lean_dec_ref(v_funTypes_1249_);
lean_dec(v___x_1246_);
lean_dec_ref(v___f_1245_);
lean_dec_ref(v_preDefs_1243_);
lean_dec(v___x_1242_);
lean_dec_ref(v_xs_1241_);
lean_dec_ref(v_fixedParamPerms_1240_);
lean_dec_ref(v___x_1238_);
lean_dec_ref(v_recArgInfos_1236_);
lean_dec_ref(v___f_1235_);
v_a_1411_ = lean_ctor_get(v___x_1383_, 0);
v_isSharedCheck_1418_ = !lean_is_exclusive(v___x_1383_);
if (v_isSharedCheck_1418_ == 0)
{
v___x_1413_ = v___x_1383_;
v_isShared_1414_ = v_isSharedCheck_1418_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_a_1411_);
lean_dec(v___x_1383_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1418_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
lean_object* v___x_1416_; 
if (v_isShared_1414_ == 0)
{
v___x_1416_ = v___x_1413_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v_a_1411_);
v___x_1416_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
return v___x_1416_;
}
}
}
}
v___jp_1419_:
{
lean_object* v___x_1424_; 
v___x_1424_ = l_Lean_Elab_Structural_mkBRecOnConst(v_recArgInfos_1236_, v___x_1238_, v_motives_1250_, v_a_1247_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_);
lean_dec_ref(v_motives_1250_);
if (lean_obj_tag(v___x_1424_) == 0)
{
lean_object* v_a_1425_; lean_object* v___x_1426_; 
v_a_1425_ = lean_ctor_get(v___x_1424_, 0);
lean_inc_n(v_a_1425_, 2);
lean_dec_ref_known(v___x_1424_, 1);
lean_inc_ref(v___x_1238_);
v___x_1426_ = l_Lean_Elab_Structural_inferBRecOnFTypes(v_recArgInfos_1236_, v___x_1238_, v_a_1425_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_);
if (lean_obj_tag(v___x_1426_) == 0)
{
lean_object* v_a_1427_; lean_object* v___x_1428_; 
v_a_1427_ = lean_ctor_get(v___x_1426_, 0);
lean_inc(v_a_1427_);
lean_dec_ref_known(v___x_1426_, 1);
lean_inc_ref(v___f_1235_);
lean_inc(v___y_1423_);
lean_inc_ref(v___y_1422_);
lean_inc(v___y_1421_);
lean_inc_ref(v___y_1420_);
v___x_1428_ = lean_apply_5(v___f_1235_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_, lean_box(0));
if (lean_obj_tag(v___x_1428_) == 0)
{
lean_object* v_a_1429_; uint8_t v___x_1430_; 
v_a_1429_ = lean_ctor_get(v___x_1428_, 0);
lean_inc(v_a_1429_);
lean_dec_ref_known(v___x_1428_, 1);
v___x_1430_ = lean_unbox(v_a_1429_);
lean_dec(v_a_1429_);
if (v___x_1430_ == 0)
{
v___y_1376_ = v_a_1427_;
v___y_1377_ = v_a_1425_;
v___y_1378_ = v___y_1420_;
v___y_1379_ = v___y_1421_;
v___y_1380_ = v___y_1422_;
v___y_1381_ = v___y_1423_;
goto v___jp_1375_;
}
else
{
lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; 
v___x_1431_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__8);
lean_inc(v_a_1427_);
v___x_1432_ = lean_array_to_list(v_a_1427_);
v___x_1433_ = lean_box(0);
v___x_1434_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_1432_, v___x_1433_);
v___x_1435_ = l_Lean_MessageData_ofList(v___x_1434_);
v___x_1436_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1436_, 0, v___x_1431_);
lean_ctor_set(v___x_1436_, 1, v___x_1435_);
lean_inc(v___x_1246_);
v___x_1437_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_1246_, v___x_1436_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_);
if (lean_obj_tag(v___x_1437_) == 0)
{
lean_dec_ref_known(v___x_1437_, 1);
v___y_1376_ = v_a_1427_;
v___y_1377_ = v_a_1425_;
v___y_1378_ = v___y_1420_;
v___y_1379_ = v___y_1421_;
v___y_1380_ = v___y_1422_;
v___y_1381_ = v___y_1423_;
goto v___jp_1375_;
}
else
{
lean_object* v_a_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1445_; 
lean_dec(v_a_1427_);
lean_dec(v_a_1425_);
lean_dec_ref(v_funTypes_1249_);
lean_dec(v___x_1246_);
lean_dec_ref(v___f_1245_);
lean_dec_ref(v_preDefs_1243_);
lean_dec(v___x_1242_);
lean_dec_ref(v_xs_1241_);
lean_dec_ref(v_fixedParamPerms_1240_);
lean_dec_ref(v___x_1238_);
lean_dec_ref(v_recArgInfos_1236_);
lean_dec_ref(v___f_1235_);
v_a_1438_ = lean_ctor_get(v___x_1437_, 0);
v_isSharedCheck_1445_ = !lean_is_exclusive(v___x_1437_);
if (v_isSharedCheck_1445_ == 0)
{
v___x_1440_ = v___x_1437_;
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_a_1438_);
lean_dec(v___x_1437_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v___x_1443_; 
if (v_isShared_1441_ == 0)
{
v___x_1443_ = v___x_1440_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v_a_1438_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
return v___x_1443_;
}
}
}
}
}
else
{
lean_object* v_a_1446_; lean_object* v___x_1448_; uint8_t v_isShared_1449_; uint8_t v_isSharedCheck_1453_; 
lean_dec(v_a_1427_);
lean_dec(v_a_1425_);
lean_dec_ref(v_funTypes_1249_);
lean_dec(v___x_1246_);
lean_dec_ref(v___f_1245_);
lean_dec_ref(v_preDefs_1243_);
lean_dec(v___x_1242_);
lean_dec_ref(v_xs_1241_);
lean_dec_ref(v_fixedParamPerms_1240_);
lean_dec_ref(v___x_1238_);
lean_dec_ref(v_recArgInfos_1236_);
lean_dec_ref(v___f_1235_);
v_a_1446_ = lean_ctor_get(v___x_1428_, 0);
v_isSharedCheck_1453_ = !lean_is_exclusive(v___x_1428_);
if (v_isSharedCheck_1453_ == 0)
{
v___x_1448_ = v___x_1428_;
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
else
{
lean_inc(v_a_1446_);
lean_dec(v___x_1428_);
v___x_1448_ = lean_box(0);
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
v_resetjp_1447_:
{
lean_object* v___x_1451_; 
if (v_isShared_1449_ == 0)
{
v___x_1451_ = v___x_1448_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v_a_1446_);
v___x_1451_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
return v___x_1451_;
}
}
}
}
else
{
lean_object* v_a_1454_; lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1461_; 
lean_dec(v_a_1425_);
lean_dec_ref(v_funTypes_1249_);
lean_dec(v___x_1246_);
lean_dec_ref(v___f_1245_);
lean_dec_ref(v_preDefs_1243_);
lean_dec(v___x_1242_);
lean_dec_ref(v_xs_1241_);
lean_dec_ref(v_fixedParamPerms_1240_);
lean_dec_ref(v___x_1238_);
lean_dec_ref(v_recArgInfos_1236_);
lean_dec_ref(v___f_1235_);
v_a_1454_ = lean_ctor_get(v___x_1426_, 0);
v_isSharedCheck_1461_ = !lean_is_exclusive(v___x_1426_);
if (v_isSharedCheck_1461_ == 0)
{
v___x_1456_ = v___x_1426_;
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
else
{
lean_inc(v_a_1454_);
lean_dec(v___x_1426_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
lean_object* v___x_1459_; 
if (v_isShared_1457_ == 0)
{
v___x_1459_ = v___x_1456_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v_a_1454_);
v___x_1459_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
return v___x_1459_;
}
}
}
}
else
{
lean_object* v_a_1462_; lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1469_; 
lean_dec_ref(v_funTypes_1249_);
lean_dec(v___x_1246_);
lean_dec_ref(v___f_1245_);
lean_dec_ref(v_preDefs_1243_);
lean_dec(v___x_1242_);
lean_dec_ref(v_xs_1241_);
lean_dec_ref(v_fixedParamPerms_1240_);
lean_dec_ref(v___x_1238_);
lean_dec_ref(v_recArgInfos_1236_);
lean_dec_ref(v___f_1235_);
v_a_1462_ = lean_ctor_get(v___x_1424_, 0);
v_isSharedCheck_1469_ = !lean_is_exclusive(v___x_1424_);
if (v_isSharedCheck_1469_ == 0)
{
v___x_1464_ = v___x_1424_;
v_isShared_1465_ = v_isSharedCheck_1469_;
goto v_resetjp_1463_;
}
else
{
lean_inc(v_a_1462_);
lean_dec(v___x_1424_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1469_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
lean_object* v___x_1467_; 
if (v_isShared_1465_ == 0)
{
v___x_1467_ = v___x_1464_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v_a_1462_);
v___x_1467_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
return v___x_1467_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___boxed(lean_object** _args){
lean_object* v___f_1502_ = _args[0];
lean_object* v_recArgInfos_1503_ = _args[1];
lean_object* v_a_1504_ = _args[2];
lean_object* v___x_1505_ = _args[3];
lean_object* v___x_1506_ = _args[4];
lean_object* v_fixedParamPerms_1507_ = _args[5];
lean_object* v_xs_1508_ = _args[6];
lean_object* v___x_1509_ = _args[7];
lean_object* v_preDefs_1510_ = _args[8];
lean_object* v_numIndices_1511_ = _args[9];
lean_object* v___f_1512_ = _args[10];
lean_object* v___x_1513_ = _args[11];
lean_object* v_a_1514_ = _args[12];
lean_object* v___x_1515_ = _args[13];
lean_object* v_funTypes_1516_ = _args[14];
lean_object* v_motives_1517_ = _args[15];
lean_object* v___y_1518_ = _args[16];
lean_object* v___y_1519_ = _args[17];
lean_object* v___y_1520_ = _args[18];
lean_object* v___y_1521_ = _args[19];
lean_object* v___y_1522_ = _args[20];
_start:
{
size_t v___x_26416__boxed_1523_; uint8_t v_a_26420__boxed_1524_; lean_object* v_res_1525_; 
v___x_26416__boxed_1523_ = lean_unbox_usize(v___x_1506_);
lean_dec(v___x_1506_);
v_a_26420__boxed_1524_ = lean_unbox(v_a_1514_);
v_res_1525_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2(v___f_1502_, v_recArgInfos_1503_, v_a_1504_, v___x_1505_, v___x_26416__boxed_1523_, v_fixedParamPerms_1507_, v_xs_1508_, v___x_1509_, v_preDefs_1510_, v_numIndices_1511_, v___f_1512_, v___x_1513_, v_a_26420__boxed_1524_, v___x_1515_, v_funTypes_1516_, v_motives_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_);
lean_dec(v___y_1521_);
lean_dec_ref(v___y_1520_);
lean_dec(v___y_1519_);
lean_dec_ref(v___y_1518_);
lean_dec_ref(v___x_1515_);
lean_dec(v_numIndices_1511_);
lean_dec_ref(v_a_1504_);
return v_res_1525_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___redArg(lean_object* v_a_1526_, lean_object* v_funTypes_1527_, size_t v_sz_1528_, size_t v_i_1529_, lean_object* v_bs_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_){
_start:
{
uint8_t v___x_1536_; 
v___x_1536_ = lean_usize_dec_lt(v_i_1529_, v_sz_1528_);
if (v___x_1536_ == 0)
{
lean_object* v___x_1537_; 
v___x_1537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1537_, 0, v_bs_1530_);
return v___x_1537_;
}
else
{
lean_object* v___x_1538_; lean_object* v_v_1539_; lean_object* v___x_1540_; lean_object* v_bs_x27_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; 
v___x_1538_ = l_Lean_instInhabitedExpr;
v_v_1539_ = lean_array_uget(v_bs_1530_, v_i_1529_);
v___x_1540_ = lean_unsigned_to_nat(0u);
v_bs_x27_1541_ = lean_array_uset(v_bs_1530_, v_i_1529_, v___x_1540_);
v___x_1542_ = lean_usize_to_nat(v_i_1529_);
v___x_1543_ = lean_array_get_borrowed(v___x_1538_, v_a_1526_, v___x_1542_);
v___x_1544_ = lean_array_get_borrowed(v___x_1538_, v_funTypes_1527_, v___x_1542_);
lean_dec(v___x_1542_);
lean_inc(v___x_1544_);
lean_inc(v___x_1543_);
v___x_1545_ = l_Lean_Elab_Structural_mkIndPredBRecOnMotive(v_v_1539_, v___x_1543_, v___x_1544_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_);
if (lean_obj_tag(v___x_1545_) == 0)
{
lean_object* v_a_1546_; size_t v___x_1547_; size_t v___x_1548_; lean_object* v___x_1549_; 
v_a_1546_ = lean_ctor_get(v___x_1545_, 0);
lean_inc(v_a_1546_);
lean_dec_ref_known(v___x_1545_, 1);
v___x_1547_ = ((size_t)1ULL);
v___x_1548_ = lean_usize_add(v_i_1529_, v___x_1547_);
v___x_1549_ = lean_array_uset(v_bs_x27_1541_, v_i_1529_, v_a_1546_);
v_i_1529_ = v___x_1548_;
v_bs_1530_ = v___x_1549_;
goto _start;
}
else
{
lean_object* v_a_1551_; lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1558_; 
lean_dec_ref(v_bs_x27_1541_);
v_a_1551_ = lean_ctor_get(v___x_1545_, 0);
v_isSharedCheck_1558_ = !lean_is_exclusive(v___x_1545_);
if (v_isSharedCheck_1558_ == 0)
{
v___x_1553_ = v___x_1545_;
v_isShared_1554_ = v_isSharedCheck_1558_;
goto v_resetjp_1552_;
}
else
{
lean_inc(v_a_1551_);
lean_dec(v___x_1545_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1558_;
goto v_resetjp_1552_;
}
v_resetjp_1552_:
{
lean_object* v___x_1556_; 
if (v_isShared_1554_ == 0)
{
v___x_1556_ = v___x_1553_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v_a_1551_);
v___x_1556_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1555_;
}
v_reusejp_1555_:
{
return v___x_1556_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___redArg___boxed(lean_object* v_a_1559_, lean_object* v_funTypes_1560_, lean_object* v_sz_1561_, lean_object* v_i_1562_, lean_object* v_bs_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_){
_start:
{
size_t v_sz_boxed_1569_; size_t v_i_boxed_1570_; lean_object* v_res_1571_; 
v_sz_boxed_1569_ = lean_unbox_usize(v_sz_1561_);
lean_dec(v_sz_1561_);
v_i_boxed_1570_ = lean_unbox_usize(v_i_1562_);
lean_dec(v_i_1562_);
v_res_1571_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___redArg(v_a_1559_, v_funTypes_1560_, v_sz_boxed_1569_, v_i_boxed_1570_, v_bs_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_);
lean_dec(v___y_1567_);
lean_dec_ref(v___y_1566_);
lean_dec(v___y_1565_);
lean_dec_ref(v___y_1564_);
lean_dec_ref(v_funTypes_1560_);
lean_dec_ref(v_a_1559_);
return v_res_1571_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__3(lean_object* v_recArgInfos_1572_, lean_object* v_a_1573_, size_t v___x_1574_, lean_object* v___f_1575_, lean_object* v_funTypes_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_){
_start:
{
size_t v_sz_1582_; lean_object* v___x_1583_; 
v_sz_1582_ = lean_array_size(v_recArgInfos_1572_);
v___x_1583_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___redArg(v_a_1573_, v_funTypes_1576_, v_sz_1582_, v___x_1574_, v_recArgInfos_1572_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_);
if (lean_obj_tag(v___x_1583_) == 0)
{
lean_object* v_a_1584_; lean_object* v___x_1585_; 
v_a_1584_ = lean_ctor_get(v___x_1583_, 0);
lean_inc(v_a_1584_);
lean_dec_ref_known(v___x_1583_, 1);
lean_inc(v___y_1580_);
lean_inc_ref(v___y_1579_);
lean_inc(v___y_1578_);
lean_inc_ref(v___y_1577_);
v___x_1585_ = lean_apply_7(v___f_1575_, v_funTypes_1576_, v_a_1584_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_, lean_box(0));
return v___x_1585_;
}
else
{
lean_object* v_a_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1593_; 
lean_dec_ref(v_funTypes_1576_);
lean_dec_ref(v___f_1575_);
v_a_1586_ = lean_ctor_get(v___x_1583_, 0);
v_isSharedCheck_1593_ = !lean_is_exclusive(v___x_1583_);
if (v_isSharedCheck_1593_ == 0)
{
v___x_1588_ = v___x_1583_;
v_isShared_1589_ = v_isSharedCheck_1593_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_a_1586_);
lean_dec(v___x_1583_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1593_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
lean_object* v___x_1591_; 
if (v_isShared_1589_ == 0)
{
v___x_1591_ = v___x_1588_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v_a_1586_);
v___x_1591_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
return v___x_1591_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__3___boxed(lean_object* v_recArgInfos_1594_, lean_object* v_a_1595_, lean_object* v___x_1596_, lean_object* v___f_1597_, lean_object* v_funTypes_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_){
_start:
{
size_t v___x_27013__boxed_1604_; lean_object* v_res_1605_; 
v___x_27013__boxed_1604_ = lean_unbox_usize(v___x_1596_);
lean_dec(v___x_1596_);
v_res_1605_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__3(v_recArgInfos_1594_, v_a_1595_, v___x_27013__boxed_1604_, v___f_1597_, v_funTypes_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_);
lean_dec(v___y_1602_);
lean_dec_ref(v___y_1601_);
lean_dec(v___y_1600_);
lean_dec_ref(v___y_1599_);
lean_dec_ref(v_a_1595_);
return v_res_1605_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___redArg(lean_object* v_a_1606_, lean_object* v_a_1607_, size_t v_sz_1608_, size_t v_i_1609_, lean_object* v_bs_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_){
_start:
{
uint8_t v___x_1616_; 
v___x_1616_ = lean_usize_dec_lt(v_i_1609_, v_sz_1608_);
if (v___x_1616_ == 0)
{
lean_object* v___x_1617_; 
v___x_1617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1617_, 0, v_bs_1610_);
return v___x_1617_;
}
else
{
lean_object* v___x_1618_; lean_object* v_v_1619_; lean_object* v___x_1620_; lean_object* v_bs_x27_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; 
v___x_1618_ = l_Lean_instInhabitedExpr;
v_v_1619_ = lean_array_uget(v_bs_1610_, v_i_1609_);
v___x_1620_ = lean_unsigned_to_nat(0u);
v_bs_x27_1621_ = lean_array_uset(v_bs_1610_, v_i_1609_, v___x_1620_);
v___x_1622_ = lean_usize_to_nat(v_i_1609_);
v___x_1623_ = lean_array_get_borrowed(v___x_1618_, v_a_1606_, v___x_1622_);
v___x_1624_ = lean_array_get_borrowed(v___x_1618_, v_a_1607_, v___x_1622_);
lean_dec(v___x_1622_);
lean_inc(v___x_1624_);
lean_inc(v___x_1623_);
v___x_1625_ = l_Lean_Elab_Structural_mkBRecOnMotive(v_v_1619_, v___x_1623_, v___x_1624_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_);
if (lean_obj_tag(v___x_1625_) == 0)
{
lean_object* v_a_1626_; size_t v___x_1627_; size_t v___x_1628_; lean_object* v___x_1629_; 
v_a_1626_ = lean_ctor_get(v___x_1625_, 0);
lean_inc(v_a_1626_);
lean_dec_ref_known(v___x_1625_, 1);
v___x_1627_ = ((size_t)1ULL);
v___x_1628_ = lean_usize_add(v_i_1609_, v___x_1627_);
v___x_1629_ = lean_array_uset(v_bs_x27_1621_, v_i_1609_, v_a_1626_);
v_i_1609_ = v___x_1628_;
v_bs_1610_ = v___x_1629_;
goto _start;
}
else
{
lean_object* v_a_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1638_; 
lean_dec_ref(v_bs_x27_1621_);
v_a_1631_ = lean_ctor_get(v___x_1625_, 0);
v_isSharedCheck_1638_ = !lean_is_exclusive(v___x_1625_);
if (v_isSharedCheck_1638_ == 0)
{
v___x_1633_ = v___x_1625_;
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_a_1631_);
lean_dec(v___x_1625_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
lean_object* v___x_1636_; 
if (v_isShared_1634_ == 0)
{
v___x_1636_ = v___x_1633_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v_a_1631_);
v___x_1636_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
return v___x_1636_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___redArg___boxed(lean_object* v_a_1639_, lean_object* v_a_1640_, lean_object* v_sz_1641_, lean_object* v_i_1642_, lean_object* v_bs_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_){
_start:
{
size_t v_sz_boxed_1649_; size_t v_i_boxed_1650_; lean_object* v_res_1651_; 
v_sz_boxed_1649_ = lean_unbox_usize(v_sz_1641_);
lean_dec(v_sz_1641_);
v_i_boxed_1650_ = lean_unbox_usize(v_i_1642_);
lean_dec(v_i_1642_);
v_res_1651_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___redArg(v_a_1639_, v_a_1640_, v_sz_boxed_1649_, v_i_boxed_1650_, v_bs_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_);
lean_dec(v___y_1647_);
lean_dec_ref(v___y_1646_);
lean_dec(v___y_1645_);
lean_dec_ref(v___y_1644_);
lean_dec_ref(v_a_1640_);
lean_dec_ref(v_a_1639_);
return v_res_1651_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg(lean_object* v_msg_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_){
_start:
{
lean_object* v_ref_1658_; lean_object* v___x_1659_; lean_object* v_a_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1668_; 
v_ref_1658_ = lean_ctor_get(v___y_1655_, 4);
v___x_1659_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11_spec__21(v_msg_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_);
v_a_1660_ = lean_ctor_get(v___x_1659_, 0);
v_isSharedCheck_1668_ = !lean_is_exclusive(v___x_1659_);
if (v_isSharedCheck_1668_ == 0)
{
v___x_1662_ = v___x_1659_;
v_isShared_1663_ = v_isSharedCheck_1668_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_a_1660_);
lean_dec(v___x_1659_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1668_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v___x_1664_; lean_object* v___x_1666_; 
lean_inc(v_ref_1658_);
v___x_1664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1664_, 0, v_ref_1658_);
lean_ctor_set(v___x_1664_, 1, v_a_1660_);
if (v_isShared_1663_ == 0)
{
lean_ctor_set_tag(v___x_1662_, 1);
lean_ctor_set(v___x_1662_, 0, v___x_1664_);
v___x_1666_ = v___x_1662_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v___x_1664_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg___boxed(lean_object* v_msg_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_){
_start:
{
lean_object* v_res_1675_; 
v_res_1675_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg(v_msg_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_);
lean_dec(v___y_1673_);
lean_dec_ref(v___y_1672_);
lean_dec(v___y_1671_);
lean_dec_ref(v___y_1670_);
return v_res_1675_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1677_; lean_object* v___x_1678_; 
v___x_1677_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__0));
v___x_1678_ = l_Lean_stringToMessageData(v___x_1677_);
return v___x_1678_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__3(void){
_start:
{
lean_object* v___x_1680_; lean_object* v___x_1681_; 
v___x_1680_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__2));
v___x_1681_ = l_Lean_stringToMessageData(v___x_1680_);
return v___x_1681_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4(lean_object* v_constName_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_){
_start:
{
lean_object* v___x_1688_; lean_object* v_env_1689_; lean_object* v___x_1690_; 
v___x_1688_ = lean_st_ref_get(v___y_1686_);
v_env_1689_ = lean_ctor_get(v___x_1688_, 0);
lean_inc_ref(v_env_1689_);
lean_dec(v___x_1688_);
lean_inc(v_constName_1682_);
v___x_1690_ = l_Lean_isInductiveCore_x3f(v_env_1689_, v_constName_1682_);
if (lean_obj_tag(v___x_1690_) == 0)
{
lean_object* v___x_1691_; uint8_t v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; 
v___x_1691_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__1, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__1);
v___x_1692_ = 0;
v___x_1693_ = l_Lean_MessageData_ofConstName(v_constName_1682_, v___x_1692_);
v___x_1694_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1694_, 0, v___x_1691_);
lean_ctor_set(v___x_1694_, 1, v___x_1693_);
v___x_1695_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__3, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__3_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__3);
v___x_1696_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1696_, 0, v___x_1694_);
lean_ctor_set(v___x_1696_, 1, v___x_1695_);
v___x_1697_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg(v___x_1696_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_);
return v___x_1697_;
}
else
{
lean_object* v_val_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1705_; 
lean_dec(v_constName_1682_);
v_val_1698_ = lean_ctor_get(v___x_1690_, 0);
v_isSharedCheck_1705_ = !lean_is_exclusive(v___x_1690_);
if (v_isSharedCheck_1705_ == 0)
{
v___x_1700_ = v___x_1690_;
v_isShared_1701_ = v_isSharedCheck_1705_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_val_1698_);
lean_dec(v___x_1690_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1705_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v___x_1703_; 
if (v_isShared_1701_ == 0)
{
lean_ctor_set_tag(v___x_1700_, 0);
v___x_1703_ = v___x_1700_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v_val_1698_);
v___x_1703_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
return v___x_1703_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___boxed(lean_object* v_constName_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_){
_start:
{
lean_object* v_res_1712_; 
v_res_1712_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4(v_constName_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_);
lean_dec(v___y_1710_);
lean_dec_ref(v___y_1709_);
lean_dec(v___y_1708_);
lean_dec_ref(v___y_1707_);
return v_res_1712_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___redArg(lean_object* v_fixedParamPerms_1713_, lean_object* v_xs_1714_, size_t v_sz_1715_, size_t v_i_1716_, lean_object* v_bs_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_){
_start:
{
uint8_t v___x_1723_; 
v___x_1723_ = lean_usize_dec_lt(v_i_1716_, v_sz_1715_);
if (v___x_1723_ == 0)
{
lean_object* v___x_1724_; 
lean_dec_ref(v_xs_1714_);
v___x_1724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1724_, 0, v_bs_1717_);
return v___x_1724_;
}
else
{
lean_object* v_v_1725_; lean_object* v_perms_1726_; lean_object* v_type_1727_; lean_object* v___x_1728_; lean_object* v_bs_x27_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; 
v_v_1725_ = lean_array_uget_borrowed(v_bs_1717_, v_i_1716_);
v_perms_1726_ = lean_ctor_get(v_fixedParamPerms_1713_, 1);
v_type_1727_ = lean_ctor_get(v_v_1725_, 6);
lean_inc_ref(v_type_1727_);
v___x_1728_ = lean_unsigned_to_nat(0u);
v_bs_x27_1729_ = lean_array_uset(v_bs_1717_, v_i_1716_, v___x_1728_);
v___x_1730_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0);
v___x_1731_ = lean_usize_to_nat(v_i_1716_);
v___x_1732_ = lean_array_get_borrowed(v___x_1730_, v_perms_1726_, v___x_1731_);
lean_dec(v___x_1731_);
lean_inc_ref(v_xs_1714_);
lean_inc(v___x_1732_);
v___x_1733_ = l_Lean_Elab_FixedParamPerm_instantiateForall(v___x_1732_, v_type_1727_, v_xs_1714_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_);
if (lean_obj_tag(v___x_1733_) == 0)
{
lean_object* v_a_1734_; size_t v___x_1735_; size_t v___x_1736_; lean_object* v___x_1737_; 
v_a_1734_ = lean_ctor_get(v___x_1733_, 0);
lean_inc(v_a_1734_);
lean_dec_ref_known(v___x_1733_, 1);
v___x_1735_ = ((size_t)1ULL);
v___x_1736_ = lean_usize_add(v_i_1716_, v___x_1735_);
v___x_1737_ = lean_array_uset(v_bs_x27_1729_, v_i_1716_, v_a_1734_);
v_i_1716_ = v___x_1736_;
v_bs_1717_ = v___x_1737_;
goto _start;
}
else
{
lean_object* v_a_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1746_; 
lean_dec_ref(v_bs_x27_1729_);
lean_dec_ref(v_xs_1714_);
v_a_1739_ = lean_ctor_get(v___x_1733_, 0);
v_isSharedCheck_1746_ = !lean_is_exclusive(v___x_1733_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1741_ = v___x_1733_;
v_isShared_1742_ = v_isSharedCheck_1746_;
goto v_resetjp_1740_;
}
else
{
lean_inc(v_a_1739_);
lean_dec(v___x_1733_);
v___x_1741_ = lean_box(0);
v_isShared_1742_ = v_isSharedCheck_1746_;
goto v_resetjp_1740_;
}
v_resetjp_1740_:
{
lean_object* v___x_1744_; 
if (v_isShared_1742_ == 0)
{
v___x_1744_ = v___x_1741_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v_a_1739_);
v___x_1744_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
return v___x_1744_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___redArg___boxed(lean_object* v_fixedParamPerms_1747_, lean_object* v_xs_1748_, lean_object* v_sz_1749_, lean_object* v_i_1750_, lean_object* v_bs_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_){
_start:
{
size_t v_sz_boxed_1757_; size_t v_i_boxed_1758_; lean_object* v_res_1759_; 
v_sz_boxed_1757_ = lean_unbox_usize(v_sz_1749_);
lean_dec(v_sz_1749_);
v_i_boxed_1758_ = lean_unbox_usize(v_i_1750_);
lean_dec(v_i_1750_);
v_res_1759_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___redArg(v_fixedParamPerms_1747_, v_xs_1748_, v_sz_boxed_1757_, v_i_boxed_1758_, v_bs_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_);
lean_dec(v___y_1755_);
lean_dec_ref(v___y_1754_);
lean_dec(v___y_1753_);
lean_dec_ref(v___y_1752_);
lean_dec_ref(v_fixedParamPerms_1747_);
return v_res_1759_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___redArg(lean_object* v_fixedParamPerms_1760_, lean_object* v_xs_1761_, size_t v_sz_1762_, size_t v_i_1763_, lean_object* v_bs_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_){
_start:
{
uint8_t v___x_1770_; 
v___x_1770_ = lean_usize_dec_lt(v_i_1763_, v_sz_1762_);
if (v___x_1770_ == 0)
{
lean_object* v___x_1771_; 
lean_dec_ref(v_xs_1761_);
v___x_1771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1771_, 0, v_bs_1764_);
return v___x_1771_;
}
else
{
lean_object* v_v_1772_; lean_object* v_perms_1773_; lean_object* v_value_1774_; lean_object* v___x_1775_; lean_object* v_bs_x27_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; 
v_v_1772_ = lean_array_uget_borrowed(v_bs_1764_, v_i_1763_);
v_perms_1773_ = lean_ctor_get(v_fixedParamPerms_1760_, 1);
v_value_1774_ = lean_ctor_get(v_v_1772_, 7);
lean_inc_ref(v_value_1774_);
v___x_1775_ = lean_unsigned_to_nat(0u);
v_bs_x27_1776_ = lean_array_uset(v_bs_1764_, v_i_1763_, v___x_1775_);
v___x_1777_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0);
v___x_1778_ = lean_usize_to_nat(v_i_1763_);
v___x_1779_ = lean_array_get_borrowed(v___x_1777_, v_perms_1773_, v___x_1778_);
lean_dec(v___x_1778_);
lean_inc_ref(v_xs_1761_);
lean_inc(v___x_1779_);
v___x_1780_ = l_Lean_Elab_FixedParamPerm_instantiateLambda(v___x_1779_, v_value_1774_, v_xs_1761_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_);
if (lean_obj_tag(v___x_1780_) == 0)
{
lean_object* v_a_1781_; size_t v___x_1782_; size_t v___x_1783_; lean_object* v___x_1784_; 
v_a_1781_ = lean_ctor_get(v___x_1780_, 0);
lean_inc(v_a_1781_);
lean_dec_ref_known(v___x_1780_, 1);
v___x_1782_ = ((size_t)1ULL);
v___x_1783_ = lean_usize_add(v_i_1763_, v___x_1782_);
v___x_1784_ = lean_array_uset(v_bs_x27_1776_, v_i_1763_, v_a_1781_);
v_i_1763_ = v___x_1783_;
v_bs_1764_ = v___x_1784_;
goto _start;
}
else
{
lean_object* v_a_1786_; lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1793_; 
lean_dec_ref(v_bs_x27_1776_);
lean_dec_ref(v_xs_1761_);
v_a_1786_ = lean_ctor_get(v___x_1780_, 0);
v_isSharedCheck_1793_ = !lean_is_exclusive(v___x_1780_);
if (v_isSharedCheck_1793_ == 0)
{
v___x_1788_ = v___x_1780_;
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
else
{
lean_inc(v_a_1786_);
lean_dec(v___x_1780_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
lean_object* v___x_1791_; 
if (v_isShared_1789_ == 0)
{
v___x_1791_ = v___x_1788_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v_a_1786_);
v___x_1791_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1790_;
}
v_reusejp_1790_:
{
return v___x_1791_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___redArg___boxed(lean_object* v_fixedParamPerms_1794_, lean_object* v_xs_1795_, lean_object* v_sz_1796_, lean_object* v_i_1797_, lean_object* v_bs_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_){
_start:
{
size_t v_sz_boxed_1804_; size_t v_i_boxed_1805_; lean_object* v_res_1806_; 
v_sz_boxed_1804_ = lean_unbox_usize(v_sz_1796_);
lean_dec(v_sz_1796_);
v_i_boxed_1805_ = lean_unbox_usize(v_i_1797_);
lean_dec(v_i_1797_);
v_res_1806_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___redArg(v_fixedParamPerms_1794_, v_xs_1795_, v_sz_boxed_1804_, v_i_boxed_1805_, v_bs_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_);
lean_dec(v___y_1802_);
lean_dec_ref(v___y_1801_);
lean_dec(v___y_1800_);
lean_dec_ref(v___y_1799_);
lean_dec_ref(v_fixedParamPerms_1794_);
return v_res_1806_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11___redArg(lean_object* v_hi_1807_, lean_object* v_pivot_1808_, lean_object* v_as_1809_, lean_object* v_i_1810_, lean_object* v_k_1811_){
_start:
{
uint8_t v___x_1812_; 
v___x_1812_ = lean_nat_dec_lt(v_k_1811_, v_hi_1807_);
if (v___x_1812_ == 0)
{
lean_object* v___x_1813_; lean_object* v___x_1814_; 
lean_dec(v_k_1811_);
v___x_1813_ = lean_array_fswap(v_as_1809_, v_i_1810_, v_hi_1807_);
v___x_1814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1814_, 0, v_i_1810_);
lean_ctor_set(v___x_1814_, 1, v___x_1813_);
return v___x_1814_;
}
else
{
lean_object* v___x_1815_; uint8_t v___x_1816_; 
v___x_1815_ = lean_array_fget_borrowed(v_as_1809_, v_k_1811_);
v___x_1816_ = l_Nat_blt(v___x_1815_, v_pivot_1808_);
if (v___x_1816_ == 0)
{
lean_object* v___x_1817_; lean_object* v___x_1818_; 
v___x_1817_ = lean_unsigned_to_nat(1u);
v___x_1818_ = lean_nat_add(v_k_1811_, v___x_1817_);
lean_dec(v_k_1811_);
v_k_1811_ = v___x_1818_;
goto _start;
}
else
{
lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; 
v___x_1820_ = lean_array_fswap(v_as_1809_, v_i_1810_, v_k_1811_);
v___x_1821_ = lean_unsigned_to_nat(1u);
v___x_1822_ = lean_nat_add(v_i_1810_, v___x_1821_);
lean_dec(v_i_1810_);
v___x_1823_ = lean_nat_add(v_k_1811_, v___x_1821_);
lean_dec(v_k_1811_);
v_as_1809_ = v___x_1820_;
v_i_1810_ = v___x_1822_;
v_k_1811_ = v___x_1823_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11___redArg___boxed(lean_object* v_hi_1825_, lean_object* v_pivot_1826_, lean_object* v_as_1827_, lean_object* v_i_1828_, lean_object* v_k_1829_){
_start:
{
lean_object* v_res_1830_; 
v_res_1830_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11___redArg(v_hi_1825_, v_pivot_1826_, v_as_1827_, v_i_1828_, v_k_1829_);
lean_dec(v_pivot_1826_);
lean_dec(v_hi_1825_);
return v_res_1830_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg(lean_object* v_n_1831_, lean_object* v_as_1832_, lean_object* v_lo_1833_, lean_object* v_hi_1834_){
_start:
{
lean_object* v___y_1836_; uint8_t v___x_1846_; 
v___x_1846_ = lean_nat_dec_lt(v_lo_1833_, v_hi_1834_);
if (v___x_1846_ == 0)
{
lean_dec(v_lo_1833_);
return v_as_1832_;
}
else
{
lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v_mid_1849_; lean_object* v___y_1851_; lean_object* v___y_1857_; lean_object* v___x_1862_; lean_object* v___x_1863_; uint8_t v___x_1864_; 
v___x_1847_ = lean_nat_add(v_lo_1833_, v_hi_1834_);
v___x_1848_ = lean_unsigned_to_nat(1u);
v_mid_1849_ = lean_nat_shiftr(v___x_1847_, v___x_1848_);
lean_dec(v___x_1847_);
v___x_1862_ = lean_array_fget_borrowed(v_as_1832_, v_mid_1849_);
v___x_1863_ = lean_array_fget_borrowed(v_as_1832_, v_lo_1833_);
v___x_1864_ = l_Nat_blt(v___x_1862_, v___x_1863_);
if (v___x_1864_ == 0)
{
v___y_1857_ = v_as_1832_;
goto v___jp_1856_;
}
else
{
lean_object* v___x_1865_; 
v___x_1865_ = lean_array_fswap(v_as_1832_, v_lo_1833_, v_mid_1849_);
v___y_1857_ = v___x_1865_;
goto v___jp_1856_;
}
v___jp_1850_:
{
lean_object* v___x_1852_; lean_object* v___x_1853_; uint8_t v___x_1854_; 
v___x_1852_ = lean_array_fget_borrowed(v___y_1851_, v_mid_1849_);
v___x_1853_ = lean_array_fget_borrowed(v___y_1851_, v_hi_1834_);
v___x_1854_ = l_Nat_blt(v___x_1852_, v___x_1853_);
if (v___x_1854_ == 0)
{
lean_dec(v_mid_1849_);
v___y_1836_ = v___y_1851_;
goto v___jp_1835_;
}
else
{
lean_object* v___x_1855_; 
v___x_1855_ = lean_array_fswap(v___y_1851_, v_mid_1849_, v_hi_1834_);
lean_dec(v_mid_1849_);
v___y_1836_ = v___x_1855_;
goto v___jp_1835_;
}
}
v___jp_1856_:
{
lean_object* v___x_1858_; lean_object* v___x_1859_; uint8_t v___x_1860_; 
v___x_1858_ = lean_array_fget_borrowed(v___y_1857_, v_hi_1834_);
v___x_1859_ = lean_array_fget_borrowed(v___y_1857_, v_lo_1833_);
v___x_1860_ = l_Nat_blt(v___x_1858_, v___x_1859_);
if (v___x_1860_ == 0)
{
v___y_1851_ = v___y_1857_;
goto v___jp_1850_;
}
else
{
lean_object* v___x_1861_; 
v___x_1861_ = lean_array_fswap(v___y_1857_, v_lo_1833_, v_hi_1834_);
v___y_1851_ = v___x_1861_;
goto v___jp_1850_;
}
}
}
v___jp_1835_:
{
lean_object* v_pivot_1837_; lean_object* v___x_1838_; lean_object* v_fst_1839_; lean_object* v_snd_1840_; uint8_t v___x_1841_; 
v_pivot_1837_ = lean_array_fget(v___y_1836_, v_hi_1834_);
lean_inc_n(v_lo_1833_, 2);
v___x_1838_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11___redArg(v_hi_1834_, v_pivot_1837_, v___y_1836_, v_lo_1833_, v_lo_1833_);
lean_dec(v_pivot_1837_);
v_fst_1839_ = lean_ctor_get(v___x_1838_, 0);
lean_inc(v_fst_1839_);
v_snd_1840_ = lean_ctor_get(v___x_1838_, 1);
lean_inc(v_snd_1840_);
lean_dec_ref(v___x_1838_);
v___x_1841_ = lean_nat_dec_le(v_hi_1834_, v_fst_1839_);
if (v___x_1841_ == 0)
{
lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; 
v___x_1842_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg(v_n_1831_, v_snd_1840_, v_lo_1833_, v_fst_1839_);
v___x_1843_ = lean_unsigned_to_nat(1u);
v___x_1844_ = lean_nat_add(v_fst_1839_, v___x_1843_);
lean_dec(v_fst_1839_);
v_as_1832_ = v___x_1842_;
v_lo_1833_ = v___x_1844_;
goto _start;
}
else
{
lean_dec(v_fst_1839_);
lean_dec(v_lo_1833_);
return v_snd_1840_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg___boxed(lean_object* v_n_1866_, lean_object* v_as_1867_, lean_object* v_lo_1868_, lean_object* v_hi_1869_){
_start:
{
lean_object* v_res_1870_; 
v_res_1870_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg(v_n_1866_, v_as_1867_, v_lo_1868_, v_hi_1869_);
lean_dec(v_hi_1869_);
lean_dec(v_n_1866_);
return v_res_1870_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__6(lean_object* v_xs_1871_, lean_object* v_f_1872_, lean_object* v_x_1873_, lean_object* v_as_1874_, size_t v_i_1875_, size_t v_stop_1876_, lean_object* v_b_1877_){
_start:
{
lean_object* v___y_1879_; uint8_t v___x_1883_; 
v___x_1883_ = lean_usize_dec_eq(v_i_1875_, v_stop_1876_);
if (v___x_1883_ == 0)
{
lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; uint8_t v___x_1888_; 
v___x_1884_ = l_Lean_Elab_Structural_instInhabitedRecArgInfo_default;
v___x_1885_ = lean_array_uget_borrowed(v_as_1874_, v_i_1875_);
v___x_1886_ = lean_array_get_borrowed(v___x_1884_, v_xs_1871_, v___x_1885_);
lean_inc_ref(v_f_1872_);
lean_inc(v___x_1886_);
v___x_1887_ = lean_apply_1(v_f_1872_, v___x_1886_);
v___x_1888_ = lean_nat_dec_eq(v___x_1887_, v_x_1873_);
lean_dec(v___x_1887_);
if (v___x_1888_ == 0)
{
v___y_1879_ = v_b_1877_;
goto v___jp_1878_;
}
else
{
lean_object* v___x_1889_; 
lean_inc(v___x_1885_);
v___x_1889_ = lean_array_push(v_b_1877_, v___x_1885_);
v___y_1879_ = v___x_1889_;
goto v___jp_1878_;
}
}
else
{
lean_dec_ref(v_f_1872_);
return v_b_1877_;
}
v___jp_1878_:
{
size_t v___x_1880_; size_t v___x_1881_; 
v___x_1880_ = ((size_t)1ULL);
v___x_1881_ = lean_usize_add(v_i_1875_, v___x_1880_);
v_i_1875_ = v___x_1881_;
v_b_1877_ = v___y_1879_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__6___boxed(lean_object* v_xs_1890_, lean_object* v_f_1891_, lean_object* v_x_1892_, lean_object* v_as_1893_, lean_object* v_i_1894_, lean_object* v_stop_1895_, lean_object* v_b_1896_){
_start:
{
size_t v_i_boxed_1897_; size_t v_stop_boxed_1898_; lean_object* v_res_1899_; 
v_i_boxed_1897_ = lean_unbox_usize(v_i_1894_);
lean_dec(v_i_1894_);
v_stop_boxed_1898_ = lean_unbox_usize(v_stop_1895_);
lean_dec(v_stop_1895_);
v_res_1899_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__6(v_xs_1890_, v_f_1891_, v_x_1892_, v_as_1893_, v_i_boxed_1897_, v_stop_boxed_1898_, v_b_1896_);
lean_dec_ref(v_as_1893_);
lean_dec(v_x_1892_);
lean_dec_ref(v_xs_1890_);
return v_res_1899_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8(lean_object* v_xs_1902_, lean_object* v_f_1903_, size_t v_sz_1904_, size_t v_i_1905_, lean_object* v_bs_1906_){
_start:
{
uint8_t v___x_1907_; 
v___x_1907_ = lean_usize_dec_lt(v_i_1905_, v_sz_1904_);
if (v___x_1907_ == 0)
{
lean_dec_ref(v_f_1903_);
return v_bs_1906_;
}
else
{
lean_object* v_v_1908_; lean_object* v___x_1909_; lean_object* v_bs_x27_1910_; lean_object* v___y_1912_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; uint8_t v___x_1921_; 
v_v_1908_ = lean_array_uget(v_bs_1906_, v_i_1905_);
v___x_1909_ = lean_unsigned_to_nat(0u);
v_bs_x27_1910_ = lean_array_uset(v_bs_1906_, v_i_1905_, v___x_1909_);
v___x_1917_ = lean_array_get_size(v_xs_1902_);
v___x_1918_ = l_Array_range(v___x_1917_);
v___x_1919_ = lean_array_get_size(v___x_1918_);
v___x_1920_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8___closed__0));
v___x_1921_ = lean_nat_dec_lt(v___x_1909_, v___x_1919_);
if (v___x_1921_ == 0)
{
lean_dec_ref(v___x_1918_);
lean_dec(v_v_1908_);
v___y_1912_ = v___x_1920_;
goto v___jp_1911_;
}
else
{
size_t v___x_1922_; size_t v___x_1923_; lean_object* v___x_1924_; 
v___x_1922_ = ((size_t)0ULL);
v___x_1923_ = lean_usize_of_nat(v___x_1919_);
lean_inc_ref(v_f_1903_);
v___x_1924_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__6(v_xs_1902_, v_f_1903_, v_v_1908_, v___x_1918_, v___x_1922_, v___x_1923_, v___x_1920_);
lean_dec_ref(v___x_1918_);
lean_dec(v_v_1908_);
v___y_1912_ = v___x_1924_;
goto v___jp_1911_;
}
v___jp_1911_:
{
size_t v___x_1913_; size_t v___x_1914_; lean_object* v___x_1915_; 
v___x_1913_ = ((size_t)1ULL);
v___x_1914_ = lean_usize_add(v_i_1905_, v___x_1913_);
v___x_1915_ = lean_array_uset(v_bs_x27_1910_, v_i_1905_, v___y_1912_);
v_i_1905_ = v___x_1914_;
v_bs_1906_ = v___x_1915_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8___boxed(lean_object* v_xs_1925_, lean_object* v_f_1926_, lean_object* v_sz_1927_, lean_object* v_i_1928_, lean_object* v_bs_1929_){
_start:
{
size_t v_sz_boxed_1930_; size_t v_i_boxed_1931_; lean_object* v_res_1932_; 
v_sz_boxed_1930_ = lean_unbox_usize(v_sz_1927_);
lean_dec(v_sz_1927_);
v_i_boxed_1931_ = lean_unbox_usize(v_i_1928_);
lean_dec(v_i_1928_);
v_res_1932_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8(v_xs_1925_, v_f_1926_, v_sz_boxed_1930_, v_i_boxed_1931_, v_bs_1929_);
lean_dec_ref(v_xs_1925_);
return v_res_1932_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__11(lean_object* v_as_1933_, size_t v_i_1934_, size_t v_stop_1935_, lean_object* v_b_1936_){
_start:
{
uint8_t v___x_1937_; 
v___x_1937_ = lean_usize_dec_eq(v_i_1934_, v_stop_1935_);
if (v___x_1937_ == 0)
{
lean_object* v___x_1938_; lean_object* v___x_1939_; size_t v___x_1940_; size_t v___x_1941_; 
v___x_1938_ = lean_array_uget_borrowed(v_as_1933_, v_i_1934_);
v___x_1939_ = l_Array_append___redArg(v_b_1936_, v___x_1938_);
v___x_1940_ = ((size_t)1ULL);
v___x_1941_ = lean_usize_add(v_i_1934_, v___x_1940_);
v_i_1934_ = v___x_1941_;
v_b_1936_ = v___x_1939_;
goto _start;
}
else
{
return v_b_1936_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__11___boxed(lean_object* v_as_1943_, lean_object* v_i_1944_, lean_object* v_stop_1945_, lean_object* v_b_1946_){
_start:
{
size_t v_i_boxed_1947_; size_t v_stop_boxed_1948_; lean_object* v_res_1949_; 
v_i_boxed_1947_ = lean_unbox_usize(v_i_1944_);
lean_dec(v_i_1944_);
v_stop_boxed_1948_ = lean_unbox_usize(v_stop_1945_);
lean_dec(v_stop_1945_);
v_res_1949_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__11(v_as_1943_, v_i_boxed_1947_, v_stop_boxed_1948_, v_b_1946_);
lean_dec_ref(v_as_1943_);
return v_res_1949_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__7___closed__0(void){
_start:
{
lean_object* v___x_1950_; 
v___x_1950_ = l_Array_instInhabited(lean_box(0));
return v___x_1950_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__7(lean_object* v_msg_1951_){
_start:
{
lean_object* v___x_1952_; lean_object* v___x_1953_; 
v___x_1952_ = lean_obj_once(&l_panic___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__7___closed__0, &l_panic___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__7___closed__0_once, _init_l_panic___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__7___closed__0);
v___x_1953_ = lean_panic_fn_borrowed(v___x_1952_, v_msg_1951_);
return v___x_1953_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9___redArg(lean_object* v_xs_1954_, lean_object* v_ys_1955_, lean_object* v_x_1956_){
_start:
{
lean_object* v_zero_1957_; uint8_t v_isZero_1958_; 
v_zero_1957_ = lean_unsigned_to_nat(0u);
v_isZero_1958_ = lean_nat_dec_eq(v_x_1956_, v_zero_1957_);
if (v_isZero_1958_ == 1)
{
lean_dec(v_x_1956_);
return v_isZero_1958_;
}
else
{
lean_object* v_one_1959_; lean_object* v_n_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; uint8_t v___x_1963_; 
v_one_1959_ = lean_unsigned_to_nat(1u);
v_n_1960_ = lean_nat_sub(v_x_1956_, v_one_1959_);
lean_dec(v_x_1956_);
v___x_1961_ = lean_array_fget_borrowed(v_xs_1954_, v_n_1960_);
v___x_1962_ = lean_array_fget_borrowed(v_ys_1955_, v_n_1960_);
v___x_1963_ = lean_nat_dec_eq(v___x_1961_, v___x_1962_);
if (v___x_1963_ == 0)
{
lean_dec(v_n_1960_);
return v___x_1963_;
}
else
{
v_x_1956_ = v_n_1960_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9___redArg___boxed(lean_object* v_xs_1965_, lean_object* v_ys_1966_, lean_object* v_x_1967_){
_start:
{
uint8_t v_res_1968_; lean_object* v_r_1969_; 
v_res_1968_ = l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9___redArg(v_xs_1965_, v_ys_1966_, v_x_1967_);
lean_dec_ref(v_ys_1966_);
lean_dec_ref(v_xs_1965_);
v_r_1969_ = lean_box(v_res_1968_);
return v_r_1969_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__2(void){
_start:
{
lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; 
v___x_1972_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__1));
v___x_1973_ = lean_unsigned_to_nat(2u);
v___x_1974_ = lean_unsigned_to_nat(63u);
v___x_1975_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__0));
v___x_1976_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__0));
v___x_1977_ = l_mkPanicMessageWithDecl(v___x_1976_, v___x_1975_, v___x_1974_, v___x_1973_, v___x_1972_);
return v___x_1977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5(lean_object* v_f_1980_, lean_object* v_xs_1981_, lean_object* v_ys_1982_){
_start:
{
size_t v_sz_1986_; size_t v___x_1987_; lean_object* v_positions_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___y_1992_; lean_object* v___y_1998_; lean_object* v___y_1999_; lean_object* v___y_2000_; lean_object* v___y_2001_; lean_object* v___y_2004_; lean_object* v___y_2005_; lean_object* v___y_2006_; lean_object* v___y_2007_; lean_object* v___y_2010_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; uint8_t v___x_2020_; 
v_sz_1986_ = lean_array_size(v_ys_1982_);
v___x_1987_ = ((size_t)0ULL);
v_positions_1988_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8(v_xs_1981_, v_f_1980_, v_sz_1986_, v___x_1987_, v_ys_1982_);
v___x_1989_ = lean_array_get_size(v_xs_1981_);
v___x_1990_ = l_Array_range(v___x_1989_);
v___x_2017_ = lean_unsigned_to_nat(0u);
v___x_2018_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__3));
v___x_2019_ = lean_array_get_size(v_positions_1988_);
v___x_2020_ = lean_nat_dec_lt(v___x_2017_, v___x_2019_);
if (v___x_2020_ == 0)
{
v___y_2010_ = v___x_2018_;
goto v___jp_2009_;
}
else
{
size_t v___x_2021_; lean_object* v___x_2022_; 
v___x_2021_ = lean_usize_of_nat(v___x_2019_);
v___x_2022_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__11(v_positions_1988_, v___x_1987_, v___x_2021_, v___x_2018_);
v___y_2010_ = v___x_2022_;
goto v___jp_2009_;
}
v___jp_1983_:
{
lean_object* v___x_1984_; lean_object* v___x_1985_; 
v___x_1984_ = lean_obj_once(&l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__2, &l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__2_once, _init_l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__2);
v___x_1985_ = l_panic___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__7(v___x_1984_);
return v___x_1985_;
}
v___jp_1991_:
{
lean_object* v___x_1993_; lean_object* v___x_1994_; uint8_t v___x_1995_; 
v___x_1993_ = lean_array_get_size(v___x_1990_);
v___x_1994_ = lean_array_get_size(v___y_1992_);
v___x_1995_ = lean_nat_dec_eq(v___x_1993_, v___x_1994_);
if (v___x_1995_ == 0)
{
lean_dec_ref(v___y_1992_);
lean_dec_ref(v___x_1990_);
lean_dec_ref(v_positions_1988_);
goto v___jp_1983_;
}
else
{
uint8_t v___x_1996_; 
v___x_1996_ = l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9___redArg(v___x_1990_, v___y_1992_, v___x_1993_);
lean_dec_ref(v___y_1992_);
lean_dec_ref(v___x_1990_);
if (v___x_1996_ == 0)
{
lean_dec_ref(v_positions_1988_);
goto v___jp_1983_;
}
else
{
return v_positions_1988_;
}
}
}
v___jp_1997_:
{
lean_object* v___x_2002_; 
v___x_2002_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg(v___y_2000_, v___y_1999_, v___y_1998_, v___y_2001_);
lean_dec(v___y_2001_);
lean_dec(v___y_2000_);
v___y_1992_ = v___x_2002_;
goto v___jp_1991_;
}
v___jp_2003_:
{
uint8_t v___x_2008_; 
v___x_2008_ = lean_nat_dec_le(v___y_2007_, v___y_2004_);
if (v___x_2008_ == 0)
{
lean_dec(v___y_2004_);
lean_inc(v___y_2007_);
v___y_1998_ = v___y_2007_;
v___y_1999_ = v___y_2005_;
v___y_2000_ = v___y_2006_;
v___y_2001_ = v___y_2007_;
goto v___jp_1997_;
}
else
{
v___y_1998_ = v___y_2007_;
v___y_1999_ = v___y_2005_;
v___y_2000_ = v___y_2006_;
v___y_2001_ = v___y_2004_;
goto v___jp_1997_;
}
}
v___jp_2009_:
{
lean_object* v___x_2011_; lean_object* v___x_2012_; uint8_t v___x_2013_; 
v___x_2011_ = lean_array_get_size(v___y_2010_);
v___x_2012_ = lean_unsigned_to_nat(0u);
v___x_2013_ = lean_nat_dec_eq(v___x_2011_, v___x_2012_);
if (v___x_2013_ == 0)
{
lean_object* v___x_2014_; lean_object* v___x_2015_; uint8_t v___x_2016_; 
v___x_2014_ = lean_unsigned_to_nat(1u);
v___x_2015_ = lean_nat_sub(v___x_2011_, v___x_2014_);
v___x_2016_ = lean_nat_dec_le(v___x_2012_, v___x_2015_);
if (v___x_2016_ == 0)
{
lean_inc(v___x_2015_);
v___y_2004_ = v___x_2015_;
v___y_2005_ = v___y_2010_;
v___y_2006_ = v___x_2011_;
v___y_2007_ = v___x_2015_;
goto v___jp_2003_;
}
else
{
v___y_2004_ = v___x_2015_;
v___y_2005_ = v___y_2010_;
v___y_2006_ = v___x_2011_;
v___y_2007_ = v___x_2012_;
goto v___jp_2003_;
}
}
else
{
v___y_1992_ = v___y_2010_;
goto v___jp_1991_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___boxed(lean_object* v_f_2023_, lean_object* v_xs_2024_, lean_object* v_ys_2025_){
_start:
{
lean_object* v_res_2026_; 
v_res_2026_ = l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5(v_f_2023_, v_xs_2024_, v_ys_2025_);
lean_dec_ref(v_xs_2024_);
return v_res_2026_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__0(lean_object* v_a_2027_, lean_object* v_a_2028_){
_start:
{
if (lean_obj_tag(v_a_2027_) == 0)
{
lean_object* v___x_2029_; 
v___x_2029_ = l_List_reverse___redArg(v_a_2028_);
return v___x_2029_;
}
else
{
lean_object* v_head_2030_; lean_object* v_tail_2031_; lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2042_; 
v_head_2030_ = lean_ctor_get(v_a_2027_, 0);
v_tail_2031_ = lean_ctor_get(v_a_2027_, 1);
v_isSharedCheck_2042_ = !lean_is_exclusive(v_a_2027_);
if (v_isSharedCheck_2042_ == 0)
{
v___x_2033_ = v_a_2027_;
v_isShared_2034_ = v_isSharedCheck_2042_;
goto v_resetjp_2032_;
}
else
{
lean_inc(v_tail_2031_);
lean_inc(v_head_2030_);
lean_dec(v_a_2027_);
v___x_2033_ = lean_box(0);
v_isShared_2034_ = v_isSharedCheck_2042_;
goto v_resetjp_2032_;
}
v_resetjp_2032_:
{
lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2039_; 
v___x_2035_ = l_Nat_reprFast(v_head_2030_);
v___x_2036_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2036_, 0, v___x_2035_);
v___x_2037_ = l_Lean_MessageData_ofFormat(v___x_2036_);
if (v_isShared_2034_ == 0)
{
lean_ctor_set(v___x_2033_, 1, v_a_2028_);
lean_ctor_set(v___x_2033_, 0, v___x_2037_);
v___x_2039_ = v___x_2033_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v___x_2037_);
lean_ctor_set(v_reuseFailAlloc_2041_, 1, v_a_2028_);
v___x_2039_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2038_;
}
v_reusejp_2038_:
{
v_a_2027_ = v_tail_2031_;
v_a_2028_ = v___x_2039_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__20(lean_object* v_a_2043_, lean_object* v_a_2044_){
_start:
{
if (lean_obj_tag(v_a_2043_) == 0)
{
lean_object* v___x_2045_; 
v___x_2045_ = l_List_reverse___redArg(v_a_2044_);
return v___x_2045_;
}
else
{
lean_object* v_head_2046_; lean_object* v_tail_2047_; lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2059_; 
v_head_2046_ = lean_ctor_get(v_a_2043_, 0);
v_tail_2047_ = lean_ctor_get(v_a_2043_, 1);
v_isSharedCheck_2059_ = !lean_is_exclusive(v_a_2043_);
if (v_isSharedCheck_2059_ == 0)
{
v___x_2049_ = v_a_2043_;
v_isShared_2050_ = v_isSharedCheck_2059_;
goto v_resetjp_2048_;
}
else
{
lean_inc(v_tail_2047_);
lean_inc(v_head_2046_);
lean_dec(v_a_2043_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2059_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2056_; 
v___x_2051_ = lean_array_to_list(v_head_2046_);
v___x_2052_ = lean_box(0);
v___x_2053_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__0(v___x_2051_, v___x_2052_);
v___x_2054_ = l_Lean_MessageData_ofList(v___x_2053_);
if (v_isShared_2050_ == 0)
{
lean_ctor_set(v___x_2049_, 1, v_a_2044_);
lean_ctor_set(v___x_2049_, 0, v___x_2054_);
v___x_2056_ = v___x_2049_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2058_; 
v_reuseFailAlloc_2058_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2058_, 0, v___x_2054_);
lean_ctor_set(v_reuseFailAlloc_2058_, 1, v_a_2044_);
v___x_2056_ = v_reuseFailAlloc_2058_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
v_a_2043_ = v_tail_2047_;
v_a_2044_ = v___x_2056_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__9(void){
_start:
{
lean_object* v___x_2074_; lean_object* v___x_2075_; 
v___x_2074_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__8));
v___x_2075_ = l_Lean_stringToMessageData(v___x_2074_);
return v___x_2075_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__11(void){
_start:
{
lean_object* v___x_2077_; lean_object* v___x_2078_; 
v___x_2077_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__10));
v___x_2078_ = l_Lean_stringToMessageData(v___x_2077_);
return v___x_2078_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion(lean_object* v_preDefs_2079_, lean_object* v_fixedParamPerms_2080_, lean_object* v_xs_2081_, lean_object* v_recArgInfos_2082_, lean_object* v_a_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_, lean_object* v_a_2086_){
_start:
{
size_t v_sz_2088_; size_t v___x_2089_; lean_object* v___x_2090_; 
v_sz_2088_ = lean_array_size(v_preDefs_2079_);
v___x_2089_ = ((size_t)0ULL);
lean_inc_ref(v_preDefs_2079_);
lean_inc_ref(v_xs_2081_);
v___x_2090_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___redArg(v_fixedParamPerms_2080_, v_xs_2081_, v_sz_2088_, v___x_2089_, v_preDefs_2079_, v_a_2083_, v_a_2084_, v_a_2085_, v_a_2086_);
if (lean_obj_tag(v___x_2090_) == 0)
{
lean_object* v_a_2091_; lean_object* v___x_2092_; 
v_a_2091_ = lean_ctor_get(v___x_2090_, 0);
lean_inc(v_a_2091_);
lean_dec_ref_known(v___x_2090_, 1);
lean_inc_ref(v_preDefs_2079_);
lean_inc_ref(v_xs_2081_);
v___x_2092_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___redArg(v_fixedParamPerms_2080_, v_xs_2081_, v_sz_2088_, v___x_2089_, v_preDefs_2079_, v_a_2083_, v_a_2084_, v_a_2085_, v_a_2086_);
if (lean_obj_tag(v___x_2092_) == 0)
{
lean_object* v_a_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v_indGroupInst_2097_; lean_object* v_toIndGroupInfo_2098_; lean_object* v_all_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2187_; 
v_a_2093_ = lean_ctor_get(v___x_2092_, 0);
lean_inc(v_a_2093_);
lean_dec_ref_known(v___x_2092_, 1);
v___x_2094_ = l_Lean_Elab_Structural_instInhabitedRecArgInfo_default;
v___x_2095_ = lean_unsigned_to_nat(0u);
v___x_2096_ = lean_array_get_borrowed(v___x_2094_, v_recArgInfos_2082_, v___x_2095_);
v_indGroupInst_2097_ = lean_ctor_get(v___x_2096_, 4);
v_toIndGroupInfo_2098_ = lean_ctor_get(v_indGroupInst_2097_, 0);
lean_inc_ref(v_toIndGroupInfo_2098_);
v_all_2099_ = lean_ctor_get(v_toIndGroupInfo_2098_, 0);
v_isSharedCheck_2187_ = !lean_is_exclusive(v_toIndGroupInfo_2098_);
if (v_isSharedCheck_2187_ == 0)
{
lean_object* v_unused_2188_; 
v_unused_2188_ = lean_ctor_get(v_toIndGroupInfo_2098_, 1);
lean_dec(v_unused_2188_);
v___x_2101_ = v_toIndGroupInfo_2098_;
v_isShared_2102_ = v_isSharedCheck_2187_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_all_2099_);
lean_dec(v_toIndGroupInfo_2098_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2187_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; 
v___x_2103_ = lean_box(0);
v___x_2104_ = lean_array_get(v___x_2103_, v_all_2099_, v___x_2095_);
lean_dec_ref(v_all_2099_);
v___x_2105_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4(v___x_2104_, v_a_2083_, v_a_2084_, v_a_2085_, v_a_2086_);
if (lean_obj_tag(v___x_2105_) == 0)
{
lean_object* v_a_2106_; lean_object* v___x_2107_; lean_object* v___f_2108_; lean_object* v___x_2109_; lean_object* v_a_2110_; lean_object* v___f_2111_; lean_object* v___f_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___y_2118_; lean_object* v___y_2119_; lean_object* v___y_2120_; lean_object* v___y_2121_; uint8_t v___x_2155_; 
v_a_2106_ = lean_ctor_get(v___x_2105_, 0);
lean_inc(v_a_2106_);
lean_dec_ref_known(v___x_2105_, 1);
v___x_2107_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__3));
v___f_2108_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__4));
v___x_2109_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0(v___x_2107_, v_a_2083_, v_a_2084_, v_a_2085_, v_a_2086_);
v_a_2110_ = lean_ctor_get(v___x_2109_, 0);
lean_inc(v_a_2110_);
lean_dec_ref(v___x_2109_);
v___f_2111_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__5));
v___f_2112_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__6));
v___x_2113_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_2114_ = l_Lean_InductiveVal_numTypeFormers(v_a_2106_);
v___x_2115_ = l_Array_range(v___x_2114_);
v___x_2116_ = l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5(v___f_2112_, v_recArgInfos_2082_, v___x_2115_);
v___x_2155_ = lean_unbox(v_a_2110_);
lean_dec(v_a_2110_);
if (v___x_2155_ == 0)
{
lean_del_object(v___x_2101_);
v___y_2118_ = v_a_2083_;
v___y_2119_ = v_a_2084_;
v___y_2120_ = v_a_2085_;
v___y_2121_ = v_a_2086_;
goto v___jp_2117_;
}
else
{
lean_object* v_toConstantVal_2156_; lean_object* v_name_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2161_; 
v_toConstantVal_2156_ = lean_ctor_get(v_a_2106_, 0);
v_name_2157_ = lean_ctor_get(v_toConstantVal_2156_, 0);
v___x_2158_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__9, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__9_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__9);
lean_inc(v_name_2157_);
v___x_2159_ = l_Lean_MessageData_ofName(v_name_2157_);
if (v_isShared_2102_ == 0)
{
lean_ctor_set_tag(v___x_2101_, 7);
lean_ctor_set(v___x_2101_, 1, v___x_2159_);
lean_ctor_set(v___x_2101_, 0, v___x_2158_);
v___x_2161_ = v___x_2101_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v___x_2158_);
lean_ctor_set(v_reuseFailAlloc_2178_, 1, v___x_2159_);
v___x_2161_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; 
v___x_2162_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__11, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__11_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__11);
v___x_2163_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2163_, 0, v___x_2161_);
lean_ctor_set(v___x_2163_, 1, v___x_2162_);
lean_inc_ref(v___x_2116_);
v___x_2164_ = lean_array_to_list(v___x_2116_);
v___x_2165_ = lean_box(0);
v___x_2166_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__20(v___x_2164_, v___x_2165_);
v___x_2167_ = l_Lean_MessageData_ofList(v___x_2166_);
v___x_2168_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2168_, 0, v___x_2163_);
lean_ctor_set(v___x_2168_, 1, v___x_2167_);
v___x_2169_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_2107_, v___x_2168_, v_a_2083_, v_a_2084_, v_a_2085_, v_a_2086_);
if (lean_obj_tag(v___x_2169_) == 0)
{
lean_dec_ref_known(v___x_2169_, 1);
v___y_2118_ = v_a_2083_;
v___y_2119_ = v_a_2084_;
v___y_2120_ = v_a_2085_;
v___y_2121_ = v_a_2086_;
goto v___jp_2117_;
}
else
{
lean_object* v_a_2170_; lean_object* v___x_2172_; uint8_t v_isShared_2173_; uint8_t v_isSharedCheck_2177_; 
lean_dec_ref(v___x_2116_);
lean_dec(v_a_2106_);
lean_dec(v_a_2093_);
lean_dec(v_a_2091_);
lean_dec_ref(v_recArgInfos_2082_);
lean_dec_ref(v_xs_2081_);
lean_dec_ref(v_fixedParamPerms_2080_);
lean_dec_ref(v_preDefs_2079_);
v_a_2170_ = lean_ctor_get(v___x_2169_, 0);
v_isSharedCheck_2177_ = !lean_is_exclusive(v___x_2169_);
if (v_isSharedCheck_2177_ == 0)
{
v___x_2172_ = v___x_2169_;
v_isShared_2173_ = v_isSharedCheck_2177_;
goto v_resetjp_2171_;
}
else
{
lean_inc(v_a_2170_);
lean_dec(v___x_2169_);
v___x_2172_ = lean_box(0);
v_isShared_2173_ = v_isSharedCheck_2177_;
goto v_resetjp_2171_;
}
v_resetjp_2171_:
{
lean_object* v___x_2175_; 
if (v_isShared_2173_ == 0)
{
v___x_2175_ = v___x_2172_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v_a_2170_);
v___x_2175_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
return v___x_2175_;
}
}
}
}
}
v___jp_2117_:
{
lean_object* v_toConstantVal_2122_; lean_object* v_numIndices_2123_; lean_object* v_name_2124_; lean_object* v___x_2125_; 
v_toConstantVal_2122_ = lean_ctor_get(v_a_2106_, 0);
lean_inc_ref(v_toConstantVal_2122_);
v_numIndices_2123_ = lean_ctor_get(v_a_2106_, 2);
lean_inc(v_numIndices_2123_);
lean_dec(v_a_2106_);
v_name_2124_ = lean_ctor_get(v_toConstantVal_2122_, 0);
lean_inc(v_name_2124_);
lean_dec_ref(v_toConstantVal_2122_);
v___x_2125_ = l_Lean_Meta_isInductivePredicate(v_name_2124_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_);
if (lean_obj_tag(v___x_2125_) == 0)
{
lean_object* v_a_2126_; lean_object* v___x_2127_; lean_object* v___f_2128_; uint8_t v___x_2129_; 
v_a_2126_ = lean_ctor_get(v___x_2125_, 0);
lean_inc_n(v_a_2126_, 2);
lean_dec_ref_known(v___x_2125_, 1);
v___x_2127_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___boxed__const__1));
lean_inc(v_numIndices_2123_);
lean_inc_ref(v_preDefs_2079_);
lean_inc_ref(v_xs_2081_);
lean_inc_ref(v_fixedParamPerms_2080_);
lean_inc_ref(v___x_2116_);
lean_inc(v_a_2091_);
lean_inc_ref(v_recArgInfos_2082_);
v___f_2128_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___boxed), 21, 14);
lean_closure_set(v___f_2128_, 0, v___f_2108_);
lean_closure_set(v___f_2128_, 1, v_recArgInfos_2082_);
lean_closure_set(v___f_2128_, 2, v_a_2091_);
lean_closure_set(v___f_2128_, 3, v___x_2116_);
lean_closure_set(v___f_2128_, 4, v___x_2127_);
lean_closure_set(v___f_2128_, 5, v_fixedParamPerms_2080_);
lean_closure_set(v___f_2128_, 6, v_xs_2081_);
lean_closure_set(v___f_2128_, 7, v___x_2095_);
lean_closure_set(v___f_2128_, 8, v_preDefs_2079_);
lean_closure_set(v___f_2128_, 9, v_numIndices_2123_);
lean_closure_set(v___f_2128_, 10, v___f_2111_);
lean_closure_set(v___f_2128_, 11, v___x_2107_);
lean_closure_set(v___f_2128_, 12, v_a_2126_);
lean_closure_set(v___f_2128_, 13, v___x_2113_);
v___x_2129_ = lean_unbox(v_a_2126_);
if (v___x_2129_ == 0)
{
size_t v_sz_2130_; lean_object* v___x_2131_; 
lean_dec_ref(v___f_2128_);
v_sz_2130_ = lean_array_size(v_recArgInfos_2082_);
lean_inc_ref(v_recArgInfos_2082_);
v___x_2131_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___redArg(v_a_2091_, v_a_2093_, v_sz_2130_, v___x_2089_, v_recArgInfos_2082_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_);
lean_dec(v_a_2093_);
if (lean_obj_tag(v___x_2131_) == 0)
{
lean_object* v_a_2132_; lean_object* v___x_2133_; uint8_t v___x_2134_; lean_object* v___x_2135_; 
v_a_2132_ = lean_ctor_get(v___x_2131_, 0);
lean_inc(v_a_2132_);
lean_dec_ref_known(v___x_2131_, 1);
v___x_2133_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__7));
v___x_2134_ = lean_unbox(v_a_2126_);
lean_dec(v_a_2126_);
v___x_2135_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2(v___f_2108_, v_recArgInfos_2082_, v_a_2091_, v___x_2116_, v___x_2089_, v_fixedParamPerms_2080_, v_xs_2081_, v___x_2095_, v_preDefs_2079_, v_numIndices_2123_, v___f_2111_, v___x_2107_, v___x_2134_, v___x_2113_, v___x_2133_, v_a_2132_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_);
lean_dec(v_numIndices_2123_);
lean_dec(v_a_2091_);
return v___x_2135_;
}
else
{
lean_object* v_a_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2143_; 
lean_dec(v_a_2126_);
lean_dec(v_numIndices_2123_);
lean_dec_ref(v___x_2116_);
lean_dec(v_a_2091_);
lean_dec_ref(v_recArgInfos_2082_);
lean_dec_ref(v_xs_2081_);
lean_dec_ref(v_fixedParamPerms_2080_);
lean_dec_ref(v_preDefs_2079_);
v_a_2136_ = lean_ctor_get(v___x_2131_, 0);
v_isSharedCheck_2143_ = !lean_is_exclusive(v___x_2131_);
if (v_isSharedCheck_2143_ == 0)
{
v___x_2138_ = v___x_2131_;
v_isShared_2139_ = v_isSharedCheck_2143_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_a_2136_);
lean_dec(v___x_2131_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2143_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v___x_2141_; 
if (v_isShared_2139_ == 0)
{
v___x_2141_ = v___x_2138_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v_a_2136_);
v___x_2141_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
return v___x_2141_;
}
}
}
}
else
{
lean_object* v___x_2144_; lean_object* v___f_2145_; lean_object* v___x_2146_; 
lean_dec(v_a_2126_);
lean_dec(v_numIndices_2123_);
lean_dec_ref(v___x_2116_);
lean_dec(v_a_2093_);
lean_dec_ref(v_xs_2081_);
lean_dec_ref(v_fixedParamPerms_2080_);
lean_dec_ref(v_preDefs_2079_);
v___x_2144_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___boxed__const__1));
lean_inc(v_a_2091_);
v___f_2145_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__3___boxed), 10, 4);
lean_closure_set(v___f_2145_, 0, v_recArgInfos_2082_);
lean_closure_set(v___f_2145_, 1, v_a_2091_);
lean_closure_set(v___f_2145_, 2, v___x_2144_);
lean_closure_set(v___f_2145_, 3, v___f_2128_);
v___x_2146_ = l_Lean_Elab_Structural_withFunTypes___redArg(v_a_2091_, v___f_2145_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_);
return v___x_2146_;
}
}
else
{
lean_object* v_a_2147_; lean_object* v___x_2149_; uint8_t v_isShared_2150_; uint8_t v_isSharedCheck_2154_; 
lean_dec(v_numIndices_2123_);
lean_dec_ref(v___x_2116_);
lean_dec(v_a_2093_);
lean_dec(v_a_2091_);
lean_dec_ref(v_recArgInfos_2082_);
lean_dec_ref(v_xs_2081_);
lean_dec_ref(v_fixedParamPerms_2080_);
lean_dec_ref(v_preDefs_2079_);
v_a_2147_ = lean_ctor_get(v___x_2125_, 0);
v_isSharedCheck_2154_ = !lean_is_exclusive(v___x_2125_);
if (v_isSharedCheck_2154_ == 0)
{
v___x_2149_ = v___x_2125_;
v_isShared_2150_ = v_isSharedCheck_2154_;
goto v_resetjp_2148_;
}
else
{
lean_inc(v_a_2147_);
lean_dec(v___x_2125_);
v___x_2149_ = lean_box(0);
v_isShared_2150_ = v_isSharedCheck_2154_;
goto v_resetjp_2148_;
}
v_resetjp_2148_:
{
lean_object* v___x_2152_; 
if (v_isShared_2150_ == 0)
{
v___x_2152_ = v___x_2149_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v_a_2147_);
v___x_2152_ = v_reuseFailAlloc_2153_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
return v___x_2152_;
}
}
}
}
}
else
{
lean_object* v_a_2179_; lean_object* v___x_2181_; uint8_t v_isShared_2182_; uint8_t v_isSharedCheck_2186_; 
lean_del_object(v___x_2101_);
lean_dec(v_a_2093_);
lean_dec(v_a_2091_);
lean_dec_ref(v_recArgInfos_2082_);
lean_dec_ref(v_xs_2081_);
lean_dec_ref(v_fixedParamPerms_2080_);
lean_dec_ref(v_preDefs_2079_);
v_a_2179_ = lean_ctor_get(v___x_2105_, 0);
v_isSharedCheck_2186_ = !lean_is_exclusive(v___x_2105_);
if (v_isSharedCheck_2186_ == 0)
{
v___x_2181_ = v___x_2105_;
v_isShared_2182_ = v_isSharedCheck_2186_;
goto v_resetjp_2180_;
}
else
{
lean_inc(v_a_2179_);
lean_dec(v___x_2105_);
v___x_2181_ = lean_box(0);
v_isShared_2182_ = v_isSharedCheck_2186_;
goto v_resetjp_2180_;
}
v_resetjp_2180_:
{
lean_object* v___x_2184_; 
if (v_isShared_2182_ == 0)
{
v___x_2184_ = v___x_2181_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v_a_2179_);
v___x_2184_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
return v___x_2184_;
}
}
}
}
}
else
{
lean_object* v_a_2189_; lean_object* v___x_2191_; uint8_t v_isShared_2192_; uint8_t v_isSharedCheck_2196_; 
lean_dec(v_a_2091_);
lean_dec_ref(v_recArgInfos_2082_);
lean_dec_ref(v_xs_2081_);
lean_dec_ref(v_fixedParamPerms_2080_);
lean_dec_ref(v_preDefs_2079_);
v_a_2189_ = lean_ctor_get(v___x_2092_, 0);
v_isSharedCheck_2196_ = !lean_is_exclusive(v___x_2092_);
if (v_isSharedCheck_2196_ == 0)
{
v___x_2191_ = v___x_2092_;
v_isShared_2192_ = v_isSharedCheck_2196_;
goto v_resetjp_2190_;
}
else
{
lean_inc(v_a_2189_);
lean_dec(v___x_2092_);
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
else
{
lean_object* v_a_2197_; lean_object* v___x_2199_; uint8_t v_isShared_2200_; uint8_t v_isSharedCheck_2204_; 
lean_dec_ref(v_recArgInfos_2082_);
lean_dec_ref(v_xs_2081_);
lean_dec_ref(v_fixedParamPerms_2080_);
lean_dec_ref(v_preDefs_2079_);
v_a_2197_ = lean_ctor_get(v___x_2090_, 0);
v_isSharedCheck_2204_ = !lean_is_exclusive(v___x_2090_);
if (v_isSharedCheck_2204_ == 0)
{
v___x_2199_ = v___x_2090_;
v_isShared_2200_ = v_isSharedCheck_2204_;
goto v_resetjp_2198_;
}
else
{
lean_inc(v_a_2197_);
lean_dec(v___x_2090_);
v___x_2199_ = lean_box(0);
v_isShared_2200_ = v_isSharedCheck_2204_;
goto v_resetjp_2198_;
}
v_resetjp_2198_:
{
lean_object* v___x_2202_; 
if (v_isShared_2200_ == 0)
{
v___x_2202_ = v___x_2199_;
goto v_reusejp_2201_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v_a_2197_);
v___x_2202_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2201_;
}
v_reusejp_2201_:
{
return v___x_2202_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___boxed(lean_object* v_preDefs_2205_, lean_object* v_fixedParamPerms_2206_, lean_object* v_xs_2207_, lean_object* v_recArgInfos_2208_, lean_object* v_a_2209_, lean_object* v_a_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_){
_start:
{
lean_object* v_res_2214_; 
v_res_2214_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion(v_preDefs_2205_, v_fixedParamPerms_2206_, v_xs_2207_, v_recArgInfos_2208_, v_a_2209_, v_a_2210_, v_a_2211_, v_a_2212_);
lean_dec(v_a_2212_);
lean_dec_ref(v_a_2211_);
lean_dec(v_a_2210_);
lean_dec_ref(v_a_2209_);
return v_res_2214_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2(lean_object* v_fixedParamPerms_2215_, lean_object* v_xs_2216_, lean_object* v_as_2217_, size_t v_sz_2218_, size_t v_i_2219_, lean_object* v_bs_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_){
_start:
{
lean_object* v___x_2226_; 
v___x_2226_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___redArg(v_fixedParamPerms_2215_, v_xs_2216_, v_sz_2218_, v_i_2219_, v_bs_2220_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_);
return v___x_2226_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___boxed(lean_object* v_fixedParamPerms_2227_, lean_object* v_xs_2228_, lean_object* v_as_2229_, lean_object* v_sz_2230_, lean_object* v_i_2231_, lean_object* v_bs_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_){
_start:
{
size_t v_sz_boxed_2238_; size_t v_i_boxed_2239_; lean_object* v_res_2240_; 
v_sz_boxed_2238_ = lean_unbox_usize(v_sz_2230_);
lean_dec(v_sz_2230_);
v_i_boxed_2239_ = lean_unbox_usize(v_i_2231_);
lean_dec(v_i_2231_);
v_res_2240_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2(v_fixedParamPerms_2227_, v_xs_2228_, v_as_2229_, v_sz_boxed_2238_, v_i_boxed_2239_, v_bs_2232_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_);
lean_dec(v___y_2236_);
lean_dec_ref(v___y_2235_);
lean_dec(v___y_2234_);
lean_dec_ref(v___y_2233_);
lean_dec_ref(v_as_2229_);
lean_dec_ref(v_fixedParamPerms_2227_);
return v_res_2240_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3(lean_object* v_fixedParamPerms_2241_, lean_object* v_xs_2242_, lean_object* v_as_2243_, size_t v_sz_2244_, size_t v_i_2245_, lean_object* v_bs_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_){
_start:
{
lean_object* v___x_2252_; 
v___x_2252_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___redArg(v_fixedParamPerms_2241_, v_xs_2242_, v_sz_2244_, v_i_2245_, v_bs_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_);
return v___x_2252_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___boxed(lean_object* v_fixedParamPerms_2253_, lean_object* v_xs_2254_, lean_object* v_as_2255_, lean_object* v_sz_2256_, lean_object* v_i_2257_, lean_object* v_bs_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_){
_start:
{
size_t v_sz_boxed_2264_; size_t v_i_boxed_2265_; lean_object* v_res_2266_; 
v_sz_boxed_2264_ = lean_unbox_usize(v_sz_2256_);
lean_dec(v_sz_2256_);
v_i_boxed_2265_ = lean_unbox_usize(v_i_2257_);
lean_dec(v_i_2257_);
v_res_2266_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3(v_fixedParamPerms_2253_, v_xs_2254_, v_as_2255_, v_sz_boxed_2264_, v_i_boxed_2265_, v_bs_2258_, v___y_2259_, v___y_2260_, v___y_2261_, v___y_2262_);
lean_dec(v___y_2262_);
lean_dec_ref(v___y_2261_);
lean_dec(v___y_2260_);
lean_dec_ref(v___y_2259_);
lean_dec_ref(v_as_2255_);
lean_dec_ref(v_fixedParamPerms_2253_);
return v_res_2266_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14(lean_object* v_00_u03b3_2267_, lean_object* v_msg_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_){
_start:
{
lean_object* v___x_2274_; 
v___x_2274_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg(v_msg_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_);
return v___x_2274_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___boxed(lean_object* v_00_u03b3_2275_, lean_object* v_msg_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_){
_start:
{
lean_object* v_res_2282_; 
v_res_2282_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14(v_00_u03b3_2275_, v_msg_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_);
lean_dec(v___y_2280_);
lean_dec_ref(v___y_2279_);
lean_dec(v___y_2278_);
lean_dec_ref(v___y_2277_);
return v_res_2282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6(lean_object* v_00_u03b3_2283_, lean_object* v_00_u03b1_2284_, lean_object* v_f_2285_, lean_object* v_positions_2286_, lean_object* v_ys_2287_, lean_object* v_xs_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_){
_start:
{
lean_object* v___x_2294_; 
v___x_2294_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg(v_f_2285_, v_positions_2286_, v_ys_2287_, v_xs_2288_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_);
return v___x_2294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___boxed(lean_object* v_00_u03b3_2295_, lean_object* v_00_u03b1_2296_, lean_object* v_f_2297_, lean_object* v_positions_2298_, lean_object* v_ys_2299_, lean_object* v_xs_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_){
_start:
{
lean_object* v_res_2306_; 
v_res_2306_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6(v_00_u03b3_2295_, v_00_u03b1_2296_, v_f_2297_, v_positions_2298_, v_ys_2299_, v_xs_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_);
lean_dec(v___y_2304_);
lean_dec_ref(v___y_2303_);
lean_dec(v___y_2302_);
lean_dec_ref(v___y_2301_);
lean_dec_ref(v_xs_2300_);
lean_dec_ref(v_ys_2299_);
lean_dec_ref(v_positions_2298_);
return v_res_2306_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7(lean_object* v___x_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_, lean_object* v_funTypes_2310_, lean_object* v_as_2311_, size_t v_sz_2312_, size_t v_i_2313_, lean_object* v_bs_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_){
_start:
{
lean_object* v___x_2320_; 
v___x_2320_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg(v___x_2307_, v_a_2308_, v_a_2309_, v_funTypes_2310_, v_sz_2312_, v_i_2313_, v_bs_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_);
return v___x_2320_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___boxed(lean_object* v___x_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_, lean_object* v_funTypes_2324_, lean_object* v_as_2325_, lean_object* v_sz_2326_, lean_object* v_i_2327_, lean_object* v_bs_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_){
_start:
{
size_t v_sz_boxed_2334_; size_t v_i_boxed_2335_; lean_object* v_res_2336_; 
v_sz_boxed_2334_ = lean_unbox_usize(v_sz_2326_);
lean_dec(v_sz_2326_);
v_i_boxed_2335_ = lean_unbox_usize(v_i_2327_);
lean_dec(v_i_2327_);
v_res_2336_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7(v___x_2321_, v_a_2322_, v_a_2323_, v_funTypes_2324_, v_as_2325_, v_sz_boxed_2334_, v_i_boxed_2335_, v_bs_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_);
lean_dec(v___y_2332_);
lean_dec_ref(v___y_2331_);
lean_dec(v___y_2330_);
lean_dec_ref(v___y_2329_);
lean_dec_ref(v_as_2325_);
return v_res_2336_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8(lean_object* v_fixedParamPerms_2337_, lean_object* v_xs_2338_, lean_object* v_as_2339_, size_t v_sz_2340_, size_t v_i_2341_, lean_object* v_bs_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_){
_start:
{
lean_object* v___x_2348_; 
v___x_2348_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg(v_fixedParamPerms_2337_, v_xs_2338_, v_sz_2340_, v_i_2341_, v_bs_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_);
return v___x_2348_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___boxed(lean_object* v_fixedParamPerms_2349_, lean_object* v_xs_2350_, lean_object* v_as_2351_, lean_object* v_sz_2352_, lean_object* v_i_2353_, lean_object* v_bs_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_){
_start:
{
size_t v_sz_boxed_2360_; size_t v_i_boxed_2361_; lean_object* v_res_2362_; 
v_sz_boxed_2360_ = lean_unbox_usize(v_sz_2352_);
lean_dec(v_sz_2352_);
v_i_boxed_2361_ = lean_unbox_usize(v_i_2353_);
lean_dec(v_i_2353_);
v_res_2362_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8(v_fixedParamPerms_2349_, v_xs_2350_, v_as_2351_, v_sz_boxed_2360_, v_i_boxed_2361_, v_bs_2354_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_);
lean_dec(v___y_2358_);
lean_dec_ref(v___y_2357_);
lean_dec(v___y_2356_);
lean_dec_ref(v___y_2355_);
lean_dec_ref(v_as_2351_);
return v_res_2362_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12(lean_object* v_00_u03b1_2363_, lean_object* v_preDefs_2364_, lean_object* v_k_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_){
_start:
{
lean_object* v___x_2371_; 
v___x_2371_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v_preDefs_2364_, v_k_2365_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_);
return v___x_2371_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___boxed(lean_object* v_00_u03b1_2372_, lean_object* v_preDefs_2373_, lean_object* v_k_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_){
_start:
{
lean_object* v_res_2380_; 
v_res_2380_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12(v_00_u03b1_2372_, v_preDefs_2373_, v_k_2374_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_);
lean_dec(v___y_2378_);
lean_dec_ref(v___y_2377_);
lean_dec(v___y_2376_);
lean_dec_ref(v___y_2375_);
return v_res_2380_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14(uint8_t v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_, lean_object* v_recArgInfos_2384_, lean_object* v___x_2385_, lean_object* v_preDefs_2386_, lean_object* v_a_2387_, lean_object* v_as_2388_, size_t v_sz_2389_, size_t v_i_2390_, lean_object* v_bs_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_){
_start:
{
lean_object* v___x_2397_; 
v___x_2397_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg(v_a_2381_, v_a_2382_, v_a_2383_, v_recArgInfos_2384_, v___x_2385_, v_preDefs_2386_, v_a_2387_, v_sz_2389_, v_i_2390_, v_bs_2391_, v___y_2392_, v___y_2393_, v___y_2394_, v___y_2395_);
return v___x_2397_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___boxed(lean_object* v_a_2398_, lean_object* v_a_2399_, lean_object* v_a_2400_, lean_object* v_recArgInfos_2401_, lean_object* v___x_2402_, lean_object* v_preDefs_2403_, lean_object* v_a_2404_, lean_object* v_as_2405_, lean_object* v_sz_2406_, lean_object* v_i_2407_, lean_object* v_bs_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_){
_start:
{
uint8_t v_a_28098__boxed_2414_; size_t v_sz_boxed_2415_; size_t v_i_boxed_2416_; lean_object* v_res_2417_; 
v_a_28098__boxed_2414_ = lean_unbox(v_a_2398_);
v_sz_boxed_2415_ = lean_unbox_usize(v_sz_2406_);
lean_dec(v_sz_2406_);
v_i_boxed_2416_ = lean_unbox_usize(v_i_2407_);
lean_dec(v_i_2407_);
v_res_2417_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14(v_a_28098__boxed_2414_, v_a_2399_, v_a_2400_, v_recArgInfos_2401_, v___x_2402_, v_preDefs_2403_, v_a_2404_, v_as_2405_, v_sz_boxed_2415_, v_i_boxed_2416_, v_bs_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_);
lean_dec(v___y_2412_);
lean_dec_ref(v___y_2411_);
lean_dec(v___y_2410_);
lean_dec_ref(v___y_2409_);
lean_dec_ref(v_as_2405_);
lean_dec_ref(v_a_2400_);
lean_dec_ref(v_a_2399_);
return v_res_2417_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16_spec__29(lean_object* v_declName_2418_, uint8_t v_s_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_){
_start:
{
lean_object* v___x_2425_; 
v___x_2425_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16_spec__29___redArg(v_declName_2418_, v_s_2419_, v___y_2421_, v___y_2423_);
return v___x_2425_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16_spec__29___boxed(lean_object* v_declName_2426_, lean_object* v_s_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_){
_start:
{
uint8_t v_s_boxed_2433_; lean_object* v_res_2434_; 
v_s_boxed_2433_ = lean_unbox(v_s_2427_);
v_res_2434_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16_spec__29(v_declName_2426_, v_s_boxed_2433_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_);
lean_dec(v___y_2431_);
lean_dec_ref(v___y_2430_);
lean_dec(v___y_2429_);
lean_dec_ref(v___y_2428_);
return v_res_2434_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17(lean_object* v_xs_2435_, uint8_t v_a_2436_, lean_object* v_preDefs_2437_, lean_object* v___x_2438_, lean_object* v_as_2439_, size_t v_sz_2440_, size_t v_i_2441_, lean_object* v_bs_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_){
_start:
{
lean_object* v___x_2448_; 
v___x_2448_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg(v_xs_2435_, v_a_2436_, v_preDefs_2437_, v___x_2438_, v_sz_2440_, v_i_2441_, v_bs_2442_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_);
return v___x_2448_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___boxed(lean_object* v_xs_2449_, lean_object* v_a_2450_, lean_object* v_preDefs_2451_, lean_object* v___x_2452_, lean_object* v_as_2453_, lean_object* v_sz_2454_, lean_object* v_i_2455_, lean_object* v_bs_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_){
_start:
{
uint8_t v_a_28147__boxed_2462_; size_t v_sz_boxed_2463_; size_t v_i_boxed_2464_; lean_object* v_res_2465_; 
v_a_28147__boxed_2462_ = lean_unbox(v_a_2450_);
v_sz_boxed_2463_ = lean_unbox_usize(v_sz_2454_);
lean_dec(v_sz_2454_);
v_i_boxed_2464_ = lean_unbox_usize(v_i_2455_);
lean_dec(v_i_2455_);
v_res_2465_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17(v_xs_2449_, v_a_28147__boxed_2462_, v_preDefs_2451_, v___x_2452_, v_as_2453_, v_sz_boxed_2463_, v_i_boxed_2464_, v_bs_2456_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_);
lean_dec(v___y_2460_);
lean_dec_ref(v___y_2459_);
lean_dec(v___y_2458_);
lean_dec_ref(v___y_2457_);
lean_dec_ref(v_as_2453_);
lean_dec_ref(v_preDefs_2451_);
lean_dec_ref(v_xs_2449_);
return v_res_2465_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18(lean_object* v_a_2466_, lean_object* v_funTypes_2467_, lean_object* v_as_2468_, size_t v_sz_2469_, size_t v_i_2470_, lean_object* v_bs_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_){
_start:
{
lean_object* v___x_2477_; 
v___x_2477_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___redArg(v_a_2466_, v_funTypes_2467_, v_sz_2469_, v_i_2470_, v_bs_2471_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_);
return v___x_2477_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___boxed(lean_object* v_a_2478_, lean_object* v_funTypes_2479_, lean_object* v_as_2480_, lean_object* v_sz_2481_, lean_object* v_i_2482_, lean_object* v_bs_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_){
_start:
{
size_t v_sz_boxed_2489_; size_t v_i_boxed_2490_; lean_object* v_res_2491_; 
v_sz_boxed_2489_ = lean_unbox_usize(v_sz_2481_);
lean_dec(v_sz_2481_);
v_i_boxed_2490_ = lean_unbox_usize(v_i_2482_);
lean_dec(v_i_2482_);
v_res_2491_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18(v_a_2478_, v_funTypes_2479_, v_as_2480_, v_sz_boxed_2489_, v_i_boxed_2490_, v_bs_2483_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_);
lean_dec(v___y_2487_);
lean_dec_ref(v___y_2486_);
lean_dec(v___y_2485_);
lean_dec_ref(v___y_2484_);
lean_dec_ref(v_as_2480_);
lean_dec_ref(v_funTypes_2479_);
lean_dec_ref(v_a_2478_);
return v_res_2491_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19(lean_object* v_a_2492_, lean_object* v_a_2493_, lean_object* v_as_2494_, size_t v_sz_2495_, size_t v_i_2496_, lean_object* v_bs_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_){
_start:
{
lean_object* v___x_2503_; 
v___x_2503_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___redArg(v_a_2492_, v_a_2493_, v_sz_2495_, v_i_2496_, v_bs_2497_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_);
return v___x_2503_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___boxed(lean_object* v_a_2504_, lean_object* v_a_2505_, lean_object* v_as_2506_, lean_object* v_sz_2507_, lean_object* v_i_2508_, lean_object* v_bs_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_){
_start:
{
size_t v_sz_boxed_2515_; size_t v_i_boxed_2516_; lean_object* v_res_2517_; 
v_sz_boxed_2515_ = lean_unbox_usize(v_sz_2507_);
lean_dec(v_sz_2507_);
v_i_boxed_2516_ = lean_unbox_usize(v_i_2508_);
lean_dec(v_i_2508_);
v_res_2517_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19(v_a_2504_, v_a_2505_, v_as_2506_, v_sz_boxed_2515_, v_i_boxed_2516_, v_bs_2509_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_);
lean_dec(v___y_2513_);
lean_dec_ref(v___y_2512_);
lean_dec(v___y_2511_);
lean_dec_ref(v___y_2510_);
lean_dec_ref(v_as_2506_);
lean_dec_ref(v_a_2505_);
lean_dec_ref(v_a_2504_);
return v_res_2517_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4(lean_object* v_00_u03b1_2518_, lean_object* v_msg_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_){
_start:
{
lean_object* v___x_2525_; 
v___x_2525_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg(v_msg_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_);
return v___x_2525_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___boxed(lean_object* v_00_u03b1_2526_, lean_object* v_msg_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_){
_start:
{
lean_object* v_res_2533_; 
v_res_2533_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4(v_00_u03b1_2526_, v_msg_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_);
lean_dec(v___y_2531_);
lean_dec_ref(v___y_2530_);
lean_dec(v___y_2529_);
lean_dec_ref(v___y_2528_);
return v_res_2533_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9(lean_object* v_xs_2534_, lean_object* v_ys_2535_, lean_object* v_hsz_2536_, lean_object* v_x_2537_, lean_object* v_x_2538_){
_start:
{
uint8_t v___x_2539_; 
v___x_2539_ = l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9___redArg(v_xs_2534_, v_ys_2535_, v_x_2537_);
return v___x_2539_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9___boxed(lean_object* v_xs_2540_, lean_object* v_ys_2541_, lean_object* v_hsz_2542_, lean_object* v_x_2543_, lean_object* v_x_2544_){
_start:
{
uint8_t v_res_2545_; lean_object* v_r_2546_; 
v_res_2545_ = l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9(v_xs_2540_, v_ys_2541_, v_hsz_2542_, v_x_2543_, v_x_2544_);
lean_dec_ref(v_ys_2541_);
lean_dec_ref(v_xs_2540_);
v_r_2546_ = lean_box(v_res_2545_);
return v_r_2546_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10(lean_object* v_n_2547_, lean_object* v_as_2548_, lean_object* v_lo_2549_, lean_object* v_hi_2550_, lean_object* v_w_2551_, lean_object* v_hlo_2552_, lean_object* v_hhi_2553_){
_start:
{
lean_object* v___x_2554_; 
v___x_2554_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg(v_n_2547_, v_as_2548_, v_lo_2549_, v_hi_2550_);
return v___x_2554_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___boxed(lean_object* v_n_2555_, lean_object* v_as_2556_, lean_object* v_lo_2557_, lean_object* v_hi_2558_, lean_object* v_w_2559_, lean_object* v_hlo_2560_, lean_object* v_hhi_2561_){
_start:
{
lean_object* v_res_2562_; 
v_res_2562_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10(v_n_2555_, v_as_2556_, v_lo_2557_, v_hi_2558_, v_w_2559_, v_hlo_2560_, v_hhi_2561_);
lean_dec(v_hi_2558_);
lean_dec(v_n_2555_);
return v_res_2562_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15(lean_object* v_00_u03b1_2563_, lean_object* v_00_u03b3_2564_, lean_object* v_xs_2565_, lean_object* v_f_2566_, lean_object* v_as_2567_, lean_object* v_bs_2568_, lean_object* v_i_2569_, lean_object* v_cs_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_){
_start:
{
lean_object* v___x_2576_; 
v___x_2576_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15___redArg(v_xs_2565_, v_f_2566_, v_as_2567_, v_bs_2568_, v_i_2569_, v_cs_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_);
return v___x_2576_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15___boxed(lean_object* v_00_u03b1_2577_, lean_object* v_00_u03b3_2578_, lean_object* v_xs_2579_, lean_object* v_f_2580_, lean_object* v_as_2581_, lean_object* v_bs_2582_, lean_object* v_i_2583_, lean_object* v_cs_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_){
_start:
{
lean_object* v_res_2590_; 
v_res_2590_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15(v_00_u03b1_2577_, v_00_u03b3_2578_, v_xs_2579_, v_f_2580_, v_as_2581_, v_bs_2582_, v_i_2583_, v_cs_2584_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_);
lean_dec(v___y_2588_);
lean_dec_ref(v___y_2587_);
lean_dec(v___y_2586_);
lean_dec_ref(v___y_2585_);
lean_dec_ref(v_bs_2582_);
lean_dec_ref(v_as_2581_);
lean_dec_ref(v_xs_2579_);
return v_res_2590_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25(lean_object* v_env_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_){
_start:
{
lean_object* v___x_2597_; 
v___x_2597_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg(v_env_2591_, v___y_2593_, v___y_2595_);
return v___x_2597_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___boxed(lean_object* v_env_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_){
_start:
{
lean_object* v_res_2604_; 
v_res_2604_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25(v_env_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_);
lean_dec(v___y_2602_);
lean_dec_ref(v___y_2601_);
lean_dec(v___y_2600_);
lean_dec_ref(v___y_2599_);
return v_res_2604_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23(lean_object* v_00_u03b1_2605_, lean_object* v_env_2606_, lean_object* v_x_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_){
_start:
{
lean_object* v___x_2613_; 
v___x_2613_ = l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23___redArg(v_env_2606_, v_x_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_);
return v___x_2613_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23___boxed(lean_object* v_00_u03b1_2614_, lean_object* v_env_2615_, lean_object* v_x_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_){
_start:
{
lean_object* v_res_2622_; 
v_res_2622_ = l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23(v_00_u03b1_2614_, v_env_2615_, v_x_2616_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_);
lean_dec(v___y_2620_);
lean_dec_ref(v___y_2619_);
lean_dec(v___y_2618_);
lean_dec_ref(v___y_2617_);
return v_res_2622_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11(lean_object* v_n_2623_, lean_object* v_lo_2624_, lean_object* v_hi_2625_, lean_object* v_hhi_2626_, lean_object* v_pivot_2627_, lean_object* v_as_2628_, lean_object* v_i_2629_, lean_object* v_k_2630_, lean_object* v_ilo_2631_, lean_object* v_ik_2632_, lean_object* v_w_2633_){
_start:
{
lean_object* v___x_2634_; 
v___x_2634_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11___redArg(v_hi_2625_, v_pivot_2627_, v_as_2628_, v_i_2629_, v_k_2630_);
return v___x_2634_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11___boxed(lean_object* v_n_2635_, lean_object* v_lo_2636_, lean_object* v_hi_2637_, lean_object* v_hhi_2638_, lean_object* v_pivot_2639_, lean_object* v_as_2640_, lean_object* v_i_2641_, lean_object* v_k_2642_, lean_object* v_ilo_2643_, lean_object* v_ik_2644_, lean_object* v_w_2645_){
_start:
{
lean_object* v_res_2646_; 
v_res_2646_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11(v_n_2635_, v_lo_2636_, v_hi_2637_, v_hhi_2638_, v_pivot_2639_, v_as_2640_, v_i_2641_, v_k_2642_, v_ilo_2643_, v_ik_2644_, v_w_2645_);
lean_dec(v_pivot_2639_);
lean_dec(v_hi_2637_);
lean_dec(v_lo_2636_);
lean_dec(v_n_2635_);
return v_res_2646_;
}
}
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___lam__0(lean_object* v_x_2647_){
_start:
{
uint8_t v___x_2648_; 
v___x_2648_ = 0;
return v___x_2648_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___lam__0___boxed(lean_object* v_x_2649_){
_start:
{
uint8_t v_res_2650_; lean_object* v_r_2651_; 
v_res_2650_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___lam__0(v_x_2649_);
lean_dec(v_x_2649_);
v_r_2651_ = lean_box(v_res_2650_);
return v_r_2651_;
}
}
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___lam__1(lean_object* v_fvarId_2652_, lean_object* v_x_2653_){
_start:
{
uint8_t v___x_2654_; 
v___x_2654_ = l_Lean_instBEqFVarId_beq(v_fvarId_2652_, v_x_2653_);
return v___x_2654_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___lam__1___boxed(lean_object* v_fvarId_2655_, lean_object* v_x_2656_){
_start:
{
uint8_t v_res_2657_; lean_object* v_r_2658_; 
v_res_2657_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___lam__1(v_fvarId_2655_, v_x_2656_);
lean_dec(v_x_2656_);
lean_dec(v_fvarId_2655_);
v_r_2658_ = lean_box(v_res_2657_);
return v_r_2658_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; 
v___x_2660_ = lean_box(0);
v___x_2661_ = lean_unsigned_to_nat(16u);
v___x_2662_ = lean_mk_array(v___x_2661_, v___x_2660_);
return v___x_2662_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; 
v___x_2663_ = lean_obj_once(&l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__1, &l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__1_once, _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__1);
v___x_2664_ = lean_unsigned_to_nat(0u);
v___x_2665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2665_, 0, v___x_2664_);
lean_ctor_set(v___x_2665_, 1, v___x_2663_);
return v___x_2665_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg(lean_object* v_e_2666_, lean_object* v_fvarId_2667_, lean_object* v___y_2668_){
_start:
{
lean_object* v___x_2670_; uint8_t v_fst_2672_; lean_object* v_mctx_2673_; lean_object* v___y_2691_; lean_object* v_mctx_2696_; lean_object* v___f_2697_; lean_object* v___f_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; uint8_t v___x_2701_; 
v___x_2670_ = lean_st_ref_get(v___y_2668_);
v_mctx_2696_ = lean_ctor_get(v___x_2670_, 0);
lean_inc_ref_n(v_mctx_2696_, 2);
lean_dec(v___x_2670_);
v___f_2697_ = ((lean_object*)(l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__0));
v___f_2698_ = lean_alloc_closure((void*)(l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_2698_, 0, v_fvarId_2667_);
v___x_2699_ = lean_obj_once(&l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__2, &l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__2_once, _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__2);
v___x_2700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2700_, 0, v___x_2699_);
lean_ctor_set(v___x_2700_, 1, v_mctx_2696_);
v___x_2701_ = l_Lean_Expr_hasFVar(v_e_2666_);
if (v___x_2701_ == 0)
{
uint8_t v___x_2702_; 
v___x_2702_ = l_Lean_Expr_hasMVar(v_e_2666_);
if (v___x_2702_ == 0)
{
lean_dec_ref_known(v___x_2700_, 2);
lean_dec_ref(v___f_2698_);
lean_dec_ref(v_e_2666_);
v_fst_2672_ = v___x_2702_;
v_mctx_2673_ = v_mctx_2696_;
goto v___jp_2671_;
}
else
{
lean_object* v___x_2703_; 
lean_dec_ref(v_mctx_2696_);
v___x_2703_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2698_, v___f_2697_, v_e_2666_, v___x_2700_);
v___y_2691_ = v___x_2703_;
goto v___jp_2690_;
}
}
else
{
lean_object* v___x_2704_; 
lean_dec_ref(v_mctx_2696_);
v___x_2704_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2698_, v___f_2697_, v_e_2666_, v___x_2700_);
v___y_2691_ = v___x_2704_;
goto v___jp_2690_;
}
v___jp_2671_:
{
lean_object* v___x_2674_; lean_object* v_cache_2675_; lean_object* v_zetaDeltaFVarIds_2676_; lean_object* v_postponed_2677_; lean_object* v_diag_2678_; lean_object* v___x_2680_; uint8_t v_isShared_2681_; uint8_t v_isSharedCheck_2688_; 
v___x_2674_ = lean_st_ref_take(v___y_2668_);
v_cache_2675_ = lean_ctor_get(v___x_2674_, 1);
v_zetaDeltaFVarIds_2676_ = lean_ctor_get(v___x_2674_, 2);
v_postponed_2677_ = lean_ctor_get(v___x_2674_, 3);
v_diag_2678_ = lean_ctor_get(v___x_2674_, 4);
v_isSharedCheck_2688_ = !lean_is_exclusive(v___x_2674_);
if (v_isSharedCheck_2688_ == 0)
{
lean_object* v_unused_2689_; 
v_unused_2689_ = lean_ctor_get(v___x_2674_, 0);
lean_dec(v_unused_2689_);
v___x_2680_ = v___x_2674_;
v_isShared_2681_ = v_isSharedCheck_2688_;
goto v_resetjp_2679_;
}
else
{
lean_inc(v_diag_2678_);
lean_inc(v_postponed_2677_);
lean_inc(v_zetaDeltaFVarIds_2676_);
lean_inc(v_cache_2675_);
lean_dec(v___x_2674_);
v___x_2680_ = lean_box(0);
v_isShared_2681_ = v_isSharedCheck_2688_;
goto v_resetjp_2679_;
}
v_resetjp_2679_:
{
lean_object* v___x_2683_; 
if (v_isShared_2681_ == 0)
{
lean_ctor_set(v___x_2680_, 0, v_mctx_2673_);
v___x_2683_ = v___x_2680_;
goto v_reusejp_2682_;
}
else
{
lean_object* v_reuseFailAlloc_2687_; 
v_reuseFailAlloc_2687_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2687_, 0, v_mctx_2673_);
lean_ctor_set(v_reuseFailAlloc_2687_, 1, v_cache_2675_);
lean_ctor_set(v_reuseFailAlloc_2687_, 2, v_zetaDeltaFVarIds_2676_);
lean_ctor_set(v_reuseFailAlloc_2687_, 3, v_postponed_2677_);
lean_ctor_set(v_reuseFailAlloc_2687_, 4, v_diag_2678_);
v___x_2683_ = v_reuseFailAlloc_2687_;
goto v_reusejp_2682_;
}
v_reusejp_2682_:
{
lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; 
v___x_2684_ = lean_st_ref_put(v___y_2668_, v___x_2683_);
v___x_2685_ = lean_box(v_fst_2672_);
v___x_2686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2686_, 0, v___x_2685_);
return v___x_2686_;
}
}
}
v___jp_2690_:
{
lean_object* v_snd_2692_; lean_object* v_fst_2693_; lean_object* v_mctx_2694_; uint8_t v___x_2695_; 
v_snd_2692_ = lean_ctor_get(v___y_2691_, 1);
lean_inc(v_snd_2692_);
v_fst_2693_ = lean_ctor_get(v___y_2691_, 0);
lean_inc(v_fst_2693_);
lean_dec_ref(v___y_2691_);
v_mctx_2694_ = lean_ctor_get(v_snd_2692_, 1);
lean_inc_ref(v_mctx_2694_);
lean_dec(v_snd_2692_);
v___x_2695_ = lean_unbox(v_fst_2693_);
lean_dec(v_fst_2693_);
v_fst_2672_ = v___x_2695_;
v_mctx_2673_ = v_mctx_2694_;
goto v___jp_2671_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___boxed(lean_object* v_e_2705_, lean_object* v_fvarId_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_){
_start:
{
lean_object* v_res_2709_; 
v_res_2709_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg(v_e_2705_, v_fvarId_2706_, v___y_2707_);
lean_dec(v___y_2707_);
return v_res_2709_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5(lean_object* v_e_2710_, lean_object* v_fvarId_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_){
_start:
{
lean_object* v___x_2717_; 
v___x_2717_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg(v_e_2710_, v_fvarId_2711_, v___y_2713_);
return v___x_2717_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___boxed(lean_object* v_e_2718_, lean_object* v_fvarId_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_){
_start:
{
lean_object* v_res_2725_; 
v_res_2725_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5(v_e_2718_, v_fvarId_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_);
lean_dec(v___y_2723_);
lean_dec_ref(v___y_2722_);
lean_dec(v___y_2721_);
lean_dec_ref(v___y_2720_);
return v_res_2725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg___lam__0(lean_object* v_k_2726_, lean_object* v_b_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_){
_start:
{
lean_object* v___x_2733_; 
lean_inc(v___y_2731_);
lean_inc_ref(v___y_2730_);
lean_inc(v___y_2729_);
lean_inc_ref(v___y_2728_);
v___x_2733_ = lean_apply_6(v_k_2726_, v_b_2727_, v___y_2728_, v___y_2729_, v___y_2730_, v___y_2731_, lean_box(0));
return v___x_2733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg___lam__0___boxed(lean_object* v_k_2734_, lean_object* v_b_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_){
_start:
{
lean_object* v_res_2741_; 
v_res_2741_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg___lam__0(v_k_2734_, v_b_2735_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_);
lean_dec(v___y_2739_);
lean_dec_ref(v___y_2738_);
lean_dec(v___y_2737_);
lean_dec_ref(v___y_2736_);
return v_res_2741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg(lean_object* v_perm_2742_, lean_object* v_type_2743_, lean_object* v_k_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_){
_start:
{
lean_object* v___f_2750_; lean_object* v___x_2751_; 
v___f_2750_ = lean_alloc_closure((void*)(l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2750_, 0, v_k_2744_);
v___x_2751_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl(lean_box(0), v_perm_2742_, v_type_2743_, v___f_2750_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_);
if (lean_obj_tag(v___x_2751_) == 0)
{
lean_object* v_a_2752_; lean_object* v___x_2754_; uint8_t v_isShared_2755_; uint8_t v_isSharedCheck_2759_; 
v_a_2752_ = lean_ctor_get(v___x_2751_, 0);
v_isSharedCheck_2759_ = !lean_is_exclusive(v___x_2751_);
if (v_isSharedCheck_2759_ == 0)
{
v___x_2754_ = v___x_2751_;
v_isShared_2755_ = v_isSharedCheck_2759_;
goto v_resetjp_2753_;
}
else
{
lean_inc(v_a_2752_);
lean_dec(v___x_2751_);
v___x_2754_ = lean_box(0);
v_isShared_2755_ = v_isSharedCheck_2759_;
goto v_resetjp_2753_;
}
v_resetjp_2753_:
{
lean_object* v___x_2757_; 
if (v_isShared_2755_ == 0)
{
v___x_2757_ = v___x_2754_;
goto v_reusejp_2756_;
}
else
{
lean_object* v_reuseFailAlloc_2758_; 
v_reuseFailAlloc_2758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2758_, 0, v_a_2752_);
v___x_2757_ = v_reuseFailAlloc_2758_;
goto v_reusejp_2756_;
}
v_reusejp_2756_:
{
return v___x_2757_;
}
}
}
else
{
lean_object* v_a_2760_; lean_object* v___x_2762_; uint8_t v_isShared_2763_; uint8_t v_isSharedCheck_2767_; 
v_a_2760_ = lean_ctor_get(v___x_2751_, 0);
v_isSharedCheck_2767_ = !lean_is_exclusive(v___x_2751_);
if (v_isSharedCheck_2767_ == 0)
{
v___x_2762_ = v___x_2751_;
v_isShared_2763_ = v_isSharedCheck_2767_;
goto v_resetjp_2761_;
}
else
{
lean_inc(v_a_2760_);
lean_dec(v___x_2751_);
v___x_2762_ = lean_box(0);
v_isShared_2763_ = v_isSharedCheck_2767_;
goto v_resetjp_2761_;
}
v_resetjp_2761_:
{
lean_object* v___x_2765_; 
if (v_isShared_2763_ == 0)
{
v___x_2765_ = v___x_2762_;
goto v_reusejp_2764_;
}
else
{
lean_object* v_reuseFailAlloc_2766_; 
v_reuseFailAlloc_2766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2766_, 0, v_a_2760_);
v___x_2765_ = v_reuseFailAlloc_2766_;
goto v_reusejp_2764_;
}
v_reusejp_2764_:
{
return v___x_2765_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg___boxed(lean_object* v_perm_2768_, lean_object* v_type_2769_, lean_object* v_k_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_){
_start:
{
lean_object* v_res_2776_; 
v_res_2776_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg(v_perm_2768_, v_type_2769_, v_k_2770_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_);
lean_dec(v___y_2774_);
lean_dec_ref(v___y_2773_);
lean_dec(v___y_2772_);
lean_dec_ref(v___y_2771_);
return v_res_2776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13(lean_object* v_00_u03b1_2777_, lean_object* v_perm_2778_, lean_object* v_type_2779_, lean_object* v_k_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_){
_start:
{
lean_object* v___x_2786_; 
v___x_2786_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg(v_perm_2778_, v_type_2779_, v_k_2780_, v___y_2781_, v___y_2782_, v___y_2783_, v___y_2784_);
return v___x_2786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___boxed(lean_object* v_00_u03b1_2787_, lean_object* v_perm_2788_, lean_object* v_type_2789_, lean_object* v_k_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_){
_start:
{
lean_object* v_res_2796_; 
v_res_2796_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13(v_00_u03b1_2787_, v_perm_2788_, v_type_2789_, v_k_2790_, v___y_2791_, v___y_2792_, v___y_2793_, v___y_2794_);
lean_dec(v___y_2794_);
lean_dec_ref(v___y_2793_);
lean_dec(v___y_2792_);
lean_dec_ref(v___y_2791_);
return v_res_2796_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1(lean_object* v_a_2797_, lean_object* v_fst_2798_, lean_object* v_fst_2799_, lean_object* v___x_2800_, lean_object* v___x_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_){
_start:
{
lean_object* v___x_2807_; 
lean_inc_ref(v_fst_2798_);
v___x_2807_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion(v_a_2797_, v_fst_2798_, v_fst_2799_, v___x_2800_, v___y_2802_, v___y_2803_, v___y_2804_, v___y_2805_);
if (lean_obj_tag(v___x_2807_) == 0)
{
lean_object* v_a_2808_; lean_object* v___x_2810_; uint8_t v_isShared_2811_; uint8_t v_isSharedCheck_2817_; 
v_a_2808_ = lean_ctor_get(v___x_2807_, 0);
v_isSharedCheck_2817_ = !lean_is_exclusive(v___x_2807_);
if (v_isSharedCheck_2817_ == 0)
{
v___x_2810_ = v___x_2807_;
v_isShared_2811_ = v_isSharedCheck_2817_;
goto v_resetjp_2809_;
}
else
{
lean_inc(v_a_2808_);
lean_dec(v___x_2807_);
v___x_2810_ = lean_box(0);
v_isShared_2811_ = v_isSharedCheck_2817_;
goto v_resetjp_2809_;
}
v_resetjp_2809_:
{
lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2815_; 
v___x_2812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2812_, 0, v_a_2808_);
lean_ctor_set(v___x_2812_, 1, v_fst_2798_);
v___x_2813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2813_, 0, v___x_2801_);
lean_ctor_set(v___x_2813_, 1, v___x_2812_);
if (v_isShared_2811_ == 0)
{
lean_ctor_set(v___x_2810_, 0, v___x_2813_);
v___x_2815_ = v___x_2810_;
goto v_reusejp_2814_;
}
else
{
lean_object* v_reuseFailAlloc_2816_; 
v_reuseFailAlloc_2816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2816_, 0, v___x_2813_);
v___x_2815_ = v_reuseFailAlloc_2816_;
goto v_reusejp_2814_;
}
v_reusejp_2814_:
{
return v___x_2815_;
}
}
}
else
{
lean_object* v_a_2818_; lean_object* v___x_2820_; uint8_t v_isShared_2821_; uint8_t v_isSharedCheck_2825_; 
lean_dec_ref(v___x_2801_);
lean_dec_ref(v_fst_2798_);
v_a_2818_ = lean_ctor_get(v___x_2807_, 0);
v_isSharedCheck_2825_ = !lean_is_exclusive(v___x_2807_);
if (v_isSharedCheck_2825_ == 0)
{
v___x_2820_ = v___x_2807_;
v_isShared_2821_ = v_isSharedCheck_2825_;
goto v_resetjp_2819_;
}
else
{
lean_inc(v_a_2818_);
lean_dec(v___x_2807_);
v___x_2820_ = lean_box(0);
v_isShared_2821_ = v_isSharedCheck_2825_;
goto v_resetjp_2819_;
}
v_resetjp_2819_:
{
lean_object* v___x_2823_; 
if (v_isShared_2821_ == 0)
{
v___x_2823_ = v___x_2820_;
goto v_reusejp_2822_;
}
else
{
lean_object* v_reuseFailAlloc_2824_; 
v_reuseFailAlloc_2824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2824_, 0, v_a_2818_);
v___x_2823_ = v_reuseFailAlloc_2824_;
goto v_reusejp_2822_;
}
v_reusejp_2822_:
{
return v___x_2823_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___boxed(lean_object* v_a_2826_, lean_object* v_fst_2827_, lean_object* v_fst_2828_, lean_object* v___x_2829_, lean_object* v___x_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_){
_start:
{
lean_object* v_res_2836_; 
v_res_2836_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1(v_a_2826_, v_fst_2827_, v_fst_2828_, v___x_2829_, v___x_2830_, v___y_2831_, v___y_2832_, v___y_2833_, v___y_2834_);
lean_dec(v___y_2834_);
lean_dec_ref(v___y_2833_);
lean_dec(v___y_2832_);
lean_dec_ref(v___y_2831_);
return v_res_2836_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__3(size_t v_sz_2837_, size_t v_i_2838_, lean_object* v_bs_2839_){
_start:
{
uint8_t v___x_2840_; 
v___x_2840_ = lean_usize_dec_lt(v_i_2838_, v_sz_2837_);
if (v___x_2840_ == 0)
{
return v_bs_2839_;
}
else
{
lean_object* v_v_2841_; lean_object* v___x_2842_; lean_object* v_bs_x27_2843_; lean_object* v___x_2844_; size_t v___x_2845_; size_t v___x_2846_; lean_object* v___x_2847_; 
v_v_2841_ = lean_array_uget(v_bs_2839_, v_i_2838_);
v___x_2842_ = lean_unsigned_to_nat(0u);
v_bs_x27_2843_ = lean_array_uset(v_bs_2839_, v_i_2838_, v___x_2842_);
v___x_2844_ = l_Lean_Elab_Structural_RecArgInfo_indicesAndRecArgPos(v_v_2841_);
v___x_2845_ = ((size_t)1ULL);
v___x_2846_ = lean_usize_add(v_i_2838_, v___x_2845_);
v___x_2847_ = lean_array_uset(v_bs_x27_2843_, v_i_2838_, v___x_2844_);
v_i_2838_ = v___x_2846_;
v_bs_2839_ = v___x_2847_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__3___boxed(lean_object* v_sz_2849_, lean_object* v_i_2850_, lean_object* v_bs_2851_){
_start:
{
size_t v_sz_boxed_2852_; size_t v_i_boxed_2853_; lean_object* v_res_2854_; 
v_sz_boxed_2852_ = lean_unbox_usize(v_sz_2849_);
lean_dec(v_sz_2849_);
v_i_boxed_2853_ = lean_unbox_usize(v_i_2850_);
lean_dec(v_i_2850_);
v_res_2854_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__3(v_sz_boxed_2852_, v_i_boxed_2853_, v_bs_2851_);
return v_res_2854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___redArg(lean_object* v_lctx_2855_, lean_object* v_localInsts_2856_, lean_object* v_x_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_){
_start:
{
lean_object* v___x_2863_; 
v___x_2863_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_2855_, v_localInsts_2856_, v_x_2857_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_);
if (lean_obj_tag(v___x_2863_) == 0)
{
lean_object* v_a_2864_; lean_object* v___x_2866_; uint8_t v_isShared_2867_; uint8_t v_isSharedCheck_2871_; 
v_a_2864_ = lean_ctor_get(v___x_2863_, 0);
v_isSharedCheck_2871_ = !lean_is_exclusive(v___x_2863_);
if (v_isSharedCheck_2871_ == 0)
{
v___x_2866_ = v___x_2863_;
v_isShared_2867_ = v_isSharedCheck_2871_;
goto v_resetjp_2865_;
}
else
{
lean_inc(v_a_2864_);
lean_dec(v___x_2863_);
v___x_2866_ = lean_box(0);
v_isShared_2867_ = v_isSharedCheck_2871_;
goto v_resetjp_2865_;
}
v_resetjp_2865_:
{
lean_object* v___x_2869_; 
if (v_isShared_2867_ == 0)
{
v___x_2869_ = v___x_2866_;
goto v_reusejp_2868_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v_a_2864_);
v___x_2869_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2868_;
}
v_reusejp_2868_:
{
return v___x_2869_;
}
}
}
else
{
lean_object* v_a_2872_; lean_object* v___x_2874_; uint8_t v_isShared_2875_; uint8_t v_isSharedCheck_2879_; 
v_a_2872_ = lean_ctor_get(v___x_2863_, 0);
v_isSharedCheck_2879_ = !lean_is_exclusive(v___x_2863_);
if (v_isSharedCheck_2879_ == 0)
{
v___x_2874_ = v___x_2863_;
v_isShared_2875_ = v_isSharedCheck_2879_;
goto v_resetjp_2873_;
}
else
{
lean_inc(v_a_2872_);
lean_dec(v___x_2863_);
v___x_2874_ = lean_box(0);
v_isShared_2875_ = v_isSharedCheck_2879_;
goto v_resetjp_2873_;
}
v_resetjp_2873_:
{
lean_object* v___x_2877_; 
if (v_isShared_2875_ == 0)
{
v___x_2877_ = v___x_2874_;
goto v_reusejp_2876_;
}
else
{
lean_object* v_reuseFailAlloc_2878_; 
v_reuseFailAlloc_2878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2878_, 0, v_a_2872_);
v___x_2877_ = v_reuseFailAlloc_2878_;
goto v_reusejp_2876_;
}
v_reusejp_2876_:
{
return v___x_2877_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___redArg___boxed(lean_object* v_lctx_2880_, lean_object* v_localInsts_2881_, lean_object* v_x_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_){
_start:
{
lean_object* v_res_2888_; 
v_res_2888_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___redArg(v_lctx_2880_, v_localInsts_2881_, v_x_2882_, v___y_2883_, v___y_2884_, v___y_2885_, v___y_2886_);
lean_dec(v___y_2886_);
lean_dec_ref(v___y_2885_);
lean_dec(v___y_2884_);
lean_dec_ref(v___y_2883_);
return v_res_2888_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__12(lean_object* v_as_2889_, size_t v_i_2890_, size_t v_stop_2891_, lean_object* v_b_2892_){
_start:
{
uint8_t v___x_2893_; 
v___x_2893_ = lean_usize_dec_eq(v_i_2890_, v_stop_2891_);
if (v___x_2893_ == 0)
{
lean_object* v___x_2894_; lean_object* v___x_2895_; size_t v___x_2896_; size_t v___x_2897_; 
v___x_2894_ = lean_array_uget_borrowed(v_as_2889_, v_i_2890_);
lean_inc(v___x_2894_);
v___x_2895_ = lean_local_ctx_erase(v_b_2892_, v___x_2894_);
v___x_2896_ = ((size_t)1ULL);
v___x_2897_ = lean_usize_add(v_i_2890_, v___x_2896_);
v_i_2890_ = v___x_2897_;
v_b_2892_ = v___x_2895_;
goto _start;
}
else
{
return v_b_2892_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__12___boxed(lean_object* v_as_2899_, lean_object* v_i_2900_, lean_object* v_stop_2901_, lean_object* v_b_2902_){
_start:
{
size_t v_i_boxed_2903_; size_t v_stop_boxed_2904_; lean_object* v_res_2905_; 
v_i_boxed_2903_ = lean_unbox_usize(v_i_2900_);
lean_dec(v_i_2900_);
v_stop_boxed_2904_ = lean_unbox_usize(v_stop_2901_);
lean_dec(v_stop_2901_);
v_res_2905_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__12(v_as_2899_, v_i_boxed_2903_, v_stop_boxed_2904_, v_b_2902_);
lean_dec_ref(v_as_2899_);
return v_res_2905_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9_spec__11(lean_object* v_a_2906_, lean_object* v_as_2907_, size_t v_i_2908_, size_t v_stop_2909_){
_start:
{
uint8_t v___x_2910_; 
v___x_2910_ = lean_usize_dec_eq(v_i_2908_, v_stop_2909_);
if (v___x_2910_ == 0)
{
lean_object* v___x_2911_; uint8_t v___x_2912_; 
v___x_2911_ = lean_array_uget_borrowed(v_as_2907_, v_i_2908_);
v___x_2912_ = l_Lean_instBEqFVarId_beq(v_a_2906_, v___x_2911_);
if (v___x_2912_ == 0)
{
size_t v___x_2913_; size_t v___x_2914_; 
v___x_2913_ = ((size_t)1ULL);
v___x_2914_ = lean_usize_add(v_i_2908_, v___x_2913_);
v_i_2908_ = v___x_2914_;
goto _start;
}
else
{
return v___x_2912_;
}
}
else
{
uint8_t v___x_2916_; 
v___x_2916_ = 0;
return v___x_2916_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9_spec__11___boxed(lean_object* v_a_2917_, lean_object* v_as_2918_, lean_object* v_i_2919_, lean_object* v_stop_2920_){
_start:
{
size_t v_i_boxed_2921_; size_t v_stop_boxed_2922_; uint8_t v_res_2923_; lean_object* v_r_2924_; 
v_i_boxed_2921_ = lean_unbox_usize(v_i_2919_);
lean_dec(v_i_2919_);
v_stop_boxed_2922_ = lean_unbox_usize(v_stop_2920_);
lean_dec(v_stop_2920_);
v_res_2923_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9_spec__11(v_a_2917_, v_as_2918_, v_i_boxed_2921_, v_stop_boxed_2922_);
lean_dec_ref(v_as_2918_);
lean_dec(v_a_2917_);
v_r_2924_ = lean_box(v_res_2923_);
return v_r_2924_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9(lean_object* v_as_2925_, lean_object* v_a_2926_){
_start:
{
lean_object* v___x_2927_; lean_object* v___x_2928_; uint8_t v___x_2929_; 
v___x_2927_ = lean_unsigned_to_nat(0u);
v___x_2928_ = lean_array_get_size(v_as_2925_);
v___x_2929_ = lean_nat_dec_lt(v___x_2927_, v___x_2928_);
if (v___x_2929_ == 0)
{
return v___x_2929_;
}
else
{
if (v___x_2929_ == 0)
{
return v___x_2929_;
}
else
{
size_t v___x_2930_; size_t v___x_2931_; uint8_t v___x_2932_; 
v___x_2930_ = ((size_t)0ULL);
v___x_2931_ = lean_usize_of_nat(v___x_2928_);
v___x_2932_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9_spec__11(v_a_2926_, v_as_2925_, v___x_2930_, v___x_2931_);
return v___x_2932_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9___boxed(lean_object* v_as_2933_, lean_object* v_a_2934_){
_start:
{
uint8_t v_res_2935_; lean_object* v_r_2936_; 
v_res_2935_ = l_Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9(v_as_2933_, v_a_2934_);
lean_dec(v_a_2934_);
lean_dec_ref(v_as_2933_);
v_r_2936_ = lean_box(v_res_2935_);
return v_r_2936_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__11(lean_object* v_fvarIds_2937_, lean_object* v_as_2938_, size_t v_i_2939_, size_t v_stop_2940_, lean_object* v_b_2941_){
_start:
{
lean_object* v___y_2943_; uint8_t v___x_2947_; 
v___x_2947_ = lean_usize_dec_eq(v_i_2939_, v_stop_2940_);
if (v___x_2947_ == 0)
{
lean_object* v___x_2948_; lean_object* v_fvar_2949_; lean_object* v___x_2950_; uint8_t v___x_2951_; 
v___x_2948_ = lean_array_uget_borrowed(v_as_2938_, v_i_2939_);
v_fvar_2949_ = lean_ctor_get(v___x_2948_, 1);
v___x_2950_ = l_Lean_Expr_fvarId_x21(v_fvar_2949_);
v___x_2951_ = l_Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9(v_fvarIds_2937_, v___x_2950_);
lean_dec(v___x_2950_);
if (v___x_2951_ == 0)
{
lean_object* v___x_2952_; 
lean_inc(v___x_2948_);
v___x_2952_ = lean_array_push(v_b_2941_, v___x_2948_);
v___y_2943_ = v___x_2952_;
goto v___jp_2942_;
}
else
{
v___y_2943_ = v_b_2941_;
goto v___jp_2942_;
}
}
else
{
return v_b_2941_;
}
v___jp_2942_:
{
size_t v___x_2944_; size_t v___x_2945_; 
v___x_2944_ = ((size_t)1ULL);
v___x_2945_ = lean_usize_add(v_i_2939_, v___x_2944_);
v_i_2939_ = v___x_2945_;
v_b_2941_ = v___y_2943_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__11___boxed(lean_object* v_fvarIds_2953_, lean_object* v_as_2954_, lean_object* v_i_2955_, lean_object* v_stop_2956_, lean_object* v_b_2957_){
_start:
{
size_t v_i_boxed_2958_; size_t v_stop_boxed_2959_; lean_object* v_res_2960_; 
v_i_boxed_2958_ = lean_unbox_usize(v_i_2955_);
lean_dec(v_i_2955_);
v_stop_boxed_2959_ = lean_unbox_usize(v_stop_2956_);
lean_dec(v_stop_2956_);
v_res_2960_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__11(v_fvarIds_2953_, v_as_2954_, v_i_boxed_2958_, v_stop_boxed_2959_, v_b_2957_);
lean_dec_ref(v_as_2954_);
lean_dec_ref(v_fvarIds_2953_);
return v_res_2960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___redArg(lean_object* v_fvarIds_2963_, lean_object* v_k_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_){
_start:
{
lean_object* v_lctx_2970_; lean_object* v_localInstances_2971_; lean_object* v___x_2972_; lean_object* v___y_2974_; lean_object* v___x_2983_; uint8_t v___x_2984_; 
v_lctx_2970_ = lean_ctor_get(v___y_2965_, 2);
v_localInstances_2971_ = lean_ctor_get(v___y_2965_, 3);
v___x_2972_ = lean_unsigned_to_nat(0u);
v___x_2983_ = lean_array_get_size(v_fvarIds_2963_);
v___x_2984_ = lean_nat_dec_lt(v___x_2972_, v___x_2983_);
if (v___x_2984_ == 0)
{
lean_inc_ref(v_lctx_2970_);
v___y_2974_ = v_lctx_2970_;
goto v___jp_2973_;
}
else
{
size_t v___x_2985_; size_t v___x_2986_; lean_object* v___x_2987_; 
v___x_2985_ = ((size_t)0ULL);
v___x_2986_ = lean_usize_of_nat(v___x_2983_);
lean_inc_ref(v_lctx_2970_);
v___x_2987_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__12(v_fvarIds_2963_, v___x_2985_, v___x_2986_, v_lctx_2970_);
v___y_2974_ = v___x_2987_;
goto v___jp_2973_;
}
v___jp_2973_:
{
lean_object* v___x_2975_; lean_object* v___x_2976_; uint8_t v___x_2977_; 
v___x_2975_ = lean_array_get_size(v_localInstances_2971_);
v___x_2976_ = ((lean_object*)(l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___redArg___closed__0));
v___x_2977_ = lean_nat_dec_lt(v___x_2972_, v___x_2975_);
if (v___x_2977_ == 0)
{
lean_object* v___x_2978_; 
v___x_2978_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___redArg(v___y_2974_, v___x_2976_, v_k_2964_, v___y_2965_, v___y_2966_, v___y_2967_, v___y_2968_);
return v___x_2978_;
}
else
{
size_t v___x_2979_; size_t v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; 
v___x_2979_ = ((size_t)0ULL);
v___x_2980_ = lean_usize_of_nat(v___x_2975_);
v___x_2981_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__11(v_fvarIds_2963_, v_localInstances_2971_, v___x_2979_, v___x_2980_, v___x_2976_);
v___x_2982_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___redArg(v___y_2974_, v___x_2981_, v_k_2964_, v___y_2965_, v___y_2966_, v___y_2967_, v___y_2968_);
return v___x_2982_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___redArg___boxed(lean_object* v_fvarIds_2988_, lean_object* v_k_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_){
_start:
{
lean_object* v_res_2995_; 
v_res_2995_ = l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___redArg(v_fvarIds_2988_, v_k_2989_, v___y_2990_, v___y_2991_, v___y_2992_, v___y_2993_);
lean_dec(v___y_2993_);
lean_dec_ref(v___y_2992_);
lean_dec(v___y_2991_);
lean_dec_ref(v___y_2990_);
lean_dec_ref(v_fvarIds_2988_);
return v_res_2995_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__14_spec__17_spec__21(lean_object* v_x_2996_, lean_object* v_x_2997_, lean_object* v_x_2998_){
_start:
{
if (lean_obj_tag(v_x_2998_) == 0)
{
lean_dec(v_x_2996_);
return v_x_2997_;
}
else
{
lean_object* v_head_2999_; lean_object* v_tail_3000_; lean_object* v___x_3002_; uint8_t v_isShared_3003_; uint8_t v_isSharedCheck_3010_; 
v_head_2999_ = lean_ctor_get(v_x_2998_, 0);
v_tail_3000_ = lean_ctor_get(v_x_2998_, 1);
v_isSharedCheck_3010_ = !lean_is_exclusive(v_x_2998_);
if (v_isSharedCheck_3010_ == 0)
{
v___x_3002_ = v_x_2998_;
v_isShared_3003_ = v_isSharedCheck_3010_;
goto v_resetjp_3001_;
}
else
{
lean_inc(v_tail_3000_);
lean_inc(v_head_2999_);
lean_dec(v_x_2998_);
v___x_3002_ = lean_box(0);
v_isShared_3003_ = v_isSharedCheck_3010_;
goto v_resetjp_3001_;
}
v_resetjp_3001_:
{
lean_object* v___x_3005_; 
lean_inc(v_x_2996_);
if (v_isShared_3003_ == 0)
{
lean_ctor_set_tag(v___x_3002_, 5);
lean_ctor_set(v___x_3002_, 1, v_x_2996_);
lean_ctor_set(v___x_3002_, 0, v_x_2997_);
v___x_3005_ = v___x_3002_;
goto v_reusejp_3004_;
}
else
{
lean_object* v_reuseFailAlloc_3009_; 
v_reuseFailAlloc_3009_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3009_, 0, v_x_2997_);
lean_ctor_set(v_reuseFailAlloc_3009_, 1, v_x_2996_);
v___x_3005_ = v_reuseFailAlloc_3009_;
goto v_reusejp_3004_;
}
v_reusejp_3004_:
{
lean_object* v___x_3006_; lean_object* v___x_3007_; 
v___x_3006_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(v_head_2999_);
v___x_3007_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3007_, 0, v___x_3005_);
lean_ctor_set(v___x_3007_, 1, v___x_3006_);
v_x_2997_ = v___x_3007_;
v_x_2998_ = v_tail_3000_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__14_spec__17(lean_object* v_x_3011_, lean_object* v_x_3012_, lean_object* v_x_3013_){
_start:
{
if (lean_obj_tag(v_x_3013_) == 0)
{
lean_dec(v_x_3011_);
return v_x_3012_;
}
else
{
lean_object* v_head_3014_; lean_object* v_tail_3015_; lean_object* v___x_3017_; uint8_t v_isShared_3018_; uint8_t v_isSharedCheck_3025_; 
v_head_3014_ = lean_ctor_get(v_x_3013_, 0);
v_tail_3015_ = lean_ctor_get(v_x_3013_, 1);
v_isSharedCheck_3025_ = !lean_is_exclusive(v_x_3013_);
if (v_isSharedCheck_3025_ == 0)
{
v___x_3017_ = v_x_3013_;
v_isShared_3018_ = v_isSharedCheck_3025_;
goto v_resetjp_3016_;
}
else
{
lean_inc(v_tail_3015_);
lean_inc(v_head_3014_);
lean_dec(v_x_3013_);
v___x_3017_ = lean_box(0);
v_isShared_3018_ = v_isSharedCheck_3025_;
goto v_resetjp_3016_;
}
v_resetjp_3016_:
{
lean_object* v___x_3020_; 
lean_inc(v_x_3011_);
if (v_isShared_3018_ == 0)
{
lean_ctor_set_tag(v___x_3017_, 5);
lean_ctor_set(v___x_3017_, 1, v_x_3011_);
lean_ctor_set(v___x_3017_, 0, v_x_3012_);
v___x_3020_ = v___x_3017_;
goto v_reusejp_3019_;
}
else
{
lean_object* v_reuseFailAlloc_3024_; 
v_reuseFailAlloc_3024_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3024_, 0, v_x_3012_);
lean_ctor_set(v_reuseFailAlloc_3024_, 1, v_x_3011_);
v___x_3020_ = v_reuseFailAlloc_3024_;
goto v_reusejp_3019_;
}
v_reusejp_3019_:
{
lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; 
v___x_3021_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(v_head_3014_);
v___x_3022_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3022_, 0, v___x_3020_);
lean_ctor_set(v___x_3022_, 1, v___x_3021_);
v___x_3023_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__14_spec__17_spec__21(v_x_3011_, v___x_3022_, v_tail_3015_);
return v___x_3023_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__14(lean_object* v_x_3026_, lean_object* v_x_3027_){
_start:
{
if (lean_obj_tag(v_x_3026_) == 0)
{
lean_object* v___x_3028_; 
lean_dec(v_x_3027_);
v___x_3028_ = lean_box(0);
return v___x_3028_;
}
else
{
lean_object* v_tail_3029_; 
v_tail_3029_ = lean_ctor_get(v_x_3026_, 1);
if (lean_obj_tag(v_tail_3029_) == 0)
{
lean_object* v_head_3030_; lean_object* v___x_3031_; 
lean_dec(v_x_3027_);
v_head_3030_ = lean_ctor_get(v_x_3026_, 0);
lean_inc(v_head_3030_);
lean_dec_ref_known(v_x_3026_, 2);
v___x_3031_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(v_head_3030_);
return v___x_3031_;
}
else
{
lean_object* v_head_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; 
lean_inc(v_tail_3029_);
v_head_3032_ = lean_ctor_get(v_x_3026_, 0);
lean_inc(v_head_3032_);
lean_dec_ref_known(v_x_3026_, 2);
v___x_3033_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(v_head_3032_);
v___x_3034_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__14_spec__17(v_x_3027_, v___x_3033_, v_tail_3029_);
return v___x_3034_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__5(void){
_start:
{
lean_object* v___x_3043_; lean_object* v___x_3044_; 
v___x_3043_ = ((lean_object*)(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__0));
v___x_3044_ = lean_string_length(v___x_3043_);
return v___x_3044_;
}
}
static lean_object* _init_l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__6(void){
_start:
{
lean_object* v___x_3045_; lean_object* v___x_3046_; 
v___x_3045_ = lean_obj_once(&l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__5, &l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__5_once, _init_l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__5);
v___x_3046_ = lean_nat_to_int(v___x_3045_);
return v___x_3046_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10(lean_object* v_xs_3054_){
_start:
{
lean_object* v___x_3055_; lean_object* v___x_3056_; uint8_t v___x_3057_; 
v___x_3055_ = lean_array_get_size(v_xs_3054_);
v___x_3056_ = lean_unsigned_to_nat(0u);
v___x_3057_ = lean_nat_dec_eq(v___x_3055_, v___x_3056_);
if (v___x_3057_ == 0)
{
lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; 
v___x_3058_ = lean_array_to_list(v_xs_3054_);
v___x_3059_ = ((lean_object*)(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__3));
v___x_3060_ = l_Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__14(v___x_3058_, v___x_3059_);
v___x_3061_ = lean_obj_once(&l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__6, &l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__6_once, _init_l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__6);
v___x_3062_ = ((lean_object*)(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__7));
v___x_3063_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3063_, 0, v___x_3062_);
lean_ctor_set(v___x_3063_, 1, v___x_3060_);
v___x_3064_ = ((lean_object*)(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__8));
v___x_3065_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3065_, 0, v___x_3063_);
lean_ctor_set(v___x_3065_, 1, v___x_3064_);
v___x_3066_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3066_, 0, v___x_3061_);
lean_ctor_set(v___x_3066_, 1, v___x_3065_);
v___x_3067_ = l_Std_Format_fill(v___x_3066_);
return v___x_3067_;
}
else
{
lean_object* v___x_3068_; 
lean_dec_ref(v_xs_3054_);
v___x_3068_ = ((lean_object*)(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__10));
return v___x_3068_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__11(size_t v_sz_3069_, size_t v_i_3070_, lean_object* v_bs_3071_){
_start:
{
uint8_t v___x_3072_; 
v___x_3072_ = lean_usize_dec_lt(v_i_3070_, v_sz_3069_);
if (v___x_3072_ == 0)
{
return v_bs_3071_;
}
else
{
lean_object* v_v_3073_; lean_object* v___x_3074_; lean_object* v_bs_x27_3075_; lean_object* v___x_3076_; size_t v___x_3077_; size_t v___x_3078_; lean_object* v___x_3079_; 
v_v_3073_ = lean_array_uget(v_bs_3071_, v_i_3070_);
v___x_3074_ = lean_unsigned_to_nat(0u);
v_bs_x27_3075_ = lean_array_uset(v_bs_3071_, v_i_3070_, v___x_3074_);
v___x_3076_ = l_Lean_mkFVar(v_v_3073_);
v___x_3077_ = ((size_t)1ULL);
v___x_3078_ = lean_usize_add(v_i_3070_, v___x_3077_);
v___x_3079_ = lean_array_uset(v_bs_x27_3075_, v_i_3070_, v___x_3076_);
v_i_3070_ = v___x_3078_;
v_bs_3071_ = v___x_3079_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__11___boxed(lean_object* v_sz_3081_, lean_object* v_i_3082_, lean_object* v_bs_3083_){
_start:
{
size_t v_sz_boxed_3084_; size_t v_i_boxed_3085_; lean_object* v_res_3086_; 
v_sz_boxed_3084_ = lean_unbox_usize(v_sz_3081_);
lean_dec(v_sz_3081_);
v_i_boxed_3085_ = lean_unbox_usize(v_i_3082_);
lean_dec(v_i_3082_);
v_res_3086_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__11(v_sz_boxed_3084_, v_i_boxed_3085_, v_bs_3083_);
return v_res_3086_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__2(size_t v_sz_3087_, size_t v_i_3088_, lean_object* v_bs_3089_){
_start:
{
uint8_t v___x_3090_; 
v___x_3090_ = lean_usize_dec_lt(v_i_3088_, v_sz_3087_);
if (v___x_3090_ == 0)
{
return v_bs_3089_;
}
else
{
lean_object* v_v_3091_; lean_object* v_recArgPos_3092_; lean_object* v___x_3093_; lean_object* v_bs_x27_3094_; size_t v___x_3095_; size_t v___x_3096_; lean_object* v___x_3097_; 
v_v_3091_ = lean_array_uget_borrowed(v_bs_3089_, v_i_3088_);
v_recArgPos_3092_ = lean_ctor_get(v_v_3091_, 2);
lean_inc(v_recArgPos_3092_);
v___x_3093_ = lean_unsigned_to_nat(0u);
v_bs_x27_3094_ = lean_array_uset(v_bs_3089_, v_i_3088_, v___x_3093_);
v___x_3095_ = ((size_t)1ULL);
v___x_3096_ = lean_usize_add(v_i_3088_, v___x_3095_);
v___x_3097_ = lean_array_uset(v_bs_x27_3094_, v_i_3088_, v_recArgPos_3092_);
v_i_3088_ = v___x_3096_;
v_bs_3089_ = v___x_3097_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__2___boxed(lean_object* v_sz_3099_, lean_object* v_i_3100_, lean_object* v_bs_3101_){
_start:
{
size_t v_sz_boxed_3102_; size_t v_i_boxed_3103_; lean_object* v_res_3104_; 
v_sz_boxed_3102_ = lean_unbox_usize(v_sz_3099_);
lean_dec(v_sz_3099_);
v_i_boxed_3103_ = lean_unbox_usize(v_i_3100_);
lean_dec(v_i_3100_);
v_res_3104_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__2(v_sz_boxed_3102_, v_i_boxed_3103_, v_bs_3101_);
return v_res_3104_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg(lean_object* v_fst_3105_, size_t v_sz_3106_, size_t v_i_3107_, lean_object* v_bs_3108_){
_start:
{
uint8_t v___x_3109_; 
v___x_3109_ = lean_usize_dec_lt(v_i_3107_, v_sz_3106_);
if (v___x_3109_ == 0)
{
return v_bs_3108_;
}
else
{
lean_object* v_v_3110_; lean_object* v_fnName_3111_; lean_object* v_recArgPos_3112_; lean_object* v_indicesPos_3113_; lean_object* v_indGroupInst_3114_; lean_object* v_indIdx_3115_; lean_object* v___x_3117_; uint8_t v_isShared_3118_; uint8_t v_isSharedCheck_3132_; 
v_v_3110_ = lean_array_uget(v_bs_3108_, v_i_3107_);
v_fnName_3111_ = lean_ctor_get(v_v_3110_, 0);
v_recArgPos_3112_ = lean_ctor_get(v_v_3110_, 2);
v_indicesPos_3113_ = lean_ctor_get(v_v_3110_, 3);
v_indGroupInst_3114_ = lean_ctor_get(v_v_3110_, 4);
v_indIdx_3115_ = lean_ctor_get(v_v_3110_, 5);
v_isSharedCheck_3132_ = !lean_is_exclusive(v_v_3110_);
if (v_isSharedCheck_3132_ == 0)
{
lean_object* v_unused_3133_; 
v_unused_3133_ = lean_ctor_get(v_v_3110_, 1);
lean_dec(v_unused_3133_);
v___x_3117_ = v_v_3110_;
v_isShared_3118_ = v_isSharedCheck_3132_;
goto v_resetjp_3116_;
}
else
{
lean_inc(v_indIdx_3115_);
lean_inc(v_indGroupInst_3114_);
lean_inc(v_indicesPos_3113_);
lean_inc(v_recArgPos_3112_);
lean_inc(v_fnName_3111_);
lean_dec(v_v_3110_);
v___x_3117_ = lean_box(0);
v_isShared_3118_ = v_isSharedCheck_3132_;
goto v_resetjp_3116_;
}
v_resetjp_3116_:
{
lean_object* v_perms_3119_; lean_object* v___x_3120_; lean_object* v_bs_x27_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3126_; 
v_perms_3119_ = lean_ctor_get(v_fst_3105_, 1);
v___x_3120_ = lean_unsigned_to_nat(0u);
v_bs_x27_3121_ = lean_array_uset(v_bs_3108_, v_i_3107_, v___x_3120_);
v___x_3122_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0);
v___x_3123_ = lean_usize_to_nat(v_i_3107_);
v___x_3124_ = lean_array_get_borrowed(v___x_3122_, v_perms_3119_, v___x_3123_);
lean_dec(v___x_3123_);
lean_inc(v___x_3124_);
if (v_isShared_3118_ == 0)
{
lean_ctor_set(v___x_3117_, 1, v___x_3124_);
v___x_3126_ = v___x_3117_;
goto v_reusejp_3125_;
}
else
{
lean_object* v_reuseFailAlloc_3131_; 
v_reuseFailAlloc_3131_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3131_, 0, v_fnName_3111_);
lean_ctor_set(v_reuseFailAlloc_3131_, 1, v___x_3124_);
lean_ctor_set(v_reuseFailAlloc_3131_, 2, v_recArgPos_3112_);
lean_ctor_set(v_reuseFailAlloc_3131_, 3, v_indicesPos_3113_);
lean_ctor_set(v_reuseFailAlloc_3131_, 4, v_indGroupInst_3114_);
lean_ctor_set(v_reuseFailAlloc_3131_, 5, v_indIdx_3115_);
v___x_3126_ = v_reuseFailAlloc_3131_;
goto v_reusejp_3125_;
}
v_reusejp_3125_:
{
size_t v___x_3127_; size_t v___x_3128_; lean_object* v___x_3129_; 
v___x_3127_ = ((size_t)1ULL);
v___x_3128_ = lean_usize_add(v_i_3107_, v___x_3127_);
v___x_3129_ = lean_array_uset(v_bs_x27_3121_, v_i_3107_, v___x_3126_);
v_i_3107_ = v___x_3128_;
v_bs_3108_ = v___x_3129_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg___boxed(lean_object* v_fst_3134_, lean_object* v_sz_3135_, lean_object* v_i_3136_, lean_object* v_bs_3137_){
_start:
{
size_t v_sz_boxed_3138_; size_t v_i_boxed_3139_; lean_object* v_res_3140_; 
v_sz_boxed_3138_ = lean_unbox_usize(v_sz_3135_);
lean_dec(v_sz_3135_);
v_i_boxed_3139_ = lean_unbox_usize(v_i_3136_);
lean_dec(v_i_3136_);
v_res_3140_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg(v_fst_3134_, v_sz_boxed_3138_, v_i_boxed_3139_, v_bs_3137_);
lean_dec_ref(v_fst_3134_);
return v_res_3140_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__1(void){
_start:
{
lean_object* v___x_3142_; lean_object* v___x_3143_; 
v___x_3142_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__0));
v___x_3143_ = l_Lean_stringToMessageData(v___x_3142_);
return v___x_3143_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__3(void){
_start:
{
lean_object* v___x_3145_; lean_object* v___x_3146_; 
v___x_3145_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__2));
v___x_3146_ = l_Lean_stringToMessageData(v___x_3145_);
return v___x_3146_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__5(void){
_start:
{
lean_object* v___x_3148_; lean_object* v___x_3149_; 
v___x_3148_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__4));
v___x_3149_ = l_Lean_stringToMessageData(v___x_3148_);
return v___x_3149_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6(lean_object* v_a_3150_, lean_object* v_as_3151_, size_t v_sz_3152_, size_t v_i_3153_, lean_object* v_b_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_){
_start:
{
lean_object* v_a_3161_; uint8_t v___x_3165_; 
v___x_3165_ = lean_usize_dec_lt(v_i_3153_, v_sz_3152_);
if (v___x_3165_ == 0)
{
lean_object* v___x_3166_; 
lean_dec_ref(v_a_3150_);
v___x_3166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3166_, 0, v_b_3154_);
return v___x_3166_;
}
else
{
lean_object* v_a_3167_; lean_object* v___x_3168_; 
v_a_3167_ = lean_array_uget_borrowed(v_as_3151_, v_i_3153_);
lean_inc(v_a_3167_);
lean_inc_ref(v_a_3150_);
v___x_3168_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg(v_a_3150_, v_a_3167_, v___y_3156_);
if (lean_obj_tag(v___x_3168_) == 0)
{
lean_object* v_a_3169_; lean_object* v___x_3170_; uint8_t v___x_3171_; 
v_a_3169_ = lean_ctor_get(v___x_3168_, 0);
lean_inc(v_a_3169_);
lean_dec_ref_known(v___x_3168_, 1);
v___x_3170_ = lean_box(0);
v___x_3171_ = lean_unbox(v_a_3169_);
lean_dec(v_a_3169_);
if (v___x_3171_ == 0)
{
v_a_3161_ = v___x_3170_;
goto v___jp_3160_;
}
else
{
uint8_t v___x_3172_; 
v___x_3172_ = l_Lean_Expr_isFVarOf(v_a_3150_, v_a_3167_);
if (v___x_3172_ == 0)
{
lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; 
v___x_3173_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__1);
lean_inc_ref(v_a_3150_);
v___x_3174_ = l_Lean_indentExpr(v_a_3150_);
v___x_3175_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3175_, 0, v___x_3173_);
lean_ctor_set(v___x_3175_, 1, v___x_3174_);
v___x_3176_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__3);
v___x_3177_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3177_, 0, v___x_3175_);
lean_ctor_set(v___x_3177_, 1, v___x_3176_);
lean_inc(v_a_3167_);
v___x_3178_ = l_Lean_mkFVar(v_a_3167_);
v___x_3179_ = l_Lean_indentExpr(v___x_3178_);
v___x_3180_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3180_, 0, v___x_3177_);
lean_ctor_set(v___x_3180_, 1, v___x_3179_);
v___x_3181_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__5);
v___x_3182_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3182_, 0, v___x_3180_);
lean_ctor_set(v___x_3182_, 1, v___x_3181_);
v___x_3183_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg(v___x_3182_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_);
if (lean_obj_tag(v___x_3183_) == 0)
{
lean_dec_ref_known(v___x_3183_, 1);
v_a_3161_ = v___x_3170_;
goto v___jp_3160_;
}
else
{
lean_dec_ref(v_a_3150_);
return v___x_3183_;
}
}
else
{
lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; 
v___x_3184_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__1);
lean_inc_ref(v_a_3150_);
v___x_3185_ = l_Lean_indentExpr(v_a_3150_);
v___x_3186_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3186_, 0, v___x_3184_);
lean_ctor_set(v___x_3186_, 1, v___x_3185_);
v___x_3187_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__5);
v___x_3188_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3188_, 0, v___x_3186_);
lean_ctor_set(v___x_3188_, 1, v___x_3187_);
v___x_3189_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg(v___x_3188_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_);
if (lean_obj_tag(v___x_3189_) == 0)
{
lean_dec_ref_known(v___x_3189_, 1);
v_a_3161_ = v___x_3170_;
goto v___jp_3160_;
}
else
{
lean_dec_ref(v_a_3150_);
return v___x_3189_;
}
}
}
}
else
{
lean_object* v_a_3190_; lean_object* v___x_3192_; uint8_t v_isShared_3193_; uint8_t v_isSharedCheck_3197_; 
lean_dec_ref(v_a_3150_);
v_a_3190_ = lean_ctor_get(v___x_3168_, 0);
v_isSharedCheck_3197_ = !lean_is_exclusive(v___x_3168_);
if (v_isSharedCheck_3197_ == 0)
{
v___x_3192_ = v___x_3168_;
v_isShared_3193_ = v_isSharedCheck_3197_;
goto v_resetjp_3191_;
}
else
{
lean_inc(v_a_3190_);
lean_dec(v___x_3168_);
v___x_3192_ = lean_box(0);
v_isShared_3193_ = v_isSharedCheck_3197_;
goto v_resetjp_3191_;
}
v_resetjp_3191_:
{
lean_object* v___x_3195_; 
if (v_isShared_3193_ == 0)
{
v___x_3195_ = v___x_3192_;
goto v_reusejp_3194_;
}
else
{
lean_object* v_reuseFailAlloc_3196_; 
v_reuseFailAlloc_3196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3196_, 0, v_a_3190_);
v___x_3195_ = v_reuseFailAlloc_3196_;
goto v_reusejp_3194_;
}
v_reusejp_3194_:
{
return v___x_3195_;
}
}
}
}
v___jp_3160_:
{
size_t v___x_3162_; size_t v___x_3163_; 
v___x_3162_ = ((size_t)1ULL);
v___x_3163_ = lean_usize_add(v_i_3153_, v___x_3162_);
v_i_3153_ = v___x_3163_;
v_b_3154_ = v_a_3161_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___boxed(lean_object* v_a_3198_, lean_object* v_as_3199_, lean_object* v_sz_3200_, lean_object* v_i_3201_, lean_object* v_b_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_){
_start:
{
size_t v_sz_boxed_3208_; size_t v_i_boxed_3209_; lean_object* v_res_3210_; 
v_sz_boxed_3208_ = lean_unbox_usize(v_sz_3200_);
lean_dec(v_sz_3200_);
v_i_boxed_3209_ = lean_unbox_usize(v_i_3201_);
lean_dec(v_i_3201_);
v_res_3210_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6(v_a_3198_, v_as_3199_, v_sz_boxed_3208_, v_i_boxed_3209_, v_b_3202_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_);
lean_dec(v___y_3206_);
lean_dec_ref(v___y_3205_);
lean_dec(v___y_3204_);
lean_dec_ref(v___y_3203_);
lean_dec_ref(v_as_3199_);
return v_res_3210_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7(lean_object* v_snd_3211_, lean_object* v_as_3212_, size_t v_sz_3213_, size_t v_i_3214_, lean_object* v_b_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_){
_start:
{
uint8_t v___x_3221_; 
v___x_3221_ = lean_usize_dec_lt(v_i_3214_, v_sz_3213_);
if (v___x_3221_ == 0)
{
lean_object* v___x_3222_; 
v___x_3222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3222_, 0, v_b_3215_);
return v___x_3222_;
}
else
{
lean_object* v___x_3223_; lean_object* v_a_3224_; size_t v_sz_3225_; size_t v___x_3226_; lean_object* v___x_3227_; 
v___x_3223_ = lean_box(0);
v_a_3224_ = lean_array_uget_borrowed(v_as_3212_, v_i_3214_);
v_sz_3225_ = lean_array_size(v_snd_3211_);
v___x_3226_ = ((size_t)0ULL);
lean_inc(v_a_3224_);
v___x_3227_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6(v_a_3224_, v_snd_3211_, v_sz_3225_, v___x_3226_, v___x_3223_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_);
if (lean_obj_tag(v___x_3227_) == 0)
{
size_t v___x_3228_; size_t v___x_3229_; 
lean_dec_ref_known(v___x_3227_, 1);
v___x_3228_ = ((size_t)1ULL);
v___x_3229_ = lean_usize_add(v_i_3214_, v___x_3228_);
v_i_3214_ = v___x_3229_;
v_b_3215_ = v___x_3223_;
goto _start;
}
else
{
return v___x_3227_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7___boxed(lean_object* v_snd_3231_, lean_object* v_as_3232_, lean_object* v_sz_3233_, lean_object* v_i_3234_, lean_object* v_b_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_){
_start:
{
size_t v_sz_boxed_3241_; size_t v_i_boxed_3242_; lean_object* v_res_3243_; 
v_sz_boxed_3241_ = lean_unbox_usize(v_sz_3233_);
lean_dec(v_sz_3233_);
v_i_boxed_3242_ = lean_unbox_usize(v_i_3234_);
lean_dec(v_i_3234_);
v_res_3243_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7(v_snd_3231_, v_as_3232_, v_sz_boxed_3241_, v_i_boxed_3242_, v_b_3235_, v___y_3236_, v___y_3237_, v___y_3238_, v___y_3239_);
lean_dec(v___y_3239_);
lean_dec_ref(v___y_3238_);
lean_dec(v___y_3237_);
lean_dec_ref(v___y_3236_);
lean_dec_ref(v_as_3232_);
lean_dec_ref(v_snd_3231_);
return v_res_3243_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8(lean_object* v_snd_3244_, lean_object* v_as_3245_, size_t v_sz_3246_, size_t v_i_3247_, lean_object* v_b_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_){
_start:
{
uint8_t v___x_3254_; 
v___x_3254_ = lean_usize_dec_lt(v_i_3247_, v_sz_3246_);
if (v___x_3254_ == 0)
{
lean_object* v___x_3255_; 
v___x_3255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3255_, 0, v_b_3248_);
return v___x_3255_;
}
else
{
lean_object* v_a_3256_; lean_object* v_indGroupInst_3257_; lean_object* v_params_3258_; lean_object* v___x_3259_; size_t v_sz_3260_; size_t v___x_3261_; lean_object* v___x_3262_; 
v_a_3256_ = lean_array_uget_borrowed(v_as_3245_, v_i_3247_);
v_indGroupInst_3257_ = lean_ctor_get(v_a_3256_, 4);
v_params_3258_ = lean_ctor_get(v_indGroupInst_3257_, 2);
v___x_3259_ = lean_box(0);
v_sz_3260_ = lean_array_size(v_params_3258_);
v___x_3261_ = ((size_t)0ULL);
v___x_3262_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7(v_snd_3244_, v_params_3258_, v_sz_3260_, v___x_3261_, v___x_3259_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_);
if (lean_obj_tag(v___x_3262_) == 0)
{
size_t v___x_3263_; size_t v___x_3264_; 
lean_dec_ref_known(v___x_3262_, 1);
v___x_3263_ = ((size_t)1ULL);
v___x_3264_ = lean_usize_add(v_i_3247_, v___x_3263_);
v_i_3247_ = v___x_3264_;
v_b_3248_ = v___x_3259_;
goto _start;
}
else
{
return v___x_3262_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8___boxed(lean_object* v_snd_3266_, lean_object* v_as_3267_, lean_object* v_sz_3268_, lean_object* v_i_3269_, lean_object* v_b_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_){
_start:
{
size_t v_sz_boxed_3276_; size_t v_i_boxed_3277_; lean_object* v_res_3278_; 
v_sz_boxed_3276_ = lean_unbox_usize(v_sz_3268_);
lean_dec(v_sz_3268_);
v_i_boxed_3277_ = lean_unbox_usize(v_i_3269_);
lean_dec(v_i_3269_);
v_res_3278_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8(v_snd_3266_, v_as_3267_, v_sz_boxed_3276_, v_i_boxed_3277_, v_b_3270_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_);
lean_dec(v___y_3274_);
lean_dec_ref(v___y_3273_);
lean_dec(v___y_3272_);
lean_dec_ref(v___y_3271_);
lean_dec_ref(v_as_3267_);
lean_dec_ref(v_snd_3266_);
return v_res_3278_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__0(void){
_start:
{
lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; 
v___x_3279_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__3));
v___x_3280_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0___closed__1));
v___x_3281_ = l_Lean_Name_append(v___x_3280_, v___x_3279_);
return v___x_3281_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3283_; lean_object* v___x_3284_; 
v___x_3283_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__1));
v___x_3284_ = l_Lean_stringToMessageData(v___x_3283_);
return v___x_3284_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__4(void){
_start:
{
lean_object* v___x_3286_; lean_object* v___x_3287_; 
v___x_3286_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__3));
v___x_3287_ = l_Lean_stringToMessageData(v___x_3286_);
return v___x_3287_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__6(void){
_start:
{
lean_object* v___x_3289_; lean_object* v___x_3290_; 
v___x_3289_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__5));
v___x_3290_ = l_Lean_stringToMessageData(v___x_3289_);
return v___x_3290_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__8(void){
_start:
{
lean_object* v___x_3292_; lean_object* v___x_3293_; 
v___x_3292_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__7));
v___x_3293_ = l_Lean_stringToMessageData(v___x_3292_);
return v___x_3293_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__10(void){
_start:
{
lean_object* v___x_3295_; lean_object* v___x_3296_; 
v___x_3295_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__9));
v___x_3296_ = l_Lean_stringToMessageData(v___x_3295_);
return v___x_3296_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0(size_t v___x_3297_, lean_object* v_a_3298_, lean_object* v_xs_3299_, lean_object* v_a_3300_, lean_object* v_recArgInfos_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_){
_start:
{
lean_object* v___y_3308_; lean_object* v___y_3309_; lean_object* v___y_3310_; lean_object* v___y_3311_; lean_object* v___y_3312_; lean_object* v___y_3313_; lean_object* v___y_3314_; lean_object* v___x_3327_; lean_object* v___y_3329_; lean_object* v___y_3330_; lean_object* v___y_3331_; lean_object* v___y_3332_; lean_object* v___y_3333_; lean_object* v___y_3334_; lean_object* v___y_3335_; lean_object* v___x_3355_; lean_object* v_a_3356_; size_t v_sz_3357_; lean_object* v___x_3358_; lean_object* v___y_3360_; lean_object* v___y_3361_; lean_object* v___y_3362_; lean_object* v___y_3363_; uint8_t v___x_3420_; 
v___x_3327_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__3));
v___x_3355_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0(v___x_3327_, v___y_3302_, v___y_3303_, v___y_3304_, v___y_3305_);
v_a_3356_ = lean_ctor_get(v___x_3355_, 0);
lean_inc(v_a_3356_);
lean_dec_ref(v___x_3355_);
v_sz_3357_ = lean_array_size(v_recArgInfos_3301_);
lean_inc_ref(v_recArgInfos_3301_);
v___x_3358_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__2(v_sz_3357_, v___x_3297_, v_recArgInfos_3301_);
v___x_3420_ = lean_unbox(v_a_3356_);
lean_dec(v_a_3356_);
if (v___x_3420_ == 0)
{
v___y_3360_ = v___y_3302_;
v___y_3361_ = v___y_3303_;
v___y_3362_ = v___y_3304_;
v___y_3363_ = v___y_3305_;
goto v___jp_3359_;
}
else
{
lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; 
v___x_3421_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__10, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__10);
lean_inc_ref(v___x_3358_);
v___x_3422_ = lean_array_to_list(v___x_3358_);
v___x_3423_ = lean_box(0);
v___x_3424_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__0(v___x_3422_, v___x_3423_);
v___x_3425_ = l_Lean_MessageData_ofList(v___x_3424_);
v___x_3426_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3426_, 0, v___x_3421_);
lean_ctor_set(v___x_3426_, 1, v___x_3425_);
v___x_3427_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_3327_, v___x_3426_, v___y_3302_, v___y_3303_, v___y_3304_, v___y_3305_);
if (lean_obj_tag(v___x_3427_) == 0)
{
lean_dec_ref_known(v___x_3427_, 1);
v___y_3360_ = v___y_3302_;
v___y_3361_ = v___y_3303_;
v___y_3362_ = v___y_3304_;
v___y_3363_ = v___y_3305_;
goto v___jp_3359_;
}
else
{
lean_object* v_a_3428_; lean_object* v___x_3430_; uint8_t v_isShared_3431_; uint8_t v_isSharedCheck_3435_; 
lean_dec_ref(v___x_3358_);
lean_dec_ref(v_recArgInfos_3301_);
lean_dec_ref(v_a_3300_);
lean_dec_ref(v_xs_3299_);
lean_dec_ref(v_a_3298_);
v_a_3428_ = lean_ctor_get(v___x_3427_, 0);
v_isSharedCheck_3435_ = !lean_is_exclusive(v___x_3427_);
if (v_isSharedCheck_3435_ == 0)
{
v___x_3430_ = v___x_3427_;
v_isShared_3431_ = v_isSharedCheck_3435_;
goto v_resetjp_3429_;
}
else
{
lean_inc(v_a_3428_);
lean_dec(v___x_3427_);
v___x_3430_ = lean_box(0);
v_isShared_3431_ = v_isSharedCheck_3435_;
goto v_resetjp_3429_;
}
v_resetjp_3429_:
{
lean_object* v___x_3433_; 
if (v_isShared_3431_ == 0)
{
v___x_3433_ = v___x_3430_;
goto v_reusejp_3432_;
}
else
{
lean_object* v_reuseFailAlloc_3434_; 
v_reuseFailAlloc_3434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3434_, 0, v_a_3428_);
v___x_3433_ = v_reuseFailAlloc_3434_;
goto v_reusejp_3432_;
}
v_reusejp_3432_:
{
return v___x_3433_;
}
}
}
}
v___jp_3307_:
{
lean_object* v___x_3315_; size_t v_sz_3316_; lean_object* v___x_3317_; 
v___x_3315_ = lean_box(0);
v_sz_3316_ = lean_array_size(v___y_3310_);
v___x_3317_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8(v___y_3308_, v___y_3310_, v_sz_3316_, v___x_3297_, v___x_3315_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_);
lean_dec_ref(v___y_3310_);
if (lean_obj_tag(v___x_3317_) == 0)
{
lean_object* v___x_3318_; 
lean_dec_ref_known(v___x_3317_, 1);
v___x_3318_ = l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___redArg(v___y_3308_, v___y_3309_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_);
lean_dec_ref(v___y_3308_);
return v___x_3318_;
}
else
{
lean_object* v_a_3319_; lean_object* v___x_3321_; uint8_t v_isShared_3322_; uint8_t v_isSharedCheck_3326_; 
lean_dec_ref(v___y_3309_);
lean_dec_ref(v___y_3308_);
v_a_3319_ = lean_ctor_get(v___x_3317_, 0);
v_isSharedCheck_3326_ = !lean_is_exclusive(v___x_3317_);
if (v_isSharedCheck_3326_ == 0)
{
v___x_3321_ = v___x_3317_;
v_isShared_3322_ = v_isSharedCheck_3326_;
goto v_resetjp_3320_;
}
else
{
lean_inc(v_a_3319_);
lean_dec(v___x_3317_);
v___x_3321_ = lean_box(0);
v_isShared_3322_ = v_isSharedCheck_3326_;
goto v_resetjp_3320_;
}
v_resetjp_3320_:
{
lean_object* v___x_3324_; 
if (v_isShared_3322_ == 0)
{
v___x_3324_ = v___x_3321_;
goto v_reusejp_3323_;
}
else
{
lean_object* v_reuseFailAlloc_3325_; 
v_reuseFailAlloc_3325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3325_, 0, v_a_3319_);
v___x_3324_ = v_reuseFailAlloc_3325_;
goto v_reusejp_3323_;
}
v_reusejp_3323_:
{
return v___x_3324_;
}
}
}
}
v___jp_3328_:
{
lean_object* v_options_3336_; uint8_t v_hasTrace_3337_; 
v_options_3336_ = lean_ctor_get(v___y_3334_, 1);
v_hasTrace_3337_ = lean_ctor_get_uint8(v_options_3336_, sizeof(void*)*1);
if (v_hasTrace_3337_ == 0)
{
v___y_3308_ = v___y_3329_;
v___y_3309_ = v___y_3330_;
v___y_3310_ = v___y_3331_;
v___y_3311_ = v___y_3332_;
v___y_3312_ = v___y_3333_;
v___y_3313_ = v___y_3334_;
v___y_3314_ = v___y_3335_;
goto v___jp_3307_;
}
else
{
lean_object* v_toCold_3338_; lean_object* v_inheritedTraceOptions_3339_; lean_object* v___x_3340_; uint8_t v___x_3341_; 
v_toCold_3338_ = lean_ctor_get(v___y_3334_, 0);
v_inheritedTraceOptions_3339_ = lean_ctor_get(v_toCold_3338_, 4);
v___x_3340_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__0);
v___x_3341_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3339_, v_options_3336_, v___x_3340_);
if (v___x_3341_ == 0)
{
v___y_3308_ = v___y_3329_;
v___y_3309_ = v___y_3330_;
v___y_3310_ = v___y_3331_;
v___y_3311_ = v___y_3332_;
v___y_3312_ = v___y_3333_;
v___y_3313_ = v___y_3334_;
v___y_3314_ = v___y_3335_;
goto v___jp_3307_;
}
else
{
lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; 
v___x_3342_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__2);
lean_inc_ref(v___y_3331_);
v___x_3343_ = l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10(v___y_3331_);
v___x_3344_ = l_Lean_MessageData_ofFormat(v___x_3343_);
v___x_3345_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3345_, 0, v___x_3342_);
lean_ctor_set(v___x_3345_, 1, v___x_3344_);
v___x_3346_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_3327_, v___x_3345_, v___y_3332_, v___y_3333_, v___y_3334_, v___y_3335_);
if (lean_obj_tag(v___x_3346_) == 0)
{
lean_dec_ref_known(v___x_3346_, 1);
v___y_3308_ = v___y_3329_;
v___y_3309_ = v___y_3330_;
v___y_3310_ = v___y_3331_;
v___y_3311_ = v___y_3332_;
v___y_3312_ = v___y_3333_;
v___y_3313_ = v___y_3334_;
v___y_3314_ = v___y_3335_;
goto v___jp_3307_;
}
else
{
lean_object* v_a_3347_; lean_object* v___x_3349_; uint8_t v_isShared_3350_; uint8_t v_isSharedCheck_3354_; 
lean_dec_ref(v___y_3331_);
lean_dec_ref(v___y_3330_);
lean_dec_ref(v___y_3329_);
v_a_3347_ = lean_ctor_get(v___x_3346_, 0);
v_isSharedCheck_3354_ = !lean_is_exclusive(v___x_3346_);
if (v_isSharedCheck_3354_ == 0)
{
v___x_3349_ = v___x_3346_;
v_isShared_3350_ = v_isSharedCheck_3354_;
goto v_resetjp_3348_;
}
else
{
lean_inc(v_a_3347_);
lean_dec(v___x_3346_);
v___x_3349_ = lean_box(0);
v_isShared_3350_ = v_isSharedCheck_3354_;
goto v_resetjp_3348_;
}
v_resetjp_3348_:
{
lean_object* v___x_3352_; 
if (v_isShared_3350_ == 0)
{
v___x_3352_ = v___x_3349_;
goto v_reusejp_3351_;
}
else
{
lean_object* v_reuseFailAlloc_3353_; 
v_reuseFailAlloc_3353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3353_, 0, v_a_3347_);
v___x_3352_ = v_reuseFailAlloc_3353_;
goto v_reusejp_3351_;
}
v_reusejp_3351_:
{
return v___x_3352_;
}
}
}
}
}
}
v___jp_3359_:
{
lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v_snd_3366_; lean_object* v_fst_3367_; lean_object* v___x_3369_; uint8_t v_isShared_3370_; uint8_t v_isSharedCheck_3419_; 
lean_inc_ref(v_recArgInfos_3301_);
v___x_3364_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__3(v_sz_3357_, v___x_3297_, v_recArgInfos_3301_);
lean_inc_ref(v_xs_3299_);
v___x_3365_ = l_Lean_Elab_FixedParamPerms_erase(v_a_3298_, v_xs_3299_, v___x_3364_);
v_snd_3366_ = lean_ctor_get(v___x_3365_, 1);
v_fst_3367_ = lean_ctor_get(v___x_3365_, 0);
v_isSharedCheck_3419_ = !lean_is_exclusive(v___x_3365_);
if (v_isSharedCheck_3419_ == 0)
{
v___x_3369_ = v___x_3365_;
v_isShared_3370_ = v_isSharedCheck_3419_;
goto v_resetjp_3368_;
}
else
{
lean_inc(v_snd_3366_);
lean_inc(v_fst_3367_);
lean_dec(v___x_3365_);
v___x_3369_ = lean_box(0);
v_isShared_3370_ = v_isSharedCheck_3419_;
goto v_resetjp_3368_;
}
v_resetjp_3368_:
{
lean_object* v_fst_3371_; lean_object* v_snd_3372_; lean_object* v___x_3374_; uint8_t v_isShared_3375_; uint8_t v_isSharedCheck_3418_; 
v_fst_3371_ = lean_ctor_get(v_snd_3366_, 0);
v_snd_3372_ = lean_ctor_get(v_snd_3366_, 1);
v_isSharedCheck_3418_ = !lean_is_exclusive(v_snd_3366_);
if (v_isSharedCheck_3418_ == 0)
{
v___x_3374_ = v_snd_3366_;
v_isShared_3375_ = v_isSharedCheck_3418_;
goto v_resetjp_3373_;
}
else
{
lean_inc(v_snd_3372_);
lean_inc(v_fst_3371_);
lean_dec(v_snd_3366_);
v___x_3374_ = lean_box(0);
v_isShared_3375_ = v_isSharedCheck_3418_;
goto v_resetjp_3373_;
}
v_resetjp_3373_:
{
lean_object* v___x_3376_; lean_object* v___f_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; uint8_t v___x_3380_; 
v___x_3376_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg(v_fst_3367_, v_sz_3357_, v___x_3297_, v_recArgInfos_3301_);
lean_inc_ref(v___x_3376_);
lean_inc(v_fst_3371_);
v___f_3377_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___boxed), 10, 5);
lean_closure_set(v___f_3377_, 0, v_a_3300_);
lean_closure_set(v___f_3377_, 1, v_fst_3367_);
lean_closure_set(v___f_3377_, 2, v_fst_3371_);
lean_closure_set(v___f_3377_, 3, v___x_3376_);
lean_closure_set(v___f_3377_, 4, v___x_3358_);
v___x_3378_ = lean_array_get_size(v_fst_3371_);
v___x_3379_ = lean_array_get_size(v_xs_3299_);
v___x_3380_ = lean_nat_dec_eq(v___x_3378_, v___x_3379_);
if (v___x_3380_ == 0)
{
lean_object* v___x_3381_; lean_object* v_a_3382_; uint8_t v___x_3383_; 
v___x_3381_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0(v___x_3327_, v___y_3360_, v___y_3361_, v___y_3362_, v___y_3363_);
v_a_3382_ = lean_ctor_get(v___x_3381_, 0);
lean_inc(v_a_3382_);
lean_dec_ref(v___x_3381_);
v___x_3383_ = lean_unbox(v_a_3382_);
lean_dec(v_a_3382_);
if (v___x_3383_ == 0)
{
lean_del_object(v___x_3374_);
lean_dec(v_fst_3371_);
lean_del_object(v___x_3369_);
lean_dec_ref(v_xs_3299_);
v___y_3329_ = v_snd_3372_;
v___y_3330_ = v___f_3377_;
v___y_3331_ = v___x_3376_;
v___y_3332_ = v___y_3360_;
v___y_3333_ = v___y_3361_;
v___y_3334_ = v___y_3362_;
v___y_3335_ = v___y_3363_;
goto v___jp_3328_;
}
else
{
lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3390_; 
v___x_3384_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__4);
v___x_3385_ = lean_array_to_list(v_xs_3299_);
v___x_3386_ = lean_box(0);
v___x_3387_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_3385_, v___x_3386_);
v___x_3388_ = l_Lean_MessageData_ofList(v___x_3387_);
if (v_isShared_3375_ == 0)
{
lean_ctor_set_tag(v___x_3374_, 7);
lean_ctor_set(v___x_3374_, 1, v___x_3388_);
lean_ctor_set(v___x_3374_, 0, v___x_3384_);
v___x_3390_ = v___x_3374_;
goto v_reusejp_3389_;
}
else
{
lean_object* v_reuseFailAlloc_3416_; 
v_reuseFailAlloc_3416_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3416_, 0, v___x_3384_);
lean_ctor_set(v_reuseFailAlloc_3416_, 1, v___x_3388_);
v___x_3390_ = v_reuseFailAlloc_3416_;
goto v_reusejp_3389_;
}
v_reusejp_3389_:
{
lean_object* v___x_3391_; lean_object* v___x_3393_; 
v___x_3391_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__6, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__6);
if (v_isShared_3370_ == 0)
{
lean_ctor_set_tag(v___x_3369_, 7);
lean_ctor_set(v___x_3369_, 1, v___x_3391_);
lean_ctor_set(v___x_3369_, 0, v___x_3390_);
v___x_3393_ = v___x_3369_;
goto v_reusejp_3392_;
}
else
{
lean_object* v_reuseFailAlloc_3415_; 
v_reuseFailAlloc_3415_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3415_, 0, v___x_3390_);
lean_ctor_set(v_reuseFailAlloc_3415_, 1, v___x_3391_);
v___x_3393_ = v_reuseFailAlloc_3415_;
goto v_reusejp_3392_;
}
v_reusejp_3392_:
{
lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; size_t v_sz_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; 
v___x_3394_ = lean_array_to_list(v_fst_3371_);
v___x_3395_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_3394_, v___x_3386_);
v___x_3396_ = l_Lean_MessageData_ofList(v___x_3395_);
v___x_3397_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3397_, 0, v___x_3393_);
lean_ctor_set(v___x_3397_, 1, v___x_3396_);
v___x_3398_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__8);
v___x_3399_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3399_, 0, v___x_3397_);
lean_ctor_set(v___x_3399_, 1, v___x_3398_);
v_sz_3400_ = lean_array_size(v_snd_3372_);
lean_inc(v_snd_3372_);
v___x_3401_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__11(v_sz_3400_, v___x_3297_, v_snd_3372_);
v___x_3402_ = lean_array_to_list(v___x_3401_);
v___x_3403_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_3402_, v___x_3386_);
v___x_3404_ = l_Lean_MessageData_ofList(v___x_3403_);
v___x_3405_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3405_, 0, v___x_3399_);
lean_ctor_set(v___x_3405_, 1, v___x_3404_);
v___x_3406_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_3327_, v___x_3405_, v___y_3360_, v___y_3361_, v___y_3362_, v___y_3363_);
if (lean_obj_tag(v___x_3406_) == 0)
{
lean_dec_ref_known(v___x_3406_, 1);
v___y_3329_ = v_snd_3372_;
v___y_3330_ = v___f_3377_;
v___y_3331_ = v___x_3376_;
v___y_3332_ = v___y_3360_;
v___y_3333_ = v___y_3361_;
v___y_3334_ = v___y_3362_;
v___y_3335_ = v___y_3363_;
goto v___jp_3328_;
}
else
{
lean_object* v_a_3407_; lean_object* v___x_3409_; uint8_t v_isShared_3410_; uint8_t v_isSharedCheck_3414_; 
lean_dec_ref(v___f_3377_);
lean_dec_ref(v___x_3376_);
lean_dec(v_snd_3372_);
v_a_3407_ = lean_ctor_get(v___x_3406_, 0);
v_isSharedCheck_3414_ = !lean_is_exclusive(v___x_3406_);
if (v_isSharedCheck_3414_ == 0)
{
v___x_3409_ = v___x_3406_;
v_isShared_3410_ = v_isSharedCheck_3414_;
goto v_resetjp_3408_;
}
else
{
lean_inc(v_a_3407_);
lean_dec(v___x_3406_);
v___x_3409_ = lean_box(0);
v_isShared_3410_ = v_isSharedCheck_3414_;
goto v_resetjp_3408_;
}
v_resetjp_3408_:
{
lean_object* v___x_3412_; 
if (v_isShared_3410_ == 0)
{
v___x_3412_ = v___x_3409_;
goto v_reusejp_3411_;
}
else
{
lean_object* v_reuseFailAlloc_3413_; 
v_reuseFailAlloc_3413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3413_, 0, v_a_3407_);
v___x_3412_ = v_reuseFailAlloc_3413_;
goto v_reusejp_3411_;
}
v_reusejp_3411_:
{
return v___x_3412_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3417_; 
lean_dec_ref(v___x_3376_);
lean_del_object(v___x_3374_);
lean_dec(v_fst_3371_);
lean_del_object(v___x_3369_);
lean_dec_ref(v_xs_3299_);
v___x_3417_ = l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___redArg(v_snd_3372_, v___f_3377_, v___y_3360_, v___y_3361_, v___y_3362_, v___y_3363_);
lean_dec(v_snd_3372_);
return v___x_3417_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___boxed(lean_object* v___x_3436_, lean_object* v_a_3437_, lean_object* v_xs_3438_, lean_object* v_a_3439_, lean_object* v_recArgInfos_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_){
_start:
{
size_t v___x_13040__boxed_3446_; lean_object* v_res_3447_; 
v___x_13040__boxed_3446_ = lean_unbox_usize(v___x_3436_);
lean_dec(v___x_3436_);
v_res_3447_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0(v___x_13040__boxed_3446_, v_a_3437_, v_xs_3438_, v_a_3439_, v_recArgInfos_3440_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_);
lean_dec(v___y_3444_);
lean_dec_ref(v___y_3443_);
lean_dec(v___y_3442_);
lean_dec_ref(v___y_3441_);
return v_res_3447_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg(lean_object* v___x_3448_, lean_object* v_xs_3449_, size_t v_sz_3450_, size_t v_i_3451_, lean_object* v_bs_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_){
_start:
{
uint8_t v___x_3458_; 
v___x_3458_ = lean_usize_dec_lt(v_i_3451_, v_sz_3450_);
if (v___x_3458_ == 0)
{
lean_object* v___x_3459_; 
lean_dec_ref(v_xs_3449_);
v___x_3459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3459_, 0, v_bs_3452_);
return v___x_3459_;
}
else
{
lean_object* v_v_3460_; lean_object* v_value_3461_; lean_object* v___x_3462_; lean_object* v_bs_x27_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; 
v_v_3460_ = lean_array_uget_borrowed(v_bs_3452_, v_i_3451_);
v_value_3461_ = lean_ctor_get(v_v_3460_, 7);
lean_inc_ref(v_value_3461_);
v___x_3462_ = lean_unsigned_to_nat(0u);
v_bs_x27_3463_ = lean_array_uset(v_bs_3452_, v_i_3451_, v___x_3462_);
v___x_3464_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0);
v___x_3465_ = lean_usize_to_nat(v_i_3451_);
v___x_3466_ = lean_array_get_borrowed(v___x_3464_, v___x_3448_, v___x_3465_);
lean_dec(v___x_3465_);
lean_inc_ref(v_xs_3449_);
lean_inc(v___x_3466_);
v___x_3467_ = l_Lean_Elab_FixedParamPerm_instantiateLambda(v___x_3466_, v_value_3461_, v_xs_3449_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_);
if (lean_obj_tag(v___x_3467_) == 0)
{
lean_object* v_a_3468_; size_t v___x_3469_; size_t v___x_3470_; lean_object* v___x_3471_; 
v_a_3468_ = lean_ctor_get(v___x_3467_, 0);
lean_inc(v_a_3468_);
lean_dec_ref_known(v___x_3467_, 1);
v___x_3469_ = ((size_t)1ULL);
v___x_3470_ = lean_usize_add(v_i_3451_, v___x_3469_);
v___x_3471_ = lean_array_uset(v_bs_x27_3463_, v_i_3451_, v_a_3468_);
v_i_3451_ = v___x_3470_;
v_bs_3452_ = v___x_3471_;
goto _start;
}
else
{
lean_object* v_a_3473_; lean_object* v___x_3475_; uint8_t v_isShared_3476_; uint8_t v_isSharedCheck_3480_; 
lean_dec_ref(v_bs_x27_3463_);
lean_dec_ref(v_xs_3449_);
v_a_3473_ = lean_ctor_get(v___x_3467_, 0);
v_isSharedCheck_3480_ = !lean_is_exclusive(v___x_3467_);
if (v_isSharedCheck_3480_ == 0)
{
v___x_3475_ = v___x_3467_;
v_isShared_3476_ = v_isSharedCheck_3480_;
goto v_resetjp_3474_;
}
else
{
lean_inc(v_a_3473_);
lean_dec(v___x_3467_);
v___x_3475_ = lean_box(0);
v_isShared_3476_ = v_isSharedCheck_3480_;
goto v_resetjp_3474_;
}
v_resetjp_3474_:
{
lean_object* v___x_3478_; 
if (v_isShared_3476_ == 0)
{
v___x_3478_ = v___x_3475_;
goto v_reusejp_3477_;
}
else
{
lean_object* v_reuseFailAlloc_3479_; 
v_reuseFailAlloc_3479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3479_, 0, v_a_3473_);
v___x_3478_ = v_reuseFailAlloc_3479_;
goto v_reusejp_3477_;
}
v_reusejp_3477_:
{
return v___x_3478_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg___boxed(lean_object* v___x_3481_, lean_object* v_xs_3482_, lean_object* v_sz_3483_, lean_object* v_i_3484_, lean_object* v_bs_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_){
_start:
{
size_t v_sz_boxed_3491_; size_t v_i_boxed_3492_; lean_object* v_res_3493_; 
v_sz_boxed_3491_ = lean_unbox_usize(v_sz_3483_);
lean_dec(v_sz_3483_);
v_i_boxed_3492_ = lean_unbox_usize(v_i_3484_);
lean_dec(v_i_3484_);
v_res_3493_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg(v___x_3481_, v_xs_3482_, v_sz_boxed_3491_, v_i_boxed_3492_, v_bs_3485_, v___y_3486_, v___y_3487_, v___y_3488_, v___y_3489_);
lean_dec(v___y_3489_);
lean_dec_ref(v___y_3488_);
lean_dec(v___y_3487_);
lean_dec_ref(v___y_3486_);
lean_dec_ref(v___x_3481_);
return v_res_3493_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__2(lean_object* v_a_3494_, lean_object* v_perms_3495_, size_t v___x_3496_, lean_object* v_fnNames_3497_, lean_object* v_a_3498_, lean_object* v_termMeasure_x3fs_3499_, lean_object* v_xs_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_){
_start:
{
size_t v_sz_3506_; lean_object* v___x_3507_; 
v_sz_3506_ = lean_array_size(v_a_3494_);
lean_inc_ref(v_a_3494_);
lean_inc_ref(v_xs_3500_);
v___x_3507_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg(v_perms_3495_, v_xs_3500_, v_sz_3506_, v___x_3496_, v_a_3494_, v___y_3501_, v___y_3502_, v___y_3503_, v___y_3504_);
if (lean_obj_tag(v___x_3507_) == 0)
{
lean_object* v_a_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; 
v_a_3508_ = lean_ctor_get(v___x_3507_, 0);
lean_inc_n(v_a_3508_, 2);
lean_dec_ref_known(v___x_3507_, 1);
lean_inc_ref(v_xs_3500_);
lean_inc_ref(v_a_3498_);
lean_inc_ref(v_fnNames_3497_);
v___x_3509_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_findRecArgCandidates___boxed), 10, 5);
lean_closure_set(v___x_3509_, 0, v_fnNames_3497_);
lean_closure_set(v___x_3509_, 1, v_a_3498_);
lean_closure_set(v___x_3509_, 2, v_xs_3500_);
lean_closure_set(v___x_3509_, 3, v_a_3508_);
lean_closure_set(v___x_3509_, 4, v_termMeasure_x3fs_3499_);
lean_inc_ref(v_a_3494_);
v___x_3510_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v_a_3494_, v___x_3509_, v___y_3501_, v___y_3502_, v___y_3503_, v___y_3504_);
if (lean_obj_tag(v___x_3510_) == 0)
{
lean_object* v_a_3511_; lean_object* v___x_3512_; lean_object* v___f_3513_; lean_object* v___x_3514_; 
v_a_3511_ = lean_ctor_get(v___x_3510_, 0);
lean_inc(v_a_3511_);
lean_dec_ref_known(v___x_3510_, 1);
v___x_3512_ = lean_box_usize(v___x_3496_);
lean_inc_ref(v_xs_3500_);
v___f_3513_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___boxed), 10, 4);
lean_closure_set(v___f_3513_, 0, v___x_3512_);
lean_closure_set(v___f_3513_, 1, v_a_3498_);
lean_closure_set(v___f_3513_, 2, v_xs_3500_);
lean_closure_set(v___f_3513_, 3, v_a_3494_);
v___x_3514_ = l_Lean_Elab_Structural_tryCandidates___redArg(v_fnNames_3497_, v_xs_3500_, v_a_3508_, v_a_3511_, v___f_3513_, v___y_3501_, v___y_3502_, v___y_3503_, v___y_3504_);
lean_dec_ref(v_fnNames_3497_);
return v___x_3514_;
}
else
{
lean_object* v_a_3515_; lean_object* v___x_3517_; uint8_t v_isShared_3518_; uint8_t v_isSharedCheck_3522_; 
lean_dec(v_a_3508_);
lean_dec_ref(v_xs_3500_);
lean_dec_ref(v_a_3498_);
lean_dec_ref(v_fnNames_3497_);
lean_dec_ref(v_a_3494_);
v_a_3515_ = lean_ctor_get(v___x_3510_, 0);
v_isSharedCheck_3522_ = !lean_is_exclusive(v___x_3510_);
if (v_isSharedCheck_3522_ == 0)
{
v___x_3517_ = v___x_3510_;
v_isShared_3518_ = v_isSharedCheck_3522_;
goto v_resetjp_3516_;
}
else
{
lean_inc(v_a_3515_);
lean_dec(v___x_3510_);
v___x_3517_ = lean_box(0);
v_isShared_3518_ = v_isSharedCheck_3522_;
goto v_resetjp_3516_;
}
v_resetjp_3516_:
{
lean_object* v___x_3520_; 
if (v_isShared_3518_ == 0)
{
v___x_3520_ = v___x_3517_;
goto v_reusejp_3519_;
}
else
{
lean_object* v_reuseFailAlloc_3521_; 
v_reuseFailAlloc_3521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3521_, 0, v_a_3515_);
v___x_3520_ = v_reuseFailAlloc_3521_;
goto v_reusejp_3519_;
}
v_reusejp_3519_:
{
return v___x_3520_;
}
}
}
}
else
{
lean_object* v_a_3523_; lean_object* v___x_3525_; uint8_t v_isShared_3526_; uint8_t v_isSharedCheck_3530_; 
lean_dec_ref(v_xs_3500_);
lean_dec_ref(v_termMeasure_x3fs_3499_);
lean_dec_ref(v_a_3498_);
lean_dec_ref(v_fnNames_3497_);
lean_dec_ref(v_a_3494_);
v_a_3523_ = lean_ctor_get(v___x_3507_, 0);
v_isSharedCheck_3530_ = !lean_is_exclusive(v___x_3507_);
if (v_isSharedCheck_3530_ == 0)
{
v___x_3525_ = v___x_3507_;
v_isShared_3526_ = v_isSharedCheck_3530_;
goto v_resetjp_3524_;
}
else
{
lean_inc(v_a_3523_);
lean_dec(v___x_3507_);
v___x_3525_ = lean_box(0);
v_isShared_3526_ = v_isSharedCheck_3530_;
goto v_resetjp_3524_;
}
v_resetjp_3524_:
{
lean_object* v___x_3528_; 
if (v_isShared_3526_ == 0)
{
v___x_3528_ = v___x_3525_;
goto v_reusejp_3527_;
}
else
{
lean_object* v_reuseFailAlloc_3529_; 
v_reuseFailAlloc_3529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3529_, 0, v_a_3523_);
v___x_3528_ = v_reuseFailAlloc_3529_;
goto v_reusejp_3527_;
}
v_reusejp_3527_:
{
return v___x_3528_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__2___boxed(lean_object* v_a_3531_, lean_object* v_perms_3532_, lean_object* v___x_3533_, lean_object* v_fnNames_3534_, lean_object* v_a_3535_, lean_object* v_termMeasure_x3fs_3536_, lean_object* v_xs_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_){
_start:
{
size_t v___x_13392__boxed_3543_; lean_object* v_res_3544_; 
v___x_13392__boxed_3543_ = lean_unbox_usize(v___x_3533_);
lean_dec(v___x_3533_);
v_res_3544_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__2(v_a_3531_, v_perms_3532_, v___x_13392__boxed_3543_, v_fnNames_3534_, v_a_3535_, v_termMeasure_x3fs_3536_, v_xs_3537_, v___y_3538_, v___y_3539_, v___y_3540_, v___y_3541_);
lean_dec(v___y_3541_);
lean_dec_ref(v___y_3540_);
lean_dec(v___y_3539_);
lean_dec_ref(v___y_3538_);
lean_dec_ref(v_perms_3532_);
return v_res_3544_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0(size_t v_sz_3545_, size_t v_i_3546_, lean_object* v_bs_3547_){
_start:
{
uint8_t v___x_3548_; 
v___x_3548_ = lean_usize_dec_lt(v_i_3546_, v_sz_3545_);
if (v___x_3548_ == 0)
{
return v_bs_3547_;
}
else
{
lean_object* v_v_3549_; lean_object* v_declName_3550_; lean_object* v___x_3551_; lean_object* v_bs_x27_3552_; size_t v___x_3553_; size_t v___x_3554_; lean_object* v___x_3555_; 
v_v_3549_ = lean_array_uget_borrowed(v_bs_3547_, v_i_3546_);
v_declName_3550_ = lean_ctor_get(v_v_3549_, 3);
lean_inc(v_declName_3550_);
v___x_3551_ = lean_unsigned_to_nat(0u);
v_bs_x27_3552_ = lean_array_uset(v_bs_3547_, v_i_3546_, v___x_3551_);
v___x_3553_ = ((size_t)1ULL);
v___x_3554_ = lean_usize_add(v_i_3546_, v___x_3553_);
v___x_3555_ = lean_array_uset(v_bs_x27_3552_, v_i_3546_, v_declName_3550_);
v_i_3546_ = v___x_3554_;
v_bs_3547_ = v___x_3555_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0___boxed(lean_object* v_sz_3557_, lean_object* v_i_3558_, lean_object* v_bs_3559_){
_start:
{
size_t v_sz_boxed_3560_; size_t v_i_boxed_3561_; lean_object* v_res_3562_; 
v_sz_boxed_3560_ = lean_unbox_usize(v_sz_3557_);
lean_dec(v_sz_3557_);
v_i_boxed_3561_ = lean_unbox_usize(v_i_3558_);
lean_dec(v_i_3558_);
v_res_3562_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0(v_sz_boxed_3560_, v_i_boxed_3561_, v_bs_3559_);
return v_res_3562_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1___redArg(lean_object* v_fnNames_3563_, lean_object* v_numSectionVars_3564_, size_t v_sz_3565_, size_t v_i_3566_, lean_object* v_bs_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_){
_start:
{
uint8_t v___x_3571_; 
v___x_3571_ = lean_usize_dec_lt(v_i_3566_, v_sz_3565_);
if (v___x_3571_ == 0)
{
lean_object* v___x_3572_; 
lean_dec(v_numSectionVars_3564_);
lean_dec_ref(v_fnNames_3563_);
v___x_3572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3572_, 0, v_bs_3567_);
return v___x_3572_;
}
else
{
lean_object* v_v_3573_; lean_object* v_ref_3574_; uint8_t v_kind_3575_; lean_object* v_levelParams_3576_; lean_object* v_modifiers_3577_; lean_object* v_declName_3578_; lean_object* v_binders_3579_; lean_object* v_numSectionVars_3580_; lean_object* v_type_3581_; lean_object* v_value_3582_; lean_object* v_termination_3583_; lean_object* v___x_3585_; uint8_t v_isShared_3586_; uint8_t v_isSharedCheck_3606_; 
v_v_3573_ = lean_array_uget(v_bs_3567_, v_i_3566_);
v_ref_3574_ = lean_ctor_get(v_v_3573_, 0);
v_kind_3575_ = lean_ctor_get_uint8(v_v_3573_, sizeof(void*)*9);
v_levelParams_3576_ = lean_ctor_get(v_v_3573_, 1);
v_modifiers_3577_ = lean_ctor_get(v_v_3573_, 2);
v_declName_3578_ = lean_ctor_get(v_v_3573_, 3);
v_binders_3579_ = lean_ctor_get(v_v_3573_, 4);
v_numSectionVars_3580_ = lean_ctor_get(v_v_3573_, 5);
v_type_3581_ = lean_ctor_get(v_v_3573_, 6);
v_value_3582_ = lean_ctor_get(v_v_3573_, 7);
v_termination_3583_ = lean_ctor_get(v_v_3573_, 8);
v_isSharedCheck_3606_ = !lean_is_exclusive(v_v_3573_);
if (v_isSharedCheck_3606_ == 0)
{
v___x_3585_ = v_v_3573_;
v_isShared_3586_ = v_isSharedCheck_3606_;
goto v_resetjp_3584_;
}
else
{
lean_inc(v_termination_3583_);
lean_inc(v_value_3582_);
lean_inc(v_type_3581_);
lean_inc(v_numSectionVars_3580_);
lean_inc(v_binders_3579_);
lean_inc(v_declName_3578_);
lean_inc(v_modifiers_3577_);
lean_inc(v_levelParams_3576_);
lean_inc(v_ref_3574_);
lean_dec(v_v_3573_);
v___x_3585_ = lean_box(0);
v_isShared_3586_ = v_isSharedCheck_3606_;
goto v_resetjp_3584_;
}
v_resetjp_3584_:
{
lean_object* v___x_3587_; 
lean_inc(v_numSectionVars_3564_);
lean_inc_ref(v_fnNames_3563_);
v___x_3587_ = l_Lean_Elab_Structural_preprocess(v_value_3582_, v_fnNames_3563_, v_numSectionVars_3564_, v___y_3568_, v___y_3569_);
if (lean_obj_tag(v___x_3587_) == 0)
{
lean_object* v_a_3588_; lean_object* v___x_3589_; lean_object* v_bs_x27_3590_; lean_object* v___x_3592_; 
v_a_3588_ = lean_ctor_get(v___x_3587_, 0);
lean_inc(v_a_3588_);
lean_dec_ref_known(v___x_3587_, 1);
v___x_3589_ = lean_unsigned_to_nat(0u);
v_bs_x27_3590_ = lean_array_uset(v_bs_3567_, v_i_3566_, v___x_3589_);
if (v_isShared_3586_ == 0)
{
lean_ctor_set(v___x_3585_, 7, v_a_3588_);
v___x_3592_ = v___x_3585_;
goto v_reusejp_3591_;
}
else
{
lean_object* v_reuseFailAlloc_3597_; 
v_reuseFailAlloc_3597_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_3597_, 0, v_ref_3574_);
lean_ctor_set(v_reuseFailAlloc_3597_, 1, v_levelParams_3576_);
lean_ctor_set(v_reuseFailAlloc_3597_, 2, v_modifiers_3577_);
lean_ctor_set(v_reuseFailAlloc_3597_, 3, v_declName_3578_);
lean_ctor_set(v_reuseFailAlloc_3597_, 4, v_binders_3579_);
lean_ctor_set(v_reuseFailAlloc_3597_, 5, v_numSectionVars_3580_);
lean_ctor_set(v_reuseFailAlloc_3597_, 6, v_type_3581_);
lean_ctor_set(v_reuseFailAlloc_3597_, 7, v_a_3588_);
lean_ctor_set(v_reuseFailAlloc_3597_, 8, v_termination_3583_);
lean_ctor_set_uint8(v_reuseFailAlloc_3597_, sizeof(void*)*9, v_kind_3575_);
v___x_3592_ = v_reuseFailAlloc_3597_;
goto v_reusejp_3591_;
}
v_reusejp_3591_:
{
size_t v___x_3593_; size_t v___x_3594_; lean_object* v___x_3595_; 
v___x_3593_ = ((size_t)1ULL);
v___x_3594_ = lean_usize_add(v_i_3566_, v___x_3593_);
v___x_3595_ = lean_array_uset(v_bs_x27_3590_, v_i_3566_, v___x_3592_);
v_i_3566_ = v___x_3594_;
v_bs_3567_ = v___x_3595_;
goto _start;
}
}
else
{
lean_object* v_a_3598_; lean_object* v___x_3600_; uint8_t v_isShared_3601_; uint8_t v_isSharedCheck_3605_; 
lean_del_object(v___x_3585_);
lean_dec_ref(v_termination_3583_);
lean_dec_ref(v_type_3581_);
lean_dec(v_numSectionVars_3580_);
lean_dec(v_binders_3579_);
lean_dec(v_declName_3578_);
lean_dec_ref(v_modifiers_3577_);
lean_dec(v_levelParams_3576_);
lean_dec(v_ref_3574_);
lean_dec_ref(v_bs_3567_);
lean_dec(v_numSectionVars_3564_);
lean_dec_ref(v_fnNames_3563_);
v_a_3598_ = lean_ctor_get(v___x_3587_, 0);
v_isSharedCheck_3605_ = !lean_is_exclusive(v___x_3587_);
if (v_isSharedCheck_3605_ == 0)
{
v___x_3600_ = v___x_3587_;
v_isShared_3601_ = v_isSharedCheck_3605_;
goto v_resetjp_3599_;
}
else
{
lean_inc(v_a_3598_);
lean_dec(v___x_3587_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1___redArg___boxed(lean_object* v_fnNames_3607_, lean_object* v_numSectionVars_3608_, lean_object* v_sz_3609_, lean_object* v_i_3610_, lean_object* v_bs_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_){
_start:
{
size_t v_sz_boxed_3615_; size_t v_i_boxed_3616_; lean_object* v_res_3617_; 
v_sz_boxed_3615_ = lean_unbox_usize(v_sz_3609_);
lean_dec(v_sz_3609_);
v_i_boxed_3616_ = lean_unbox_usize(v_i_3610_);
lean_dec(v_i_3610_);
v_res_3617_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1___redArg(v_fnNames_3607_, v_numSectionVars_3608_, v_sz_boxed_3615_, v_i_boxed_3616_, v_bs_3611_, v___y_3612_, v___y_3613_);
lean_dec(v___y_3613_);
lean_dec_ref(v___y_3612_);
return v_res_3617_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1(lean_object* v_fnNames_3618_, lean_object* v_numSectionVars_3619_, size_t v_sz_3620_, size_t v_i_3621_, lean_object* v_bs_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_){
_start:
{
lean_object* v___x_3628_; 
v___x_3628_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1___redArg(v_fnNames_3618_, v_numSectionVars_3619_, v_sz_3620_, v_i_3621_, v_bs_3622_, v___y_3625_, v___y_3626_);
return v___x_3628_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1___boxed(lean_object* v_fnNames_3629_, lean_object* v_numSectionVars_3630_, lean_object* v_sz_3631_, lean_object* v_i_3632_, lean_object* v_bs_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_){
_start:
{
size_t v_sz_boxed_3639_; size_t v_i_boxed_3640_; lean_object* v_res_3641_; 
v_sz_boxed_3639_ = lean_unbox_usize(v_sz_3631_);
lean_dec(v_sz_3631_);
v_i_boxed_3640_ = lean_unbox_usize(v_i_3632_);
lean_dec(v_i_3632_);
v_res_3641_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1(v_fnNames_3629_, v_numSectionVars_3630_, v_sz_boxed_3639_, v_i_boxed_3640_, v_bs_3633_, v___y_3634_, v___y_3635_, v___y_3636_, v___y_3637_);
lean_dec(v___y_3637_);
lean_dec_ref(v___y_3636_);
lean_dec(v___y_3635_);
lean_dec_ref(v___y_3634_);
return v_res_3641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos(lean_object* v_preDefs_3642_, lean_object* v_termMeasure_x3fs_3643_, lean_object* v_a_3644_, lean_object* v_a_3645_, lean_object* v_a_3646_, lean_object* v_a_3647_){
_start:
{
lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v_numSectionVars_3652_; size_t v_sz_3653_; size_t v___x_3654_; lean_object* v_fnNames_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; 
v___x_3649_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_3650_ = lean_unsigned_to_nat(0u);
v___x_3651_ = lean_array_get_borrowed(v___x_3649_, v_preDefs_3642_, v___x_3650_);
v_numSectionVars_3652_ = lean_ctor_get(v___x_3651_, 5);
v_sz_3653_ = lean_array_size(v_preDefs_3642_);
v___x_3654_ = ((size_t)0ULL);
lean_inc_ref_n(v_preDefs_3642_, 2);
v_fnNames_3655_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0(v_sz_3653_, v___x_3654_, v_preDefs_3642_);
v___x_3656_ = lean_box_usize(v_sz_3653_);
v___x_3657_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___boxed__const__1));
lean_inc(v_numSectionVars_3652_);
lean_inc_ref(v_fnNames_3655_);
v___x_3658_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1___boxed), 10, 5);
lean_closure_set(v___x_3658_, 0, v_fnNames_3655_);
lean_closure_set(v___x_3658_, 1, v_numSectionVars_3652_);
lean_closure_set(v___x_3658_, 2, v___x_3656_);
lean_closure_set(v___x_3658_, 3, v___x_3657_);
lean_closure_set(v___x_3658_, 4, v_preDefs_3642_);
v___x_3659_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v_preDefs_3642_, v___x_3658_, v_a_3644_, v_a_3645_, v_a_3646_, v_a_3647_);
if (lean_obj_tag(v___x_3659_) == 0)
{
lean_object* v_a_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; 
v_a_3660_ = lean_ctor_get(v___x_3659_, 0);
lean_inc_n(v_a_3660_, 3);
lean_dec_ref_known(v___x_3659_, 1);
v___x_3661_ = lean_alloc_closure((void*)(l_Lean_Elab_getFixedParamPerms___boxed), 6, 1);
lean_closure_set(v___x_3661_, 0, v_a_3660_);
v___x_3662_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v_a_3660_, v___x_3661_, v_a_3644_, v_a_3645_, v_a_3646_, v_a_3647_);
if (lean_obj_tag(v___x_3662_) == 0)
{
lean_object* v_a_3663_; lean_object* v_perms_3664_; lean_object* v___x_3665_; lean_object* v_type_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___f_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; 
v_a_3663_ = lean_ctor_get(v___x_3662_, 0);
lean_inc(v_a_3663_);
lean_dec_ref_known(v___x_3662_, 1);
v_perms_3664_ = lean_ctor_get(v_a_3663_, 1);
lean_inc_ref_n(v_perms_3664_, 2);
v___x_3665_ = lean_array_get_borrowed(v___x_3649_, v_a_3660_, v___x_3650_);
v_type_3666_ = lean_ctor_get(v___x_3665_, 6);
lean_inc_ref(v_type_3666_);
v___x_3667_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0);
v___x_3668_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___boxed__const__1));
v___f_3669_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__2___boxed), 12, 6);
lean_closure_set(v___f_3669_, 0, v_a_3660_);
lean_closure_set(v___f_3669_, 1, v_perms_3664_);
lean_closure_set(v___f_3669_, 2, v___x_3668_);
lean_closure_set(v___f_3669_, 3, v_fnNames_3655_);
lean_closure_set(v___f_3669_, 4, v_a_3663_);
lean_closure_set(v___f_3669_, 5, v_termMeasure_x3fs_3643_);
v___x_3670_ = lean_array_get(v___x_3667_, v_perms_3664_, v___x_3650_);
lean_dec_ref(v_perms_3664_);
v___x_3671_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg(v___x_3670_, v_type_3666_, v___f_3669_, v_a_3644_, v_a_3645_, v_a_3646_, v_a_3647_);
return v___x_3671_;
}
else
{
lean_object* v_a_3672_; lean_object* v___x_3674_; uint8_t v_isShared_3675_; uint8_t v_isSharedCheck_3679_; 
lean_dec(v_a_3660_);
lean_dec_ref(v_fnNames_3655_);
lean_dec_ref(v_termMeasure_x3fs_3643_);
v_a_3672_ = lean_ctor_get(v___x_3662_, 0);
v_isSharedCheck_3679_ = !lean_is_exclusive(v___x_3662_);
if (v_isSharedCheck_3679_ == 0)
{
v___x_3674_ = v___x_3662_;
v_isShared_3675_ = v_isSharedCheck_3679_;
goto v_resetjp_3673_;
}
else
{
lean_inc(v_a_3672_);
lean_dec(v___x_3662_);
v___x_3674_ = lean_box(0);
v_isShared_3675_ = v_isSharedCheck_3679_;
goto v_resetjp_3673_;
}
v_resetjp_3673_:
{
lean_object* v___x_3677_; 
if (v_isShared_3675_ == 0)
{
v___x_3677_ = v___x_3674_;
goto v_reusejp_3676_;
}
else
{
lean_object* v_reuseFailAlloc_3678_; 
v_reuseFailAlloc_3678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3678_, 0, v_a_3672_);
v___x_3677_ = v_reuseFailAlloc_3678_;
goto v_reusejp_3676_;
}
v_reusejp_3676_:
{
return v___x_3677_;
}
}
}
}
else
{
lean_object* v_a_3680_; lean_object* v___x_3682_; uint8_t v_isShared_3683_; uint8_t v_isSharedCheck_3687_; 
lean_dec_ref(v_fnNames_3655_);
lean_dec_ref(v_termMeasure_x3fs_3643_);
v_a_3680_ = lean_ctor_get(v___x_3659_, 0);
v_isSharedCheck_3687_ = !lean_is_exclusive(v___x_3659_);
if (v_isSharedCheck_3687_ == 0)
{
v___x_3682_ = v___x_3659_;
v_isShared_3683_ = v_isSharedCheck_3687_;
goto v_resetjp_3681_;
}
else
{
lean_inc(v_a_3680_);
lean_dec(v___x_3659_);
v___x_3682_ = lean_box(0);
v_isShared_3683_ = v_isSharedCheck_3687_;
goto v_resetjp_3681_;
}
v_resetjp_3681_:
{
lean_object* v___x_3685_; 
if (v_isShared_3683_ == 0)
{
v___x_3685_ = v___x_3682_;
goto v_reusejp_3684_;
}
else
{
lean_object* v_reuseFailAlloc_3686_; 
v_reuseFailAlloc_3686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3686_, 0, v_a_3680_);
v___x_3685_ = v_reuseFailAlloc_3686_;
goto v_reusejp_3684_;
}
v_reusejp_3684_:
{
return v___x_3685_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___boxed(lean_object* v_preDefs_3688_, lean_object* v_termMeasure_x3fs_3689_, lean_object* v_a_3690_, lean_object* v_a_3691_, lean_object* v_a_3692_, lean_object* v_a_3693_, lean_object* v_a_3694_){
_start:
{
lean_object* v_res_3695_; 
v_res_3695_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos(v_preDefs_3688_, v_termMeasure_x3fs_3689_, v_a_3690_, v_a_3691_, v_a_3692_, v_a_3693_);
lean_dec(v_a_3693_);
lean_dec_ref(v_a_3692_);
lean_dec(v_a_3691_);
lean_dec_ref(v_a_3690_);
return v_res_3695_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4(lean_object* v_fst_3696_, lean_object* v_as_3697_, size_t v_sz_3698_, size_t v_i_3699_, lean_object* v_bs_3700_){
_start:
{
lean_object* v___x_3701_; 
v___x_3701_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg(v_fst_3696_, v_sz_3698_, v_i_3699_, v_bs_3700_);
return v___x_3701_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___boxed(lean_object* v_fst_3702_, lean_object* v_as_3703_, lean_object* v_sz_3704_, lean_object* v_i_3705_, lean_object* v_bs_3706_){
_start:
{
size_t v_sz_boxed_3707_; size_t v_i_boxed_3708_; lean_object* v_res_3709_; 
v_sz_boxed_3707_ = lean_unbox_usize(v_sz_3704_);
lean_dec(v_sz_3704_);
v_i_boxed_3708_ = lean_unbox_usize(v_i_3705_);
lean_dec(v_i_3705_);
v_res_3709_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4(v_fst_3702_, v_as_3703_, v_sz_boxed_3707_, v_i_boxed_3708_, v_bs_3706_);
lean_dec_ref(v_as_3703_);
lean_dec_ref(v_fst_3702_);
return v_res_3709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10(lean_object* v_00_u03b1_3710_, lean_object* v_lctx_3711_, lean_object* v_localInsts_3712_, lean_object* v_x_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_){
_start:
{
lean_object* v___x_3719_; 
v___x_3719_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___redArg(v_lctx_3711_, v_localInsts_3712_, v_x_3713_, v___y_3714_, v___y_3715_, v___y_3716_, v___y_3717_);
return v___x_3719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___boxed(lean_object* v_00_u03b1_3720_, lean_object* v_lctx_3721_, lean_object* v_localInsts_3722_, lean_object* v_x_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_){
_start:
{
lean_object* v_res_3729_; 
v_res_3729_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10(v_00_u03b1_3720_, v_lctx_3721_, v_localInsts_3722_, v_x_3723_, v___y_3724_, v___y_3725_, v___y_3726_, v___y_3727_);
lean_dec(v___y_3727_);
lean_dec_ref(v___y_3726_);
lean_dec(v___y_3725_);
lean_dec_ref(v___y_3724_);
return v_res_3729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9(lean_object* v_00_u03b1_3730_, lean_object* v_fvarIds_3731_, lean_object* v_k_3732_, lean_object* v___y_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_){
_start:
{
lean_object* v___x_3738_; 
v___x_3738_ = l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___redArg(v_fvarIds_3731_, v_k_3732_, v___y_3733_, v___y_3734_, v___y_3735_, v___y_3736_);
return v___x_3738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___boxed(lean_object* v_00_u03b1_3739_, lean_object* v_fvarIds_3740_, lean_object* v_k_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_){
_start:
{
lean_object* v_res_3747_; 
v_res_3747_ = l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9(v_00_u03b1_3739_, v_fvarIds_3740_, v_k_3741_, v___y_3742_, v___y_3743_, v___y_3744_, v___y_3745_);
lean_dec(v___y_3745_);
lean_dec_ref(v___y_3744_);
lean_dec(v___y_3743_);
lean_dec_ref(v___y_3742_);
lean_dec_ref(v_fvarIds_3740_);
return v_res_3747_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__15(lean_object* v_a_3748_){
_start:
{
lean_object* v___x_3749_; 
v___x_3749_ = lean_nat_to_int(v_a_3748_);
return v___x_3749_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12(lean_object* v___x_3750_, lean_object* v_xs_3751_, lean_object* v_as_3752_, size_t v_sz_3753_, size_t v_i_3754_, lean_object* v_bs_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_){
_start:
{
lean_object* v___x_3761_; 
v___x_3761_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg(v___x_3750_, v_xs_3751_, v_sz_3753_, v_i_3754_, v_bs_3755_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_);
return v___x_3761_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___boxed(lean_object* v___x_3762_, lean_object* v_xs_3763_, lean_object* v_as_3764_, lean_object* v_sz_3765_, lean_object* v_i_3766_, lean_object* v_bs_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_){
_start:
{
size_t v_sz_boxed_3773_; size_t v_i_boxed_3774_; lean_object* v_res_3775_; 
v_sz_boxed_3773_ = lean_unbox_usize(v_sz_3765_);
lean_dec(v_sz_3765_);
v_i_boxed_3774_ = lean_unbox_usize(v_i_3766_);
lean_dec(v_i_3766_);
v_res_3775_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12(v___x_3762_, v_xs_3763_, v_as_3764_, v_sz_boxed_3773_, v_i_boxed_3774_, v_bs_3767_, v___y_3768_, v___y_3769_, v___y_3770_, v___y_3771_);
lean_dec(v___y_3771_);
lean_dec_ref(v___y_3770_);
lean_dec(v___y_3769_);
lean_dec_ref(v___y_3768_);
lean_dec_ref(v_as_3764_);
lean_dec_ref(v___x_3762_);
return v_res_3775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure___lam__0(lean_object* v___x_3776_, lean_object* v_recArgPos_3777_, lean_object* v_xs_3778_, lean_object* v_x_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_){
_start:
{
lean_object* v___x_3785_; uint8_t v___x_3786_; uint8_t v___x_3787_; uint8_t v___x_3788_; lean_object* v___x_3789_; 
v___x_3785_ = lean_array_get_borrowed(v___x_3776_, v_xs_3778_, v_recArgPos_3777_);
v___x_3786_ = 0;
v___x_3787_ = 1;
v___x_3788_ = 1;
lean_inc(v___x_3785_);
v___x_3789_ = l_Lean_Meta_mkLambdaFVars(v_xs_3778_, v___x_3785_, v___x_3786_, v___x_3787_, v___x_3786_, v___x_3787_, v___x_3788_, v___y_3780_, v___y_3781_, v___y_3782_, v___y_3783_);
return v___x_3789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure___lam__0___boxed(lean_object* v___x_3790_, lean_object* v_recArgPos_3791_, lean_object* v_xs_3792_, lean_object* v_x_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_){
_start:
{
lean_object* v_res_3799_; 
v_res_3799_ = l_Lean_Elab_Structural_reportTermMeasure___lam__0(v___x_3790_, v_recArgPos_3791_, v_xs_3792_, v_x_3793_, v___y_3794_, v___y_3795_, v___y_3796_, v___y_3797_);
lean_dec(v___y_3797_);
lean_dec_ref(v___y_3796_);
lean_dec(v___y_3795_);
lean_dec_ref(v___y_3794_);
lean_dec_ref(v_x_3793_);
lean_dec_ref(v_xs_3792_);
lean_dec(v_recArgPos_3791_);
lean_dec_ref(v___x_3790_);
return v_res_3799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure___lam__1(lean_object* v_xs_3800_, lean_object* v_x_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_){
_start:
{
lean_object* v___x_3807_; lean_object* v___x_3808_; 
v___x_3807_ = lean_array_get_size(v_xs_3800_);
v___x_3808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3808_, 0, v___x_3807_);
return v___x_3808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure___lam__1___boxed(lean_object* v_xs_3809_, lean_object* v_x_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_){
_start:
{
lean_object* v_res_3816_; 
v_res_3816_ = l_Lean_Elab_Structural_reportTermMeasure___lam__1(v_xs_3809_, v_x_3810_, v___y_3811_, v___y_3812_, v___y_3813_, v___y_3814_);
lean_dec(v___y_3814_);
lean_dec_ref(v___y_3813_);
lean_dec(v___y_3812_);
lean_dec_ref(v___y_3811_);
lean_dec_ref(v_x_3810_);
lean_dec_ref(v_xs_3809_);
return v_res_3816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure(lean_object* v_preDef_3828_, lean_object* v_recArgPos_3829_, lean_object* v_a_3830_, lean_object* v_a_3831_, lean_object* v_a_3832_, lean_object* v_a_3833_){
_start:
{
lean_object* v_termination_3835_; lean_object* v_terminationBy_x3f_x3f_3836_; 
v_termination_3835_ = lean_ctor_get(v_preDef_3828_, 8);
lean_inc_ref(v_termination_3835_);
v_terminationBy_x3f_x3f_3836_ = lean_ctor_get(v_termination_3835_, 1);
lean_inc(v_terminationBy_x3f_x3f_3836_);
if (lean_obj_tag(v_terminationBy_x3f_x3f_3836_) == 1)
{
lean_object* v_value_3837_; lean_object* v_extraParams_3838_; lean_object* v___x_3840_; uint8_t v_isShared_3841_; uint8_t v_isSharedCheck_3890_; 
v_value_3837_ = lean_ctor_get(v_preDef_3828_, 7);
lean_inc_ref(v_value_3837_);
lean_dec_ref(v_preDef_3828_);
v_extraParams_3838_ = lean_ctor_get(v_termination_3835_, 5);
v_isSharedCheck_3890_ = !lean_is_exclusive(v_termination_3835_);
if (v_isSharedCheck_3890_ == 0)
{
lean_object* v_unused_3891_; lean_object* v_unused_3892_; lean_object* v_unused_3893_; lean_object* v_unused_3894_; lean_object* v_unused_3895_; 
v_unused_3891_ = lean_ctor_get(v_termination_3835_, 4);
lean_dec(v_unused_3891_);
v_unused_3892_ = lean_ctor_get(v_termination_3835_, 3);
lean_dec(v_unused_3892_);
v_unused_3893_ = lean_ctor_get(v_termination_3835_, 2);
lean_dec(v_unused_3893_);
v_unused_3894_ = lean_ctor_get(v_termination_3835_, 1);
lean_dec(v_unused_3894_);
v_unused_3895_ = lean_ctor_get(v_termination_3835_, 0);
lean_dec(v_unused_3895_);
v___x_3840_ = v_termination_3835_;
v_isShared_3841_ = v_isSharedCheck_3890_;
goto v_resetjp_3839_;
}
else
{
lean_inc(v_extraParams_3838_);
lean_dec(v_termination_3835_);
v___x_3840_ = lean_box(0);
v_isShared_3841_ = v_isSharedCheck_3890_;
goto v_resetjp_3839_;
}
v_resetjp_3839_:
{
lean_object* v_val_3842_; lean_object* v___x_3843_; lean_object* v___f_3844_; uint8_t v___x_3845_; lean_object* v___x_3846_; 
v_val_3842_ = lean_ctor_get(v_terminationBy_x3f_x3f_3836_, 0);
lean_inc(v_val_3842_);
lean_dec_ref_known(v_terminationBy_x3f_x3f_3836_, 1);
v___x_3843_ = l_Lean_instInhabitedExpr;
v___f_3844_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_reportTermMeasure___lam__0___boxed), 9, 2);
lean_closure_set(v___f_3844_, 0, v___x_3843_);
lean_closure_set(v___f_3844_, 1, v_recArgPos_3829_);
v___x_3845_ = 0;
lean_inc_ref(v_value_3837_);
v___x_3846_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg(v_value_3837_, v___f_3844_, v___x_3845_, v_a_3830_, v_a_3831_, v_a_3832_, v_a_3833_);
if (lean_obj_tag(v___x_3846_) == 0)
{
lean_object* v_a_3847_; lean_object* v___f_3848_; lean_object* v___x_3849_; 
v_a_3847_ = lean_ctor_get(v___x_3846_, 0);
lean_inc(v_a_3847_);
lean_dec_ref_known(v___x_3846_, 1);
v___f_3848_ = ((lean_object*)(l_Lean_Elab_Structural_reportTermMeasure___closed__0));
v___x_3849_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg(v_value_3837_, v___f_3848_, v___x_3845_, v_a_3830_, v_a_3831_, v_a_3832_, v_a_3833_);
if (lean_obj_tag(v___x_3849_) == 0)
{
lean_object* v_a_3850_; lean_object* v___x_3851_; uint8_t v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; 
v_a_3850_ = lean_ctor_get(v___x_3849_, 0);
lean_inc(v_a_3850_);
lean_dec_ref_known(v___x_3849_, 1);
v___x_3851_ = lean_box(0);
v___x_3852_ = 1;
v___x_3853_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3853_, 0, v___x_3851_);
lean_ctor_set(v___x_3853_, 1, v_a_3847_);
lean_ctor_set_uint8(v___x_3853_, sizeof(void*)*2, v___x_3852_);
v___x_3854_ = l_Lean_Elab_TerminationMeasure_delab(v_a_3850_, v_extraParams_3838_, v___x_3853_, v_a_3830_, v_a_3831_, v_a_3832_, v_a_3833_);
lean_dec(v_a_3850_);
if (lean_obj_tag(v___x_3854_) == 0)
{
lean_object* v_a_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3860_; 
v_a_3855_ = lean_ctor_get(v___x_3854_, 0);
lean_inc(v_a_3855_);
lean_dec_ref_known(v___x_3854_, 1);
v___x_3856_ = ((lean_object*)(l_Lean_Elab_Structural_reportTermMeasure___closed__5));
v___x_3857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3857_, 0, v___x_3856_);
lean_ctor_set(v___x_3857_, 1, v_a_3855_);
v___x_3858_ = lean_box(0);
if (v_isShared_3841_ == 0)
{
lean_ctor_set(v___x_3840_, 5, v___x_3858_);
lean_ctor_set(v___x_3840_, 4, v___x_3858_);
lean_ctor_set(v___x_3840_, 3, v___x_3858_);
lean_ctor_set(v___x_3840_, 2, v___x_3858_);
lean_ctor_set(v___x_3840_, 1, v___x_3858_);
lean_ctor_set(v___x_3840_, 0, v___x_3857_);
v___x_3860_ = v___x_3840_;
goto v_reusejp_3859_;
}
else
{
lean_object* v_reuseFailAlloc_3865_; 
v_reuseFailAlloc_3865_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3865_, 0, v___x_3857_);
lean_ctor_set(v_reuseFailAlloc_3865_, 1, v___x_3858_);
lean_ctor_set(v_reuseFailAlloc_3865_, 2, v___x_3858_);
lean_ctor_set(v_reuseFailAlloc_3865_, 3, v___x_3858_);
lean_ctor_set(v_reuseFailAlloc_3865_, 4, v___x_3858_);
lean_ctor_set(v_reuseFailAlloc_3865_, 5, v___x_3858_);
v___x_3860_ = v_reuseFailAlloc_3865_;
goto v_reusejp_3859_;
}
v_reusejp_3859_:
{
lean_object* v___x_3861_; uint8_t v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; 
v___x_3861_ = ((lean_object*)(l_Lean_Elab_Structural_reportTermMeasure___closed__6));
v___x_3862_ = 4;
v___x_3863_ = l_Lean_MessageData_nil;
v___x_3864_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_val_3842_, v___x_3860_, v___x_3858_, v___x_3861_, v___x_3858_, v___x_3862_, v___x_3863_, v_a_3832_, v_a_3833_);
return v___x_3864_;
}
}
else
{
lean_object* v_a_3866_; lean_object* v___x_3868_; uint8_t v_isShared_3869_; uint8_t v_isSharedCheck_3873_; 
lean_dec(v_val_3842_);
lean_del_object(v___x_3840_);
v_a_3866_ = lean_ctor_get(v___x_3854_, 0);
v_isSharedCheck_3873_ = !lean_is_exclusive(v___x_3854_);
if (v_isSharedCheck_3873_ == 0)
{
v___x_3868_ = v___x_3854_;
v_isShared_3869_ = v_isSharedCheck_3873_;
goto v_resetjp_3867_;
}
else
{
lean_inc(v_a_3866_);
lean_dec(v___x_3854_);
v___x_3868_ = lean_box(0);
v_isShared_3869_ = v_isSharedCheck_3873_;
goto v_resetjp_3867_;
}
v_resetjp_3867_:
{
lean_object* v___x_3871_; 
if (v_isShared_3869_ == 0)
{
v___x_3871_ = v___x_3868_;
goto v_reusejp_3870_;
}
else
{
lean_object* v_reuseFailAlloc_3872_; 
v_reuseFailAlloc_3872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3872_, 0, v_a_3866_);
v___x_3871_ = v_reuseFailAlloc_3872_;
goto v_reusejp_3870_;
}
v_reusejp_3870_:
{
return v___x_3871_;
}
}
}
}
else
{
lean_object* v_a_3874_; lean_object* v___x_3876_; uint8_t v_isShared_3877_; uint8_t v_isSharedCheck_3881_; 
lean_dec(v_a_3847_);
lean_dec(v_val_3842_);
lean_del_object(v___x_3840_);
lean_dec(v_extraParams_3838_);
v_a_3874_ = lean_ctor_get(v___x_3849_, 0);
v_isSharedCheck_3881_ = !lean_is_exclusive(v___x_3849_);
if (v_isSharedCheck_3881_ == 0)
{
v___x_3876_ = v___x_3849_;
v_isShared_3877_ = v_isSharedCheck_3881_;
goto v_resetjp_3875_;
}
else
{
lean_inc(v_a_3874_);
lean_dec(v___x_3849_);
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
lean_dec(v_val_3842_);
lean_del_object(v___x_3840_);
lean_dec(v_extraParams_3838_);
lean_dec_ref(v_value_3837_);
v_a_3882_ = lean_ctor_get(v___x_3846_, 0);
v_isSharedCheck_3889_ = !lean_is_exclusive(v___x_3846_);
if (v_isSharedCheck_3889_ == 0)
{
v___x_3884_ = v___x_3846_;
v_isShared_3885_ = v_isSharedCheck_3889_;
goto v_resetjp_3883_;
}
else
{
lean_inc(v_a_3882_);
lean_dec(v___x_3846_);
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
}
else
{
lean_object* v___x_3896_; lean_object* v___x_3897_; 
lean_dec(v_terminationBy_x3f_x3f_3836_);
lean_dec_ref(v_termination_3835_);
lean_dec(v_recArgPos_3829_);
lean_dec_ref(v_preDef_3828_);
v___x_3896_ = lean_box(0);
v___x_3897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3897_, 0, v___x_3896_);
return v___x_3897_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure___boxed(lean_object* v_preDef_3898_, lean_object* v_recArgPos_3899_, lean_object* v_a_3900_, lean_object* v_a_3901_, lean_object* v_a_3902_, lean_object* v_a_3903_, lean_object* v_a_3904_){
_start:
{
lean_object* v_res_3905_; 
v_res_3905_ = l_Lean_Elab_Structural_reportTermMeasure(v_preDef_3898_, v_recArgPos_3899_, v_a_3900_, v_a_3901_, v_a_3902_, v_a_3903_);
lean_dec(v_a_3903_);
lean_dec_ref(v_a_3902_);
lean_dec(v_a_3901_);
lean_dec_ref(v_a_3900_);
return v_res_3905_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___redArg(lean_object* v_as_3906_, size_t v_sz_3907_, size_t v_i_3908_, lean_object* v_b_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_){
_start:
{
uint8_t v___x_3915_; 
v___x_3915_ = lean_usize_dec_lt(v_i_3908_, v_sz_3907_);
if (v___x_3915_ == 0)
{
lean_object* v___x_3916_; 
v___x_3916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3916_, 0, v_b_3909_);
return v___x_3916_;
}
else
{
lean_object* v_a_3917_; lean_object* v_declName_3918_; lean_object* v___x_3919_; 
v_a_3917_ = lean_array_uget_borrowed(v_as_3906_, v_i_3908_);
v_declName_3918_ = lean_ctor_get(v_a_3917_, 3);
lean_inc(v_declName_3918_);
v___x_3919_ = l_Lean_Meta_saveEqnAffectingOptions(v_declName_3918_, v___y_3910_, v___y_3911_, v___y_3912_, v___y_3913_);
if (lean_obj_tag(v___x_3919_) == 0)
{
lean_object* v___x_3920_; size_t v___x_3921_; size_t v___x_3922_; 
lean_dec_ref_known(v___x_3919_, 1);
v___x_3920_ = lean_box(0);
v___x_3921_ = ((size_t)1ULL);
v___x_3922_ = lean_usize_add(v_i_3908_, v___x_3921_);
v_i_3908_ = v___x_3922_;
v_b_3909_ = v___x_3920_;
goto _start;
}
else
{
return v___x_3919_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___redArg___boxed(lean_object* v_as_3924_, lean_object* v_sz_3925_, lean_object* v_i_3926_, lean_object* v_b_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_){
_start:
{
size_t v_sz_boxed_3933_; size_t v_i_boxed_3934_; lean_object* v_res_3935_; 
v_sz_boxed_3933_ = lean_unbox_usize(v_sz_3925_);
lean_dec(v_sz_3925_);
v_i_boxed_3934_ = lean_unbox_usize(v_i_3926_);
lean_dec(v_i_3926_);
v_res_3935_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___redArg(v_as_3924_, v_sz_boxed_3933_, v_i_boxed_3934_, v_b_3927_, v___y_3928_, v___y_3929_, v___y_3930_, v___y_3931_);
lean_dec(v___y_3931_);
lean_dec_ref(v___y_3930_);
lean_dec(v___y_3929_);
lean_dec_ref(v___y_3928_);
lean_dec_ref(v_as_3924_);
return v_res_3935_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__1(lean_object* v_docCtx_3936_, lean_object* v_a_3937_, lean_object* v_snd_3938_, lean_object* v_as_3939_, size_t v_sz_3940_, size_t v_i_3941_, lean_object* v_b_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_){
_start:
{
uint8_t v___x_3950_; 
v___x_3950_ = lean_usize_dec_lt(v_i_3941_, v_sz_3940_);
if (v___x_3950_ == 0)
{
lean_object* v___x_3951_; 
lean_dec_ref(v_snd_3938_);
lean_dec_ref(v_a_3937_);
lean_dec_ref(v_docCtx_3936_);
v___x_3951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3951_, 0, v_b_3942_);
return v___x_3951_;
}
else
{
lean_object* v_array_3952_; lean_object* v_start_3953_; lean_object* v_stop_3954_; uint8_t v___x_3955_; 
v_array_3952_ = lean_ctor_get(v_b_3942_, 0);
v_start_3953_ = lean_ctor_get(v_b_3942_, 1);
v_stop_3954_ = lean_ctor_get(v_b_3942_, 2);
v___x_3955_ = lean_nat_dec_lt(v_start_3953_, v_stop_3954_);
if (v___x_3955_ == 0)
{
lean_object* v___x_3956_; 
lean_dec_ref(v_snd_3938_);
lean_dec_ref(v_a_3937_);
lean_dec_ref(v_docCtx_3936_);
v___x_3956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3956_, 0, v_b_3942_);
return v___x_3956_;
}
else
{
lean_object* v___x_3958_; uint8_t v_isShared_3959_; uint8_t v_isSharedCheck_4023_; 
lean_inc(v_stop_3954_);
lean_inc(v_start_3953_);
lean_inc_ref(v_array_3952_);
v_isSharedCheck_4023_ = !lean_is_exclusive(v_b_3942_);
if (v_isSharedCheck_4023_ == 0)
{
lean_object* v_unused_4024_; lean_object* v_unused_4025_; lean_object* v_unused_4026_; 
v_unused_4024_ = lean_ctor_get(v_b_3942_, 2);
lean_dec(v_unused_4024_);
v_unused_4025_ = lean_ctor_get(v_b_3942_, 1);
lean_dec(v_unused_4025_);
v_unused_4026_ = lean_ctor_get(v_b_3942_, 0);
lean_dec(v_unused_4026_);
v___x_3958_ = v_b_3942_;
v_isShared_3959_ = v_isSharedCheck_4023_;
goto v_resetjp_3957_;
}
else
{
lean_dec(v_b_3942_);
v___x_3958_ = lean_box(0);
v_isShared_3959_ = v_isSharedCheck_4023_;
goto v_resetjp_3957_;
}
v_resetjp_3957_:
{
lean_object* v_a_3960_; uint8_t v_kind_3961_; lean_object* v_type_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3967_; 
v_a_3960_ = lean_array_uget_borrowed(v_as_3939_, v_i_3941_);
v_kind_3961_ = lean_ctor_get_uint8(v_a_3960_, sizeof(void*)*9);
v_type_3962_ = lean_ctor_get(v_a_3960_, 6);
v___x_3963_ = lean_array_fget(v_array_3952_, v_start_3953_);
v___x_3964_ = lean_unsigned_to_nat(1u);
v___x_3965_ = lean_nat_add(v_start_3953_, v___x_3964_);
lean_dec(v_start_3953_);
if (v_isShared_3959_ == 0)
{
lean_ctor_set(v___x_3958_, 1, v___x_3965_);
v___x_3967_ = v___x_3958_;
goto v_reusejp_3966_;
}
else
{
lean_object* v_reuseFailAlloc_4022_; 
v_reuseFailAlloc_4022_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4022_, 0, v_array_3952_);
lean_ctor_set(v_reuseFailAlloc_4022_, 1, v___x_3965_);
lean_ctor_set(v_reuseFailAlloc_4022_, 2, v_stop_3954_);
v___x_3967_ = v_reuseFailAlloc_4022_;
goto v_reusejp_3966_;
}
v_reusejp_3966_:
{
lean_object* v_preDef_3969_; lean_object* v___y_3970_; lean_object* v___y_3971_; lean_object* v___y_3972_; lean_object* v___y_3973_; lean_object* v___y_3974_; lean_object* v___y_3975_; uint8_t v___x_3988_; 
v___x_3988_ = l_Lean_Elab_DefKind_isTheorem(v_kind_3961_);
if (v___x_3988_ == 0)
{
lean_object* v___x_3989_; 
lean_inc_ref(v_type_3962_);
v___x_3989_ = l_Lean_Meta_isProp(v_type_3962_, v___y_3945_, v___y_3946_, v___y_3947_, v___y_3948_);
if (lean_obj_tag(v___x_3989_) == 0)
{
lean_object* v_a_3990_; uint8_t v___x_3991_; 
v_a_3990_ = lean_ctor_get(v___x_3989_, 0);
lean_inc(v_a_3990_);
lean_dec_ref_known(v___x_3989_, 1);
v___x_3991_ = lean_unbox(v_a_3990_);
lean_dec(v_a_3990_);
if (v___x_3991_ == 0)
{
lean_object* v___x_3992_; 
lean_inc(v_a_3960_);
v___x_3992_ = l_Lean_Elab_abstractNestedProofs(v_a_3960_, v___x_3955_, v___y_3945_, v___y_3946_, v___y_3947_, v___y_3948_);
if (lean_obj_tag(v___x_3992_) == 0)
{
lean_object* v_a_3993_; size_t v_sz_3994_; size_t v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; 
v_a_3993_ = lean_ctor_get(v___x_3992_, 0);
lean_inc_n(v_a_3993_, 2);
lean_dec_ref_known(v___x_3992_, 1);
v_sz_3994_ = lean_array_size(v_a_3937_);
v___x_3995_ = ((size_t)0ULL);
lean_inc_ref(v_a_3937_);
v___x_3996_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0(v_sz_3994_, v___x_3995_, v_a_3937_);
lean_inc_ref(v_snd_3938_);
lean_inc(v___x_3963_);
v___x_3997_ = l_Lean_Elab_Structural_registerEqnsInfo(v_a_3993_, v___x_3996_, v___x_3963_, v_snd_3938_, v___y_3947_, v___y_3948_);
if (lean_obj_tag(v___x_3997_) == 0)
{
lean_dec_ref_known(v___x_3997_, 1);
v_preDef_3969_ = v_a_3993_;
v___y_3970_ = v___y_3943_;
v___y_3971_ = v___y_3944_;
v___y_3972_ = v___y_3945_;
v___y_3973_ = v___y_3946_;
v___y_3974_ = v___y_3947_;
v___y_3975_ = v___y_3948_;
goto v___jp_3968_;
}
else
{
lean_object* v_a_3998_; lean_object* v___x_4000_; uint8_t v_isShared_4001_; uint8_t v_isSharedCheck_4005_; 
lean_dec(v_a_3993_);
lean_dec_ref(v___x_3967_);
lean_dec(v___x_3963_);
lean_dec_ref(v_snd_3938_);
lean_dec_ref(v_a_3937_);
lean_dec_ref(v_docCtx_3936_);
v_a_3998_ = lean_ctor_get(v___x_3997_, 0);
v_isSharedCheck_4005_ = !lean_is_exclusive(v___x_3997_);
if (v_isSharedCheck_4005_ == 0)
{
v___x_4000_ = v___x_3997_;
v_isShared_4001_ = v_isSharedCheck_4005_;
goto v_resetjp_3999_;
}
else
{
lean_inc(v_a_3998_);
lean_dec(v___x_3997_);
v___x_4000_ = lean_box(0);
v_isShared_4001_ = v_isSharedCheck_4005_;
goto v_resetjp_3999_;
}
v_resetjp_3999_:
{
lean_object* v___x_4003_; 
if (v_isShared_4001_ == 0)
{
v___x_4003_ = v___x_4000_;
goto v_reusejp_4002_;
}
else
{
lean_object* v_reuseFailAlloc_4004_; 
v_reuseFailAlloc_4004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4004_, 0, v_a_3998_);
v___x_4003_ = v_reuseFailAlloc_4004_;
goto v_reusejp_4002_;
}
v_reusejp_4002_:
{
return v___x_4003_;
}
}
}
}
else
{
lean_object* v_a_4006_; lean_object* v___x_4008_; uint8_t v_isShared_4009_; uint8_t v_isSharedCheck_4013_; 
lean_dec_ref(v___x_3967_);
lean_dec(v___x_3963_);
lean_dec_ref(v_snd_3938_);
lean_dec_ref(v_a_3937_);
lean_dec_ref(v_docCtx_3936_);
v_a_4006_ = lean_ctor_get(v___x_3992_, 0);
v_isSharedCheck_4013_ = !lean_is_exclusive(v___x_3992_);
if (v_isSharedCheck_4013_ == 0)
{
v___x_4008_ = v___x_3992_;
v_isShared_4009_ = v_isSharedCheck_4013_;
goto v_resetjp_4007_;
}
else
{
lean_inc(v_a_4006_);
lean_dec(v___x_3992_);
v___x_4008_ = lean_box(0);
v_isShared_4009_ = v_isSharedCheck_4013_;
goto v_resetjp_4007_;
}
v_resetjp_4007_:
{
lean_object* v___x_4011_; 
if (v_isShared_4009_ == 0)
{
v___x_4011_ = v___x_4008_;
goto v_reusejp_4010_;
}
else
{
lean_object* v_reuseFailAlloc_4012_; 
v_reuseFailAlloc_4012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4012_, 0, v_a_4006_);
v___x_4011_ = v_reuseFailAlloc_4012_;
goto v_reusejp_4010_;
}
v_reusejp_4010_:
{
return v___x_4011_;
}
}
}
}
else
{
lean_inc(v_a_3960_);
v_preDef_3969_ = v_a_3960_;
v___y_3970_ = v___y_3943_;
v___y_3971_ = v___y_3944_;
v___y_3972_ = v___y_3945_;
v___y_3973_ = v___y_3946_;
v___y_3974_ = v___y_3947_;
v___y_3975_ = v___y_3948_;
goto v___jp_3968_;
}
}
else
{
lean_object* v_a_4014_; lean_object* v___x_4016_; uint8_t v_isShared_4017_; uint8_t v_isSharedCheck_4021_; 
lean_dec_ref(v___x_3967_);
lean_dec(v___x_3963_);
lean_dec_ref(v_snd_3938_);
lean_dec_ref(v_a_3937_);
lean_dec_ref(v_docCtx_3936_);
v_a_4014_ = lean_ctor_get(v___x_3989_, 0);
v_isSharedCheck_4021_ = !lean_is_exclusive(v___x_3989_);
if (v_isSharedCheck_4021_ == 0)
{
v___x_4016_ = v___x_3989_;
v_isShared_4017_ = v_isSharedCheck_4021_;
goto v_resetjp_4015_;
}
else
{
lean_inc(v_a_4014_);
lean_dec(v___x_3989_);
v___x_4016_ = lean_box(0);
v_isShared_4017_ = v_isSharedCheck_4021_;
goto v_resetjp_4015_;
}
v_resetjp_4015_:
{
lean_object* v___x_4019_; 
if (v_isShared_4017_ == 0)
{
v___x_4019_ = v___x_4016_;
goto v_reusejp_4018_;
}
else
{
lean_object* v_reuseFailAlloc_4020_; 
v_reuseFailAlloc_4020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4020_, 0, v_a_4014_);
v___x_4019_ = v_reuseFailAlloc_4020_;
goto v_reusejp_4018_;
}
v_reusejp_4018_:
{
return v___x_4019_;
}
}
}
}
else
{
lean_inc(v_a_3960_);
v_preDef_3969_ = v_a_3960_;
v___y_3970_ = v___y_3943_;
v___y_3971_ = v___y_3944_;
v___y_3972_ = v___y_3945_;
v___y_3973_ = v___y_3946_;
v___y_3974_ = v___y_3947_;
v___y_3975_ = v___y_3948_;
goto v___jp_3968_;
}
v___jp_3968_:
{
lean_object* v___x_3976_; 
lean_inc_ref(v_docCtx_3936_);
v___x_3976_ = l_Lean_Elab_Structural_addSmartUnfoldingDef(v_docCtx_3936_, v_preDef_3969_, v___x_3963_, v___y_3970_, v___y_3971_, v___y_3972_, v___y_3973_, v___y_3974_, v___y_3975_);
if (lean_obj_tag(v___x_3976_) == 0)
{
size_t v___x_3977_; size_t v___x_3978_; 
lean_dec_ref_known(v___x_3976_, 1);
v___x_3977_ = ((size_t)1ULL);
v___x_3978_ = lean_usize_add(v_i_3941_, v___x_3977_);
v_i_3941_ = v___x_3978_;
v_b_3942_ = v___x_3967_;
goto _start;
}
else
{
lean_object* v_a_3980_; lean_object* v___x_3982_; uint8_t v_isShared_3983_; uint8_t v_isSharedCheck_3987_; 
lean_dec_ref(v___x_3967_);
lean_dec_ref(v_snd_3938_);
lean_dec_ref(v_a_3937_);
lean_dec_ref(v_docCtx_3936_);
v_a_3980_ = lean_ctor_get(v___x_3976_, 0);
v_isSharedCheck_3987_ = !lean_is_exclusive(v___x_3976_);
if (v_isSharedCheck_3987_ == 0)
{
v___x_3982_ = v___x_3976_;
v_isShared_3983_ = v_isSharedCheck_3987_;
goto v_resetjp_3981_;
}
else
{
lean_inc(v_a_3980_);
lean_dec(v___x_3976_);
v___x_3982_ = lean_box(0);
v_isShared_3983_ = v_isSharedCheck_3987_;
goto v_resetjp_3981_;
}
v_resetjp_3981_:
{
lean_object* v___x_3985_; 
if (v_isShared_3983_ == 0)
{
v___x_3985_ = v___x_3982_;
goto v_reusejp_3984_;
}
else
{
lean_object* v_reuseFailAlloc_3986_; 
v_reuseFailAlloc_3986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3986_, 0, v_a_3980_);
v___x_3985_ = v_reuseFailAlloc_3986_;
goto v_reusejp_3984_;
}
v_reusejp_3984_:
{
return v___x_3985_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__1___boxed(lean_object* v_docCtx_4027_, lean_object* v_a_4028_, lean_object* v_snd_4029_, lean_object* v_as_4030_, lean_object* v_sz_4031_, lean_object* v_i_4032_, lean_object* v_b_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_){
_start:
{
size_t v_sz_boxed_4041_; size_t v_i_boxed_4042_; lean_object* v_res_4043_; 
v_sz_boxed_4041_ = lean_unbox_usize(v_sz_4031_);
lean_dec(v_sz_4031_);
v_i_boxed_4042_ = lean_unbox_usize(v_i_4032_);
lean_dec(v_i_4032_);
v_res_4043_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__1(v_docCtx_4027_, v_a_4028_, v_snd_4029_, v_as_4030_, v_sz_boxed_4041_, v_i_boxed_4042_, v_b_4033_, v___y_4034_, v___y_4035_, v___y_4036_, v___y_4037_, v___y_4038_, v___y_4039_);
lean_dec(v___y_4039_);
lean_dec_ref(v___y_4038_);
lean_dec(v___y_4037_);
lean_dec_ref(v___y_4036_);
lean_dec(v___y_4035_);
lean_dec_ref(v___y_4034_);
lean_dec_ref(v_as_4030_);
return v_res_4043_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___lam__0(lean_object* v___x_4044_, lean_object* v_e_4045_){
_start:
{
lean_object* v___x_4046_; lean_object* v___x_4047_; 
v___x_4046_ = l_Lean_indentD(v_e_4045_);
v___x_4047_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4047_, 0, v___x_4044_);
lean_ctor_set(v___x_4047_, 1, v___x_4046_);
return v___x_4047_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___lam__1(lean_object* v_docCtx_4048_, lean_object* v_a_4049_, uint8_t v___x_4050_, lean_object* v___x_4051_, uint8_t v___x_4052_, lean_object* v___y_4053_, lean_object* v___y_4054_, lean_object* v___y_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_){
_start:
{
lean_object* v___x_4060_; 
v___x_4060_ = l_Lean_Elab_addNonRec(v_docCtx_4048_, v_a_4049_, v___x_4050_, v___x_4051_, v___x_4052_, v___x_4050_, v___x_4052_, v___y_4053_, v___y_4054_, v___y_4055_, v___y_4056_, v___y_4057_, v___y_4058_);
return v___x_4060_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___lam__1___boxed(lean_object* v_docCtx_4061_, lean_object* v_a_4062_, lean_object* v___x_4063_, lean_object* v___x_4064_, lean_object* v___x_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_, lean_object* v___y_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_){
_start:
{
uint8_t v___x_9188__boxed_4073_; uint8_t v___x_9190__boxed_4074_; lean_object* v_res_4075_; 
v___x_9188__boxed_4073_ = lean_unbox(v___x_4063_);
v___x_9190__boxed_4074_ = lean_unbox(v___x_4065_);
v_res_4075_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___lam__1(v_docCtx_4061_, v_a_4062_, v___x_9188__boxed_4073_, v___x_4064_, v___x_9190__boxed_4074_, v___y_4066_, v___y_4067_, v___y_4068_, v___y_4069_, v___y_4070_, v___y_4071_);
lean_dec(v___y_4071_);
lean_dec_ref(v___y_4070_);
lean_dec(v___y_4069_);
lean_dec_ref(v___y_4068_);
lean_dec(v___y_4067_);
lean_dec_ref(v___y_4066_);
return v_res_4075_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__1(void){
_start:
{
lean_object* v___x_4077_; lean_object* v___x_4078_; 
v___x_4077_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__0));
v___x_4078_ = l_Lean_stringToMessageData(v___x_4077_);
return v___x_4078_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__2(void){
_start:
{
lean_object* v___x_4079_; lean_object* v___f_4080_; 
v___x_4079_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__1);
v___f_4080_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___lam__0), 2, 1);
lean_closure_set(v___f_4080_, 0, v___x_4079_);
return v___f_4080_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5(lean_object* v_names_4081_, lean_object* v_docCtx_4082_, lean_object* v_as_4083_, size_t v_i_4084_, size_t v_stop_4085_, lean_object* v_b_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_){
_start:
{
uint8_t v___x_4094_; 
v___x_4094_ = lean_usize_dec_eq(v_i_4084_, v_stop_4085_);
if (v___x_4094_ == 0)
{
lean_object* v___x_4095_; lean_object* v___x_4096_; 
v___x_4095_ = lean_array_uget_borrowed(v_as_4083_, v_i_4084_);
lean_inc(v___x_4095_);
v___x_4096_ = l_Lean_Elab_eraseRecAppSyntax(v___x_4095_, v___y_4091_, v___y_4092_);
if (lean_obj_tag(v___x_4096_) == 0)
{
lean_object* v_a_4097_; lean_object* v___f_4098_; lean_object* v___x_4099_; uint8_t v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___f_4103_; lean_object* v___x_4104_; 
v_a_4097_ = lean_ctor_get(v___x_4096_, 0);
lean_inc(v_a_4097_);
lean_dec_ref_known(v___x_4096_, 1);
v___f_4098_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__2);
lean_inc_ref(v_names_4081_);
v___x_4099_ = lean_array_to_list(v_names_4081_);
v___x_4100_ = 1;
v___x_4101_ = lean_box(v___x_4094_);
v___x_4102_ = lean_box(v___x_4100_);
lean_inc(v___y_4088_);
lean_inc_ref(v___y_4087_);
lean_inc_ref(v_docCtx_4082_);
v___f_4103_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___lam__1___boxed), 12, 7);
lean_closure_set(v___f_4103_, 0, v_docCtx_4082_);
lean_closure_set(v___f_4103_, 1, v_a_4097_);
lean_closure_set(v___f_4103_, 2, v___x_4101_);
lean_closure_set(v___f_4103_, 3, v___x_4099_);
lean_closure_set(v___f_4103_, 4, v___x_4102_);
lean_closure_set(v___f_4103_, 5, v___y_4087_);
lean_closure_set(v___f_4103_, 6, v___y_4088_);
v___x_4104_ = l_Lean_Meta_mapErrorImp___redArg(v___f_4103_, v___f_4098_, v___y_4089_, v___y_4090_, v___y_4091_, v___y_4092_);
if (lean_obj_tag(v___x_4104_) == 0)
{
if (lean_obj_tag(v___x_4104_) == 0)
{
lean_object* v_a_4105_; size_t v___x_4106_; size_t v___x_4107_; 
v_a_4105_ = lean_ctor_get(v___x_4104_, 0);
lean_inc(v_a_4105_);
lean_dec_ref_known(v___x_4104_, 1);
v___x_4106_ = ((size_t)1ULL);
v___x_4107_ = lean_usize_add(v_i_4084_, v___x_4106_);
v_i_4084_ = v___x_4107_;
v_b_4086_ = v_a_4105_;
goto _start;
}
else
{
lean_dec_ref(v_docCtx_4082_);
lean_dec_ref(v_names_4081_);
return v___x_4104_;
}
}
else
{
lean_object* v_a_4109_; lean_object* v___x_4111_; uint8_t v_isShared_4112_; uint8_t v_isSharedCheck_4116_; 
lean_dec_ref(v_docCtx_4082_);
lean_dec_ref(v_names_4081_);
v_a_4109_ = lean_ctor_get(v___x_4104_, 0);
v_isSharedCheck_4116_ = !lean_is_exclusive(v___x_4104_);
if (v_isSharedCheck_4116_ == 0)
{
v___x_4111_ = v___x_4104_;
v_isShared_4112_ = v_isSharedCheck_4116_;
goto v_resetjp_4110_;
}
else
{
lean_inc(v_a_4109_);
lean_dec(v___x_4104_);
v___x_4111_ = lean_box(0);
v_isShared_4112_ = v_isSharedCheck_4116_;
goto v_resetjp_4110_;
}
v_resetjp_4110_:
{
lean_object* v___x_4114_; 
if (v_isShared_4112_ == 0)
{
v___x_4114_ = v___x_4111_;
goto v_reusejp_4113_;
}
else
{
lean_object* v_reuseFailAlloc_4115_; 
v_reuseFailAlloc_4115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4115_, 0, v_a_4109_);
v___x_4114_ = v_reuseFailAlloc_4115_;
goto v_reusejp_4113_;
}
v_reusejp_4113_:
{
return v___x_4114_;
}
}
}
}
else
{
lean_object* v_a_4117_; lean_object* v___x_4119_; uint8_t v_isShared_4120_; uint8_t v_isSharedCheck_4124_; 
lean_dec_ref(v_docCtx_4082_);
lean_dec_ref(v_names_4081_);
v_a_4117_ = lean_ctor_get(v___x_4096_, 0);
v_isSharedCheck_4124_ = !lean_is_exclusive(v___x_4096_);
if (v_isSharedCheck_4124_ == 0)
{
v___x_4119_ = v___x_4096_;
v_isShared_4120_ = v_isSharedCheck_4124_;
goto v_resetjp_4118_;
}
else
{
lean_inc(v_a_4117_);
lean_dec(v___x_4096_);
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
lean_object* v___x_4125_; 
lean_dec_ref(v_docCtx_4082_);
lean_dec_ref(v_names_4081_);
v___x_4125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4125_, 0, v_b_4086_);
return v___x_4125_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___boxed(lean_object* v_names_4126_, lean_object* v_docCtx_4127_, lean_object* v_as_4128_, lean_object* v_i_4129_, lean_object* v_stop_4130_, lean_object* v_b_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_){
_start:
{
size_t v_i_boxed_4139_; size_t v_stop_boxed_4140_; lean_object* v_res_4141_; 
v_i_boxed_4139_ = lean_unbox_usize(v_i_4129_);
lean_dec(v_i_4129_);
v_stop_boxed_4140_ = lean_unbox_usize(v_stop_4130_);
lean_dec(v_stop_4130_);
v_res_4141_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5(v_names_4126_, v_docCtx_4127_, v_as_4128_, v_i_boxed_4139_, v_stop_boxed_4140_, v_b_4131_, v___y_4132_, v___y_4133_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_);
lean_dec(v___y_4137_);
lean_dec_ref(v___y_4136_);
lean_dec(v___y_4135_);
lean_dec_ref(v___y_4134_);
lean_dec(v___y_4133_);
lean_dec_ref(v___y_4132_);
lean_dec_ref(v_as_4128_);
return v_res_4141_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4___redArg(lean_object* v_as_4142_, size_t v_sz_4143_, size_t v_i_4144_, lean_object* v_b_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_){
_start:
{
uint8_t v___x_4151_; 
v___x_4151_ = lean_usize_dec_lt(v_i_4144_, v_sz_4143_);
if (v___x_4151_ == 0)
{
lean_object* v___x_4152_; 
v___x_4152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4152_, 0, v_b_4145_);
return v___x_4152_;
}
else
{
lean_object* v_array_4153_; lean_object* v_start_4154_; lean_object* v_stop_4155_; uint8_t v___x_4156_; 
v_array_4153_ = lean_ctor_get(v_b_4145_, 0);
v_start_4154_ = lean_ctor_get(v_b_4145_, 1);
v_stop_4155_ = lean_ctor_get(v_b_4145_, 2);
v___x_4156_ = lean_nat_dec_lt(v_start_4154_, v_stop_4155_);
if (v___x_4156_ == 0)
{
lean_object* v___x_4157_; 
v___x_4157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4157_, 0, v_b_4145_);
return v___x_4157_;
}
else
{
lean_object* v___x_4159_; uint8_t v_isShared_4160_; uint8_t v_isSharedCheck_4180_; 
lean_inc(v_stop_4155_);
lean_inc(v_start_4154_);
lean_inc_ref(v_array_4153_);
v_isSharedCheck_4180_ = !lean_is_exclusive(v_b_4145_);
if (v_isSharedCheck_4180_ == 0)
{
lean_object* v_unused_4181_; lean_object* v_unused_4182_; lean_object* v_unused_4183_; 
v_unused_4181_ = lean_ctor_get(v_b_4145_, 2);
lean_dec(v_unused_4181_);
v_unused_4182_ = lean_ctor_get(v_b_4145_, 1);
lean_dec(v_unused_4182_);
v_unused_4183_ = lean_ctor_get(v_b_4145_, 0);
lean_dec(v_unused_4183_);
v___x_4159_ = v_b_4145_;
v_isShared_4160_ = v_isSharedCheck_4180_;
goto v_resetjp_4158_;
}
else
{
lean_dec(v_b_4145_);
v___x_4159_ = lean_box(0);
v_isShared_4160_ = v_isSharedCheck_4180_;
goto v_resetjp_4158_;
}
v_resetjp_4158_:
{
lean_object* v_a_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; 
v_a_4161_ = lean_array_uget_borrowed(v_as_4142_, v_i_4144_);
v___x_4162_ = lean_array_fget_borrowed(v_array_4153_, v_start_4154_);
lean_inc(v_a_4161_);
lean_inc(v___x_4162_);
v___x_4163_ = l_Lean_Elab_Structural_reportTermMeasure(v___x_4162_, v_a_4161_, v___y_4146_, v___y_4147_, v___y_4148_, v___y_4149_);
if (lean_obj_tag(v___x_4163_) == 0)
{
lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4167_; 
lean_dec_ref_known(v___x_4163_, 1);
v___x_4164_ = lean_unsigned_to_nat(1u);
v___x_4165_ = lean_nat_add(v_start_4154_, v___x_4164_);
lean_dec(v_start_4154_);
if (v_isShared_4160_ == 0)
{
lean_ctor_set(v___x_4159_, 1, v___x_4165_);
v___x_4167_ = v___x_4159_;
goto v_reusejp_4166_;
}
else
{
lean_object* v_reuseFailAlloc_4171_; 
v_reuseFailAlloc_4171_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4171_, 0, v_array_4153_);
lean_ctor_set(v_reuseFailAlloc_4171_, 1, v___x_4165_);
lean_ctor_set(v_reuseFailAlloc_4171_, 2, v_stop_4155_);
v___x_4167_ = v_reuseFailAlloc_4171_;
goto v_reusejp_4166_;
}
v_reusejp_4166_:
{
size_t v___x_4168_; size_t v___x_4169_; 
v___x_4168_ = ((size_t)1ULL);
v___x_4169_ = lean_usize_add(v_i_4144_, v___x_4168_);
v_i_4144_ = v___x_4169_;
v_b_4145_ = v___x_4167_;
goto _start;
}
}
else
{
lean_object* v_a_4172_; lean_object* v___x_4174_; uint8_t v_isShared_4175_; uint8_t v_isSharedCheck_4179_; 
lean_del_object(v___x_4159_);
lean_dec(v_stop_4155_);
lean_dec(v_start_4154_);
lean_dec_ref(v_array_4153_);
v_a_4172_ = lean_ctor_get(v___x_4163_, 0);
v_isSharedCheck_4179_ = !lean_is_exclusive(v___x_4163_);
if (v_isSharedCheck_4179_ == 0)
{
v___x_4174_ = v___x_4163_;
v_isShared_4175_ = v_isSharedCheck_4179_;
goto v_resetjp_4173_;
}
else
{
lean_inc(v_a_4172_);
lean_dec(v___x_4163_);
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
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4___redArg___boxed(lean_object* v_as_4184_, lean_object* v_sz_4185_, lean_object* v_i_4186_, lean_object* v_b_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_){
_start:
{
size_t v_sz_boxed_4193_; size_t v_i_boxed_4194_; lean_object* v_res_4195_; 
v_sz_boxed_4193_ = lean_unbox_usize(v_sz_4185_);
lean_dec(v_sz_4185_);
v_i_boxed_4194_ = lean_unbox_usize(v_i_4186_);
lean_dec(v_i_4186_);
v_res_4195_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4___redArg(v_as_4184_, v_sz_boxed_4193_, v_i_boxed_4194_, v_b_4187_, v___y_4188_, v___y_4189_, v___y_4190_, v___y_4191_);
lean_dec(v___y_4191_);
lean_dec_ref(v___y_4190_);
lean_dec(v___y_4189_);
lean_dec_ref(v___y_4188_);
lean_dec_ref(v_as_4184_);
return v_res_4195_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___redArg(size_t v_sz_4196_, size_t v_i_4197_, lean_object* v_bs_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_){
_start:
{
uint8_t v___x_4202_; 
v___x_4202_ = lean_usize_dec_lt(v_i_4197_, v_sz_4196_);
if (v___x_4202_ == 0)
{
lean_object* v___x_4203_; 
v___x_4203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4203_, 0, v_bs_4198_);
return v___x_4203_;
}
else
{
lean_object* v_v_4204_; lean_object* v___x_4205_; 
v_v_4204_ = lean_array_uget_borrowed(v_bs_4198_, v_i_4197_);
lean_inc(v_v_4204_);
v___x_4205_ = l_Lean_Elab_eraseRecAppSyntax(v_v_4204_, v___y_4199_, v___y_4200_);
if (lean_obj_tag(v___x_4205_) == 0)
{
lean_object* v_a_4206_; lean_object* v___x_4207_; lean_object* v_bs_x27_4208_; size_t v___x_4209_; size_t v___x_4210_; lean_object* v___x_4211_; 
v_a_4206_ = lean_ctor_get(v___x_4205_, 0);
lean_inc(v_a_4206_);
lean_dec_ref_known(v___x_4205_, 1);
v___x_4207_ = lean_unsigned_to_nat(0u);
v_bs_x27_4208_ = lean_array_uset(v_bs_4198_, v_i_4197_, v___x_4207_);
v___x_4209_ = ((size_t)1ULL);
v___x_4210_ = lean_usize_add(v_i_4197_, v___x_4209_);
v___x_4211_ = lean_array_uset(v_bs_x27_4208_, v_i_4197_, v_a_4206_);
v_i_4197_ = v___x_4210_;
v_bs_4198_ = v___x_4211_;
goto _start;
}
else
{
lean_object* v_a_4213_; lean_object* v___x_4215_; uint8_t v_isShared_4216_; uint8_t v_isSharedCheck_4220_; 
lean_dec_ref(v_bs_4198_);
v_a_4213_ = lean_ctor_get(v___x_4205_, 0);
v_isSharedCheck_4220_ = !lean_is_exclusive(v___x_4205_);
if (v_isSharedCheck_4220_ == 0)
{
v___x_4215_ = v___x_4205_;
v_isShared_4216_ = v_isSharedCheck_4220_;
goto v_resetjp_4214_;
}
else
{
lean_inc(v_a_4213_);
lean_dec(v___x_4205_);
v___x_4215_ = lean_box(0);
v_isShared_4216_ = v_isSharedCheck_4220_;
goto v_resetjp_4214_;
}
v_resetjp_4214_:
{
lean_object* v___x_4218_; 
if (v_isShared_4216_ == 0)
{
v___x_4218_ = v___x_4215_;
goto v_reusejp_4217_;
}
else
{
lean_object* v_reuseFailAlloc_4219_; 
v_reuseFailAlloc_4219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4219_, 0, v_a_4213_);
v___x_4218_ = v_reuseFailAlloc_4219_;
goto v_reusejp_4217_;
}
v_reusejp_4217_:
{
return v___x_4218_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___redArg___boxed(lean_object* v_sz_4221_, lean_object* v_i_4222_, lean_object* v_bs_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_, lean_object* v___y_4226_){
_start:
{
size_t v_sz_boxed_4227_; size_t v_i_boxed_4228_; lean_object* v_res_4229_; 
v_sz_boxed_4227_ = lean_unbox_usize(v_sz_4221_);
lean_dec(v_sz_4221_);
v_i_boxed_4228_ = lean_unbox_usize(v_i_4222_);
lean_dec(v_i_4222_);
v_res_4229_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___redArg(v_sz_boxed_4227_, v_i_boxed_4228_, v_bs_4223_, v___y_4224_, v___y_4225_);
lean_dec(v___y_4225_);
lean_dec_ref(v___y_4224_);
return v_res_4229_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___redArg(lean_object* v_as_4230_, size_t v_sz_4231_, size_t v_i_4232_, lean_object* v_b_4233_, lean_object* v___y_4234_, lean_object* v___y_4235_){
_start:
{
uint8_t v___x_4237_; 
v___x_4237_ = lean_usize_dec_lt(v_i_4232_, v_sz_4231_);
if (v___x_4237_ == 0)
{
lean_object* v___x_4238_; 
v___x_4238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4238_, 0, v_b_4233_);
return v___x_4238_;
}
else
{
lean_object* v_a_4239_; lean_object* v_declName_4240_; lean_object* v___x_4241_; 
v_a_4239_ = lean_array_uget_borrowed(v_as_4230_, v_i_4232_);
v_declName_4240_ = lean_ctor_get(v_a_4239_, 3);
lean_inc(v_declName_4240_);
v___x_4241_ = l_Lean_enableRealizationsForConst(v_declName_4240_, v___y_4234_, v___y_4235_);
if (lean_obj_tag(v___x_4241_) == 0)
{
lean_object* v___x_4242_; size_t v___x_4243_; size_t v___x_4244_; 
lean_dec_ref_known(v___x_4241_, 1);
v___x_4242_ = lean_box(0);
v___x_4243_ = ((size_t)1ULL);
v___x_4244_ = lean_usize_add(v_i_4232_, v___x_4243_);
v_i_4232_ = v___x_4244_;
v_b_4233_ = v___x_4242_;
goto _start;
}
else
{
return v___x_4241_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___redArg___boxed(lean_object* v_as_4246_, lean_object* v_sz_4247_, lean_object* v_i_4248_, lean_object* v_b_4249_, lean_object* v___y_4250_, lean_object* v___y_4251_, lean_object* v___y_4252_){
_start:
{
size_t v_sz_boxed_4253_; size_t v_i_boxed_4254_; lean_object* v_res_4255_; 
v_sz_boxed_4253_ = lean_unbox_usize(v_sz_4247_);
lean_dec(v_sz_4247_);
v_i_boxed_4254_ = lean_unbox_usize(v_i_4248_);
lean_dec(v_i_4248_);
v_res_4255_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___redArg(v_as_4246_, v_sz_boxed_4253_, v_i_boxed_4254_, v_b_4249_, v___y_4250_, v___y_4251_);
lean_dec(v___y_4251_);
lean_dec_ref(v___y_4250_);
lean_dec_ref(v_as_4246_);
return v_res_4255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_structuralRecursion(lean_object* v_docCtx_4256_, lean_object* v_preDefs_4257_, lean_object* v_termMeasure_x3fs_4258_, lean_object* v_a_4259_, lean_object* v_a_4260_, lean_object* v_a_4261_, lean_object* v_a_4262_, lean_object* v_a_4263_, lean_object* v_a_4264_){
_start:
{
size_t v_sz_4266_; size_t v___x_4267_; lean_object* v_names_4268_; lean_object* v___x_4269_; 
v_sz_4266_ = lean_array_size(v_preDefs_4257_);
v___x_4267_ = ((size_t)0ULL);
lean_inc_ref_n(v_preDefs_4257_, 2);
v_names_4268_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0(v_sz_4266_, v___x_4267_, v_preDefs_4257_);
v___x_4269_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos(v_preDefs_4257_, v_termMeasure_x3fs_4258_, v_a_4261_, v_a_4262_, v_a_4263_, v_a_4264_);
if (lean_obj_tag(v___x_4269_) == 0)
{
lean_object* v_a_4270_; lean_object* v_snd_4271_; lean_object* v_fst_4272_; lean_object* v_fst_4273_; lean_object* v_snd_4274_; lean_object* v___y_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; size_t v_sz_4310_; lean_object* v___x_4311_; 
v_a_4270_ = lean_ctor_get(v___x_4269_, 0);
lean_inc(v_a_4270_);
lean_dec_ref_known(v___x_4269_, 1);
v_snd_4271_ = lean_ctor_get(v_a_4270_, 1);
lean_inc(v_snd_4271_);
v_fst_4272_ = lean_ctor_get(v_a_4270_, 0);
lean_inc(v_fst_4272_);
lean_dec(v_a_4270_);
v_fst_4273_ = lean_ctor_get(v_snd_4271_, 0);
lean_inc(v_fst_4273_);
v_snd_4274_ = lean_ctor_get(v_snd_4271_, 1);
lean_inc(v_snd_4274_);
lean_dec(v_snd_4271_);
v___x_4307_ = lean_unsigned_to_nat(0u);
v___x_4308_ = lean_array_get_size(v_preDefs_4257_);
lean_inc_ref(v_preDefs_4257_);
v___x_4309_ = l_Array_toSubarray___redArg(v_preDefs_4257_, v___x_4307_, v___x_4308_);
v_sz_4310_ = lean_array_size(v_fst_4272_);
v___x_4311_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4___redArg(v_fst_4272_, v_sz_4310_, v___x_4267_, v___x_4309_, v_a_4261_, v_a_4262_, v_a_4263_, v_a_4264_);
if (lean_obj_tag(v___x_4311_) == 0)
{
lean_object* v___x_4312_; uint8_t v___x_4313_; 
lean_dec_ref_known(v___x_4311_, 1);
v___x_4312_ = lean_array_get_size(v_fst_4273_);
v___x_4313_ = lean_nat_dec_lt(v___x_4307_, v___x_4312_);
if (v___x_4313_ == 0)
{
lean_dec_ref(v_names_4268_);
goto v___jp_4275_;
}
else
{
lean_object* v___x_4314_; uint8_t v___x_4315_; 
v___x_4314_ = lean_box(0);
v___x_4315_ = lean_nat_dec_le(v___x_4312_, v___x_4312_);
if (v___x_4315_ == 0)
{
if (v___x_4313_ == 0)
{
lean_dec_ref(v_names_4268_);
goto v___jp_4275_;
}
else
{
size_t v___x_4316_; lean_object* v___x_4317_; 
v___x_4316_ = lean_usize_of_nat(v___x_4312_);
lean_inc_ref(v_docCtx_4256_);
v___x_4317_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5(v_names_4268_, v_docCtx_4256_, v_fst_4273_, v___x_4267_, v___x_4316_, v___x_4314_, v_a_4259_, v_a_4260_, v_a_4261_, v_a_4262_, v_a_4263_, v_a_4264_);
v___y_4306_ = v___x_4317_;
goto v___jp_4305_;
}
}
else
{
size_t v___x_4318_; lean_object* v___x_4319_; 
v___x_4318_ = lean_usize_of_nat(v___x_4312_);
lean_inc_ref(v_docCtx_4256_);
v___x_4319_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5(v_names_4268_, v_docCtx_4256_, v_fst_4273_, v___x_4267_, v___x_4318_, v___x_4314_, v_a_4259_, v_a_4260_, v_a_4261_, v_a_4262_, v_a_4263_, v_a_4264_);
v___y_4306_ = v___x_4319_;
goto v___jp_4305_;
}
}
}
else
{
lean_object* v_a_4320_; lean_object* v___x_4322_; uint8_t v_isShared_4323_; uint8_t v_isSharedCheck_4327_; 
lean_dec(v_snd_4274_);
lean_dec(v_fst_4273_);
lean_dec(v_fst_4272_);
lean_dec_ref(v_names_4268_);
lean_dec_ref(v_preDefs_4257_);
lean_dec_ref(v_docCtx_4256_);
v_a_4320_ = lean_ctor_get(v___x_4311_, 0);
v_isSharedCheck_4327_ = !lean_is_exclusive(v___x_4311_);
if (v_isSharedCheck_4327_ == 0)
{
v___x_4322_ = v___x_4311_;
v_isShared_4323_ = v_isSharedCheck_4327_;
goto v_resetjp_4321_;
}
else
{
lean_inc(v_a_4320_);
lean_dec(v___x_4311_);
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
v___jp_4275_:
{
lean_object* v___x_4276_; 
v___x_4276_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___redArg(v_sz_4266_, v___x_4267_, v_preDefs_4257_, v_a_4263_, v_a_4264_);
if (lean_obj_tag(v___x_4276_) == 0)
{
lean_object* v_a_4277_; lean_object* v___x_4278_; 
v_a_4277_ = lean_ctor_get(v___x_4276_, 0);
lean_inc_n(v_a_4277_, 2);
lean_dec_ref_known(v___x_4276_, 1);
lean_inc_ref(v_docCtx_4256_);
v___x_4278_ = l_Lean_Elab_addAndCompilePartialRec(v_docCtx_4256_, v_a_4277_, v_a_4259_, v_a_4260_, v_a_4261_, v_a_4262_, v_a_4263_, v_a_4264_);
if (lean_obj_tag(v___x_4278_) == 0)
{
lean_object* v___x_4279_; lean_object* v___x_4280_; lean_object* v___x_4281_; size_t v_sz_4282_; lean_object* v___x_4283_; 
lean_dec_ref_known(v___x_4278_, 1);
v___x_4279_ = lean_unsigned_to_nat(0u);
v___x_4280_ = lean_array_get_size(v_fst_4272_);
v___x_4281_ = l_Array_toSubarray___redArg(v_fst_4272_, v___x_4279_, v___x_4280_);
v_sz_4282_ = lean_array_size(v_a_4277_);
lean_inc(v_a_4277_);
v___x_4283_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__1(v_docCtx_4256_, v_a_4277_, v_snd_4274_, v_a_4277_, v_sz_4282_, v___x_4267_, v___x_4281_, v_a_4259_, v_a_4260_, v_a_4261_, v_a_4262_, v_a_4263_, v_a_4264_);
if (lean_obj_tag(v___x_4283_) == 0)
{
lean_object* v___x_4284_; lean_object* v___x_4285_; 
lean_dec_ref_known(v___x_4283_, 1);
v___x_4284_ = lean_box(0);
v___x_4285_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___redArg(v_a_4277_, v_sz_4282_, v___x_4267_, v___x_4284_, v_a_4261_, v_a_4262_, v_a_4263_, v_a_4264_);
if (lean_obj_tag(v___x_4285_) == 0)
{
lean_object* v___x_4286_; 
lean_dec_ref_known(v___x_4285_, 1);
v___x_4286_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___redArg(v_a_4277_, v_sz_4282_, v___x_4267_, v___x_4284_, v_a_4263_, v_a_4264_);
lean_dec(v_a_4277_);
if (lean_obj_tag(v___x_4286_) == 0)
{
uint8_t v___x_4287_; lean_object* v___x_4288_; 
lean_dec_ref_known(v___x_4286_, 1);
v___x_4287_ = 1;
v___x_4288_ = l_Lean_Elab_applyAttributesOf(v_fst_4273_, v___x_4287_, v_a_4259_, v_a_4260_, v_a_4261_, v_a_4262_, v_a_4263_, v_a_4264_);
lean_dec(v_fst_4273_);
return v___x_4288_;
}
else
{
lean_dec(v_fst_4273_);
return v___x_4286_;
}
}
else
{
lean_dec(v_a_4277_);
lean_dec(v_fst_4273_);
return v___x_4285_;
}
}
else
{
lean_object* v_a_4289_; lean_object* v___x_4291_; uint8_t v_isShared_4292_; uint8_t v_isSharedCheck_4296_; 
lean_dec(v_a_4277_);
lean_dec(v_fst_4273_);
v_a_4289_ = lean_ctor_get(v___x_4283_, 0);
v_isSharedCheck_4296_ = !lean_is_exclusive(v___x_4283_);
if (v_isSharedCheck_4296_ == 0)
{
v___x_4291_ = v___x_4283_;
v_isShared_4292_ = v_isSharedCheck_4296_;
goto v_resetjp_4290_;
}
else
{
lean_inc(v_a_4289_);
lean_dec(v___x_4283_);
v___x_4291_ = lean_box(0);
v_isShared_4292_ = v_isSharedCheck_4296_;
goto v_resetjp_4290_;
}
v_resetjp_4290_:
{
lean_object* v___x_4294_; 
if (v_isShared_4292_ == 0)
{
v___x_4294_ = v___x_4291_;
goto v_reusejp_4293_;
}
else
{
lean_object* v_reuseFailAlloc_4295_; 
v_reuseFailAlloc_4295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4295_, 0, v_a_4289_);
v___x_4294_ = v_reuseFailAlloc_4295_;
goto v_reusejp_4293_;
}
v_reusejp_4293_:
{
return v___x_4294_;
}
}
}
}
else
{
lean_dec(v_a_4277_);
lean_dec(v_snd_4274_);
lean_dec(v_fst_4273_);
lean_dec(v_fst_4272_);
lean_dec_ref(v_docCtx_4256_);
return v___x_4278_;
}
}
else
{
lean_object* v_a_4297_; lean_object* v___x_4299_; uint8_t v_isShared_4300_; uint8_t v_isSharedCheck_4304_; 
lean_dec(v_snd_4274_);
lean_dec(v_fst_4273_);
lean_dec(v_fst_4272_);
lean_dec_ref(v_docCtx_4256_);
v_a_4297_ = lean_ctor_get(v___x_4276_, 0);
v_isSharedCheck_4304_ = !lean_is_exclusive(v___x_4276_);
if (v_isSharedCheck_4304_ == 0)
{
v___x_4299_ = v___x_4276_;
v_isShared_4300_ = v_isSharedCheck_4304_;
goto v_resetjp_4298_;
}
else
{
lean_inc(v_a_4297_);
lean_dec(v___x_4276_);
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
v___jp_4305_:
{
if (lean_obj_tag(v___y_4306_) == 0)
{
lean_dec_ref_known(v___y_4306_, 1);
goto v___jp_4275_;
}
else
{
lean_dec(v_snd_4274_);
lean_dec(v_fst_4273_);
lean_dec(v_fst_4272_);
lean_dec_ref(v_preDefs_4257_);
lean_dec_ref(v_docCtx_4256_);
return v___y_4306_;
}
}
}
else
{
lean_object* v_a_4328_; lean_object* v___x_4330_; uint8_t v_isShared_4331_; uint8_t v_isSharedCheck_4335_; 
lean_dec_ref(v_names_4268_);
lean_dec_ref(v_preDefs_4257_);
lean_dec_ref(v_docCtx_4256_);
v_a_4328_ = lean_ctor_get(v___x_4269_, 0);
v_isSharedCheck_4335_ = !lean_is_exclusive(v___x_4269_);
if (v_isSharedCheck_4335_ == 0)
{
v___x_4330_ = v___x_4269_;
v_isShared_4331_ = v_isSharedCheck_4335_;
goto v_resetjp_4329_;
}
else
{
lean_inc(v_a_4328_);
lean_dec(v___x_4269_);
v___x_4330_ = lean_box(0);
v_isShared_4331_ = v_isSharedCheck_4335_;
goto v_resetjp_4329_;
}
v_resetjp_4329_:
{
lean_object* v___x_4333_; 
if (v_isShared_4331_ == 0)
{
v___x_4333_ = v___x_4330_;
goto v_reusejp_4332_;
}
else
{
lean_object* v_reuseFailAlloc_4334_; 
v_reuseFailAlloc_4334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4334_, 0, v_a_4328_);
v___x_4333_ = v_reuseFailAlloc_4334_;
goto v_reusejp_4332_;
}
v_reusejp_4332_:
{
return v___x_4333_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_structuralRecursion___boxed(lean_object* v_docCtx_4336_, lean_object* v_preDefs_4337_, lean_object* v_termMeasure_x3fs_4338_, lean_object* v_a_4339_, lean_object* v_a_4340_, lean_object* v_a_4341_, lean_object* v_a_4342_, lean_object* v_a_4343_, lean_object* v_a_4344_, lean_object* v_a_4345_){
_start:
{
lean_object* v_res_4346_; 
v_res_4346_ = l_Lean_Elab_Structural_structuralRecursion(v_docCtx_4336_, v_preDefs_4337_, v_termMeasure_x3fs_4338_, v_a_4339_, v_a_4340_, v_a_4341_, v_a_4342_, v_a_4343_, v_a_4344_);
lean_dec(v_a_4344_);
lean_dec_ref(v_a_4343_);
lean_dec(v_a_4342_);
lean_dec_ref(v_a_4341_);
lean_dec(v_a_4340_);
lean_dec_ref(v_a_4339_);
return v_res_4346_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0(size_t v_sz_4347_, size_t v_i_4348_, lean_object* v_bs_4349_, lean_object* v___y_4350_, lean_object* v___y_4351_, lean_object* v___y_4352_, lean_object* v___y_4353_, lean_object* v___y_4354_, lean_object* v___y_4355_){
_start:
{
lean_object* v___x_4357_; 
v___x_4357_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___redArg(v_sz_4347_, v_i_4348_, v_bs_4349_, v___y_4354_, v___y_4355_);
return v___x_4357_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___boxed(lean_object* v_sz_4358_, lean_object* v_i_4359_, lean_object* v_bs_4360_, lean_object* v___y_4361_, lean_object* v___y_4362_, lean_object* v___y_4363_, lean_object* v___y_4364_, lean_object* v___y_4365_, lean_object* v___y_4366_, lean_object* v___y_4367_){
_start:
{
size_t v_sz_boxed_4368_; size_t v_i_boxed_4369_; lean_object* v_res_4370_; 
v_sz_boxed_4368_ = lean_unbox_usize(v_sz_4358_);
lean_dec(v_sz_4358_);
v_i_boxed_4369_ = lean_unbox_usize(v_i_4359_);
lean_dec(v_i_4359_);
v_res_4370_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0(v_sz_boxed_4368_, v_i_boxed_4369_, v_bs_4360_, v___y_4361_, v___y_4362_, v___y_4363_, v___y_4364_, v___y_4365_, v___y_4366_);
lean_dec(v___y_4366_);
lean_dec_ref(v___y_4365_);
lean_dec(v___y_4364_);
lean_dec_ref(v___y_4363_);
lean_dec(v___y_4362_);
lean_dec_ref(v___y_4361_);
return v_res_4370_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2(lean_object* v_as_4371_, size_t v_sz_4372_, size_t v_i_4373_, lean_object* v_b_4374_, lean_object* v___y_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_, lean_object* v___y_4378_, lean_object* v___y_4379_, lean_object* v___y_4380_){
_start:
{
lean_object* v___x_4382_; 
v___x_4382_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___redArg(v_as_4371_, v_sz_4372_, v_i_4373_, v_b_4374_, v___y_4377_, v___y_4378_, v___y_4379_, v___y_4380_);
return v___x_4382_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___boxed(lean_object* v_as_4383_, lean_object* v_sz_4384_, lean_object* v_i_4385_, lean_object* v_b_4386_, lean_object* v___y_4387_, lean_object* v___y_4388_, lean_object* v___y_4389_, lean_object* v___y_4390_, lean_object* v___y_4391_, lean_object* v___y_4392_, lean_object* v___y_4393_){
_start:
{
size_t v_sz_boxed_4394_; size_t v_i_boxed_4395_; lean_object* v_res_4396_; 
v_sz_boxed_4394_ = lean_unbox_usize(v_sz_4384_);
lean_dec(v_sz_4384_);
v_i_boxed_4395_ = lean_unbox_usize(v_i_4385_);
lean_dec(v_i_4385_);
v_res_4396_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2(v_as_4383_, v_sz_boxed_4394_, v_i_boxed_4395_, v_b_4386_, v___y_4387_, v___y_4388_, v___y_4389_, v___y_4390_, v___y_4391_, v___y_4392_);
lean_dec(v___y_4392_);
lean_dec_ref(v___y_4391_);
lean_dec(v___y_4390_);
lean_dec_ref(v___y_4389_);
lean_dec(v___y_4388_);
lean_dec_ref(v___y_4387_);
lean_dec_ref(v_as_4383_);
return v_res_4396_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3(lean_object* v_as_4397_, size_t v_sz_4398_, size_t v_i_4399_, lean_object* v_b_4400_, lean_object* v___y_4401_, lean_object* v___y_4402_, lean_object* v___y_4403_, lean_object* v___y_4404_, lean_object* v___y_4405_, lean_object* v___y_4406_){
_start:
{
lean_object* v___x_4408_; 
v___x_4408_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___redArg(v_as_4397_, v_sz_4398_, v_i_4399_, v_b_4400_, v___y_4405_, v___y_4406_);
return v___x_4408_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___boxed(lean_object* v_as_4409_, lean_object* v_sz_4410_, lean_object* v_i_4411_, lean_object* v_b_4412_, lean_object* v___y_4413_, lean_object* v___y_4414_, lean_object* v___y_4415_, lean_object* v___y_4416_, lean_object* v___y_4417_, lean_object* v___y_4418_, lean_object* v___y_4419_){
_start:
{
size_t v_sz_boxed_4420_; size_t v_i_boxed_4421_; lean_object* v_res_4422_; 
v_sz_boxed_4420_ = lean_unbox_usize(v_sz_4410_);
lean_dec(v_sz_4410_);
v_i_boxed_4421_ = lean_unbox_usize(v_i_4411_);
lean_dec(v_i_4411_);
v_res_4422_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3(v_as_4409_, v_sz_boxed_4420_, v_i_boxed_4421_, v_b_4412_, v___y_4413_, v___y_4414_, v___y_4415_, v___y_4416_, v___y_4417_, v___y_4418_);
lean_dec(v___y_4418_);
lean_dec_ref(v___y_4417_);
lean_dec(v___y_4416_);
lean_dec_ref(v___y_4415_);
lean_dec(v___y_4414_);
lean_dec_ref(v___y_4413_);
lean_dec_ref(v_as_4409_);
return v_res_4422_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4(lean_object* v_as_4423_, size_t v_sz_4424_, size_t v_i_4425_, lean_object* v_b_4426_, lean_object* v___y_4427_, lean_object* v___y_4428_, lean_object* v___y_4429_, lean_object* v___y_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_){
_start:
{
lean_object* v___x_4434_; 
v___x_4434_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4___redArg(v_as_4423_, v_sz_4424_, v_i_4425_, v_b_4426_, v___y_4429_, v___y_4430_, v___y_4431_, v___y_4432_);
return v___x_4434_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4___boxed(lean_object* v_as_4435_, lean_object* v_sz_4436_, lean_object* v_i_4437_, lean_object* v_b_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_, lean_object* v___y_4441_, lean_object* v___y_4442_, lean_object* v___y_4443_, lean_object* v___y_4444_, lean_object* v___y_4445_){
_start:
{
size_t v_sz_boxed_4446_; size_t v_i_boxed_4447_; lean_object* v_res_4448_; 
v_sz_boxed_4446_ = lean_unbox_usize(v_sz_4436_);
lean_dec(v_sz_4436_);
v_i_boxed_4447_ = lean_unbox_usize(v_i_4437_);
lean_dec(v_i_4437_);
v_res_4448_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4(v_as_4435_, v_sz_boxed_4446_, v_i_boxed_4447_, v_b_4438_, v___y_4439_, v___y_4440_, v___y_4441_, v___y_4442_, v___y_4443_, v___y_4444_);
lean_dec(v___y_4444_);
lean_dec_ref(v___y_4443_);
lean_dec(v___y_4442_);
lean_dec_ref(v___y_4441_);
lean_dec(v___y_4440_);
lean_dec_ref(v___y_4439_);
lean_dec_ref(v_as_4435_);
return v_res_4448_;
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
