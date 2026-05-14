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
lean_object* l_Array_instInhabited(lean_object*);
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
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_withEnv___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_FixedParamPerm_buildArgs___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_beta(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_mkBRecOnApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_enableRealizationsForConst(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_Elab_Structural_mkBRecOnF___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_mkIndPredBRecOnF___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_erase(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
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
lean_object* l_Lean_Meta_PProdN_mkLambdas___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_InductiveVal_numTypeFormers(lean_object*);
lean_object* l_Array_range(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
uint8_t l_Nat_blt(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInductivePredicate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_zip___redArg(lean_object*, lean_object*);
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
lean_object* l_Lean_Elab_Structural_mkBRecOnConst(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_mkBRecOnMotive(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg___closed__0;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16_spec__29___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16_spec__29___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_f"};
static const lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg___closed__0 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg___closed__0_value;
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(253, 65, 185, 154, 193, 83, 240, 170)}};
static const lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg___closed__1 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__20(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16_spec__29(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16_spec__29___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_21830__overap_176_; lean_object* v___x_177_; 
v___x_21830__overap_176_ = lean_array_uget_borrowed(v_as_166_, v_i_167_);
lean_inc(v___x_21830__overap_176_);
lean_inc(v___y_173_);
lean_inc_ref(v___y_172_);
lean_inc(v___y_171_);
lean_inc_ref(v___y_170_);
v___x_177_ = lean_apply_5(v___x_21830__overap_176_, v___y_170_, v___y_171_, v___y_172_, v___y_173_, lean_box(0));
if (lean_obj_tag(v___x_177_) == 0)
{
lean_object* v_a_178_; size_t v___x_179_; size_t v___x_180_; 
v_a_178_ = lean_ctor_get(v___x_177_, 0);
lean_inc(v_a_178_);
lean_dec_ref(v___x_177_);
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
lean_dec_ref(v___x_204_);
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
lean_object* v___x_253_; lean_object* v_nextMacroScope_254_; lean_object* v_ngen_255_; lean_object* v_auxDeclNGen_256_; lean_object* v_traceState_257_; lean_object* v_messages_258_; lean_object* v_infoState_259_; lean_object* v_snapshotTasks_260_; lean_object* v_newDecls_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_287_; 
v___x_253_ = lean_st_ref_take(v___y_251_);
v_nextMacroScope_254_ = lean_ctor_get(v___x_253_, 1);
v_ngen_255_ = lean_ctor_get(v___x_253_, 2);
v_auxDeclNGen_256_ = lean_ctor_get(v___x_253_, 3);
v_traceState_257_ = lean_ctor_get(v___x_253_, 4);
v_messages_258_ = lean_ctor_get(v___x_253_, 6);
v_infoState_259_ = lean_ctor_get(v___x_253_, 7);
v_snapshotTasks_260_ = lean_ctor_get(v___x_253_, 8);
v_newDecls_261_ = lean_ctor_get(v___x_253_, 9);
v_isSharedCheck_287_ = !lean_is_exclusive(v___x_253_);
if (v_isSharedCheck_287_ == 0)
{
lean_object* v_unused_288_; lean_object* v_unused_289_; 
v_unused_288_ = lean_ctor_get(v___x_253_, 5);
lean_dec(v_unused_288_);
v_unused_289_ = lean_ctor_get(v___x_253_, 0);
lean_dec(v_unused_289_);
v___x_263_ = v___x_253_;
v_isShared_264_ = v_isSharedCheck_287_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_newDecls_261_);
lean_inc(v_snapshotTasks_260_);
lean_inc(v_infoState_259_);
lean_inc(v_messages_258_);
lean_inc(v_traceState_257_);
lean_inc(v_auxDeclNGen_256_);
lean_inc(v_ngen_255_);
lean_inc(v_nextMacroScope_254_);
lean_dec(v___x_253_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_287_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v___x_265_; lean_object* v___x_267_; 
v___x_265_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__2);
if (v_isShared_264_ == 0)
{
lean_ctor_set(v___x_263_, 5, v___x_265_);
lean_ctor_set(v___x_263_, 0, v_env_249_);
v___x_267_ = v___x_263_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v_env_249_);
lean_ctor_set(v_reuseFailAlloc_286_, 1, v_nextMacroScope_254_);
lean_ctor_set(v_reuseFailAlloc_286_, 2, v_ngen_255_);
lean_ctor_set(v_reuseFailAlloc_286_, 3, v_auxDeclNGen_256_);
lean_ctor_set(v_reuseFailAlloc_286_, 4, v_traceState_257_);
lean_ctor_set(v_reuseFailAlloc_286_, 5, v___x_265_);
lean_ctor_set(v_reuseFailAlloc_286_, 6, v_messages_258_);
lean_ctor_set(v_reuseFailAlloc_286_, 7, v_infoState_259_);
lean_ctor_set(v_reuseFailAlloc_286_, 8, v_snapshotTasks_260_);
lean_ctor_set(v_reuseFailAlloc_286_, 9, v_newDecls_261_);
v___x_267_ = v_reuseFailAlloc_286_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v_mctx_270_; lean_object* v_zetaDeltaFVarIds_271_; lean_object* v_postponed_272_; lean_object* v_diag_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_284_; 
v___x_268_ = lean_st_ref_set(v___y_251_, v___x_267_);
v___x_269_ = lean_st_ref_take(v___y_250_);
v_mctx_270_ = lean_ctor_get(v___x_269_, 0);
v_zetaDeltaFVarIds_271_ = lean_ctor_get(v___x_269_, 2);
v_postponed_272_ = lean_ctor_get(v___x_269_, 3);
v_diag_273_ = lean_ctor_get(v___x_269_, 4);
v_isSharedCheck_284_ = !lean_is_exclusive(v___x_269_);
if (v_isSharedCheck_284_ == 0)
{
lean_object* v_unused_285_; 
v_unused_285_ = lean_ctor_get(v___x_269_, 1);
lean_dec(v_unused_285_);
v___x_275_ = v___x_269_;
v_isShared_276_ = v_isSharedCheck_284_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_diag_273_);
lean_inc(v_postponed_272_);
lean_inc(v_zetaDeltaFVarIds_271_);
lean_inc(v_mctx_270_);
lean_dec(v___x_269_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_284_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v___x_277_; lean_object* v___x_279_; 
v___x_277_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__3, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__3);
if (v_isShared_276_ == 0)
{
lean_ctor_set(v___x_275_, 1, v___x_277_);
v___x_279_ = v___x_275_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v_mctx_270_);
lean_ctor_set(v_reuseFailAlloc_283_, 1, v___x_277_);
lean_ctor_set(v_reuseFailAlloc_283_, 2, v_zetaDeltaFVarIds_271_);
lean_ctor_set(v_reuseFailAlloc_283_, 3, v_postponed_272_);
lean_ctor_set(v_reuseFailAlloc_283_, 4, v_diag_273_);
v___x_279_ = v_reuseFailAlloc_283_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_280_ = lean_st_ref_set(v___y_250_, v___x_279_);
v___x_281_ = lean_box(0);
v___x_282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_282_, 0, v___x_281_);
return v___x_282_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___boxed(lean_object* v_env_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg(v_env_290_, v___y_291_, v___y_292_);
lean_dec(v___y_292_);
lean_dec(v___y_291_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23___redArg(lean_object* v_env_295_, lean_object* v_x_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_){
_start:
{
lean_object* v___x_302_; lean_object* v_env_303_; lean_object* v_a_305_; lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_302_ = lean_st_ref_get(v___y_300_);
v_env_303_ = lean_ctor_get(v___x_302_, 0);
lean_inc_ref(v_env_303_);
lean_dec(v___x_302_);
v___x_315_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg(v_env_295_, v___y_298_, v___y_300_);
lean_dec_ref(v___x_315_);
lean_inc(v___y_300_);
lean_inc_ref(v___y_299_);
lean_inc(v___y_298_);
lean_inc_ref(v___y_297_);
v___x_316_ = lean_apply_5(v_x_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_, lean_box(0));
if (lean_obj_tag(v___x_316_) == 0)
{
lean_object* v_a_317_; lean_object* v___x_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_325_; 
v_a_317_ = lean_ctor_get(v___x_316_, 0);
lean_inc(v_a_317_);
lean_dec_ref(v___x_316_);
v___x_318_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg(v_env_303_, v___y_298_, v___y_300_);
v_isSharedCheck_325_ = !lean_is_exclusive(v___x_318_);
if (v_isSharedCheck_325_ == 0)
{
lean_object* v_unused_326_; 
v_unused_326_ = lean_ctor_get(v___x_318_, 0);
lean_dec(v_unused_326_);
v___x_320_ = v___x_318_;
v_isShared_321_ = v_isSharedCheck_325_;
goto v_resetjp_319_;
}
else
{
lean_dec(v___x_318_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_325_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v___x_323_; 
if (v_isShared_321_ == 0)
{
lean_ctor_set(v___x_320_, 0, v_a_317_);
v___x_323_ = v___x_320_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v_a_317_);
v___x_323_ = v_reuseFailAlloc_324_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
return v___x_323_;
}
}
}
else
{
lean_object* v_a_327_; 
v_a_327_ = lean_ctor_get(v___x_316_, 0);
lean_inc(v_a_327_);
lean_dec_ref(v___x_316_);
v_a_305_ = v_a_327_;
goto v___jp_304_;
}
v___jp_304_:
{
lean_object* v___x_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_313_; 
v___x_306_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg(v_env_303_, v___y_298_, v___y_300_);
v_isSharedCheck_313_ = !lean_is_exclusive(v___x_306_);
if (v_isSharedCheck_313_ == 0)
{
lean_object* v_unused_314_; 
v_unused_314_ = lean_ctor_get(v___x_306_, 0);
lean_dec(v_unused_314_);
v___x_308_ = v___x_306_;
v_isShared_309_ = v_isSharedCheck_313_;
goto v_resetjp_307_;
}
else
{
lean_dec(v___x_306_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_313_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v___x_311_; 
if (v_isShared_309_ == 0)
{
lean_ctor_set_tag(v___x_308_, 1);
lean_ctor_set(v___x_308_, 0, v_a_305_);
v___x_311_ = v___x_308_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v_a_305_);
v___x_311_ = v_reuseFailAlloc_312_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
return v___x_311_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23___redArg___boxed(lean_object* v_env_328_, lean_object* v_x_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23___redArg(v_env_328_, v_x_329_, v___y_330_, v___y_331_, v___y_332_, v___y_333_);
lean_dec(v___y_333_);
lean_dec_ref(v___y_332_);
lean_dec(v___y_331_);
lean_dec_ref(v___y_330_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___lam__1(lean_object* v___x_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_){
_start:
{
lean_object* v___x_342_; 
v___x_342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_342_, 0, v___x_336_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___lam__1___boxed(lean_object* v___x_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___lam__1(v___x_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_);
lean_dec(v___y_347_);
lean_dec_ref(v___y_346_);
lean_dec(v___y_345_);
lean_dec_ref(v___y_344_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___lam__0(lean_object* v___y_350_, lean_object* v_k_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_){
_start:
{
lean_object* v___x_357_; 
lean_inc(v___y_355_);
lean_inc_ref(v___y_354_);
lean_inc(v___y_353_);
lean_inc_ref(v___y_352_);
v___x_357_ = lean_apply_5(v___y_350_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, lean_box(0));
if (lean_obj_tag(v___x_357_) == 0)
{
lean_object* v___x_358_; 
lean_dec_ref(v___x_357_);
v___x_358_ = lean_apply_5(v_k_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, lean_box(0));
return v___x_358_;
}
else
{
lean_object* v_a_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_366_; 
lean_dec(v___y_355_);
lean_dec_ref(v___y_354_);
lean_dec(v___y_353_);
lean_dec_ref(v___y_352_);
lean_dec_ref(v_k_351_);
v_a_359_ = lean_ctor_get(v___x_357_, 0);
v_isSharedCheck_366_ = !lean_is_exclusive(v___x_357_);
if (v_isSharedCheck_366_ == 0)
{
v___x_361_ = v___x_357_;
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_a_359_);
lean_dec(v___x_357_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v___x_364_; 
if (v_isShared_362_ == 0)
{
v___x_364_ = v___x_361_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_a_359_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___lam__0___boxed(lean_object* v___y_367_, lean_object* v_k_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___lam__0(v___y_367_, v_k_368_, v___y_369_, v___y_370_, v___y_371_, v___y_372_);
return v_res_374_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(lean_object* v_preDefs_379_, lean_object* v_k_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_){
_start:
{
lean_object* v___y_387_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; uint8_t v___x_396_; 
v___x_393_ = lean_unsigned_to_nat(0u);
v___x_394_ = lean_array_get_size(v_preDefs_379_);
v___x_395_ = lean_box(0);
v___x_396_ = lean_nat_dec_lt(v___x_393_, v___x_394_);
if (v___x_396_ == 0)
{
lean_object* v___f_397_; 
lean_dec_ref(v_preDefs_379_);
v___f_397_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___closed__0));
v___y_387_ = v___f_397_;
goto v___jp_386_;
}
else
{
uint8_t v___x_398_; 
v___x_398_ = lean_nat_dec_le(v___x_394_, v___x_394_);
if (v___x_398_ == 0)
{
if (v___x_396_ == 0)
{
lean_object* v___f_399_; 
lean_dec_ref(v_preDefs_379_);
v___f_399_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___closed__0));
v___y_387_ = v___f_399_;
goto v___jp_386_;
}
else
{
size_t v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_400_ = lean_usize_of_nat(v___x_394_);
v___x_401_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___boxed__const__1));
v___x_402_ = lean_box_usize(v___x_400_);
v___x_403_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__24___boxed), 9, 4);
lean_closure_set(v___x_403_, 0, v_preDefs_379_);
lean_closure_set(v___x_403_, 1, v___x_401_);
lean_closure_set(v___x_403_, 2, v___x_402_);
lean_closure_set(v___x_403_, 3, v___x_395_);
v___y_387_ = v___x_403_;
goto v___jp_386_;
}
}
else
{
size_t v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_404_ = lean_usize_of_nat(v___x_394_);
v___x_405_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___boxed__const__1));
v___x_406_ = lean_box_usize(v___x_404_);
v___x_407_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__24___boxed), 9, 4);
lean_closure_set(v___x_407_, 0, v_preDefs_379_);
lean_closure_set(v___x_407_, 1, v___x_405_);
lean_closure_set(v___x_407_, 2, v___x_406_);
lean_closure_set(v___x_407_, 3, v___x_395_);
v___y_387_ = v___x_407_;
goto v___jp_386_;
}
}
v___jp_386_:
{
lean_object* v___x_388_; lean_object* v_env_389_; lean_object* v___f_390_; lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_388_ = lean_st_ref_get(v___y_384_);
v_env_389_ = lean_ctor_get(v___x_388_, 0);
lean_inc_ref(v_env_389_);
lean_dec(v___x_388_);
v___f_390_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_390_, 0, v___y_387_);
lean_closure_set(v___f_390_, 1, v_k_380_);
v___x_391_ = l_Lean_Environment_unlockAsync(v_env_389_);
v___x_392_ = l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23___redArg(v___x_391_, v___f_390_, v___y_381_, v___y_382_, v___y_383_, v___y_384_);
return v___x_392_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___boxed(lean_object* v_preDefs_408_, lean_object* v_k_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v_preDefs_408_, v_k_409_, v___y_410_, v___y_411_, v___y_412_, v___y_413_);
lean_dec(v___y_413_);
lean_dec_ref(v___y_412_);
lean_dec(v___y_411_);
lean_dec_ref(v___y_410_);
return v_res_415_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg___closed__0(void){
_start:
{
lean_object* v___x_416_; lean_object* v_dummy_417_; 
v___x_416_ = lean_box(0);
v_dummy_417_ = l_Lean_Expr_sort___override(v___x_416_);
return v_dummy_417_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg(uint8_t v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_recArgInfos_421_, lean_object* v___x_422_, lean_object* v_preDefs_423_, lean_object* v_a_424_, lean_object* v_as_425_, lean_object* v_i_426_, lean_object* v_j_427_, lean_object* v_bs_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_){
_start:
{
lean_object* v_zero_434_; uint8_t v_isZero_435_; 
v_zero_434_ = lean_unsigned_to_nat(0u);
v_isZero_435_ = lean_nat_dec_eq(v_i_426_, v_zero_434_);
if (v_isZero_435_ == 1)
{
lean_object* v___x_436_; 
lean_dec(v_j_427_);
lean_dec(v_i_426_);
lean_dec_ref(v_a_424_);
lean_dec_ref(v_preDefs_423_);
lean_dec_ref(v___x_422_);
lean_dec_ref(v_recArgInfos_421_);
v___x_436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_436_, 0, v_bs_428_);
return v___x_436_;
}
else
{
lean_object* v___x_437_; lean_object* v_one_438_; lean_object* v_n_439_; lean_object* v_a_441_; lean_object* v___x_445_; 
v___x_437_ = l_Lean_instInhabitedExpr;
v_one_438_ = lean_unsigned_to_nat(1u);
v_n_439_ = lean_nat_sub(v_i_426_, v_one_438_);
lean_dec(v_i_426_);
v___x_445_ = lean_array_fget_borrowed(v_as_425_, v_j_427_);
if (v_a_418_ == 0)
{
lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_446_ = lean_array_get_borrowed(v___x_437_, v_a_419_, v_j_427_);
v___x_447_ = lean_array_get_borrowed(v___x_437_, v_a_420_, v_j_427_);
lean_inc(v___x_447_);
lean_inc(v___x_446_);
lean_inc(v___x_445_);
lean_inc_ref(v___x_422_);
lean_inc_ref(v_recArgInfos_421_);
v___x_448_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnF___boxed), 10, 5);
lean_closure_set(v___x_448_, 0, v_recArgInfos_421_);
lean_closure_set(v___x_448_, 1, v___x_422_);
lean_closure_set(v___x_448_, 2, v___x_445_);
lean_closure_set(v___x_448_, 3, v___x_446_);
lean_closure_set(v___x_448_, 4, v___x_447_);
lean_inc_ref(v_preDefs_423_);
v___x_449_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v_preDefs_423_, v___x_448_, v___y_429_, v___y_430_, v___y_431_, v___y_432_);
if (lean_obj_tag(v___x_449_) == 0)
{
lean_object* v_a_450_; 
v_a_450_ = lean_ctor_get(v___x_449_, 0);
lean_inc(v_a_450_);
lean_dec_ref(v___x_449_);
v_a_441_ = v_a_450_;
goto v___jp_440_;
}
else
{
lean_object* v_a_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_458_; 
lean_dec(v_n_439_);
lean_dec_ref(v_bs_428_);
lean_dec(v_j_427_);
lean_dec_ref(v_a_424_);
lean_dec_ref(v_preDefs_423_);
lean_dec_ref(v___x_422_);
lean_dec_ref(v_recArgInfos_421_);
v_a_451_ = lean_ctor_get(v___x_449_, 0);
v_isSharedCheck_458_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_458_ == 0)
{
v___x_453_ = v___x_449_;
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_a_451_);
lean_dec(v___x_449_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___x_456_; 
if (v_isShared_454_ == 0)
{
v___x_456_ = v___x_453_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_a_451_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
return v___x_456_;
}
}
}
}
else
{
lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v_dummy_462_; lean_object* v_nargs_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_459_ = lean_array_get_borrowed(v___x_437_, v_a_419_, v_j_427_);
v___x_460_ = lean_array_get_borrowed(v___x_437_, v_a_420_, v_j_427_);
lean_inc_ref(v_a_424_);
v___x_461_ = lean_apply_1(v_a_424_, v_zero_434_);
v_dummy_462_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg___closed__0, &l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg___closed__0_once, _init_l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg___closed__0);
v_nargs_463_ = l_Lean_Expr_getAppNumArgs(v___x_461_);
lean_inc(v_nargs_463_);
v___x_464_ = lean_mk_array(v_nargs_463_, v_dummy_462_);
v___x_465_ = lean_nat_sub(v_nargs_463_, v_one_438_);
lean_dec(v_nargs_463_);
v___x_466_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___x_461_, v___x_464_, v___x_465_);
lean_inc(v___x_460_);
lean_inc(v___x_459_);
lean_inc(v___x_445_);
lean_inc_ref(v___x_422_);
lean_inc_ref(v_recArgInfos_421_);
v___x_467_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkIndPredBRecOnF___boxed), 11, 6);
lean_closure_set(v___x_467_, 0, v_recArgInfos_421_);
lean_closure_set(v___x_467_, 1, v___x_422_);
lean_closure_set(v___x_467_, 2, v___x_445_);
lean_closure_set(v___x_467_, 3, v___x_459_);
lean_closure_set(v___x_467_, 4, v___x_460_);
lean_closure_set(v___x_467_, 5, v___x_466_);
lean_inc_ref(v_preDefs_423_);
v___x_468_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v_preDefs_423_, v___x_467_, v___y_429_, v___y_430_, v___y_431_, v___y_432_);
if (lean_obj_tag(v___x_468_) == 0)
{
lean_object* v_a_469_; lean_object* v_fst_470_; lean_object* v_snd_471_; lean_object* v___y_473_; lean_object* v___x_482_; uint8_t v___x_483_; 
v_a_469_ = lean_ctor_get(v___x_468_, 0);
lean_inc(v_a_469_);
lean_dec_ref(v___x_468_);
v_fst_470_ = lean_ctor_get(v_a_469_, 0);
lean_inc(v_fst_470_);
v_snd_471_ = lean_ctor_get(v_a_469_, 1);
lean_inc(v_snd_471_);
lean_dec(v_a_469_);
v___x_482_ = lean_array_get_size(v_snd_471_);
v___x_483_ = lean_nat_dec_lt(v_zero_434_, v___x_482_);
if (v___x_483_ == 0)
{
lean_dec(v_snd_471_);
v_a_441_ = v_fst_470_;
goto v___jp_440_;
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
v_a_441_ = v_fst_470_;
goto v___jp_440_;
}
else
{
size_t v___x_486_; size_t v___x_487_; lean_object* v___x_488_; 
v___x_486_ = ((size_t)0ULL);
v___x_487_ = lean_usize_of_nat(v___x_482_);
v___x_488_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13(v_snd_471_, v___x_486_, v___x_487_, v___x_484_, v___y_429_, v___y_430_, v___y_431_, v___y_432_);
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
v___x_491_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13(v_snd_471_, v___x_489_, v___x_490_, v___x_484_, v___y_429_, v___y_430_, v___y_431_, v___y_432_);
lean_dec(v_snd_471_);
v___y_473_ = v___x_491_;
goto v___jp_472_;
}
}
v___jp_472_:
{
if (lean_obj_tag(v___y_473_) == 0)
{
lean_dec_ref(v___y_473_);
v_a_441_ = v_fst_470_;
goto v___jp_440_;
}
else
{
lean_object* v_a_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_481_; 
lean_dec(v_fst_470_);
lean_dec(v_n_439_);
lean_dec_ref(v_bs_428_);
lean_dec(v_j_427_);
lean_dec_ref(v_a_424_);
lean_dec_ref(v_preDefs_423_);
lean_dec_ref(v___x_422_);
lean_dec_ref(v_recArgInfos_421_);
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
lean_dec(v_n_439_);
lean_dec_ref(v_bs_428_);
lean_dec(v_j_427_);
lean_dec_ref(v_a_424_);
lean_dec_ref(v_preDefs_423_);
lean_dec_ref(v___x_422_);
lean_dec_ref(v_recArgInfos_421_);
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
v___jp_440_:
{
lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_442_ = lean_nat_add(v_j_427_, v_one_438_);
lean_dec(v_j_427_);
v___x_443_ = lean_array_push(v_bs_428_, v_a_441_);
v_i_426_ = v_n_439_;
v_j_427_ = v___x_442_;
v_bs_428_ = v___x_443_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg___boxed(lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_recArgInfos_503_, lean_object* v___x_504_, lean_object* v_preDefs_505_, lean_object* v_a_506_, lean_object* v_as_507_, lean_object* v_i_508_, lean_object* v_j_509_, lean_object* v_bs_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_){
_start:
{
uint8_t v_a_27675__boxed_516_; lean_object* v_res_517_; 
v_a_27675__boxed_516_ = lean_unbox(v_a_500_);
v_res_517_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg(v_a_27675__boxed_516_, v_a_501_, v_a_502_, v_recArgInfos_503_, v___x_504_, v_preDefs_505_, v_a_506_, v_as_507_, v_i_508_, v_j_509_, v_bs_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_);
lean_dec(v___y_514_);
lean_dec_ref(v___y_513_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
lean_dec_ref(v_as_507_);
lean_dec_ref(v_a_502_);
lean_dec_ref(v_a_501_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11_spec__21(lean_object* v_msgData_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_){
_start:
{
lean_object* v___x_524_; lean_object* v_env_525_; lean_object* v___x_526_; lean_object* v_mctx_527_; lean_object* v_lctx_528_; lean_object* v_options_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_524_ = lean_st_ref_get(v___y_522_);
v_env_525_ = lean_ctor_get(v___x_524_, 0);
lean_inc_ref(v_env_525_);
lean_dec(v___x_524_);
v___x_526_ = lean_st_ref_get(v___y_520_);
v_mctx_527_ = lean_ctor_get(v___x_526_, 0);
lean_inc_ref(v_mctx_527_);
lean_dec(v___x_526_);
v_lctx_528_ = lean_ctor_get(v___y_519_, 2);
v_options_529_ = lean_ctor_get(v___y_521_, 2);
lean_inc_ref(v_options_529_);
lean_inc_ref(v_lctx_528_);
v___x_530_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_530_, 0, v_env_525_);
lean_ctor_set(v___x_530_, 1, v_mctx_527_);
lean_ctor_set(v___x_530_, 2, v_lctx_528_);
lean_ctor_set(v___x_530_, 3, v_options_529_);
v___x_531_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_531_, 0, v___x_530_);
lean_ctor_set(v___x_531_, 1, v_msgData_518_);
v___x_532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_532_, 0, v___x_531_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11_spec__21___boxed(lean_object* v_msgData_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_){
_start:
{
lean_object* v_res_539_; 
v_res_539_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11_spec__21(v_msgData_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_);
lean_dec(v___y_537_);
lean_dec_ref(v___y_536_);
lean_dec(v___y_535_);
lean_dec_ref(v___y_534_);
return v_res_539_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___closed__0(void){
_start:
{
lean_object* v___x_540_; double v___x_541_; 
v___x_540_ = lean_unsigned_to_nat(0u);
v___x_541_ = lean_float_of_nat(v___x_540_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(lean_object* v_cls_545_, lean_object* v_msg_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_){
_start:
{
lean_object* v_ref_552_; lean_object* v___x_553_; lean_object* v_a_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_599_; 
v_ref_552_ = lean_ctor_get(v___y_549_, 5);
v___x_553_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11_spec__21(v_msg_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_);
v_a_554_ = lean_ctor_get(v___x_553_, 0);
v_isSharedCheck_599_ = !lean_is_exclusive(v___x_553_);
if (v_isSharedCheck_599_ == 0)
{
v___x_556_ = v___x_553_;
v_isShared_557_ = v_isSharedCheck_599_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_a_554_);
lean_dec(v___x_553_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_599_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v___x_558_; lean_object* v_traceState_559_; lean_object* v_env_560_; lean_object* v_nextMacroScope_561_; lean_object* v_ngen_562_; lean_object* v_auxDeclNGen_563_; lean_object* v_cache_564_; lean_object* v_messages_565_; lean_object* v_infoState_566_; lean_object* v_snapshotTasks_567_; lean_object* v_newDecls_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_598_; 
v___x_558_ = lean_st_ref_take(v___y_550_);
v_traceState_559_ = lean_ctor_get(v___x_558_, 4);
v_env_560_ = lean_ctor_get(v___x_558_, 0);
v_nextMacroScope_561_ = lean_ctor_get(v___x_558_, 1);
v_ngen_562_ = lean_ctor_get(v___x_558_, 2);
v_auxDeclNGen_563_ = lean_ctor_get(v___x_558_, 3);
v_cache_564_ = lean_ctor_get(v___x_558_, 5);
v_messages_565_ = lean_ctor_get(v___x_558_, 6);
v_infoState_566_ = lean_ctor_get(v___x_558_, 7);
v_snapshotTasks_567_ = lean_ctor_get(v___x_558_, 8);
v_newDecls_568_ = lean_ctor_get(v___x_558_, 9);
v_isSharedCheck_598_ = !lean_is_exclusive(v___x_558_);
if (v_isSharedCheck_598_ == 0)
{
v___x_570_ = v___x_558_;
v_isShared_571_ = v_isSharedCheck_598_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_newDecls_568_);
lean_inc(v_snapshotTasks_567_);
lean_inc(v_infoState_566_);
lean_inc(v_messages_565_);
lean_inc(v_cache_564_);
lean_inc(v_traceState_559_);
lean_inc(v_auxDeclNGen_563_);
lean_inc(v_ngen_562_);
lean_inc(v_nextMacroScope_561_);
lean_inc(v_env_560_);
lean_dec(v___x_558_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_598_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
uint64_t v_tid_572_; lean_object* v_traces_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_597_; 
v_tid_572_ = lean_ctor_get_uint64(v_traceState_559_, sizeof(void*)*1);
v_traces_573_ = lean_ctor_get(v_traceState_559_, 0);
v_isSharedCheck_597_ = !lean_is_exclusive(v_traceState_559_);
if (v_isSharedCheck_597_ == 0)
{
v___x_575_ = v_traceState_559_;
v_isShared_576_ = v_isSharedCheck_597_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_traces_573_);
lean_dec(v_traceState_559_);
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
lean_ctor_set(v___x_581_, 0, v_cls_545_);
lean_ctor_set(v___x_581_, 1, v___x_577_);
lean_ctor_set(v___x_581_, 2, v___x_580_);
lean_ctor_set_float(v___x_581_, sizeof(void*)*3, v___x_578_);
lean_ctor_set_float(v___x_581_, sizeof(void*)*3 + 8, v___x_578_);
lean_ctor_set_uint8(v___x_581_, sizeof(void*)*3 + 16, v___x_579_);
v___x_582_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___closed__2));
v___x_583_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_583_, 0, v___x_581_);
lean_ctor_set(v___x_583_, 1, v_a_554_);
lean_ctor_set(v___x_583_, 2, v___x_582_);
lean_inc(v_ref_552_);
v___x_584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_584_, 0, v_ref_552_);
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
v_reuseFailAlloc_595_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v_env_560_);
lean_ctor_set(v_reuseFailAlloc_595_, 1, v_nextMacroScope_561_);
lean_ctor_set(v_reuseFailAlloc_595_, 2, v_ngen_562_);
lean_ctor_set(v_reuseFailAlloc_595_, 3, v_auxDeclNGen_563_);
lean_ctor_set(v_reuseFailAlloc_595_, 4, v___x_587_);
lean_ctor_set(v_reuseFailAlloc_595_, 5, v_cache_564_);
lean_ctor_set(v_reuseFailAlloc_595_, 6, v_messages_565_);
lean_ctor_set(v_reuseFailAlloc_595_, 7, v_infoState_566_);
lean_ctor_set(v_reuseFailAlloc_595_, 8, v_snapshotTasks_567_);
lean_ctor_set(v_reuseFailAlloc_595_, 9, v_newDecls_568_);
v___x_589_ = v_reuseFailAlloc_595_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_593_; 
v___x_590_ = lean_st_ref_set(v___y_550_, v___x_589_);
v___x_591_ = lean_box(0);
if (v_isShared_557_ == 0)
{
lean_ctor_set(v___x_556_, 0, v___x_591_);
v___x_593_ = v___x_556_;
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
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(lean_object* v_a_644_, lean_object* v_a_645_){
_start:
{
if (lean_obj_tag(v_a_644_) == 0)
{
lean_object* v___x_646_; 
v___x_646_ = l_List_reverse___redArg(v_a_645_);
return v___x_646_;
}
else
{
lean_object* v_head_647_; lean_object* v_tail_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_657_; 
v_head_647_ = lean_ctor_get(v_a_644_, 0);
v_tail_648_ = lean_ctor_get(v_a_644_, 1);
v_isSharedCheck_657_ = !lean_is_exclusive(v_a_644_);
if (v_isSharedCheck_657_ == 0)
{
v___x_650_ = v_a_644_;
v_isShared_651_ = v_isSharedCheck_657_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_tail_648_);
lean_inc(v_head_647_);
lean_dec(v_a_644_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_657_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
lean_object* v___x_652_; lean_object* v___x_654_; 
v___x_652_ = l_Lean_MessageData_ofExpr(v_head_647_);
if (v_isShared_651_ == 0)
{
lean_ctor_set(v___x_650_, 1, v_a_645_);
lean_ctor_set(v___x_650_, 0, v___x_652_);
v___x_654_ = v___x_650_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v___x_652_);
lean_ctor_set(v_reuseFailAlloc_656_, 1, v_a_645_);
v___x_654_ = v_reuseFailAlloc_656_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
v_a_644_ = v_tail_648_;
v_a_645_ = v___x_654_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___lam__0(lean_object* v_fixedParamPerms_658_, lean_object* v___x_659_, lean_object* v_j_660_, lean_object* v_xs_661_, lean_object* v_snd_662_, uint8_t v_isZero_663_, lean_object* v_ys_664_, lean_object* v_x_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_){
_start:
{
lean_object* v_perms_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; uint8_t v___x_675_; uint8_t v___x_676_; lean_object* v___x_677_; 
v_perms_671_ = lean_ctor_get(v_fixedParamPerms_658_, 1);
v___x_672_ = lean_array_get_borrowed(v___x_659_, v_perms_671_, v_j_660_);
lean_inc_ref(v_ys_664_);
lean_inc(v___x_672_);
v___x_673_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v___x_672_, v_xs_661_, v_ys_664_);
v___x_674_ = l_Lean_Expr_beta(v_snd_662_, v_ys_664_);
v___x_675_ = 1;
v___x_676_ = 1;
v___x_677_ = l_Lean_Meta_mkLambdaFVars(v___x_673_, v___x_674_, v_isZero_663_, v___x_675_, v_isZero_663_, v___x_675_, v___x_676_, v___y_666_, v___y_667_, v___y_668_, v___y_669_);
lean_dec_ref(v___x_673_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___lam__0___boxed(lean_object* v_fixedParamPerms_678_, lean_object* v___x_679_, lean_object* v_j_680_, lean_object* v_xs_681_, lean_object* v_snd_682_, lean_object* v_isZero_683_, lean_object* v_ys_684_, lean_object* v_x_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_){
_start:
{
uint8_t v_isZero_boxed_691_; lean_object* v_res_692_; 
v_isZero_boxed_691_ = lean_unbox(v_isZero_683_);
v_res_692_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___lam__0(v_fixedParamPerms_678_, v___x_679_, v_j_680_, v_xs_681_, v_snd_682_, v_isZero_boxed_691_, v_ys_684_, v_x_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_);
lean_dec(v___y_689_);
lean_dec_ref(v___y_688_);
lean_dec(v___y_687_);
lean_dec_ref(v___y_686_);
lean_dec_ref(v_x_685_);
lean_dec_ref(v_xs_681_);
lean_dec(v_j_680_);
lean_dec_ref(v___x_679_);
lean_dec_ref(v_fixedParamPerms_678_);
return v_res_692_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_693_; 
v___x_693_ = l_Array_instInhabited(lean_box(0));
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg(lean_object* v_fixedParamPerms_694_, lean_object* v_xs_695_, lean_object* v_as_696_, lean_object* v_i_697_, lean_object* v_j_698_, lean_object* v_bs_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_){
_start:
{
lean_object* v_zero_705_; uint8_t v_isZero_706_; 
v_zero_705_ = lean_unsigned_to_nat(0u);
v_isZero_706_ = lean_nat_dec_eq(v_i_697_, v_zero_705_);
if (v_isZero_706_ == 1)
{
lean_object* v___x_707_; 
lean_dec(v_j_698_);
lean_dec(v_i_697_);
lean_dec_ref(v_xs_695_);
lean_dec_ref(v_fixedParamPerms_694_);
v___x_707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_707_, 0, v_bs_699_);
return v___x_707_;
}
else
{
lean_object* v___x_708_; lean_object* v_fst_709_; lean_object* v_snd_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___f_713_; lean_object* v___x_714_; 
v___x_708_ = lean_array_fget_borrowed(v_as_696_, v_j_698_);
v_fst_709_ = lean_ctor_get(v___x_708_, 0);
v_snd_710_ = lean_ctor_get(v___x_708_, 1);
v___x_711_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0, &l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0_once, _init_l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0);
v___x_712_ = lean_box(v_isZero_706_);
lean_inc(v_snd_710_);
lean_inc_ref(v_xs_695_);
lean_inc(v_j_698_);
lean_inc_ref(v_fixedParamPerms_694_);
v___f_713_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___lam__0___boxed), 13, 6);
lean_closure_set(v___f_713_, 0, v_fixedParamPerms_694_);
lean_closure_set(v___f_713_, 1, v___x_711_);
lean_closure_set(v___f_713_, 2, v_j_698_);
lean_closure_set(v___f_713_, 3, v_xs_695_);
lean_closure_set(v___f_713_, 4, v_snd_710_);
lean_closure_set(v___f_713_, 5, v___x_712_);
lean_inc(v_fst_709_);
v___x_714_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg(v_fst_709_, v___f_713_, v_isZero_706_, v___y_700_, v___y_701_, v___y_702_, v___y_703_);
if (lean_obj_tag(v___x_714_) == 0)
{
lean_object* v_a_715_; lean_object* v_one_716_; lean_object* v_n_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
v_a_715_ = lean_ctor_get(v___x_714_, 0);
lean_inc(v_a_715_);
lean_dec_ref(v___x_714_);
v_one_716_ = lean_unsigned_to_nat(1u);
v_n_717_ = lean_nat_sub(v_i_697_, v_one_716_);
lean_dec(v_i_697_);
v___x_718_ = lean_nat_add(v_j_698_, v_one_716_);
lean_dec(v_j_698_);
v___x_719_ = lean_array_push(v_bs_699_, v_a_715_);
v_i_697_ = v_n_717_;
v_j_698_ = v___x_718_;
v_bs_699_ = v___x_719_;
goto _start;
}
else
{
lean_object* v_a_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_728_; 
lean_dec_ref(v_bs_699_);
lean_dec(v_j_698_);
lean_dec(v_i_697_);
lean_dec_ref(v_xs_695_);
lean_dec_ref(v_fixedParamPerms_694_);
v_a_721_ = lean_ctor_get(v___x_714_, 0);
v_isSharedCheck_728_ = !lean_is_exclusive(v___x_714_);
if (v_isSharedCheck_728_ == 0)
{
v___x_723_ = v___x_714_;
v_isShared_724_ = v_isSharedCheck_728_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_a_721_);
lean_dec(v___x_714_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_728_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v___x_726_; 
if (v_isShared_724_ == 0)
{
v___x_726_ = v___x_723_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v_a_721_);
v___x_726_ = v_reuseFailAlloc_727_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
return v___x_726_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___boxed(lean_object* v_fixedParamPerms_729_, lean_object* v_xs_730_, lean_object* v_as_731_, lean_object* v_i_732_, lean_object* v_j_733_, lean_object* v_bs_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_){
_start:
{
lean_object* v_res_740_; 
v_res_740_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg(v_fixedParamPerms_729_, v_xs_730_, v_as_731_, v_i_732_, v_j_733_, v_bs_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_);
lean_dec(v___y_738_);
lean_dec_ref(v___y_737_);
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
lean_dec_ref(v_as_731_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__15(lean_object* v_a_741_, lean_object* v_a_742_){
_start:
{
if (lean_obj_tag(v_a_741_) == 0)
{
lean_object* v___x_743_; 
v___x_743_ = l_List_reverse___redArg(v_a_742_);
return v___x_743_;
}
else
{
lean_object* v_head_744_; lean_object* v_tail_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_754_; 
v_head_744_ = lean_ctor_get(v_a_741_, 0);
v_tail_745_ = lean_ctor_get(v_a_741_, 1);
v_isSharedCheck_754_ = !lean_is_exclusive(v_a_741_);
if (v_isSharedCheck_754_ == 0)
{
v___x_747_ = v_a_741_;
v_isShared_748_ = v_isSharedCheck_754_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_tail_745_);
lean_inc(v_head_744_);
lean_dec(v_a_741_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_754_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_749_; lean_object* v___x_751_; 
v___x_749_ = l_Lean_mkLevelParam(v_head_744_);
if (v_isShared_748_ == 0)
{
lean_ctor_set(v___x_747_, 1, v_a_742_);
lean_ctor_set(v___x_747_, 0, v___x_749_);
v___x_751_ = v___x_747_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v___x_749_);
lean_ctor_set(v_reuseFailAlloc_753_, 1, v_a_742_);
v___x_751_ = v_reuseFailAlloc_753_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
v_a_741_ = v_tail_745_;
v_a_742_ = v___x_751_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__0(void){
_start:
{
lean_object* v___x_755_; 
v___x_755_ = l_instMonadEIO(lean_box(0));
return v___x_755_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__5(void){
_start:
{
lean_object* v___x_760_; 
v___x_760_ = l_Array_instInhabited(lean_box(0));
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg(lean_object* v_msg_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_){
_start:
{
lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v_toApplicative_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_830_; 
v___x_767_ = lean_obj_once(&l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__0, &l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__0_once, _init_l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__0);
v___x_768_ = l_StateRefT_x27_instMonad___redArg(v___x_767_);
v_toApplicative_769_ = lean_ctor_get(v___x_768_, 0);
v_isSharedCheck_830_ = !lean_is_exclusive(v___x_768_);
if (v_isSharedCheck_830_ == 0)
{
lean_object* v_unused_831_; 
v_unused_831_ = lean_ctor_get(v___x_768_, 1);
lean_dec(v_unused_831_);
v___x_771_ = v___x_768_;
v_isShared_772_ = v_isSharedCheck_830_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_toApplicative_769_);
lean_dec(v___x_768_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_830_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v_toFunctor_773_; lean_object* v_toSeq_774_; lean_object* v_toSeqLeft_775_; lean_object* v_toSeqRight_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_828_; 
v_toFunctor_773_ = lean_ctor_get(v_toApplicative_769_, 0);
v_toSeq_774_ = lean_ctor_get(v_toApplicative_769_, 2);
v_toSeqLeft_775_ = lean_ctor_get(v_toApplicative_769_, 3);
v_toSeqRight_776_ = lean_ctor_get(v_toApplicative_769_, 4);
v_isSharedCheck_828_ = !lean_is_exclusive(v_toApplicative_769_);
if (v_isSharedCheck_828_ == 0)
{
lean_object* v_unused_829_; 
v_unused_829_ = lean_ctor_get(v_toApplicative_769_, 1);
lean_dec(v_unused_829_);
v___x_778_ = v_toApplicative_769_;
v_isShared_779_ = v_isSharedCheck_828_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_toSeqRight_776_);
lean_inc(v_toSeqLeft_775_);
lean_inc(v_toSeq_774_);
lean_inc(v_toFunctor_773_);
lean_dec(v_toApplicative_769_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_828_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___f_780_; lean_object* v___f_781_; lean_object* v___f_782_; lean_object* v___f_783_; lean_object* v___x_784_; lean_object* v___f_785_; lean_object* v___f_786_; lean_object* v___f_787_; lean_object* v___x_789_; 
v___f_780_ = ((lean_object*)(l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__1));
v___f_781_ = ((lean_object*)(l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__2));
lean_inc_ref(v_toFunctor_773_);
v___f_782_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_782_, 0, v_toFunctor_773_);
v___f_783_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_783_, 0, v_toFunctor_773_);
v___x_784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_784_, 0, v___f_782_);
lean_ctor_set(v___x_784_, 1, v___f_783_);
v___f_785_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_785_, 0, v_toSeqRight_776_);
v___f_786_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_786_, 0, v_toSeqLeft_775_);
v___f_787_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_787_, 0, v_toSeq_774_);
if (v_isShared_779_ == 0)
{
lean_ctor_set(v___x_778_, 4, v___f_785_);
lean_ctor_set(v___x_778_, 3, v___f_786_);
lean_ctor_set(v___x_778_, 2, v___f_787_);
lean_ctor_set(v___x_778_, 1, v___f_780_);
lean_ctor_set(v___x_778_, 0, v___x_784_);
v___x_789_ = v___x_778_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v___x_784_);
lean_ctor_set(v_reuseFailAlloc_827_, 1, v___f_780_);
lean_ctor_set(v_reuseFailAlloc_827_, 2, v___f_787_);
lean_ctor_set(v_reuseFailAlloc_827_, 3, v___f_786_);
lean_ctor_set(v_reuseFailAlloc_827_, 4, v___f_785_);
v___x_789_ = v_reuseFailAlloc_827_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
lean_object* v___x_791_; 
if (v_isShared_772_ == 0)
{
lean_ctor_set(v___x_771_, 1, v___f_781_);
lean_ctor_set(v___x_771_, 0, v___x_789_);
v___x_791_ = v___x_771_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v___x_789_);
lean_ctor_set(v_reuseFailAlloc_826_, 1, v___f_781_);
v___x_791_ = v_reuseFailAlloc_826_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
lean_object* v___x_792_; lean_object* v_toApplicative_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_824_; 
v___x_792_ = l_StateRefT_x27_instMonad___redArg(v___x_791_);
v_toApplicative_793_ = lean_ctor_get(v___x_792_, 0);
v_isSharedCheck_824_ = !lean_is_exclusive(v___x_792_);
if (v_isSharedCheck_824_ == 0)
{
lean_object* v_unused_825_; 
v_unused_825_ = lean_ctor_get(v___x_792_, 1);
lean_dec(v_unused_825_);
v___x_795_ = v___x_792_;
v_isShared_796_ = v_isSharedCheck_824_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_toApplicative_793_);
lean_dec(v___x_792_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_824_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v_toFunctor_797_; lean_object* v_toSeq_798_; lean_object* v_toSeqLeft_799_; lean_object* v_toSeqRight_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_822_; 
v_toFunctor_797_ = lean_ctor_get(v_toApplicative_793_, 0);
v_toSeq_798_ = lean_ctor_get(v_toApplicative_793_, 2);
v_toSeqLeft_799_ = lean_ctor_get(v_toApplicative_793_, 3);
v_toSeqRight_800_ = lean_ctor_get(v_toApplicative_793_, 4);
v_isSharedCheck_822_ = !lean_is_exclusive(v_toApplicative_793_);
if (v_isSharedCheck_822_ == 0)
{
lean_object* v_unused_823_; 
v_unused_823_ = lean_ctor_get(v_toApplicative_793_, 1);
lean_dec(v_unused_823_);
v___x_802_ = v_toApplicative_793_;
v_isShared_803_ = v_isSharedCheck_822_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_toSeqRight_800_);
lean_inc(v_toSeqLeft_799_);
lean_inc(v_toSeq_798_);
lean_inc(v_toFunctor_797_);
lean_dec(v_toApplicative_793_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_822_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___f_804_; lean_object* v___f_805_; lean_object* v___f_806_; lean_object* v___f_807_; lean_object* v___x_808_; lean_object* v___f_809_; lean_object* v___f_810_; lean_object* v___f_811_; lean_object* v___x_813_; 
v___f_804_ = ((lean_object*)(l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__3));
v___f_805_ = ((lean_object*)(l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__4));
lean_inc_ref(v_toFunctor_797_);
v___f_806_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_806_, 0, v_toFunctor_797_);
v___f_807_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_807_, 0, v_toFunctor_797_);
v___x_808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_808_, 0, v___f_806_);
lean_ctor_set(v___x_808_, 1, v___f_807_);
v___f_809_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_809_, 0, v_toSeqRight_800_);
v___f_810_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_810_, 0, v_toSeqLeft_799_);
v___f_811_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_811_, 0, v_toSeq_798_);
if (v_isShared_803_ == 0)
{
lean_ctor_set(v___x_802_, 4, v___f_809_);
lean_ctor_set(v___x_802_, 3, v___f_810_);
lean_ctor_set(v___x_802_, 2, v___f_811_);
lean_ctor_set(v___x_802_, 1, v___f_804_);
lean_ctor_set(v___x_802_, 0, v___x_808_);
v___x_813_ = v___x_802_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v___x_808_);
lean_ctor_set(v_reuseFailAlloc_821_, 1, v___f_804_);
lean_ctor_set(v_reuseFailAlloc_821_, 2, v___f_811_);
lean_ctor_set(v_reuseFailAlloc_821_, 3, v___f_810_);
lean_ctor_set(v_reuseFailAlloc_821_, 4, v___f_809_);
v___x_813_ = v_reuseFailAlloc_821_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
lean_object* v___x_815_; 
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 1, v___f_805_);
lean_ctor_set(v___x_795_, 0, v___x_813_);
v___x_815_ = v___x_795_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v___x_813_);
lean_ctor_set(v_reuseFailAlloc_820_, 1, v___f_805_);
v___x_815_ = v_reuseFailAlloc_820_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_23958__overap_818_; lean_object* v___x_819_; 
v___x_816_ = lean_obj_once(&l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__5, &l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__5_once, _init_l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__5);
v___x_817_ = l_instInhabitedOfMonad___redArg(v___x_815_, v___x_816_);
v___x_23958__overap_818_ = lean_panic_fn_borrowed(v___x_817_, v_msg_761_);
lean_dec(v___x_817_);
lean_inc(v___y_765_);
lean_inc_ref(v___y_764_);
lean_inc(v___y_763_);
lean_inc_ref(v___y_762_);
v___x_819_ = lean_apply_5(v___x_23958__overap_818_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, lean_box(0));
return v___x_819_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___boxed(lean_object* v_msg_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_){
_start:
{
lean_object* v_res_838_; 
v_res_838_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg(v_msg_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_);
lean_dec(v___y_836_);
lean_dec_ref(v___y_835_);
lean_dec(v___y_834_);
lean_dec_ref(v___y_833_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__13(lean_object* v_xs_839_, size_t v_sz_840_, size_t v_i_841_, lean_object* v_bs_842_){
_start:
{
uint8_t v___x_843_; 
v___x_843_ = lean_usize_dec_lt(v_i_841_, v_sz_840_);
if (v___x_843_ == 0)
{
return v_bs_842_;
}
else
{
lean_object* v___x_844_; lean_object* v_v_845_; lean_object* v___x_846_; lean_object* v_bs_x27_847_; lean_object* v___x_848_; size_t v___x_849_; size_t v___x_850_; lean_object* v___x_851_; 
v___x_844_ = l_Lean_instInhabitedExpr;
v_v_845_ = lean_array_uget(v_bs_842_, v_i_841_);
v___x_846_ = lean_unsigned_to_nat(0u);
v_bs_x27_847_ = lean_array_uset(v_bs_842_, v_i_841_, v___x_846_);
v___x_848_ = lean_array_get_borrowed(v___x_844_, v_xs_839_, v_v_845_);
lean_dec(v_v_845_);
v___x_849_ = ((size_t)1ULL);
v___x_850_ = lean_usize_add(v_i_841_, v___x_849_);
lean_inc(v___x_848_);
v___x_851_ = lean_array_uset(v_bs_x27_847_, v_i_841_, v___x_848_);
v_i_841_ = v___x_850_;
v_bs_842_ = v___x_851_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__13___boxed(lean_object* v_xs_853_, lean_object* v_sz_854_, lean_object* v_i_855_, lean_object* v_bs_856_){
_start:
{
size_t v_sz_boxed_857_; size_t v_i_boxed_858_; lean_object* v_res_859_; 
v_sz_boxed_857_ = lean_unbox_usize(v_sz_854_);
lean_dec(v_sz_854_);
v_i_boxed_858_ = lean_unbox_usize(v_i_855_);
lean_dec(v_i_855_);
v_res_859_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__13(v_xs_853_, v_sz_boxed_857_, v_i_boxed_858_, v_bs_856_);
lean_dec_ref(v_xs_853_);
return v_res_859_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15___redArg(lean_object* v_xs_860_, lean_object* v_f_861_, lean_object* v_as_862_, lean_object* v_bs_863_, lean_object* v_i_864_, lean_object* v_cs_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_){
_start:
{
lean_object* v___x_871_; uint8_t v___x_872_; 
v___x_871_ = lean_array_get_size(v_as_862_);
v___x_872_ = lean_nat_dec_lt(v_i_864_, v___x_871_);
if (v___x_872_ == 0)
{
lean_object* v___x_873_; 
lean_dec(v_i_864_);
lean_dec_ref(v_f_861_);
v___x_873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_873_, 0, v_cs_865_);
return v___x_873_;
}
else
{
lean_object* v___x_874_; uint8_t v___x_875_; 
v___x_874_ = lean_array_get_size(v_bs_863_);
v___x_875_ = lean_nat_dec_lt(v_i_864_, v___x_874_);
if (v___x_875_ == 0)
{
lean_object* v___x_876_; 
lean_dec(v_i_864_);
lean_dec_ref(v_f_861_);
v___x_876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_876_, 0, v_cs_865_);
return v___x_876_;
}
else
{
lean_object* v_a_877_; lean_object* v_b_878_; size_t v_sz_879_; size_t v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; 
v_a_877_ = lean_array_fget_borrowed(v_as_862_, v_i_864_);
v_b_878_ = lean_array_fget_borrowed(v_bs_863_, v_i_864_);
v_sz_879_ = lean_array_size(v_b_878_);
v___x_880_ = ((size_t)0ULL);
lean_inc(v_b_878_);
v___x_881_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__13(v_xs_860_, v_sz_879_, v___x_880_, v_b_878_);
lean_inc_ref(v_f_861_);
lean_inc(v___y_869_);
lean_inc_ref(v___y_868_);
lean_inc(v___y_867_);
lean_inc_ref(v___y_866_);
lean_inc(v_a_877_);
v___x_882_ = lean_apply_7(v_f_861_, v_a_877_, v___x_881_, v___y_866_, v___y_867_, v___y_868_, v___y_869_, lean_box(0));
if (lean_obj_tag(v___x_882_) == 0)
{
lean_object* v_a_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; 
v_a_883_ = lean_ctor_get(v___x_882_, 0);
lean_inc(v_a_883_);
lean_dec_ref(v___x_882_);
v___x_884_ = lean_unsigned_to_nat(1u);
v___x_885_ = lean_nat_add(v_i_864_, v___x_884_);
lean_dec(v_i_864_);
v___x_886_ = lean_array_push(v_cs_865_, v_a_883_);
v_i_864_ = v___x_885_;
v_cs_865_ = v___x_886_;
goto _start;
}
else
{
lean_object* v_a_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_895_; 
lean_dec_ref(v_cs_865_);
lean_dec(v_i_864_);
lean_dec_ref(v_f_861_);
v_a_888_ = lean_ctor_get(v___x_882_, 0);
v_isSharedCheck_895_ = !lean_is_exclusive(v___x_882_);
if (v_isSharedCheck_895_ == 0)
{
v___x_890_ = v___x_882_;
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_a_888_);
lean_dec(v___x_882_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v___x_893_; 
if (v_isShared_891_ == 0)
{
v___x_893_ = v___x_890_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v_a_888_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15___redArg___boxed(lean_object* v_xs_896_, lean_object* v_f_897_, lean_object* v_as_898_, lean_object* v_bs_899_, lean_object* v_i_900_, lean_object* v_cs_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_){
_start:
{
lean_object* v_res_907_; 
v_res_907_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15___redArg(v_xs_896_, v_f_897_, v_as_898_, v_bs_899_, v_i_900_, v_cs_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_);
lean_dec(v___y_905_);
lean_dec_ref(v___y_904_);
lean_dec(v___y_903_);
lean_dec_ref(v___y_902_);
lean_dec_ref(v_bs_899_);
lean_dec_ref(v_as_898_);
lean_dec_ref(v_xs_896_);
return v_res_907_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; 
v___x_911_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__2));
v___x_912_ = lean_unsigned_to_nat(2u);
v___x_913_ = lean_unsigned_to_nat(73u);
v___x_914_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__1));
v___x_915_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__0));
v___x_916_ = l_mkPanicMessageWithDecl(v___x_915_, v___x_914_, v___x_913_, v___x_912_, v___x_911_);
return v___x_916_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_918_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__4));
v___x_919_ = lean_unsigned_to_nat(2u);
v___x_920_ = lean_unsigned_to_nat(74u);
v___x_921_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__1));
v___x_922_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__0));
v___x_923_ = l_mkPanicMessageWithDecl(v___x_922_, v___x_921_, v___x_920_, v___x_919_, v___x_918_);
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg(lean_object* v_f_926_, lean_object* v_positions_927_, lean_object* v_ys_928_, lean_object* v_xs_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_){
_start:
{
lean_object* v___x_935_; lean_object* v___x_936_; uint8_t v___x_937_; 
v___x_935_ = lean_array_get_size(v_positions_927_);
v___x_936_ = lean_array_get_size(v_ys_928_);
v___x_937_ = lean_nat_dec_eq(v___x_935_, v___x_936_);
if (v___x_937_ == 0)
{
lean_object* v___x_938_; lean_object* v___x_939_; 
lean_dec_ref(v_f_926_);
v___x_938_ = lean_obj_once(&l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__3, &l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__3_once, _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__3);
v___x_939_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg(v___x_938_, v___y_930_, v___y_931_, v___y_932_, v___y_933_);
return v___x_939_;
}
else
{
lean_object* v___x_940_; lean_object* v___x_941_; uint8_t v___x_942_; 
v___x_940_ = l_Lean_Elab_Structural_Positions_numIndices(v_positions_927_);
v___x_941_ = lean_array_get_size(v_xs_929_);
v___x_942_ = lean_nat_dec_eq(v___x_940_, v___x_941_);
lean_dec(v___x_940_);
if (v___x_942_ == 0)
{
lean_object* v___x_943_; lean_object* v___x_944_; 
lean_dec_ref(v_f_926_);
v___x_943_ = lean_obj_once(&l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__5, &l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__5_once, _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__5);
v___x_944_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg(v___x_943_, v___y_930_, v___y_931_, v___y_932_, v___y_933_);
return v___x_944_;
}
else
{
lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_945_ = lean_unsigned_to_nat(0u);
v___x_946_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__6));
v___x_947_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15___redArg(v_xs_929_, v_f_926_, v_ys_928_, v_positions_927_, v___x_945_, v___x_946_, v___y_930_, v___y_931_, v___y_932_, v___y_933_);
return v___x_947_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___boxed(lean_object* v_f_948_, lean_object* v_positions_949_, lean_object* v_ys_950_, lean_object* v_xs_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_){
_start:
{
lean_object* v_res_957_; 
v_res_957_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg(v_f_948_, v_positions_949_, v_ys_950_, v_xs_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_);
lean_dec(v___y_955_);
lean_dec_ref(v___y_954_);
lean_dec(v___y_953_);
lean_dec_ref(v___y_952_);
lean_dec_ref(v_xs_951_);
lean_dec_ref(v_ys_950_);
lean_dec_ref(v_positions_949_);
return v_res_957_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg(lean_object* v___x_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_funTypes_961_, lean_object* v_as_962_, lean_object* v_i_963_, lean_object* v_j_964_, lean_object* v_bs_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_){
_start:
{
lean_object* v_zero_971_; uint8_t v_isZero_972_; 
v_zero_971_ = lean_unsigned_to_nat(0u);
v_isZero_972_ = lean_nat_dec_eq(v_i_963_, v_zero_971_);
if (v_isZero_972_ == 1)
{
lean_object* v___x_973_; 
lean_dec(v_j_964_);
lean_dec(v_i_963_);
lean_dec_ref(v_funTypes_961_);
lean_dec_ref(v_a_960_);
lean_dec_ref(v_a_959_);
lean_dec_ref(v___x_958_);
v___x_973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_973_, 0, v_bs_965_);
return v___x_973_;
}
else
{
lean_object* v___x_974_; lean_object* v_fst_975_; lean_object* v_snd_976_; lean_object* v___x_977_; 
v___x_974_ = lean_array_fget_borrowed(v_as_962_, v_j_964_);
v_fst_975_ = lean_ctor_get(v___x_974_, 0);
v_snd_976_ = lean_ctor_get(v___x_974_, 1);
lean_inc(v_snd_976_);
lean_inc(v_fst_975_);
lean_inc_ref(v_funTypes_961_);
lean_inc_ref(v_a_960_);
lean_inc_ref(v_a_959_);
lean_inc(v_j_964_);
lean_inc_ref(v___x_958_);
v___x_977_ = l_Lean_Elab_Structural_mkBRecOnApp(v___x_958_, v_j_964_, v_a_959_, v_a_960_, v_funTypes_961_, v_fst_975_, v_snd_976_, v___y_966_, v___y_967_, v___y_968_, v___y_969_);
if (lean_obj_tag(v___x_977_) == 0)
{
lean_object* v_a_978_; lean_object* v_one_979_; lean_object* v_n_980_; lean_object* v___x_981_; lean_object* v___x_982_; 
v_a_978_ = lean_ctor_get(v___x_977_, 0);
lean_inc(v_a_978_);
lean_dec_ref(v___x_977_);
v_one_979_ = lean_unsigned_to_nat(1u);
v_n_980_ = lean_nat_sub(v_i_963_, v_one_979_);
lean_dec(v_i_963_);
v___x_981_ = lean_nat_add(v_j_964_, v_one_979_);
lean_dec(v_j_964_);
v___x_982_ = lean_array_push(v_bs_965_, v_a_978_);
v_i_963_ = v_n_980_;
v_j_964_ = v___x_981_;
v_bs_965_ = v___x_982_;
goto _start;
}
else
{
lean_object* v_a_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_991_; 
lean_dec_ref(v_bs_965_);
lean_dec(v_j_964_);
lean_dec(v_i_963_);
lean_dec_ref(v_funTypes_961_);
lean_dec_ref(v_a_960_);
lean_dec_ref(v_a_959_);
lean_dec_ref(v___x_958_);
v_a_984_ = lean_ctor_get(v___x_977_, 0);
v_isSharedCheck_991_ = !lean_is_exclusive(v___x_977_);
if (v_isSharedCheck_991_ == 0)
{
v___x_986_ = v___x_977_;
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_a_984_);
lean_dec(v___x_977_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v___x_989_; 
if (v_isShared_987_ == 0)
{
v___x_989_ = v___x_986_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v_a_984_);
v___x_989_ = v_reuseFailAlloc_990_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
return v___x_989_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg___boxed(lean_object* v___x_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_funTypes_995_, lean_object* v_as_996_, lean_object* v_i_997_, lean_object* v_j_998_, lean_object* v_bs_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_){
_start:
{
lean_object* v_res_1005_; 
v_res_1005_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg(v___x_992_, v_a_993_, v_a_994_, v_funTypes_995_, v_as_996_, v_i_997_, v_j_998_, v_bs_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_);
lean_dec(v___y_1003_);
lean_dec_ref(v___y_1002_);
lean_dec(v___y_1001_);
lean_dec_ref(v___y_1000_);
lean_dec_ref(v_as_996_);
return v_res_1005_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16_spec__29___redArg(lean_object* v_declName_1006_, uint8_t v_s_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_){
_start:
{
lean_object* v___x_1011_; lean_object* v_env_1012_; lean_object* v_nextMacroScope_1013_; lean_object* v_ngen_1014_; lean_object* v_auxDeclNGen_1015_; lean_object* v_traceState_1016_; lean_object* v_messages_1017_; lean_object* v_infoState_1018_; lean_object* v_snapshotTasks_1019_; lean_object* v_newDecls_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1049_; 
v___x_1011_ = lean_st_ref_take(v___y_1009_);
v_env_1012_ = lean_ctor_get(v___x_1011_, 0);
v_nextMacroScope_1013_ = lean_ctor_get(v___x_1011_, 1);
v_ngen_1014_ = lean_ctor_get(v___x_1011_, 2);
v_auxDeclNGen_1015_ = lean_ctor_get(v___x_1011_, 3);
v_traceState_1016_ = lean_ctor_get(v___x_1011_, 4);
v_messages_1017_ = lean_ctor_get(v___x_1011_, 6);
v_infoState_1018_ = lean_ctor_get(v___x_1011_, 7);
v_snapshotTasks_1019_ = lean_ctor_get(v___x_1011_, 8);
v_newDecls_1020_ = lean_ctor_get(v___x_1011_, 9);
v_isSharedCheck_1049_ = !lean_is_exclusive(v___x_1011_);
if (v_isSharedCheck_1049_ == 0)
{
lean_object* v_unused_1050_; 
v_unused_1050_ = lean_ctor_get(v___x_1011_, 5);
lean_dec(v_unused_1050_);
v___x_1022_ = v___x_1011_;
v_isShared_1023_ = v_isSharedCheck_1049_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_newDecls_1020_);
lean_inc(v_snapshotTasks_1019_);
lean_inc(v_infoState_1018_);
lean_inc(v_messages_1017_);
lean_inc(v_traceState_1016_);
lean_inc(v_auxDeclNGen_1015_);
lean_inc(v_ngen_1014_);
lean_inc(v_nextMacroScope_1013_);
lean_inc(v_env_1012_);
lean_dec(v___x_1011_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1049_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
uint8_t v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1029_; 
v___x_1024_ = 0;
v___x_1025_ = lean_box(0);
v___x_1026_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_1012_, v_declName_1006_, v_s_1007_, v___x_1024_, v___x_1025_);
v___x_1027_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__2);
if (v_isShared_1023_ == 0)
{
lean_ctor_set(v___x_1022_, 5, v___x_1027_);
lean_ctor_set(v___x_1022_, 0, v___x_1026_);
v___x_1029_ = v___x_1022_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v___x_1026_);
lean_ctor_set(v_reuseFailAlloc_1048_, 1, v_nextMacroScope_1013_);
lean_ctor_set(v_reuseFailAlloc_1048_, 2, v_ngen_1014_);
lean_ctor_set(v_reuseFailAlloc_1048_, 3, v_auxDeclNGen_1015_);
lean_ctor_set(v_reuseFailAlloc_1048_, 4, v_traceState_1016_);
lean_ctor_set(v_reuseFailAlloc_1048_, 5, v___x_1027_);
lean_ctor_set(v_reuseFailAlloc_1048_, 6, v_messages_1017_);
lean_ctor_set(v_reuseFailAlloc_1048_, 7, v_infoState_1018_);
lean_ctor_set(v_reuseFailAlloc_1048_, 8, v_snapshotTasks_1019_);
lean_ctor_set(v_reuseFailAlloc_1048_, 9, v_newDecls_1020_);
v___x_1029_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v_mctx_1032_; lean_object* v_zetaDeltaFVarIds_1033_; lean_object* v_postponed_1034_; lean_object* v_diag_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1046_; 
v___x_1030_ = lean_st_ref_set(v___y_1009_, v___x_1029_);
v___x_1031_ = lean_st_ref_take(v___y_1008_);
v_mctx_1032_ = lean_ctor_get(v___x_1031_, 0);
v_zetaDeltaFVarIds_1033_ = lean_ctor_get(v___x_1031_, 2);
v_postponed_1034_ = lean_ctor_get(v___x_1031_, 3);
v_diag_1035_ = lean_ctor_get(v___x_1031_, 4);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_1031_);
if (v_isSharedCheck_1046_ == 0)
{
lean_object* v_unused_1047_; 
v_unused_1047_ = lean_ctor_get(v___x_1031_, 1);
lean_dec(v_unused_1047_);
v___x_1037_ = v___x_1031_;
v_isShared_1038_ = v_isSharedCheck_1046_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_diag_1035_);
lean_inc(v_postponed_1034_);
lean_inc(v_zetaDeltaFVarIds_1033_);
lean_inc(v_mctx_1032_);
lean_dec(v___x_1031_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1046_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v___x_1039_; lean_object* v___x_1041_; 
v___x_1039_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__3, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__3);
if (v_isShared_1038_ == 0)
{
lean_ctor_set(v___x_1037_, 1, v___x_1039_);
v___x_1041_ = v___x_1037_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v_mctx_1032_);
lean_ctor_set(v_reuseFailAlloc_1045_, 1, v___x_1039_);
lean_ctor_set(v_reuseFailAlloc_1045_, 2, v_zetaDeltaFVarIds_1033_);
lean_ctor_set(v_reuseFailAlloc_1045_, 3, v_postponed_1034_);
lean_ctor_set(v_reuseFailAlloc_1045_, 4, v_diag_1035_);
v___x_1041_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1042_ = lean_st_ref_set(v___y_1008_, v___x_1041_);
v___x_1043_ = lean_box(0);
v___x_1044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1044_, 0, v___x_1043_);
return v___x_1044_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16_spec__29___redArg___boxed(lean_object* v_declName_1051_, lean_object* v_s_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_){
_start:
{
uint8_t v_s_boxed_1056_; lean_object* v_res_1057_; 
v_s_boxed_1056_ = lean_unbox(v_s_1052_);
v_res_1057_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16_spec__29___redArg(v_declName_1051_, v_s_boxed_1056_, v___y_1053_, v___y_1054_);
lean_dec(v___y_1054_);
lean_dec(v___y_1053_);
return v_res_1057_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16(lean_object* v_declName_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_){
_start:
{
uint8_t v___x_1064_; lean_object* v___x_1065_; 
v___x_1064_ = 0;
v___x_1065_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16_spec__29___redArg(v_declName_1058_, v___x_1064_, v___y_1060_, v___y_1062_);
return v___x_1065_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16___boxed(lean_object* v_declName_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_){
_start:
{
lean_object* v_res_1072_; 
v_res_1072_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16(v_declName_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_);
lean_dec(v___y_1070_);
lean_dec_ref(v___y_1069_);
lean_dec(v___y_1068_);
lean_dec_ref(v___y_1067_);
return v_res_1072_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg(lean_object* v_xs_1076_, uint8_t v_a_1077_, lean_object* v_preDefs_1078_, lean_object* v___x_1079_, lean_object* v_as_1080_, lean_object* v_i_1081_, lean_object* v_j_1082_, lean_object* v_bs_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_){
_start:
{
lean_object* v_zero_1089_; uint8_t v_isZero_1090_; 
v_zero_1089_ = lean_unsigned_to_nat(0u);
v_isZero_1090_ = lean_nat_dec_eq(v_i_1081_, v_zero_1089_);
if (v_isZero_1090_ == 1)
{
lean_object* v___x_1091_; 
lean_dec(v_j_1082_);
lean_dec(v_i_1081_);
lean_dec(v___x_1079_);
v___x_1091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1091_, 0, v_bs_1083_);
return v___x_1091_;
}
else
{
uint8_t v___x_1092_; lean_object* v_one_1093_; lean_object* v_n_1094_; lean_object* v_a_1096_; lean_object* v___y_1101_; lean_object* v___x_1111_; uint8_t v___x_1112_; lean_object* v___x_1113_; 
v___x_1092_ = 1;
v_one_1093_ = lean_unsigned_to_nat(1u);
v_n_1094_ = lean_nat_sub(v_i_1081_, v_one_1093_);
lean_dec(v_i_1081_);
v___x_1111_ = lean_array_fget_borrowed(v_as_1080_, v_j_1082_);
v___x_1112_ = 1;
lean_inc(v___x_1111_);
v___x_1113_ = l_Lean_Meta_mkLambdaFVars(v_xs_1076_, v___x_1111_, v_a_1077_, v___x_1092_, v_a_1077_, v___x_1092_, v___x_1112_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_);
if (lean_obj_tag(v___x_1113_) == 0)
{
lean_object* v_a_1114_; lean_object* v___x_1115_; 
v_a_1114_ = lean_ctor_get(v___x_1113_, 0);
lean_inc(v_a_1114_);
lean_dec_ref(v___x_1113_);
v___x_1115_ = l_Lean_Elab_eraseRecAppSyntaxExpr(v_a_1114_, v___y_1086_, v___y_1087_);
if (lean_obj_tag(v___x_1115_) == 0)
{
lean_object* v_a_1116_; lean_object* v___x_1117_; 
v_a_1116_ = lean_ctor_get(v___x_1115_, 0);
lean_inc_n(v_a_1116_, 2);
lean_dec_ref(v___x_1115_);
lean_inc(v___y_1087_);
lean_inc_ref(v___y_1086_);
lean_inc(v___y_1085_);
lean_inc_ref(v___y_1084_);
v___x_1117_ = lean_infer_type(v_a_1116_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_);
if (lean_obj_tag(v___x_1117_) == 0)
{
lean_object* v_a_1118_; lean_object* v___x_1119_; 
v_a_1118_ = lean_ctor_get(v___x_1117_, 0);
lean_inc(v_a_1118_);
lean_dec_ref(v___x_1117_);
v___x_1119_ = l_Lean_Meta_letToHave(v_a_1118_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_);
if (lean_obj_tag(v___x_1119_) == 0)
{
lean_object* v_a_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1195_; 
v_a_1120_ = lean_ctor_get(v___x_1119_, 0);
v_isSharedCheck_1195_ = !lean_is_exclusive(v___x_1119_);
if (v_isSharedCheck_1195_ == 0)
{
v___x_1122_ = v___x_1119_;
v_isShared_1123_ = v_isSharedCheck_1195_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_a_1120_);
lean_dec(v___x_1119_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1195_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v_modifiers_1127_; lean_object* v_levelParams_1128_; lean_object* v_declName_1129_; lean_object* v_env_1130_; uint8_t v_isUnsafe_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; uint32_t v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; uint8_t v___y_1138_; 
v___x_1124_ = lean_st_ref_get(v___y_1087_);
v___x_1125_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_1126_ = lean_array_get_borrowed(v___x_1125_, v_preDefs_1078_, v_j_1082_);
v_modifiers_1127_ = lean_ctor_get(v___x_1126_, 2);
v_levelParams_1128_ = lean_ctor_get(v___x_1126_, 1);
v_declName_1129_ = lean_ctor_get(v___x_1126_, 3);
v_env_1130_ = lean_ctor_get(v___x_1124_, 0);
lean_inc_ref(v_env_1130_);
lean_dec(v___x_1124_);
v_isUnsafe_1131_ = lean_ctor_get_uint8(v_modifiers_1127_, sizeof(void*)*3 + 4);
v___x_1132_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg___closed__1));
lean_inc(v_declName_1129_);
v___x_1133_ = l_Lean_Name_append(v_declName_1129_, v___x_1132_);
lean_inc(v_a_1116_);
v___x_1134_ = l_Lean_getMaxHeight(v_env_1130_, v_a_1116_);
lean_inc(v_levelParams_1128_);
lean_inc(v___x_1133_);
v___x_1135_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1135_, 0, v___x_1133_);
lean_ctor_set(v___x_1135_, 1, v_levelParams_1128_);
lean_ctor_set(v___x_1135_, 2, v_a_1120_);
v___x_1136_ = lean_box(1);
if (v_isUnsafe_1131_ == 0)
{
uint8_t v___x_1193_; 
v___x_1193_ = 1;
v___y_1138_ = v___x_1193_;
goto v___jp_1137_;
}
else
{
uint8_t v___x_1194_; 
v___x_1194_ = 0;
v___y_1138_ = v___x_1194_;
goto v___jp_1137_;
}
v___jp_1137_:
{
lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1143_; 
v___x_1139_ = lean_box(0);
lean_inc(v___x_1133_);
v___x_1140_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1140_, 0, v___x_1133_);
lean_ctor_set(v___x_1140_, 1, v___x_1139_);
v___x_1141_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1141_, 0, v___x_1135_);
lean_ctor_set(v___x_1141_, 1, v_a_1116_);
lean_ctor_set(v___x_1141_, 2, v___x_1136_);
lean_ctor_set(v___x_1141_, 3, v___x_1140_);
lean_ctor_set_uint8(v___x_1141_, sizeof(void*)*4, v___y_1138_);
if (v_isShared_1123_ == 0)
{
lean_ctor_set_tag(v___x_1122_, 1);
lean_ctor_set(v___x_1122_, 0, v___x_1141_);
v___x_1143_ = v___x_1122_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v___x_1141_);
v___x_1143_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
lean_object* v___x_1144_; 
v___x_1144_ = l_Lean_addDecl(v___x_1143_, v_a_1077_, v___y_1086_, v___y_1087_);
if (lean_obj_tag(v___x_1144_) == 0)
{
lean_object* v___x_1145_; lean_object* v_env_1146_; lean_object* v_nextMacroScope_1147_; lean_object* v_ngen_1148_; lean_object* v_auxDeclNGen_1149_; lean_object* v_traceState_1150_; lean_object* v_messages_1151_; lean_object* v_infoState_1152_; lean_object* v_snapshotTasks_1153_; lean_object* v_newDecls_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1182_; 
lean_dec_ref(v___x_1144_);
v___x_1145_ = lean_st_ref_take(v___y_1087_);
v_env_1146_ = lean_ctor_get(v___x_1145_, 0);
v_nextMacroScope_1147_ = lean_ctor_get(v___x_1145_, 1);
v_ngen_1148_ = lean_ctor_get(v___x_1145_, 2);
v_auxDeclNGen_1149_ = lean_ctor_get(v___x_1145_, 3);
v_traceState_1150_ = lean_ctor_get(v___x_1145_, 4);
v_messages_1151_ = lean_ctor_get(v___x_1145_, 6);
v_infoState_1152_ = lean_ctor_get(v___x_1145_, 7);
v_snapshotTasks_1153_ = lean_ctor_get(v___x_1145_, 8);
v_newDecls_1154_ = lean_ctor_get(v___x_1145_, 9);
v_isSharedCheck_1182_ = !lean_is_exclusive(v___x_1145_);
if (v_isSharedCheck_1182_ == 0)
{
lean_object* v_unused_1183_; 
v_unused_1183_ = lean_ctor_get(v___x_1145_, 5);
lean_dec(v_unused_1183_);
v___x_1156_ = v___x_1145_;
v_isShared_1157_ = v_isSharedCheck_1182_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_newDecls_1154_);
lean_inc(v_snapshotTasks_1153_);
lean_inc(v_infoState_1152_);
lean_inc(v_messages_1151_);
lean_inc(v_traceState_1150_);
lean_inc(v_auxDeclNGen_1149_);
lean_inc(v_ngen_1148_);
lean_inc(v_nextMacroScope_1147_);
lean_inc(v_env_1146_);
lean_dec(v___x_1145_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1182_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1161_; 
lean_inc(v___x_1133_);
v___x_1158_ = l_Lean_setDefHeightOverride(v_env_1146_, v___x_1133_, v___x_1134_);
v___x_1159_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__2);
if (v_isShared_1157_ == 0)
{
lean_ctor_set(v___x_1156_, 5, v___x_1159_);
lean_ctor_set(v___x_1156_, 0, v___x_1158_);
v___x_1161_ = v___x_1156_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v___x_1158_);
lean_ctor_set(v_reuseFailAlloc_1181_, 1, v_nextMacroScope_1147_);
lean_ctor_set(v_reuseFailAlloc_1181_, 2, v_ngen_1148_);
lean_ctor_set(v_reuseFailAlloc_1181_, 3, v_auxDeclNGen_1149_);
lean_ctor_set(v_reuseFailAlloc_1181_, 4, v_traceState_1150_);
lean_ctor_set(v_reuseFailAlloc_1181_, 5, v___x_1159_);
lean_ctor_set(v_reuseFailAlloc_1181_, 6, v_messages_1151_);
lean_ctor_set(v_reuseFailAlloc_1181_, 7, v_infoState_1152_);
lean_ctor_set(v_reuseFailAlloc_1181_, 8, v_snapshotTasks_1153_);
lean_ctor_set(v_reuseFailAlloc_1181_, 9, v_newDecls_1154_);
v___x_1161_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v_mctx_1164_; lean_object* v_zetaDeltaFVarIds_1165_; lean_object* v_postponed_1166_; lean_object* v_diag_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1179_; 
v___x_1162_ = lean_st_ref_set(v___y_1087_, v___x_1161_);
v___x_1163_ = lean_st_ref_take(v___y_1085_);
v_mctx_1164_ = lean_ctor_get(v___x_1163_, 0);
v_zetaDeltaFVarIds_1165_ = lean_ctor_get(v___x_1163_, 2);
v_postponed_1166_ = lean_ctor_get(v___x_1163_, 3);
v_diag_1167_ = lean_ctor_get(v___x_1163_, 4);
v_isSharedCheck_1179_ = !lean_is_exclusive(v___x_1163_);
if (v_isSharedCheck_1179_ == 0)
{
lean_object* v_unused_1180_; 
v_unused_1180_ = lean_ctor_get(v___x_1163_, 1);
lean_dec(v_unused_1180_);
v___x_1169_ = v___x_1163_;
v_isShared_1170_ = v_isSharedCheck_1179_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_diag_1167_);
lean_inc(v_postponed_1166_);
lean_inc(v_zetaDeltaFVarIds_1165_);
lean_inc(v_mctx_1164_);
lean_dec(v___x_1163_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1179_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v___x_1171_; lean_object* v___x_1173_; 
v___x_1171_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__3, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__3);
if (v_isShared_1170_ == 0)
{
lean_ctor_set(v___x_1169_, 1, v___x_1171_);
v___x_1173_ = v___x_1169_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v_mctx_1164_);
lean_ctor_set(v_reuseFailAlloc_1178_, 1, v___x_1171_);
lean_ctor_set(v_reuseFailAlloc_1178_, 2, v_zetaDeltaFVarIds_1165_);
lean_ctor_set(v_reuseFailAlloc_1178_, 3, v_postponed_1166_);
lean_ctor_set(v_reuseFailAlloc_1178_, 4, v_diag_1167_);
v___x_1173_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; 
v___x_1174_ = lean_st_ref_set(v___y_1085_, v___x_1173_);
lean_inc(v___x_1133_);
v___x_1175_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16(v___x_1133_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_);
lean_dec_ref(v___x_1175_);
lean_inc(v___x_1079_);
v___x_1176_ = l_Lean_mkConst(v___x_1133_, v___x_1079_);
v___x_1177_ = l_Lean_mkAppN(v___x_1176_, v_xs_1076_);
v_a_1096_ = v___x_1177_;
goto v___jp_1095_;
}
}
}
}
}
else
{
lean_object* v_a_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1191_; 
lean_dec(v___x_1133_);
lean_dec(v_n_1094_);
lean_dec_ref(v_bs_1083_);
lean_dec(v_j_1082_);
lean_dec(v___x_1079_);
v_a_1184_ = lean_ctor_get(v___x_1144_, 0);
v_isSharedCheck_1191_ = !lean_is_exclusive(v___x_1144_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1186_ = v___x_1144_;
v_isShared_1187_ = v_isSharedCheck_1191_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_a_1184_);
lean_dec(v___x_1144_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1191_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v___x_1189_; 
if (v_isShared_1187_ == 0)
{
v___x_1189_ = v___x_1186_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v_a_1184_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
return v___x_1189_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_1116_);
v___y_1101_ = v___x_1119_;
goto v___jp_1100_;
}
}
else
{
lean_dec(v_a_1116_);
v___y_1101_ = v___x_1117_;
goto v___jp_1100_;
}
}
else
{
v___y_1101_ = v___x_1115_;
goto v___jp_1100_;
}
}
else
{
v___y_1101_ = v___x_1113_;
goto v___jp_1100_;
}
v___jp_1095_:
{
lean_object* v___x_1097_; lean_object* v___x_1098_; 
v___x_1097_ = lean_nat_add(v_j_1082_, v_one_1093_);
lean_dec(v_j_1082_);
v___x_1098_ = lean_array_push(v_bs_1083_, v_a_1096_);
v_i_1081_ = v_n_1094_;
v_j_1082_ = v___x_1097_;
v_bs_1083_ = v___x_1098_;
goto _start;
}
v___jp_1100_:
{
if (lean_obj_tag(v___y_1101_) == 0)
{
lean_object* v_a_1102_; 
v_a_1102_ = lean_ctor_get(v___y_1101_, 0);
lean_inc(v_a_1102_);
lean_dec_ref(v___y_1101_);
v_a_1096_ = v_a_1102_;
goto v___jp_1095_;
}
else
{
lean_object* v_a_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1110_; 
lean_dec(v_n_1094_);
lean_dec_ref(v_bs_1083_);
lean_dec(v_j_1082_);
lean_dec(v___x_1079_);
v_a_1103_ = lean_ctor_get(v___y_1101_, 0);
v_isSharedCheck_1110_ = !lean_is_exclusive(v___y_1101_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1105_ = v___y_1101_;
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_a_1103_);
lean_dec(v___y_1101_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v___x_1108_; 
if (v_isShared_1106_ == 0)
{
v___x_1108_ = v___x_1105_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v_a_1103_);
v___x_1108_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
return v___x_1108_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg___boxed(lean_object* v_xs_1196_, lean_object* v_a_1197_, lean_object* v_preDefs_1198_, lean_object* v___x_1199_, lean_object* v_as_1200_, lean_object* v_i_1201_, lean_object* v_j_1202_, lean_object* v_bs_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_){
_start:
{
uint8_t v_a_28628__boxed_1209_; lean_object* v_res_1210_; 
v_a_28628__boxed_1209_ = lean_unbox(v_a_1197_);
v_res_1210_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg(v_xs_1196_, v_a_28628__boxed_1209_, v_preDefs_1198_, v___x_1199_, v_as_1200_, v_i_1201_, v_j_1202_, v_bs_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_);
lean_dec(v___y_1207_);
lean_dec_ref(v___y_1206_);
lean_dec(v___y_1205_);
lean_dec_ref(v___y_1204_);
lean_dec_ref(v_as_1200_);
lean_dec_ref(v_preDefs_1198_);
lean_dec_ref(v_xs_1196_);
return v_res_1210_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__2(void){
_start:
{
lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; 
v___x_1214_ = lean_box(0);
v___x_1215_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__1));
v___x_1216_ = l_Lean_Expr_const___override(v___x_1215_, v___x_1214_);
return v___x_1216_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__4(void){
_start:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; 
v___x_1218_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__3));
v___x_1219_ = l_Lean_stringToMessageData(v___x_1218_);
return v___x_1219_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__6(void){
_start:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; 
v___x_1221_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__5));
v___x_1222_ = l_Lean_stringToMessageData(v___x_1221_);
return v___x_1222_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__8(void){
_start:
{
lean_object* v___x_1224_; lean_object* v___x_1225_; 
v___x_1224_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__7));
v___x_1225_ = l_Lean_stringToMessageData(v___x_1224_);
return v___x_1225_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__10(void){
_start:
{
lean_object* v___x_1227_; lean_object* v___x_1228_; 
v___x_1227_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__9));
v___x_1228_ = l_Lean_stringToMessageData(v___x_1227_);
return v___x_1228_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__12(void){
_start:
{
lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___x_1230_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__11));
v___x_1231_ = l_Lean_stringToMessageData(v___x_1230_);
return v___x_1231_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2(lean_object* v___f_1232_, lean_object* v_recArgInfos_1233_, lean_object* v_a_1234_, lean_object* v___x_1235_, lean_object* v___x_1236_, lean_object* v_fixedParamPerms_1237_, lean_object* v_xs_1238_, lean_object* v_preDefs_1239_, lean_object* v_numIndices_1240_, lean_object* v___f_1241_, lean_object* v___x_1242_, uint8_t v_a_1243_, lean_object* v_funTypes_1244_, lean_object* v_motives_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_){
_start:
{
lean_object* v___y_1252_; lean_object* v___y_1253_; lean_object* v___y_1254_; lean_object* v___y_1255_; lean_object* v___y_1256_; lean_object* v___y_1257_; lean_object* v___y_1294_; lean_object* v_FArgs_1295_; lean_object* v___y_1296_; lean_object* v___y_1297_; lean_object* v___y_1298_; lean_object* v___y_1299_; lean_object* v___y_1350_; lean_object* v___y_1351_; lean_object* v___y_1352_; lean_object* v___y_1353_; lean_object* v___y_1354_; lean_object* v___y_1355_; lean_object* v___y_1374_; lean_object* v___y_1375_; lean_object* v___y_1376_; lean_object* v___y_1377_; lean_object* v___y_1378_; lean_object* v___y_1379_; lean_object* v___y_1419_; lean_object* v___y_1420_; lean_object* v___y_1421_; lean_object* v___y_1422_; lean_object* v___x_1469_; 
lean_inc_ref(v___f_1232_);
lean_inc(v___y_1249_);
lean_inc_ref(v___y_1248_);
lean_inc(v___y_1247_);
lean_inc_ref(v___y_1246_);
v___x_1469_ = lean_apply_5(v___f_1232_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, lean_box(0));
if (lean_obj_tag(v___x_1469_) == 0)
{
lean_object* v_a_1470_; uint8_t v___x_1471_; 
v_a_1470_ = lean_ctor_get(v___x_1469_, 0);
lean_inc(v_a_1470_);
lean_dec_ref(v___x_1469_);
v___x_1471_ = lean_unbox(v_a_1470_);
lean_dec(v_a_1470_);
if (v___x_1471_ == 0)
{
v___y_1419_ = v___y_1246_;
v___y_1420_ = v___y_1247_;
v___y_1421_ = v___y_1248_;
v___y_1422_ = v___y_1249_;
goto v___jp_1418_;
}
else
{
lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; 
v___x_1472_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__10, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__10);
lean_inc_ref(v_funTypes_1244_);
v___x_1473_ = lean_array_to_list(v_funTypes_1244_);
v___x_1474_ = lean_box(0);
v___x_1475_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_1473_, v___x_1474_);
v___x_1476_ = l_Lean_MessageData_ofList(v___x_1475_);
v___x_1477_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1477_, 0, v___x_1472_);
lean_ctor_set(v___x_1477_, 1, v___x_1476_);
v___x_1478_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__12, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__12_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__12);
v___x_1479_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1479_, 0, v___x_1477_);
lean_ctor_set(v___x_1479_, 1, v___x_1478_);
lean_inc_ref(v_motives_1245_);
v___x_1480_ = lean_array_to_list(v_motives_1245_);
v___x_1481_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_1480_, v___x_1474_);
v___x_1482_ = l_Lean_MessageData_ofList(v___x_1481_);
v___x_1483_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1483_, 0, v___x_1479_);
lean_ctor_set(v___x_1483_, 1, v___x_1482_);
lean_inc(v___x_1242_);
v___x_1484_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_1242_, v___x_1483_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_);
if (lean_obj_tag(v___x_1484_) == 0)
{
lean_dec_ref(v___x_1484_);
v___y_1419_ = v___y_1246_;
v___y_1420_ = v___y_1247_;
v___y_1421_ = v___y_1248_;
v___y_1422_ = v___y_1249_;
goto v___jp_1418_;
}
else
{
lean_object* v_a_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1492_; 
lean_dec_ref(v_motives_1245_);
lean_dec_ref(v_funTypes_1244_);
lean_dec(v___x_1242_);
lean_dec_ref(v___f_1241_);
lean_dec_ref(v_preDefs_1239_);
lean_dec_ref(v_xs_1238_);
lean_dec_ref(v_fixedParamPerms_1237_);
lean_dec(v___x_1236_);
lean_dec_ref(v___x_1235_);
lean_dec_ref(v_recArgInfos_1233_);
lean_dec_ref(v___f_1232_);
v_a_1485_ = lean_ctor_get(v___x_1484_, 0);
v_isSharedCheck_1492_ = !lean_is_exclusive(v___x_1484_);
if (v_isSharedCheck_1492_ == 0)
{
v___x_1487_ = v___x_1484_;
v_isShared_1488_ = v_isSharedCheck_1492_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_a_1485_);
lean_dec(v___x_1484_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1492_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
lean_object* v___x_1490_; 
if (v_isShared_1488_ == 0)
{
v___x_1490_ = v___x_1487_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v_a_1485_);
v___x_1490_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
return v___x_1490_;
}
}
}
}
}
else
{
lean_object* v_a_1493_; lean_object* v___x_1495_; uint8_t v_isShared_1496_; uint8_t v_isSharedCheck_1500_; 
lean_dec_ref(v_motives_1245_);
lean_dec_ref(v_funTypes_1244_);
lean_dec(v___x_1242_);
lean_dec_ref(v___f_1241_);
lean_dec_ref(v_preDefs_1239_);
lean_dec_ref(v_xs_1238_);
lean_dec_ref(v_fixedParamPerms_1237_);
lean_dec(v___x_1236_);
lean_dec_ref(v___x_1235_);
lean_dec_ref(v_recArgInfos_1233_);
lean_dec_ref(v___f_1232_);
v_a_1493_ = lean_ctor_get(v___x_1469_, 0);
v_isSharedCheck_1500_ = !lean_is_exclusive(v___x_1469_);
if (v_isSharedCheck_1500_ == 0)
{
v___x_1495_ = v___x_1469_;
v_isShared_1496_ = v_isSharedCheck_1500_;
goto v_resetjp_1494_;
}
else
{
lean_inc(v_a_1493_);
lean_dec(v___x_1469_);
v___x_1495_ = lean_box(0);
v_isShared_1496_ = v_isSharedCheck_1500_;
goto v_resetjp_1494_;
}
v_resetjp_1494_:
{
lean_object* v___x_1498_; 
if (v_isShared_1496_ == 0)
{
v___x_1498_ = v___x_1495_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v_a_1493_);
v___x_1498_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
return v___x_1498_;
}
}
}
v___jp_1251_:
{
lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1258_ = l_Array_zip___redArg(v_recArgInfos_1233_, v_a_1234_);
lean_dec_ref(v_recArgInfos_1233_);
v___x_1259_ = lean_array_get_size(v___x_1258_);
v___x_1260_ = lean_mk_empty_array_with_capacity(v___x_1259_);
lean_inc(v___x_1236_);
v___x_1261_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg(v___x_1235_, v___y_1252_, v___y_1253_, v_funTypes_1244_, v___x_1258_, v___x_1259_, v___x_1236_, v___x_1260_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_);
lean_dec_ref(v___x_1258_);
if (lean_obj_tag(v___x_1261_) == 0)
{
lean_object* v_a_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; 
v_a_1262_ = lean_ctor_get(v___x_1261_, 0);
lean_inc(v_a_1262_);
lean_dec_ref(v___x_1261_);
v___x_1263_ = l_Array_zip___redArg(v_a_1234_, v_a_1262_);
lean_dec(v_a_1262_);
v___x_1264_ = lean_array_get_size(v___x_1263_);
v___x_1265_ = lean_mk_empty_array_with_capacity(v___x_1264_);
lean_inc(v___x_1236_);
v___x_1266_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg(v_fixedParamPerms_1237_, v_xs_1238_, v___x_1263_, v___x_1264_, v___x_1236_, v___x_1265_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_);
lean_dec_ref(v___x_1263_);
if (lean_obj_tag(v___x_1266_) == 0)
{
lean_object* v_a_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1276_; 
v_a_1267_ = lean_ctor_get(v___x_1266_, 0);
v_isSharedCheck_1276_ = !lean_is_exclusive(v___x_1266_);
if (v_isSharedCheck_1276_ == 0)
{
v___x_1269_ = v___x_1266_;
v_isShared_1270_ = v_isSharedCheck_1276_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_a_1267_);
lean_dec(v___x_1266_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1276_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1274_; 
v___x_1271_ = lean_mk_empty_array_with_capacity(v___x_1236_);
v___x_1272_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9(v_preDefs_1239_, v_a_1267_, v___x_1236_, v___x_1271_);
lean_dec(v_a_1267_);
lean_dec_ref(v_preDefs_1239_);
if (v_isShared_1270_ == 0)
{
lean_ctor_set(v___x_1269_, 0, v___x_1272_);
v___x_1274_ = v___x_1269_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v___x_1272_);
v___x_1274_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
return v___x_1274_;
}
}
}
else
{
lean_object* v_a_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1284_; 
lean_dec_ref(v_preDefs_1239_);
lean_dec(v___x_1236_);
v_a_1277_ = lean_ctor_get(v___x_1266_, 0);
v_isSharedCheck_1284_ = !lean_is_exclusive(v___x_1266_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1279_ = v___x_1266_;
v_isShared_1280_ = v_isSharedCheck_1284_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_a_1277_);
lean_dec(v___x_1266_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1284_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v___x_1282_; 
if (v_isShared_1280_ == 0)
{
v___x_1282_ = v___x_1279_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v_a_1277_);
v___x_1282_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
return v___x_1282_;
}
}
}
}
else
{
lean_object* v_a_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1292_; 
lean_dec_ref(v_preDefs_1239_);
lean_dec_ref(v_xs_1238_);
lean_dec_ref(v_fixedParamPerms_1237_);
lean_dec(v___x_1236_);
v_a_1285_ = lean_ctor_get(v___x_1261_, 0);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1261_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1287_ = v___x_1261_;
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_a_1285_);
lean_dec(v___x_1261_);
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
v___jp_1293_:
{
lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; 
lean_inc_ref(v___y_1294_);
lean_inc(v___x_1236_);
v___x_1300_ = lean_apply_1(v___y_1294_, v___x_1236_);
v___x_1301_ = lean_unsigned_to_nat(1u);
v___x_1302_ = lean_nat_add(v_numIndices_1240_, v___x_1301_);
v___x_1303_ = lean_box(0);
v___x_1304_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__2);
v___x_1305_ = lean_mk_array(v___x_1302_, v___x_1304_);
v___x_1306_ = l_Lean_mkAppN(v___x_1300_, v___x_1305_);
lean_dec_ref(v___x_1305_);
v___x_1307_ = lean_array_get_size(v___x_1235_);
v___x_1308_ = l_Lean_Meta_inferArgumentTypesN(v___x_1307_, v___x_1306_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_);
if (lean_obj_tag(v___x_1308_) == 0)
{
lean_object* v_a_1309_; lean_object* v___x_1310_; 
v_a_1309_ = lean_ctor_get(v___x_1308_, 0);
lean_inc(v_a_1309_);
lean_dec_ref(v___x_1308_);
v___x_1310_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg(v___f_1241_, v___x_1235_, v_a_1309_, v_FArgs_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_);
lean_dec_ref(v_FArgs_1295_);
lean_dec(v_a_1309_);
if (lean_obj_tag(v___x_1310_) == 0)
{
lean_object* v_options_1311_; uint8_t v_hasTrace_1312_; 
v_options_1311_ = lean_ctor_get(v___y_1298_, 2);
v_hasTrace_1312_ = lean_ctor_get_uint8(v_options_1311_, sizeof(void*)*1);
if (v_hasTrace_1312_ == 0)
{
lean_object* v_a_1313_; 
lean_dec(v___x_1242_);
v_a_1313_ = lean_ctor_get(v___x_1310_, 0);
lean_inc(v_a_1313_);
lean_dec_ref(v___x_1310_);
v___y_1252_ = v___y_1294_;
v___y_1253_ = v_a_1313_;
v___y_1254_ = v___y_1296_;
v___y_1255_ = v___y_1297_;
v___y_1256_ = v___y_1298_;
v___y_1257_ = v___y_1299_;
goto v___jp_1251_;
}
else
{
lean_object* v_a_1314_; lean_object* v_inheritedTraceOptions_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; uint8_t v___x_1318_; 
v_a_1314_ = lean_ctor_get(v___x_1310_, 0);
lean_inc(v_a_1314_);
lean_dec_ref(v___x_1310_);
v_inheritedTraceOptions_1315_ = lean_ctor_get(v___y_1298_, 13);
v___x_1316_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0___closed__1));
lean_inc(v___x_1242_);
v___x_1317_ = l_Lean_Name_append(v___x_1316_, v___x_1242_);
v___x_1318_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1315_, v_options_1311_, v___x_1317_);
lean_dec(v___x_1317_);
if (v___x_1318_ == 0)
{
lean_dec(v___x_1242_);
v___y_1252_ = v___y_1294_;
v___y_1253_ = v_a_1314_;
v___y_1254_ = v___y_1296_;
v___y_1255_ = v___y_1297_;
v___y_1256_ = v___y_1298_;
v___y_1257_ = v___y_1299_;
goto v___jp_1251_;
}
else
{
lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; 
v___x_1319_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__4);
lean_inc(v_a_1314_);
v___x_1320_ = lean_array_to_list(v_a_1314_);
v___x_1321_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_1320_, v___x_1303_);
v___x_1322_ = l_Lean_MessageData_ofList(v___x_1321_);
v___x_1323_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1323_, 0, v___x_1319_);
lean_ctor_set(v___x_1323_, 1, v___x_1322_);
v___x_1324_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_1242_, v___x_1323_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_);
if (lean_obj_tag(v___x_1324_) == 0)
{
lean_dec_ref(v___x_1324_);
v___y_1252_ = v___y_1294_;
v___y_1253_ = v_a_1314_;
v___y_1254_ = v___y_1296_;
v___y_1255_ = v___y_1297_;
v___y_1256_ = v___y_1298_;
v___y_1257_ = v___y_1299_;
goto v___jp_1251_;
}
else
{
lean_object* v_a_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1332_; 
lean_dec(v_a_1314_);
lean_dec_ref(v___y_1294_);
lean_dec_ref(v_funTypes_1244_);
lean_dec_ref(v_preDefs_1239_);
lean_dec_ref(v_xs_1238_);
lean_dec_ref(v_fixedParamPerms_1237_);
lean_dec(v___x_1236_);
lean_dec_ref(v___x_1235_);
lean_dec_ref(v_recArgInfos_1233_);
v_a_1325_ = lean_ctor_get(v___x_1324_, 0);
v_isSharedCheck_1332_ = !lean_is_exclusive(v___x_1324_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1327_ = v___x_1324_;
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_a_1325_);
lean_dec(v___x_1324_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1330_; 
if (v_isShared_1328_ == 0)
{
v___x_1330_ = v___x_1327_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v_a_1325_);
v___x_1330_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
return v___x_1330_;
}
}
}
}
}
}
else
{
lean_object* v_a_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1340_; 
lean_dec_ref(v___y_1294_);
lean_dec_ref(v_funTypes_1244_);
lean_dec(v___x_1242_);
lean_dec_ref(v_preDefs_1239_);
lean_dec_ref(v_xs_1238_);
lean_dec_ref(v_fixedParamPerms_1237_);
lean_dec(v___x_1236_);
lean_dec_ref(v___x_1235_);
lean_dec_ref(v_recArgInfos_1233_);
v_a_1333_ = lean_ctor_get(v___x_1310_, 0);
v_isSharedCheck_1340_ = !lean_is_exclusive(v___x_1310_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1335_ = v___x_1310_;
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_a_1333_);
lean_dec(v___x_1310_);
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
else
{
lean_object* v_a_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1348_; 
lean_dec_ref(v_FArgs_1295_);
lean_dec_ref(v___y_1294_);
lean_dec_ref(v_funTypes_1244_);
lean_dec(v___x_1242_);
lean_dec_ref(v___f_1241_);
lean_dec_ref(v_preDefs_1239_);
lean_dec_ref(v_xs_1238_);
lean_dec_ref(v_fixedParamPerms_1237_);
lean_dec(v___x_1236_);
lean_dec_ref(v___x_1235_);
lean_dec_ref(v_recArgInfos_1233_);
v_a_1341_ = lean_ctor_get(v___x_1308_, 0);
v_isSharedCheck_1348_ = !lean_is_exclusive(v___x_1308_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1343_ = v___x_1308_;
v_isShared_1344_ = v_isSharedCheck_1348_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_a_1341_);
lean_dec(v___x_1308_);
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
v___jp_1349_:
{
if (v_a_1243_ == 0)
{
lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v_levelParams_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; 
v___x_1356_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_1357_ = lean_array_get_borrowed(v___x_1356_, v_preDefs_1239_, v___x_1236_);
v_levelParams_1358_ = lean_ctor_get(v___x_1357_, 1);
v___x_1359_ = lean_box(0);
lean_inc(v_levelParams_1358_);
v___x_1360_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__15(v_levelParams_1358_, v___x_1359_);
v___x_1361_ = lean_array_get_size(v___y_1351_);
v___x_1362_ = lean_mk_empty_array_with_capacity(v___x_1361_);
lean_inc(v___x_1236_);
v___x_1363_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg(v_xs_1238_, v_a_1243_, v_preDefs_1239_, v___x_1360_, v___y_1351_, v___x_1361_, v___x_1236_, v___x_1362_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
lean_dec_ref(v___y_1351_);
if (lean_obj_tag(v___x_1363_) == 0)
{
lean_object* v_a_1364_; 
v_a_1364_ = lean_ctor_get(v___x_1363_, 0);
lean_inc(v_a_1364_);
lean_dec_ref(v___x_1363_);
v___y_1294_ = v___y_1350_;
v_FArgs_1295_ = v_a_1364_;
v___y_1296_ = v___y_1352_;
v___y_1297_ = v___y_1353_;
v___y_1298_ = v___y_1354_;
v___y_1299_ = v___y_1355_;
goto v___jp_1293_;
}
else
{
lean_object* v_a_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1372_; 
lean_dec_ref(v___y_1350_);
lean_dec_ref(v_funTypes_1244_);
lean_dec(v___x_1242_);
lean_dec_ref(v___f_1241_);
lean_dec_ref(v_preDefs_1239_);
lean_dec_ref(v_xs_1238_);
lean_dec_ref(v_fixedParamPerms_1237_);
lean_dec(v___x_1236_);
lean_dec_ref(v___x_1235_);
lean_dec_ref(v_recArgInfos_1233_);
v_a_1365_ = lean_ctor_get(v___x_1363_, 0);
v_isSharedCheck_1372_ = !lean_is_exclusive(v___x_1363_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1367_ = v___x_1363_;
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_a_1365_);
lean_dec(v___x_1363_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v___x_1370_; 
if (v_isShared_1368_ == 0)
{
v___x_1370_ = v___x_1367_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v_a_1365_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
return v___x_1370_;
}
}
}
}
else
{
v___y_1294_ = v___y_1350_;
v_FArgs_1295_ = v___y_1351_;
v___y_1296_ = v___y_1352_;
v___y_1297_ = v___y_1353_;
v___y_1298_ = v___y_1354_;
v___y_1299_ = v___y_1355_;
goto v___jp_1293_;
}
}
v___jp_1373_:
{
lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; 
v___x_1380_ = lean_array_get_size(v_recArgInfos_1233_);
v___x_1381_ = lean_mk_empty_array_with_capacity(v___x_1380_);
lean_inc(v___x_1236_);
lean_inc_ref(v___y_1374_);
lean_inc_ref(v_preDefs_1239_);
lean_inc_ref(v___x_1235_);
lean_inc_ref(v_recArgInfos_1233_);
v___x_1382_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg(v_a_1243_, v_a_1234_, v___y_1375_, v_recArgInfos_1233_, v___x_1235_, v_preDefs_1239_, v___y_1374_, v_recArgInfos_1233_, v___x_1380_, v___x_1236_, v___x_1381_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_);
lean_dec_ref(v___y_1375_);
if (lean_obj_tag(v___x_1382_) == 0)
{
lean_object* v_a_1383_; lean_object* v___x_1384_; 
v_a_1383_ = lean_ctor_get(v___x_1382_, 0);
lean_inc(v_a_1383_);
lean_dec_ref(v___x_1382_);
lean_inc(v___y_1379_);
lean_inc_ref(v___y_1378_);
lean_inc(v___y_1377_);
lean_inc_ref(v___y_1376_);
v___x_1384_ = lean_apply_5(v___f_1232_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_, lean_box(0));
if (lean_obj_tag(v___x_1384_) == 0)
{
lean_object* v_a_1385_; uint8_t v___x_1386_; 
v_a_1385_ = lean_ctor_get(v___x_1384_, 0);
lean_inc(v_a_1385_);
lean_dec_ref(v___x_1384_);
v___x_1386_ = lean_unbox(v_a_1385_);
lean_dec(v_a_1385_);
if (v___x_1386_ == 0)
{
v___y_1350_ = v___y_1374_;
v___y_1351_ = v_a_1383_;
v___y_1352_ = v___y_1376_;
v___y_1353_ = v___y_1377_;
v___y_1354_ = v___y_1378_;
v___y_1355_ = v___y_1379_;
goto v___jp_1349_;
}
else
{
lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; 
v___x_1387_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__6, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__6);
lean_inc(v_a_1383_);
v___x_1388_ = lean_array_to_list(v_a_1383_);
v___x_1389_ = lean_box(0);
v___x_1390_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_1388_, v___x_1389_);
v___x_1391_ = l_Lean_MessageData_ofList(v___x_1390_);
v___x_1392_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1392_, 0, v___x_1387_);
lean_ctor_set(v___x_1392_, 1, v___x_1391_);
lean_inc(v___x_1242_);
v___x_1393_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_1242_, v___x_1392_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_);
if (lean_obj_tag(v___x_1393_) == 0)
{
lean_dec_ref(v___x_1393_);
v___y_1350_ = v___y_1374_;
v___y_1351_ = v_a_1383_;
v___y_1352_ = v___y_1376_;
v___y_1353_ = v___y_1377_;
v___y_1354_ = v___y_1378_;
v___y_1355_ = v___y_1379_;
goto v___jp_1349_;
}
else
{
lean_object* v_a_1394_; lean_object* v___x_1396_; uint8_t v_isShared_1397_; uint8_t v_isSharedCheck_1401_; 
lean_dec(v_a_1383_);
lean_dec_ref(v___y_1374_);
lean_dec_ref(v_funTypes_1244_);
lean_dec(v___x_1242_);
lean_dec_ref(v___f_1241_);
lean_dec_ref(v_preDefs_1239_);
lean_dec_ref(v_xs_1238_);
lean_dec_ref(v_fixedParamPerms_1237_);
lean_dec(v___x_1236_);
lean_dec_ref(v___x_1235_);
lean_dec_ref(v_recArgInfos_1233_);
v_a_1394_ = lean_ctor_get(v___x_1393_, 0);
v_isSharedCheck_1401_ = !lean_is_exclusive(v___x_1393_);
if (v_isSharedCheck_1401_ == 0)
{
v___x_1396_ = v___x_1393_;
v_isShared_1397_ = v_isSharedCheck_1401_;
goto v_resetjp_1395_;
}
else
{
lean_inc(v_a_1394_);
lean_dec(v___x_1393_);
v___x_1396_ = lean_box(0);
v_isShared_1397_ = v_isSharedCheck_1401_;
goto v_resetjp_1395_;
}
v_resetjp_1395_:
{
lean_object* v___x_1399_; 
if (v_isShared_1397_ == 0)
{
v___x_1399_ = v___x_1396_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v_a_1394_);
v___x_1399_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
return v___x_1399_;
}
}
}
}
}
else
{
lean_object* v_a_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1409_; 
lean_dec(v_a_1383_);
lean_dec_ref(v___y_1374_);
lean_dec_ref(v_funTypes_1244_);
lean_dec(v___x_1242_);
lean_dec_ref(v___f_1241_);
lean_dec_ref(v_preDefs_1239_);
lean_dec_ref(v_xs_1238_);
lean_dec_ref(v_fixedParamPerms_1237_);
lean_dec(v___x_1236_);
lean_dec_ref(v___x_1235_);
lean_dec_ref(v_recArgInfos_1233_);
v_a_1402_ = lean_ctor_get(v___x_1384_, 0);
v_isSharedCheck_1409_ = !lean_is_exclusive(v___x_1384_);
if (v_isSharedCheck_1409_ == 0)
{
v___x_1404_ = v___x_1384_;
v_isShared_1405_ = v_isSharedCheck_1409_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_a_1402_);
lean_dec(v___x_1384_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1409_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v___x_1407_; 
if (v_isShared_1405_ == 0)
{
v___x_1407_ = v___x_1404_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v_a_1402_);
v___x_1407_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
return v___x_1407_;
}
}
}
}
else
{
lean_object* v_a_1410_; lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1417_; 
lean_dec_ref(v___y_1374_);
lean_dec_ref(v_funTypes_1244_);
lean_dec(v___x_1242_);
lean_dec_ref(v___f_1241_);
lean_dec_ref(v_preDefs_1239_);
lean_dec_ref(v_xs_1238_);
lean_dec_ref(v_fixedParamPerms_1237_);
lean_dec(v___x_1236_);
lean_dec_ref(v___x_1235_);
lean_dec_ref(v_recArgInfos_1233_);
lean_dec_ref(v___f_1232_);
v_a_1410_ = lean_ctor_get(v___x_1382_, 0);
v_isSharedCheck_1417_ = !lean_is_exclusive(v___x_1382_);
if (v_isSharedCheck_1417_ == 0)
{
v___x_1412_ = v___x_1382_;
v_isShared_1413_ = v_isSharedCheck_1417_;
goto v_resetjp_1411_;
}
else
{
lean_inc(v_a_1410_);
lean_dec(v___x_1382_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1417_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
lean_object* v___x_1415_; 
if (v_isShared_1413_ == 0)
{
v___x_1415_ = v___x_1412_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v_a_1410_);
v___x_1415_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
return v___x_1415_;
}
}
}
}
v___jp_1418_:
{
lean_object* v___x_1423_; 
v___x_1423_ = l_Lean_Elab_Structural_mkBRecOnConst(v_recArgInfos_1233_, v___x_1235_, v_motives_1245_, v_a_1243_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_);
lean_dec_ref(v_motives_1245_);
if (lean_obj_tag(v___x_1423_) == 0)
{
lean_object* v_a_1424_; lean_object* v___x_1425_; 
v_a_1424_ = lean_ctor_get(v___x_1423_, 0);
lean_inc_n(v_a_1424_, 2);
lean_dec_ref(v___x_1423_);
lean_inc_ref(v___x_1235_);
v___x_1425_ = l_Lean_Elab_Structural_inferBRecOnFTypes(v_recArgInfos_1233_, v___x_1235_, v_a_1424_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_);
if (lean_obj_tag(v___x_1425_) == 0)
{
lean_object* v_a_1426_; lean_object* v___x_1427_; 
v_a_1426_ = lean_ctor_get(v___x_1425_, 0);
lean_inc(v_a_1426_);
lean_dec_ref(v___x_1425_);
lean_inc_ref(v___f_1232_);
lean_inc(v___y_1422_);
lean_inc_ref(v___y_1421_);
lean_inc(v___y_1420_);
lean_inc_ref(v___y_1419_);
v___x_1427_ = lean_apply_5(v___f_1232_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_, lean_box(0));
if (lean_obj_tag(v___x_1427_) == 0)
{
lean_object* v_a_1428_; uint8_t v___x_1429_; 
v_a_1428_ = lean_ctor_get(v___x_1427_, 0);
lean_inc(v_a_1428_);
lean_dec_ref(v___x_1427_);
v___x_1429_ = lean_unbox(v_a_1428_);
lean_dec(v_a_1428_);
if (v___x_1429_ == 0)
{
v___y_1374_ = v_a_1424_;
v___y_1375_ = v_a_1426_;
v___y_1376_ = v___y_1419_;
v___y_1377_ = v___y_1420_;
v___y_1378_ = v___y_1421_;
v___y_1379_ = v___y_1422_;
goto v___jp_1373_;
}
else
{
lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; 
v___x_1430_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__8);
lean_inc(v_a_1426_);
v___x_1431_ = lean_array_to_list(v_a_1426_);
v___x_1432_ = lean_box(0);
v___x_1433_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_1431_, v___x_1432_);
v___x_1434_ = l_Lean_MessageData_ofList(v___x_1433_);
v___x_1435_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1435_, 0, v___x_1430_);
lean_ctor_set(v___x_1435_, 1, v___x_1434_);
lean_inc(v___x_1242_);
v___x_1436_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_1242_, v___x_1435_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_);
if (lean_obj_tag(v___x_1436_) == 0)
{
lean_dec_ref(v___x_1436_);
v___y_1374_ = v_a_1424_;
v___y_1375_ = v_a_1426_;
v___y_1376_ = v___y_1419_;
v___y_1377_ = v___y_1420_;
v___y_1378_ = v___y_1421_;
v___y_1379_ = v___y_1422_;
goto v___jp_1373_;
}
else
{
lean_object* v_a_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1444_; 
lean_dec(v_a_1426_);
lean_dec(v_a_1424_);
lean_dec_ref(v_funTypes_1244_);
lean_dec(v___x_1242_);
lean_dec_ref(v___f_1241_);
lean_dec_ref(v_preDefs_1239_);
lean_dec_ref(v_xs_1238_);
lean_dec_ref(v_fixedParamPerms_1237_);
lean_dec(v___x_1236_);
lean_dec_ref(v___x_1235_);
lean_dec_ref(v_recArgInfos_1233_);
lean_dec_ref(v___f_1232_);
v_a_1437_ = lean_ctor_get(v___x_1436_, 0);
v_isSharedCheck_1444_ = !lean_is_exclusive(v___x_1436_);
if (v_isSharedCheck_1444_ == 0)
{
v___x_1439_ = v___x_1436_;
v_isShared_1440_ = v_isSharedCheck_1444_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_a_1437_);
lean_dec(v___x_1436_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1444_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
lean_object* v___x_1442_; 
if (v_isShared_1440_ == 0)
{
v___x_1442_ = v___x_1439_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v_a_1437_);
v___x_1442_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
return v___x_1442_;
}
}
}
}
}
else
{
lean_object* v_a_1445_; lean_object* v___x_1447_; uint8_t v_isShared_1448_; uint8_t v_isSharedCheck_1452_; 
lean_dec(v_a_1426_);
lean_dec(v_a_1424_);
lean_dec_ref(v_funTypes_1244_);
lean_dec(v___x_1242_);
lean_dec_ref(v___f_1241_);
lean_dec_ref(v_preDefs_1239_);
lean_dec_ref(v_xs_1238_);
lean_dec_ref(v_fixedParamPerms_1237_);
lean_dec(v___x_1236_);
lean_dec_ref(v___x_1235_);
lean_dec_ref(v_recArgInfos_1233_);
lean_dec_ref(v___f_1232_);
v_a_1445_ = lean_ctor_get(v___x_1427_, 0);
v_isSharedCheck_1452_ = !lean_is_exclusive(v___x_1427_);
if (v_isSharedCheck_1452_ == 0)
{
v___x_1447_ = v___x_1427_;
v_isShared_1448_ = v_isSharedCheck_1452_;
goto v_resetjp_1446_;
}
else
{
lean_inc(v_a_1445_);
lean_dec(v___x_1427_);
v___x_1447_ = lean_box(0);
v_isShared_1448_ = v_isSharedCheck_1452_;
goto v_resetjp_1446_;
}
v_resetjp_1446_:
{
lean_object* v___x_1450_; 
if (v_isShared_1448_ == 0)
{
v___x_1450_ = v___x_1447_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v_a_1445_);
v___x_1450_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
return v___x_1450_;
}
}
}
}
else
{
lean_object* v_a_1453_; lean_object* v___x_1455_; uint8_t v_isShared_1456_; uint8_t v_isSharedCheck_1460_; 
lean_dec(v_a_1424_);
lean_dec_ref(v_funTypes_1244_);
lean_dec(v___x_1242_);
lean_dec_ref(v___f_1241_);
lean_dec_ref(v_preDefs_1239_);
lean_dec_ref(v_xs_1238_);
lean_dec_ref(v_fixedParamPerms_1237_);
lean_dec(v___x_1236_);
lean_dec_ref(v___x_1235_);
lean_dec_ref(v_recArgInfos_1233_);
lean_dec_ref(v___f_1232_);
v_a_1453_ = lean_ctor_get(v___x_1425_, 0);
v_isSharedCheck_1460_ = !lean_is_exclusive(v___x_1425_);
if (v_isSharedCheck_1460_ == 0)
{
v___x_1455_ = v___x_1425_;
v_isShared_1456_ = v_isSharedCheck_1460_;
goto v_resetjp_1454_;
}
else
{
lean_inc(v_a_1453_);
lean_dec(v___x_1425_);
v___x_1455_ = lean_box(0);
v_isShared_1456_ = v_isSharedCheck_1460_;
goto v_resetjp_1454_;
}
v_resetjp_1454_:
{
lean_object* v___x_1458_; 
if (v_isShared_1456_ == 0)
{
v___x_1458_ = v___x_1455_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v_a_1453_);
v___x_1458_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
return v___x_1458_;
}
}
}
}
else
{
lean_object* v_a_1461_; lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1468_; 
lean_dec_ref(v_funTypes_1244_);
lean_dec(v___x_1242_);
lean_dec_ref(v___f_1241_);
lean_dec_ref(v_preDefs_1239_);
lean_dec_ref(v_xs_1238_);
lean_dec_ref(v_fixedParamPerms_1237_);
lean_dec(v___x_1236_);
lean_dec_ref(v___x_1235_);
lean_dec_ref(v_recArgInfos_1233_);
lean_dec_ref(v___f_1232_);
v_a_1461_ = lean_ctor_get(v___x_1423_, 0);
v_isSharedCheck_1468_ = !lean_is_exclusive(v___x_1423_);
if (v_isSharedCheck_1468_ == 0)
{
v___x_1463_ = v___x_1423_;
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
else
{
lean_inc(v_a_1461_);
lean_dec(v___x_1423_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___boxed(lean_object** _args){
lean_object* v___f_1501_ = _args[0];
lean_object* v_recArgInfos_1502_ = _args[1];
lean_object* v_a_1503_ = _args[2];
lean_object* v___x_1504_ = _args[3];
lean_object* v___x_1505_ = _args[4];
lean_object* v_fixedParamPerms_1506_ = _args[5];
lean_object* v_xs_1507_ = _args[6];
lean_object* v_preDefs_1508_ = _args[7];
lean_object* v_numIndices_1509_ = _args[8];
lean_object* v___f_1510_ = _args[9];
lean_object* v___x_1511_ = _args[10];
lean_object* v_a_1512_ = _args[11];
lean_object* v_funTypes_1513_ = _args[12];
lean_object* v_motives_1514_ = _args[13];
lean_object* v___y_1515_ = _args[14];
lean_object* v___y_1516_ = _args[15];
lean_object* v___y_1517_ = _args[16];
lean_object* v___y_1518_ = _args[17];
lean_object* v___y_1519_ = _args[18];
_start:
{
uint8_t v_a_28882__boxed_1520_; lean_object* v_res_1521_; 
v_a_28882__boxed_1520_ = lean_unbox(v_a_1512_);
v_res_1521_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2(v___f_1501_, v_recArgInfos_1502_, v_a_1503_, v___x_1504_, v___x_1505_, v_fixedParamPerms_1506_, v_xs_1507_, v_preDefs_1508_, v_numIndices_1509_, v___f_1510_, v___x_1511_, v_a_28882__boxed_1520_, v_funTypes_1513_, v_motives_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_);
lean_dec(v___y_1518_);
lean_dec_ref(v___y_1517_);
lean_dec(v___y_1516_);
lean_dec_ref(v___y_1515_);
lean_dec(v_numIndices_1509_);
lean_dec_ref(v_a_1503_);
return v_res_1521_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___redArg(lean_object* v_a_1522_, lean_object* v_funTypes_1523_, lean_object* v_as_1524_, lean_object* v_i_1525_, lean_object* v_j_1526_, lean_object* v_bs_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_){
_start:
{
lean_object* v_zero_1533_; uint8_t v_isZero_1534_; 
v_zero_1533_ = lean_unsigned_to_nat(0u);
v_isZero_1534_ = lean_nat_dec_eq(v_i_1525_, v_zero_1533_);
if (v_isZero_1534_ == 1)
{
lean_object* v___x_1535_; 
lean_dec(v_j_1526_);
lean_dec(v_i_1525_);
v___x_1535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1535_, 0, v_bs_1527_);
return v___x_1535_;
}
else
{
lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; 
v___x_1536_ = l_Lean_instInhabitedExpr;
v___x_1537_ = lean_array_fget_borrowed(v_as_1524_, v_j_1526_);
v___x_1538_ = lean_array_get_borrowed(v___x_1536_, v_a_1522_, v_j_1526_);
v___x_1539_ = lean_array_get_borrowed(v___x_1536_, v_funTypes_1523_, v_j_1526_);
lean_inc(v___x_1539_);
lean_inc(v___x_1538_);
lean_inc(v___x_1537_);
v___x_1540_ = l_Lean_Elab_Structural_mkIndPredBRecOnMotive(v___x_1537_, v___x_1538_, v___x_1539_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_);
if (lean_obj_tag(v___x_1540_) == 0)
{
lean_object* v_a_1541_; lean_object* v_one_1542_; lean_object* v_n_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; 
v_a_1541_ = lean_ctor_get(v___x_1540_, 0);
lean_inc(v_a_1541_);
lean_dec_ref(v___x_1540_);
v_one_1542_ = lean_unsigned_to_nat(1u);
v_n_1543_ = lean_nat_sub(v_i_1525_, v_one_1542_);
lean_dec(v_i_1525_);
v___x_1544_ = lean_nat_add(v_j_1526_, v_one_1542_);
lean_dec(v_j_1526_);
v___x_1545_ = lean_array_push(v_bs_1527_, v_a_1541_);
v_i_1525_ = v_n_1543_;
v_j_1526_ = v___x_1544_;
v_bs_1527_ = v___x_1545_;
goto _start;
}
else
{
lean_object* v_a_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1554_; 
lean_dec_ref(v_bs_1527_);
lean_dec(v_j_1526_);
lean_dec(v_i_1525_);
v_a_1547_ = lean_ctor_get(v___x_1540_, 0);
v_isSharedCheck_1554_ = !lean_is_exclusive(v___x_1540_);
if (v_isSharedCheck_1554_ == 0)
{
v___x_1549_ = v___x_1540_;
v_isShared_1550_ = v_isSharedCheck_1554_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_a_1547_);
lean_dec(v___x_1540_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1554_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
lean_object* v___x_1552_; 
if (v_isShared_1550_ == 0)
{
v___x_1552_ = v___x_1549_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v_a_1547_);
v___x_1552_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
return v___x_1552_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___redArg___boxed(lean_object* v_a_1555_, lean_object* v_funTypes_1556_, lean_object* v_as_1557_, lean_object* v_i_1558_, lean_object* v_j_1559_, lean_object* v_bs_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_){
_start:
{
lean_object* v_res_1566_; 
v_res_1566_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___redArg(v_a_1555_, v_funTypes_1556_, v_as_1557_, v_i_1558_, v_j_1559_, v_bs_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_);
lean_dec(v___y_1564_);
lean_dec_ref(v___y_1563_);
lean_dec(v___y_1562_);
lean_dec_ref(v___y_1561_);
lean_dec_ref(v_as_1557_);
lean_dec_ref(v_funTypes_1556_);
lean_dec_ref(v_a_1555_);
return v_res_1566_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__3(lean_object* v_recArgInfos_1567_, lean_object* v_a_1568_, lean_object* v___x_1569_, lean_object* v___f_1570_, lean_object* v_funTypes_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_){
_start:
{
lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; 
v___x_1577_ = lean_array_get_size(v_recArgInfos_1567_);
v___x_1578_ = lean_mk_empty_array_with_capacity(v___x_1577_);
v___x_1579_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___redArg(v_a_1568_, v_funTypes_1571_, v_recArgInfos_1567_, v___x_1577_, v___x_1569_, v___x_1578_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_);
if (lean_obj_tag(v___x_1579_) == 0)
{
lean_object* v_a_1580_; lean_object* v___x_1581_; 
v_a_1580_ = lean_ctor_get(v___x_1579_, 0);
lean_inc(v_a_1580_);
lean_dec_ref(v___x_1579_);
lean_inc(v___y_1575_);
lean_inc_ref(v___y_1574_);
lean_inc(v___y_1573_);
lean_inc_ref(v___y_1572_);
v___x_1581_ = lean_apply_7(v___f_1570_, v_funTypes_1571_, v_a_1580_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_, lean_box(0));
return v___x_1581_;
}
else
{
lean_object* v_a_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1589_; 
lean_dec_ref(v_funTypes_1571_);
lean_dec_ref(v___f_1570_);
v_a_1582_ = lean_ctor_get(v___x_1579_, 0);
v_isSharedCheck_1589_ = !lean_is_exclusive(v___x_1579_);
if (v_isSharedCheck_1589_ == 0)
{
v___x_1584_ = v___x_1579_;
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_a_1582_);
lean_dec(v___x_1579_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v___x_1587_; 
if (v_isShared_1585_ == 0)
{
v___x_1587_ = v___x_1584_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v_a_1582_);
v___x_1587_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
return v___x_1587_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__3___boxed(lean_object* v_recArgInfos_1590_, lean_object* v_a_1591_, lean_object* v___x_1592_, lean_object* v___f_1593_, lean_object* v_funTypes_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_){
_start:
{
lean_object* v_res_1600_; 
v_res_1600_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__3(v_recArgInfos_1590_, v_a_1591_, v___x_1592_, v___f_1593_, v_funTypes_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_);
lean_dec(v___y_1598_);
lean_dec_ref(v___y_1597_);
lean_dec(v___y_1596_);
lean_dec_ref(v___y_1595_);
lean_dec_ref(v_a_1591_);
lean_dec_ref(v_recArgInfos_1590_);
return v_res_1600_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg(lean_object* v_msg_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_){
_start:
{
lean_object* v_ref_1607_; lean_object* v___x_1608_; lean_object* v_a_1609_; lean_object* v___x_1611_; uint8_t v_isShared_1612_; uint8_t v_isSharedCheck_1617_; 
v_ref_1607_ = lean_ctor_get(v___y_1604_, 5);
v___x_1608_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11_spec__21(v_msg_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_);
v_a_1609_ = lean_ctor_get(v___x_1608_, 0);
v_isSharedCheck_1617_ = !lean_is_exclusive(v___x_1608_);
if (v_isSharedCheck_1617_ == 0)
{
v___x_1611_ = v___x_1608_;
v_isShared_1612_ = v_isSharedCheck_1617_;
goto v_resetjp_1610_;
}
else
{
lean_inc(v_a_1609_);
lean_dec(v___x_1608_);
v___x_1611_ = lean_box(0);
v_isShared_1612_ = v_isSharedCheck_1617_;
goto v_resetjp_1610_;
}
v_resetjp_1610_:
{
lean_object* v___x_1613_; lean_object* v___x_1615_; 
lean_inc(v_ref_1607_);
v___x_1613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1613_, 0, v_ref_1607_);
lean_ctor_set(v___x_1613_, 1, v_a_1609_);
if (v_isShared_1612_ == 0)
{
lean_ctor_set_tag(v___x_1611_, 1);
lean_ctor_set(v___x_1611_, 0, v___x_1613_);
v___x_1615_ = v___x_1611_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v___x_1613_);
v___x_1615_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
return v___x_1615_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg___boxed(lean_object* v_msg_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_){
_start:
{
lean_object* v_res_1624_; 
v_res_1624_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg(v_msg_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_);
lean_dec(v___y_1622_);
lean_dec_ref(v___y_1621_);
lean_dec(v___y_1620_);
lean_dec_ref(v___y_1619_);
return v_res_1624_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1626_; lean_object* v___x_1627_; 
v___x_1626_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__0));
v___x_1627_ = l_Lean_stringToMessageData(v___x_1626_);
return v___x_1627_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__3(void){
_start:
{
lean_object* v___x_1629_; lean_object* v___x_1630_; 
v___x_1629_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__2));
v___x_1630_ = l_Lean_stringToMessageData(v___x_1629_);
return v___x_1630_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4(lean_object* v_constName_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_){
_start:
{
lean_object* v___x_1637_; lean_object* v_env_1638_; lean_object* v___x_1639_; 
v___x_1637_ = lean_st_ref_get(v___y_1635_);
v_env_1638_ = lean_ctor_get(v___x_1637_, 0);
lean_inc_ref(v_env_1638_);
lean_dec(v___x_1637_);
lean_inc(v_constName_1631_);
v___x_1639_ = l_Lean_isInductiveCore_x3f(v_env_1638_, v_constName_1631_);
if (lean_obj_tag(v___x_1639_) == 0)
{
lean_object* v___x_1640_; uint8_t v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; 
v___x_1640_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__1, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__1);
v___x_1641_ = 0;
v___x_1642_ = l_Lean_MessageData_ofConstName(v_constName_1631_, v___x_1641_);
v___x_1643_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1643_, 0, v___x_1640_);
lean_ctor_set(v___x_1643_, 1, v___x_1642_);
v___x_1644_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__3, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__3_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__3);
v___x_1645_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1645_, 0, v___x_1643_);
lean_ctor_set(v___x_1645_, 1, v___x_1644_);
v___x_1646_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg(v___x_1645_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_);
return v___x_1646_;
}
else
{
lean_object* v_val_1647_; lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1654_; 
lean_dec(v_constName_1631_);
v_val_1647_ = lean_ctor_get(v___x_1639_, 0);
v_isSharedCheck_1654_ = !lean_is_exclusive(v___x_1639_);
if (v_isSharedCheck_1654_ == 0)
{
v___x_1649_ = v___x_1639_;
v_isShared_1650_ = v_isSharedCheck_1654_;
goto v_resetjp_1648_;
}
else
{
lean_inc(v_val_1647_);
lean_dec(v___x_1639_);
v___x_1649_ = lean_box(0);
v_isShared_1650_ = v_isSharedCheck_1654_;
goto v_resetjp_1648_;
}
v_resetjp_1648_:
{
lean_object* v___x_1652_; 
if (v_isShared_1650_ == 0)
{
lean_ctor_set_tag(v___x_1649_, 0);
v___x_1652_ = v___x_1649_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1653_; 
v_reuseFailAlloc_1653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1653_, 0, v_val_1647_);
v___x_1652_ = v_reuseFailAlloc_1653_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
return v___x_1652_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___boxed(lean_object* v_constName_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_){
_start:
{
lean_object* v_res_1661_; 
v_res_1661_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4(v_constName_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_);
lean_dec(v___y_1659_);
lean_dec_ref(v___y_1658_);
lean_dec(v___y_1657_);
lean_dec_ref(v___y_1656_);
return v_res_1661_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___redArg(lean_object* v_a_1662_, lean_object* v_a_1663_, lean_object* v_as_1664_, lean_object* v_i_1665_, lean_object* v_j_1666_, lean_object* v_bs_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_){
_start:
{
lean_object* v_zero_1673_; uint8_t v_isZero_1674_; 
v_zero_1673_ = lean_unsigned_to_nat(0u);
v_isZero_1674_ = lean_nat_dec_eq(v_i_1665_, v_zero_1673_);
if (v_isZero_1674_ == 1)
{
lean_object* v___x_1675_; 
lean_dec(v_j_1666_);
lean_dec(v_i_1665_);
v___x_1675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1675_, 0, v_bs_1667_);
return v___x_1675_;
}
else
{
lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___x_1676_ = l_Lean_instInhabitedExpr;
v___x_1677_ = lean_array_fget_borrowed(v_as_1664_, v_j_1666_);
v___x_1678_ = lean_array_get_borrowed(v___x_1676_, v_a_1662_, v_j_1666_);
v___x_1679_ = lean_array_get_borrowed(v___x_1676_, v_a_1663_, v_j_1666_);
lean_inc(v___x_1679_);
lean_inc(v___x_1678_);
lean_inc(v___x_1677_);
v___x_1680_ = l_Lean_Elab_Structural_mkBRecOnMotive(v___x_1677_, v___x_1678_, v___x_1679_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_);
if (lean_obj_tag(v___x_1680_) == 0)
{
lean_object* v_a_1681_; lean_object* v_one_1682_; lean_object* v_n_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; 
v_a_1681_ = lean_ctor_get(v___x_1680_, 0);
lean_inc(v_a_1681_);
lean_dec_ref(v___x_1680_);
v_one_1682_ = lean_unsigned_to_nat(1u);
v_n_1683_ = lean_nat_sub(v_i_1665_, v_one_1682_);
lean_dec(v_i_1665_);
v___x_1684_ = lean_nat_add(v_j_1666_, v_one_1682_);
lean_dec(v_j_1666_);
v___x_1685_ = lean_array_push(v_bs_1667_, v_a_1681_);
v_i_1665_ = v_n_1683_;
v_j_1666_ = v___x_1684_;
v_bs_1667_ = v___x_1685_;
goto _start;
}
else
{
lean_object* v_a_1687_; lean_object* v___x_1689_; uint8_t v_isShared_1690_; uint8_t v_isSharedCheck_1694_; 
lean_dec_ref(v_bs_1667_);
lean_dec(v_j_1666_);
lean_dec(v_i_1665_);
v_a_1687_ = lean_ctor_get(v___x_1680_, 0);
v_isSharedCheck_1694_ = !lean_is_exclusive(v___x_1680_);
if (v_isSharedCheck_1694_ == 0)
{
v___x_1689_ = v___x_1680_;
v_isShared_1690_ = v_isSharedCheck_1694_;
goto v_resetjp_1688_;
}
else
{
lean_inc(v_a_1687_);
lean_dec(v___x_1680_);
v___x_1689_ = lean_box(0);
v_isShared_1690_ = v_isSharedCheck_1694_;
goto v_resetjp_1688_;
}
v_resetjp_1688_:
{
lean_object* v___x_1692_; 
if (v_isShared_1690_ == 0)
{
v___x_1692_ = v___x_1689_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v_a_1687_);
v___x_1692_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
return v___x_1692_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___redArg___boxed(lean_object* v_a_1695_, lean_object* v_a_1696_, lean_object* v_as_1697_, lean_object* v_i_1698_, lean_object* v_j_1699_, lean_object* v_bs_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_){
_start:
{
lean_object* v_res_1706_; 
v_res_1706_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___redArg(v_a_1695_, v_a_1696_, v_as_1697_, v_i_1698_, v_j_1699_, v_bs_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_);
lean_dec(v___y_1704_);
lean_dec_ref(v___y_1703_);
lean_dec(v___y_1702_);
lean_dec_ref(v___y_1701_);
lean_dec_ref(v_as_1697_);
lean_dec_ref(v_a_1696_);
lean_dec_ref(v_a_1695_);
return v_res_1706_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11___redArg(lean_object* v_hi_1707_, lean_object* v_pivot_1708_, lean_object* v_as_1709_, lean_object* v_i_1710_, lean_object* v_k_1711_){
_start:
{
uint8_t v___x_1712_; 
v___x_1712_ = lean_nat_dec_lt(v_k_1711_, v_hi_1707_);
if (v___x_1712_ == 0)
{
lean_object* v___x_1713_; lean_object* v___x_1714_; 
lean_dec(v_k_1711_);
v___x_1713_ = lean_array_fswap(v_as_1709_, v_i_1710_, v_hi_1707_);
v___x_1714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1714_, 0, v_i_1710_);
lean_ctor_set(v___x_1714_, 1, v___x_1713_);
return v___x_1714_;
}
else
{
lean_object* v___x_1715_; uint8_t v___x_1716_; 
v___x_1715_ = lean_array_fget_borrowed(v_as_1709_, v_k_1711_);
v___x_1716_ = l_Nat_blt(v___x_1715_, v_pivot_1708_);
if (v___x_1716_ == 0)
{
lean_object* v___x_1717_; lean_object* v___x_1718_; 
v___x_1717_ = lean_unsigned_to_nat(1u);
v___x_1718_ = lean_nat_add(v_k_1711_, v___x_1717_);
lean_dec(v_k_1711_);
v_k_1711_ = v___x_1718_;
goto _start;
}
else
{
lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; 
v___x_1720_ = lean_array_fswap(v_as_1709_, v_i_1710_, v_k_1711_);
v___x_1721_ = lean_unsigned_to_nat(1u);
v___x_1722_ = lean_nat_add(v_i_1710_, v___x_1721_);
lean_dec(v_i_1710_);
v___x_1723_ = lean_nat_add(v_k_1711_, v___x_1721_);
lean_dec(v_k_1711_);
v_as_1709_ = v___x_1720_;
v_i_1710_ = v___x_1722_;
v_k_1711_ = v___x_1723_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11___redArg___boxed(lean_object* v_hi_1725_, lean_object* v_pivot_1726_, lean_object* v_as_1727_, lean_object* v_i_1728_, lean_object* v_k_1729_){
_start:
{
lean_object* v_res_1730_; 
v_res_1730_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11___redArg(v_hi_1725_, v_pivot_1726_, v_as_1727_, v_i_1728_, v_k_1729_);
lean_dec(v_pivot_1726_);
lean_dec(v_hi_1725_);
return v_res_1730_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg(lean_object* v_n_1731_, lean_object* v_as_1732_, lean_object* v_lo_1733_, lean_object* v_hi_1734_){
_start:
{
lean_object* v___y_1736_; uint8_t v___x_1746_; 
v___x_1746_ = lean_nat_dec_lt(v_lo_1733_, v_hi_1734_);
if (v___x_1746_ == 0)
{
lean_dec(v_lo_1733_);
return v_as_1732_;
}
else
{
lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v_mid_1749_; lean_object* v___y_1751_; lean_object* v___y_1757_; lean_object* v___x_1762_; lean_object* v___x_1763_; uint8_t v___x_1764_; 
v___x_1747_ = lean_nat_add(v_lo_1733_, v_hi_1734_);
v___x_1748_ = lean_unsigned_to_nat(1u);
v_mid_1749_ = lean_nat_shiftr(v___x_1747_, v___x_1748_);
lean_dec(v___x_1747_);
v___x_1762_ = lean_array_fget_borrowed(v_as_1732_, v_mid_1749_);
v___x_1763_ = lean_array_fget_borrowed(v_as_1732_, v_lo_1733_);
v___x_1764_ = l_Nat_blt(v___x_1762_, v___x_1763_);
if (v___x_1764_ == 0)
{
v___y_1757_ = v_as_1732_;
goto v___jp_1756_;
}
else
{
lean_object* v___x_1765_; 
v___x_1765_ = lean_array_fswap(v_as_1732_, v_lo_1733_, v_mid_1749_);
v___y_1757_ = v___x_1765_;
goto v___jp_1756_;
}
v___jp_1750_:
{
lean_object* v___x_1752_; lean_object* v___x_1753_; uint8_t v___x_1754_; 
v___x_1752_ = lean_array_fget_borrowed(v___y_1751_, v_mid_1749_);
v___x_1753_ = lean_array_fget_borrowed(v___y_1751_, v_hi_1734_);
v___x_1754_ = l_Nat_blt(v___x_1752_, v___x_1753_);
if (v___x_1754_ == 0)
{
lean_dec(v_mid_1749_);
v___y_1736_ = v___y_1751_;
goto v___jp_1735_;
}
else
{
lean_object* v___x_1755_; 
v___x_1755_ = lean_array_fswap(v___y_1751_, v_mid_1749_, v_hi_1734_);
lean_dec(v_mid_1749_);
v___y_1736_ = v___x_1755_;
goto v___jp_1735_;
}
}
v___jp_1756_:
{
lean_object* v___x_1758_; lean_object* v___x_1759_; uint8_t v___x_1760_; 
v___x_1758_ = lean_array_fget_borrowed(v___y_1757_, v_hi_1734_);
v___x_1759_ = lean_array_fget_borrowed(v___y_1757_, v_lo_1733_);
v___x_1760_ = l_Nat_blt(v___x_1758_, v___x_1759_);
if (v___x_1760_ == 0)
{
v___y_1751_ = v___y_1757_;
goto v___jp_1750_;
}
else
{
lean_object* v___x_1761_; 
v___x_1761_ = lean_array_fswap(v___y_1757_, v_lo_1733_, v_hi_1734_);
v___y_1751_ = v___x_1761_;
goto v___jp_1750_;
}
}
}
v___jp_1735_:
{
lean_object* v_pivot_1737_; lean_object* v___x_1738_; lean_object* v_fst_1739_; lean_object* v_snd_1740_; uint8_t v___x_1741_; 
v_pivot_1737_ = lean_array_fget(v___y_1736_, v_hi_1734_);
lean_inc_n(v_lo_1733_, 2);
v___x_1738_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11___redArg(v_hi_1734_, v_pivot_1737_, v___y_1736_, v_lo_1733_, v_lo_1733_);
lean_dec(v_pivot_1737_);
v_fst_1739_ = lean_ctor_get(v___x_1738_, 0);
lean_inc(v_fst_1739_);
v_snd_1740_ = lean_ctor_get(v___x_1738_, 1);
lean_inc(v_snd_1740_);
lean_dec_ref(v___x_1738_);
v___x_1741_ = lean_nat_dec_le(v_hi_1734_, v_fst_1739_);
if (v___x_1741_ == 0)
{
lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; 
v___x_1742_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg(v_n_1731_, v_snd_1740_, v_lo_1733_, v_fst_1739_);
v___x_1743_ = lean_unsigned_to_nat(1u);
v___x_1744_ = lean_nat_add(v_fst_1739_, v___x_1743_);
lean_dec(v_fst_1739_);
v_as_1732_ = v___x_1742_;
v_lo_1733_ = v___x_1744_;
goto _start;
}
else
{
lean_dec(v_fst_1739_);
lean_dec(v_lo_1733_);
return v_snd_1740_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg___boxed(lean_object* v_n_1766_, lean_object* v_as_1767_, lean_object* v_lo_1768_, lean_object* v_hi_1769_){
_start:
{
lean_object* v_res_1770_; 
v_res_1770_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg(v_n_1766_, v_as_1767_, v_lo_1768_, v_hi_1769_);
lean_dec(v_hi_1769_);
lean_dec(v_n_1766_);
return v_res_1770_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__6(lean_object* v_xs_1771_, lean_object* v_f_1772_, lean_object* v_x_1773_, lean_object* v_as_1774_, size_t v_i_1775_, size_t v_stop_1776_, lean_object* v_b_1777_){
_start:
{
lean_object* v___y_1779_; uint8_t v___x_1783_; 
v___x_1783_ = lean_usize_dec_eq(v_i_1775_, v_stop_1776_);
if (v___x_1783_ == 0)
{
lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; uint8_t v___x_1788_; 
v___x_1784_ = l_Lean_Elab_Structural_instInhabitedRecArgInfo_default;
v___x_1785_ = lean_array_uget_borrowed(v_as_1774_, v_i_1775_);
v___x_1786_ = lean_array_get_borrowed(v___x_1784_, v_xs_1771_, v___x_1785_);
lean_inc_ref(v_f_1772_);
lean_inc(v___x_1786_);
v___x_1787_ = lean_apply_1(v_f_1772_, v___x_1786_);
v___x_1788_ = lean_nat_dec_eq(v___x_1787_, v_x_1773_);
lean_dec(v___x_1787_);
if (v___x_1788_ == 0)
{
v___y_1779_ = v_b_1777_;
goto v___jp_1778_;
}
else
{
lean_object* v___x_1789_; 
lean_inc(v___x_1785_);
v___x_1789_ = lean_array_push(v_b_1777_, v___x_1785_);
v___y_1779_ = v___x_1789_;
goto v___jp_1778_;
}
}
else
{
lean_dec_ref(v_f_1772_);
return v_b_1777_;
}
v___jp_1778_:
{
size_t v___x_1780_; size_t v___x_1781_; 
v___x_1780_ = ((size_t)1ULL);
v___x_1781_ = lean_usize_add(v_i_1775_, v___x_1780_);
v_i_1775_ = v___x_1781_;
v_b_1777_ = v___y_1779_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__6___boxed(lean_object* v_xs_1790_, lean_object* v_f_1791_, lean_object* v_x_1792_, lean_object* v_as_1793_, lean_object* v_i_1794_, lean_object* v_stop_1795_, lean_object* v_b_1796_){
_start:
{
size_t v_i_boxed_1797_; size_t v_stop_boxed_1798_; lean_object* v_res_1799_; 
v_i_boxed_1797_ = lean_unbox_usize(v_i_1794_);
lean_dec(v_i_1794_);
v_stop_boxed_1798_ = lean_unbox_usize(v_stop_1795_);
lean_dec(v_stop_1795_);
v_res_1799_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__6(v_xs_1790_, v_f_1791_, v_x_1792_, v_as_1793_, v_i_boxed_1797_, v_stop_boxed_1798_, v_b_1796_);
lean_dec_ref(v_as_1793_);
lean_dec(v_x_1792_);
lean_dec_ref(v_xs_1790_);
return v_res_1799_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8(lean_object* v_xs_1802_, lean_object* v_f_1803_, size_t v_sz_1804_, size_t v_i_1805_, lean_object* v_bs_1806_){
_start:
{
uint8_t v___x_1807_; 
v___x_1807_ = lean_usize_dec_lt(v_i_1805_, v_sz_1804_);
if (v___x_1807_ == 0)
{
lean_dec_ref(v_f_1803_);
return v_bs_1806_;
}
else
{
lean_object* v_v_1808_; lean_object* v___x_1809_; lean_object* v_bs_x27_1810_; lean_object* v___y_1812_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; uint8_t v___x_1821_; 
v_v_1808_ = lean_array_uget(v_bs_1806_, v_i_1805_);
v___x_1809_ = lean_unsigned_to_nat(0u);
v_bs_x27_1810_ = lean_array_uset(v_bs_1806_, v_i_1805_, v___x_1809_);
v___x_1817_ = lean_array_get_size(v_xs_1802_);
v___x_1818_ = l_Array_range(v___x_1817_);
v___x_1819_ = lean_array_get_size(v___x_1818_);
v___x_1820_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8___closed__0));
v___x_1821_ = lean_nat_dec_lt(v___x_1809_, v___x_1819_);
if (v___x_1821_ == 0)
{
lean_dec_ref(v___x_1818_);
lean_dec(v_v_1808_);
v___y_1812_ = v___x_1820_;
goto v___jp_1811_;
}
else
{
uint8_t v___x_1822_; 
v___x_1822_ = lean_nat_dec_le(v___x_1819_, v___x_1819_);
if (v___x_1822_ == 0)
{
if (v___x_1821_ == 0)
{
lean_dec_ref(v___x_1818_);
lean_dec(v_v_1808_);
v___y_1812_ = v___x_1820_;
goto v___jp_1811_;
}
else
{
size_t v___x_1823_; size_t v___x_1824_; lean_object* v___x_1825_; 
v___x_1823_ = ((size_t)0ULL);
v___x_1824_ = lean_usize_of_nat(v___x_1819_);
lean_inc_ref(v_f_1803_);
v___x_1825_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__6(v_xs_1802_, v_f_1803_, v_v_1808_, v___x_1818_, v___x_1823_, v___x_1824_, v___x_1820_);
lean_dec_ref(v___x_1818_);
lean_dec(v_v_1808_);
v___y_1812_ = v___x_1825_;
goto v___jp_1811_;
}
}
else
{
size_t v___x_1826_; size_t v___x_1827_; lean_object* v___x_1828_; 
v___x_1826_ = ((size_t)0ULL);
v___x_1827_ = lean_usize_of_nat(v___x_1819_);
lean_inc_ref(v_f_1803_);
v___x_1828_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__6(v_xs_1802_, v_f_1803_, v_v_1808_, v___x_1818_, v___x_1826_, v___x_1827_, v___x_1820_);
lean_dec_ref(v___x_1818_);
lean_dec(v_v_1808_);
v___y_1812_ = v___x_1828_;
goto v___jp_1811_;
}
}
v___jp_1811_:
{
size_t v___x_1813_; size_t v___x_1814_; lean_object* v___x_1815_; 
v___x_1813_ = ((size_t)1ULL);
v___x_1814_ = lean_usize_add(v_i_1805_, v___x_1813_);
v___x_1815_ = lean_array_uset(v_bs_x27_1810_, v_i_1805_, v___y_1812_);
v_i_1805_ = v___x_1814_;
v_bs_1806_ = v___x_1815_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8___boxed(lean_object* v_xs_1829_, lean_object* v_f_1830_, lean_object* v_sz_1831_, lean_object* v_i_1832_, lean_object* v_bs_1833_){
_start:
{
size_t v_sz_boxed_1834_; size_t v_i_boxed_1835_; lean_object* v_res_1836_; 
v_sz_boxed_1834_ = lean_unbox_usize(v_sz_1831_);
lean_dec(v_sz_1831_);
v_i_boxed_1835_ = lean_unbox_usize(v_i_1832_);
lean_dec(v_i_1832_);
v_res_1836_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8(v_xs_1829_, v_f_1830_, v_sz_boxed_1834_, v_i_boxed_1835_, v_bs_1833_);
lean_dec_ref(v_xs_1829_);
return v_res_1836_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__11(lean_object* v_as_1837_, size_t v_i_1838_, size_t v_stop_1839_, lean_object* v_b_1840_){
_start:
{
uint8_t v___x_1841_; 
v___x_1841_ = lean_usize_dec_eq(v_i_1838_, v_stop_1839_);
if (v___x_1841_ == 0)
{
lean_object* v___x_1842_; lean_object* v___x_1843_; size_t v___x_1844_; size_t v___x_1845_; 
v___x_1842_ = lean_array_uget_borrowed(v_as_1837_, v_i_1838_);
v___x_1843_ = l_Array_append___redArg(v_b_1840_, v___x_1842_);
v___x_1844_ = ((size_t)1ULL);
v___x_1845_ = lean_usize_add(v_i_1838_, v___x_1844_);
v_i_1838_ = v___x_1845_;
v_b_1840_ = v___x_1843_;
goto _start;
}
else
{
return v_b_1840_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__11___boxed(lean_object* v_as_1847_, lean_object* v_i_1848_, lean_object* v_stop_1849_, lean_object* v_b_1850_){
_start:
{
size_t v_i_boxed_1851_; size_t v_stop_boxed_1852_; lean_object* v_res_1853_; 
v_i_boxed_1851_ = lean_unbox_usize(v_i_1848_);
lean_dec(v_i_1848_);
v_stop_boxed_1852_ = lean_unbox_usize(v_stop_1849_);
lean_dec(v_stop_1849_);
v_res_1853_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__11(v_as_1847_, v_i_boxed_1851_, v_stop_boxed_1852_, v_b_1850_);
lean_dec_ref(v_as_1847_);
return v_res_1853_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__7___closed__0(void){
_start:
{
lean_object* v___x_1854_; 
v___x_1854_ = l_Array_instInhabited(lean_box(0));
return v___x_1854_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__7(lean_object* v_msg_1855_){
_start:
{
lean_object* v___x_1856_; lean_object* v___x_1857_; 
v___x_1856_ = lean_obj_once(&l_panic___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__7___closed__0, &l_panic___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__7___closed__0_once, _init_l_panic___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__7___closed__0);
v___x_1857_ = lean_panic_fn_borrowed(v___x_1856_, v_msg_1855_);
return v___x_1857_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9___redArg(lean_object* v_xs_1858_, lean_object* v_ys_1859_, lean_object* v_x_1860_){
_start:
{
lean_object* v_zero_1861_; uint8_t v_isZero_1862_; 
v_zero_1861_ = lean_unsigned_to_nat(0u);
v_isZero_1862_ = lean_nat_dec_eq(v_x_1860_, v_zero_1861_);
if (v_isZero_1862_ == 1)
{
lean_dec(v_x_1860_);
return v_isZero_1862_;
}
else
{
lean_object* v_one_1863_; lean_object* v_n_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; uint8_t v___x_1867_; 
v_one_1863_ = lean_unsigned_to_nat(1u);
v_n_1864_ = lean_nat_sub(v_x_1860_, v_one_1863_);
lean_dec(v_x_1860_);
v___x_1865_ = lean_array_fget_borrowed(v_xs_1858_, v_n_1864_);
v___x_1866_ = lean_array_fget_borrowed(v_ys_1859_, v_n_1864_);
v___x_1867_ = lean_nat_dec_eq(v___x_1865_, v___x_1866_);
if (v___x_1867_ == 0)
{
lean_dec(v_n_1864_);
return v___x_1867_;
}
else
{
v_x_1860_ = v_n_1864_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9___redArg___boxed(lean_object* v_xs_1869_, lean_object* v_ys_1870_, lean_object* v_x_1871_){
_start:
{
uint8_t v_res_1872_; lean_object* v_r_1873_; 
v_res_1872_ = l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9___redArg(v_xs_1869_, v_ys_1870_, v_x_1871_);
lean_dec_ref(v_ys_1870_);
lean_dec_ref(v_xs_1869_);
v_r_1873_ = lean_box(v_res_1872_);
return v_r_1873_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__2(void){
_start:
{
lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; 
v___x_1876_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__1));
v___x_1877_ = lean_unsigned_to_nat(2u);
v___x_1878_ = lean_unsigned_to_nat(63u);
v___x_1879_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__0));
v___x_1880_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__0));
v___x_1881_ = l_mkPanicMessageWithDecl(v___x_1880_, v___x_1879_, v___x_1878_, v___x_1877_, v___x_1876_);
return v___x_1881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5(lean_object* v_f_1884_, lean_object* v_xs_1885_, lean_object* v_ys_1886_){
_start:
{
size_t v_sz_1890_; size_t v___x_1891_; lean_object* v_positions_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___y_1896_; lean_object* v___y_1902_; lean_object* v___y_1903_; lean_object* v___y_1904_; lean_object* v___y_1905_; lean_object* v___y_1908_; lean_object* v___y_1909_; lean_object* v___y_1910_; lean_object* v___y_1911_; lean_object* v___y_1914_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; uint8_t v___x_1924_; 
v_sz_1890_ = lean_array_size(v_ys_1886_);
v___x_1891_ = ((size_t)0ULL);
v_positions_1892_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8(v_xs_1885_, v_f_1884_, v_sz_1890_, v___x_1891_, v_ys_1886_);
v___x_1893_ = lean_array_get_size(v_xs_1885_);
v___x_1894_ = l_Array_range(v___x_1893_);
v___x_1921_ = lean_unsigned_to_nat(0u);
v___x_1922_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__3));
v___x_1923_ = lean_array_get_size(v_positions_1892_);
v___x_1924_ = lean_nat_dec_lt(v___x_1921_, v___x_1923_);
if (v___x_1924_ == 0)
{
v___y_1914_ = v___x_1922_;
goto v___jp_1913_;
}
else
{
uint8_t v___x_1925_; 
v___x_1925_ = lean_nat_dec_le(v___x_1923_, v___x_1923_);
if (v___x_1925_ == 0)
{
if (v___x_1924_ == 0)
{
v___y_1914_ = v___x_1922_;
goto v___jp_1913_;
}
else
{
size_t v___x_1926_; lean_object* v___x_1927_; 
v___x_1926_ = lean_usize_of_nat(v___x_1923_);
v___x_1927_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__11(v_positions_1892_, v___x_1891_, v___x_1926_, v___x_1922_);
v___y_1914_ = v___x_1927_;
goto v___jp_1913_;
}
}
else
{
size_t v___x_1928_; lean_object* v___x_1929_; 
v___x_1928_ = lean_usize_of_nat(v___x_1923_);
v___x_1929_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__11(v_positions_1892_, v___x_1891_, v___x_1928_, v___x_1922_);
v___y_1914_ = v___x_1929_;
goto v___jp_1913_;
}
}
v___jp_1887_:
{
lean_object* v___x_1888_; lean_object* v___x_1889_; 
v___x_1888_ = lean_obj_once(&l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__2, &l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__2_once, _init_l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__2);
v___x_1889_ = l_panic___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__7(v___x_1888_);
return v___x_1889_;
}
v___jp_1895_:
{
lean_object* v___x_1897_; lean_object* v___x_1898_; uint8_t v___x_1899_; 
v___x_1897_ = lean_array_get_size(v___x_1894_);
v___x_1898_ = lean_array_get_size(v___y_1896_);
v___x_1899_ = lean_nat_dec_eq(v___x_1897_, v___x_1898_);
if (v___x_1899_ == 0)
{
lean_dec_ref(v___y_1896_);
lean_dec_ref(v___x_1894_);
lean_dec_ref(v_positions_1892_);
goto v___jp_1887_;
}
else
{
uint8_t v___x_1900_; 
v___x_1900_ = l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9___redArg(v___x_1894_, v___y_1896_, v___x_1897_);
lean_dec_ref(v___y_1896_);
lean_dec_ref(v___x_1894_);
if (v___x_1900_ == 0)
{
lean_dec_ref(v_positions_1892_);
goto v___jp_1887_;
}
else
{
return v_positions_1892_;
}
}
}
v___jp_1901_:
{
lean_object* v___x_1906_; 
v___x_1906_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg(v___y_1903_, v___y_1904_, v___y_1902_, v___y_1905_);
lean_dec(v___y_1905_);
lean_dec(v___y_1903_);
v___y_1896_ = v___x_1906_;
goto v___jp_1895_;
}
v___jp_1907_:
{
uint8_t v___x_1912_; 
v___x_1912_ = lean_nat_dec_le(v___y_1911_, v___y_1908_);
if (v___x_1912_ == 0)
{
lean_dec(v___y_1908_);
lean_inc(v___y_1911_);
v___y_1902_ = v___y_1911_;
v___y_1903_ = v___y_1909_;
v___y_1904_ = v___y_1910_;
v___y_1905_ = v___y_1911_;
goto v___jp_1901_;
}
else
{
v___y_1902_ = v___y_1911_;
v___y_1903_ = v___y_1909_;
v___y_1904_ = v___y_1910_;
v___y_1905_ = v___y_1908_;
goto v___jp_1901_;
}
}
v___jp_1913_:
{
lean_object* v___x_1915_; lean_object* v___x_1916_; uint8_t v___x_1917_; 
v___x_1915_ = lean_array_get_size(v___y_1914_);
v___x_1916_ = lean_unsigned_to_nat(0u);
v___x_1917_ = lean_nat_dec_eq(v___x_1915_, v___x_1916_);
if (v___x_1917_ == 0)
{
lean_object* v___x_1918_; lean_object* v___x_1919_; uint8_t v___x_1920_; 
v___x_1918_ = lean_unsigned_to_nat(1u);
v___x_1919_ = lean_nat_sub(v___x_1915_, v___x_1918_);
v___x_1920_ = lean_nat_dec_le(v___x_1916_, v___x_1919_);
if (v___x_1920_ == 0)
{
lean_inc(v___x_1919_);
v___y_1908_ = v___x_1919_;
v___y_1909_ = v___x_1915_;
v___y_1910_ = v___y_1914_;
v___y_1911_ = v___x_1919_;
goto v___jp_1907_;
}
else
{
v___y_1908_ = v___x_1919_;
v___y_1909_ = v___x_1915_;
v___y_1910_ = v___y_1914_;
v___y_1911_ = v___x_1916_;
goto v___jp_1907_;
}
}
else
{
v___y_1896_ = v___y_1914_;
goto v___jp_1895_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___boxed(lean_object* v_f_1930_, lean_object* v_xs_1931_, lean_object* v_ys_1932_){
_start:
{
lean_object* v_res_1933_; 
v_res_1933_ = l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5(v_f_1930_, v_xs_1931_, v_ys_1932_);
lean_dec_ref(v_xs_1931_);
return v_res_1933_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___redArg(lean_object* v_fixedParamPerms_1934_, lean_object* v_xs_1935_, lean_object* v_as_1936_, lean_object* v_i_1937_, lean_object* v_j_1938_, lean_object* v_bs_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_){
_start:
{
lean_object* v_zero_1945_; uint8_t v_isZero_1946_; 
v_zero_1945_ = lean_unsigned_to_nat(0u);
v_isZero_1946_ = lean_nat_dec_eq(v_i_1937_, v_zero_1945_);
if (v_isZero_1946_ == 1)
{
lean_object* v___x_1947_; 
lean_dec(v_j_1938_);
lean_dec(v_i_1937_);
lean_dec_ref(v_xs_1935_);
v___x_1947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1947_, 0, v_bs_1939_);
return v___x_1947_;
}
else
{
lean_object* v_perms_1948_; lean_object* v___x_1949_; lean_object* v_value_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; 
v_perms_1948_ = lean_ctor_get(v_fixedParamPerms_1934_, 1);
v___x_1949_ = lean_array_fget_borrowed(v_as_1936_, v_j_1938_);
v_value_1950_ = lean_ctor_get(v___x_1949_, 7);
v___x_1951_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0, &l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0_once, _init_l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0);
v___x_1952_ = lean_array_get_borrowed(v___x_1951_, v_perms_1948_, v_j_1938_);
lean_inc_ref(v_xs_1935_);
lean_inc_ref(v_value_1950_);
lean_inc(v___x_1952_);
v___x_1953_ = l_Lean_Elab_FixedParamPerm_instantiateLambda(v___x_1952_, v_value_1950_, v_xs_1935_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_);
if (lean_obj_tag(v___x_1953_) == 0)
{
lean_object* v_a_1954_; lean_object* v_one_1955_; lean_object* v_n_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; 
v_a_1954_ = lean_ctor_get(v___x_1953_, 0);
lean_inc(v_a_1954_);
lean_dec_ref(v___x_1953_);
v_one_1955_ = lean_unsigned_to_nat(1u);
v_n_1956_ = lean_nat_sub(v_i_1937_, v_one_1955_);
lean_dec(v_i_1937_);
v___x_1957_ = lean_nat_add(v_j_1938_, v_one_1955_);
lean_dec(v_j_1938_);
v___x_1958_ = lean_array_push(v_bs_1939_, v_a_1954_);
v_i_1937_ = v_n_1956_;
v_j_1938_ = v___x_1957_;
v_bs_1939_ = v___x_1958_;
goto _start;
}
else
{
lean_object* v_a_1960_; lean_object* v___x_1962_; uint8_t v_isShared_1963_; uint8_t v_isSharedCheck_1967_; 
lean_dec_ref(v_bs_1939_);
lean_dec(v_j_1938_);
lean_dec(v_i_1937_);
lean_dec_ref(v_xs_1935_);
v_a_1960_ = lean_ctor_get(v___x_1953_, 0);
v_isSharedCheck_1967_ = !lean_is_exclusive(v___x_1953_);
if (v_isSharedCheck_1967_ == 0)
{
v___x_1962_ = v___x_1953_;
v_isShared_1963_ = v_isSharedCheck_1967_;
goto v_resetjp_1961_;
}
else
{
lean_inc(v_a_1960_);
lean_dec(v___x_1953_);
v___x_1962_ = lean_box(0);
v_isShared_1963_ = v_isSharedCheck_1967_;
goto v_resetjp_1961_;
}
v_resetjp_1961_:
{
lean_object* v___x_1965_; 
if (v_isShared_1963_ == 0)
{
v___x_1965_ = v___x_1962_;
goto v_reusejp_1964_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v_a_1960_);
v___x_1965_ = v_reuseFailAlloc_1966_;
goto v_reusejp_1964_;
}
v_reusejp_1964_:
{
return v___x_1965_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___redArg___boxed(lean_object* v_fixedParamPerms_1968_, lean_object* v_xs_1969_, lean_object* v_as_1970_, lean_object* v_i_1971_, lean_object* v_j_1972_, lean_object* v_bs_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_){
_start:
{
lean_object* v_res_1979_; 
v_res_1979_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___redArg(v_fixedParamPerms_1968_, v_xs_1969_, v_as_1970_, v_i_1971_, v_j_1972_, v_bs_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_);
lean_dec(v___y_1977_);
lean_dec_ref(v___y_1976_);
lean_dec(v___y_1975_);
lean_dec_ref(v___y_1974_);
lean_dec_ref(v_as_1970_);
lean_dec_ref(v_fixedParamPerms_1968_);
return v_res_1979_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__0(lean_object* v_a_1980_, lean_object* v_a_1981_){
_start:
{
if (lean_obj_tag(v_a_1980_) == 0)
{
lean_object* v___x_1982_; 
v___x_1982_ = l_List_reverse___redArg(v_a_1981_);
return v___x_1982_;
}
else
{
lean_object* v_head_1983_; lean_object* v_tail_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_1995_; 
v_head_1983_ = lean_ctor_get(v_a_1980_, 0);
v_tail_1984_ = lean_ctor_get(v_a_1980_, 1);
v_isSharedCheck_1995_ = !lean_is_exclusive(v_a_1980_);
if (v_isSharedCheck_1995_ == 0)
{
v___x_1986_ = v_a_1980_;
v_isShared_1987_ = v_isSharedCheck_1995_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_tail_1984_);
lean_inc(v_head_1983_);
lean_dec(v_a_1980_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_1995_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1992_; 
v___x_1988_ = l_Nat_reprFast(v_head_1983_);
v___x_1989_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1989_, 0, v___x_1988_);
v___x_1990_ = l_Lean_MessageData_ofFormat(v___x_1989_);
if (v_isShared_1987_ == 0)
{
lean_ctor_set(v___x_1986_, 1, v_a_1981_);
lean_ctor_set(v___x_1986_, 0, v___x_1990_);
v___x_1992_ = v___x_1986_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v___x_1990_);
lean_ctor_set(v_reuseFailAlloc_1994_, 1, v_a_1981_);
v___x_1992_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
v_a_1980_ = v_tail_1984_;
v_a_1981_ = v___x_1992_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__20(lean_object* v_a_1996_, lean_object* v_a_1997_){
_start:
{
if (lean_obj_tag(v_a_1996_) == 0)
{
lean_object* v___x_1998_; 
v___x_1998_ = l_List_reverse___redArg(v_a_1997_);
return v___x_1998_;
}
else
{
lean_object* v_head_1999_; lean_object* v_tail_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2012_; 
v_head_1999_ = lean_ctor_get(v_a_1996_, 0);
v_tail_2000_ = lean_ctor_get(v_a_1996_, 1);
v_isSharedCheck_2012_ = !lean_is_exclusive(v_a_1996_);
if (v_isSharedCheck_2012_ == 0)
{
v___x_2002_ = v_a_1996_;
v_isShared_2003_ = v_isSharedCheck_2012_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_tail_2000_);
lean_inc(v_head_1999_);
lean_dec(v_a_1996_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2012_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2009_; 
v___x_2004_ = lean_array_to_list(v_head_1999_);
v___x_2005_ = lean_box(0);
v___x_2006_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__0(v___x_2004_, v___x_2005_);
v___x_2007_ = l_Lean_MessageData_ofList(v___x_2006_);
if (v_isShared_2003_ == 0)
{
lean_ctor_set(v___x_2002_, 1, v_a_1997_);
lean_ctor_set(v___x_2002_, 0, v___x_2007_);
v___x_2009_ = v___x_2002_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2011_; 
v_reuseFailAlloc_2011_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2011_, 0, v___x_2007_);
lean_ctor_set(v_reuseFailAlloc_2011_, 1, v_a_1997_);
v___x_2009_ = v_reuseFailAlloc_2011_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
v_a_1996_ = v_tail_2000_;
v_a_1997_ = v___x_2009_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___redArg(lean_object* v_fixedParamPerms_2013_, lean_object* v_xs_2014_, lean_object* v_as_2015_, lean_object* v_i_2016_, lean_object* v_j_2017_, lean_object* v_bs_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_){
_start:
{
lean_object* v_zero_2024_; uint8_t v_isZero_2025_; 
v_zero_2024_ = lean_unsigned_to_nat(0u);
v_isZero_2025_ = lean_nat_dec_eq(v_i_2016_, v_zero_2024_);
if (v_isZero_2025_ == 1)
{
lean_object* v___x_2026_; 
lean_dec(v_j_2017_);
lean_dec(v_i_2016_);
lean_dec_ref(v_xs_2014_);
v___x_2026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2026_, 0, v_bs_2018_);
return v___x_2026_;
}
else
{
lean_object* v_perms_2027_; lean_object* v___x_2028_; lean_object* v_type_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; 
v_perms_2027_ = lean_ctor_get(v_fixedParamPerms_2013_, 1);
v___x_2028_ = lean_array_fget_borrowed(v_as_2015_, v_j_2017_);
v_type_2029_ = lean_ctor_get(v___x_2028_, 6);
v___x_2030_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0, &l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0_once, _init_l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0);
v___x_2031_ = lean_array_get_borrowed(v___x_2030_, v_perms_2027_, v_j_2017_);
lean_inc_ref(v_xs_2014_);
lean_inc_ref(v_type_2029_);
lean_inc(v___x_2031_);
v___x_2032_ = l_Lean_Elab_FixedParamPerm_instantiateForall(v___x_2031_, v_type_2029_, v_xs_2014_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_);
if (lean_obj_tag(v___x_2032_) == 0)
{
lean_object* v_a_2033_; lean_object* v_one_2034_; lean_object* v_n_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; 
v_a_2033_ = lean_ctor_get(v___x_2032_, 0);
lean_inc(v_a_2033_);
lean_dec_ref(v___x_2032_);
v_one_2034_ = lean_unsigned_to_nat(1u);
v_n_2035_ = lean_nat_sub(v_i_2016_, v_one_2034_);
lean_dec(v_i_2016_);
v___x_2036_ = lean_nat_add(v_j_2017_, v_one_2034_);
lean_dec(v_j_2017_);
v___x_2037_ = lean_array_push(v_bs_2018_, v_a_2033_);
v_i_2016_ = v_n_2035_;
v_j_2017_ = v___x_2036_;
v_bs_2018_ = v___x_2037_;
goto _start;
}
else
{
lean_object* v_a_2039_; lean_object* v___x_2041_; uint8_t v_isShared_2042_; uint8_t v_isSharedCheck_2046_; 
lean_dec_ref(v_bs_2018_);
lean_dec(v_j_2017_);
lean_dec(v_i_2016_);
lean_dec_ref(v_xs_2014_);
v_a_2039_ = lean_ctor_get(v___x_2032_, 0);
v_isSharedCheck_2046_ = !lean_is_exclusive(v___x_2032_);
if (v_isSharedCheck_2046_ == 0)
{
v___x_2041_ = v___x_2032_;
v_isShared_2042_ = v_isSharedCheck_2046_;
goto v_resetjp_2040_;
}
else
{
lean_inc(v_a_2039_);
lean_dec(v___x_2032_);
v___x_2041_ = lean_box(0);
v_isShared_2042_ = v_isSharedCheck_2046_;
goto v_resetjp_2040_;
}
v_resetjp_2040_:
{
lean_object* v___x_2044_; 
if (v_isShared_2042_ == 0)
{
v___x_2044_ = v___x_2041_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v_a_2039_);
v___x_2044_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
return v___x_2044_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___redArg___boxed(lean_object* v_fixedParamPerms_2047_, lean_object* v_xs_2048_, lean_object* v_as_2049_, lean_object* v_i_2050_, lean_object* v_j_2051_, lean_object* v_bs_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_){
_start:
{
lean_object* v_res_2058_; 
v_res_2058_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___redArg(v_fixedParamPerms_2047_, v_xs_2048_, v_as_2049_, v_i_2050_, v_j_2051_, v_bs_2052_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_);
lean_dec(v___y_2056_);
lean_dec_ref(v___y_2055_);
lean_dec(v___y_2054_);
lean_dec_ref(v___y_2053_);
lean_dec_ref(v_as_2049_);
lean_dec_ref(v_fixedParamPerms_2047_);
return v_res_2058_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__9(void){
_start:
{
lean_object* v___x_2073_; lean_object* v___x_2074_; 
v___x_2073_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__8));
v___x_2074_ = l_Lean_stringToMessageData(v___x_2073_);
return v___x_2074_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__11(void){
_start:
{
lean_object* v___x_2076_; lean_object* v___x_2077_; 
v___x_2076_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__10));
v___x_2077_ = l_Lean_stringToMessageData(v___x_2076_);
return v___x_2077_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion(lean_object* v_preDefs_2078_, lean_object* v_fixedParamPerms_2079_, lean_object* v_xs_2080_, lean_object* v_recArgInfos_2081_, lean_object* v_a_2082_, lean_object* v_a_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_){
_start:
{
lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; 
v___x_2087_ = lean_array_get_size(v_preDefs_2078_);
v___x_2088_ = lean_unsigned_to_nat(0u);
v___x_2089_ = lean_mk_empty_array_with_capacity(v___x_2087_);
lean_inc_ref(v___x_2089_);
lean_inc_ref(v_xs_2080_);
v___x_2090_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___redArg(v_fixedParamPerms_2079_, v_xs_2080_, v_preDefs_2078_, v___x_2087_, v___x_2088_, v___x_2089_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_);
if (lean_obj_tag(v___x_2090_) == 0)
{
lean_object* v_a_2091_; lean_object* v___x_2092_; 
v_a_2091_ = lean_ctor_get(v___x_2090_, 0);
lean_inc(v_a_2091_);
lean_dec_ref(v___x_2090_);
lean_inc_ref(v_xs_2080_);
v___x_2092_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___redArg(v_fixedParamPerms_2079_, v_xs_2080_, v_preDefs_2078_, v___x_2087_, v___x_2088_, v___x_2089_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_);
if (lean_obj_tag(v___x_2092_) == 0)
{
lean_object* v_a_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v_indGroupInst_2096_; lean_object* v_toIndGroupInfo_2097_; lean_object* v_all_2098_; lean_object* v___x_2100_; uint8_t v_isShared_2101_; uint8_t v_isSharedCheck_2184_; 
v_a_2093_ = lean_ctor_get(v___x_2092_, 0);
lean_inc(v_a_2093_);
lean_dec_ref(v___x_2092_);
v___x_2094_ = l_Lean_Elab_Structural_instInhabitedRecArgInfo_default;
v___x_2095_ = lean_array_get_borrowed(v___x_2094_, v_recArgInfos_2081_, v___x_2088_);
v_indGroupInst_2096_ = lean_ctor_get(v___x_2095_, 4);
v_toIndGroupInfo_2097_ = lean_ctor_get(v_indGroupInst_2096_, 0);
lean_inc_ref(v_toIndGroupInfo_2097_);
v_all_2098_ = lean_ctor_get(v_toIndGroupInfo_2097_, 0);
v_isSharedCheck_2184_ = !lean_is_exclusive(v_toIndGroupInfo_2097_);
if (v_isSharedCheck_2184_ == 0)
{
lean_object* v_unused_2185_; 
v_unused_2185_ = lean_ctor_get(v_toIndGroupInfo_2097_, 1);
lean_dec(v_unused_2185_);
v___x_2100_ = v_toIndGroupInfo_2097_;
v_isShared_2101_ = v_isSharedCheck_2184_;
goto v_resetjp_2099_;
}
else
{
lean_inc(v_all_2098_);
lean_dec(v_toIndGroupInfo_2097_);
v___x_2100_ = lean_box(0);
v_isShared_2101_ = v_isSharedCheck_2184_;
goto v_resetjp_2099_;
}
v_resetjp_2099_:
{
lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; 
v___x_2102_ = lean_box(0);
v___x_2103_ = lean_array_get(v___x_2102_, v_all_2098_, v___x_2088_);
lean_dec_ref(v_all_2098_);
v___x_2104_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4(v___x_2103_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_);
if (lean_obj_tag(v___x_2104_) == 0)
{
lean_object* v_a_2105_; lean_object* v___x_2106_; lean_object* v___f_2107_; lean_object* v___x_2108_; lean_object* v_a_2109_; lean_object* v___f_2110_; lean_object* v___f_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___y_2116_; lean_object* v___y_2117_; lean_object* v___y_2118_; lean_object* v___y_2119_; uint8_t v___x_2152_; 
v_a_2105_ = lean_ctor_get(v___x_2104_, 0);
lean_inc(v_a_2105_);
lean_dec_ref(v___x_2104_);
v___x_2106_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__3));
v___f_2107_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__4));
v___x_2108_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0(v___x_2106_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_);
v_a_2109_ = lean_ctor_get(v___x_2108_, 0);
lean_inc(v_a_2109_);
lean_dec_ref(v___x_2108_);
v___f_2110_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__5));
v___f_2111_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__6));
v___x_2112_ = l_Lean_InductiveVal_numTypeFormers(v_a_2105_);
v___x_2113_ = l_Array_range(v___x_2112_);
v___x_2114_ = l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5(v___f_2111_, v_recArgInfos_2081_, v___x_2113_);
v___x_2152_ = lean_unbox(v_a_2109_);
lean_dec(v_a_2109_);
if (v___x_2152_ == 0)
{
lean_del_object(v___x_2100_);
v___y_2116_ = v_a_2082_;
v___y_2117_ = v_a_2083_;
v___y_2118_ = v_a_2084_;
v___y_2119_ = v_a_2085_;
goto v___jp_2115_;
}
else
{
lean_object* v_toConstantVal_2153_; lean_object* v_name_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2158_; 
v_toConstantVal_2153_ = lean_ctor_get(v_a_2105_, 0);
v_name_2154_ = lean_ctor_get(v_toConstantVal_2153_, 0);
v___x_2155_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__9, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__9_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__9);
lean_inc(v_name_2154_);
v___x_2156_ = l_Lean_MessageData_ofName(v_name_2154_);
if (v_isShared_2101_ == 0)
{
lean_ctor_set_tag(v___x_2100_, 7);
lean_ctor_set(v___x_2100_, 1, v___x_2156_);
lean_ctor_set(v___x_2100_, 0, v___x_2155_);
v___x_2158_ = v___x_2100_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2175_; 
v_reuseFailAlloc_2175_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2175_, 0, v___x_2155_);
lean_ctor_set(v_reuseFailAlloc_2175_, 1, v___x_2156_);
v___x_2158_ = v_reuseFailAlloc_2175_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; 
v___x_2159_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__11, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__11_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__11);
v___x_2160_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2160_, 0, v___x_2158_);
lean_ctor_set(v___x_2160_, 1, v___x_2159_);
lean_inc_ref(v___x_2114_);
v___x_2161_ = lean_array_to_list(v___x_2114_);
v___x_2162_ = lean_box(0);
v___x_2163_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__20(v___x_2161_, v___x_2162_);
v___x_2164_ = l_Lean_MessageData_ofList(v___x_2163_);
v___x_2165_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2165_, 0, v___x_2160_);
lean_ctor_set(v___x_2165_, 1, v___x_2164_);
v___x_2166_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_2106_, v___x_2165_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_);
if (lean_obj_tag(v___x_2166_) == 0)
{
lean_dec_ref(v___x_2166_);
v___y_2116_ = v_a_2082_;
v___y_2117_ = v_a_2083_;
v___y_2118_ = v_a_2084_;
v___y_2119_ = v_a_2085_;
goto v___jp_2115_;
}
else
{
lean_object* v_a_2167_; lean_object* v___x_2169_; uint8_t v_isShared_2170_; uint8_t v_isSharedCheck_2174_; 
lean_dec_ref(v___x_2114_);
lean_dec(v_a_2105_);
lean_dec(v_a_2093_);
lean_dec(v_a_2091_);
lean_dec_ref(v_recArgInfos_2081_);
lean_dec_ref(v_xs_2080_);
lean_dec_ref(v_fixedParamPerms_2079_);
lean_dec_ref(v_preDefs_2078_);
v_a_2167_ = lean_ctor_get(v___x_2166_, 0);
v_isSharedCheck_2174_ = !lean_is_exclusive(v___x_2166_);
if (v_isSharedCheck_2174_ == 0)
{
v___x_2169_ = v___x_2166_;
v_isShared_2170_ = v_isSharedCheck_2174_;
goto v_resetjp_2168_;
}
else
{
lean_inc(v_a_2167_);
lean_dec(v___x_2166_);
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
}
v___jp_2115_:
{
lean_object* v_toConstantVal_2120_; lean_object* v_numIndices_2121_; lean_object* v_name_2122_; lean_object* v___x_2123_; 
v_toConstantVal_2120_ = lean_ctor_get(v_a_2105_, 0);
lean_inc_ref(v_toConstantVal_2120_);
v_numIndices_2121_ = lean_ctor_get(v_a_2105_, 2);
lean_inc(v_numIndices_2121_);
lean_dec(v_a_2105_);
v_name_2122_ = lean_ctor_get(v_toConstantVal_2120_, 0);
lean_inc(v_name_2122_);
lean_dec_ref(v_toConstantVal_2120_);
v___x_2123_ = l_Lean_Meta_isInductivePredicate(v_name_2122_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_);
if (lean_obj_tag(v___x_2123_) == 0)
{
lean_object* v_a_2124_; lean_object* v___f_2125_; uint8_t v___x_2126_; 
v_a_2124_ = lean_ctor_get(v___x_2123_, 0);
lean_inc_n(v_a_2124_, 2);
lean_dec_ref(v___x_2123_);
lean_inc(v_numIndices_2121_);
lean_inc_ref(v_preDefs_2078_);
lean_inc_ref(v_xs_2080_);
lean_inc_ref(v_fixedParamPerms_2079_);
lean_inc_ref(v___x_2114_);
lean_inc(v_a_2091_);
lean_inc_ref(v_recArgInfos_2081_);
v___f_2125_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___boxed), 19, 12);
lean_closure_set(v___f_2125_, 0, v___f_2107_);
lean_closure_set(v___f_2125_, 1, v_recArgInfos_2081_);
lean_closure_set(v___f_2125_, 2, v_a_2091_);
lean_closure_set(v___f_2125_, 3, v___x_2114_);
lean_closure_set(v___f_2125_, 4, v___x_2088_);
lean_closure_set(v___f_2125_, 5, v_fixedParamPerms_2079_);
lean_closure_set(v___f_2125_, 6, v_xs_2080_);
lean_closure_set(v___f_2125_, 7, v_preDefs_2078_);
lean_closure_set(v___f_2125_, 8, v_numIndices_2121_);
lean_closure_set(v___f_2125_, 9, v___f_2110_);
lean_closure_set(v___f_2125_, 10, v___x_2106_);
lean_closure_set(v___f_2125_, 11, v_a_2124_);
v___x_2126_ = lean_unbox(v_a_2124_);
if (v___x_2126_ == 0)
{
lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; 
lean_dec_ref(v___f_2125_);
v___x_2127_ = lean_array_get_size(v_recArgInfos_2081_);
v___x_2128_ = lean_mk_empty_array_with_capacity(v___x_2127_);
v___x_2129_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___redArg(v_a_2091_, v_a_2093_, v_recArgInfos_2081_, v___x_2127_, v___x_2088_, v___x_2128_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_);
lean_dec(v_a_2093_);
if (lean_obj_tag(v___x_2129_) == 0)
{
lean_object* v_a_2130_; lean_object* v___x_2131_; uint8_t v___x_2132_; lean_object* v___x_2133_; 
v_a_2130_ = lean_ctor_get(v___x_2129_, 0);
lean_inc(v_a_2130_);
lean_dec_ref(v___x_2129_);
v___x_2131_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__7));
v___x_2132_ = lean_unbox(v_a_2124_);
lean_dec(v_a_2124_);
v___x_2133_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2(v___f_2107_, v_recArgInfos_2081_, v_a_2091_, v___x_2114_, v___x_2088_, v_fixedParamPerms_2079_, v_xs_2080_, v_preDefs_2078_, v_numIndices_2121_, v___f_2110_, v___x_2106_, v___x_2132_, v___x_2131_, v_a_2130_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_);
lean_dec(v_numIndices_2121_);
lean_dec(v_a_2091_);
return v___x_2133_;
}
else
{
lean_object* v_a_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2141_; 
lean_dec(v_a_2124_);
lean_dec(v_numIndices_2121_);
lean_dec_ref(v___x_2114_);
lean_dec(v_a_2091_);
lean_dec_ref(v_recArgInfos_2081_);
lean_dec_ref(v_xs_2080_);
lean_dec_ref(v_fixedParamPerms_2079_);
lean_dec_ref(v_preDefs_2078_);
v_a_2134_ = lean_ctor_get(v___x_2129_, 0);
v_isSharedCheck_2141_ = !lean_is_exclusive(v___x_2129_);
if (v_isSharedCheck_2141_ == 0)
{
v___x_2136_ = v___x_2129_;
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_a_2134_);
lean_dec(v___x_2129_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v___x_2139_; 
if (v_isShared_2137_ == 0)
{
v___x_2139_ = v___x_2136_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v_a_2134_);
v___x_2139_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
return v___x_2139_;
}
}
}
}
else
{
lean_object* v___f_2142_; lean_object* v___x_2143_; 
lean_dec(v_a_2124_);
lean_dec(v_numIndices_2121_);
lean_dec_ref(v___x_2114_);
lean_dec(v_a_2093_);
lean_dec_ref(v_xs_2080_);
lean_dec_ref(v_fixedParamPerms_2079_);
lean_dec_ref(v_preDefs_2078_);
lean_inc(v_a_2091_);
v___f_2142_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__3___boxed), 10, 4);
lean_closure_set(v___f_2142_, 0, v_recArgInfos_2081_);
lean_closure_set(v___f_2142_, 1, v_a_2091_);
lean_closure_set(v___f_2142_, 2, v___x_2088_);
lean_closure_set(v___f_2142_, 3, v___f_2125_);
v___x_2143_ = l_Lean_Elab_Structural_withFunTypes___redArg(v_a_2091_, v___f_2142_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_);
return v___x_2143_;
}
}
else
{
lean_object* v_a_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2151_; 
lean_dec(v_numIndices_2121_);
lean_dec_ref(v___x_2114_);
lean_dec(v_a_2093_);
lean_dec(v_a_2091_);
lean_dec_ref(v_recArgInfos_2081_);
lean_dec_ref(v_xs_2080_);
lean_dec_ref(v_fixedParamPerms_2079_);
lean_dec_ref(v_preDefs_2078_);
v_a_2144_ = lean_ctor_get(v___x_2123_, 0);
v_isSharedCheck_2151_ = !lean_is_exclusive(v___x_2123_);
if (v_isSharedCheck_2151_ == 0)
{
v___x_2146_ = v___x_2123_;
v_isShared_2147_ = v_isSharedCheck_2151_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_a_2144_);
lean_dec(v___x_2123_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2151_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
lean_object* v___x_2149_; 
if (v_isShared_2147_ == 0)
{
v___x_2149_ = v___x_2146_;
goto v_reusejp_2148_;
}
else
{
lean_object* v_reuseFailAlloc_2150_; 
v_reuseFailAlloc_2150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2150_, 0, v_a_2144_);
v___x_2149_ = v_reuseFailAlloc_2150_;
goto v_reusejp_2148_;
}
v_reusejp_2148_:
{
return v___x_2149_;
}
}
}
}
}
else
{
lean_object* v_a_2176_; lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2183_; 
lean_del_object(v___x_2100_);
lean_dec(v_a_2093_);
lean_dec(v_a_2091_);
lean_dec_ref(v_recArgInfos_2081_);
lean_dec_ref(v_xs_2080_);
lean_dec_ref(v_fixedParamPerms_2079_);
lean_dec_ref(v_preDefs_2078_);
v_a_2176_ = lean_ctor_get(v___x_2104_, 0);
v_isSharedCheck_2183_ = !lean_is_exclusive(v___x_2104_);
if (v_isSharedCheck_2183_ == 0)
{
v___x_2178_ = v___x_2104_;
v_isShared_2179_ = v_isSharedCheck_2183_;
goto v_resetjp_2177_;
}
else
{
lean_inc(v_a_2176_);
lean_dec(v___x_2104_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2183_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
lean_object* v___x_2181_; 
if (v_isShared_2179_ == 0)
{
v___x_2181_ = v___x_2178_;
goto v_reusejp_2180_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v_a_2176_);
v___x_2181_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2180_;
}
v_reusejp_2180_:
{
return v___x_2181_;
}
}
}
}
}
else
{
lean_object* v_a_2186_; lean_object* v___x_2188_; uint8_t v_isShared_2189_; uint8_t v_isSharedCheck_2193_; 
lean_dec(v_a_2091_);
lean_dec_ref(v_recArgInfos_2081_);
lean_dec_ref(v_xs_2080_);
lean_dec_ref(v_fixedParamPerms_2079_);
lean_dec_ref(v_preDefs_2078_);
v_a_2186_ = lean_ctor_get(v___x_2092_, 0);
v_isSharedCheck_2193_ = !lean_is_exclusive(v___x_2092_);
if (v_isSharedCheck_2193_ == 0)
{
v___x_2188_ = v___x_2092_;
v_isShared_2189_ = v_isSharedCheck_2193_;
goto v_resetjp_2187_;
}
else
{
lean_inc(v_a_2186_);
lean_dec(v___x_2092_);
v___x_2188_ = lean_box(0);
v_isShared_2189_ = v_isSharedCheck_2193_;
goto v_resetjp_2187_;
}
v_resetjp_2187_:
{
lean_object* v___x_2191_; 
if (v_isShared_2189_ == 0)
{
v___x_2191_ = v___x_2188_;
goto v_reusejp_2190_;
}
else
{
lean_object* v_reuseFailAlloc_2192_; 
v_reuseFailAlloc_2192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2192_, 0, v_a_2186_);
v___x_2191_ = v_reuseFailAlloc_2192_;
goto v_reusejp_2190_;
}
v_reusejp_2190_:
{
return v___x_2191_;
}
}
}
}
else
{
lean_object* v_a_2194_; lean_object* v___x_2196_; uint8_t v_isShared_2197_; uint8_t v_isSharedCheck_2201_; 
lean_dec_ref(v___x_2089_);
lean_dec_ref(v_recArgInfos_2081_);
lean_dec_ref(v_xs_2080_);
lean_dec_ref(v_fixedParamPerms_2079_);
lean_dec_ref(v_preDefs_2078_);
v_a_2194_ = lean_ctor_get(v___x_2090_, 0);
v_isSharedCheck_2201_ = !lean_is_exclusive(v___x_2090_);
if (v_isSharedCheck_2201_ == 0)
{
v___x_2196_ = v___x_2090_;
v_isShared_2197_ = v_isSharedCheck_2201_;
goto v_resetjp_2195_;
}
else
{
lean_inc(v_a_2194_);
lean_dec(v___x_2090_);
v___x_2196_ = lean_box(0);
v_isShared_2197_ = v_isSharedCheck_2201_;
goto v_resetjp_2195_;
}
v_resetjp_2195_:
{
lean_object* v___x_2199_; 
if (v_isShared_2197_ == 0)
{
v___x_2199_ = v___x_2196_;
goto v_reusejp_2198_;
}
else
{
lean_object* v_reuseFailAlloc_2200_; 
v_reuseFailAlloc_2200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2200_, 0, v_a_2194_);
v___x_2199_ = v_reuseFailAlloc_2200_;
goto v_reusejp_2198_;
}
v_reusejp_2198_:
{
return v___x_2199_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___boxed(lean_object* v_preDefs_2202_, lean_object* v_fixedParamPerms_2203_, lean_object* v_xs_2204_, lean_object* v_recArgInfos_2205_, lean_object* v_a_2206_, lean_object* v_a_2207_, lean_object* v_a_2208_, lean_object* v_a_2209_, lean_object* v_a_2210_){
_start:
{
lean_object* v_res_2211_; 
v_res_2211_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion(v_preDefs_2202_, v_fixedParamPerms_2203_, v_xs_2204_, v_recArgInfos_2205_, v_a_2206_, v_a_2207_, v_a_2208_, v_a_2209_);
lean_dec(v_a_2209_);
lean_dec_ref(v_a_2208_);
lean_dec(v_a_2207_);
lean_dec_ref(v_a_2206_);
return v_res_2211_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2(lean_object* v_fixedParamPerms_2212_, lean_object* v_xs_2213_, lean_object* v_as_2214_, lean_object* v_i_2215_, lean_object* v_j_2216_, lean_object* v_inv_2217_, lean_object* v_bs_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_){
_start:
{
lean_object* v___x_2224_; 
v___x_2224_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___redArg(v_fixedParamPerms_2212_, v_xs_2213_, v_as_2214_, v_i_2215_, v_j_2216_, v_bs_2218_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_);
return v___x_2224_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___boxed(lean_object* v_fixedParamPerms_2225_, lean_object* v_xs_2226_, lean_object* v_as_2227_, lean_object* v_i_2228_, lean_object* v_j_2229_, lean_object* v_inv_2230_, lean_object* v_bs_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_){
_start:
{
lean_object* v_res_2237_; 
v_res_2237_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2(v_fixedParamPerms_2225_, v_xs_2226_, v_as_2227_, v_i_2228_, v_j_2229_, v_inv_2230_, v_bs_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_);
lean_dec(v___y_2235_);
lean_dec_ref(v___y_2234_);
lean_dec(v___y_2233_);
lean_dec_ref(v___y_2232_);
lean_dec_ref(v_as_2227_);
lean_dec_ref(v_fixedParamPerms_2225_);
return v_res_2237_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3(lean_object* v_fixedParamPerms_2238_, lean_object* v_xs_2239_, lean_object* v_as_2240_, lean_object* v_i_2241_, lean_object* v_j_2242_, lean_object* v_inv_2243_, lean_object* v_bs_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_){
_start:
{
lean_object* v___x_2250_; 
v___x_2250_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___redArg(v_fixedParamPerms_2238_, v_xs_2239_, v_as_2240_, v_i_2241_, v_j_2242_, v_bs_2244_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_);
return v___x_2250_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___boxed(lean_object* v_fixedParamPerms_2251_, lean_object* v_xs_2252_, lean_object* v_as_2253_, lean_object* v_i_2254_, lean_object* v_j_2255_, lean_object* v_inv_2256_, lean_object* v_bs_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_){
_start:
{
lean_object* v_res_2263_; 
v_res_2263_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3(v_fixedParamPerms_2251_, v_xs_2252_, v_as_2253_, v_i_2254_, v_j_2255_, v_inv_2256_, v_bs_2257_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_);
lean_dec(v___y_2261_);
lean_dec_ref(v___y_2260_);
lean_dec(v___y_2259_);
lean_dec_ref(v___y_2258_);
lean_dec_ref(v_as_2253_);
lean_dec_ref(v_fixedParamPerms_2251_);
return v_res_2263_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14(lean_object* v_00_u03b3_2264_, lean_object* v_msg_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_){
_start:
{
lean_object* v___x_2271_; 
v___x_2271_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg(v_msg_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_);
return v___x_2271_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___boxed(lean_object* v_00_u03b3_2272_, lean_object* v_msg_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_){
_start:
{
lean_object* v_res_2279_; 
v_res_2279_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14(v_00_u03b3_2272_, v_msg_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_);
lean_dec(v___y_2277_);
lean_dec_ref(v___y_2276_);
lean_dec(v___y_2275_);
lean_dec_ref(v___y_2274_);
return v_res_2279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6(lean_object* v_00_u03b3_2280_, lean_object* v_00_u03b1_2281_, lean_object* v_f_2282_, lean_object* v_positions_2283_, lean_object* v_ys_2284_, lean_object* v_xs_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_){
_start:
{
lean_object* v___x_2291_; 
v___x_2291_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg(v_f_2282_, v_positions_2283_, v_ys_2284_, v_xs_2285_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_);
return v___x_2291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___boxed(lean_object* v_00_u03b3_2292_, lean_object* v_00_u03b1_2293_, lean_object* v_f_2294_, lean_object* v_positions_2295_, lean_object* v_ys_2296_, lean_object* v_xs_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_){
_start:
{
lean_object* v_res_2303_; 
v_res_2303_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6(v_00_u03b3_2292_, v_00_u03b1_2293_, v_f_2294_, v_positions_2295_, v_ys_2296_, v_xs_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_);
lean_dec(v___y_2301_);
lean_dec_ref(v___y_2300_);
lean_dec(v___y_2299_);
lean_dec_ref(v___y_2298_);
lean_dec_ref(v_xs_2297_);
lean_dec_ref(v_ys_2296_);
lean_dec_ref(v_positions_2295_);
return v_res_2303_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7(lean_object* v___x_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_, lean_object* v_funTypes_2307_, lean_object* v_as_2308_, lean_object* v_i_2309_, lean_object* v_j_2310_, lean_object* v_inv_2311_, lean_object* v_bs_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_){
_start:
{
lean_object* v___x_2318_; 
v___x_2318_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg(v___x_2304_, v_a_2305_, v_a_2306_, v_funTypes_2307_, v_as_2308_, v_i_2309_, v_j_2310_, v_bs_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_);
return v___x_2318_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___boxed(lean_object* v___x_2319_, lean_object* v_a_2320_, lean_object* v_a_2321_, lean_object* v_funTypes_2322_, lean_object* v_as_2323_, lean_object* v_i_2324_, lean_object* v_j_2325_, lean_object* v_inv_2326_, lean_object* v_bs_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_){
_start:
{
lean_object* v_res_2333_; 
v_res_2333_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7(v___x_2319_, v_a_2320_, v_a_2321_, v_funTypes_2322_, v_as_2323_, v_i_2324_, v_j_2325_, v_inv_2326_, v_bs_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_);
lean_dec(v___y_2331_);
lean_dec_ref(v___y_2330_);
lean_dec(v___y_2329_);
lean_dec_ref(v___y_2328_);
lean_dec_ref(v_as_2323_);
return v_res_2333_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8(lean_object* v_fixedParamPerms_2334_, lean_object* v_xs_2335_, lean_object* v_as_2336_, lean_object* v_i_2337_, lean_object* v_j_2338_, lean_object* v_inv_2339_, lean_object* v_bs_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_){
_start:
{
lean_object* v___x_2346_; 
v___x_2346_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg(v_fixedParamPerms_2334_, v_xs_2335_, v_as_2336_, v_i_2337_, v_j_2338_, v_bs_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_);
return v___x_2346_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___boxed(lean_object* v_fixedParamPerms_2347_, lean_object* v_xs_2348_, lean_object* v_as_2349_, lean_object* v_i_2350_, lean_object* v_j_2351_, lean_object* v_inv_2352_, lean_object* v_bs_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_){
_start:
{
lean_object* v_res_2359_; 
v_res_2359_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8(v_fixedParamPerms_2347_, v_xs_2348_, v_as_2349_, v_i_2350_, v_j_2351_, v_inv_2352_, v_bs_2353_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_);
lean_dec(v___y_2357_);
lean_dec_ref(v___y_2356_);
lean_dec(v___y_2355_);
lean_dec_ref(v___y_2354_);
lean_dec_ref(v_as_2349_);
return v_res_2359_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12(lean_object* v_00_u03b1_2360_, lean_object* v_preDefs_2361_, lean_object* v_k_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_){
_start:
{
lean_object* v___x_2368_; 
v___x_2368_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v_preDefs_2361_, v_k_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_);
return v___x_2368_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___boxed(lean_object* v_00_u03b1_2369_, lean_object* v_preDefs_2370_, lean_object* v_k_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_){
_start:
{
lean_object* v_res_2377_; 
v_res_2377_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12(v_00_u03b1_2369_, v_preDefs_2370_, v_k_2371_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_);
lean_dec(v___y_2375_);
lean_dec_ref(v___y_2374_);
lean_dec(v___y_2373_);
lean_dec_ref(v___y_2372_);
return v_res_2377_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14(uint8_t v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v_recArgInfos_2381_, lean_object* v___x_2382_, lean_object* v_preDefs_2383_, lean_object* v_a_2384_, lean_object* v_as_2385_, lean_object* v_i_2386_, lean_object* v_j_2387_, lean_object* v_inv_2388_, lean_object* v_bs_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_){
_start:
{
lean_object* v___x_2395_; 
v___x_2395_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg(v_a_2378_, v_a_2379_, v_a_2380_, v_recArgInfos_2381_, v___x_2382_, v_preDefs_2383_, v_a_2384_, v_as_2385_, v_i_2386_, v_j_2387_, v_bs_2389_, v___y_2390_, v___y_2391_, v___y_2392_, v___y_2393_);
return v___x_2395_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___boxed(lean_object** _args){
lean_object* v_a_2396_ = _args[0];
lean_object* v_a_2397_ = _args[1];
lean_object* v_a_2398_ = _args[2];
lean_object* v_recArgInfos_2399_ = _args[3];
lean_object* v___x_2400_ = _args[4];
lean_object* v_preDefs_2401_ = _args[5];
lean_object* v_a_2402_ = _args[6];
lean_object* v_as_2403_ = _args[7];
lean_object* v_i_2404_ = _args[8];
lean_object* v_j_2405_ = _args[9];
lean_object* v_inv_2406_ = _args[10];
lean_object* v_bs_2407_ = _args[11];
lean_object* v___y_2408_ = _args[12];
lean_object* v___y_2409_ = _args[13];
lean_object* v___y_2410_ = _args[14];
lean_object* v___y_2411_ = _args[15];
lean_object* v___y_2412_ = _args[16];
_start:
{
uint8_t v_a_30571__boxed_2413_; lean_object* v_res_2414_; 
v_a_30571__boxed_2413_ = lean_unbox(v_a_2396_);
v_res_2414_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14(v_a_30571__boxed_2413_, v_a_2397_, v_a_2398_, v_recArgInfos_2399_, v___x_2400_, v_preDefs_2401_, v_a_2402_, v_as_2403_, v_i_2404_, v_j_2405_, v_inv_2406_, v_bs_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_);
lean_dec(v___y_2411_);
lean_dec_ref(v___y_2410_);
lean_dec(v___y_2409_);
lean_dec_ref(v___y_2408_);
lean_dec_ref(v_as_2403_);
lean_dec_ref(v_a_2398_);
lean_dec_ref(v_a_2397_);
return v_res_2414_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16_spec__29(lean_object* v_declName_2415_, uint8_t v_s_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_){
_start:
{
lean_object* v___x_2422_; 
v___x_2422_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16_spec__29___redArg(v_declName_2415_, v_s_2416_, v___y_2418_, v___y_2420_);
return v___x_2422_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16_spec__29___boxed(lean_object* v_declName_2423_, lean_object* v_s_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_){
_start:
{
uint8_t v_s_boxed_2430_; lean_object* v_res_2431_; 
v_s_boxed_2430_ = lean_unbox(v_s_2424_);
v_res_2431_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16_spec__29(v_declName_2423_, v_s_boxed_2430_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_);
lean_dec(v___y_2428_);
lean_dec_ref(v___y_2427_);
lean_dec(v___y_2426_);
lean_dec_ref(v___y_2425_);
return v_res_2431_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17(lean_object* v_xs_2432_, uint8_t v_a_2433_, lean_object* v_preDefs_2434_, lean_object* v___x_2435_, lean_object* v_as_2436_, lean_object* v_i_2437_, lean_object* v_j_2438_, lean_object* v_inv_2439_, lean_object* v_bs_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_){
_start:
{
lean_object* v___x_2446_; 
v___x_2446_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg(v_xs_2432_, v_a_2433_, v_preDefs_2434_, v___x_2435_, v_as_2436_, v_i_2437_, v_j_2438_, v_bs_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_);
return v___x_2446_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___boxed(lean_object* v_xs_2447_, lean_object* v_a_2448_, lean_object* v_preDefs_2449_, lean_object* v___x_2450_, lean_object* v_as_2451_, lean_object* v_i_2452_, lean_object* v_j_2453_, lean_object* v_inv_2454_, lean_object* v_bs_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_){
_start:
{
uint8_t v_a_30620__boxed_2461_; lean_object* v_res_2462_; 
v_a_30620__boxed_2461_ = lean_unbox(v_a_2448_);
v_res_2462_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17(v_xs_2447_, v_a_30620__boxed_2461_, v_preDefs_2449_, v___x_2450_, v_as_2451_, v_i_2452_, v_j_2453_, v_inv_2454_, v_bs_2455_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_);
lean_dec(v___y_2459_);
lean_dec_ref(v___y_2458_);
lean_dec(v___y_2457_);
lean_dec_ref(v___y_2456_);
lean_dec_ref(v_as_2451_);
lean_dec_ref(v_preDefs_2449_);
lean_dec_ref(v_xs_2447_);
return v_res_2462_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18(lean_object* v_a_2463_, lean_object* v_funTypes_2464_, lean_object* v_as_2465_, lean_object* v_i_2466_, lean_object* v_j_2467_, lean_object* v_inv_2468_, lean_object* v_bs_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_){
_start:
{
lean_object* v___x_2475_; 
v___x_2475_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___redArg(v_a_2463_, v_funTypes_2464_, v_as_2465_, v_i_2466_, v_j_2467_, v_bs_2469_, v___y_2470_, v___y_2471_, v___y_2472_, v___y_2473_);
return v___x_2475_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___boxed(lean_object* v_a_2476_, lean_object* v_funTypes_2477_, lean_object* v_as_2478_, lean_object* v_i_2479_, lean_object* v_j_2480_, lean_object* v_inv_2481_, lean_object* v_bs_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_){
_start:
{
lean_object* v_res_2488_; 
v_res_2488_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18(v_a_2476_, v_funTypes_2477_, v_as_2478_, v_i_2479_, v_j_2480_, v_inv_2481_, v_bs_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_);
lean_dec(v___y_2486_);
lean_dec_ref(v___y_2485_);
lean_dec(v___y_2484_);
lean_dec_ref(v___y_2483_);
lean_dec_ref(v_as_2478_);
lean_dec_ref(v_funTypes_2477_);
lean_dec_ref(v_a_2476_);
return v_res_2488_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19(lean_object* v_a_2489_, lean_object* v_a_2490_, lean_object* v_as_2491_, lean_object* v_i_2492_, lean_object* v_j_2493_, lean_object* v_inv_2494_, lean_object* v_bs_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_){
_start:
{
lean_object* v___x_2501_; 
v___x_2501_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___redArg(v_a_2489_, v_a_2490_, v_as_2491_, v_i_2492_, v_j_2493_, v_bs_2495_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_);
return v___x_2501_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___boxed(lean_object* v_a_2502_, lean_object* v_a_2503_, lean_object* v_as_2504_, lean_object* v_i_2505_, lean_object* v_j_2506_, lean_object* v_inv_2507_, lean_object* v_bs_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_){
_start:
{
lean_object* v_res_2514_; 
v_res_2514_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19(v_a_2502_, v_a_2503_, v_as_2504_, v_i_2505_, v_j_2506_, v_inv_2507_, v_bs_2508_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_);
lean_dec(v___y_2512_);
lean_dec_ref(v___y_2511_);
lean_dec(v___y_2510_);
lean_dec_ref(v___y_2509_);
lean_dec_ref(v_as_2504_);
lean_dec_ref(v_a_2503_);
lean_dec_ref(v_a_2502_);
return v_res_2514_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4(lean_object* v_00_u03b1_2515_, lean_object* v_msg_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_){
_start:
{
lean_object* v___x_2522_; 
v___x_2522_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg(v_msg_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_);
return v___x_2522_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___boxed(lean_object* v_00_u03b1_2523_, lean_object* v_msg_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_){
_start:
{
lean_object* v_res_2530_; 
v_res_2530_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4(v_00_u03b1_2523_, v_msg_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_);
lean_dec(v___y_2528_);
lean_dec_ref(v___y_2527_);
lean_dec(v___y_2526_);
lean_dec_ref(v___y_2525_);
return v_res_2530_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9(lean_object* v_xs_2531_, lean_object* v_ys_2532_, lean_object* v_hsz_2533_, lean_object* v_x_2534_, lean_object* v_x_2535_){
_start:
{
uint8_t v___x_2536_; 
v___x_2536_ = l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9___redArg(v_xs_2531_, v_ys_2532_, v_x_2534_);
return v___x_2536_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9___boxed(lean_object* v_xs_2537_, lean_object* v_ys_2538_, lean_object* v_hsz_2539_, lean_object* v_x_2540_, lean_object* v_x_2541_){
_start:
{
uint8_t v_res_2542_; lean_object* v_r_2543_; 
v_res_2542_ = l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9(v_xs_2537_, v_ys_2538_, v_hsz_2539_, v_x_2540_, v_x_2541_);
lean_dec_ref(v_ys_2538_);
lean_dec_ref(v_xs_2537_);
v_r_2543_ = lean_box(v_res_2542_);
return v_r_2543_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10(lean_object* v_n_2544_, lean_object* v_as_2545_, lean_object* v_lo_2546_, lean_object* v_hi_2547_, lean_object* v_w_2548_, lean_object* v_hlo_2549_, lean_object* v_hhi_2550_){
_start:
{
lean_object* v___x_2551_; 
v___x_2551_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg(v_n_2544_, v_as_2545_, v_lo_2546_, v_hi_2547_);
return v___x_2551_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___boxed(lean_object* v_n_2552_, lean_object* v_as_2553_, lean_object* v_lo_2554_, lean_object* v_hi_2555_, lean_object* v_w_2556_, lean_object* v_hlo_2557_, lean_object* v_hhi_2558_){
_start:
{
lean_object* v_res_2559_; 
v_res_2559_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10(v_n_2552_, v_as_2553_, v_lo_2554_, v_hi_2555_, v_w_2556_, v_hlo_2557_, v_hhi_2558_);
lean_dec(v_hi_2555_);
lean_dec(v_n_2552_);
return v_res_2559_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15(lean_object* v_00_u03b1_2560_, lean_object* v_00_u03b3_2561_, lean_object* v_xs_2562_, lean_object* v_f_2563_, lean_object* v_as_2564_, lean_object* v_bs_2565_, lean_object* v_i_2566_, lean_object* v_cs_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_){
_start:
{
lean_object* v___x_2573_; 
v___x_2573_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15___redArg(v_xs_2562_, v_f_2563_, v_as_2564_, v_bs_2565_, v_i_2566_, v_cs_2567_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_);
return v___x_2573_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15___boxed(lean_object* v_00_u03b1_2574_, lean_object* v_00_u03b3_2575_, lean_object* v_xs_2576_, lean_object* v_f_2577_, lean_object* v_as_2578_, lean_object* v_bs_2579_, lean_object* v_i_2580_, lean_object* v_cs_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_){
_start:
{
lean_object* v_res_2587_; 
v_res_2587_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15(v_00_u03b1_2574_, v_00_u03b3_2575_, v_xs_2576_, v_f_2577_, v_as_2578_, v_bs_2579_, v_i_2580_, v_cs_2581_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_);
lean_dec(v___y_2585_);
lean_dec_ref(v___y_2584_);
lean_dec(v___y_2583_);
lean_dec_ref(v___y_2582_);
lean_dec_ref(v_bs_2579_);
lean_dec_ref(v_as_2578_);
lean_dec_ref(v_xs_2576_);
return v_res_2587_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25(lean_object* v_env_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_){
_start:
{
lean_object* v___x_2594_; 
v___x_2594_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg(v_env_2588_, v___y_2590_, v___y_2592_);
return v___x_2594_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___boxed(lean_object* v_env_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_){
_start:
{
lean_object* v_res_2601_; 
v_res_2601_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25(v_env_2595_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_);
lean_dec(v___y_2599_);
lean_dec_ref(v___y_2598_);
lean_dec(v___y_2597_);
lean_dec_ref(v___y_2596_);
return v_res_2601_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23(lean_object* v_00_u03b1_2602_, lean_object* v_env_2603_, lean_object* v_x_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_){
_start:
{
lean_object* v___x_2610_; 
v___x_2610_ = l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23___redArg(v_env_2603_, v_x_2604_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_);
return v___x_2610_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23___boxed(lean_object* v_00_u03b1_2611_, lean_object* v_env_2612_, lean_object* v_x_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_){
_start:
{
lean_object* v_res_2619_; 
v_res_2619_ = l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23(v_00_u03b1_2611_, v_env_2612_, v_x_2613_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_);
lean_dec(v___y_2617_);
lean_dec_ref(v___y_2616_);
lean_dec(v___y_2615_);
lean_dec_ref(v___y_2614_);
return v_res_2619_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11(lean_object* v_n_2620_, lean_object* v_lo_2621_, lean_object* v_hi_2622_, lean_object* v_hhi_2623_, lean_object* v_pivot_2624_, lean_object* v_as_2625_, lean_object* v_i_2626_, lean_object* v_k_2627_, lean_object* v_ilo_2628_, lean_object* v_ik_2629_, lean_object* v_w_2630_){
_start:
{
lean_object* v___x_2631_; 
v___x_2631_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11___redArg(v_hi_2622_, v_pivot_2624_, v_as_2625_, v_i_2626_, v_k_2627_);
return v___x_2631_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11___boxed(lean_object* v_n_2632_, lean_object* v_lo_2633_, lean_object* v_hi_2634_, lean_object* v_hhi_2635_, lean_object* v_pivot_2636_, lean_object* v_as_2637_, lean_object* v_i_2638_, lean_object* v_k_2639_, lean_object* v_ilo_2640_, lean_object* v_ik_2641_, lean_object* v_w_2642_){
_start:
{
lean_object* v_res_2643_; 
v_res_2643_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11(v_n_2632_, v_lo_2633_, v_hi_2634_, v_hhi_2635_, v_pivot_2636_, v_as_2637_, v_i_2638_, v_k_2639_, v_ilo_2640_, v_ik_2641_, v_w_2642_);
lean_dec(v_pivot_2636_);
lean_dec(v_hi_2634_);
lean_dec(v_lo_2633_);
lean_dec(v_n_2632_);
return v_res_2643_;
}
}
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___lam__0(lean_object* v_x_2644_){
_start:
{
uint8_t v___x_2645_; 
v___x_2645_ = 0;
return v___x_2645_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___lam__0___boxed(lean_object* v_x_2646_){
_start:
{
uint8_t v_res_2647_; lean_object* v_r_2648_; 
v_res_2647_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___lam__0(v_x_2646_);
lean_dec(v_x_2646_);
v_r_2648_ = lean_box(v_res_2647_);
return v_r_2648_;
}
}
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___lam__1(lean_object* v_fvarId_2649_, lean_object* v_x_2650_){
_start:
{
uint8_t v___x_2651_; 
v___x_2651_ = l_Lean_instBEqFVarId_beq(v_fvarId_2649_, v_x_2650_);
return v___x_2651_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___lam__1___boxed(lean_object* v_fvarId_2652_, lean_object* v_x_2653_){
_start:
{
uint8_t v_res_2654_; lean_object* v_r_2655_; 
v_res_2654_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___lam__1(v_fvarId_2652_, v_x_2653_);
lean_dec(v_x_2653_);
lean_dec(v_fvarId_2652_);
v_r_2655_ = lean_box(v_res_2654_);
return v_r_2655_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; 
v___x_2657_ = lean_box(0);
v___x_2658_ = lean_unsigned_to_nat(16u);
v___x_2659_ = lean_mk_array(v___x_2658_, v___x_2657_);
return v___x_2659_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; 
v___x_2660_ = lean_obj_once(&l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__1, &l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__1_once, _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__1);
v___x_2661_ = lean_unsigned_to_nat(0u);
v___x_2662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2662_, 0, v___x_2661_);
lean_ctor_set(v___x_2662_, 1, v___x_2660_);
return v___x_2662_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg(lean_object* v_e_2663_, lean_object* v_fvarId_2664_, lean_object* v___y_2665_){
_start:
{
lean_object* v___x_2667_; uint8_t v_fst_2669_; lean_object* v_mctx_2670_; lean_object* v___y_2688_; lean_object* v_mctx_2693_; lean_object* v___f_2694_; lean_object* v___f_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; uint8_t v___x_2698_; 
v___x_2667_ = lean_st_ref_get(v___y_2665_);
v_mctx_2693_ = lean_ctor_get(v___x_2667_, 0);
lean_inc_ref_n(v_mctx_2693_, 2);
lean_dec(v___x_2667_);
v___f_2694_ = ((lean_object*)(l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__0));
v___f_2695_ = lean_alloc_closure((void*)(l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_2695_, 0, v_fvarId_2664_);
v___x_2696_ = lean_obj_once(&l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__2, &l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__2_once, _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__2);
v___x_2697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2697_, 0, v___x_2696_);
lean_ctor_set(v___x_2697_, 1, v_mctx_2693_);
v___x_2698_ = l_Lean_Expr_hasFVar(v_e_2663_);
if (v___x_2698_ == 0)
{
uint8_t v___x_2699_; 
v___x_2699_ = l_Lean_Expr_hasMVar(v_e_2663_);
if (v___x_2699_ == 0)
{
lean_dec_ref(v___x_2697_);
lean_dec_ref(v___f_2695_);
lean_dec_ref(v_e_2663_);
v_fst_2669_ = v___x_2699_;
v_mctx_2670_ = v_mctx_2693_;
goto v___jp_2668_;
}
else
{
lean_object* v___x_2700_; 
lean_dec_ref(v_mctx_2693_);
v___x_2700_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2695_, v___f_2694_, v_e_2663_, v___x_2697_);
v___y_2688_ = v___x_2700_;
goto v___jp_2687_;
}
}
else
{
lean_object* v___x_2701_; 
lean_dec_ref(v_mctx_2693_);
v___x_2701_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2695_, v___f_2694_, v_e_2663_, v___x_2697_);
v___y_2688_ = v___x_2701_;
goto v___jp_2687_;
}
v___jp_2668_:
{
lean_object* v___x_2671_; lean_object* v_cache_2672_; lean_object* v_zetaDeltaFVarIds_2673_; lean_object* v_postponed_2674_; lean_object* v_diag_2675_; lean_object* v___x_2677_; uint8_t v_isShared_2678_; uint8_t v_isSharedCheck_2685_; 
v___x_2671_ = lean_st_ref_take(v___y_2665_);
v_cache_2672_ = lean_ctor_get(v___x_2671_, 1);
v_zetaDeltaFVarIds_2673_ = lean_ctor_get(v___x_2671_, 2);
v_postponed_2674_ = lean_ctor_get(v___x_2671_, 3);
v_diag_2675_ = lean_ctor_get(v___x_2671_, 4);
v_isSharedCheck_2685_ = !lean_is_exclusive(v___x_2671_);
if (v_isSharedCheck_2685_ == 0)
{
lean_object* v_unused_2686_; 
v_unused_2686_ = lean_ctor_get(v___x_2671_, 0);
lean_dec(v_unused_2686_);
v___x_2677_ = v___x_2671_;
v_isShared_2678_ = v_isSharedCheck_2685_;
goto v_resetjp_2676_;
}
else
{
lean_inc(v_diag_2675_);
lean_inc(v_postponed_2674_);
lean_inc(v_zetaDeltaFVarIds_2673_);
lean_inc(v_cache_2672_);
lean_dec(v___x_2671_);
v___x_2677_ = lean_box(0);
v_isShared_2678_ = v_isSharedCheck_2685_;
goto v_resetjp_2676_;
}
v_resetjp_2676_:
{
lean_object* v___x_2680_; 
if (v_isShared_2678_ == 0)
{
lean_ctor_set(v___x_2677_, 0, v_mctx_2670_);
v___x_2680_ = v___x_2677_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2684_; 
v_reuseFailAlloc_2684_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2684_, 0, v_mctx_2670_);
lean_ctor_set(v_reuseFailAlloc_2684_, 1, v_cache_2672_);
lean_ctor_set(v_reuseFailAlloc_2684_, 2, v_zetaDeltaFVarIds_2673_);
lean_ctor_set(v_reuseFailAlloc_2684_, 3, v_postponed_2674_);
lean_ctor_set(v_reuseFailAlloc_2684_, 4, v_diag_2675_);
v___x_2680_ = v_reuseFailAlloc_2684_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; 
v___x_2681_ = lean_st_ref_set(v___y_2665_, v___x_2680_);
v___x_2682_ = lean_box(v_fst_2669_);
v___x_2683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2683_, 0, v___x_2682_);
return v___x_2683_;
}
}
}
v___jp_2687_:
{
lean_object* v_snd_2689_; lean_object* v_fst_2690_; lean_object* v_mctx_2691_; uint8_t v___x_2692_; 
v_snd_2689_ = lean_ctor_get(v___y_2688_, 1);
lean_inc(v_snd_2689_);
v_fst_2690_ = lean_ctor_get(v___y_2688_, 0);
lean_inc(v_fst_2690_);
lean_dec_ref(v___y_2688_);
v_mctx_2691_ = lean_ctor_get(v_snd_2689_, 1);
lean_inc_ref(v_mctx_2691_);
lean_dec(v_snd_2689_);
v___x_2692_ = lean_unbox(v_fst_2690_);
lean_dec(v_fst_2690_);
v_fst_2669_ = v___x_2692_;
v_mctx_2670_ = v_mctx_2691_;
goto v___jp_2668_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___boxed(lean_object* v_e_2702_, lean_object* v_fvarId_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_){
_start:
{
lean_object* v_res_2706_; 
v_res_2706_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg(v_e_2702_, v_fvarId_2703_, v___y_2704_);
lean_dec(v___y_2704_);
return v_res_2706_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5(lean_object* v_e_2707_, lean_object* v_fvarId_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_){
_start:
{
lean_object* v___x_2714_; 
v___x_2714_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg(v_e_2707_, v_fvarId_2708_, v___y_2710_);
return v___x_2714_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___boxed(lean_object* v_e_2715_, lean_object* v_fvarId_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_){
_start:
{
lean_object* v_res_2722_; 
v_res_2722_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5(v_e_2715_, v_fvarId_2716_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_);
lean_dec(v___y_2720_);
lean_dec_ref(v___y_2719_);
lean_dec(v___y_2718_);
lean_dec_ref(v___y_2717_);
return v_res_2722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg___lam__0(lean_object* v_k_2723_, lean_object* v_b_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_){
_start:
{
lean_object* v___x_2730_; 
lean_inc(v___y_2728_);
lean_inc_ref(v___y_2727_);
lean_inc(v___y_2726_);
lean_inc_ref(v___y_2725_);
v___x_2730_ = lean_apply_6(v_k_2723_, v_b_2724_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_, lean_box(0));
return v___x_2730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg___lam__0___boxed(lean_object* v_k_2731_, lean_object* v_b_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_){
_start:
{
lean_object* v_res_2738_; 
v_res_2738_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg___lam__0(v_k_2731_, v_b_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_);
lean_dec(v___y_2736_);
lean_dec_ref(v___y_2735_);
lean_dec(v___y_2734_);
lean_dec_ref(v___y_2733_);
return v_res_2738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg(lean_object* v_perm_2739_, lean_object* v_type_2740_, lean_object* v_k_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_){
_start:
{
lean_object* v___f_2747_; lean_object* v___x_2748_; 
v___f_2747_ = lean_alloc_closure((void*)(l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2747_, 0, v_k_2741_);
v___x_2748_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl(lean_box(0), v_perm_2739_, v_type_2740_, v___f_2747_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_);
if (lean_obj_tag(v___x_2748_) == 0)
{
lean_object* v_a_2749_; lean_object* v___x_2751_; uint8_t v_isShared_2752_; uint8_t v_isSharedCheck_2756_; 
v_a_2749_ = lean_ctor_get(v___x_2748_, 0);
v_isSharedCheck_2756_ = !lean_is_exclusive(v___x_2748_);
if (v_isSharedCheck_2756_ == 0)
{
v___x_2751_ = v___x_2748_;
v_isShared_2752_ = v_isSharedCheck_2756_;
goto v_resetjp_2750_;
}
else
{
lean_inc(v_a_2749_);
lean_dec(v___x_2748_);
v___x_2751_ = lean_box(0);
v_isShared_2752_ = v_isSharedCheck_2756_;
goto v_resetjp_2750_;
}
v_resetjp_2750_:
{
lean_object* v___x_2754_; 
if (v_isShared_2752_ == 0)
{
v___x_2754_ = v___x_2751_;
goto v_reusejp_2753_;
}
else
{
lean_object* v_reuseFailAlloc_2755_; 
v_reuseFailAlloc_2755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2755_, 0, v_a_2749_);
v___x_2754_ = v_reuseFailAlloc_2755_;
goto v_reusejp_2753_;
}
v_reusejp_2753_:
{
return v___x_2754_;
}
}
}
else
{
lean_object* v_a_2757_; lean_object* v___x_2759_; uint8_t v_isShared_2760_; uint8_t v_isSharedCheck_2764_; 
v_a_2757_ = lean_ctor_get(v___x_2748_, 0);
v_isSharedCheck_2764_ = !lean_is_exclusive(v___x_2748_);
if (v_isSharedCheck_2764_ == 0)
{
v___x_2759_ = v___x_2748_;
v_isShared_2760_ = v_isSharedCheck_2764_;
goto v_resetjp_2758_;
}
else
{
lean_inc(v_a_2757_);
lean_dec(v___x_2748_);
v___x_2759_ = lean_box(0);
v_isShared_2760_ = v_isSharedCheck_2764_;
goto v_resetjp_2758_;
}
v_resetjp_2758_:
{
lean_object* v___x_2762_; 
if (v_isShared_2760_ == 0)
{
v___x_2762_ = v___x_2759_;
goto v_reusejp_2761_;
}
else
{
lean_object* v_reuseFailAlloc_2763_; 
v_reuseFailAlloc_2763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2763_, 0, v_a_2757_);
v___x_2762_ = v_reuseFailAlloc_2763_;
goto v_reusejp_2761_;
}
v_reusejp_2761_:
{
return v___x_2762_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg___boxed(lean_object* v_perm_2765_, lean_object* v_type_2766_, lean_object* v_k_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_){
_start:
{
lean_object* v_res_2773_; 
v_res_2773_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg(v_perm_2765_, v_type_2766_, v_k_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_);
lean_dec(v___y_2771_);
lean_dec_ref(v___y_2770_);
lean_dec(v___y_2769_);
lean_dec_ref(v___y_2768_);
return v_res_2773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13(lean_object* v_00_u03b1_2774_, lean_object* v_perm_2775_, lean_object* v_type_2776_, lean_object* v_k_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_){
_start:
{
lean_object* v___x_2783_; 
v___x_2783_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg(v_perm_2775_, v_type_2776_, v_k_2777_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_);
return v___x_2783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___boxed(lean_object* v_00_u03b1_2784_, lean_object* v_perm_2785_, lean_object* v_type_2786_, lean_object* v_k_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_){
_start:
{
lean_object* v_res_2793_; 
v_res_2793_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13(v_00_u03b1_2784_, v_perm_2785_, v_type_2786_, v_k_2787_, v___y_2788_, v___y_2789_, v___y_2790_, v___y_2791_);
lean_dec(v___y_2791_);
lean_dec_ref(v___y_2790_);
lean_dec(v___y_2789_);
lean_dec_ref(v___y_2788_);
return v_res_2793_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1(lean_object* v_a_2794_, lean_object* v_fst_2795_, lean_object* v_fst_2796_, lean_object* v___x_2797_, lean_object* v___x_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_){
_start:
{
lean_object* v___x_2804_; 
lean_inc_ref(v_fst_2795_);
v___x_2804_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion(v_a_2794_, v_fst_2795_, v_fst_2796_, v___x_2797_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_);
if (lean_obj_tag(v___x_2804_) == 0)
{
lean_object* v_a_2805_; lean_object* v___x_2807_; uint8_t v_isShared_2808_; uint8_t v_isSharedCheck_2814_; 
v_a_2805_ = lean_ctor_get(v___x_2804_, 0);
v_isSharedCheck_2814_ = !lean_is_exclusive(v___x_2804_);
if (v_isSharedCheck_2814_ == 0)
{
v___x_2807_ = v___x_2804_;
v_isShared_2808_ = v_isSharedCheck_2814_;
goto v_resetjp_2806_;
}
else
{
lean_inc(v_a_2805_);
lean_dec(v___x_2804_);
v___x_2807_ = lean_box(0);
v_isShared_2808_ = v_isSharedCheck_2814_;
goto v_resetjp_2806_;
}
v_resetjp_2806_:
{
lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2812_; 
v___x_2809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2809_, 0, v_a_2805_);
lean_ctor_set(v___x_2809_, 1, v_fst_2795_);
v___x_2810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2810_, 0, v___x_2798_);
lean_ctor_set(v___x_2810_, 1, v___x_2809_);
if (v_isShared_2808_ == 0)
{
lean_ctor_set(v___x_2807_, 0, v___x_2810_);
v___x_2812_ = v___x_2807_;
goto v_reusejp_2811_;
}
else
{
lean_object* v_reuseFailAlloc_2813_; 
v_reuseFailAlloc_2813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2813_, 0, v___x_2810_);
v___x_2812_ = v_reuseFailAlloc_2813_;
goto v_reusejp_2811_;
}
v_reusejp_2811_:
{
return v___x_2812_;
}
}
}
else
{
lean_object* v_a_2815_; lean_object* v___x_2817_; uint8_t v_isShared_2818_; uint8_t v_isSharedCheck_2822_; 
lean_dec_ref(v___x_2798_);
lean_dec_ref(v_fst_2795_);
v_a_2815_ = lean_ctor_get(v___x_2804_, 0);
v_isSharedCheck_2822_ = !lean_is_exclusive(v___x_2804_);
if (v_isSharedCheck_2822_ == 0)
{
v___x_2817_ = v___x_2804_;
v_isShared_2818_ = v_isSharedCheck_2822_;
goto v_resetjp_2816_;
}
else
{
lean_inc(v_a_2815_);
lean_dec(v___x_2804_);
v___x_2817_ = lean_box(0);
v_isShared_2818_ = v_isSharedCheck_2822_;
goto v_resetjp_2816_;
}
v_resetjp_2816_:
{
lean_object* v___x_2820_; 
if (v_isShared_2818_ == 0)
{
v___x_2820_ = v___x_2817_;
goto v_reusejp_2819_;
}
else
{
lean_object* v_reuseFailAlloc_2821_; 
v_reuseFailAlloc_2821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2821_, 0, v_a_2815_);
v___x_2820_ = v_reuseFailAlloc_2821_;
goto v_reusejp_2819_;
}
v_reusejp_2819_:
{
return v___x_2820_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___boxed(lean_object* v_a_2823_, lean_object* v_fst_2824_, lean_object* v_fst_2825_, lean_object* v___x_2826_, lean_object* v___x_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_){
_start:
{
lean_object* v_res_2833_; 
v_res_2833_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1(v_a_2823_, v_fst_2824_, v_fst_2825_, v___x_2826_, v___x_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_);
lean_dec(v___y_2831_);
lean_dec_ref(v___y_2830_);
lean_dec(v___y_2829_);
lean_dec_ref(v___y_2828_);
return v_res_2833_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__3(size_t v_sz_2834_, size_t v_i_2835_, lean_object* v_bs_2836_){
_start:
{
uint8_t v___x_2837_; 
v___x_2837_ = lean_usize_dec_lt(v_i_2835_, v_sz_2834_);
if (v___x_2837_ == 0)
{
return v_bs_2836_;
}
else
{
lean_object* v_v_2838_; lean_object* v___x_2839_; lean_object* v_bs_x27_2840_; lean_object* v___x_2841_; size_t v___x_2842_; size_t v___x_2843_; lean_object* v___x_2844_; 
v_v_2838_ = lean_array_uget(v_bs_2836_, v_i_2835_);
v___x_2839_ = lean_unsigned_to_nat(0u);
v_bs_x27_2840_ = lean_array_uset(v_bs_2836_, v_i_2835_, v___x_2839_);
v___x_2841_ = l_Lean_Elab_Structural_RecArgInfo_indicesAndRecArgPos(v_v_2838_);
v___x_2842_ = ((size_t)1ULL);
v___x_2843_ = lean_usize_add(v_i_2835_, v___x_2842_);
v___x_2844_ = lean_array_uset(v_bs_x27_2840_, v_i_2835_, v___x_2841_);
v_i_2835_ = v___x_2843_;
v_bs_2836_ = v___x_2844_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__3___boxed(lean_object* v_sz_2846_, lean_object* v_i_2847_, lean_object* v_bs_2848_){
_start:
{
size_t v_sz_boxed_2849_; size_t v_i_boxed_2850_; lean_object* v_res_2851_; 
v_sz_boxed_2849_ = lean_unbox_usize(v_sz_2846_);
lean_dec(v_sz_2846_);
v_i_boxed_2850_ = lean_unbox_usize(v_i_2847_);
lean_dec(v_i_2847_);
v_res_2851_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__3(v_sz_boxed_2849_, v_i_boxed_2850_, v_bs_2848_);
return v_res_2851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___redArg(lean_object* v_lctx_2852_, lean_object* v_localInsts_2853_, lean_object* v_x_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_){
_start:
{
lean_object* v___x_2860_; 
v___x_2860_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_2852_, v_localInsts_2853_, v_x_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_);
if (lean_obj_tag(v___x_2860_) == 0)
{
lean_object* v_a_2861_; lean_object* v___x_2863_; uint8_t v_isShared_2864_; uint8_t v_isSharedCheck_2868_; 
v_a_2861_ = lean_ctor_get(v___x_2860_, 0);
v_isSharedCheck_2868_ = !lean_is_exclusive(v___x_2860_);
if (v_isSharedCheck_2868_ == 0)
{
v___x_2863_ = v___x_2860_;
v_isShared_2864_ = v_isSharedCheck_2868_;
goto v_resetjp_2862_;
}
else
{
lean_inc(v_a_2861_);
lean_dec(v___x_2860_);
v___x_2863_ = lean_box(0);
v_isShared_2864_ = v_isSharedCheck_2868_;
goto v_resetjp_2862_;
}
v_resetjp_2862_:
{
lean_object* v___x_2866_; 
if (v_isShared_2864_ == 0)
{
v___x_2866_ = v___x_2863_;
goto v_reusejp_2865_;
}
else
{
lean_object* v_reuseFailAlloc_2867_; 
v_reuseFailAlloc_2867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2867_, 0, v_a_2861_);
v___x_2866_ = v_reuseFailAlloc_2867_;
goto v_reusejp_2865_;
}
v_reusejp_2865_:
{
return v___x_2866_;
}
}
}
else
{
lean_object* v_a_2869_; lean_object* v___x_2871_; uint8_t v_isShared_2872_; uint8_t v_isSharedCheck_2876_; 
v_a_2869_ = lean_ctor_get(v___x_2860_, 0);
v_isSharedCheck_2876_ = !lean_is_exclusive(v___x_2860_);
if (v_isSharedCheck_2876_ == 0)
{
v___x_2871_ = v___x_2860_;
v_isShared_2872_ = v_isSharedCheck_2876_;
goto v_resetjp_2870_;
}
else
{
lean_inc(v_a_2869_);
lean_dec(v___x_2860_);
v___x_2871_ = lean_box(0);
v_isShared_2872_ = v_isSharedCheck_2876_;
goto v_resetjp_2870_;
}
v_resetjp_2870_:
{
lean_object* v___x_2874_; 
if (v_isShared_2872_ == 0)
{
v___x_2874_ = v___x_2871_;
goto v_reusejp_2873_;
}
else
{
lean_object* v_reuseFailAlloc_2875_; 
v_reuseFailAlloc_2875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2875_, 0, v_a_2869_);
v___x_2874_ = v_reuseFailAlloc_2875_;
goto v_reusejp_2873_;
}
v_reusejp_2873_:
{
return v___x_2874_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___redArg___boxed(lean_object* v_lctx_2877_, lean_object* v_localInsts_2878_, lean_object* v_x_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_){
_start:
{
lean_object* v_res_2885_; 
v_res_2885_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___redArg(v_lctx_2877_, v_localInsts_2878_, v_x_2879_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_);
lean_dec(v___y_2883_);
lean_dec_ref(v___y_2882_);
lean_dec(v___y_2881_);
lean_dec_ref(v___y_2880_);
return v_res_2885_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__12(lean_object* v_as_2886_, size_t v_i_2887_, size_t v_stop_2888_, lean_object* v_b_2889_){
_start:
{
uint8_t v___x_2890_; 
v___x_2890_ = lean_usize_dec_eq(v_i_2887_, v_stop_2888_);
if (v___x_2890_ == 0)
{
lean_object* v___x_2891_; lean_object* v___x_2892_; size_t v___x_2893_; size_t v___x_2894_; 
v___x_2891_ = lean_array_uget_borrowed(v_as_2886_, v_i_2887_);
lean_inc(v___x_2891_);
v___x_2892_ = lean_local_ctx_erase(v_b_2889_, v___x_2891_);
v___x_2893_ = ((size_t)1ULL);
v___x_2894_ = lean_usize_add(v_i_2887_, v___x_2893_);
v_i_2887_ = v___x_2894_;
v_b_2889_ = v___x_2892_;
goto _start;
}
else
{
return v_b_2889_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__12___boxed(lean_object* v_as_2896_, lean_object* v_i_2897_, lean_object* v_stop_2898_, lean_object* v_b_2899_){
_start:
{
size_t v_i_boxed_2900_; size_t v_stop_boxed_2901_; lean_object* v_res_2902_; 
v_i_boxed_2900_ = lean_unbox_usize(v_i_2897_);
lean_dec(v_i_2897_);
v_stop_boxed_2901_ = lean_unbox_usize(v_stop_2898_);
lean_dec(v_stop_2898_);
v_res_2902_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__12(v_as_2896_, v_i_boxed_2900_, v_stop_boxed_2901_, v_b_2899_);
lean_dec_ref(v_as_2896_);
return v_res_2902_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9_spec__11(lean_object* v_a_2903_, lean_object* v_as_2904_, size_t v_i_2905_, size_t v_stop_2906_){
_start:
{
uint8_t v___x_2907_; 
v___x_2907_ = lean_usize_dec_eq(v_i_2905_, v_stop_2906_);
if (v___x_2907_ == 0)
{
lean_object* v___x_2908_; uint8_t v___x_2909_; 
v___x_2908_ = lean_array_uget_borrowed(v_as_2904_, v_i_2905_);
v___x_2909_ = l_Lean_instBEqFVarId_beq(v_a_2903_, v___x_2908_);
if (v___x_2909_ == 0)
{
size_t v___x_2910_; size_t v___x_2911_; 
v___x_2910_ = ((size_t)1ULL);
v___x_2911_ = lean_usize_add(v_i_2905_, v___x_2910_);
v_i_2905_ = v___x_2911_;
goto _start;
}
else
{
return v___x_2909_;
}
}
else
{
uint8_t v___x_2913_; 
v___x_2913_ = 0;
return v___x_2913_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9_spec__11___boxed(lean_object* v_a_2914_, lean_object* v_as_2915_, lean_object* v_i_2916_, lean_object* v_stop_2917_){
_start:
{
size_t v_i_boxed_2918_; size_t v_stop_boxed_2919_; uint8_t v_res_2920_; lean_object* v_r_2921_; 
v_i_boxed_2918_ = lean_unbox_usize(v_i_2916_);
lean_dec(v_i_2916_);
v_stop_boxed_2919_ = lean_unbox_usize(v_stop_2917_);
lean_dec(v_stop_2917_);
v_res_2920_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9_spec__11(v_a_2914_, v_as_2915_, v_i_boxed_2918_, v_stop_boxed_2919_);
lean_dec_ref(v_as_2915_);
lean_dec(v_a_2914_);
v_r_2921_ = lean_box(v_res_2920_);
return v_r_2921_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9(lean_object* v_as_2922_, lean_object* v_a_2923_){
_start:
{
lean_object* v___x_2924_; lean_object* v___x_2925_; uint8_t v___x_2926_; 
v___x_2924_ = lean_unsigned_to_nat(0u);
v___x_2925_ = lean_array_get_size(v_as_2922_);
v___x_2926_ = lean_nat_dec_lt(v___x_2924_, v___x_2925_);
if (v___x_2926_ == 0)
{
return v___x_2926_;
}
else
{
if (v___x_2926_ == 0)
{
return v___x_2926_;
}
else
{
size_t v___x_2927_; size_t v___x_2928_; uint8_t v___x_2929_; 
v___x_2927_ = ((size_t)0ULL);
v___x_2928_ = lean_usize_of_nat(v___x_2925_);
v___x_2929_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9_spec__11(v_a_2923_, v_as_2922_, v___x_2927_, v___x_2928_);
return v___x_2929_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9___boxed(lean_object* v_as_2930_, lean_object* v_a_2931_){
_start:
{
uint8_t v_res_2932_; lean_object* v_r_2933_; 
v_res_2932_ = l_Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9(v_as_2930_, v_a_2931_);
lean_dec(v_a_2931_);
lean_dec_ref(v_as_2930_);
v_r_2933_ = lean_box(v_res_2932_);
return v_r_2933_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__11(lean_object* v_fvarIds_2934_, lean_object* v_as_2935_, size_t v_i_2936_, size_t v_stop_2937_, lean_object* v_b_2938_){
_start:
{
lean_object* v___y_2940_; uint8_t v___x_2944_; 
v___x_2944_ = lean_usize_dec_eq(v_i_2936_, v_stop_2937_);
if (v___x_2944_ == 0)
{
lean_object* v___x_2945_; lean_object* v_fvar_2946_; lean_object* v___x_2947_; uint8_t v___x_2948_; 
v___x_2945_ = lean_array_uget_borrowed(v_as_2935_, v_i_2936_);
v_fvar_2946_ = lean_ctor_get(v___x_2945_, 1);
v___x_2947_ = l_Lean_Expr_fvarId_x21(v_fvar_2946_);
v___x_2948_ = l_Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9(v_fvarIds_2934_, v___x_2947_);
lean_dec(v___x_2947_);
if (v___x_2948_ == 0)
{
lean_object* v___x_2949_; 
lean_inc(v___x_2945_);
v___x_2949_ = lean_array_push(v_b_2938_, v___x_2945_);
v___y_2940_ = v___x_2949_;
goto v___jp_2939_;
}
else
{
v___y_2940_ = v_b_2938_;
goto v___jp_2939_;
}
}
else
{
return v_b_2938_;
}
v___jp_2939_:
{
size_t v___x_2941_; size_t v___x_2942_; 
v___x_2941_ = ((size_t)1ULL);
v___x_2942_ = lean_usize_add(v_i_2936_, v___x_2941_);
v_i_2936_ = v___x_2942_;
v_b_2938_ = v___y_2940_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__11___boxed(lean_object* v_fvarIds_2950_, lean_object* v_as_2951_, lean_object* v_i_2952_, lean_object* v_stop_2953_, lean_object* v_b_2954_){
_start:
{
size_t v_i_boxed_2955_; size_t v_stop_boxed_2956_; lean_object* v_res_2957_; 
v_i_boxed_2955_ = lean_unbox_usize(v_i_2952_);
lean_dec(v_i_2952_);
v_stop_boxed_2956_ = lean_unbox_usize(v_stop_2953_);
lean_dec(v_stop_2953_);
v_res_2957_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__11(v_fvarIds_2950_, v_as_2951_, v_i_boxed_2955_, v_stop_boxed_2956_, v_b_2954_);
lean_dec_ref(v_as_2951_);
lean_dec_ref(v_fvarIds_2950_);
return v_res_2957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___redArg(lean_object* v_fvarIds_2960_, lean_object* v_k_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_){
_start:
{
lean_object* v_lctx_2967_; lean_object* v_localInstances_2968_; lean_object* v___x_2969_; lean_object* v___y_2971_; lean_object* v___x_2986_; uint8_t v___x_2987_; 
v_lctx_2967_ = lean_ctor_get(v___y_2962_, 2);
v_localInstances_2968_ = lean_ctor_get(v___y_2962_, 3);
v___x_2969_ = lean_unsigned_to_nat(0u);
v___x_2986_ = lean_array_get_size(v_fvarIds_2960_);
v___x_2987_ = lean_nat_dec_lt(v___x_2969_, v___x_2986_);
if (v___x_2987_ == 0)
{
lean_inc_ref(v_lctx_2967_);
v___y_2971_ = v_lctx_2967_;
goto v___jp_2970_;
}
else
{
uint8_t v___x_2988_; 
v___x_2988_ = lean_nat_dec_le(v___x_2986_, v___x_2986_);
if (v___x_2988_ == 0)
{
if (v___x_2987_ == 0)
{
lean_inc_ref(v_lctx_2967_);
v___y_2971_ = v_lctx_2967_;
goto v___jp_2970_;
}
else
{
size_t v___x_2989_; size_t v___x_2990_; lean_object* v___x_2991_; 
v___x_2989_ = ((size_t)0ULL);
v___x_2990_ = lean_usize_of_nat(v___x_2986_);
lean_inc_ref(v_lctx_2967_);
v___x_2991_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__12(v_fvarIds_2960_, v___x_2989_, v___x_2990_, v_lctx_2967_);
v___y_2971_ = v___x_2991_;
goto v___jp_2970_;
}
}
else
{
size_t v___x_2992_; size_t v___x_2993_; lean_object* v___x_2994_; 
v___x_2992_ = ((size_t)0ULL);
v___x_2993_ = lean_usize_of_nat(v___x_2986_);
lean_inc_ref(v_lctx_2967_);
v___x_2994_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__12(v_fvarIds_2960_, v___x_2992_, v___x_2993_, v_lctx_2967_);
v___y_2971_ = v___x_2994_;
goto v___jp_2970_;
}
}
v___jp_2970_:
{
lean_object* v___x_2972_; lean_object* v___x_2973_; uint8_t v___x_2974_; 
v___x_2972_ = lean_array_get_size(v_localInstances_2968_);
v___x_2973_ = ((lean_object*)(l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___redArg___closed__0));
v___x_2974_ = lean_nat_dec_lt(v___x_2969_, v___x_2972_);
if (v___x_2974_ == 0)
{
lean_object* v___x_2975_; 
v___x_2975_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___redArg(v___y_2971_, v___x_2973_, v_k_2961_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_);
return v___x_2975_;
}
else
{
uint8_t v___x_2976_; 
v___x_2976_ = lean_nat_dec_le(v___x_2972_, v___x_2972_);
if (v___x_2976_ == 0)
{
if (v___x_2974_ == 0)
{
lean_object* v___x_2977_; 
v___x_2977_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___redArg(v___y_2971_, v___x_2973_, v_k_2961_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_);
return v___x_2977_;
}
else
{
size_t v___x_2978_; size_t v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; 
v___x_2978_ = ((size_t)0ULL);
v___x_2979_ = lean_usize_of_nat(v___x_2972_);
v___x_2980_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__11(v_fvarIds_2960_, v_localInstances_2968_, v___x_2978_, v___x_2979_, v___x_2973_);
v___x_2981_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___redArg(v___y_2971_, v___x_2980_, v_k_2961_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_);
return v___x_2981_;
}
}
else
{
size_t v___x_2982_; size_t v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; 
v___x_2982_ = ((size_t)0ULL);
v___x_2983_ = lean_usize_of_nat(v___x_2972_);
v___x_2984_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__11(v_fvarIds_2960_, v_localInstances_2968_, v___x_2982_, v___x_2983_, v___x_2973_);
v___x_2985_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___redArg(v___y_2971_, v___x_2984_, v_k_2961_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_);
return v___x_2985_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___redArg___boxed(lean_object* v_fvarIds_2995_, lean_object* v_k_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_){
_start:
{
lean_object* v_res_3002_; 
v_res_3002_ = l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___redArg(v_fvarIds_2995_, v_k_2996_, v___y_2997_, v___y_2998_, v___y_2999_, v___y_3000_);
lean_dec(v___y_3000_);
lean_dec_ref(v___y_2999_);
lean_dec(v___y_2998_);
lean_dec_ref(v___y_2997_);
lean_dec_ref(v_fvarIds_2995_);
return v_res_3002_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__14_spec__17_spec__21(lean_object* v_x_3003_, lean_object* v_x_3004_, lean_object* v_x_3005_){
_start:
{
if (lean_obj_tag(v_x_3005_) == 0)
{
lean_dec(v_x_3003_);
return v_x_3004_;
}
else
{
lean_object* v_head_3006_; lean_object* v_tail_3007_; lean_object* v___x_3009_; uint8_t v_isShared_3010_; uint8_t v_isSharedCheck_3017_; 
v_head_3006_ = lean_ctor_get(v_x_3005_, 0);
v_tail_3007_ = lean_ctor_get(v_x_3005_, 1);
v_isSharedCheck_3017_ = !lean_is_exclusive(v_x_3005_);
if (v_isSharedCheck_3017_ == 0)
{
v___x_3009_ = v_x_3005_;
v_isShared_3010_ = v_isSharedCheck_3017_;
goto v_resetjp_3008_;
}
else
{
lean_inc(v_tail_3007_);
lean_inc(v_head_3006_);
lean_dec(v_x_3005_);
v___x_3009_ = lean_box(0);
v_isShared_3010_ = v_isSharedCheck_3017_;
goto v_resetjp_3008_;
}
v_resetjp_3008_:
{
lean_object* v___x_3012_; 
lean_inc(v_x_3003_);
if (v_isShared_3010_ == 0)
{
lean_ctor_set_tag(v___x_3009_, 5);
lean_ctor_set(v___x_3009_, 1, v_x_3003_);
lean_ctor_set(v___x_3009_, 0, v_x_3004_);
v___x_3012_ = v___x_3009_;
goto v_reusejp_3011_;
}
else
{
lean_object* v_reuseFailAlloc_3016_; 
v_reuseFailAlloc_3016_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3016_, 0, v_x_3004_);
lean_ctor_set(v_reuseFailAlloc_3016_, 1, v_x_3003_);
v___x_3012_ = v_reuseFailAlloc_3016_;
goto v_reusejp_3011_;
}
v_reusejp_3011_:
{
lean_object* v___x_3013_; lean_object* v___x_3014_; 
v___x_3013_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(v_head_3006_);
v___x_3014_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3014_, 0, v___x_3012_);
lean_ctor_set(v___x_3014_, 1, v___x_3013_);
v_x_3004_ = v___x_3014_;
v_x_3005_ = v_tail_3007_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__14_spec__17(lean_object* v_x_3018_, lean_object* v_x_3019_, lean_object* v_x_3020_){
_start:
{
if (lean_obj_tag(v_x_3020_) == 0)
{
lean_dec(v_x_3018_);
return v_x_3019_;
}
else
{
lean_object* v_head_3021_; lean_object* v_tail_3022_; lean_object* v___x_3024_; uint8_t v_isShared_3025_; uint8_t v_isSharedCheck_3032_; 
v_head_3021_ = lean_ctor_get(v_x_3020_, 0);
v_tail_3022_ = lean_ctor_get(v_x_3020_, 1);
v_isSharedCheck_3032_ = !lean_is_exclusive(v_x_3020_);
if (v_isSharedCheck_3032_ == 0)
{
v___x_3024_ = v_x_3020_;
v_isShared_3025_ = v_isSharedCheck_3032_;
goto v_resetjp_3023_;
}
else
{
lean_inc(v_tail_3022_);
lean_inc(v_head_3021_);
lean_dec(v_x_3020_);
v___x_3024_ = lean_box(0);
v_isShared_3025_ = v_isSharedCheck_3032_;
goto v_resetjp_3023_;
}
v_resetjp_3023_:
{
lean_object* v___x_3027_; 
lean_inc(v_x_3018_);
if (v_isShared_3025_ == 0)
{
lean_ctor_set_tag(v___x_3024_, 5);
lean_ctor_set(v___x_3024_, 1, v_x_3018_);
lean_ctor_set(v___x_3024_, 0, v_x_3019_);
v___x_3027_ = v___x_3024_;
goto v_reusejp_3026_;
}
else
{
lean_object* v_reuseFailAlloc_3031_; 
v_reuseFailAlloc_3031_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3031_, 0, v_x_3019_);
lean_ctor_set(v_reuseFailAlloc_3031_, 1, v_x_3018_);
v___x_3027_ = v_reuseFailAlloc_3031_;
goto v_reusejp_3026_;
}
v_reusejp_3026_:
{
lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; 
v___x_3028_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(v_head_3021_);
v___x_3029_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3029_, 0, v___x_3027_);
lean_ctor_set(v___x_3029_, 1, v___x_3028_);
v___x_3030_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__14_spec__17_spec__21(v_x_3018_, v___x_3029_, v_tail_3022_);
return v___x_3030_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__14(lean_object* v_x_3033_, lean_object* v_x_3034_){
_start:
{
if (lean_obj_tag(v_x_3033_) == 0)
{
lean_object* v___x_3035_; 
lean_dec(v_x_3034_);
v___x_3035_ = lean_box(0);
return v___x_3035_;
}
else
{
lean_object* v_tail_3036_; 
v_tail_3036_ = lean_ctor_get(v_x_3033_, 1);
if (lean_obj_tag(v_tail_3036_) == 0)
{
lean_object* v_head_3037_; lean_object* v___x_3038_; 
lean_dec(v_x_3034_);
v_head_3037_ = lean_ctor_get(v_x_3033_, 0);
lean_inc(v_head_3037_);
lean_dec_ref(v_x_3033_);
v___x_3038_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(v_head_3037_);
return v___x_3038_;
}
else
{
lean_object* v_head_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; 
lean_inc(v_tail_3036_);
v_head_3039_ = lean_ctor_get(v_x_3033_, 0);
lean_inc(v_head_3039_);
lean_dec_ref(v_x_3033_);
v___x_3040_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(v_head_3039_);
v___x_3041_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__14_spec__17(v_x_3034_, v___x_3040_, v_tail_3036_);
return v___x_3041_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__5(void){
_start:
{
lean_object* v___x_3050_; lean_object* v___x_3051_; 
v___x_3050_ = ((lean_object*)(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__0));
v___x_3051_ = lean_string_length(v___x_3050_);
return v___x_3051_;
}
}
static lean_object* _init_l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__6(void){
_start:
{
lean_object* v___x_3052_; lean_object* v___x_3053_; 
v___x_3052_ = lean_obj_once(&l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__5, &l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__5_once, _init_l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__5);
v___x_3053_ = lean_nat_to_int(v___x_3052_);
return v___x_3053_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10(lean_object* v_xs_3061_){
_start:
{
lean_object* v___x_3062_; lean_object* v___x_3063_; uint8_t v___x_3064_; 
v___x_3062_ = lean_array_get_size(v_xs_3061_);
v___x_3063_ = lean_unsigned_to_nat(0u);
v___x_3064_ = lean_nat_dec_eq(v___x_3062_, v___x_3063_);
if (v___x_3064_ == 0)
{
lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; 
v___x_3065_ = lean_array_to_list(v_xs_3061_);
v___x_3066_ = ((lean_object*)(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__3));
v___x_3067_ = l_Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__14(v___x_3065_, v___x_3066_);
v___x_3068_ = lean_obj_once(&l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__6, &l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__6_once, _init_l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__6);
v___x_3069_ = ((lean_object*)(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__7));
v___x_3070_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3070_, 0, v___x_3069_);
lean_ctor_set(v___x_3070_, 1, v___x_3067_);
v___x_3071_ = ((lean_object*)(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__8));
v___x_3072_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3072_, 0, v___x_3070_);
lean_ctor_set(v___x_3072_, 1, v___x_3071_);
v___x_3073_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3073_, 0, v___x_3068_);
lean_ctor_set(v___x_3073_, 1, v___x_3072_);
v___x_3074_ = l_Std_Format_fill(v___x_3073_);
return v___x_3074_;
}
else
{
lean_object* v___x_3075_; 
lean_dec_ref(v_xs_3061_);
v___x_3075_ = ((lean_object*)(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__10));
return v___x_3075_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__11(size_t v_sz_3076_, size_t v_i_3077_, lean_object* v_bs_3078_){
_start:
{
uint8_t v___x_3079_; 
v___x_3079_ = lean_usize_dec_lt(v_i_3077_, v_sz_3076_);
if (v___x_3079_ == 0)
{
return v_bs_3078_;
}
else
{
lean_object* v_v_3080_; lean_object* v___x_3081_; lean_object* v_bs_x27_3082_; lean_object* v___x_3083_; size_t v___x_3084_; size_t v___x_3085_; lean_object* v___x_3086_; 
v_v_3080_ = lean_array_uget(v_bs_3078_, v_i_3077_);
v___x_3081_ = lean_unsigned_to_nat(0u);
v_bs_x27_3082_ = lean_array_uset(v_bs_3078_, v_i_3077_, v___x_3081_);
v___x_3083_ = l_Lean_mkFVar(v_v_3080_);
v___x_3084_ = ((size_t)1ULL);
v___x_3085_ = lean_usize_add(v_i_3077_, v___x_3084_);
v___x_3086_ = lean_array_uset(v_bs_x27_3082_, v_i_3077_, v___x_3083_);
v_i_3077_ = v___x_3085_;
v_bs_3078_ = v___x_3086_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__11___boxed(lean_object* v_sz_3088_, lean_object* v_i_3089_, lean_object* v_bs_3090_){
_start:
{
size_t v_sz_boxed_3091_; size_t v_i_boxed_3092_; lean_object* v_res_3093_; 
v_sz_boxed_3091_ = lean_unbox_usize(v_sz_3088_);
lean_dec(v_sz_3088_);
v_i_boxed_3092_ = lean_unbox_usize(v_i_3089_);
lean_dec(v_i_3089_);
v_res_3093_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__11(v_sz_boxed_3091_, v_i_boxed_3092_, v_bs_3090_);
return v_res_3093_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg(lean_object* v_fst_3094_, lean_object* v_as_3095_, lean_object* v_i_3096_, lean_object* v_j_3097_, lean_object* v_bs_3098_){
_start:
{
lean_object* v_zero_3099_; uint8_t v_isZero_3100_; 
v_zero_3099_ = lean_unsigned_to_nat(0u);
v_isZero_3100_ = lean_nat_dec_eq(v_i_3096_, v_zero_3099_);
if (v_isZero_3100_ == 1)
{
lean_dec(v_j_3097_);
lean_dec(v_i_3096_);
return v_bs_3098_;
}
else
{
lean_object* v___x_3101_; lean_object* v_fnName_3102_; lean_object* v_recArgPos_3103_; lean_object* v_indicesPos_3104_; lean_object* v_indGroupInst_3105_; lean_object* v_indIdx_3106_; lean_object* v___x_3108_; uint8_t v_isShared_3109_; uint8_t v_isSharedCheck_3121_; 
v___x_3101_ = lean_array_fget(v_as_3095_, v_j_3097_);
v_fnName_3102_ = lean_ctor_get(v___x_3101_, 0);
v_recArgPos_3103_ = lean_ctor_get(v___x_3101_, 2);
v_indicesPos_3104_ = lean_ctor_get(v___x_3101_, 3);
v_indGroupInst_3105_ = lean_ctor_get(v___x_3101_, 4);
v_indIdx_3106_ = lean_ctor_get(v___x_3101_, 5);
v_isSharedCheck_3121_ = !lean_is_exclusive(v___x_3101_);
if (v_isSharedCheck_3121_ == 0)
{
lean_object* v_unused_3122_; 
v_unused_3122_ = lean_ctor_get(v___x_3101_, 1);
lean_dec(v_unused_3122_);
v___x_3108_ = v___x_3101_;
v_isShared_3109_ = v_isSharedCheck_3121_;
goto v_resetjp_3107_;
}
else
{
lean_inc(v_indIdx_3106_);
lean_inc(v_indGroupInst_3105_);
lean_inc(v_indicesPos_3104_);
lean_inc(v_recArgPos_3103_);
lean_inc(v_fnName_3102_);
lean_dec(v___x_3101_);
v___x_3108_ = lean_box(0);
v_isShared_3109_ = v_isSharedCheck_3121_;
goto v_resetjp_3107_;
}
v_resetjp_3107_:
{
lean_object* v_perms_3110_; lean_object* v___x_3111_; lean_object* v_one_3112_; lean_object* v_n_3113_; lean_object* v___x_3114_; lean_object* v___x_3116_; 
v_perms_3110_ = lean_ctor_get(v_fst_3094_, 1);
v___x_3111_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0, &l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0_once, _init_l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0);
v_one_3112_ = lean_unsigned_to_nat(1u);
v_n_3113_ = lean_nat_sub(v_i_3096_, v_one_3112_);
lean_dec(v_i_3096_);
v___x_3114_ = lean_array_get_borrowed(v___x_3111_, v_perms_3110_, v_j_3097_);
lean_inc(v___x_3114_);
if (v_isShared_3109_ == 0)
{
lean_ctor_set(v___x_3108_, 1, v___x_3114_);
v___x_3116_ = v___x_3108_;
goto v_reusejp_3115_;
}
else
{
lean_object* v_reuseFailAlloc_3120_; 
v_reuseFailAlloc_3120_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3120_, 0, v_fnName_3102_);
lean_ctor_set(v_reuseFailAlloc_3120_, 1, v___x_3114_);
lean_ctor_set(v_reuseFailAlloc_3120_, 2, v_recArgPos_3103_);
lean_ctor_set(v_reuseFailAlloc_3120_, 3, v_indicesPos_3104_);
lean_ctor_set(v_reuseFailAlloc_3120_, 4, v_indGroupInst_3105_);
lean_ctor_set(v_reuseFailAlloc_3120_, 5, v_indIdx_3106_);
v___x_3116_ = v_reuseFailAlloc_3120_;
goto v_reusejp_3115_;
}
v_reusejp_3115_:
{
lean_object* v___x_3117_; lean_object* v___x_3118_; 
v___x_3117_ = lean_nat_add(v_j_3097_, v_one_3112_);
lean_dec(v_j_3097_);
v___x_3118_ = lean_array_push(v_bs_3098_, v___x_3116_);
v_i_3096_ = v_n_3113_;
v_j_3097_ = v___x_3117_;
v_bs_3098_ = v___x_3118_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg___boxed(lean_object* v_fst_3123_, lean_object* v_as_3124_, lean_object* v_i_3125_, lean_object* v_j_3126_, lean_object* v_bs_3127_){
_start:
{
lean_object* v_res_3128_; 
v_res_3128_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg(v_fst_3123_, v_as_3124_, v_i_3125_, v_j_3126_, v_bs_3127_);
lean_dec_ref(v_as_3124_);
lean_dec_ref(v_fst_3123_);
return v_res_3128_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__2(size_t v_sz_3129_, size_t v_i_3130_, lean_object* v_bs_3131_){
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
lean_object* v_v_3133_; lean_object* v_recArgPos_3134_; lean_object* v___x_3135_; lean_object* v_bs_x27_3136_; size_t v___x_3137_; size_t v___x_3138_; lean_object* v___x_3139_; 
v_v_3133_ = lean_array_uget_borrowed(v_bs_3131_, v_i_3130_);
v_recArgPos_3134_ = lean_ctor_get(v_v_3133_, 2);
lean_inc(v_recArgPos_3134_);
v___x_3135_ = lean_unsigned_to_nat(0u);
v_bs_x27_3136_ = lean_array_uset(v_bs_3131_, v_i_3130_, v___x_3135_);
v___x_3137_ = ((size_t)1ULL);
v___x_3138_ = lean_usize_add(v_i_3130_, v___x_3137_);
v___x_3139_ = lean_array_uset(v_bs_x27_3136_, v_i_3130_, v_recArgPos_3134_);
v_i_3130_ = v___x_3138_;
v_bs_3131_ = v___x_3139_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__2___boxed(lean_object* v_sz_3141_, lean_object* v_i_3142_, lean_object* v_bs_3143_){
_start:
{
size_t v_sz_boxed_3144_; size_t v_i_boxed_3145_; lean_object* v_res_3146_; 
v_sz_boxed_3144_ = lean_unbox_usize(v_sz_3141_);
lean_dec(v_sz_3141_);
v_i_boxed_3145_ = lean_unbox_usize(v_i_3142_);
lean_dec(v_i_3142_);
v_res_3146_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__2(v_sz_boxed_3144_, v_i_boxed_3145_, v_bs_3143_);
return v_res_3146_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__1(void){
_start:
{
lean_object* v___x_3148_; lean_object* v___x_3149_; 
v___x_3148_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__0));
v___x_3149_ = l_Lean_stringToMessageData(v___x_3148_);
return v___x_3149_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__3(void){
_start:
{
lean_object* v___x_3151_; lean_object* v___x_3152_; 
v___x_3151_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__2));
v___x_3152_ = l_Lean_stringToMessageData(v___x_3151_);
return v___x_3152_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__5(void){
_start:
{
lean_object* v___x_3154_; lean_object* v___x_3155_; 
v___x_3154_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__4));
v___x_3155_ = l_Lean_stringToMessageData(v___x_3154_);
return v___x_3155_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6(lean_object* v_a_3156_, lean_object* v_as_3157_, size_t v_sz_3158_, size_t v_i_3159_, lean_object* v_b_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_){
_start:
{
lean_object* v_a_3167_; uint8_t v___x_3171_; 
v___x_3171_ = lean_usize_dec_lt(v_i_3159_, v_sz_3158_);
if (v___x_3171_ == 0)
{
lean_object* v___x_3172_; 
lean_dec_ref(v_a_3156_);
v___x_3172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3172_, 0, v_b_3160_);
return v___x_3172_;
}
else
{
lean_object* v_a_3173_; lean_object* v___x_3174_; 
v_a_3173_ = lean_array_uget_borrowed(v_as_3157_, v_i_3159_);
lean_inc(v_a_3173_);
lean_inc_ref(v_a_3156_);
v___x_3174_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg(v_a_3156_, v_a_3173_, v___y_3162_);
if (lean_obj_tag(v___x_3174_) == 0)
{
lean_object* v_a_3175_; lean_object* v___x_3176_; uint8_t v___x_3177_; 
v_a_3175_ = lean_ctor_get(v___x_3174_, 0);
lean_inc(v_a_3175_);
lean_dec_ref(v___x_3174_);
v___x_3176_ = lean_box(0);
v___x_3177_ = lean_unbox(v_a_3175_);
lean_dec(v_a_3175_);
if (v___x_3177_ == 0)
{
v_a_3167_ = v___x_3176_;
goto v___jp_3166_;
}
else
{
uint8_t v___x_3178_; 
v___x_3178_ = l_Lean_Expr_isFVarOf(v_a_3156_, v_a_3173_);
if (v___x_3178_ == 0)
{
lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; 
v___x_3179_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__1);
lean_inc_ref(v_a_3156_);
v___x_3180_ = l_Lean_indentExpr(v_a_3156_);
v___x_3181_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3181_, 0, v___x_3179_);
lean_ctor_set(v___x_3181_, 1, v___x_3180_);
v___x_3182_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__3);
v___x_3183_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3183_, 0, v___x_3181_);
lean_ctor_set(v___x_3183_, 1, v___x_3182_);
lean_inc(v_a_3173_);
v___x_3184_ = l_Lean_mkFVar(v_a_3173_);
v___x_3185_ = l_Lean_indentExpr(v___x_3184_);
v___x_3186_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3186_, 0, v___x_3183_);
lean_ctor_set(v___x_3186_, 1, v___x_3185_);
v___x_3187_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__5);
v___x_3188_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3188_, 0, v___x_3186_);
lean_ctor_set(v___x_3188_, 1, v___x_3187_);
v___x_3189_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg(v___x_3188_, v___y_3161_, v___y_3162_, v___y_3163_, v___y_3164_);
if (lean_obj_tag(v___x_3189_) == 0)
{
lean_dec_ref(v___x_3189_);
v_a_3167_ = v___x_3176_;
goto v___jp_3166_;
}
else
{
lean_dec_ref(v_a_3156_);
return v___x_3189_;
}
}
else
{
lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; 
v___x_3190_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__1);
lean_inc_ref(v_a_3156_);
v___x_3191_ = l_Lean_indentExpr(v_a_3156_);
v___x_3192_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3192_, 0, v___x_3190_);
lean_ctor_set(v___x_3192_, 1, v___x_3191_);
v___x_3193_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__5);
v___x_3194_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3194_, 0, v___x_3192_);
lean_ctor_set(v___x_3194_, 1, v___x_3193_);
v___x_3195_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg(v___x_3194_, v___y_3161_, v___y_3162_, v___y_3163_, v___y_3164_);
if (lean_obj_tag(v___x_3195_) == 0)
{
lean_dec_ref(v___x_3195_);
v_a_3167_ = v___x_3176_;
goto v___jp_3166_;
}
else
{
lean_dec_ref(v_a_3156_);
return v___x_3195_;
}
}
}
}
else
{
lean_object* v_a_3196_; lean_object* v___x_3198_; uint8_t v_isShared_3199_; uint8_t v_isSharedCheck_3203_; 
lean_dec_ref(v_a_3156_);
v_a_3196_ = lean_ctor_get(v___x_3174_, 0);
v_isSharedCheck_3203_ = !lean_is_exclusive(v___x_3174_);
if (v_isSharedCheck_3203_ == 0)
{
v___x_3198_ = v___x_3174_;
v_isShared_3199_ = v_isSharedCheck_3203_;
goto v_resetjp_3197_;
}
else
{
lean_inc(v_a_3196_);
lean_dec(v___x_3174_);
v___x_3198_ = lean_box(0);
v_isShared_3199_ = v_isSharedCheck_3203_;
goto v_resetjp_3197_;
}
v_resetjp_3197_:
{
lean_object* v___x_3201_; 
if (v_isShared_3199_ == 0)
{
v___x_3201_ = v___x_3198_;
goto v_reusejp_3200_;
}
else
{
lean_object* v_reuseFailAlloc_3202_; 
v_reuseFailAlloc_3202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3202_, 0, v_a_3196_);
v___x_3201_ = v_reuseFailAlloc_3202_;
goto v_reusejp_3200_;
}
v_reusejp_3200_:
{
return v___x_3201_;
}
}
}
}
v___jp_3166_:
{
size_t v___x_3168_; size_t v___x_3169_; 
v___x_3168_ = ((size_t)1ULL);
v___x_3169_ = lean_usize_add(v_i_3159_, v___x_3168_);
v_i_3159_ = v___x_3169_;
v_b_3160_ = v_a_3167_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___boxed(lean_object* v_a_3204_, lean_object* v_as_3205_, lean_object* v_sz_3206_, lean_object* v_i_3207_, lean_object* v_b_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_){
_start:
{
size_t v_sz_boxed_3214_; size_t v_i_boxed_3215_; lean_object* v_res_3216_; 
v_sz_boxed_3214_ = lean_unbox_usize(v_sz_3206_);
lean_dec(v_sz_3206_);
v_i_boxed_3215_ = lean_unbox_usize(v_i_3207_);
lean_dec(v_i_3207_);
v_res_3216_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6(v_a_3204_, v_as_3205_, v_sz_boxed_3214_, v_i_boxed_3215_, v_b_3208_, v___y_3209_, v___y_3210_, v___y_3211_, v___y_3212_);
lean_dec(v___y_3212_);
lean_dec_ref(v___y_3211_);
lean_dec(v___y_3210_);
lean_dec_ref(v___y_3209_);
lean_dec_ref(v_as_3205_);
return v_res_3216_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7(lean_object* v_snd_3217_, lean_object* v_as_3218_, size_t v_sz_3219_, size_t v_i_3220_, lean_object* v_b_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_){
_start:
{
uint8_t v___x_3227_; 
v___x_3227_ = lean_usize_dec_lt(v_i_3220_, v_sz_3219_);
if (v___x_3227_ == 0)
{
lean_object* v___x_3228_; 
v___x_3228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3228_, 0, v_b_3221_);
return v___x_3228_;
}
else
{
lean_object* v___x_3229_; lean_object* v_a_3230_; size_t v_sz_3231_; size_t v___x_3232_; lean_object* v___x_3233_; 
v___x_3229_ = lean_box(0);
v_a_3230_ = lean_array_uget_borrowed(v_as_3218_, v_i_3220_);
v_sz_3231_ = lean_array_size(v_snd_3217_);
v___x_3232_ = ((size_t)0ULL);
lean_inc(v_a_3230_);
v___x_3233_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6(v_a_3230_, v_snd_3217_, v_sz_3231_, v___x_3232_, v___x_3229_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_);
if (lean_obj_tag(v___x_3233_) == 0)
{
size_t v___x_3234_; size_t v___x_3235_; 
lean_dec_ref(v___x_3233_);
v___x_3234_ = ((size_t)1ULL);
v___x_3235_ = lean_usize_add(v_i_3220_, v___x_3234_);
v_i_3220_ = v___x_3235_;
v_b_3221_ = v___x_3229_;
goto _start;
}
else
{
return v___x_3233_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7___boxed(lean_object* v_snd_3237_, lean_object* v_as_3238_, lean_object* v_sz_3239_, lean_object* v_i_3240_, lean_object* v_b_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_){
_start:
{
size_t v_sz_boxed_3247_; size_t v_i_boxed_3248_; lean_object* v_res_3249_; 
v_sz_boxed_3247_ = lean_unbox_usize(v_sz_3239_);
lean_dec(v_sz_3239_);
v_i_boxed_3248_ = lean_unbox_usize(v_i_3240_);
lean_dec(v_i_3240_);
v_res_3249_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7(v_snd_3237_, v_as_3238_, v_sz_boxed_3247_, v_i_boxed_3248_, v_b_3241_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_);
lean_dec(v___y_3245_);
lean_dec_ref(v___y_3244_);
lean_dec(v___y_3243_);
lean_dec_ref(v___y_3242_);
lean_dec_ref(v_as_3238_);
lean_dec_ref(v_snd_3237_);
return v_res_3249_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8(lean_object* v_snd_3250_, lean_object* v_as_3251_, size_t v_sz_3252_, size_t v_i_3253_, lean_object* v_b_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_){
_start:
{
uint8_t v___x_3260_; 
v___x_3260_ = lean_usize_dec_lt(v_i_3253_, v_sz_3252_);
if (v___x_3260_ == 0)
{
lean_object* v___x_3261_; 
v___x_3261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3261_, 0, v_b_3254_);
return v___x_3261_;
}
else
{
lean_object* v_a_3262_; lean_object* v_indGroupInst_3263_; lean_object* v_params_3264_; lean_object* v___x_3265_; size_t v_sz_3266_; size_t v___x_3267_; lean_object* v___x_3268_; 
v_a_3262_ = lean_array_uget_borrowed(v_as_3251_, v_i_3253_);
v_indGroupInst_3263_ = lean_ctor_get(v_a_3262_, 4);
v_params_3264_ = lean_ctor_get(v_indGroupInst_3263_, 2);
v___x_3265_ = lean_box(0);
v_sz_3266_ = lean_array_size(v_params_3264_);
v___x_3267_ = ((size_t)0ULL);
v___x_3268_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7(v_snd_3250_, v_params_3264_, v_sz_3266_, v___x_3267_, v___x_3265_, v___y_3255_, v___y_3256_, v___y_3257_, v___y_3258_);
if (lean_obj_tag(v___x_3268_) == 0)
{
size_t v___x_3269_; size_t v___x_3270_; 
lean_dec_ref(v___x_3268_);
v___x_3269_ = ((size_t)1ULL);
v___x_3270_ = lean_usize_add(v_i_3253_, v___x_3269_);
v_i_3253_ = v___x_3270_;
v_b_3254_ = v___x_3265_;
goto _start;
}
else
{
return v___x_3268_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8___boxed(lean_object* v_snd_3272_, lean_object* v_as_3273_, lean_object* v_sz_3274_, lean_object* v_i_3275_, lean_object* v_b_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_){
_start:
{
size_t v_sz_boxed_3282_; size_t v_i_boxed_3283_; lean_object* v_res_3284_; 
v_sz_boxed_3282_ = lean_unbox_usize(v_sz_3274_);
lean_dec(v_sz_3274_);
v_i_boxed_3283_ = lean_unbox_usize(v_i_3275_);
lean_dec(v_i_3275_);
v_res_3284_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8(v_snd_3272_, v_as_3273_, v_sz_boxed_3282_, v_i_boxed_3283_, v_b_3276_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_);
lean_dec(v___y_3280_);
lean_dec_ref(v___y_3279_);
lean_dec(v___y_3278_);
lean_dec_ref(v___y_3277_);
lean_dec_ref(v_as_3273_);
lean_dec_ref(v_snd_3272_);
return v_res_3284_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__0(void){
_start:
{
lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; 
v___x_3285_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__3));
v___x_3286_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0___closed__1));
v___x_3287_ = l_Lean_Name_append(v___x_3286_, v___x_3285_);
return v___x_3287_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3289_; lean_object* v___x_3290_; 
v___x_3289_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__1));
v___x_3290_ = l_Lean_stringToMessageData(v___x_3289_);
return v___x_3290_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__4(void){
_start:
{
lean_object* v___x_3292_; lean_object* v___x_3293_; 
v___x_3292_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__3));
v___x_3293_ = l_Lean_stringToMessageData(v___x_3292_);
return v___x_3293_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__6(void){
_start:
{
lean_object* v___x_3295_; lean_object* v___x_3296_; 
v___x_3295_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__5));
v___x_3296_ = l_Lean_stringToMessageData(v___x_3295_);
return v___x_3296_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__8(void){
_start:
{
lean_object* v___x_3298_; lean_object* v___x_3299_; 
v___x_3298_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__7));
v___x_3299_ = l_Lean_stringToMessageData(v___x_3298_);
return v___x_3299_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__10(void){
_start:
{
lean_object* v___x_3301_; lean_object* v___x_3302_; 
v___x_3301_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__9));
v___x_3302_ = l_Lean_stringToMessageData(v___x_3301_);
return v___x_3302_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0(size_t v___x_3303_, lean_object* v_a_3304_, lean_object* v_xs_3305_, lean_object* v___x_3306_, lean_object* v_a_3307_, lean_object* v_recArgInfos_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_){
_start:
{
lean_object* v___y_3315_; lean_object* v___y_3316_; lean_object* v___y_3317_; lean_object* v___y_3318_; lean_object* v___y_3319_; lean_object* v___y_3320_; lean_object* v___y_3321_; lean_object* v___x_3334_; lean_object* v___y_3336_; lean_object* v___y_3337_; lean_object* v___y_3338_; lean_object* v___y_3339_; lean_object* v___y_3340_; lean_object* v___y_3341_; lean_object* v___y_3342_; lean_object* v___x_3361_; lean_object* v_a_3362_; size_t v_sz_3363_; lean_object* v___x_3364_; lean_object* v___y_3366_; lean_object* v___y_3367_; lean_object* v___y_3368_; lean_object* v___y_3369_; uint8_t v___x_3428_; 
v___x_3334_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__3));
v___x_3361_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0(v___x_3334_, v___y_3309_, v___y_3310_, v___y_3311_, v___y_3312_);
v_a_3362_ = lean_ctor_get(v___x_3361_, 0);
lean_inc(v_a_3362_);
lean_dec_ref(v___x_3361_);
v_sz_3363_ = lean_array_size(v_recArgInfos_3308_);
lean_inc_ref(v_recArgInfos_3308_);
v___x_3364_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__2(v_sz_3363_, v___x_3303_, v_recArgInfos_3308_);
v___x_3428_ = lean_unbox(v_a_3362_);
lean_dec(v_a_3362_);
if (v___x_3428_ == 0)
{
v___y_3366_ = v___y_3309_;
v___y_3367_ = v___y_3310_;
v___y_3368_ = v___y_3311_;
v___y_3369_ = v___y_3312_;
goto v___jp_3365_;
}
else
{
lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; 
v___x_3429_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__10, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__10);
lean_inc_ref(v___x_3364_);
v___x_3430_ = lean_array_to_list(v___x_3364_);
v___x_3431_ = lean_box(0);
v___x_3432_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__0(v___x_3430_, v___x_3431_);
v___x_3433_ = l_Lean_MessageData_ofList(v___x_3432_);
v___x_3434_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3434_, 0, v___x_3429_);
lean_ctor_set(v___x_3434_, 1, v___x_3433_);
v___x_3435_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_3334_, v___x_3434_, v___y_3309_, v___y_3310_, v___y_3311_, v___y_3312_);
if (lean_obj_tag(v___x_3435_) == 0)
{
lean_dec_ref(v___x_3435_);
v___y_3366_ = v___y_3309_;
v___y_3367_ = v___y_3310_;
v___y_3368_ = v___y_3311_;
v___y_3369_ = v___y_3312_;
goto v___jp_3365_;
}
else
{
lean_object* v_a_3436_; lean_object* v___x_3438_; uint8_t v_isShared_3439_; uint8_t v_isSharedCheck_3443_; 
lean_dec_ref(v___x_3364_);
lean_dec_ref(v_recArgInfos_3308_);
lean_dec_ref(v_a_3307_);
lean_dec(v___x_3306_);
lean_dec_ref(v_xs_3305_);
lean_dec_ref(v_a_3304_);
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
v___jp_3314_:
{
lean_object* v___x_3322_; size_t v_sz_3323_; lean_object* v___x_3324_; 
v___x_3322_ = lean_box(0);
v_sz_3323_ = lean_array_size(v___y_3317_);
v___x_3324_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8(v___y_3316_, v___y_3317_, v_sz_3323_, v___x_3303_, v___x_3322_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_);
lean_dec_ref(v___y_3317_);
if (lean_obj_tag(v___x_3324_) == 0)
{
lean_object* v___x_3325_; 
lean_dec_ref(v___x_3324_);
v___x_3325_ = l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___redArg(v___y_3316_, v___y_3315_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_);
lean_dec_ref(v___y_3316_);
return v___x_3325_;
}
else
{
lean_object* v_a_3326_; lean_object* v___x_3328_; uint8_t v_isShared_3329_; uint8_t v_isSharedCheck_3333_; 
lean_dec_ref(v___y_3316_);
lean_dec_ref(v___y_3315_);
v_a_3326_ = lean_ctor_get(v___x_3324_, 0);
v_isSharedCheck_3333_ = !lean_is_exclusive(v___x_3324_);
if (v_isSharedCheck_3333_ == 0)
{
v___x_3328_ = v___x_3324_;
v_isShared_3329_ = v_isSharedCheck_3333_;
goto v_resetjp_3327_;
}
else
{
lean_inc(v_a_3326_);
lean_dec(v___x_3324_);
v___x_3328_ = lean_box(0);
v_isShared_3329_ = v_isSharedCheck_3333_;
goto v_resetjp_3327_;
}
v_resetjp_3327_:
{
lean_object* v___x_3331_; 
if (v_isShared_3329_ == 0)
{
v___x_3331_ = v___x_3328_;
goto v_reusejp_3330_;
}
else
{
lean_object* v_reuseFailAlloc_3332_; 
v_reuseFailAlloc_3332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3332_, 0, v_a_3326_);
v___x_3331_ = v_reuseFailAlloc_3332_;
goto v_reusejp_3330_;
}
v_reusejp_3330_:
{
return v___x_3331_;
}
}
}
}
v___jp_3335_:
{
lean_object* v_options_3343_; uint8_t v_hasTrace_3344_; 
v_options_3343_ = lean_ctor_get(v___y_3341_, 2);
v_hasTrace_3344_ = lean_ctor_get_uint8(v_options_3343_, sizeof(void*)*1);
if (v_hasTrace_3344_ == 0)
{
v___y_3315_ = v___y_3336_;
v___y_3316_ = v___y_3337_;
v___y_3317_ = v___y_3338_;
v___y_3318_ = v___y_3339_;
v___y_3319_ = v___y_3340_;
v___y_3320_ = v___y_3341_;
v___y_3321_ = v___y_3342_;
goto v___jp_3314_;
}
else
{
lean_object* v_inheritedTraceOptions_3345_; lean_object* v___x_3346_; uint8_t v___x_3347_; 
v_inheritedTraceOptions_3345_ = lean_ctor_get(v___y_3341_, 13);
v___x_3346_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__0);
v___x_3347_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3345_, v_options_3343_, v___x_3346_);
if (v___x_3347_ == 0)
{
v___y_3315_ = v___y_3336_;
v___y_3316_ = v___y_3337_;
v___y_3317_ = v___y_3338_;
v___y_3318_ = v___y_3339_;
v___y_3319_ = v___y_3340_;
v___y_3320_ = v___y_3341_;
v___y_3321_ = v___y_3342_;
goto v___jp_3314_;
}
else
{
lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; 
v___x_3348_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__2);
lean_inc_ref(v___y_3338_);
v___x_3349_ = l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10(v___y_3338_);
v___x_3350_ = l_Lean_MessageData_ofFormat(v___x_3349_);
v___x_3351_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3351_, 0, v___x_3348_);
lean_ctor_set(v___x_3351_, 1, v___x_3350_);
v___x_3352_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_3334_, v___x_3351_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_);
if (lean_obj_tag(v___x_3352_) == 0)
{
lean_dec_ref(v___x_3352_);
v___y_3315_ = v___y_3336_;
v___y_3316_ = v___y_3337_;
v___y_3317_ = v___y_3338_;
v___y_3318_ = v___y_3339_;
v___y_3319_ = v___y_3340_;
v___y_3320_ = v___y_3341_;
v___y_3321_ = v___y_3342_;
goto v___jp_3314_;
}
else
{
lean_object* v_a_3353_; lean_object* v___x_3355_; uint8_t v_isShared_3356_; uint8_t v_isSharedCheck_3360_; 
lean_dec_ref(v___y_3338_);
lean_dec_ref(v___y_3337_);
lean_dec_ref(v___y_3336_);
v_a_3353_ = lean_ctor_get(v___x_3352_, 0);
v_isSharedCheck_3360_ = !lean_is_exclusive(v___x_3352_);
if (v_isSharedCheck_3360_ == 0)
{
v___x_3355_ = v___x_3352_;
v_isShared_3356_ = v_isSharedCheck_3360_;
goto v_resetjp_3354_;
}
else
{
lean_inc(v_a_3353_);
lean_dec(v___x_3352_);
v___x_3355_ = lean_box(0);
v_isShared_3356_ = v_isSharedCheck_3360_;
goto v_resetjp_3354_;
}
v_resetjp_3354_:
{
lean_object* v___x_3358_; 
if (v_isShared_3356_ == 0)
{
v___x_3358_ = v___x_3355_;
goto v_reusejp_3357_;
}
else
{
lean_object* v_reuseFailAlloc_3359_; 
v_reuseFailAlloc_3359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3359_, 0, v_a_3353_);
v___x_3358_ = v_reuseFailAlloc_3359_;
goto v_reusejp_3357_;
}
v_reusejp_3357_:
{
return v___x_3358_;
}
}
}
}
}
}
v___jp_3365_:
{
lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v_snd_3372_; lean_object* v_fst_3373_; lean_object* v___x_3375_; uint8_t v_isShared_3376_; uint8_t v_isSharedCheck_3427_; 
lean_inc_ref(v_recArgInfos_3308_);
v___x_3370_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__3(v_sz_3363_, v___x_3303_, v_recArgInfos_3308_);
lean_inc_ref(v_xs_3305_);
v___x_3371_ = l_Lean_Elab_FixedParamPerms_erase(v_a_3304_, v_xs_3305_, v___x_3370_);
v_snd_3372_ = lean_ctor_get(v___x_3371_, 1);
v_fst_3373_ = lean_ctor_get(v___x_3371_, 0);
v_isSharedCheck_3427_ = !lean_is_exclusive(v___x_3371_);
if (v_isSharedCheck_3427_ == 0)
{
v___x_3375_ = v___x_3371_;
v_isShared_3376_ = v_isSharedCheck_3427_;
goto v_resetjp_3374_;
}
else
{
lean_inc(v_snd_3372_);
lean_inc(v_fst_3373_);
lean_dec(v___x_3371_);
v___x_3375_ = lean_box(0);
v_isShared_3376_ = v_isSharedCheck_3427_;
goto v_resetjp_3374_;
}
v_resetjp_3374_:
{
lean_object* v_fst_3377_; lean_object* v_snd_3378_; lean_object* v___x_3380_; uint8_t v_isShared_3381_; uint8_t v_isSharedCheck_3426_; 
v_fst_3377_ = lean_ctor_get(v_snd_3372_, 0);
v_snd_3378_ = lean_ctor_get(v_snd_3372_, 1);
v_isSharedCheck_3426_ = !lean_is_exclusive(v_snd_3372_);
if (v_isSharedCheck_3426_ == 0)
{
v___x_3380_ = v_snd_3372_;
v_isShared_3381_ = v_isSharedCheck_3426_;
goto v_resetjp_3379_;
}
else
{
lean_inc(v_snd_3378_);
lean_inc(v_fst_3377_);
lean_dec(v_snd_3372_);
v___x_3380_ = lean_box(0);
v_isShared_3381_ = v_isSharedCheck_3426_;
goto v_resetjp_3379_;
}
v_resetjp_3379_:
{
lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___f_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; uint8_t v___x_3388_; 
v___x_3382_ = lean_array_get_size(v_recArgInfos_3308_);
v___x_3383_ = lean_mk_empty_array_with_capacity(v___x_3382_);
v___x_3384_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg(v_fst_3373_, v_recArgInfos_3308_, v___x_3382_, v___x_3306_, v___x_3383_);
lean_dec_ref(v_recArgInfos_3308_);
lean_inc_ref(v___x_3384_);
lean_inc(v_fst_3377_);
v___f_3385_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___boxed), 10, 5);
lean_closure_set(v___f_3385_, 0, v_a_3307_);
lean_closure_set(v___f_3385_, 1, v_fst_3373_);
lean_closure_set(v___f_3385_, 2, v_fst_3377_);
lean_closure_set(v___f_3385_, 3, v___x_3384_);
lean_closure_set(v___f_3385_, 4, v___x_3364_);
v___x_3386_ = lean_array_get_size(v_fst_3377_);
v___x_3387_ = lean_array_get_size(v_xs_3305_);
v___x_3388_ = lean_nat_dec_eq(v___x_3386_, v___x_3387_);
if (v___x_3388_ == 0)
{
lean_object* v___x_3389_; lean_object* v_a_3390_; uint8_t v___x_3391_; 
v___x_3389_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0(v___x_3334_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_);
v_a_3390_ = lean_ctor_get(v___x_3389_, 0);
lean_inc(v_a_3390_);
lean_dec_ref(v___x_3389_);
v___x_3391_ = lean_unbox(v_a_3390_);
lean_dec(v_a_3390_);
if (v___x_3391_ == 0)
{
lean_del_object(v___x_3380_);
lean_dec(v_fst_3377_);
lean_del_object(v___x_3375_);
lean_dec_ref(v_xs_3305_);
v___y_3336_ = v___f_3385_;
v___y_3337_ = v_snd_3378_;
v___y_3338_ = v___x_3384_;
v___y_3339_ = v___y_3366_;
v___y_3340_ = v___y_3367_;
v___y_3341_ = v___y_3368_;
v___y_3342_ = v___y_3369_;
goto v___jp_3335_;
}
else
{
lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3398_; 
v___x_3392_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__4);
v___x_3393_ = lean_array_to_list(v_xs_3305_);
v___x_3394_ = lean_box(0);
v___x_3395_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_3393_, v___x_3394_);
v___x_3396_ = l_Lean_MessageData_ofList(v___x_3395_);
if (v_isShared_3381_ == 0)
{
lean_ctor_set_tag(v___x_3380_, 7);
lean_ctor_set(v___x_3380_, 1, v___x_3396_);
lean_ctor_set(v___x_3380_, 0, v___x_3392_);
v___x_3398_ = v___x_3380_;
goto v_reusejp_3397_;
}
else
{
lean_object* v_reuseFailAlloc_3424_; 
v_reuseFailAlloc_3424_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3424_, 0, v___x_3392_);
lean_ctor_set(v_reuseFailAlloc_3424_, 1, v___x_3396_);
v___x_3398_ = v_reuseFailAlloc_3424_;
goto v_reusejp_3397_;
}
v_reusejp_3397_:
{
lean_object* v___x_3399_; lean_object* v___x_3401_; 
v___x_3399_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__6, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__6);
if (v_isShared_3376_ == 0)
{
lean_ctor_set_tag(v___x_3375_, 7);
lean_ctor_set(v___x_3375_, 1, v___x_3399_);
lean_ctor_set(v___x_3375_, 0, v___x_3398_);
v___x_3401_ = v___x_3375_;
goto v_reusejp_3400_;
}
else
{
lean_object* v_reuseFailAlloc_3423_; 
v_reuseFailAlloc_3423_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3423_, 0, v___x_3398_);
lean_ctor_set(v_reuseFailAlloc_3423_, 1, v___x_3399_);
v___x_3401_ = v_reuseFailAlloc_3423_;
goto v_reusejp_3400_;
}
v_reusejp_3400_:
{
lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; size_t v_sz_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; 
v___x_3402_ = lean_array_to_list(v_fst_3377_);
v___x_3403_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_3402_, v___x_3394_);
v___x_3404_ = l_Lean_MessageData_ofList(v___x_3403_);
v___x_3405_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3405_, 0, v___x_3401_);
lean_ctor_set(v___x_3405_, 1, v___x_3404_);
v___x_3406_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__8);
v___x_3407_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3407_, 0, v___x_3405_);
lean_ctor_set(v___x_3407_, 1, v___x_3406_);
v_sz_3408_ = lean_array_size(v_snd_3378_);
lean_inc(v_snd_3378_);
v___x_3409_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__11(v_sz_3408_, v___x_3303_, v_snd_3378_);
v___x_3410_ = lean_array_to_list(v___x_3409_);
v___x_3411_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_3410_, v___x_3394_);
v___x_3412_ = l_Lean_MessageData_ofList(v___x_3411_);
v___x_3413_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3413_, 0, v___x_3407_);
lean_ctor_set(v___x_3413_, 1, v___x_3412_);
v___x_3414_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_3334_, v___x_3413_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_);
if (lean_obj_tag(v___x_3414_) == 0)
{
lean_dec_ref(v___x_3414_);
v___y_3336_ = v___f_3385_;
v___y_3337_ = v_snd_3378_;
v___y_3338_ = v___x_3384_;
v___y_3339_ = v___y_3366_;
v___y_3340_ = v___y_3367_;
v___y_3341_ = v___y_3368_;
v___y_3342_ = v___y_3369_;
goto v___jp_3335_;
}
else
{
lean_object* v_a_3415_; lean_object* v___x_3417_; uint8_t v_isShared_3418_; uint8_t v_isSharedCheck_3422_; 
lean_dec_ref(v___f_3385_);
lean_dec_ref(v___x_3384_);
lean_dec(v_snd_3378_);
v_a_3415_ = lean_ctor_get(v___x_3414_, 0);
v_isSharedCheck_3422_ = !lean_is_exclusive(v___x_3414_);
if (v_isSharedCheck_3422_ == 0)
{
v___x_3417_ = v___x_3414_;
v_isShared_3418_ = v_isSharedCheck_3422_;
goto v_resetjp_3416_;
}
else
{
lean_inc(v_a_3415_);
lean_dec(v___x_3414_);
v___x_3417_ = lean_box(0);
v_isShared_3418_ = v_isSharedCheck_3422_;
goto v_resetjp_3416_;
}
v_resetjp_3416_:
{
lean_object* v___x_3420_; 
if (v_isShared_3418_ == 0)
{
v___x_3420_ = v___x_3417_;
goto v_reusejp_3419_;
}
else
{
lean_object* v_reuseFailAlloc_3421_; 
v_reuseFailAlloc_3421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3421_, 0, v_a_3415_);
v___x_3420_ = v_reuseFailAlloc_3421_;
goto v_reusejp_3419_;
}
v_reusejp_3419_:
{
return v___x_3420_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3425_; 
lean_dec_ref(v___x_3384_);
lean_del_object(v___x_3380_);
lean_dec(v_fst_3377_);
lean_del_object(v___x_3375_);
lean_dec_ref(v_xs_3305_);
v___x_3425_ = l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___redArg(v_snd_3378_, v___f_3385_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_);
lean_dec(v_snd_3378_);
return v___x_3425_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___boxed(lean_object* v___x_3444_, lean_object* v_a_3445_, lean_object* v_xs_3446_, lean_object* v___x_3447_, lean_object* v_a_3448_, lean_object* v_recArgInfos_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_){
_start:
{
size_t v___x_15816__boxed_3455_; lean_object* v_res_3456_; 
v___x_15816__boxed_3455_ = lean_unbox_usize(v___x_3444_);
lean_dec(v___x_3444_);
v_res_3456_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0(v___x_15816__boxed_3455_, v_a_3445_, v_xs_3446_, v___x_3447_, v_a_3448_, v_recArgInfos_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_);
lean_dec(v___y_3453_);
lean_dec_ref(v___y_3452_);
lean_dec(v___y_3451_);
lean_dec_ref(v___y_3450_);
return v_res_3456_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg(lean_object* v___x_3457_, lean_object* v_xs_3458_, lean_object* v_as_3459_, lean_object* v_i_3460_, lean_object* v_j_3461_, lean_object* v_bs_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_){
_start:
{
lean_object* v_zero_3468_; uint8_t v_isZero_3469_; 
v_zero_3468_ = lean_unsigned_to_nat(0u);
v_isZero_3469_ = lean_nat_dec_eq(v_i_3460_, v_zero_3468_);
if (v_isZero_3469_ == 1)
{
lean_object* v___x_3470_; 
lean_dec(v_j_3461_);
lean_dec(v_i_3460_);
lean_dec_ref(v_xs_3458_);
v___x_3470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3470_, 0, v_bs_3462_);
return v___x_3470_;
}
else
{
lean_object* v___x_3471_; lean_object* v_value_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; 
v___x_3471_ = lean_array_fget_borrowed(v_as_3459_, v_j_3461_);
v_value_3472_ = lean_ctor_get(v___x_3471_, 7);
v___x_3473_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0, &l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0_once, _init_l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0);
v___x_3474_ = lean_array_get_borrowed(v___x_3473_, v___x_3457_, v_j_3461_);
lean_inc_ref(v_xs_3458_);
lean_inc_ref(v_value_3472_);
lean_inc(v___x_3474_);
v___x_3475_ = l_Lean_Elab_FixedParamPerm_instantiateLambda(v___x_3474_, v_value_3472_, v_xs_3458_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_);
if (lean_obj_tag(v___x_3475_) == 0)
{
lean_object* v_a_3476_; lean_object* v_one_3477_; lean_object* v_n_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; 
v_a_3476_ = lean_ctor_get(v___x_3475_, 0);
lean_inc(v_a_3476_);
lean_dec_ref(v___x_3475_);
v_one_3477_ = lean_unsigned_to_nat(1u);
v_n_3478_ = lean_nat_sub(v_i_3460_, v_one_3477_);
lean_dec(v_i_3460_);
v___x_3479_ = lean_nat_add(v_j_3461_, v_one_3477_);
lean_dec(v_j_3461_);
v___x_3480_ = lean_array_push(v_bs_3462_, v_a_3476_);
v_i_3460_ = v_n_3478_;
v_j_3461_ = v___x_3479_;
v_bs_3462_ = v___x_3480_;
goto _start;
}
else
{
lean_object* v_a_3482_; lean_object* v___x_3484_; uint8_t v_isShared_3485_; uint8_t v_isSharedCheck_3489_; 
lean_dec_ref(v_bs_3462_);
lean_dec(v_j_3461_);
lean_dec(v_i_3460_);
lean_dec_ref(v_xs_3458_);
v_a_3482_ = lean_ctor_get(v___x_3475_, 0);
v_isSharedCheck_3489_ = !lean_is_exclusive(v___x_3475_);
if (v_isSharedCheck_3489_ == 0)
{
v___x_3484_ = v___x_3475_;
v_isShared_3485_ = v_isSharedCheck_3489_;
goto v_resetjp_3483_;
}
else
{
lean_inc(v_a_3482_);
lean_dec(v___x_3475_);
v___x_3484_ = lean_box(0);
v_isShared_3485_ = v_isSharedCheck_3489_;
goto v_resetjp_3483_;
}
v_resetjp_3483_:
{
lean_object* v___x_3487_; 
if (v_isShared_3485_ == 0)
{
v___x_3487_ = v___x_3484_;
goto v_reusejp_3486_;
}
else
{
lean_object* v_reuseFailAlloc_3488_; 
v_reuseFailAlloc_3488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3488_, 0, v_a_3482_);
v___x_3487_ = v_reuseFailAlloc_3488_;
goto v_reusejp_3486_;
}
v_reusejp_3486_:
{
return v___x_3487_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg___boxed(lean_object* v___x_3490_, lean_object* v_xs_3491_, lean_object* v_as_3492_, lean_object* v_i_3493_, lean_object* v_j_3494_, lean_object* v_bs_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_){
_start:
{
lean_object* v_res_3501_; 
v_res_3501_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg(v___x_3490_, v_xs_3491_, v_as_3492_, v_i_3493_, v_j_3494_, v_bs_3495_, v___y_3496_, v___y_3497_, v___y_3498_, v___y_3499_);
lean_dec(v___y_3499_);
lean_dec_ref(v___y_3498_);
lean_dec(v___y_3497_);
lean_dec_ref(v___y_3496_);
lean_dec_ref(v_as_3492_);
lean_dec_ref(v___x_3490_);
return v_res_3501_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__2(lean_object* v_a_3502_, lean_object* v_perms_3503_, lean_object* v___x_3504_, lean_object* v_fnNames_3505_, lean_object* v_a_3506_, lean_object* v_termMeasure_x3fs_3507_, size_t v___x_3508_, lean_object* v_xs_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_){
_start:
{
lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; 
v___x_3515_ = lean_array_get_size(v_a_3502_);
v___x_3516_ = lean_mk_empty_array_with_capacity(v___x_3515_);
lean_inc(v___x_3504_);
lean_inc_ref(v_xs_3509_);
v___x_3517_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg(v_perms_3503_, v_xs_3509_, v_a_3502_, v___x_3515_, v___x_3504_, v___x_3516_, v___y_3510_, v___y_3511_, v___y_3512_, v___y_3513_);
if (lean_obj_tag(v___x_3517_) == 0)
{
lean_object* v_a_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; 
v_a_3518_ = lean_ctor_get(v___x_3517_, 0);
lean_inc_n(v_a_3518_, 2);
lean_dec_ref(v___x_3517_);
lean_inc_ref(v_xs_3509_);
lean_inc_ref(v_a_3506_);
lean_inc_ref(v_fnNames_3505_);
v___x_3519_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_findRecArgCandidates___boxed), 10, 5);
lean_closure_set(v___x_3519_, 0, v_fnNames_3505_);
lean_closure_set(v___x_3519_, 1, v_a_3506_);
lean_closure_set(v___x_3519_, 2, v_xs_3509_);
lean_closure_set(v___x_3519_, 3, v_a_3518_);
lean_closure_set(v___x_3519_, 4, v_termMeasure_x3fs_3507_);
lean_inc_ref(v_a_3502_);
v___x_3520_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v_a_3502_, v___x_3519_, v___y_3510_, v___y_3511_, v___y_3512_, v___y_3513_);
if (lean_obj_tag(v___x_3520_) == 0)
{
lean_object* v_a_3521_; lean_object* v___x_3522_; lean_object* v___f_3523_; lean_object* v___x_3524_; 
v_a_3521_ = lean_ctor_get(v___x_3520_, 0);
lean_inc(v_a_3521_);
lean_dec_ref(v___x_3520_);
v___x_3522_ = lean_box_usize(v___x_3508_);
lean_inc_ref(v_xs_3509_);
v___f_3523_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___boxed), 11, 5);
lean_closure_set(v___f_3523_, 0, v___x_3522_);
lean_closure_set(v___f_3523_, 1, v_a_3506_);
lean_closure_set(v___f_3523_, 2, v_xs_3509_);
lean_closure_set(v___f_3523_, 3, v___x_3504_);
lean_closure_set(v___f_3523_, 4, v_a_3502_);
v___x_3524_ = l_Lean_Elab_Structural_tryCandidates___redArg(v_fnNames_3505_, v_xs_3509_, v_a_3518_, v_a_3521_, v___f_3523_, v___y_3510_, v___y_3511_, v___y_3512_, v___y_3513_);
lean_dec_ref(v_fnNames_3505_);
return v___x_3524_;
}
else
{
lean_object* v_a_3525_; lean_object* v___x_3527_; uint8_t v_isShared_3528_; uint8_t v_isSharedCheck_3532_; 
lean_dec(v_a_3518_);
lean_dec_ref(v_xs_3509_);
lean_dec_ref(v_a_3506_);
lean_dec_ref(v_fnNames_3505_);
lean_dec(v___x_3504_);
lean_dec_ref(v_a_3502_);
v_a_3525_ = lean_ctor_get(v___x_3520_, 0);
v_isSharedCheck_3532_ = !lean_is_exclusive(v___x_3520_);
if (v_isSharedCheck_3532_ == 0)
{
v___x_3527_ = v___x_3520_;
v_isShared_3528_ = v_isSharedCheck_3532_;
goto v_resetjp_3526_;
}
else
{
lean_inc(v_a_3525_);
lean_dec(v___x_3520_);
v___x_3527_ = lean_box(0);
v_isShared_3528_ = v_isSharedCheck_3532_;
goto v_resetjp_3526_;
}
v_resetjp_3526_:
{
lean_object* v___x_3530_; 
if (v_isShared_3528_ == 0)
{
v___x_3530_ = v___x_3527_;
goto v_reusejp_3529_;
}
else
{
lean_object* v_reuseFailAlloc_3531_; 
v_reuseFailAlloc_3531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3531_, 0, v_a_3525_);
v___x_3530_ = v_reuseFailAlloc_3531_;
goto v_reusejp_3529_;
}
v_reusejp_3529_:
{
return v___x_3530_;
}
}
}
}
else
{
lean_object* v_a_3533_; lean_object* v___x_3535_; uint8_t v_isShared_3536_; uint8_t v_isSharedCheck_3540_; 
lean_dec_ref(v_xs_3509_);
lean_dec_ref(v_termMeasure_x3fs_3507_);
lean_dec_ref(v_a_3506_);
lean_dec_ref(v_fnNames_3505_);
lean_dec(v___x_3504_);
lean_dec_ref(v_a_3502_);
v_a_3533_ = lean_ctor_get(v___x_3517_, 0);
v_isSharedCheck_3540_ = !lean_is_exclusive(v___x_3517_);
if (v_isSharedCheck_3540_ == 0)
{
v___x_3535_ = v___x_3517_;
v_isShared_3536_ = v_isSharedCheck_3540_;
goto v_resetjp_3534_;
}
else
{
lean_inc(v_a_3533_);
lean_dec(v___x_3517_);
v___x_3535_ = lean_box(0);
v_isShared_3536_ = v_isSharedCheck_3540_;
goto v_resetjp_3534_;
}
v_resetjp_3534_:
{
lean_object* v___x_3538_; 
if (v_isShared_3536_ == 0)
{
v___x_3538_ = v___x_3535_;
goto v_reusejp_3537_;
}
else
{
lean_object* v_reuseFailAlloc_3539_; 
v_reuseFailAlloc_3539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3539_, 0, v_a_3533_);
v___x_3538_ = v_reuseFailAlloc_3539_;
goto v_reusejp_3537_;
}
v_reusejp_3537_:
{
return v___x_3538_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__2___boxed(lean_object* v_a_3541_, lean_object* v_perms_3542_, lean_object* v___x_3543_, lean_object* v_fnNames_3544_, lean_object* v_a_3545_, lean_object* v_termMeasure_x3fs_3546_, lean_object* v___x_3547_, lean_object* v_xs_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_){
_start:
{
size_t v___x_16173__boxed_3554_; lean_object* v_res_3555_; 
v___x_16173__boxed_3554_ = lean_unbox_usize(v___x_3547_);
lean_dec(v___x_3547_);
v_res_3555_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__2(v_a_3541_, v_perms_3542_, v___x_3543_, v_fnNames_3544_, v_a_3545_, v_termMeasure_x3fs_3546_, v___x_16173__boxed_3554_, v_xs_3548_, v___y_3549_, v___y_3550_, v___y_3551_, v___y_3552_);
lean_dec(v___y_3552_);
lean_dec_ref(v___y_3551_);
lean_dec(v___y_3550_);
lean_dec_ref(v___y_3549_);
lean_dec_ref(v_perms_3542_);
return v_res_3555_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0(size_t v_sz_3556_, size_t v_i_3557_, lean_object* v_bs_3558_){
_start:
{
uint8_t v___x_3559_; 
v___x_3559_ = lean_usize_dec_lt(v_i_3557_, v_sz_3556_);
if (v___x_3559_ == 0)
{
return v_bs_3558_;
}
else
{
lean_object* v_v_3560_; lean_object* v_declName_3561_; lean_object* v___x_3562_; lean_object* v_bs_x27_3563_; size_t v___x_3564_; size_t v___x_3565_; lean_object* v___x_3566_; 
v_v_3560_ = lean_array_uget_borrowed(v_bs_3558_, v_i_3557_);
v_declName_3561_ = lean_ctor_get(v_v_3560_, 3);
lean_inc(v_declName_3561_);
v___x_3562_ = lean_unsigned_to_nat(0u);
v_bs_x27_3563_ = lean_array_uset(v_bs_3558_, v_i_3557_, v___x_3562_);
v___x_3564_ = ((size_t)1ULL);
v___x_3565_ = lean_usize_add(v_i_3557_, v___x_3564_);
v___x_3566_ = lean_array_uset(v_bs_x27_3563_, v_i_3557_, v_declName_3561_);
v_i_3557_ = v___x_3565_;
v_bs_3558_ = v___x_3566_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0___boxed(lean_object* v_sz_3568_, lean_object* v_i_3569_, lean_object* v_bs_3570_){
_start:
{
size_t v_sz_boxed_3571_; size_t v_i_boxed_3572_; lean_object* v_res_3573_; 
v_sz_boxed_3571_ = lean_unbox_usize(v_sz_3568_);
lean_dec(v_sz_3568_);
v_i_boxed_3572_ = lean_unbox_usize(v_i_3569_);
lean_dec(v_i_3569_);
v_res_3573_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0(v_sz_boxed_3571_, v_i_boxed_3572_, v_bs_3570_);
return v_res_3573_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1___redArg(lean_object* v_fnNames_3574_, lean_object* v_numSectionVars_3575_, size_t v_sz_3576_, size_t v_i_3577_, lean_object* v_bs_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_){
_start:
{
uint8_t v___x_3582_; 
v___x_3582_ = lean_usize_dec_lt(v_i_3577_, v_sz_3576_);
if (v___x_3582_ == 0)
{
lean_object* v___x_3583_; 
lean_dec(v_numSectionVars_3575_);
lean_dec_ref(v_fnNames_3574_);
v___x_3583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3583_, 0, v_bs_3578_);
return v___x_3583_;
}
else
{
lean_object* v_v_3584_; lean_object* v_ref_3585_; uint8_t v_kind_3586_; lean_object* v_levelParams_3587_; lean_object* v_modifiers_3588_; lean_object* v_declName_3589_; lean_object* v_binders_3590_; lean_object* v_numSectionVars_3591_; lean_object* v_type_3592_; lean_object* v_value_3593_; lean_object* v_termination_3594_; lean_object* v___x_3596_; uint8_t v_isShared_3597_; uint8_t v_isSharedCheck_3617_; 
v_v_3584_ = lean_array_uget(v_bs_3578_, v_i_3577_);
v_ref_3585_ = lean_ctor_get(v_v_3584_, 0);
v_kind_3586_ = lean_ctor_get_uint8(v_v_3584_, sizeof(void*)*9);
v_levelParams_3587_ = lean_ctor_get(v_v_3584_, 1);
v_modifiers_3588_ = lean_ctor_get(v_v_3584_, 2);
v_declName_3589_ = lean_ctor_get(v_v_3584_, 3);
v_binders_3590_ = lean_ctor_get(v_v_3584_, 4);
v_numSectionVars_3591_ = lean_ctor_get(v_v_3584_, 5);
v_type_3592_ = lean_ctor_get(v_v_3584_, 6);
v_value_3593_ = lean_ctor_get(v_v_3584_, 7);
v_termination_3594_ = lean_ctor_get(v_v_3584_, 8);
v_isSharedCheck_3617_ = !lean_is_exclusive(v_v_3584_);
if (v_isSharedCheck_3617_ == 0)
{
v___x_3596_ = v_v_3584_;
v_isShared_3597_ = v_isSharedCheck_3617_;
goto v_resetjp_3595_;
}
else
{
lean_inc(v_termination_3594_);
lean_inc(v_value_3593_);
lean_inc(v_type_3592_);
lean_inc(v_numSectionVars_3591_);
lean_inc(v_binders_3590_);
lean_inc(v_declName_3589_);
lean_inc(v_modifiers_3588_);
lean_inc(v_levelParams_3587_);
lean_inc(v_ref_3585_);
lean_dec(v_v_3584_);
v___x_3596_ = lean_box(0);
v_isShared_3597_ = v_isSharedCheck_3617_;
goto v_resetjp_3595_;
}
v_resetjp_3595_:
{
lean_object* v___x_3598_; 
lean_inc(v_numSectionVars_3575_);
lean_inc_ref(v_fnNames_3574_);
v___x_3598_ = l_Lean_Elab_Structural_preprocess(v_value_3593_, v_fnNames_3574_, v_numSectionVars_3575_, v___y_3579_, v___y_3580_);
if (lean_obj_tag(v___x_3598_) == 0)
{
lean_object* v_a_3599_; lean_object* v___x_3600_; lean_object* v_bs_x27_3601_; lean_object* v___x_3603_; 
v_a_3599_ = lean_ctor_get(v___x_3598_, 0);
lean_inc(v_a_3599_);
lean_dec_ref(v___x_3598_);
v___x_3600_ = lean_unsigned_to_nat(0u);
v_bs_x27_3601_ = lean_array_uset(v_bs_3578_, v_i_3577_, v___x_3600_);
if (v_isShared_3597_ == 0)
{
lean_ctor_set(v___x_3596_, 7, v_a_3599_);
v___x_3603_ = v___x_3596_;
goto v_reusejp_3602_;
}
else
{
lean_object* v_reuseFailAlloc_3608_; 
v_reuseFailAlloc_3608_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_3608_, 0, v_ref_3585_);
lean_ctor_set(v_reuseFailAlloc_3608_, 1, v_levelParams_3587_);
lean_ctor_set(v_reuseFailAlloc_3608_, 2, v_modifiers_3588_);
lean_ctor_set(v_reuseFailAlloc_3608_, 3, v_declName_3589_);
lean_ctor_set(v_reuseFailAlloc_3608_, 4, v_binders_3590_);
lean_ctor_set(v_reuseFailAlloc_3608_, 5, v_numSectionVars_3591_);
lean_ctor_set(v_reuseFailAlloc_3608_, 6, v_type_3592_);
lean_ctor_set(v_reuseFailAlloc_3608_, 7, v_a_3599_);
lean_ctor_set(v_reuseFailAlloc_3608_, 8, v_termination_3594_);
lean_ctor_set_uint8(v_reuseFailAlloc_3608_, sizeof(void*)*9, v_kind_3586_);
v___x_3603_ = v_reuseFailAlloc_3608_;
goto v_reusejp_3602_;
}
v_reusejp_3602_:
{
size_t v___x_3604_; size_t v___x_3605_; lean_object* v___x_3606_; 
v___x_3604_ = ((size_t)1ULL);
v___x_3605_ = lean_usize_add(v_i_3577_, v___x_3604_);
v___x_3606_ = lean_array_uset(v_bs_x27_3601_, v_i_3577_, v___x_3603_);
v_i_3577_ = v___x_3605_;
v_bs_3578_ = v___x_3606_;
goto _start;
}
}
else
{
lean_object* v_a_3609_; lean_object* v___x_3611_; uint8_t v_isShared_3612_; uint8_t v_isSharedCheck_3616_; 
lean_del_object(v___x_3596_);
lean_dec_ref(v_termination_3594_);
lean_dec_ref(v_type_3592_);
lean_dec(v_numSectionVars_3591_);
lean_dec(v_binders_3590_);
lean_dec(v_declName_3589_);
lean_dec_ref(v_modifiers_3588_);
lean_dec(v_levelParams_3587_);
lean_dec(v_ref_3585_);
lean_dec_ref(v_bs_3578_);
lean_dec(v_numSectionVars_3575_);
lean_dec_ref(v_fnNames_3574_);
v_a_3609_ = lean_ctor_get(v___x_3598_, 0);
v_isSharedCheck_3616_ = !lean_is_exclusive(v___x_3598_);
if (v_isSharedCheck_3616_ == 0)
{
v___x_3611_ = v___x_3598_;
v_isShared_3612_ = v_isSharedCheck_3616_;
goto v_resetjp_3610_;
}
else
{
lean_inc(v_a_3609_);
lean_dec(v___x_3598_);
v___x_3611_ = lean_box(0);
v_isShared_3612_ = v_isSharedCheck_3616_;
goto v_resetjp_3610_;
}
v_resetjp_3610_:
{
lean_object* v___x_3614_; 
if (v_isShared_3612_ == 0)
{
v___x_3614_ = v___x_3611_;
goto v_reusejp_3613_;
}
else
{
lean_object* v_reuseFailAlloc_3615_; 
v_reuseFailAlloc_3615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3615_, 0, v_a_3609_);
v___x_3614_ = v_reuseFailAlloc_3615_;
goto v_reusejp_3613_;
}
v_reusejp_3613_:
{
return v___x_3614_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1___redArg___boxed(lean_object* v_fnNames_3618_, lean_object* v_numSectionVars_3619_, lean_object* v_sz_3620_, lean_object* v_i_3621_, lean_object* v_bs_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_){
_start:
{
size_t v_sz_boxed_3626_; size_t v_i_boxed_3627_; lean_object* v_res_3628_; 
v_sz_boxed_3626_ = lean_unbox_usize(v_sz_3620_);
lean_dec(v_sz_3620_);
v_i_boxed_3627_ = lean_unbox_usize(v_i_3621_);
lean_dec(v_i_3621_);
v_res_3628_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1___redArg(v_fnNames_3618_, v_numSectionVars_3619_, v_sz_boxed_3626_, v_i_boxed_3627_, v_bs_3622_, v___y_3623_, v___y_3624_);
lean_dec(v___y_3624_);
lean_dec_ref(v___y_3623_);
return v_res_3628_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1(lean_object* v_fnNames_3629_, lean_object* v_numSectionVars_3630_, size_t v_sz_3631_, size_t v_i_3632_, lean_object* v_bs_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_){
_start:
{
lean_object* v___x_3639_; 
v___x_3639_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1___redArg(v_fnNames_3629_, v_numSectionVars_3630_, v_sz_3631_, v_i_3632_, v_bs_3633_, v___y_3636_, v___y_3637_);
return v___x_3639_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1___boxed(lean_object* v_fnNames_3640_, lean_object* v_numSectionVars_3641_, lean_object* v_sz_3642_, lean_object* v_i_3643_, lean_object* v_bs_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_){
_start:
{
size_t v_sz_boxed_3650_; size_t v_i_boxed_3651_; lean_object* v_res_3652_; 
v_sz_boxed_3650_ = lean_unbox_usize(v_sz_3642_);
lean_dec(v_sz_3642_);
v_i_boxed_3651_ = lean_unbox_usize(v_i_3643_);
lean_dec(v_i_3643_);
v_res_3652_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1(v_fnNames_3640_, v_numSectionVars_3641_, v_sz_boxed_3650_, v_i_boxed_3651_, v_bs_3644_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_);
lean_dec(v___y_3648_);
lean_dec_ref(v___y_3647_);
lean_dec(v___y_3646_);
lean_dec_ref(v___y_3645_);
return v_res_3652_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos(lean_object* v_preDefs_3653_, lean_object* v_termMeasure_x3fs_3654_, lean_object* v_a_3655_, lean_object* v_a_3656_, lean_object* v_a_3657_, lean_object* v_a_3658_){
_start:
{
lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v_numSectionVars_3663_; size_t v_sz_3664_; size_t v___x_3665_; lean_object* v_fnNames_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; 
v___x_3660_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_3661_ = lean_unsigned_to_nat(0u);
v___x_3662_ = lean_array_get_borrowed(v___x_3660_, v_preDefs_3653_, v___x_3661_);
v_numSectionVars_3663_ = lean_ctor_get(v___x_3662_, 5);
v_sz_3664_ = lean_array_size(v_preDefs_3653_);
v___x_3665_ = ((size_t)0ULL);
lean_inc_ref_n(v_preDefs_3653_, 2);
v_fnNames_3666_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0(v_sz_3664_, v___x_3665_, v_preDefs_3653_);
v___x_3667_ = lean_box_usize(v_sz_3664_);
v___x_3668_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___boxed__const__1));
lean_inc(v_numSectionVars_3663_);
lean_inc_ref(v_fnNames_3666_);
v___x_3669_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1___boxed), 10, 5);
lean_closure_set(v___x_3669_, 0, v_fnNames_3666_);
lean_closure_set(v___x_3669_, 1, v_numSectionVars_3663_);
lean_closure_set(v___x_3669_, 2, v___x_3667_);
lean_closure_set(v___x_3669_, 3, v___x_3668_);
lean_closure_set(v___x_3669_, 4, v_preDefs_3653_);
v___x_3670_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v_preDefs_3653_, v___x_3669_, v_a_3655_, v_a_3656_, v_a_3657_, v_a_3658_);
if (lean_obj_tag(v___x_3670_) == 0)
{
lean_object* v_a_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; 
v_a_3671_ = lean_ctor_get(v___x_3670_, 0);
lean_inc_n(v_a_3671_, 3);
lean_dec_ref(v___x_3670_);
v___x_3672_ = lean_alloc_closure((void*)(l_Lean_Elab_getFixedParamPerms___boxed), 6, 1);
lean_closure_set(v___x_3672_, 0, v_a_3671_);
v___x_3673_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v_a_3671_, v___x_3672_, v_a_3655_, v_a_3656_, v_a_3657_, v_a_3658_);
if (lean_obj_tag(v___x_3673_) == 0)
{
lean_object* v_a_3674_; lean_object* v_perms_3675_; lean_object* v___x_3676_; lean_object* v_type_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___f_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; 
v_a_3674_ = lean_ctor_get(v___x_3673_, 0);
lean_inc(v_a_3674_);
lean_dec_ref(v___x_3673_);
v_perms_3675_ = lean_ctor_get(v_a_3674_, 1);
lean_inc_ref_n(v_perms_3675_, 2);
v___x_3676_ = lean_array_get_borrowed(v___x_3660_, v_a_3671_, v___x_3661_);
v_type_3677_ = lean_ctor_get(v___x_3676_, 6);
lean_inc_ref(v_type_3677_);
v___x_3678_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0, &l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0_once, _init_l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0);
v___x_3679_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___boxed__const__1));
v___f_3680_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__2___boxed), 13, 7);
lean_closure_set(v___f_3680_, 0, v_a_3671_);
lean_closure_set(v___f_3680_, 1, v_perms_3675_);
lean_closure_set(v___f_3680_, 2, v___x_3661_);
lean_closure_set(v___f_3680_, 3, v_fnNames_3666_);
lean_closure_set(v___f_3680_, 4, v_a_3674_);
lean_closure_set(v___f_3680_, 5, v_termMeasure_x3fs_3654_);
lean_closure_set(v___f_3680_, 6, v___x_3679_);
v___x_3681_ = lean_array_get(v___x_3678_, v_perms_3675_, v___x_3661_);
lean_dec_ref(v_perms_3675_);
v___x_3682_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg(v___x_3681_, v_type_3677_, v___f_3680_, v_a_3655_, v_a_3656_, v_a_3657_, v_a_3658_);
return v___x_3682_;
}
else
{
lean_object* v_a_3683_; lean_object* v___x_3685_; uint8_t v_isShared_3686_; uint8_t v_isSharedCheck_3690_; 
lean_dec(v_a_3671_);
lean_dec_ref(v_fnNames_3666_);
lean_dec_ref(v_termMeasure_x3fs_3654_);
v_a_3683_ = lean_ctor_get(v___x_3673_, 0);
v_isSharedCheck_3690_ = !lean_is_exclusive(v___x_3673_);
if (v_isSharedCheck_3690_ == 0)
{
v___x_3685_ = v___x_3673_;
v_isShared_3686_ = v_isSharedCheck_3690_;
goto v_resetjp_3684_;
}
else
{
lean_inc(v_a_3683_);
lean_dec(v___x_3673_);
v___x_3685_ = lean_box(0);
v_isShared_3686_ = v_isSharedCheck_3690_;
goto v_resetjp_3684_;
}
v_resetjp_3684_:
{
lean_object* v___x_3688_; 
if (v_isShared_3686_ == 0)
{
v___x_3688_ = v___x_3685_;
goto v_reusejp_3687_;
}
else
{
lean_object* v_reuseFailAlloc_3689_; 
v_reuseFailAlloc_3689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3689_, 0, v_a_3683_);
v___x_3688_ = v_reuseFailAlloc_3689_;
goto v_reusejp_3687_;
}
v_reusejp_3687_:
{
return v___x_3688_;
}
}
}
}
else
{
lean_object* v_a_3691_; lean_object* v___x_3693_; uint8_t v_isShared_3694_; uint8_t v_isSharedCheck_3698_; 
lean_dec_ref(v_fnNames_3666_);
lean_dec_ref(v_termMeasure_x3fs_3654_);
v_a_3691_ = lean_ctor_get(v___x_3670_, 0);
v_isSharedCheck_3698_ = !lean_is_exclusive(v___x_3670_);
if (v_isSharedCheck_3698_ == 0)
{
v___x_3693_ = v___x_3670_;
v_isShared_3694_ = v_isSharedCheck_3698_;
goto v_resetjp_3692_;
}
else
{
lean_inc(v_a_3691_);
lean_dec(v___x_3670_);
v___x_3693_ = lean_box(0);
v_isShared_3694_ = v_isSharedCheck_3698_;
goto v_resetjp_3692_;
}
v_resetjp_3692_:
{
lean_object* v___x_3696_; 
if (v_isShared_3694_ == 0)
{
v___x_3696_ = v___x_3693_;
goto v_reusejp_3695_;
}
else
{
lean_object* v_reuseFailAlloc_3697_; 
v_reuseFailAlloc_3697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3697_, 0, v_a_3691_);
v___x_3696_ = v_reuseFailAlloc_3697_;
goto v_reusejp_3695_;
}
v_reusejp_3695_:
{
return v___x_3696_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___boxed(lean_object* v_preDefs_3699_, lean_object* v_termMeasure_x3fs_3700_, lean_object* v_a_3701_, lean_object* v_a_3702_, lean_object* v_a_3703_, lean_object* v_a_3704_, lean_object* v_a_3705_){
_start:
{
lean_object* v_res_3706_; 
v_res_3706_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos(v_preDefs_3699_, v_termMeasure_x3fs_3700_, v_a_3701_, v_a_3702_, v_a_3703_, v_a_3704_);
lean_dec(v_a_3704_);
lean_dec_ref(v_a_3703_);
lean_dec(v_a_3702_);
lean_dec_ref(v_a_3701_);
return v_res_3706_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4(lean_object* v_fst_3707_, lean_object* v_as_3708_, lean_object* v_i_3709_, lean_object* v_j_3710_, lean_object* v_inv_3711_, lean_object* v_bs_3712_){
_start:
{
lean_object* v___x_3713_; 
v___x_3713_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg(v_fst_3707_, v_as_3708_, v_i_3709_, v_j_3710_, v_bs_3712_);
return v___x_3713_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___boxed(lean_object* v_fst_3714_, lean_object* v_as_3715_, lean_object* v_i_3716_, lean_object* v_j_3717_, lean_object* v_inv_3718_, lean_object* v_bs_3719_){
_start:
{
lean_object* v_res_3720_; 
v_res_3720_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4(v_fst_3714_, v_as_3715_, v_i_3716_, v_j_3717_, v_inv_3718_, v_bs_3719_);
lean_dec_ref(v_as_3715_);
lean_dec_ref(v_fst_3714_);
return v_res_3720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10(lean_object* v_00_u03b1_3721_, lean_object* v_lctx_3722_, lean_object* v_localInsts_3723_, lean_object* v_x_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_){
_start:
{
lean_object* v___x_3730_; 
v___x_3730_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___redArg(v_lctx_3722_, v_localInsts_3723_, v_x_3724_, v___y_3725_, v___y_3726_, v___y_3727_, v___y_3728_);
return v___x_3730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___boxed(lean_object* v_00_u03b1_3731_, lean_object* v_lctx_3732_, lean_object* v_localInsts_3733_, lean_object* v_x_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_){
_start:
{
lean_object* v_res_3740_; 
v_res_3740_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10(v_00_u03b1_3731_, v_lctx_3732_, v_localInsts_3733_, v_x_3734_, v___y_3735_, v___y_3736_, v___y_3737_, v___y_3738_);
lean_dec(v___y_3738_);
lean_dec_ref(v___y_3737_);
lean_dec(v___y_3736_);
lean_dec_ref(v___y_3735_);
return v_res_3740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9(lean_object* v_00_u03b1_3741_, lean_object* v_fvarIds_3742_, lean_object* v_k_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_){
_start:
{
lean_object* v___x_3749_; 
v___x_3749_ = l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___redArg(v_fvarIds_3742_, v_k_3743_, v___y_3744_, v___y_3745_, v___y_3746_, v___y_3747_);
return v___x_3749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___boxed(lean_object* v_00_u03b1_3750_, lean_object* v_fvarIds_3751_, lean_object* v_k_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_){
_start:
{
lean_object* v_res_3758_; 
v_res_3758_ = l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9(v_00_u03b1_3750_, v_fvarIds_3751_, v_k_3752_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_);
lean_dec(v___y_3756_);
lean_dec_ref(v___y_3755_);
lean_dec(v___y_3754_);
lean_dec_ref(v___y_3753_);
lean_dec_ref(v_fvarIds_3751_);
return v_res_3758_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__15(lean_object* v_a_3759_){
_start:
{
lean_object* v___x_3760_; 
v___x_3760_ = lean_nat_to_int(v_a_3759_);
return v___x_3760_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12(lean_object* v___x_3761_, lean_object* v_xs_3762_, lean_object* v_as_3763_, lean_object* v_i_3764_, lean_object* v_j_3765_, lean_object* v_inv_3766_, lean_object* v_bs_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_){
_start:
{
lean_object* v___x_3773_; 
v___x_3773_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg(v___x_3761_, v_xs_3762_, v_as_3763_, v_i_3764_, v_j_3765_, v_bs_3767_, v___y_3768_, v___y_3769_, v___y_3770_, v___y_3771_);
return v___x_3773_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___boxed(lean_object* v___x_3774_, lean_object* v_xs_3775_, lean_object* v_as_3776_, lean_object* v_i_3777_, lean_object* v_j_3778_, lean_object* v_inv_3779_, lean_object* v_bs_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_){
_start:
{
lean_object* v_res_3786_; 
v_res_3786_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12(v___x_3774_, v_xs_3775_, v_as_3776_, v_i_3777_, v_j_3778_, v_inv_3779_, v_bs_3780_, v___y_3781_, v___y_3782_, v___y_3783_, v___y_3784_);
lean_dec(v___y_3784_);
lean_dec_ref(v___y_3783_);
lean_dec(v___y_3782_);
lean_dec_ref(v___y_3781_);
lean_dec_ref(v_as_3776_);
lean_dec_ref(v___x_3774_);
return v_res_3786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure___lam__0(lean_object* v___x_3787_, lean_object* v_recArgPos_3788_, lean_object* v_xs_3789_, lean_object* v_x_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_){
_start:
{
lean_object* v___x_3796_; uint8_t v___x_3797_; uint8_t v___x_3798_; uint8_t v___x_3799_; lean_object* v___x_3800_; 
v___x_3796_ = lean_array_get_borrowed(v___x_3787_, v_xs_3789_, v_recArgPos_3788_);
v___x_3797_ = 0;
v___x_3798_ = 1;
v___x_3799_ = 1;
lean_inc(v___x_3796_);
v___x_3800_ = l_Lean_Meta_mkLambdaFVars(v_xs_3789_, v___x_3796_, v___x_3797_, v___x_3798_, v___x_3797_, v___x_3798_, v___x_3799_, v___y_3791_, v___y_3792_, v___y_3793_, v___y_3794_);
return v___x_3800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure___lam__0___boxed(lean_object* v___x_3801_, lean_object* v_recArgPos_3802_, lean_object* v_xs_3803_, lean_object* v_x_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_){
_start:
{
lean_object* v_res_3810_; 
v_res_3810_ = l_Lean_Elab_Structural_reportTermMeasure___lam__0(v___x_3801_, v_recArgPos_3802_, v_xs_3803_, v_x_3804_, v___y_3805_, v___y_3806_, v___y_3807_, v___y_3808_);
lean_dec(v___y_3808_);
lean_dec_ref(v___y_3807_);
lean_dec(v___y_3806_);
lean_dec_ref(v___y_3805_);
lean_dec_ref(v_x_3804_);
lean_dec_ref(v_xs_3803_);
lean_dec(v_recArgPos_3802_);
lean_dec_ref(v___x_3801_);
return v_res_3810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure___lam__1(lean_object* v_xs_3811_, lean_object* v_x_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_){
_start:
{
lean_object* v___x_3818_; lean_object* v___x_3819_; 
v___x_3818_ = lean_array_get_size(v_xs_3811_);
v___x_3819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3819_, 0, v___x_3818_);
return v___x_3819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure___lam__1___boxed(lean_object* v_xs_3820_, lean_object* v_x_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_){
_start:
{
lean_object* v_res_3827_; 
v_res_3827_ = l_Lean_Elab_Structural_reportTermMeasure___lam__1(v_xs_3820_, v_x_3821_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_);
lean_dec(v___y_3825_);
lean_dec_ref(v___y_3824_);
lean_dec(v___y_3823_);
lean_dec_ref(v___y_3822_);
lean_dec_ref(v_x_3821_);
lean_dec_ref(v_xs_3820_);
return v_res_3827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure(lean_object* v_preDef_3839_, lean_object* v_recArgPos_3840_, lean_object* v_a_3841_, lean_object* v_a_3842_, lean_object* v_a_3843_, lean_object* v_a_3844_){
_start:
{
lean_object* v_termination_3846_; lean_object* v_terminationBy_x3f_x3f_3847_; 
v_termination_3846_ = lean_ctor_get(v_preDef_3839_, 8);
lean_inc_ref(v_termination_3846_);
v_terminationBy_x3f_x3f_3847_ = lean_ctor_get(v_termination_3846_, 1);
lean_inc(v_terminationBy_x3f_x3f_3847_);
if (lean_obj_tag(v_terminationBy_x3f_x3f_3847_) == 1)
{
lean_object* v_value_3848_; lean_object* v_extraParams_3849_; lean_object* v___x_3851_; uint8_t v_isShared_3852_; uint8_t v_isSharedCheck_3901_; 
v_value_3848_ = lean_ctor_get(v_preDef_3839_, 7);
lean_inc_ref(v_value_3848_);
lean_dec_ref(v_preDef_3839_);
v_extraParams_3849_ = lean_ctor_get(v_termination_3846_, 5);
v_isSharedCheck_3901_ = !lean_is_exclusive(v_termination_3846_);
if (v_isSharedCheck_3901_ == 0)
{
lean_object* v_unused_3902_; lean_object* v_unused_3903_; lean_object* v_unused_3904_; lean_object* v_unused_3905_; lean_object* v_unused_3906_; 
v_unused_3902_ = lean_ctor_get(v_termination_3846_, 4);
lean_dec(v_unused_3902_);
v_unused_3903_ = lean_ctor_get(v_termination_3846_, 3);
lean_dec(v_unused_3903_);
v_unused_3904_ = lean_ctor_get(v_termination_3846_, 2);
lean_dec(v_unused_3904_);
v_unused_3905_ = lean_ctor_get(v_termination_3846_, 1);
lean_dec(v_unused_3905_);
v_unused_3906_ = lean_ctor_get(v_termination_3846_, 0);
lean_dec(v_unused_3906_);
v___x_3851_ = v_termination_3846_;
v_isShared_3852_ = v_isSharedCheck_3901_;
goto v_resetjp_3850_;
}
else
{
lean_inc(v_extraParams_3849_);
lean_dec(v_termination_3846_);
v___x_3851_ = lean_box(0);
v_isShared_3852_ = v_isSharedCheck_3901_;
goto v_resetjp_3850_;
}
v_resetjp_3850_:
{
lean_object* v_val_3853_; lean_object* v___x_3854_; lean_object* v___f_3855_; uint8_t v___x_3856_; lean_object* v___x_3857_; 
v_val_3853_ = lean_ctor_get(v_terminationBy_x3f_x3f_3847_, 0);
lean_inc(v_val_3853_);
lean_dec_ref(v_terminationBy_x3f_x3f_3847_);
v___x_3854_ = l_Lean_instInhabitedExpr;
v___f_3855_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_reportTermMeasure___lam__0___boxed), 9, 2);
lean_closure_set(v___f_3855_, 0, v___x_3854_);
lean_closure_set(v___f_3855_, 1, v_recArgPos_3840_);
v___x_3856_ = 0;
lean_inc_ref(v_value_3848_);
v___x_3857_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg(v_value_3848_, v___f_3855_, v___x_3856_, v_a_3841_, v_a_3842_, v_a_3843_, v_a_3844_);
if (lean_obj_tag(v___x_3857_) == 0)
{
lean_object* v_a_3858_; lean_object* v___f_3859_; lean_object* v___x_3860_; 
v_a_3858_ = lean_ctor_get(v___x_3857_, 0);
lean_inc(v_a_3858_);
lean_dec_ref(v___x_3857_);
v___f_3859_ = ((lean_object*)(l_Lean_Elab_Structural_reportTermMeasure___closed__0));
v___x_3860_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg(v_value_3848_, v___f_3859_, v___x_3856_, v_a_3841_, v_a_3842_, v_a_3843_, v_a_3844_);
if (lean_obj_tag(v___x_3860_) == 0)
{
lean_object* v_a_3861_; lean_object* v___x_3862_; uint8_t v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; 
v_a_3861_ = lean_ctor_get(v___x_3860_, 0);
lean_inc(v_a_3861_);
lean_dec_ref(v___x_3860_);
v___x_3862_ = lean_box(0);
v___x_3863_ = 1;
v___x_3864_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3864_, 0, v___x_3862_);
lean_ctor_set(v___x_3864_, 1, v_a_3858_);
lean_ctor_set_uint8(v___x_3864_, sizeof(void*)*2, v___x_3863_);
v___x_3865_ = l_Lean_Elab_TerminationMeasure_delab(v_a_3861_, v_extraParams_3849_, v___x_3864_, v_a_3841_, v_a_3842_, v_a_3843_, v_a_3844_);
lean_dec(v_a_3861_);
if (lean_obj_tag(v___x_3865_) == 0)
{
lean_object* v_a_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3871_; 
v_a_3866_ = lean_ctor_get(v___x_3865_, 0);
lean_inc(v_a_3866_);
lean_dec_ref(v___x_3865_);
v___x_3867_ = ((lean_object*)(l_Lean_Elab_Structural_reportTermMeasure___closed__5));
v___x_3868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3868_, 0, v___x_3867_);
lean_ctor_set(v___x_3868_, 1, v_a_3866_);
v___x_3869_ = lean_box(0);
if (v_isShared_3852_ == 0)
{
lean_ctor_set(v___x_3851_, 5, v___x_3869_);
lean_ctor_set(v___x_3851_, 4, v___x_3869_);
lean_ctor_set(v___x_3851_, 3, v___x_3869_);
lean_ctor_set(v___x_3851_, 2, v___x_3869_);
lean_ctor_set(v___x_3851_, 1, v___x_3869_);
lean_ctor_set(v___x_3851_, 0, v___x_3868_);
v___x_3871_ = v___x_3851_;
goto v_reusejp_3870_;
}
else
{
lean_object* v_reuseFailAlloc_3876_; 
v_reuseFailAlloc_3876_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3876_, 0, v___x_3868_);
lean_ctor_set(v_reuseFailAlloc_3876_, 1, v___x_3869_);
lean_ctor_set(v_reuseFailAlloc_3876_, 2, v___x_3869_);
lean_ctor_set(v_reuseFailAlloc_3876_, 3, v___x_3869_);
lean_ctor_set(v_reuseFailAlloc_3876_, 4, v___x_3869_);
lean_ctor_set(v_reuseFailAlloc_3876_, 5, v___x_3869_);
v___x_3871_ = v_reuseFailAlloc_3876_;
goto v_reusejp_3870_;
}
v_reusejp_3870_:
{
lean_object* v___x_3872_; uint8_t v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; 
v___x_3872_ = ((lean_object*)(l_Lean_Elab_Structural_reportTermMeasure___closed__6));
v___x_3873_ = 4;
v___x_3874_ = l_Lean_MessageData_nil;
v___x_3875_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_val_3853_, v___x_3871_, v___x_3869_, v___x_3872_, v___x_3869_, v___x_3873_, v___x_3874_, v_a_3843_, v_a_3844_);
return v___x_3875_;
}
}
else
{
lean_object* v_a_3877_; lean_object* v___x_3879_; uint8_t v_isShared_3880_; uint8_t v_isSharedCheck_3884_; 
lean_dec(v_val_3853_);
lean_del_object(v___x_3851_);
v_a_3877_ = lean_ctor_get(v___x_3865_, 0);
v_isSharedCheck_3884_ = !lean_is_exclusive(v___x_3865_);
if (v_isSharedCheck_3884_ == 0)
{
v___x_3879_ = v___x_3865_;
v_isShared_3880_ = v_isSharedCheck_3884_;
goto v_resetjp_3878_;
}
else
{
lean_inc(v_a_3877_);
lean_dec(v___x_3865_);
v___x_3879_ = lean_box(0);
v_isShared_3880_ = v_isSharedCheck_3884_;
goto v_resetjp_3878_;
}
v_resetjp_3878_:
{
lean_object* v___x_3882_; 
if (v_isShared_3880_ == 0)
{
v___x_3882_ = v___x_3879_;
goto v_reusejp_3881_;
}
else
{
lean_object* v_reuseFailAlloc_3883_; 
v_reuseFailAlloc_3883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3883_, 0, v_a_3877_);
v___x_3882_ = v_reuseFailAlloc_3883_;
goto v_reusejp_3881_;
}
v_reusejp_3881_:
{
return v___x_3882_;
}
}
}
}
else
{
lean_object* v_a_3885_; lean_object* v___x_3887_; uint8_t v_isShared_3888_; uint8_t v_isSharedCheck_3892_; 
lean_dec(v_a_3858_);
lean_dec(v_val_3853_);
lean_del_object(v___x_3851_);
lean_dec(v_extraParams_3849_);
v_a_3885_ = lean_ctor_get(v___x_3860_, 0);
v_isSharedCheck_3892_ = !lean_is_exclusive(v___x_3860_);
if (v_isSharedCheck_3892_ == 0)
{
v___x_3887_ = v___x_3860_;
v_isShared_3888_ = v_isSharedCheck_3892_;
goto v_resetjp_3886_;
}
else
{
lean_inc(v_a_3885_);
lean_dec(v___x_3860_);
v___x_3887_ = lean_box(0);
v_isShared_3888_ = v_isSharedCheck_3892_;
goto v_resetjp_3886_;
}
v_resetjp_3886_:
{
lean_object* v___x_3890_; 
if (v_isShared_3888_ == 0)
{
v___x_3890_ = v___x_3887_;
goto v_reusejp_3889_;
}
else
{
lean_object* v_reuseFailAlloc_3891_; 
v_reuseFailAlloc_3891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3891_, 0, v_a_3885_);
v___x_3890_ = v_reuseFailAlloc_3891_;
goto v_reusejp_3889_;
}
v_reusejp_3889_:
{
return v___x_3890_;
}
}
}
}
else
{
lean_object* v_a_3893_; lean_object* v___x_3895_; uint8_t v_isShared_3896_; uint8_t v_isSharedCheck_3900_; 
lean_dec(v_val_3853_);
lean_del_object(v___x_3851_);
lean_dec(v_extraParams_3849_);
lean_dec_ref(v_value_3848_);
v_a_3893_ = lean_ctor_get(v___x_3857_, 0);
v_isSharedCheck_3900_ = !lean_is_exclusive(v___x_3857_);
if (v_isSharedCheck_3900_ == 0)
{
v___x_3895_ = v___x_3857_;
v_isShared_3896_ = v_isSharedCheck_3900_;
goto v_resetjp_3894_;
}
else
{
lean_inc(v_a_3893_);
lean_dec(v___x_3857_);
v___x_3895_ = lean_box(0);
v_isShared_3896_ = v_isSharedCheck_3900_;
goto v_resetjp_3894_;
}
v_resetjp_3894_:
{
lean_object* v___x_3898_; 
if (v_isShared_3896_ == 0)
{
v___x_3898_ = v___x_3895_;
goto v_reusejp_3897_;
}
else
{
lean_object* v_reuseFailAlloc_3899_; 
v_reuseFailAlloc_3899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3899_, 0, v_a_3893_);
v___x_3898_ = v_reuseFailAlloc_3899_;
goto v_reusejp_3897_;
}
v_reusejp_3897_:
{
return v___x_3898_;
}
}
}
}
}
else
{
lean_object* v___x_3907_; lean_object* v___x_3908_; 
lean_dec(v_terminationBy_x3f_x3f_3847_);
lean_dec_ref(v_termination_3846_);
lean_dec(v_recArgPos_3840_);
lean_dec_ref(v_preDef_3839_);
v___x_3907_ = lean_box(0);
v___x_3908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3908_, 0, v___x_3907_);
return v___x_3908_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure___boxed(lean_object* v_preDef_3909_, lean_object* v_recArgPos_3910_, lean_object* v_a_3911_, lean_object* v_a_3912_, lean_object* v_a_3913_, lean_object* v_a_3914_, lean_object* v_a_3915_){
_start:
{
lean_object* v_res_3916_; 
v_res_3916_ = l_Lean_Elab_Structural_reportTermMeasure(v_preDef_3909_, v_recArgPos_3910_, v_a_3911_, v_a_3912_, v_a_3913_, v_a_3914_);
lean_dec(v_a_3914_);
lean_dec_ref(v_a_3913_);
lean_dec(v_a_3912_);
lean_dec_ref(v_a_3911_);
return v_res_3916_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___redArg(lean_object* v_as_3917_, size_t v_sz_3918_, size_t v_i_3919_, lean_object* v_b_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_){
_start:
{
uint8_t v___x_3926_; 
v___x_3926_ = lean_usize_dec_lt(v_i_3919_, v_sz_3918_);
if (v___x_3926_ == 0)
{
lean_object* v___x_3927_; 
v___x_3927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3927_, 0, v_b_3920_);
return v___x_3927_;
}
else
{
lean_object* v_a_3928_; lean_object* v_declName_3929_; lean_object* v___x_3930_; 
v_a_3928_ = lean_array_uget_borrowed(v_as_3917_, v_i_3919_);
v_declName_3929_ = lean_ctor_get(v_a_3928_, 3);
lean_inc(v_declName_3929_);
v___x_3930_ = l_Lean_Meta_saveEqnAffectingOptions(v_declName_3929_, v___y_3921_, v___y_3922_, v___y_3923_, v___y_3924_);
if (lean_obj_tag(v___x_3930_) == 0)
{
lean_object* v___x_3931_; size_t v___x_3932_; size_t v___x_3933_; 
lean_dec_ref(v___x_3930_);
v___x_3931_ = lean_box(0);
v___x_3932_ = ((size_t)1ULL);
v___x_3933_ = lean_usize_add(v_i_3919_, v___x_3932_);
v_i_3919_ = v___x_3933_;
v_b_3920_ = v___x_3931_;
goto _start;
}
else
{
return v___x_3930_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___redArg___boxed(lean_object* v_as_3935_, lean_object* v_sz_3936_, lean_object* v_i_3937_, lean_object* v_b_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_){
_start:
{
size_t v_sz_boxed_3944_; size_t v_i_boxed_3945_; lean_object* v_res_3946_; 
v_sz_boxed_3944_ = lean_unbox_usize(v_sz_3936_);
lean_dec(v_sz_3936_);
v_i_boxed_3945_ = lean_unbox_usize(v_i_3937_);
lean_dec(v_i_3937_);
v_res_3946_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___redArg(v_as_3935_, v_sz_boxed_3944_, v_i_boxed_3945_, v_b_3938_, v___y_3939_, v___y_3940_, v___y_3941_, v___y_3942_);
lean_dec(v___y_3942_);
lean_dec_ref(v___y_3941_);
lean_dec(v___y_3940_);
lean_dec_ref(v___y_3939_);
lean_dec_ref(v_as_3935_);
return v_res_3946_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__1(lean_object* v_docCtx_3947_, lean_object* v_a_3948_, lean_object* v_snd_3949_, lean_object* v_as_3950_, size_t v_sz_3951_, size_t v_i_3952_, lean_object* v_b_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_){
_start:
{
uint8_t v___x_3961_; 
v___x_3961_ = lean_usize_dec_lt(v_i_3952_, v_sz_3951_);
if (v___x_3961_ == 0)
{
lean_object* v___x_3962_; 
lean_dec_ref(v_snd_3949_);
lean_dec_ref(v_a_3948_);
lean_dec_ref(v_docCtx_3947_);
v___x_3962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3962_, 0, v_b_3953_);
return v___x_3962_;
}
else
{
lean_object* v_array_3963_; lean_object* v_start_3964_; lean_object* v_stop_3965_; uint8_t v___x_3966_; 
v_array_3963_ = lean_ctor_get(v_b_3953_, 0);
v_start_3964_ = lean_ctor_get(v_b_3953_, 1);
v_stop_3965_ = lean_ctor_get(v_b_3953_, 2);
v___x_3966_ = lean_nat_dec_lt(v_start_3964_, v_stop_3965_);
if (v___x_3966_ == 0)
{
lean_object* v___x_3967_; 
lean_dec_ref(v_snd_3949_);
lean_dec_ref(v_a_3948_);
lean_dec_ref(v_docCtx_3947_);
v___x_3967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3967_, 0, v_b_3953_);
return v___x_3967_;
}
else
{
lean_object* v___x_3969_; uint8_t v_isShared_3970_; uint8_t v_isSharedCheck_4034_; 
lean_inc(v_stop_3965_);
lean_inc(v_start_3964_);
lean_inc_ref(v_array_3963_);
v_isSharedCheck_4034_ = !lean_is_exclusive(v_b_3953_);
if (v_isSharedCheck_4034_ == 0)
{
lean_object* v_unused_4035_; lean_object* v_unused_4036_; lean_object* v_unused_4037_; 
v_unused_4035_ = lean_ctor_get(v_b_3953_, 2);
lean_dec(v_unused_4035_);
v_unused_4036_ = lean_ctor_get(v_b_3953_, 1);
lean_dec(v_unused_4036_);
v_unused_4037_ = lean_ctor_get(v_b_3953_, 0);
lean_dec(v_unused_4037_);
v___x_3969_ = v_b_3953_;
v_isShared_3970_ = v_isSharedCheck_4034_;
goto v_resetjp_3968_;
}
else
{
lean_dec(v_b_3953_);
v___x_3969_ = lean_box(0);
v_isShared_3970_ = v_isSharedCheck_4034_;
goto v_resetjp_3968_;
}
v_resetjp_3968_:
{
lean_object* v_a_3971_; uint8_t v_kind_3972_; lean_object* v_type_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3978_; 
v_a_3971_ = lean_array_uget_borrowed(v_as_3950_, v_i_3952_);
v_kind_3972_ = lean_ctor_get_uint8(v_a_3971_, sizeof(void*)*9);
v_type_3973_ = lean_ctor_get(v_a_3971_, 6);
v___x_3974_ = lean_array_fget(v_array_3963_, v_start_3964_);
v___x_3975_ = lean_unsigned_to_nat(1u);
v___x_3976_ = lean_nat_add(v_start_3964_, v___x_3975_);
lean_dec(v_start_3964_);
if (v_isShared_3970_ == 0)
{
lean_ctor_set(v___x_3969_, 1, v___x_3976_);
v___x_3978_ = v___x_3969_;
goto v_reusejp_3977_;
}
else
{
lean_object* v_reuseFailAlloc_4033_; 
v_reuseFailAlloc_4033_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4033_, 0, v_array_3963_);
lean_ctor_set(v_reuseFailAlloc_4033_, 1, v___x_3976_);
lean_ctor_set(v_reuseFailAlloc_4033_, 2, v_stop_3965_);
v___x_3978_ = v_reuseFailAlloc_4033_;
goto v_reusejp_3977_;
}
v_reusejp_3977_:
{
lean_object* v_preDef_3980_; lean_object* v___y_3981_; lean_object* v___y_3982_; lean_object* v___y_3983_; lean_object* v___y_3984_; lean_object* v___y_3985_; lean_object* v___y_3986_; uint8_t v___x_3999_; 
v___x_3999_ = l_Lean_Elab_DefKind_isTheorem(v_kind_3972_);
if (v___x_3999_ == 0)
{
lean_object* v___x_4000_; 
lean_inc_ref(v_type_3973_);
v___x_4000_ = l_Lean_Meta_isProp(v_type_3973_, v___y_3956_, v___y_3957_, v___y_3958_, v___y_3959_);
if (lean_obj_tag(v___x_4000_) == 0)
{
lean_object* v_a_4001_; uint8_t v___x_4002_; 
v_a_4001_ = lean_ctor_get(v___x_4000_, 0);
lean_inc(v_a_4001_);
lean_dec_ref(v___x_4000_);
v___x_4002_ = lean_unbox(v_a_4001_);
lean_dec(v_a_4001_);
if (v___x_4002_ == 0)
{
lean_object* v___x_4003_; 
lean_inc(v_a_3971_);
v___x_4003_ = l_Lean_Elab_abstractNestedProofs(v_a_3971_, v___x_3966_, v___y_3956_, v___y_3957_, v___y_3958_, v___y_3959_);
if (lean_obj_tag(v___x_4003_) == 0)
{
lean_object* v_a_4004_; size_t v_sz_4005_; size_t v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; 
v_a_4004_ = lean_ctor_get(v___x_4003_, 0);
lean_inc_n(v_a_4004_, 2);
lean_dec_ref(v___x_4003_);
v_sz_4005_ = lean_array_size(v_a_3948_);
v___x_4006_ = ((size_t)0ULL);
lean_inc_ref(v_a_3948_);
v___x_4007_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0(v_sz_4005_, v___x_4006_, v_a_3948_);
lean_inc_ref(v_snd_3949_);
lean_inc(v___x_3974_);
v___x_4008_ = l_Lean_Elab_Structural_registerEqnsInfo(v_a_4004_, v___x_4007_, v___x_3974_, v_snd_3949_, v___y_3958_, v___y_3959_);
if (lean_obj_tag(v___x_4008_) == 0)
{
lean_dec_ref(v___x_4008_);
v_preDef_3980_ = v_a_4004_;
v___y_3981_ = v___y_3954_;
v___y_3982_ = v___y_3955_;
v___y_3983_ = v___y_3956_;
v___y_3984_ = v___y_3957_;
v___y_3985_ = v___y_3958_;
v___y_3986_ = v___y_3959_;
goto v___jp_3979_;
}
else
{
lean_object* v_a_4009_; lean_object* v___x_4011_; uint8_t v_isShared_4012_; uint8_t v_isSharedCheck_4016_; 
lean_dec(v_a_4004_);
lean_dec_ref(v___x_3978_);
lean_dec(v___x_3974_);
lean_dec_ref(v_snd_3949_);
lean_dec_ref(v_a_3948_);
lean_dec_ref(v_docCtx_3947_);
v_a_4009_ = lean_ctor_get(v___x_4008_, 0);
v_isSharedCheck_4016_ = !lean_is_exclusive(v___x_4008_);
if (v_isSharedCheck_4016_ == 0)
{
v___x_4011_ = v___x_4008_;
v_isShared_4012_ = v_isSharedCheck_4016_;
goto v_resetjp_4010_;
}
else
{
lean_inc(v_a_4009_);
lean_dec(v___x_4008_);
v___x_4011_ = lean_box(0);
v_isShared_4012_ = v_isSharedCheck_4016_;
goto v_resetjp_4010_;
}
v_resetjp_4010_:
{
lean_object* v___x_4014_; 
if (v_isShared_4012_ == 0)
{
v___x_4014_ = v___x_4011_;
goto v_reusejp_4013_;
}
else
{
lean_object* v_reuseFailAlloc_4015_; 
v_reuseFailAlloc_4015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4015_, 0, v_a_4009_);
v___x_4014_ = v_reuseFailAlloc_4015_;
goto v_reusejp_4013_;
}
v_reusejp_4013_:
{
return v___x_4014_;
}
}
}
}
else
{
lean_object* v_a_4017_; lean_object* v___x_4019_; uint8_t v_isShared_4020_; uint8_t v_isSharedCheck_4024_; 
lean_dec_ref(v___x_3978_);
lean_dec(v___x_3974_);
lean_dec_ref(v_snd_3949_);
lean_dec_ref(v_a_3948_);
lean_dec_ref(v_docCtx_3947_);
v_a_4017_ = lean_ctor_get(v___x_4003_, 0);
v_isSharedCheck_4024_ = !lean_is_exclusive(v___x_4003_);
if (v_isSharedCheck_4024_ == 0)
{
v___x_4019_ = v___x_4003_;
v_isShared_4020_ = v_isSharedCheck_4024_;
goto v_resetjp_4018_;
}
else
{
lean_inc(v_a_4017_);
lean_dec(v___x_4003_);
v___x_4019_ = lean_box(0);
v_isShared_4020_ = v_isSharedCheck_4024_;
goto v_resetjp_4018_;
}
v_resetjp_4018_:
{
lean_object* v___x_4022_; 
if (v_isShared_4020_ == 0)
{
v___x_4022_ = v___x_4019_;
goto v_reusejp_4021_;
}
else
{
lean_object* v_reuseFailAlloc_4023_; 
v_reuseFailAlloc_4023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4023_, 0, v_a_4017_);
v___x_4022_ = v_reuseFailAlloc_4023_;
goto v_reusejp_4021_;
}
v_reusejp_4021_:
{
return v___x_4022_;
}
}
}
}
else
{
lean_inc(v_a_3971_);
v_preDef_3980_ = v_a_3971_;
v___y_3981_ = v___y_3954_;
v___y_3982_ = v___y_3955_;
v___y_3983_ = v___y_3956_;
v___y_3984_ = v___y_3957_;
v___y_3985_ = v___y_3958_;
v___y_3986_ = v___y_3959_;
goto v___jp_3979_;
}
}
else
{
lean_object* v_a_4025_; lean_object* v___x_4027_; uint8_t v_isShared_4028_; uint8_t v_isSharedCheck_4032_; 
lean_dec_ref(v___x_3978_);
lean_dec(v___x_3974_);
lean_dec_ref(v_snd_3949_);
lean_dec_ref(v_a_3948_);
lean_dec_ref(v_docCtx_3947_);
v_a_4025_ = lean_ctor_get(v___x_4000_, 0);
v_isSharedCheck_4032_ = !lean_is_exclusive(v___x_4000_);
if (v_isSharedCheck_4032_ == 0)
{
v___x_4027_ = v___x_4000_;
v_isShared_4028_ = v_isSharedCheck_4032_;
goto v_resetjp_4026_;
}
else
{
lean_inc(v_a_4025_);
lean_dec(v___x_4000_);
v___x_4027_ = lean_box(0);
v_isShared_4028_ = v_isSharedCheck_4032_;
goto v_resetjp_4026_;
}
v_resetjp_4026_:
{
lean_object* v___x_4030_; 
if (v_isShared_4028_ == 0)
{
v___x_4030_ = v___x_4027_;
goto v_reusejp_4029_;
}
else
{
lean_object* v_reuseFailAlloc_4031_; 
v_reuseFailAlloc_4031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4031_, 0, v_a_4025_);
v___x_4030_ = v_reuseFailAlloc_4031_;
goto v_reusejp_4029_;
}
v_reusejp_4029_:
{
return v___x_4030_;
}
}
}
}
else
{
lean_inc(v_a_3971_);
v_preDef_3980_ = v_a_3971_;
v___y_3981_ = v___y_3954_;
v___y_3982_ = v___y_3955_;
v___y_3983_ = v___y_3956_;
v___y_3984_ = v___y_3957_;
v___y_3985_ = v___y_3958_;
v___y_3986_ = v___y_3959_;
goto v___jp_3979_;
}
v___jp_3979_:
{
lean_object* v___x_3987_; 
lean_inc_ref(v_docCtx_3947_);
v___x_3987_ = l_Lean_Elab_Structural_addSmartUnfoldingDef(v_docCtx_3947_, v_preDef_3980_, v___x_3974_, v___y_3981_, v___y_3982_, v___y_3983_, v___y_3984_, v___y_3985_, v___y_3986_);
if (lean_obj_tag(v___x_3987_) == 0)
{
size_t v___x_3988_; size_t v___x_3989_; 
lean_dec_ref(v___x_3987_);
v___x_3988_ = ((size_t)1ULL);
v___x_3989_ = lean_usize_add(v_i_3952_, v___x_3988_);
v_i_3952_ = v___x_3989_;
v_b_3953_ = v___x_3978_;
goto _start;
}
else
{
lean_object* v_a_3991_; lean_object* v___x_3993_; uint8_t v_isShared_3994_; uint8_t v_isSharedCheck_3998_; 
lean_dec_ref(v___x_3978_);
lean_dec_ref(v_snd_3949_);
lean_dec_ref(v_a_3948_);
lean_dec_ref(v_docCtx_3947_);
v_a_3991_ = lean_ctor_get(v___x_3987_, 0);
v_isSharedCheck_3998_ = !lean_is_exclusive(v___x_3987_);
if (v_isSharedCheck_3998_ == 0)
{
v___x_3993_ = v___x_3987_;
v_isShared_3994_ = v_isSharedCheck_3998_;
goto v_resetjp_3992_;
}
else
{
lean_inc(v_a_3991_);
lean_dec(v___x_3987_);
v___x_3993_ = lean_box(0);
v_isShared_3994_ = v_isSharedCheck_3998_;
goto v_resetjp_3992_;
}
v_resetjp_3992_:
{
lean_object* v___x_3996_; 
if (v_isShared_3994_ == 0)
{
v___x_3996_ = v___x_3993_;
goto v_reusejp_3995_;
}
else
{
lean_object* v_reuseFailAlloc_3997_; 
v_reuseFailAlloc_3997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3997_, 0, v_a_3991_);
v___x_3996_ = v_reuseFailAlloc_3997_;
goto v_reusejp_3995_;
}
v_reusejp_3995_:
{
return v___x_3996_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__1___boxed(lean_object* v_docCtx_4038_, lean_object* v_a_4039_, lean_object* v_snd_4040_, lean_object* v_as_4041_, lean_object* v_sz_4042_, lean_object* v_i_4043_, lean_object* v_b_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_){
_start:
{
size_t v_sz_boxed_4052_; size_t v_i_boxed_4053_; lean_object* v_res_4054_; 
v_sz_boxed_4052_ = lean_unbox_usize(v_sz_4042_);
lean_dec(v_sz_4042_);
v_i_boxed_4053_ = lean_unbox_usize(v_i_4043_);
lean_dec(v_i_4043_);
v_res_4054_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__1(v_docCtx_4038_, v_a_4039_, v_snd_4040_, v_as_4041_, v_sz_boxed_4052_, v_i_boxed_4053_, v_b_4044_, v___y_4045_, v___y_4046_, v___y_4047_, v___y_4048_, v___y_4049_, v___y_4050_);
lean_dec(v___y_4050_);
lean_dec_ref(v___y_4049_);
lean_dec(v___y_4048_);
lean_dec_ref(v___y_4047_);
lean_dec(v___y_4046_);
lean_dec_ref(v___y_4045_);
lean_dec_ref(v_as_4041_);
return v_res_4054_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___lam__0(lean_object* v___x_4055_, lean_object* v_e_4056_){
_start:
{
lean_object* v___x_4057_; lean_object* v___x_4058_; 
v___x_4057_ = l_Lean_indentD(v_e_4056_);
v___x_4058_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4058_, 0, v___x_4055_);
lean_ctor_set(v___x_4058_, 1, v___x_4057_);
return v___x_4058_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___lam__1(lean_object* v_docCtx_4059_, lean_object* v_a_4060_, uint8_t v___x_4061_, lean_object* v___x_4062_, uint8_t v___x_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_){
_start:
{
lean_object* v___x_4071_; 
v___x_4071_ = l_Lean_Elab_addNonRec(v_docCtx_4059_, v_a_4060_, v___x_4061_, v___x_4062_, v___x_4063_, v___x_4061_, v___x_4063_, v___y_4064_, v___y_4065_, v___y_4066_, v___y_4067_, v___y_4068_, v___y_4069_);
return v___x_4071_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___lam__1___boxed(lean_object* v_docCtx_4072_, lean_object* v_a_4073_, lean_object* v___x_4074_, lean_object* v___x_4075_, lean_object* v___x_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_){
_start:
{
uint8_t v___x_9560__boxed_4084_; uint8_t v___x_9562__boxed_4085_; lean_object* v_res_4086_; 
v___x_9560__boxed_4084_ = lean_unbox(v___x_4074_);
v___x_9562__boxed_4085_ = lean_unbox(v___x_4076_);
v_res_4086_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___lam__1(v_docCtx_4072_, v_a_4073_, v___x_9560__boxed_4084_, v___x_4075_, v___x_9562__boxed_4085_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_, v___y_4081_, v___y_4082_);
lean_dec(v___y_4082_);
lean_dec_ref(v___y_4081_);
lean_dec(v___y_4080_);
lean_dec_ref(v___y_4079_);
lean_dec(v___y_4078_);
lean_dec_ref(v___y_4077_);
return v_res_4086_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__1(void){
_start:
{
lean_object* v___x_4088_; lean_object* v___x_4089_; 
v___x_4088_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__0));
v___x_4089_ = l_Lean_stringToMessageData(v___x_4088_);
return v___x_4089_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__2(void){
_start:
{
lean_object* v___x_4090_; lean_object* v___f_4091_; 
v___x_4090_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__1);
v___f_4091_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___lam__0), 2, 1);
lean_closure_set(v___f_4091_, 0, v___x_4090_);
return v___f_4091_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5(lean_object* v_names_4092_, lean_object* v_docCtx_4093_, lean_object* v_as_4094_, size_t v_i_4095_, size_t v_stop_4096_, lean_object* v_b_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_){
_start:
{
uint8_t v___x_4105_; 
v___x_4105_ = lean_usize_dec_eq(v_i_4095_, v_stop_4096_);
if (v___x_4105_ == 0)
{
lean_object* v___x_4106_; lean_object* v___x_4107_; 
v___x_4106_ = lean_array_uget_borrowed(v_as_4094_, v_i_4095_);
lean_inc(v___x_4106_);
v___x_4107_ = l_Lean_Elab_eraseRecAppSyntax(v___x_4106_, v___y_4102_, v___y_4103_);
if (lean_obj_tag(v___x_4107_) == 0)
{
lean_object* v_a_4108_; lean_object* v___f_4109_; lean_object* v___x_4110_; uint8_t v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___f_4114_; lean_object* v___x_4115_; 
v_a_4108_ = lean_ctor_get(v___x_4107_, 0);
lean_inc(v_a_4108_);
lean_dec_ref(v___x_4107_);
v___f_4109_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__2);
lean_inc_ref(v_names_4092_);
v___x_4110_ = lean_array_to_list(v_names_4092_);
v___x_4111_ = 1;
v___x_4112_ = lean_box(v___x_4105_);
v___x_4113_ = lean_box(v___x_4111_);
lean_inc(v___y_4099_);
lean_inc_ref(v___y_4098_);
lean_inc_ref(v_docCtx_4093_);
v___f_4114_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___lam__1___boxed), 12, 7);
lean_closure_set(v___f_4114_, 0, v_docCtx_4093_);
lean_closure_set(v___f_4114_, 1, v_a_4108_);
lean_closure_set(v___f_4114_, 2, v___x_4112_);
lean_closure_set(v___f_4114_, 3, v___x_4110_);
lean_closure_set(v___f_4114_, 4, v___x_4113_);
lean_closure_set(v___f_4114_, 5, v___y_4098_);
lean_closure_set(v___f_4114_, 6, v___y_4099_);
v___x_4115_ = l_Lean_Meta_mapErrorImp___redArg(v___f_4114_, v___f_4109_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_);
if (lean_obj_tag(v___x_4115_) == 0)
{
if (lean_obj_tag(v___x_4115_) == 0)
{
lean_object* v_a_4116_; size_t v___x_4117_; size_t v___x_4118_; 
v_a_4116_ = lean_ctor_get(v___x_4115_, 0);
lean_inc(v_a_4116_);
lean_dec_ref(v___x_4115_);
v___x_4117_ = ((size_t)1ULL);
v___x_4118_ = lean_usize_add(v_i_4095_, v___x_4117_);
v_i_4095_ = v___x_4118_;
v_b_4097_ = v_a_4116_;
goto _start;
}
else
{
lean_dec_ref(v_docCtx_4093_);
lean_dec_ref(v_names_4092_);
return v___x_4115_;
}
}
else
{
lean_object* v_a_4120_; lean_object* v___x_4122_; uint8_t v_isShared_4123_; uint8_t v_isSharedCheck_4127_; 
lean_dec_ref(v_docCtx_4093_);
lean_dec_ref(v_names_4092_);
v_a_4120_ = lean_ctor_get(v___x_4115_, 0);
v_isSharedCheck_4127_ = !lean_is_exclusive(v___x_4115_);
if (v_isSharedCheck_4127_ == 0)
{
v___x_4122_ = v___x_4115_;
v_isShared_4123_ = v_isSharedCheck_4127_;
goto v_resetjp_4121_;
}
else
{
lean_inc(v_a_4120_);
lean_dec(v___x_4115_);
v___x_4122_ = lean_box(0);
v_isShared_4123_ = v_isSharedCheck_4127_;
goto v_resetjp_4121_;
}
v_resetjp_4121_:
{
lean_object* v___x_4125_; 
if (v_isShared_4123_ == 0)
{
v___x_4125_ = v___x_4122_;
goto v_reusejp_4124_;
}
else
{
lean_object* v_reuseFailAlloc_4126_; 
v_reuseFailAlloc_4126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4126_, 0, v_a_4120_);
v___x_4125_ = v_reuseFailAlloc_4126_;
goto v_reusejp_4124_;
}
v_reusejp_4124_:
{
return v___x_4125_;
}
}
}
}
else
{
lean_object* v_a_4128_; lean_object* v___x_4130_; uint8_t v_isShared_4131_; uint8_t v_isSharedCheck_4135_; 
lean_dec_ref(v_docCtx_4093_);
lean_dec_ref(v_names_4092_);
v_a_4128_ = lean_ctor_get(v___x_4107_, 0);
v_isSharedCheck_4135_ = !lean_is_exclusive(v___x_4107_);
if (v_isSharedCheck_4135_ == 0)
{
v___x_4130_ = v___x_4107_;
v_isShared_4131_ = v_isSharedCheck_4135_;
goto v_resetjp_4129_;
}
else
{
lean_inc(v_a_4128_);
lean_dec(v___x_4107_);
v___x_4130_ = lean_box(0);
v_isShared_4131_ = v_isSharedCheck_4135_;
goto v_resetjp_4129_;
}
v_resetjp_4129_:
{
lean_object* v___x_4133_; 
if (v_isShared_4131_ == 0)
{
v___x_4133_ = v___x_4130_;
goto v_reusejp_4132_;
}
else
{
lean_object* v_reuseFailAlloc_4134_; 
v_reuseFailAlloc_4134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4134_, 0, v_a_4128_);
v___x_4133_ = v_reuseFailAlloc_4134_;
goto v_reusejp_4132_;
}
v_reusejp_4132_:
{
return v___x_4133_;
}
}
}
}
else
{
lean_object* v___x_4136_; 
lean_dec_ref(v_docCtx_4093_);
lean_dec_ref(v_names_4092_);
v___x_4136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4136_, 0, v_b_4097_);
return v___x_4136_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___boxed(lean_object* v_names_4137_, lean_object* v_docCtx_4138_, lean_object* v_as_4139_, lean_object* v_i_4140_, lean_object* v_stop_4141_, lean_object* v_b_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_){
_start:
{
size_t v_i_boxed_4150_; size_t v_stop_boxed_4151_; lean_object* v_res_4152_; 
v_i_boxed_4150_ = lean_unbox_usize(v_i_4140_);
lean_dec(v_i_4140_);
v_stop_boxed_4151_ = lean_unbox_usize(v_stop_4141_);
lean_dec(v_stop_4141_);
v_res_4152_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5(v_names_4137_, v_docCtx_4138_, v_as_4139_, v_i_boxed_4150_, v_stop_boxed_4151_, v_b_4142_, v___y_4143_, v___y_4144_, v___y_4145_, v___y_4146_, v___y_4147_, v___y_4148_);
lean_dec(v___y_4148_);
lean_dec_ref(v___y_4147_);
lean_dec(v___y_4146_);
lean_dec_ref(v___y_4145_);
lean_dec(v___y_4144_);
lean_dec_ref(v___y_4143_);
lean_dec_ref(v_as_4139_);
return v_res_4152_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4___redArg(lean_object* v_as_4153_, size_t v_sz_4154_, size_t v_i_4155_, lean_object* v_b_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_, lean_object* v___y_4160_){
_start:
{
uint8_t v___x_4162_; 
v___x_4162_ = lean_usize_dec_lt(v_i_4155_, v_sz_4154_);
if (v___x_4162_ == 0)
{
lean_object* v___x_4163_; 
v___x_4163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4163_, 0, v_b_4156_);
return v___x_4163_;
}
else
{
lean_object* v_array_4164_; lean_object* v_start_4165_; lean_object* v_stop_4166_; uint8_t v___x_4167_; 
v_array_4164_ = lean_ctor_get(v_b_4156_, 0);
v_start_4165_ = lean_ctor_get(v_b_4156_, 1);
v_stop_4166_ = lean_ctor_get(v_b_4156_, 2);
v___x_4167_ = lean_nat_dec_lt(v_start_4165_, v_stop_4166_);
if (v___x_4167_ == 0)
{
lean_object* v___x_4168_; 
v___x_4168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4168_, 0, v_b_4156_);
return v___x_4168_;
}
else
{
lean_object* v___x_4170_; uint8_t v_isShared_4171_; uint8_t v_isSharedCheck_4191_; 
lean_inc(v_stop_4166_);
lean_inc(v_start_4165_);
lean_inc_ref(v_array_4164_);
v_isSharedCheck_4191_ = !lean_is_exclusive(v_b_4156_);
if (v_isSharedCheck_4191_ == 0)
{
lean_object* v_unused_4192_; lean_object* v_unused_4193_; lean_object* v_unused_4194_; 
v_unused_4192_ = lean_ctor_get(v_b_4156_, 2);
lean_dec(v_unused_4192_);
v_unused_4193_ = lean_ctor_get(v_b_4156_, 1);
lean_dec(v_unused_4193_);
v_unused_4194_ = lean_ctor_get(v_b_4156_, 0);
lean_dec(v_unused_4194_);
v___x_4170_ = v_b_4156_;
v_isShared_4171_ = v_isSharedCheck_4191_;
goto v_resetjp_4169_;
}
else
{
lean_dec(v_b_4156_);
v___x_4170_ = lean_box(0);
v_isShared_4171_ = v_isSharedCheck_4191_;
goto v_resetjp_4169_;
}
v_resetjp_4169_:
{
lean_object* v_a_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; 
v_a_4172_ = lean_array_uget_borrowed(v_as_4153_, v_i_4155_);
v___x_4173_ = lean_array_fget_borrowed(v_array_4164_, v_start_4165_);
lean_inc(v_a_4172_);
lean_inc(v___x_4173_);
v___x_4174_ = l_Lean_Elab_Structural_reportTermMeasure(v___x_4173_, v_a_4172_, v___y_4157_, v___y_4158_, v___y_4159_, v___y_4160_);
if (lean_obj_tag(v___x_4174_) == 0)
{
lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4178_; 
lean_dec_ref(v___x_4174_);
v___x_4175_ = lean_unsigned_to_nat(1u);
v___x_4176_ = lean_nat_add(v_start_4165_, v___x_4175_);
lean_dec(v_start_4165_);
if (v_isShared_4171_ == 0)
{
lean_ctor_set(v___x_4170_, 1, v___x_4176_);
v___x_4178_ = v___x_4170_;
goto v_reusejp_4177_;
}
else
{
lean_object* v_reuseFailAlloc_4182_; 
v_reuseFailAlloc_4182_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4182_, 0, v_array_4164_);
lean_ctor_set(v_reuseFailAlloc_4182_, 1, v___x_4176_);
lean_ctor_set(v_reuseFailAlloc_4182_, 2, v_stop_4166_);
v___x_4178_ = v_reuseFailAlloc_4182_;
goto v_reusejp_4177_;
}
v_reusejp_4177_:
{
size_t v___x_4179_; size_t v___x_4180_; 
v___x_4179_ = ((size_t)1ULL);
v___x_4180_ = lean_usize_add(v_i_4155_, v___x_4179_);
v_i_4155_ = v___x_4180_;
v_b_4156_ = v___x_4178_;
goto _start;
}
}
else
{
lean_object* v_a_4183_; lean_object* v___x_4185_; uint8_t v_isShared_4186_; uint8_t v_isSharedCheck_4190_; 
lean_del_object(v___x_4170_);
lean_dec(v_stop_4166_);
lean_dec(v_start_4165_);
lean_dec_ref(v_array_4164_);
v_a_4183_ = lean_ctor_get(v___x_4174_, 0);
v_isSharedCheck_4190_ = !lean_is_exclusive(v___x_4174_);
if (v_isSharedCheck_4190_ == 0)
{
v___x_4185_ = v___x_4174_;
v_isShared_4186_ = v_isSharedCheck_4190_;
goto v_resetjp_4184_;
}
else
{
lean_inc(v_a_4183_);
lean_dec(v___x_4174_);
v___x_4185_ = lean_box(0);
v_isShared_4186_ = v_isSharedCheck_4190_;
goto v_resetjp_4184_;
}
v_resetjp_4184_:
{
lean_object* v___x_4188_; 
if (v_isShared_4186_ == 0)
{
v___x_4188_ = v___x_4185_;
goto v_reusejp_4187_;
}
else
{
lean_object* v_reuseFailAlloc_4189_; 
v_reuseFailAlloc_4189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4189_, 0, v_a_4183_);
v___x_4188_ = v_reuseFailAlloc_4189_;
goto v_reusejp_4187_;
}
v_reusejp_4187_:
{
return v___x_4188_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4___redArg___boxed(lean_object* v_as_4195_, lean_object* v_sz_4196_, lean_object* v_i_4197_, lean_object* v_b_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_){
_start:
{
size_t v_sz_boxed_4204_; size_t v_i_boxed_4205_; lean_object* v_res_4206_; 
v_sz_boxed_4204_ = lean_unbox_usize(v_sz_4196_);
lean_dec(v_sz_4196_);
v_i_boxed_4205_ = lean_unbox_usize(v_i_4197_);
lean_dec(v_i_4197_);
v_res_4206_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4___redArg(v_as_4195_, v_sz_boxed_4204_, v_i_boxed_4205_, v_b_4198_, v___y_4199_, v___y_4200_, v___y_4201_, v___y_4202_);
lean_dec(v___y_4202_);
lean_dec_ref(v___y_4201_);
lean_dec(v___y_4200_);
lean_dec_ref(v___y_4199_);
lean_dec_ref(v_as_4195_);
return v_res_4206_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___redArg(size_t v_sz_4207_, size_t v_i_4208_, lean_object* v_bs_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_){
_start:
{
uint8_t v___x_4213_; 
v___x_4213_ = lean_usize_dec_lt(v_i_4208_, v_sz_4207_);
if (v___x_4213_ == 0)
{
lean_object* v___x_4214_; 
v___x_4214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4214_, 0, v_bs_4209_);
return v___x_4214_;
}
else
{
lean_object* v_v_4215_; lean_object* v___x_4216_; 
v_v_4215_ = lean_array_uget_borrowed(v_bs_4209_, v_i_4208_);
lean_inc(v_v_4215_);
v___x_4216_ = l_Lean_Elab_eraseRecAppSyntax(v_v_4215_, v___y_4210_, v___y_4211_);
if (lean_obj_tag(v___x_4216_) == 0)
{
lean_object* v_a_4217_; lean_object* v___x_4218_; lean_object* v_bs_x27_4219_; size_t v___x_4220_; size_t v___x_4221_; lean_object* v___x_4222_; 
v_a_4217_ = lean_ctor_get(v___x_4216_, 0);
lean_inc(v_a_4217_);
lean_dec_ref(v___x_4216_);
v___x_4218_ = lean_unsigned_to_nat(0u);
v_bs_x27_4219_ = lean_array_uset(v_bs_4209_, v_i_4208_, v___x_4218_);
v___x_4220_ = ((size_t)1ULL);
v___x_4221_ = lean_usize_add(v_i_4208_, v___x_4220_);
v___x_4222_ = lean_array_uset(v_bs_x27_4219_, v_i_4208_, v_a_4217_);
v_i_4208_ = v___x_4221_;
v_bs_4209_ = v___x_4222_;
goto _start;
}
else
{
lean_object* v_a_4224_; lean_object* v___x_4226_; uint8_t v_isShared_4227_; uint8_t v_isSharedCheck_4231_; 
lean_dec_ref(v_bs_4209_);
v_a_4224_ = lean_ctor_get(v___x_4216_, 0);
v_isSharedCheck_4231_ = !lean_is_exclusive(v___x_4216_);
if (v_isSharedCheck_4231_ == 0)
{
v___x_4226_ = v___x_4216_;
v_isShared_4227_ = v_isSharedCheck_4231_;
goto v_resetjp_4225_;
}
else
{
lean_inc(v_a_4224_);
lean_dec(v___x_4216_);
v___x_4226_ = lean_box(0);
v_isShared_4227_ = v_isSharedCheck_4231_;
goto v_resetjp_4225_;
}
v_resetjp_4225_:
{
lean_object* v___x_4229_; 
if (v_isShared_4227_ == 0)
{
v___x_4229_ = v___x_4226_;
goto v_reusejp_4228_;
}
else
{
lean_object* v_reuseFailAlloc_4230_; 
v_reuseFailAlloc_4230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4230_, 0, v_a_4224_);
v___x_4229_ = v_reuseFailAlloc_4230_;
goto v_reusejp_4228_;
}
v_reusejp_4228_:
{
return v___x_4229_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___redArg___boxed(lean_object* v_sz_4232_, lean_object* v_i_4233_, lean_object* v_bs_4234_, lean_object* v___y_4235_, lean_object* v___y_4236_, lean_object* v___y_4237_){
_start:
{
size_t v_sz_boxed_4238_; size_t v_i_boxed_4239_; lean_object* v_res_4240_; 
v_sz_boxed_4238_ = lean_unbox_usize(v_sz_4232_);
lean_dec(v_sz_4232_);
v_i_boxed_4239_ = lean_unbox_usize(v_i_4233_);
lean_dec(v_i_4233_);
v_res_4240_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___redArg(v_sz_boxed_4238_, v_i_boxed_4239_, v_bs_4234_, v___y_4235_, v___y_4236_);
lean_dec(v___y_4236_);
lean_dec_ref(v___y_4235_);
return v_res_4240_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___redArg(lean_object* v_as_4241_, size_t v_sz_4242_, size_t v_i_4243_, lean_object* v_b_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_){
_start:
{
uint8_t v___x_4248_; 
v___x_4248_ = lean_usize_dec_lt(v_i_4243_, v_sz_4242_);
if (v___x_4248_ == 0)
{
lean_object* v___x_4249_; 
v___x_4249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4249_, 0, v_b_4244_);
return v___x_4249_;
}
else
{
lean_object* v_a_4250_; lean_object* v_declName_4251_; lean_object* v___x_4252_; 
v_a_4250_ = lean_array_uget_borrowed(v_as_4241_, v_i_4243_);
v_declName_4251_ = lean_ctor_get(v_a_4250_, 3);
lean_inc(v_declName_4251_);
v___x_4252_ = l_Lean_enableRealizationsForConst(v_declName_4251_, v___y_4245_, v___y_4246_);
if (lean_obj_tag(v___x_4252_) == 0)
{
lean_object* v___x_4253_; size_t v___x_4254_; size_t v___x_4255_; 
lean_dec_ref(v___x_4252_);
v___x_4253_ = lean_box(0);
v___x_4254_ = ((size_t)1ULL);
v___x_4255_ = lean_usize_add(v_i_4243_, v___x_4254_);
v_i_4243_ = v___x_4255_;
v_b_4244_ = v___x_4253_;
goto _start;
}
else
{
return v___x_4252_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___redArg___boxed(lean_object* v_as_4257_, lean_object* v_sz_4258_, lean_object* v_i_4259_, lean_object* v_b_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_){
_start:
{
size_t v_sz_boxed_4264_; size_t v_i_boxed_4265_; lean_object* v_res_4266_; 
v_sz_boxed_4264_ = lean_unbox_usize(v_sz_4258_);
lean_dec(v_sz_4258_);
v_i_boxed_4265_ = lean_unbox_usize(v_i_4259_);
lean_dec(v_i_4259_);
v_res_4266_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___redArg(v_as_4257_, v_sz_boxed_4264_, v_i_boxed_4265_, v_b_4260_, v___y_4261_, v___y_4262_);
lean_dec(v___y_4262_);
lean_dec_ref(v___y_4261_);
lean_dec_ref(v_as_4257_);
return v_res_4266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_structuralRecursion(lean_object* v_docCtx_4267_, lean_object* v_preDefs_4268_, lean_object* v_termMeasure_x3fs_4269_, lean_object* v_a_4270_, lean_object* v_a_4271_, lean_object* v_a_4272_, lean_object* v_a_4273_, lean_object* v_a_4274_, lean_object* v_a_4275_){
_start:
{
size_t v_sz_4277_; size_t v___x_4278_; lean_object* v_names_4279_; lean_object* v___x_4280_; 
v_sz_4277_ = lean_array_size(v_preDefs_4268_);
v___x_4278_ = ((size_t)0ULL);
lean_inc_ref_n(v_preDefs_4268_, 2);
v_names_4279_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0(v_sz_4277_, v___x_4278_, v_preDefs_4268_);
v___x_4280_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos(v_preDefs_4268_, v_termMeasure_x3fs_4269_, v_a_4272_, v_a_4273_, v_a_4274_, v_a_4275_);
if (lean_obj_tag(v___x_4280_) == 0)
{
lean_object* v_a_4281_; lean_object* v_snd_4282_; lean_object* v_fst_4283_; lean_object* v_fst_4284_; lean_object* v_snd_4285_; lean_object* v___y_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; size_t v_sz_4321_; lean_object* v___x_4322_; 
v_a_4281_ = lean_ctor_get(v___x_4280_, 0);
lean_inc(v_a_4281_);
lean_dec_ref(v___x_4280_);
v_snd_4282_ = lean_ctor_get(v_a_4281_, 1);
lean_inc(v_snd_4282_);
v_fst_4283_ = lean_ctor_get(v_a_4281_, 0);
lean_inc(v_fst_4283_);
lean_dec(v_a_4281_);
v_fst_4284_ = lean_ctor_get(v_snd_4282_, 0);
lean_inc(v_fst_4284_);
v_snd_4285_ = lean_ctor_get(v_snd_4282_, 1);
lean_inc(v_snd_4285_);
lean_dec(v_snd_4282_);
v___x_4318_ = lean_unsigned_to_nat(0u);
v___x_4319_ = lean_array_get_size(v_preDefs_4268_);
lean_inc_ref(v_preDefs_4268_);
v___x_4320_ = l_Array_toSubarray___redArg(v_preDefs_4268_, v___x_4318_, v___x_4319_);
v_sz_4321_ = lean_array_size(v_fst_4283_);
v___x_4322_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4___redArg(v_fst_4283_, v_sz_4321_, v___x_4278_, v___x_4320_, v_a_4272_, v_a_4273_, v_a_4274_, v_a_4275_);
if (lean_obj_tag(v___x_4322_) == 0)
{
lean_object* v___x_4323_; uint8_t v___x_4324_; 
lean_dec_ref(v___x_4322_);
v___x_4323_ = lean_array_get_size(v_fst_4284_);
v___x_4324_ = lean_nat_dec_lt(v___x_4318_, v___x_4323_);
if (v___x_4324_ == 0)
{
lean_dec_ref(v_names_4279_);
goto v___jp_4286_;
}
else
{
lean_object* v___x_4325_; uint8_t v___x_4326_; 
v___x_4325_ = lean_box(0);
v___x_4326_ = lean_nat_dec_le(v___x_4323_, v___x_4323_);
if (v___x_4326_ == 0)
{
if (v___x_4324_ == 0)
{
lean_dec_ref(v_names_4279_);
goto v___jp_4286_;
}
else
{
size_t v___x_4327_; lean_object* v___x_4328_; 
v___x_4327_ = lean_usize_of_nat(v___x_4323_);
lean_inc_ref(v_docCtx_4267_);
v___x_4328_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5(v_names_4279_, v_docCtx_4267_, v_fst_4284_, v___x_4278_, v___x_4327_, v___x_4325_, v_a_4270_, v_a_4271_, v_a_4272_, v_a_4273_, v_a_4274_, v_a_4275_);
v___y_4317_ = v___x_4328_;
goto v___jp_4316_;
}
}
else
{
size_t v___x_4329_; lean_object* v___x_4330_; 
v___x_4329_ = lean_usize_of_nat(v___x_4323_);
lean_inc_ref(v_docCtx_4267_);
v___x_4330_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5(v_names_4279_, v_docCtx_4267_, v_fst_4284_, v___x_4278_, v___x_4329_, v___x_4325_, v_a_4270_, v_a_4271_, v_a_4272_, v_a_4273_, v_a_4274_, v_a_4275_);
v___y_4317_ = v___x_4330_;
goto v___jp_4316_;
}
}
}
else
{
lean_object* v_a_4331_; lean_object* v___x_4333_; uint8_t v_isShared_4334_; uint8_t v_isSharedCheck_4338_; 
lean_dec(v_snd_4285_);
lean_dec(v_fst_4284_);
lean_dec(v_fst_4283_);
lean_dec_ref(v_names_4279_);
lean_dec_ref(v_preDefs_4268_);
lean_dec_ref(v_docCtx_4267_);
v_a_4331_ = lean_ctor_get(v___x_4322_, 0);
v_isSharedCheck_4338_ = !lean_is_exclusive(v___x_4322_);
if (v_isSharedCheck_4338_ == 0)
{
v___x_4333_ = v___x_4322_;
v_isShared_4334_ = v_isSharedCheck_4338_;
goto v_resetjp_4332_;
}
else
{
lean_inc(v_a_4331_);
lean_dec(v___x_4322_);
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
v___jp_4286_:
{
lean_object* v___x_4287_; 
v___x_4287_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___redArg(v_sz_4277_, v___x_4278_, v_preDefs_4268_, v_a_4274_, v_a_4275_);
if (lean_obj_tag(v___x_4287_) == 0)
{
lean_object* v_a_4288_; lean_object* v___x_4289_; 
v_a_4288_ = lean_ctor_get(v___x_4287_, 0);
lean_inc_n(v_a_4288_, 2);
lean_dec_ref(v___x_4287_);
lean_inc_ref(v_docCtx_4267_);
v___x_4289_ = l_Lean_Elab_addAndCompilePartialRec(v_docCtx_4267_, v_a_4288_, v_a_4270_, v_a_4271_, v_a_4272_, v_a_4273_, v_a_4274_, v_a_4275_);
if (lean_obj_tag(v___x_4289_) == 0)
{
lean_object* v___x_4290_; lean_object* v___x_4291_; lean_object* v___x_4292_; size_t v_sz_4293_; lean_object* v___x_4294_; 
lean_dec_ref(v___x_4289_);
v___x_4290_ = lean_unsigned_to_nat(0u);
v___x_4291_ = lean_array_get_size(v_fst_4283_);
v___x_4292_ = l_Array_toSubarray___redArg(v_fst_4283_, v___x_4290_, v___x_4291_);
v_sz_4293_ = lean_array_size(v_a_4288_);
lean_inc(v_a_4288_);
v___x_4294_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__1(v_docCtx_4267_, v_a_4288_, v_snd_4285_, v_a_4288_, v_sz_4293_, v___x_4278_, v___x_4292_, v_a_4270_, v_a_4271_, v_a_4272_, v_a_4273_, v_a_4274_, v_a_4275_);
if (lean_obj_tag(v___x_4294_) == 0)
{
lean_object* v___x_4295_; lean_object* v___x_4296_; 
lean_dec_ref(v___x_4294_);
v___x_4295_ = lean_box(0);
v___x_4296_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___redArg(v_a_4288_, v_sz_4293_, v___x_4278_, v___x_4295_, v_a_4272_, v_a_4273_, v_a_4274_, v_a_4275_);
if (lean_obj_tag(v___x_4296_) == 0)
{
lean_object* v___x_4297_; 
lean_dec_ref(v___x_4296_);
v___x_4297_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___redArg(v_a_4288_, v_sz_4293_, v___x_4278_, v___x_4295_, v_a_4274_, v_a_4275_);
lean_dec(v_a_4288_);
if (lean_obj_tag(v___x_4297_) == 0)
{
uint8_t v___x_4298_; lean_object* v___x_4299_; 
lean_dec_ref(v___x_4297_);
v___x_4298_ = 1;
v___x_4299_ = l_Lean_Elab_applyAttributesOf(v_fst_4284_, v___x_4298_, v_a_4270_, v_a_4271_, v_a_4272_, v_a_4273_, v_a_4274_, v_a_4275_);
lean_dec(v_fst_4284_);
return v___x_4299_;
}
else
{
lean_dec(v_fst_4284_);
return v___x_4297_;
}
}
else
{
lean_dec(v_a_4288_);
lean_dec(v_fst_4284_);
return v___x_4296_;
}
}
else
{
lean_object* v_a_4300_; lean_object* v___x_4302_; uint8_t v_isShared_4303_; uint8_t v_isSharedCheck_4307_; 
lean_dec(v_a_4288_);
lean_dec(v_fst_4284_);
v_a_4300_ = lean_ctor_get(v___x_4294_, 0);
v_isSharedCheck_4307_ = !lean_is_exclusive(v___x_4294_);
if (v_isSharedCheck_4307_ == 0)
{
v___x_4302_ = v___x_4294_;
v_isShared_4303_ = v_isSharedCheck_4307_;
goto v_resetjp_4301_;
}
else
{
lean_inc(v_a_4300_);
lean_dec(v___x_4294_);
v___x_4302_ = lean_box(0);
v_isShared_4303_ = v_isSharedCheck_4307_;
goto v_resetjp_4301_;
}
v_resetjp_4301_:
{
lean_object* v___x_4305_; 
if (v_isShared_4303_ == 0)
{
v___x_4305_ = v___x_4302_;
goto v_reusejp_4304_;
}
else
{
lean_object* v_reuseFailAlloc_4306_; 
v_reuseFailAlloc_4306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4306_, 0, v_a_4300_);
v___x_4305_ = v_reuseFailAlloc_4306_;
goto v_reusejp_4304_;
}
v_reusejp_4304_:
{
return v___x_4305_;
}
}
}
}
else
{
lean_dec(v_a_4288_);
lean_dec(v_snd_4285_);
lean_dec(v_fst_4284_);
lean_dec(v_fst_4283_);
lean_dec_ref(v_docCtx_4267_);
return v___x_4289_;
}
}
else
{
lean_object* v_a_4308_; lean_object* v___x_4310_; uint8_t v_isShared_4311_; uint8_t v_isSharedCheck_4315_; 
lean_dec(v_snd_4285_);
lean_dec(v_fst_4284_);
lean_dec(v_fst_4283_);
lean_dec_ref(v_docCtx_4267_);
v_a_4308_ = lean_ctor_get(v___x_4287_, 0);
v_isSharedCheck_4315_ = !lean_is_exclusive(v___x_4287_);
if (v_isSharedCheck_4315_ == 0)
{
v___x_4310_ = v___x_4287_;
v_isShared_4311_ = v_isSharedCheck_4315_;
goto v_resetjp_4309_;
}
else
{
lean_inc(v_a_4308_);
lean_dec(v___x_4287_);
v___x_4310_ = lean_box(0);
v_isShared_4311_ = v_isSharedCheck_4315_;
goto v_resetjp_4309_;
}
v_resetjp_4309_:
{
lean_object* v___x_4313_; 
if (v_isShared_4311_ == 0)
{
v___x_4313_ = v___x_4310_;
goto v_reusejp_4312_;
}
else
{
lean_object* v_reuseFailAlloc_4314_; 
v_reuseFailAlloc_4314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4314_, 0, v_a_4308_);
v___x_4313_ = v_reuseFailAlloc_4314_;
goto v_reusejp_4312_;
}
v_reusejp_4312_:
{
return v___x_4313_;
}
}
}
}
v___jp_4316_:
{
if (lean_obj_tag(v___y_4317_) == 0)
{
lean_dec_ref(v___y_4317_);
goto v___jp_4286_;
}
else
{
lean_dec(v_snd_4285_);
lean_dec(v_fst_4284_);
lean_dec(v_fst_4283_);
lean_dec_ref(v_preDefs_4268_);
lean_dec_ref(v_docCtx_4267_);
return v___y_4317_;
}
}
}
else
{
lean_object* v_a_4339_; lean_object* v___x_4341_; uint8_t v_isShared_4342_; uint8_t v_isSharedCheck_4346_; 
lean_dec_ref(v_names_4279_);
lean_dec_ref(v_preDefs_4268_);
lean_dec_ref(v_docCtx_4267_);
v_a_4339_ = lean_ctor_get(v___x_4280_, 0);
v_isSharedCheck_4346_ = !lean_is_exclusive(v___x_4280_);
if (v_isSharedCheck_4346_ == 0)
{
v___x_4341_ = v___x_4280_;
v_isShared_4342_ = v_isSharedCheck_4346_;
goto v_resetjp_4340_;
}
else
{
lean_inc(v_a_4339_);
lean_dec(v___x_4280_);
v___x_4341_ = lean_box(0);
v_isShared_4342_ = v_isSharedCheck_4346_;
goto v_resetjp_4340_;
}
v_resetjp_4340_:
{
lean_object* v___x_4344_; 
if (v_isShared_4342_ == 0)
{
v___x_4344_ = v___x_4341_;
goto v_reusejp_4343_;
}
else
{
lean_object* v_reuseFailAlloc_4345_; 
v_reuseFailAlloc_4345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4345_, 0, v_a_4339_);
v___x_4344_ = v_reuseFailAlloc_4345_;
goto v_reusejp_4343_;
}
v_reusejp_4343_:
{
return v___x_4344_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_structuralRecursion___boxed(lean_object* v_docCtx_4347_, lean_object* v_preDefs_4348_, lean_object* v_termMeasure_x3fs_4349_, lean_object* v_a_4350_, lean_object* v_a_4351_, lean_object* v_a_4352_, lean_object* v_a_4353_, lean_object* v_a_4354_, lean_object* v_a_4355_, lean_object* v_a_4356_){
_start:
{
lean_object* v_res_4357_; 
v_res_4357_ = l_Lean_Elab_Structural_structuralRecursion(v_docCtx_4347_, v_preDefs_4348_, v_termMeasure_x3fs_4349_, v_a_4350_, v_a_4351_, v_a_4352_, v_a_4353_, v_a_4354_, v_a_4355_);
lean_dec(v_a_4355_);
lean_dec_ref(v_a_4354_);
lean_dec(v_a_4353_);
lean_dec_ref(v_a_4352_);
lean_dec(v_a_4351_);
lean_dec_ref(v_a_4350_);
return v_res_4357_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0(size_t v_sz_4358_, size_t v_i_4359_, lean_object* v_bs_4360_, lean_object* v___y_4361_, lean_object* v___y_4362_, lean_object* v___y_4363_, lean_object* v___y_4364_, lean_object* v___y_4365_, lean_object* v___y_4366_){
_start:
{
lean_object* v___x_4368_; 
v___x_4368_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___redArg(v_sz_4358_, v_i_4359_, v_bs_4360_, v___y_4365_, v___y_4366_);
return v___x_4368_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___boxed(lean_object* v_sz_4369_, lean_object* v_i_4370_, lean_object* v_bs_4371_, lean_object* v___y_4372_, lean_object* v___y_4373_, lean_object* v___y_4374_, lean_object* v___y_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_, lean_object* v___y_4378_){
_start:
{
size_t v_sz_boxed_4379_; size_t v_i_boxed_4380_; lean_object* v_res_4381_; 
v_sz_boxed_4379_ = lean_unbox_usize(v_sz_4369_);
lean_dec(v_sz_4369_);
v_i_boxed_4380_ = lean_unbox_usize(v_i_4370_);
lean_dec(v_i_4370_);
v_res_4381_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0(v_sz_boxed_4379_, v_i_boxed_4380_, v_bs_4371_, v___y_4372_, v___y_4373_, v___y_4374_, v___y_4375_, v___y_4376_, v___y_4377_);
lean_dec(v___y_4377_);
lean_dec_ref(v___y_4376_);
lean_dec(v___y_4375_);
lean_dec_ref(v___y_4374_);
lean_dec(v___y_4373_);
lean_dec_ref(v___y_4372_);
return v_res_4381_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2(lean_object* v_as_4382_, size_t v_sz_4383_, size_t v_i_4384_, lean_object* v_b_4385_, lean_object* v___y_4386_, lean_object* v___y_4387_, lean_object* v___y_4388_, lean_object* v___y_4389_, lean_object* v___y_4390_, lean_object* v___y_4391_){
_start:
{
lean_object* v___x_4393_; 
v___x_4393_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___redArg(v_as_4382_, v_sz_4383_, v_i_4384_, v_b_4385_, v___y_4388_, v___y_4389_, v___y_4390_, v___y_4391_);
return v___x_4393_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___boxed(lean_object* v_as_4394_, lean_object* v_sz_4395_, lean_object* v_i_4396_, lean_object* v_b_4397_, lean_object* v___y_4398_, lean_object* v___y_4399_, lean_object* v___y_4400_, lean_object* v___y_4401_, lean_object* v___y_4402_, lean_object* v___y_4403_, lean_object* v___y_4404_){
_start:
{
size_t v_sz_boxed_4405_; size_t v_i_boxed_4406_; lean_object* v_res_4407_; 
v_sz_boxed_4405_ = lean_unbox_usize(v_sz_4395_);
lean_dec(v_sz_4395_);
v_i_boxed_4406_ = lean_unbox_usize(v_i_4396_);
lean_dec(v_i_4396_);
v_res_4407_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2(v_as_4394_, v_sz_boxed_4405_, v_i_boxed_4406_, v_b_4397_, v___y_4398_, v___y_4399_, v___y_4400_, v___y_4401_, v___y_4402_, v___y_4403_);
lean_dec(v___y_4403_);
lean_dec_ref(v___y_4402_);
lean_dec(v___y_4401_);
lean_dec_ref(v___y_4400_);
lean_dec(v___y_4399_);
lean_dec_ref(v___y_4398_);
lean_dec_ref(v_as_4394_);
return v_res_4407_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3(lean_object* v_as_4408_, size_t v_sz_4409_, size_t v_i_4410_, lean_object* v_b_4411_, lean_object* v___y_4412_, lean_object* v___y_4413_, lean_object* v___y_4414_, lean_object* v___y_4415_, lean_object* v___y_4416_, lean_object* v___y_4417_){
_start:
{
lean_object* v___x_4419_; 
v___x_4419_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___redArg(v_as_4408_, v_sz_4409_, v_i_4410_, v_b_4411_, v___y_4416_, v___y_4417_);
return v___x_4419_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___boxed(lean_object* v_as_4420_, lean_object* v_sz_4421_, lean_object* v_i_4422_, lean_object* v_b_4423_, lean_object* v___y_4424_, lean_object* v___y_4425_, lean_object* v___y_4426_, lean_object* v___y_4427_, lean_object* v___y_4428_, lean_object* v___y_4429_, lean_object* v___y_4430_){
_start:
{
size_t v_sz_boxed_4431_; size_t v_i_boxed_4432_; lean_object* v_res_4433_; 
v_sz_boxed_4431_ = lean_unbox_usize(v_sz_4421_);
lean_dec(v_sz_4421_);
v_i_boxed_4432_ = lean_unbox_usize(v_i_4422_);
lean_dec(v_i_4422_);
v_res_4433_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3(v_as_4420_, v_sz_boxed_4431_, v_i_boxed_4432_, v_b_4423_, v___y_4424_, v___y_4425_, v___y_4426_, v___y_4427_, v___y_4428_, v___y_4429_);
lean_dec(v___y_4429_);
lean_dec_ref(v___y_4428_);
lean_dec(v___y_4427_);
lean_dec_ref(v___y_4426_);
lean_dec(v___y_4425_);
lean_dec_ref(v___y_4424_);
lean_dec_ref(v_as_4420_);
return v_res_4433_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4(lean_object* v_as_4434_, size_t v_sz_4435_, size_t v_i_4436_, lean_object* v_b_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_, lean_object* v___y_4441_, lean_object* v___y_4442_, lean_object* v___y_4443_){
_start:
{
lean_object* v___x_4445_; 
v___x_4445_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4___redArg(v_as_4434_, v_sz_4435_, v_i_4436_, v_b_4437_, v___y_4440_, v___y_4441_, v___y_4442_, v___y_4443_);
return v___x_4445_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4___boxed(lean_object* v_as_4446_, lean_object* v_sz_4447_, lean_object* v_i_4448_, lean_object* v_b_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_, lean_object* v___y_4452_, lean_object* v___y_4453_, lean_object* v___y_4454_, lean_object* v___y_4455_, lean_object* v___y_4456_){
_start:
{
size_t v_sz_boxed_4457_; size_t v_i_boxed_4458_; lean_object* v_res_4459_; 
v_sz_boxed_4457_ = lean_unbox_usize(v_sz_4447_);
lean_dec(v_sz_4447_);
v_i_boxed_4458_ = lean_unbox_usize(v_i_4448_);
lean_dec(v_i_4448_);
v_res_4459_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4(v_as_4446_, v_sz_boxed_4457_, v_i_boxed_4458_, v_b_4449_, v___y_4450_, v___y_4451_, v___y_4452_, v___y_4453_, v___y_4454_, v___y_4455_);
lean_dec(v___y_4455_);
lean_dec_ref(v___y_4454_);
lean_dec(v___y_4453_);
lean_dec_ref(v___y_4452_);
lean_dec(v___y_4451_);
lean_dec_ref(v___y_4450_);
lean_dec_ref(v_as_4446_);
return v_res_4459_;
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
