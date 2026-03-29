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
lean_object* l_Lean_Elab_TerminationMeasure_delab(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
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
lean_object* l_Nat_blt___boxed(lean_object*, lean_object*);
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInductivePredicate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_zip___redArg(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__24___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__24___redArg___closed__0;
static lean_once_cell_t l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__24___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__24___redArg___closed__1;
static lean_once_cell_t l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__24___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__24___redArg___closed__2;
static lean_once_cell_t l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__24___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__24___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__24___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__24___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Nat_blt___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__24(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_21771__overap_176_; lean_object* v___x_177_; 
v___x_21771__overap_176_ = lean_array_uget_borrowed(v_as_166_, v_i_167_);
lean_inc(v___x_21771__overap_176_);
lean_inc(v___y_173_);
lean_inc_ref(v___y_172_);
lean_inc(v___y_171_);
lean_inc_ref(v___y_170_);
v___x_177_ = lean_apply_5(v___x_21771__overap_176_, v___y_170_, v___y_171_, v___y_172_, v___y_173_, lean_box(0));
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
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__24___redArg___closed__0(void){
_start:
{
lean_object* v___x_242_; 
v___x_242_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_242_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__24___redArg___closed__1(void){
_start:
{
lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_243_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__24___redArg___closed__0, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__24___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__24___redArg___closed__0);
v___x_244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_244_, 0, v___x_243_);
return v___x_244_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__24___redArg___closed__2(void){
_start:
{
lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_245_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__24___redArg___closed__1, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__24___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__24___redArg___closed__1);
v___x_246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_246_, 0, v___x_245_);
lean_ctor_set(v___x_246_, 1, v___x_245_);
return v___x_246_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__24___redArg___closed__3(void){
_start:
{
lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_247_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__24___redArg___closed__1, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__24___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__24___redArg___closed__1);
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
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__24___redArg(lean_object* v_env_249_, lean_object* v___y_250_, lean_object* v___y_251_){
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
v___x_264_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__24___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__24___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__24___redArg___closed__2);
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
v___x_276_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__24___redArg___closed__3, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__24___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__24___redArg___closed__3);
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
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__24___redArg___boxed(lean_object* v_env_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__24___redArg(v_env_289_, v___y_290_, v___y_291_);
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
v___x_314_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__24___redArg(v_env_294_, v___y_297_, v___y_299_);
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
lean_dec_ref(v___x_315_);
v___x_317_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__24___redArg(v_env_302_, v___y_297_, v___y_299_);
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
lean_dec_ref(v___x_315_);
v_a_304_ = v_a_326_;
goto v___jp_303_;
}
v___jp_303_:
{
lean_object* v___x_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_312_; 
v___x_305_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__24___redArg(v_env_302_, v___y_297_, v___y_299_);
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
lean_dec_ref(v___x_356_);
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
static lean_object* _init_l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg___closed__0(void){
_start:
{
lean_object* v___x_415_; lean_object* v_dummy_416_; 
v___x_415_ = lean_box(0);
v_dummy_416_ = l_Lean_Expr_sort___override(v___x_415_);
return v_dummy_416_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg(uint8_t v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_recArgInfos_420_, lean_object* v___x_421_, lean_object* v_preDefs_422_, lean_object* v_a_423_, lean_object* v_as_424_, lean_object* v_i_425_, lean_object* v_j_426_, lean_object* v_bs_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_){
_start:
{
lean_object* v_zero_433_; uint8_t v_isZero_434_; 
v_zero_433_ = lean_unsigned_to_nat(0u);
v_isZero_434_ = lean_nat_dec_eq(v_i_425_, v_zero_433_);
if (v_isZero_434_ == 1)
{
lean_object* v___x_435_; 
lean_dec(v_j_426_);
lean_dec(v_i_425_);
lean_dec_ref(v_a_423_);
lean_dec_ref(v_preDefs_422_);
lean_dec_ref(v___x_421_);
lean_dec_ref(v_recArgInfos_420_);
v___x_435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_435_, 0, v_bs_427_);
return v___x_435_;
}
else
{
lean_object* v___x_436_; lean_object* v_one_437_; lean_object* v_n_438_; lean_object* v_a_440_; lean_object* v___x_444_; 
v___x_436_ = l_Lean_instInhabitedExpr;
v_one_437_ = lean_unsigned_to_nat(1u);
v_n_438_ = lean_nat_sub(v_i_425_, v_one_437_);
lean_dec(v_i_425_);
v___x_444_ = lean_array_fget_borrowed(v_as_424_, v_j_426_);
if (v_a_417_ == 0)
{
lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_445_ = lean_array_get_borrowed(v___x_436_, v_a_418_, v_j_426_);
v___x_446_ = lean_array_get_borrowed(v___x_436_, v_a_419_, v_j_426_);
lean_inc(v___x_446_);
lean_inc(v___x_445_);
lean_inc(v___x_444_);
lean_inc_ref(v___x_421_);
lean_inc_ref(v_recArgInfos_420_);
v___x_447_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnF___boxed), 10, 5);
lean_closure_set(v___x_447_, 0, v_recArgInfos_420_);
lean_closure_set(v___x_447_, 1, v___x_421_);
lean_closure_set(v___x_447_, 2, v___x_444_);
lean_closure_set(v___x_447_, 3, v___x_445_);
lean_closure_set(v___x_447_, 4, v___x_446_);
lean_inc_ref(v_preDefs_422_);
v___x_448_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v_preDefs_422_, v___x_447_, v___y_428_, v___y_429_, v___y_430_, v___y_431_);
if (lean_obj_tag(v___x_448_) == 0)
{
lean_object* v_a_449_; 
v_a_449_ = lean_ctor_get(v___x_448_, 0);
lean_inc(v_a_449_);
lean_dec_ref(v___x_448_);
v_a_440_ = v_a_449_;
goto v___jp_439_;
}
else
{
lean_object* v_a_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_457_; 
lean_dec(v_n_438_);
lean_dec_ref(v_bs_427_);
lean_dec(v_j_426_);
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
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v_dummy_461_; lean_object* v_nargs_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_458_ = lean_array_get_borrowed(v___x_436_, v_a_418_, v_j_426_);
v___x_459_ = lean_array_get_borrowed(v___x_436_, v_a_419_, v_j_426_);
lean_inc_ref(v_a_423_);
v___x_460_ = lean_apply_1(v_a_423_, v_zero_433_);
v_dummy_461_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg___closed__0, &l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg___closed__0_once, _init_l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg___closed__0);
v_nargs_462_ = l_Lean_Expr_getAppNumArgs(v___x_460_);
lean_inc(v_nargs_462_);
v___x_463_ = lean_mk_array(v_nargs_462_, v_dummy_461_);
v___x_464_ = lean_nat_sub(v_nargs_462_, v_one_437_);
lean_dec(v_nargs_462_);
v___x_465_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___x_460_, v___x_463_, v___x_464_);
lean_inc(v___x_459_);
lean_inc(v___x_458_);
lean_inc(v___x_444_);
lean_inc_ref(v___x_421_);
lean_inc_ref(v_recArgInfos_420_);
v___x_466_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkIndPredBRecOnF___boxed), 11, 6);
lean_closure_set(v___x_466_, 0, v_recArgInfos_420_);
lean_closure_set(v___x_466_, 1, v___x_421_);
lean_closure_set(v___x_466_, 2, v___x_444_);
lean_closure_set(v___x_466_, 3, v___x_458_);
lean_closure_set(v___x_466_, 4, v___x_459_);
lean_closure_set(v___x_466_, 5, v___x_465_);
lean_inc_ref(v_preDefs_422_);
v___x_467_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v_preDefs_422_, v___x_466_, v___y_428_, v___y_429_, v___y_430_, v___y_431_);
if (lean_obj_tag(v___x_467_) == 0)
{
lean_object* v_a_468_; lean_object* v_fst_469_; lean_object* v_snd_470_; lean_object* v___y_472_; lean_object* v___x_481_; uint8_t v___x_482_; 
v_a_468_ = lean_ctor_get(v___x_467_, 0);
lean_inc(v_a_468_);
lean_dec_ref(v___x_467_);
v_fst_469_ = lean_ctor_get(v_a_468_, 0);
lean_inc(v_fst_469_);
v_snd_470_ = lean_ctor_get(v_a_468_, 1);
lean_inc(v_snd_470_);
lean_dec(v_a_468_);
v___x_481_ = lean_array_get_size(v_snd_470_);
v___x_482_ = lean_nat_dec_lt(v_zero_433_, v___x_481_);
if (v___x_482_ == 0)
{
lean_dec(v_snd_470_);
v_a_440_ = v_fst_469_;
goto v___jp_439_;
}
else
{
lean_object* v___x_483_; uint8_t v___x_484_; 
v___x_483_ = lean_box(0);
v___x_484_ = lean_nat_dec_le(v___x_481_, v___x_481_);
if (v___x_484_ == 0)
{
if (v___x_482_ == 0)
{
lean_dec(v_snd_470_);
v_a_440_ = v_fst_469_;
goto v___jp_439_;
}
else
{
size_t v___x_485_; size_t v___x_486_; lean_object* v___x_487_; 
v___x_485_ = ((size_t)0ULL);
v___x_486_ = lean_usize_of_nat(v___x_481_);
v___x_487_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13(v_snd_470_, v___x_485_, v___x_486_, v___x_483_, v___y_428_, v___y_429_, v___y_430_, v___y_431_);
lean_dec(v_snd_470_);
v___y_472_ = v___x_487_;
goto v___jp_471_;
}
}
else
{
size_t v___x_488_; size_t v___x_489_; lean_object* v___x_490_; 
v___x_488_ = ((size_t)0ULL);
v___x_489_ = lean_usize_of_nat(v___x_481_);
v___x_490_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13(v_snd_470_, v___x_488_, v___x_489_, v___x_483_, v___y_428_, v___y_429_, v___y_430_, v___y_431_);
lean_dec(v_snd_470_);
v___y_472_ = v___x_490_;
goto v___jp_471_;
}
}
v___jp_471_:
{
if (lean_obj_tag(v___y_472_) == 0)
{
lean_dec_ref(v___y_472_);
v_a_440_ = v_fst_469_;
goto v___jp_439_;
}
else
{
lean_object* v_a_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_480_; 
lean_dec(v_fst_469_);
lean_dec(v_n_438_);
lean_dec_ref(v_bs_427_);
lean_dec(v_j_426_);
lean_dec_ref(v_a_423_);
lean_dec_ref(v_preDefs_422_);
lean_dec_ref(v___x_421_);
lean_dec_ref(v_recArgInfos_420_);
v_a_473_ = lean_ctor_get(v___y_472_, 0);
v_isSharedCheck_480_ = !lean_is_exclusive(v___y_472_);
if (v_isSharedCheck_480_ == 0)
{
v___x_475_ = v___y_472_;
v_isShared_476_ = v_isSharedCheck_480_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_a_473_);
lean_dec(v___y_472_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_480_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v___x_478_; 
if (v_isShared_476_ == 0)
{
v___x_478_ = v___x_475_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v_a_473_);
v___x_478_ = v_reuseFailAlloc_479_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
return v___x_478_;
}
}
}
}
}
else
{
lean_object* v_a_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_498_; 
lean_dec(v_n_438_);
lean_dec_ref(v_bs_427_);
lean_dec(v_j_426_);
lean_dec_ref(v_a_423_);
lean_dec_ref(v_preDefs_422_);
lean_dec_ref(v___x_421_);
lean_dec_ref(v_recArgInfos_420_);
v_a_491_ = lean_ctor_get(v___x_467_, 0);
v_isSharedCheck_498_ = !lean_is_exclusive(v___x_467_);
if (v_isSharedCheck_498_ == 0)
{
v___x_493_ = v___x_467_;
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_a_491_);
lean_dec(v___x_467_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_496_; 
if (v_isShared_494_ == 0)
{
v___x_496_ = v___x_493_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v_a_491_);
v___x_496_ = v_reuseFailAlloc_497_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
return v___x_496_;
}
}
}
}
v___jp_439_:
{
lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_441_ = lean_nat_add(v_j_426_, v_one_437_);
lean_dec(v_j_426_);
v___x_442_ = lean_array_push(v_bs_427_, v_a_440_);
v_i_425_ = v_n_438_;
v_j_426_ = v___x_441_;
v_bs_427_ = v___x_442_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg___boxed(lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_recArgInfos_502_, lean_object* v___x_503_, lean_object* v_preDefs_504_, lean_object* v_a_505_, lean_object* v_as_506_, lean_object* v_i_507_, lean_object* v_j_508_, lean_object* v_bs_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_){
_start:
{
uint8_t v_a_27513__boxed_515_; lean_object* v_res_516_; 
v_a_27513__boxed_515_ = lean_unbox(v_a_499_);
v_res_516_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg(v_a_27513__boxed_515_, v_a_500_, v_a_501_, v_recArgInfos_502_, v___x_503_, v_preDefs_504_, v_a_505_, v_as_506_, v_i_507_, v_j_508_, v_bs_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_);
lean_dec(v___y_513_);
lean_dec_ref(v___y_512_);
lean_dec(v___y_511_);
lean_dec_ref(v___y_510_);
lean_dec_ref(v_as_506_);
lean_dec_ref(v_a_501_);
lean_dec_ref(v_a_500_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11_spec__21(lean_object* v_msgData_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_){
_start:
{
lean_object* v___x_523_; lean_object* v_env_524_; lean_object* v___x_525_; lean_object* v_mctx_526_; lean_object* v_lctx_527_; lean_object* v_options_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_523_ = lean_st_ref_get(v___y_521_);
v_env_524_ = lean_ctor_get(v___x_523_, 0);
lean_inc_ref(v_env_524_);
lean_dec(v___x_523_);
v___x_525_ = lean_st_ref_get(v___y_519_);
v_mctx_526_ = lean_ctor_get(v___x_525_, 0);
lean_inc_ref(v_mctx_526_);
lean_dec(v___x_525_);
v_lctx_527_ = lean_ctor_get(v___y_518_, 2);
v_options_528_ = lean_ctor_get(v___y_520_, 2);
lean_inc_ref(v_options_528_);
lean_inc_ref(v_lctx_527_);
v___x_529_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_529_, 0, v_env_524_);
lean_ctor_set(v___x_529_, 1, v_mctx_526_);
lean_ctor_set(v___x_529_, 2, v_lctx_527_);
lean_ctor_set(v___x_529_, 3, v_options_528_);
v___x_530_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_530_, 0, v___x_529_);
lean_ctor_set(v___x_530_, 1, v_msgData_517_);
v___x_531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_531_, 0, v___x_530_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11_spec__21___boxed(lean_object* v_msgData_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11_spec__21(v_msgData_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_);
lean_dec(v___y_536_);
lean_dec_ref(v___y_535_);
lean_dec(v___y_534_);
lean_dec_ref(v___y_533_);
return v_res_538_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___closed__0(void){
_start:
{
lean_object* v___x_539_; double v___x_540_; 
v___x_539_ = lean_unsigned_to_nat(0u);
v___x_540_ = lean_float_of_nat(v___x_539_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(lean_object* v_cls_544_, lean_object* v_msg_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_){
_start:
{
lean_object* v_ref_551_; lean_object* v___x_552_; lean_object* v_a_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_597_; 
v_ref_551_ = lean_ctor_get(v___y_548_, 5);
v___x_552_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11_spec__21(v_msg_545_, v___y_546_, v___y_547_, v___y_548_, v___y_549_);
v_a_553_ = lean_ctor_get(v___x_552_, 0);
v_isSharedCheck_597_ = !lean_is_exclusive(v___x_552_);
if (v_isSharedCheck_597_ == 0)
{
v___x_555_ = v___x_552_;
v_isShared_556_ = v_isSharedCheck_597_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_a_553_);
lean_dec(v___x_552_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_597_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
lean_object* v___x_557_; lean_object* v_traceState_558_; lean_object* v_env_559_; lean_object* v_nextMacroScope_560_; lean_object* v_ngen_561_; lean_object* v_auxDeclNGen_562_; lean_object* v_cache_563_; lean_object* v_messages_564_; lean_object* v_infoState_565_; lean_object* v_snapshotTasks_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_596_; 
v___x_557_ = lean_st_ref_take(v___y_549_);
v_traceState_558_ = lean_ctor_get(v___x_557_, 4);
v_env_559_ = lean_ctor_get(v___x_557_, 0);
v_nextMacroScope_560_ = lean_ctor_get(v___x_557_, 1);
v_ngen_561_ = lean_ctor_get(v___x_557_, 2);
v_auxDeclNGen_562_ = lean_ctor_get(v___x_557_, 3);
v_cache_563_ = lean_ctor_get(v___x_557_, 5);
v_messages_564_ = lean_ctor_get(v___x_557_, 6);
v_infoState_565_ = lean_ctor_get(v___x_557_, 7);
v_snapshotTasks_566_ = lean_ctor_get(v___x_557_, 8);
v_isSharedCheck_596_ = !lean_is_exclusive(v___x_557_);
if (v_isSharedCheck_596_ == 0)
{
v___x_568_ = v___x_557_;
v_isShared_569_ = v_isSharedCheck_596_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_snapshotTasks_566_);
lean_inc(v_infoState_565_);
lean_inc(v_messages_564_);
lean_inc(v_cache_563_);
lean_inc(v_traceState_558_);
lean_inc(v_auxDeclNGen_562_);
lean_inc(v_ngen_561_);
lean_inc(v_nextMacroScope_560_);
lean_inc(v_env_559_);
lean_dec(v___x_557_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_596_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
uint64_t v_tid_570_; lean_object* v_traces_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_595_; 
v_tid_570_ = lean_ctor_get_uint64(v_traceState_558_, sizeof(void*)*1);
v_traces_571_ = lean_ctor_get(v_traceState_558_, 0);
v_isSharedCheck_595_ = !lean_is_exclusive(v_traceState_558_);
if (v_isSharedCheck_595_ == 0)
{
v___x_573_ = v_traceState_558_;
v_isShared_574_ = v_isSharedCheck_595_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_traces_571_);
lean_dec(v_traceState_558_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_595_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v___x_575_; double v___x_576_; uint8_t v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_585_; 
v___x_575_ = lean_box(0);
v___x_576_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___closed__0);
v___x_577_ = 0;
v___x_578_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___closed__1));
v___x_579_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_579_, 0, v_cls_544_);
lean_ctor_set(v___x_579_, 1, v___x_575_);
lean_ctor_set(v___x_579_, 2, v___x_578_);
lean_ctor_set_float(v___x_579_, sizeof(void*)*3, v___x_576_);
lean_ctor_set_float(v___x_579_, sizeof(void*)*3 + 8, v___x_576_);
lean_ctor_set_uint8(v___x_579_, sizeof(void*)*3 + 16, v___x_577_);
v___x_580_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___closed__2));
v___x_581_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_581_, 0, v___x_579_);
lean_ctor_set(v___x_581_, 1, v_a_553_);
lean_ctor_set(v___x_581_, 2, v___x_580_);
lean_inc(v_ref_551_);
v___x_582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_582_, 0, v_ref_551_);
lean_ctor_set(v___x_582_, 1, v___x_581_);
v___x_583_ = l_Lean_PersistentArray_push___redArg(v_traces_571_, v___x_582_);
if (v_isShared_574_ == 0)
{
lean_ctor_set(v___x_573_, 0, v___x_583_);
v___x_585_ = v___x_573_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v___x_583_);
lean_ctor_set_uint64(v_reuseFailAlloc_594_, sizeof(void*)*1, v_tid_570_);
v___x_585_ = v_reuseFailAlloc_594_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
lean_object* v___x_587_; 
if (v_isShared_569_ == 0)
{
lean_ctor_set(v___x_568_, 4, v___x_585_);
v___x_587_ = v___x_568_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v_env_559_);
lean_ctor_set(v_reuseFailAlloc_593_, 1, v_nextMacroScope_560_);
lean_ctor_set(v_reuseFailAlloc_593_, 2, v_ngen_561_);
lean_ctor_set(v_reuseFailAlloc_593_, 3, v_auxDeclNGen_562_);
lean_ctor_set(v_reuseFailAlloc_593_, 4, v___x_585_);
lean_ctor_set(v_reuseFailAlloc_593_, 5, v_cache_563_);
lean_ctor_set(v_reuseFailAlloc_593_, 6, v_messages_564_);
lean_ctor_set(v_reuseFailAlloc_593_, 7, v_infoState_565_);
lean_ctor_set(v_reuseFailAlloc_593_, 8, v_snapshotTasks_566_);
v___x_587_ = v_reuseFailAlloc_593_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_591_; 
v___x_588_ = lean_st_ref_set(v___y_549_, v___x_587_);
v___x_589_ = lean_box(0);
if (v_isShared_556_ == 0)
{
lean_ctor_set(v___x_555_, 0, v___x_589_);
v___x_591_ = v___x_555_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v___x_589_);
v___x_591_ = v_reuseFailAlloc_592_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
return v___x_591_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___boxed(lean_object* v_cls_598_, lean_object* v_msg_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_){
_start:
{
lean_object* v_res_605_; 
v_res_605_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v_cls_598_, v_msg_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_);
lean_dec(v___y_603_);
lean_dec_ref(v___y_602_);
lean_dec(v___y_601_);
lean_dec_ref(v___y_600_);
return v_res_605_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9(lean_object* v_as_606_, lean_object* v_bs_607_, lean_object* v_i_608_, lean_object* v_cs_609_){
_start:
{
lean_object* v___x_610_; uint8_t v___x_611_; 
v___x_610_ = lean_array_get_size(v_as_606_);
v___x_611_ = lean_nat_dec_lt(v_i_608_, v___x_610_);
if (v___x_611_ == 0)
{
lean_dec(v_i_608_);
return v_cs_609_;
}
else
{
lean_object* v___x_612_; uint8_t v___x_613_; 
v___x_612_ = lean_array_get_size(v_bs_607_);
v___x_613_ = lean_nat_dec_lt(v_i_608_, v___x_612_);
if (v___x_613_ == 0)
{
lean_dec(v_i_608_);
return v_cs_609_;
}
else
{
lean_object* v_a_614_; lean_object* v_ref_615_; uint8_t v_kind_616_; lean_object* v_levelParams_617_; lean_object* v_modifiers_618_; lean_object* v_declName_619_; lean_object* v_binders_620_; lean_object* v_numSectionVars_621_; lean_object* v_type_622_; lean_object* v_termination_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_635_; 
v_a_614_ = lean_array_fget(v_as_606_, v_i_608_);
v_ref_615_ = lean_ctor_get(v_a_614_, 0);
v_kind_616_ = lean_ctor_get_uint8(v_a_614_, sizeof(void*)*9);
v_levelParams_617_ = lean_ctor_get(v_a_614_, 1);
v_modifiers_618_ = lean_ctor_get(v_a_614_, 2);
v_declName_619_ = lean_ctor_get(v_a_614_, 3);
v_binders_620_ = lean_ctor_get(v_a_614_, 4);
v_numSectionVars_621_ = lean_ctor_get(v_a_614_, 5);
v_type_622_ = lean_ctor_get(v_a_614_, 6);
v_termination_623_ = lean_ctor_get(v_a_614_, 8);
v_isSharedCheck_635_ = !lean_is_exclusive(v_a_614_);
if (v_isSharedCheck_635_ == 0)
{
lean_object* v_unused_636_; 
v_unused_636_ = lean_ctor_get(v_a_614_, 7);
lean_dec(v_unused_636_);
v___x_625_ = v_a_614_;
v_isShared_626_ = v_isSharedCheck_635_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_termination_623_);
lean_inc(v_type_622_);
lean_inc(v_numSectionVars_621_);
lean_inc(v_binders_620_);
lean_inc(v_declName_619_);
lean_inc(v_modifiers_618_);
lean_inc(v_levelParams_617_);
lean_inc(v_ref_615_);
lean_dec(v_a_614_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_635_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v_b_627_; lean_object* v___x_629_; 
v_b_627_ = lean_array_fget_borrowed(v_bs_607_, v_i_608_);
lean_inc(v_b_627_);
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 7, v_b_627_);
v___x_629_ = v___x_625_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v_ref_615_);
lean_ctor_set(v_reuseFailAlloc_634_, 1, v_levelParams_617_);
lean_ctor_set(v_reuseFailAlloc_634_, 2, v_modifiers_618_);
lean_ctor_set(v_reuseFailAlloc_634_, 3, v_declName_619_);
lean_ctor_set(v_reuseFailAlloc_634_, 4, v_binders_620_);
lean_ctor_set(v_reuseFailAlloc_634_, 5, v_numSectionVars_621_);
lean_ctor_set(v_reuseFailAlloc_634_, 6, v_type_622_);
lean_ctor_set(v_reuseFailAlloc_634_, 7, v_b_627_);
lean_ctor_set(v_reuseFailAlloc_634_, 8, v_termination_623_);
lean_ctor_set_uint8(v_reuseFailAlloc_634_, sizeof(void*)*9, v_kind_616_);
v___x_629_ = v_reuseFailAlloc_634_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_630_ = lean_unsigned_to_nat(1u);
v___x_631_ = lean_nat_add(v_i_608_, v___x_630_);
lean_dec(v_i_608_);
v___x_632_ = lean_array_push(v_cs_609_, v___x_629_);
v_i_608_ = v___x_631_;
v_cs_609_ = v___x_632_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9___boxed(lean_object* v_as_637_, lean_object* v_bs_638_, lean_object* v_i_639_, lean_object* v_cs_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9(v_as_637_, v_bs_638_, v_i_639_, v_cs_640_);
lean_dec_ref(v_bs_638_);
lean_dec_ref(v_as_637_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(lean_object* v_a_642_, lean_object* v_a_643_){
_start:
{
if (lean_obj_tag(v_a_642_) == 0)
{
lean_object* v___x_644_; 
v___x_644_ = l_List_reverse___redArg(v_a_643_);
return v___x_644_;
}
else
{
lean_object* v_head_645_; lean_object* v_tail_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_655_; 
v_head_645_ = lean_ctor_get(v_a_642_, 0);
v_tail_646_ = lean_ctor_get(v_a_642_, 1);
v_isSharedCheck_655_ = !lean_is_exclusive(v_a_642_);
if (v_isSharedCheck_655_ == 0)
{
v___x_648_ = v_a_642_;
v_isShared_649_ = v_isSharedCheck_655_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_tail_646_);
lean_inc(v_head_645_);
lean_dec(v_a_642_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_655_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___x_650_; lean_object* v___x_652_; 
v___x_650_ = l_Lean_MessageData_ofExpr(v_head_645_);
if (v_isShared_649_ == 0)
{
lean_ctor_set(v___x_648_, 1, v_a_643_);
lean_ctor_set(v___x_648_, 0, v___x_650_);
v___x_652_ = v___x_648_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v___x_650_);
lean_ctor_set(v_reuseFailAlloc_654_, 1, v_a_643_);
v___x_652_ = v_reuseFailAlloc_654_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
v_a_642_ = v_tail_646_;
v_a_643_ = v___x_652_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___lam__0(lean_object* v_fixedParamPerms_656_, lean_object* v___x_657_, lean_object* v_j_658_, lean_object* v_xs_659_, lean_object* v_snd_660_, uint8_t v_isZero_661_, lean_object* v_ys_662_, lean_object* v_x_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_){
_start:
{
lean_object* v_perms_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; uint8_t v___x_673_; uint8_t v___x_674_; lean_object* v___x_675_; 
v_perms_669_ = lean_ctor_get(v_fixedParamPerms_656_, 1);
v___x_670_ = lean_array_get_borrowed(v___x_657_, v_perms_669_, v_j_658_);
lean_inc_ref(v_ys_662_);
lean_inc(v___x_670_);
v___x_671_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v___x_670_, v_xs_659_, v_ys_662_);
v___x_672_ = l_Lean_Expr_beta(v_snd_660_, v_ys_662_);
v___x_673_ = 1;
v___x_674_ = 1;
v___x_675_ = l_Lean_Meta_mkLambdaFVars(v___x_671_, v___x_672_, v_isZero_661_, v___x_673_, v_isZero_661_, v___x_673_, v___x_674_, v___y_664_, v___y_665_, v___y_666_, v___y_667_);
lean_dec_ref(v___x_671_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___lam__0___boxed(lean_object* v_fixedParamPerms_676_, lean_object* v___x_677_, lean_object* v_j_678_, lean_object* v_xs_679_, lean_object* v_snd_680_, lean_object* v_isZero_681_, lean_object* v_ys_682_, lean_object* v_x_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_){
_start:
{
uint8_t v_isZero_boxed_689_; lean_object* v_res_690_; 
v_isZero_boxed_689_ = lean_unbox(v_isZero_681_);
v_res_690_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___lam__0(v_fixedParamPerms_676_, v___x_677_, v_j_678_, v_xs_679_, v_snd_680_, v_isZero_boxed_689_, v_ys_682_, v_x_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_);
lean_dec(v___y_687_);
lean_dec_ref(v___y_686_);
lean_dec(v___y_685_);
lean_dec_ref(v___y_684_);
lean_dec_ref(v_x_683_);
lean_dec_ref(v_xs_679_);
lean_dec(v_j_678_);
lean_dec_ref(v___x_677_);
lean_dec_ref(v_fixedParamPerms_676_);
return v_res_690_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_691_; 
v___x_691_ = l_Array_instInhabited(lean_box(0));
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg(lean_object* v_fixedParamPerms_692_, lean_object* v_xs_693_, lean_object* v_as_694_, lean_object* v_i_695_, lean_object* v_j_696_, lean_object* v_bs_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_){
_start:
{
lean_object* v_zero_703_; uint8_t v_isZero_704_; 
v_zero_703_ = lean_unsigned_to_nat(0u);
v_isZero_704_ = lean_nat_dec_eq(v_i_695_, v_zero_703_);
if (v_isZero_704_ == 1)
{
lean_object* v___x_705_; 
lean_dec(v_j_696_);
lean_dec(v_i_695_);
lean_dec_ref(v_xs_693_);
lean_dec_ref(v_fixedParamPerms_692_);
v___x_705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_705_, 0, v_bs_697_);
return v___x_705_;
}
else
{
lean_object* v___x_706_; lean_object* v_fst_707_; lean_object* v_snd_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___f_711_; lean_object* v___x_712_; 
v___x_706_ = lean_array_fget_borrowed(v_as_694_, v_j_696_);
v_fst_707_ = lean_ctor_get(v___x_706_, 0);
v_snd_708_ = lean_ctor_get(v___x_706_, 1);
v___x_709_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0, &l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0_once, _init_l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0);
v___x_710_ = lean_box(v_isZero_704_);
lean_inc(v_snd_708_);
lean_inc_ref(v_xs_693_);
lean_inc(v_j_696_);
lean_inc_ref(v_fixedParamPerms_692_);
v___f_711_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___lam__0___boxed), 13, 6);
lean_closure_set(v___f_711_, 0, v_fixedParamPerms_692_);
lean_closure_set(v___f_711_, 1, v___x_709_);
lean_closure_set(v___f_711_, 2, v_j_696_);
lean_closure_set(v___f_711_, 3, v_xs_693_);
lean_closure_set(v___f_711_, 4, v_snd_708_);
lean_closure_set(v___f_711_, 5, v___x_710_);
lean_inc(v_fst_707_);
v___x_712_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg(v_fst_707_, v___f_711_, v_isZero_704_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
if (lean_obj_tag(v___x_712_) == 0)
{
lean_object* v_a_713_; lean_object* v_one_714_; lean_object* v_n_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
v_a_713_ = lean_ctor_get(v___x_712_, 0);
lean_inc(v_a_713_);
lean_dec_ref(v___x_712_);
v_one_714_ = lean_unsigned_to_nat(1u);
v_n_715_ = lean_nat_sub(v_i_695_, v_one_714_);
lean_dec(v_i_695_);
v___x_716_ = lean_nat_add(v_j_696_, v_one_714_);
lean_dec(v_j_696_);
v___x_717_ = lean_array_push(v_bs_697_, v_a_713_);
v_i_695_ = v_n_715_;
v_j_696_ = v___x_716_;
v_bs_697_ = v___x_717_;
goto _start;
}
else
{
lean_object* v_a_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_726_; 
lean_dec_ref(v_bs_697_);
lean_dec(v_j_696_);
lean_dec(v_i_695_);
lean_dec_ref(v_xs_693_);
lean_dec_ref(v_fixedParamPerms_692_);
v_a_719_ = lean_ctor_get(v___x_712_, 0);
v_isSharedCheck_726_ = !lean_is_exclusive(v___x_712_);
if (v_isSharedCheck_726_ == 0)
{
v___x_721_ = v___x_712_;
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_a_719_);
lean_dec(v___x_712_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v___x_724_; 
if (v_isShared_722_ == 0)
{
v___x_724_ = v___x_721_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v_a_719_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___boxed(lean_object* v_fixedParamPerms_727_, lean_object* v_xs_728_, lean_object* v_as_729_, lean_object* v_i_730_, lean_object* v_j_731_, lean_object* v_bs_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg(v_fixedParamPerms_727_, v_xs_728_, v_as_729_, v_i_730_, v_j_731_, v_bs_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_);
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
lean_dec(v___y_734_);
lean_dec_ref(v___y_733_);
lean_dec_ref(v_as_729_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__15(lean_object* v_a_739_, lean_object* v_a_740_){
_start:
{
if (lean_obj_tag(v_a_739_) == 0)
{
lean_object* v___x_741_; 
v___x_741_ = l_List_reverse___redArg(v_a_740_);
return v___x_741_;
}
else
{
lean_object* v_head_742_; lean_object* v_tail_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_752_; 
v_head_742_ = lean_ctor_get(v_a_739_, 0);
v_tail_743_ = lean_ctor_get(v_a_739_, 1);
v_isSharedCheck_752_ = !lean_is_exclusive(v_a_739_);
if (v_isSharedCheck_752_ == 0)
{
v___x_745_ = v_a_739_;
v_isShared_746_ = v_isSharedCheck_752_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_tail_743_);
lean_inc(v_head_742_);
lean_dec(v_a_739_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_752_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v___x_747_; lean_object* v___x_749_; 
v___x_747_ = l_Lean_mkLevelParam(v_head_742_);
if (v_isShared_746_ == 0)
{
lean_ctor_set(v___x_745_, 1, v_a_740_);
lean_ctor_set(v___x_745_, 0, v___x_747_);
v___x_749_ = v___x_745_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v___x_747_);
lean_ctor_set(v_reuseFailAlloc_751_, 1, v_a_740_);
v___x_749_ = v_reuseFailAlloc_751_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
v_a_739_ = v_tail_743_;
v_a_740_ = v___x_749_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__0(void){
_start:
{
lean_object* v___x_753_; 
v___x_753_ = l_instMonadEIO(lean_box(0));
return v___x_753_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__5(void){
_start:
{
lean_object* v___x_758_; 
v___x_758_ = l_Array_instInhabited(lean_box(0));
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg(lean_object* v_msg_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_){
_start:
{
lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v_toApplicative_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_828_; 
v___x_765_ = lean_obj_once(&l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__0, &l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__0_once, _init_l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__0);
v___x_766_ = l_StateRefT_x27_instMonad___redArg(v___x_765_);
v_toApplicative_767_ = lean_ctor_get(v___x_766_, 0);
v_isSharedCheck_828_ = !lean_is_exclusive(v___x_766_);
if (v_isSharedCheck_828_ == 0)
{
lean_object* v_unused_829_; 
v_unused_829_ = lean_ctor_get(v___x_766_, 1);
lean_dec(v_unused_829_);
v___x_769_ = v___x_766_;
v_isShared_770_ = v_isSharedCheck_828_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_toApplicative_767_);
lean_dec(v___x_766_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_828_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v_toFunctor_771_; lean_object* v_toSeq_772_; lean_object* v_toSeqLeft_773_; lean_object* v_toSeqRight_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_826_; 
v_toFunctor_771_ = lean_ctor_get(v_toApplicative_767_, 0);
v_toSeq_772_ = lean_ctor_get(v_toApplicative_767_, 2);
v_toSeqLeft_773_ = lean_ctor_get(v_toApplicative_767_, 3);
v_toSeqRight_774_ = lean_ctor_get(v_toApplicative_767_, 4);
v_isSharedCheck_826_ = !lean_is_exclusive(v_toApplicative_767_);
if (v_isSharedCheck_826_ == 0)
{
lean_object* v_unused_827_; 
v_unused_827_ = lean_ctor_get(v_toApplicative_767_, 1);
lean_dec(v_unused_827_);
v___x_776_ = v_toApplicative_767_;
v_isShared_777_ = v_isSharedCheck_826_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_toSeqRight_774_);
lean_inc(v_toSeqLeft_773_);
lean_inc(v_toSeq_772_);
lean_inc(v_toFunctor_771_);
lean_dec(v_toApplicative_767_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_826_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___f_778_; lean_object* v___f_779_; lean_object* v___f_780_; lean_object* v___f_781_; lean_object* v___x_782_; lean_object* v___f_783_; lean_object* v___f_784_; lean_object* v___f_785_; lean_object* v___x_787_; 
v___f_778_ = ((lean_object*)(l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__1));
v___f_779_ = ((lean_object*)(l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__2));
lean_inc_ref(v_toFunctor_771_);
v___f_780_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_780_, 0, v_toFunctor_771_);
v___f_781_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_781_, 0, v_toFunctor_771_);
v___x_782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_782_, 0, v___f_780_);
lean_ctor_set(v___x_782_, 1, v___f_781_);
v___f_783_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_783_, 0, v_toSeqRight_774_);
v___f_784_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_784_, 0, v_toSeqLeft_773_);
v___f_785_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_785_, 0, v_toSeq_772_);
if (v_isShared_777_ == 0)
{
lean_ctor_set(v___x_776_, 4, v___f_783_);
lean_ctor_set(v___x_776_, 3, v___f_784_);
lean_ctor_set(v___x_776_, 2, v___f_785_);
lean_ctor_set(v___x_776_, 1, v___f_778_);
lean_ctor_set(v___x_776_, 0, v___x_782_);
v___x_787_ = v___x_776_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v___x_782_);
lean_ctor_set(v_reuseFailAlloc_825_, 1, v___f_778_);
lean_ctor_set(v_reuseFailAlloc_825_, 2, v___f_785_);
lean_ctor_set(v_reuseFailAlloc_825_, 3, v___f_784_);
lean_ctor_set(v_reuseFailAlloc_825_, 4, v___f_783_);
v___x_787_ = v_reuseFailAlloc_825_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
lean_object* v___x_789_; 
if (v_isShared_770_ == 0)
{
lean_ctor_set(v___x_769_, 1, v___f_779_);
lean_ctor_set(v___x_769_, 0, v___x_787_);
v___x_789_ = v___x_769_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v___x_787_);
lean_ctor_set(v_reuseFailAlloc_824_, 1, v___f_779_);
v___x_789_ = v_reuseFailAlloc_824_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
lean_object* v___x_790_; lean_object* v_toApplicative_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_822_; 
v___x_790_ = l_StateRefT_x27_instMonad___redArg(v___x_789_);
v_toApplicative_791_ = lean_ctor_get(v___x_790_, 0);
v_isSharedCheck_822_ = !lean_is_exclusive(v___x_790_);
if (v_isSharedCheck_822_ == 0)
{
lean_object* v_unused_823_; 
v_unused_823_ = lean_ctor_get(v___x_790_, 1);
lean_dec(v_unused_823_);
v___x_793_ = v___x_790_;
v_isShared_794_ = v_isSharedCheck_822_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_toApplicative_791_);
lean_dec(v___x_790_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_822_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v_toFunctor_795_; lean_object* v_toSeq_796_; lean_object* v_toSeqLeft_797_; lean_object* v_toSeqRight_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_820_; 
v_toFunctor_795_ = lean_ctor_get(v_toApplicative_791_, 0);
v_toSeq_796_ = lean_ctor_get(v_toApplicative_791_, 2);
v_toSeqLeft_797_ = lean_ctor_get(v_toApplicative_791_, 3);
v_toSeqRight_798_ = lean_ctor_get(v_toApplicative_791_, 4);
v_isSharedCheck_820_ = !lean_is_exclusive(v_toApplicative_791_);
if (v_isSharedCheck_820_ == 0)
{
lean_object* v_unused_821_; 
v_unused_821_ = lean_ctor_get(v_toApplicative_791_, 1);
lean_dec(v_unused_821_);
v___x_800_ = v_toApplicative_791_;
v_isShared_801_ = v_isSharedCheck_820_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_toSeqRight_798_);
lean_inc(v_toSeqLeft_797_);
lean_inc(v_toSeq_796_);
lean_inc(v_toFunctor_795_);
lean_dec(v_toApplicative_791_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_820_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___f_802_; lean_object* v___f_803_; lean_object* v___f_804_; lean_object* v___f_805_; lean_object* v___x_806_; lean_object* v___f_807_; lean_object* v___f_808_; lean_object* v___f_809_; lean_object* v___x_811_; 
v___f_802_ = ((lean_object*)(l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__3));
v___f_803_ = ((lean_object*)(l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__4));
lean_inc_ref(v_toFunctor_795_);
v___f_804_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_804_, 0, v_toFunctor_795_);
v___f_805_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_805_, 0, v_toFunctor_795_);
v___x_806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_806_, 0, v___f_804_);
lean_ctor_set(v___x_806_, 1, v___f_805_);
v___f_807_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_807_, 0, v_toSeqRight_798_);
v___f_808_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_808_, 0, v_toSeqLeft_797_);
v___f_809_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_809_, 0, v_toSeq_796_);
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 4, v___f_807_);
lean_ctor_set(v___x_800_, 3, v___f_808_);
lean_ctor_set(v___x_800_, 2, v___f_809_);
lean_ctor_set(v___x_800_, 1, v___f_802_);
lean_ctor_set(v___x_800_, 0, v___x_806_);
v___x_811_ = v___x_800_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v___x_806_);
lean_ctor_set(v_reuseFailAlloc_819_, 1, v___f_802_);
lean_ctor_set(v_reuseFailAlloc_819_, 2, v___f_809_);
lean_ctor_set(v_reuseFailAlloc_819_, 3, v___f_808_);
lean_ctor_set(v_reuseFailAlloc_819_, 4, v___f_807_);
v___x_811_ = v_reuseFailAlloc_819_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
lean_object* v___x_813_; 
if (v_isShared_794_ == 0)
{
lean_ctor_set(v___x_793_, 1, v___f_803_);
lean_ctor_set(v___x_793_, 0, v___x_811_);
v___x_813_ = v___x_793_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v___x_811_);
lean_ctor_set(v_reuseFailAlloc_818_, 1, v___f_803_);
v___x_813_ = v_reuseFailAlloc_818_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_23844__overap_816_; lean_object* v___x_817_; 
v___x_814_ = lean_obj_once(&l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__5, &l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__5_once, _init_l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__5);
v___x_815_ = l_instInhabitedOfMonad___redArg(v___x_813_, v___x_814_);
v___x_23844__overap_816_ = lean_panic_fn_borrowed(v___x_815_, v_msg_759_);
lean_dec(v___x_815_);
lean_inc(v___y_763_);
lean_inc_ref(v___y_762_);
lean_inc(v___y_761_);
lean_inc_ref(v___y_760_);
v___x_817_ = lean_apply_5(v___x_23844__overap_816_, v___y_760_, v___y_761_, v___y_762_, v___y_763_, lean_box(0));
return v___x_817_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___boxed(lean_object* v_msg_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_){
_start:
{
lean_object* v_res_836_; 
v_res_836_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg(v_msg_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_);
lean_dec(v___y_834_);
lean_dec_ref(v___y_833_);
lean_dec(v___y_832_);
lean_dec_ref(v___y_831_);
return v_res_836_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__13(lean_object* v_xs_837_, size_t v_sz_838_, size_t v_i_839_, lean_object* v_bs_840_){
_start:
{
uint8_t v___x_841_; 
v___x_841_ = lean_usize_dec_lt(v_i_839_, v_sz_838_);
if (v___x_841_ == 0)
{
return v_bs_840_;
}
else
{
lean_object* v___x_842_; lean_object* v_v_843_; lean_object* v___x_844_; lean_object* v_bs_x27_845_; lean_object* v___x_846_; size_t v___x_847_; size_t v___x_848_; lean_object* v___x_849_; 
v___x_842_ = l_Lean_instInhabitedExpr;
v_v_843_ = lean_array_uget(v_bs_840_, v_i_839_);
v___x_844_ = lean_unsigned_to_nat(0u);
v_bs_x27_845_ = lean_array_uset(v_bs_840_, v_i_839_, v___x_844_);
v___x_846_ = lean_array_get_borrowed(v___x_842_, v_xs_837_, v_v_843_);
lean_dec(v_v_843_);
v___x_847_ = ((size_t)1ULL);
v___x_848_ = lean_usize_add(v_i_839_, v___x_847_);
lean_inc(v___x_846_);
v___x_849_ = lean_array_uset(v_bs_x27_845_, v_i_839_, v___x_846_);
v_i_839_ = v___x_848_;
v_bs_840_ = v___x_849_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__13___boxed(lean_object* v_xs_851_, lean_object* v_sz_852_, lean_object* v_i_853_, lean_object* v_bs_854_){
_start:
{
size_t v_sz_boxed_855_; size_t v_i_boxed_856_; lean_object* v_res_857_; 
v_sz_boxed_855_ = lean_unbox_usize(v_sz_852_);
lean_dec(v_sz_852_);
v_i_boxed_856_ = lean_unbox_usize(v_i_853_);
lean_dec(v_i_853_);
v_res_857_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__13(v_xs_851_, v_sz_boxed_855_, v_i_boxed_856_, v_bs_854_);
lean_dec_ref(v_xs_851_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15___redArg(lean_object* v_xs_858_, lean_object* v_f_859_, lean_object* v_as_860_, lean_object* v_bs_861_, lean_object* v_i_862_, lean_object* v_cs_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_){
_start:
{
lean_object* v___x_869_; uint8_t v___x_870_; 
v___x_869_ = lean_array_get_size(v_as_860_);
v___x_870_ = lean_nat_dec_lt(v_i_862_, v___x_869_);
if (v___x_870_ == 0)
{
lean_object* v___x_871_; 
lean_dec(v_i_862_);
lean_dec_ref(v_f_859_);
v___x_871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_871_, 0, v_cs_863_);
return v___x_871_;
}
else
{
lean_object* v___x_872_; uint8_t v___x_873_; 
v___x_872_ = lean_array_get_size(v_bs_861_);
v___x_873_ = lean_nat_dec_lt(v_i_862_, v___x_872_);
if (v___x_873_ == 0)
{
lean_object* v___x_874_; 
lean_dec(v_i_862_);
lean_dec_ref(v_f_859_);
v___x_874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_874_, 0, v_cs_863_);
return v___x_874_;
}
else
{
lean_object* v_a_875_; lean_object* v_b_876_; size_t v_sz_877_; size_t v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; 
v_a_875_ = lean_array_fget_borrowed(v_as_860_, v_i_862_);
v_b_876_ = lean_array_fget_borrowed(v_bs_861_, v_i_862_);
v_sz_877_ = lean_array_size(v_b_876_);
v___x_878_ = ((size_t)0ULL);
lean_inc(v_b_876_);
v___x_879_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__13(v_xs_858_, v_sz_877_, v___x_878_, v_b_876_);
lean_inc_ref(v_f_859_);
lean_inc(v___y_867_);
lean_inc_ref(v___y_866_);
lean_inc(v___y_865_);
lean_inc_ref(v___y_864_);
lean_inc(v_a_875_);
v___x_880_ = lean_apply_7(v_f_859_, v_a_875_, v___x_879_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, lean_box(0));
if (lean_obj_tag(v___x_880_) == 0)
{
lean_object* v_a_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; 
v_a_881_ = lean_ctor_get(v___x_880_, 0);
lean_inc(v_a_881_);
lean_dec_ref(v___x_880_);
v___x_882_ = lean_unsigned_to_nat(1u);
v___x_883_ = lean_nat_add(v_i_862_, v___x_882_);
lean_dec(v_i_862_);
v___x_884_ = lean_array_push(v_cs_863_, v_a_881_);
v_i_862_ = v___x_883_;
v_cs_863_ = v___x_884_;
goto _start;
}
else
{
lean_object* v_a_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_893_; 
lean_dec_ref(v_cs_863_);
lean_dec(v_i_862_);
lean_dec_ref(v_f_859_);
v_a_886_ = lean_ctor_get(v___x_880_, 0);
v_isSharedCheck_893_ = !lean_is_exclusive(v___x_880_);
if (v_isSharedCheck_893_ == 0)
{
v___x_888_ = v___x_880_;
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_a_886_);
lean_dec(v___x_880_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v___x_891_; 
if (v_isShared_889_ == 0)
{
v___x_891_ = v___x_888_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v_a_886_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
return v___x_891_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15___redArg___boxed(lean_object* v_xs_894_, lean_object* v_f_895_, lean_object* v_as_896_, lean_object* v_bs_897_, lean_object* v_i_898_, lean_object* v_cs_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_){
_start:
{
lean_object* v_res_905_; 
v_res_905_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15___redArg(v_xs_894_, v_f_895_, v_as_896_, v_bs_897_, v_i_898_, v_cs_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_);
lean_dec(v___y_903_);
lean_dec_ref(v___y_902_);
lean_dec(v___y_901_);
lean_dec_ref(v___y_900_);
lean_dec_ref(v_bs_897_);
lean_dec_ref(v_as_896_);
lean_dec_ref(v_xs_894_);
return v_res_905_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; 
v___x_909_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__2));
v___x_910_ = lean_unsigned_to_nat(2u);
v___x_911_ = lean_unsigned_to_nat(73u);
v___x_912_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__1));
v___x_913_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__0));
v___x_914_ = l_mkPanicMessageWithDecl(v___x_913_, v___x_912_, v___x_911_, v___x_910_, v___x_909_);
return v___x_914_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_916_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__4));
v___x_917_ = lean_unsigned_to_nat(2u);
v___x_918_ = lean_unsigned_to_nat(74u);
v___x_919_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__1));
v___x_920_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__0));
v___x_921_ = l_mkPanicMessageWithDecl(v___x_920_, v___x_919_, v___x_918_, v___x_917_, v___x_916_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg(lean_object* v_f_924_, lean_object* v_positions_925_, lean_object* v_ys_926_, lean_object* v_xs_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_){
_start:
{
lean_object* v___x_933_; lean_object* v___x_934_; uint8_t v___x_935_; 
v___x_933_ = lean_array_get_size(v_positions_925_);
v___x_934_ = lean_array_get_size(v_ys_926_);
v___x_935_ = lean_nat_dec_eq(v___x_933_, v___x_934_);
if (v___x_935_ == 0)
{
lean_object* v___x_936_; lean_object* v___x_937_; 
lean_dec_ref(v_f_924_);
v___x_936_ = lean_obj_once(&l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__3, &l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__3_once, _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__3);
v___x_937_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg(v___x_936_, v___y_928_, v___y_929_, v___y_930_, v___y_931_);
return v___x_937_;
}
else
{
lean_object* v___x_938_; lean_object* v___x_939_; uint8_t v___x_940_; 
v___x_938_ = l_Lean_Elab_Structural_Positions_numIndices(v_positions_925_);
v___x_939_ = lean_array_get_size(v_xs_927_);
v___x_940_ = lean_nat_dec_eq(v___x_938_, v___x_939_);
lean_dec(v___x_938_);
if (v___x_940_ == 0)
{
lean_object* v___x_941_; lean_object* v___x_942_; 
lean_dec_ref(v_f_924_);
v___x_941_ = lean_obj_once(&l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__5, &l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__5_once, _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__5);
v___x_942_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg(v___x_941_, v___y_928_, v___y_929_, v___y_930_, v___y_931_);
return v___x_942_;
}
else
{
lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_943_ = lean_unsigned_to_nat(0u);
v___x_944_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__6));
v___x_945_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15___redArg(v_xs_927_, v_f_924_, v_ys_926_, v_positions_925_, v___x_943_, v___x_944_, v___y_928_, v___y_929_, v___y_930_, v___y_931_);
return v___x_945_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___boxed(lean_object* v_f_946_, lean_object* v_positions_947_, lean_object* v_ys_948_, lean_object* v_xs_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_){
_start:
{
lean_object* v_res_955_; 
v_res_955_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg(v_f_946_, v_positions_947_, v_ys_948_, v_xs_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_);
lean_dec(v___y_953_);
lean_dec_ref(v___y_952_);
lean_dec(v___y_951_);
lean_dec_ref(v___y_950_);
lean_dec_ref(v_xs_949_);
lean_dec_ref(v_ys_948_);
lean_dec_ref(v_positions_947_);
return v_res_955_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg(lean_object* v___x_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_funTypes_959_, lean_object* v_as_960_, lean_object* v_i_961_, lean_object* v_j_962_, lean_object* v_bs_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_){
_start:
{
lean_object* v_zero_969_; uint8_t v_isZero_970_; 
v_zero_969_ = lean_unsigned_to_nat(0u);
v_isZero_970_ = lean_nat_dec_eq(v_i_961_, v_zero_969_);
if (v_isZero_970_ == 1)
{
lean_object* v___x_971_; 
lean_dec(v_j_962_);
lean_dec(v_i_961_);
lean_dec_ref(v_funTypes_959_);
lean_dec_ref(v_a_958_);
lean_dec_ref(v_a_957_);
lean_dec_ref(v___x_956_);
v___x_971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_971_, 0, v_bs_963_);
return v___x_971_;
}
else
{
lean_object* v___x_972_; lean_object* v_fst_973_; lean_object* v_snd_974_; lean_object* v___x_975_; 
v___x_972_ = lean_array_fget_borrowed(v_as_960_, v_j_962_);
v_fst_973_ = lean_ctor_get(v___x_972_, 0);
v_snd_974_ = lean_ctor_get(v___x_972_, 1);
lean_inc(v_snd_974_);
lean_inc(v_fst_973_);
lean_inc_ref(v_funTypes_959_);
lean_inc_ref(v_a_958_);
lean_inc_ref(v_a_957_);
lean_inc(v_j_962_);
lean_inc_ref(v___x_956_);
v___x_975_ = l_Lean_Elab_Structural_mkBRecOnApp(v___x_956_, v_j_962_, v_a_957_, v_a_958_, v_funTypes_959_, v_fst_973_, v_snd_974_, v___y_964_, v___y_965_, v___y_966_, v___y_967_);
if (lean_obj_tag(v___x_975_) == 0)
{
lean_object* v_a_976_; lean_object* v_one_977_; lean_object* v_n_978_; lean_object* v___x_979_; lean_object* v___x_980_; 
v_a_976_ = lean_ctor_get(v___x_975_, 0);
lean_inc(v_a_976_);
lean_dec_ref(v___x_975_);
v_one_977_ = lean_unsigned_to_nat(1u);
v_n_978_ = lean_nat_sub(v_i_961_, v_one_977_);
lean_dec(v_i_961_);
v___x_979_ = lean_nat_add(v_j_962_, v_one_977_);
lean_dec(v_j_962_);
v___x_980_ = lean_array_push(v_bs_963_, v_a_976_);
v_i_961_ = v_n_978_;
v_j_962_ = v___x_979_;
v_bs_963_ = v___x_980_;
goto _start;
}
else
{
lean_object* v_a_982_; lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_989_; 
lean_dec_ref(v_bs_963_);
lean_dec(v_j_962_);
lean_dec(v_i_961_);
lean_dec_ref(v_funTypes_959_);
lean_dec_ref(v_a_958_);
lean_dec_ref(v_a_957_);
lean_dec_ref(v___x_956_);
v_a_982_ = lean_ctor_get(v___x_975_, 0);
v_isSharedCheck_989_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_989_ == 0)
{
v___x_984_ = v___x_975_;
v_isShared_985_ = v_isSharedCheck_989_;
goto v_resetjp_983_;
}
else
{
lean_inc(v_a_982_);
lean_dec(v___x_975_);
v___x_984_ = lean_box(0);
v_isShared_985_ = v_isSharedCheck_989_;
goto v_resetjp_983_;
}
v_resetjp_983_:
{
lean_object* v___x_987_; 
if (v_isShared_985_ == 0)
{
v___x_987_ = v___x_984_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v_a_982_);
v___x_987_ = v_reuseFailAlloc_988_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
return v___x_987_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg___boxed(lean_object* v___x_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_funTypes_993_, lean_object* v_as_994_, lean_object* v_i_995_, lean_object* v_j_996_, lean_object* v_bs_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_){
_start:
{
lean_object* v_res_1003_; 
v_res_1003_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg(v___x_990_, v_a_991_, v_a_992_, v_funTypes_993_, v_as_994_, v_i_995_, v_j_996_, v_bs_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_);
lean_dec(v___y_1001_);
lean_dec_ref(v___y_1000_);
lean_dec(v___y_999_);
lean_dec_ref(v___y_998_);
lean_dec_ref(v_as_994_);
return v_res_1003_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16_spec__29___redArg(lean_object* v_declName_1004_, uint8_t v_s_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_){
_start:
{
lean_object* v___x_1009_; lean_object* v_env_1010_; lean_object* v_nextMacroScope_1011_; lean_object* v_ngen_1012_; lean_object* v_auxDeclNGen_1013_; lean_object* v_traceState_1014_; lean_object* v_messages_1015_; lean_object* v_infoState_1016_; lean_object* v_snapshotTasks_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1046_; 
v___x_1009_ = lean_st_ref_take(v___y_1007_);
v_env_1010_ = lean_ctor_get(v___x_1009_, 0);
v_nextMacroScope_1011_ = lean_ctor_get(v___x_1009_, 1);
v_ngen_1012_ = lean_ctor_get(v___x_1009_, 2);
v_auxDeclNGen_1013_ = lean_ctor_get(v___x_1009_, 3);
v_traceState_1014_ = lean_ctor_get(v___x_1009_, 4);
v_messages_1015_ = lean_ctor_get(v___x_1009_, 6);
v_infoState_1016_ = lean_ctor_get(v___x_1009_, 7);
v_snapshotTasks_1017_ = lean_ctor_get(v___x_1009_, 8);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_1009_);
if (v_isSharedCheck_1046_ == 0)
{
lean_object* v_unused_1047_; 
v_unused_1047_ = lean_ctor_get(v___x_1009_, 5);
lean_dec(v_unused_1047_);
v___x_1019_ = v___x_1009_;
v_isShared_1020_ = v_isSharedCheck_1046_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_snapshotTasks_1017_);
lean_inc(v_infoState_1016_);
lean_inc(v_messages_1015_);
lean_inc(v_traceState_1014_);
lean_inc(v_auxDeclNGen_1013_);
lean_inc(v_ngen_1012_);
lean_inc(v_nextMacroScope_1011_);
lean_inc(v_env_1010_);
lean_dec(v___x_1009_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1046_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
uint8_t v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1026_; 
v___x_1021_ = 0;
v___x_1022_ = lean_box(0);
v___x_1023_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_1010_, v_declName_1004_, v_s_1005_, v___x_1021_, v___x_1022_);
v___x_1024_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__24___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__24___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__24___redArg___closed__2);
if (v_isShared_1020_ == 0)
{
lean_ctor_set(v___x_1019_, 5, v___x_1024_);
lean_ctor_set(v___x_1019_, 0, v___x_1023_);
v___x_1026_ = v___x_1019_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v___x_1023_);
lean_ctor_set(v_reuseFailAlloc_1045_, 1, v_nextMacroScope_1011_);
lean_ctor_set(v_reuseFailAlloc_1045_, 2, v_ngen_1012_);
lean_ctor_set(v_reuseFailAlloc_1045_, 3, v_auxDeclNGen_1013_);
lean_ctor_set(v_reuseFailAlloc_1045_, 4, v_traceState_1014_);
lean_ctor_set(v_reuseFailAlloc_1045_, 5, v___x_1024_);
lean_ctor_set(v_reuseFailAlloc_1045_, 6, v_messages_1015_);
lean_ctor_set(v_reuseFailAlloc_1045_, 7, v_infoState_1016_);
lean_ctor_set(v_reuseFailAlloc_1045_, 8, v_snapshotTasks_1017_);
v___x_1026_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v_mctx_1029_; lean_object* v_zetaDeltaFVarIds_1030_; lean_object* v_postponed_1031_; lean_object* v_diag_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1043_; 
v___x_1027_ = lean_st_ref_set(v___y_1007_, v___x_1026_);
v___x_1028_ = lean_st_ref_take(v___y_1006_);
v_mctx_1029_ = lean_ctor_get(v___x_1028_, 0);
v_zetaDeltaFVarIds_1030_ = lean_ctor_get(v___x_1028_, 2);
v_postponed_1031_ = lean_ctor_get(v___x_1028_, 3);
v_diag_1032_ = lean_ctor_get(v___x_1028_, 4);
v_isSharedCheck_1043_ = !lean_is_exclusive(v___x_1028_);
if (v_isSharedCheck_1043_ == 0)
{
lean_object* v_unused_1044_; 
v_unused_1044_ = lean_ctor_get(v___x_1028_, 1);
lean_dec(v_unused_1044_);
v___x_1034_ = v___x_1028_;
v_isShared_1035_ = v_isSharedCheck_1043_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_diag_1032_);
lean_inc(v_postponed_1031_);
lean_inc(v_zetaDeltaFVarIds_1030_);
lean_inc(v_mctx_1029_);
lean_dec(v___x_1028_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1043_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v___x_1036_; lean_object* v___x_1038_; 
v___x_1036_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__24___redArg___closed__3, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__24___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__24___redArg___closed__3);
if (v_isShared_1035_ == 0)
{
lean_ctor_set(v___x_1034_, 1, v___x_1036_);
v___x_1038_ = v___x_1034_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v_mctx_1029_);
lean_ctor_set(v_reuseFailAlloc_1042_, 1, v___x_1036_);
lean_ctor_set(v_reuseFailAlloc_1042_, 2, v_zetaDeltaFVarIds_1030_);
lean_ctor_set(v_reuseFailAlloc_1042_, 3, v_postponed_1031_);
lean_ctor_set(v_reuseFailAlloc_1042_, 4, v_diag_1032_);
v___x_1038_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; 
v___x_1039_ = lean_st_ref_set(v___y_1006_, v___x_1038_);
v___x_1040_ = lean_box(0);
v___x_1041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1040_);
return v___x_1041_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16_spec__29___redArg___boxed(lean_object* v_declName_1048_, lean_object* v_s_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_){
_start:
{
uint8_t v_s_boxed_1053_; lean_object* v_res_1054_; 
v_s_boxed_1053_ = lean_unbox(v_s_1049_);
v_res_1054_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16_spec__29___redArg(v_declName_1048_, v_s_boxed_1053_, v___y_1050_, v___y_1051_);
lean_dec(v___y_1051_);
lean_dec(v___y_1050_);
return v_res_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16(lean_object* v_declName_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_){
_start:
{
uint8_t v___x_1061_; lean_object* v___x_1062_; 
v___x_1061_ = 0;
v___x_1062_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16_spec__29___redArg(v_declName_1055_, v___x_1061_, v___y_1057_, v___y_1059_);
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16___boxed(lean_object* v_declName_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_){
_start:
{
lean_object* v_res_1069_; 
v_res_1069_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16(v_declName_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_);
lean_dec(v___y_1067_);
lean_dec_ref(v___y_1066_);
lean_dec(v___y_1065_);
lean_dec_ref(v___y_1064_);
return v_res_1069_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg(lean_object* v_xs_1073_, uint8_t v_a_1074_, lean_object* v_preDefs_1075_, lean_object* v___x_1076_, lean_object* v_as_1077_, lean_object* v_i_1078_, lean_object* v_j_1079_, lean_object* v_bs_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_){
_start:
{
lean_object* v_zero_1086_; uint8_t v_isZero_1087_; 
v_zero_1086_ = lean_unsigned_to_nat(0u);
v_isZero_1087_ = lean_nat_dec_eq(v_i_1078_, v_zero_1086_);
if (v_isZero_1087_ == 1)
{
lean_object* v___x_1088_; 
lean_dec(v_j_1079_);
lean_dec(v_i_1078_);
lean_dec(v___x_1076_);
v___x_1088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1088_, 0, v_bs_1080_);
return v___x_1088_;
}
else
{
uint8_t v___x_1089_; lean_object* v_one_1090_; lean_object* v_n_1091_; lean_object* v_a_1093_; lean_object* v___y_1098_; lean_object* v___x_1108_; uint8_t v___x_1109_; lean_object* v___x_1110_; 
v___x_1089_ = 1;
v_one_1090_ = lean_unsigned_to_nat(1u);
v_n_1091_ = lean_nat_sub(v_i_1078_, v_one_1090_);
lean_dec(v_i_1078_);
v___x_1108_ = lean_array_fget_borrowed(v_as_1077_, v_j_1079_);
v___x_1109_ = 1;
lean_inc(v___x_1108_);
v___x_1110_ = l_Lean_Meta_mkLambdaFVars(v_xs_1073_, v___x_1108_, v_a_1074_, v___x_1089_, v_a_1074_, v___x_1089_, v___x_1109_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_);
if (lean_obj_tag(v___x_1110_) == 0)
{
lean_object* v_a_1111_; lean_object* v___x_1112_; 
v_a_1111_ = lean_ctor_get(v___x_1110_, 0);
lean_inc(v_a_1111_);
lean_dec_ref(v___x_1110_);
v___x_1112_ = l_Lean_Elab_eraseRecAppSyntaxExpr(v_a_1111_, v___y_1083_, v___y_1084_);
if (lean_obj_tag(v___x_1112_) == 0)
{
lean_object* v_a_1113_; lean_object* v___x_1114_; 
v_a_1113_ = lean_ctor_get(v___x_1112_, 0);
lean_inc_n(v_a_1113_, 2);
lean_dec_ref(v___x_1112_);
lean_inc(v___y_1084_);
lean_inc_ref(v___y_1083_);
lean_inc(v___y_1082_);
lean_inc_ref(v___y_1081_);
v___x_1114_ = lean_infer_type(v_a_1113_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_);
if (lean_obj_tag(v___x_1114_) == 0)
{
lean_object* v_a_1115_; lean_object* v___x_1116_; 
v_a_1115_ = lean_ctor_get(v___x_1114_, 0);
lean_inc(v_a_1115_);
lean_dec_ref(v___x_1114_);
v___x_1116_ = l_Lean_Meta_letToHave(v_a_1115_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_);
if (lean_obj_tag(v___x_1116_) == 0)
{
lean_object* v_a_1117_; lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1191_; 
v_a_1117_ = lean_ctor_get(v___x_1116_, 0);
v_isSharedCheck_1191_ = !lean_is_exclusive(v___x_1116_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1119_ = v___x_1116_;
v_isShared_1120_ = v_isSharedCheck_1191_;
goto v_resetjp_1118_;
}
else
{
lean_inc(v_a_1117_);
lean_dec(v___x_1116_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1191_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v_modifiers_1124_; lean_object* v_levelParams_1125_; lean_object* v_declName_1126_; lean_object* v_env_1127_; uint8_t v_isUnsafe_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; uint32_t v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; uint8_t v___y_1135_; 
v___x_1121_ = lean_st_ref_get(v___y_1084_);
v___x_1122_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_1123_ = lean_array_get_borrowed(v___x_1122_, v_preDefs_1075_, v_j_1079_);
v_modifiers_1124_ = lean_ctor_get(v___x_1123_, 2);
v_levelParams_1125_ = lean_ctor_get(v___x_1123_, 1);
v_declName_1126_ = lean_ctor_get(v___x_1123_, 3);
v_env_1127_ = lean_ctor_get(v___x_1121_, 0);
lean_inc_ref(v_env_1127_);
lean_dec(v___x_1121_);
v_isUnsafe_1128_ = lean_ctor_get_uint8(v_modifiers_1124_, sizeof(void*)*3 + 4);
v___x_1129_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg___closed__1));
lean_inc(v_declName_1126_);
v___x_1130_ = l_Lean_Name_append(v_declName_1126_, v___x_1129_);
lean_inc(v_a_1113_);
v___x_1131_ = l_Lean_getMaxHeight(v_env_1127_, v_a_1113_);
lean_inc(v_levelParams_1125_);
lean_inc(v___x_1130_);
v___x_1132_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1132_, 0, v___x_1130_);
lean_ctor_set(v___x_1132_, 1, v_levelParams_1125_);
lean_ctor_set(v___x_1132_, 2, v_a_1117_);
v___x_1133_ = lean_box(1);
if (v_isUnsafe_1128_ == 0)
{
uint8_t v___x_1189_; 
v___x_1189_ = 1;
v___y_1135_ = v___x_1189_;
goto v___jp_1134_;
}
else
{
uint8_t v___x_1190_; 
v___x_1190_ = 0;
v___y_1135_ = v___x_1190_;
goto v___jp_1134_;
}
v___jp_1134_:
{
lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1140_; 
v___x_1136_ = lean_box(0);
lean_inc(v___x_1130_);
v___x_1137_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1137_, 0, v___x_1130_);
lean_ctor_set(v___x_1137_, 1, v___x_1136_);
v___x_1138_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1138_, 0, v___x_1132_);
lean_ctor_set(v___x_1138_, 1, v_a_1113_);
lean_ctor_set(v___x_1138_, 2, v___x_1133_);
lean_ctor_set(v___x_1138_, 3, v___x_1137_);
lean_ctor_set_uint8(v___x_1138_, sizeof(void*)*4, v___y_1135_);
if (v_isShared_1120_ == 0)
{
lean_ctor_set_tag(v___x_1119_, 1);
lean_ctor_set(v___x_1119_, 0, v___x_1138_);
v___x_1140_ = v___x_1119_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v___x_1138_);
v___x_1140_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
lean_object* v___x_1141_; 
v___x_1141_ = l_Lean_addDecl(v___x_1140_, v_a_1074_, v___y_1083_, v___y_1084_);
if (lean_obj_tag(v___x_1141_) == 0)
{
lean_object* v___x_1142_; lean_object* v_env_1143_; lean_object* v_nextMacroScope_1144_; lean_object* v_ngen_1145_; lean_object* v_auxDeclNGen_1146_; lean_object* v_traceState_1147_; lean_object* v_messages_1148_; lean_object* v_infoState_1149_; lean_object* v_snapshotTasks_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1178_; 
lean_dec_ref(v___x_1141_);
v___x_1142_ = lean_st_ref_take(v___y_1084_);
v_env_1143_ = lean_ctor_get(v___x_1142_, 0);
v_nextMacroScope_1144_ = lean_ctor_get(v___x_1142_, 1);
v_ngen_1145_ = lean_ctor_get(v___x_1142_, 2);
v_auxDeclNGen_1146_ = lean_ctor_get(v___x_1142_, 3);
v_traceState_1147_ = lean_ctor_get(v___x_1142_, 4);
v_messages_1148_ = lean_ctor_get(v___x_1142_, 6);
v_infoState_1149_ = lean_ctor_get(v___x_1142_, 7);
v_snapshotTasks_1150_ = lean_ctor_get(v___x_1142_, 8);
v_isSharedCheck_1178_ = !lean_is_exclusive(v___x_1142_);
if (v_isSharedCheck_1178_ == 0)
{
lean_object* v_unused_1179_; 
v_unused_1179_ = lean_ctor_get(v___x_1142_, 5);
lean_dec(v_unused_1179_);
v___x_1152_ = v___x_1142_;
v_isShared_1153_ = v_isSharedCheck_1178_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_snapshotTasks_1150_);
lean_inc(v_infoState_1149_);
lean_inc(v_messages_1148_);
lean_inc(v_traceState_1147_);
lean_inc(v_auxDeclNGen_1146_);
lean_inc(v_ngen_1145_);
lean_inc(v_nextMacroScope_1144_);
lean_inc(v_env_1143_);
lean_dec(v___x_1142_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1178_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1157_; 
lean_inc(v___x_1130_);
v___x_1154_ = l_Lean_setDefHeightOverride(v_env_1143_, v___x_1130_, v___x_1131_);
v___x_1155_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__24___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__24___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__24___redArg___closed__2);
if (v_isShared_1153_ == 0)
{
lean_ctor_set(v___x_1152_, 5, v___x_1155_);
lean_ctor_set(v___x_1152_, 0, v___x_1154_);
v___x_1157_ = v___x_1152_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v___x_1154_);
lean_ctor_set(v_reuseFailAlloc_1177_, 1, v_nextMacroScope_1144_);
lean_ctor_set(v_reuseFailAlloc_1177_, 2, v_ngen_1145_);
lean_ctor_set(v_reuseFailAlloc_1177_, 3, v_auxDeclNGen_1146_);
lean_ctor_set(v_reuseFailAlloc_1177_, 4, v_traceState_1147_);
lean_ctor_set(v_reuseFailAlloc_1177_, 5, v___x_1155_);
lean_ctor_set(v_reuseFailAlloc_1177_, 6, v_messages_1148_);
lean_ctor_set(v_reuseFailAlloc_1177_, 7, v_infoState_1149_);
lean_ctor_set(v_reuseFailAlloc_1177_, 8, v_snapshotTasks_1150_);
v___x_1157_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v_mctx_1160_; lean_object* v_zetaDeltaFVarIds_1161_; lean_object* v_postponed_1162_; lean_object* v_diag_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1175_; 
v___x_1158_ = lean_st_ref_set(v___y_1084_, v___x_1157_);
v___x_1159_ = lean_st_ref_take(v___y_1082_);
v_mctx_1160_ = lean_ctor_get(v___x_1159_, 0);
v_zetaDeltaFVarIds_1161_ = lean_ctor_get(v___x_1159_, 2);
v_postponed_1162_ = lean_ctor_get(v___x_1159_, 3);
v_diag_1163_ = lean_ctor_get(v___x_1159_, 4);
v_isSharedCheck_1175_ = !lean_is_exclusive(v___x_1159_);
if (v_isSharedCheck_1175_ == 0)
{
lean_object* v_unused_1176_; 
v_unused_1176_ = lean_ctor_get(v___x_1159_, 1);
lean_dec(v_unused_1176_);
v___x_1165_ = v___x_1159_;
v_isShared_1166_ = v_isSharedCheck_1175_;
goto v_resetjp_1164_;
}
else
{
lean_inc(v_diag_1163_);
lean_inc(v_postponed_1162_);
lean_inc(v_zetaDeltaFVarIds_1161_);
lean_inc(v_mctx_1160_);
lean_dec(v___x_1159_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1175_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
lean_object* v___x_1167_; lean_object* v___x_1169_; 
v___x_1167_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__24___redArg___closed__3, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__24___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__24___redArg___closed__3);
if (v_isShared_1166_ == 0)
{
lean_ctor_set(v___x_1165_, 1, v___x_1167_);
v___x_1169_ = v___x_1165_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v_mctx_1160_);
lean_ctor_set(v_reuseFailAlloc_1174_, 1, v___x_1167_);
lean_ctor_set(v_reuseFailAlloc_1174_, 2, v_zetaDeltaFVarIds_1161_);
lean_ctor_set(v_reuseFailAlloc_1174_, 3, v_postponed_1162_);
lean_ctor_set(v_reuseFailAlloc_1174_, 4, v_diag_1163_);
v___x_1169_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; 
v___x_1170_ = lean_st_ref_set(v___y_1082_, v___x_1169_);
lean_inc(v___x_1130_);
v___x_1171_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16(v___x_1130_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_);
lean_dec_ref(v___x_1171_);
lean_inc(v___x_1076_);
v___x_1172_ = l_Lean_mkConst(v___x_1130_, v___x_1076_);
v___x_1173_ = l_Lean_mkAppN(v___x_1172_, v_xs_1073_);
v_a_1093_ = v___x_1173_;
goto v___jp_1092_;
}
}
}
}
}
else
{
lean_object* v_a_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1187_; 
lean_dec(v___x_1130_);
lean_dec(v_n_1091_);
lean_dec_ref(v_bs_1080_);
lean_dec(v_j_1079_);
lean_dec(v___x_1076_);
v_a_1180_ = lean_ctor_get(v___x_1141_, 0);
v_isSharedCheck_1187_ = !lean_is_exclusive(v___x_1141_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1182_ = v___x_1141_;
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_a_1180_);
lean_dec(v___x_1141_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v___x_1185_; 
if (v_isShared_1183_ == 0)
{
v___x_1185_ = v___x_1182_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v_a_1180_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
return v___x_1185_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_1113_);
v___y_1098_ = v___x_1116_;
goto v___jp_1097_;
}
}
else
{
lean_dec(v_a_1113_);
v___y_1098_ = v___x_1114_;
goto v___jp_1097_;
}
}
else
{
v___y_1098_ = v___x_1112_;
goto v___jp_1097_;
}
}
else
{
v___y_1098_ = v___x_1110_;
goto v___jp_1097_;
}
v___jp_1092_:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___x_1094_ = lean_nat_add(v_j_1079_, v_one_1090_);
lean_dec(v_j_1079_);
v___x_1095_ = lean_array_push(v_bs_1080_, v_a_1093_);
v_i_1078_ = v_n_1091_;
v_j_1079_ = v___x_1094_;
v_bs_1080_ = v___x_1095_;
goto _start;
}
v___jp_1097_:
{
if (lean_obj_tag(v___y_1098_) == 0)
{
lean_object* v_a_1099_; 
v_a_1099_ = lean_ctor_get(v___y_1098_, 0);
lean_inc(v_a_1099_);
lean_dec_ref(v___y_1098_);
v_a_1093_ = v_a_1099_;
goto v___jp_1092_;
}
else
{
lean_object* v_a_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1107_; 
lean_dec(v_n_1091_);
lean_dec_ref(v_bs_1080_);
lean_dec(v_j_1079_);
lean_dec(v___x_1076_);
v_a_1100_ = lean_ctor_get(v___y_1098_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___y_1098_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1102_ = v___y_1098_;
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_a_1100_);
lean_dec(v___y_1098_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1105_; 
if (v_isShared_1103_ == 0)
{
v___x_1105_ = v___x_1102_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_a_1100_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg___boxed(lean_object* v_xs_1192_, lean_object* v_a_1193_, lean_object* v_preDefs_1194_, lean_object* v___x_1195_, lean_object* v_as_1196_, lean_object* v_i_1197_, lean_object* v_j_1198_, lean_object* v_bs_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_){
_start:
{
uint8_t v_a_28466__boxed_1205_; lean_object* v_res_1206_; 
v_a_28466__boxed_1205_ = lean_unbox(v_a_1193_);
v_res_1206_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg(v_xs_1192_, v_a_28466__boxed_1205_, v_preDefs_1194_, v___x_1195_, v_as_1196_, v_i_1197_, v_j_1198_, v_bs_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_);
lean_dec(v___y_1203_);
lean_dec_ref(v___y_1202_);
lean_dec(v___y_1201_);
lean_dec_ref(v___y_1200_);
lean_dec_ref(v_as_1196_);
lean_dec_ref(v_preDefs_1194_);
lean_dec_ref(v_xs_1192_);
return v_res_1206_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__2(void){
_start:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; 
v___x_1210_ = lean_box(0);
v___x_1211_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__1));
v___x_1212_ = l_Lean_Expr_const___override(v___x_1211_, v___x_1210_);
return v___x_1212_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__4(void){
_start:
{
lean_object* v___x_1214_; lean_object* v___x_1215_; 
v___x_1214_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__3));
v___x_1215_ = l_Lean_stringToMessageData(v___x_1214_);
return v___x_1215_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__6(void){
_start:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1217_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__5));
v___x_1218_ = l_Lean_stringToMessageData(v___x_1217_);
return v___x_1218_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__8(void){
_start:
{
lean_object* v___x_1220_; lean_object* v___x_1221_; 
v___x_1220_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__7));
v___x_1221_ = l_Lean_stringToMessageData(v___x_1220_);
return v___x_1221_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__10(void){
_start:
{
lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___x_1223_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__9));
v___x_1224_ = l_Lean_stringToMessageData(v___x_1223_);
return v___x_1224_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__12(void){
_start:
{
lean_object* v___x_1226_; lean_object* v___x_1227_; 
v___x_1226_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__11));
v___x_1227_ = l_Lean_stringToMessageData(v___x_1226_);
return v___x_1227_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2(lean_object* v___f_1228_, lean_object* v_recArgInfos_1229_, lean_object* v_a_1230_, lean_object* v___x_1231_, lean_object* v___x_1232_, lean_object* v_fixedParamPerms_1233_, lean_object* v_xs_1234_, lean_object* v_preDefs_1235_, lean_object* v_numIndices_1236_, lean_object* v___f_1237_, lean_object* v___x_1238_, uint8_t v_a_1239_, lean_object* v_funTypes_1240_, lean_object* v_motives_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_){
_start:
{
lean_object* v___y_1248_; lean_object* v___y_1249_; lean_object* v___y_1250_; lean_object* v___y_1251_; lean_object* v___y_1252_; lean_object* v___y_1253_; lean_object* v___y_1290_; lean_object* v_FArgs_1291_; lean_object* v___y_1292_; lean_object* v___y_1293_; lean_object* v___y_1294_; lean_object* v___y_1295_; lean_object* v___y_1346_; lean_object* v___y_1347_; lean_object* v___y_1348_; lean_object* v___y_1349_; lean_object* v___y_1350_; lean_object* v___y_1351_; lean_object* v___y_1370_; lean_object* v___y_1371_; lean_object* v___y_1372_; lean_object* v___y_1373_; lean_object* v___y_1374_; lean_object* v___y_1375_; lean_object* v___y_1415_; lean_object* v___y_1416_; lean_object* v___y_1417_; lean_object* v___y_1418_; lean_object* v___x_1465_; 
lean_inc_ref(v___f_1228_);
lean_inc(v___y_1245_);
lean_inc_ref(v___y_1244_);
lean_inc(v___y_1243_);
lean_inc_ref(v___y_1242_);
v___x_1465_ = lean_apply_5(v___f_1228_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, lean_box(0));
if (lean_obj_tag(v___x_1465_) == 0)
{
lean_object* v_a_1466_; uint8_t v___x_1467_; 
v_a_1466_ = lean_ctor_get(v___x_1465_, 0);
lean_inc(v_a_1466_);
lean_dec_ref(v___x_1465_);
v___x_1467_ = lean_unbox(v_a_1466_);
lean_dec(v_a_1466_);
if (v___x_1467_ == 0)
{
v___y_1415_ = v___y_1242_;
v___y_1416_ = v___y_1243_;
v___y_1417_ = v___y_1244_;
v___y_1418_ = v___y_1245_;
goto v___jp_1414_;
}
else
{
lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; 
v___x_1468_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__10, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__10);
lean_inc_ref(v_funTypes_1240_);
v___x_1469_ = lean_array_to_list(v_funTypes_1240_);
v___x_1470_ = lean_box(0);
v___x_1471_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_1469_, v___x_1470_);
v___x_1472_ = l_Lean_MessageData_ofList(v___x_1471_);
v___x_1473_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1473_, 0, v___x_1468_);
lean_ctor_set(v___x_1473_, 1, v___x_1472_);
v___x_1474_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__12, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__12_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__12);
v___x_1475_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1475_, 0, v___x_1473_);
lean_ctor_set(v___x_1475_, 1, v___x_1474_);
lean_inc_ref(v_motives_1241_);
v___x_1476_ = lean_array_to_list(v_motives_1241_);
v___x_1477_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_1476_, v___x_1470_);
v___x_1478_ = l_Lean_MessageData_ofList(v___x_1477_);
v___x_1479_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1479_, 0, v___x_1475_);
lean_ctor_set(v___x_1479_, 1, v___x_1478_);
lean_inc(v___x_1238_);
v___x_1480_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_1238_, v___x_1479_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_);
if (lean_obj_tag(v___x_1480_) == 0)
{
lean_dec_ref(v___x_1480_);
v___y_1415_ = v___y_1242_;
v___y_1416_ = v___y_1243_;
v___y_1417_ = v___y_1244_;
v___y_1418_ = v___y_1245_;
goto v___jp_1414_;
}
else
{
lean_object* v_a_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1488_; 
lean_dec_ref(v_motives_1241_);
lean_dec_ref(v_funTypes_1240_);
lean_dec(v___x_1238_);
lean_dec_ref(v___f_1237_);
lean_dec_ref(v_preDefs_1235_);
lean_dec_ref(v_xs_1234_);
lean_dec_ref(v_fixedParamPerms_1233_);
lean_dec(v___x_1232_);
lean_dec_ref(v___x_1231_);
lean_dec_ref(v_recArgInfos_1229_);
lean_dec_ref(v___f_1228_);
v_a_1481_ = lean_ctor_get(v___x_1480_, 0);
v_isSharedCheck_1488_ = !lean_is_exclusive(v___x_1480_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1483_ = v___x_1480_;
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_a_1481_);
lean_dec(v___x_1480_);
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
}
else
{
lean_object* v_a_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1496_; 
lean_dec_ref(v_motives_1241_);
lean_dec_ref(v_funTypes_1240_);
lean_dec(v___x_1238_);
lean_dec_ref(v___f_1237_);
lean_dec_ref(v_preDefs_1235_);
lean_dec_ref(v_xs_1234_);
lean_dec_ref(v_fixedParamPerms_1233_);
lean_dec(v___x_1232_);
lean_dec_ref(v___x_1231_);
lean_dec_ref(v_recArgInfos_1229_);
lean_dec_ref(v___f_1228_);
v_a_1489_ = lean_ctor_get(v___x_1465_, 0);
v_isSharedCheck_1496_ = !lean_is_exclusive(v___x_1465_);
if (v_isSharedCheck_1496_ == 0)
{
v___x_1491_ = v___x_1465_;
v_isShared_1492_ = v_isSharedCheck_1496_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_a_1489_);
lean_dec(v___x_1465_);
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
v___jp_1247_:
{
lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; 
v___x_1254_ = l_Array_zip___redArg(v_recArgInfos_1229_, v_a_1230_);
lean_dec_ref(v_recArgInfos_1229_);
v___x_1255_ = lean_array_get_size(v___x_1254_);
v___x_1256_ = lean_mk_empty_array_with_capacity(v___x_1255_);
lean_inc(v___x_1232_);
v___x_1257_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg(v___x_1231_, v___y_1249_, v___y_1248_, v_funTypes_1240_, v___x_1254_, v___x_1255_, v___x_1232_, v___x_1256_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_);
lean_dec_ref(v___x_1254_);
if (lean_obj_tag(v___x_1257_) == 0)
{
lean_object* v_a_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; 
v_a_1258_ = lean_ctor_get(v___x_1257_, 0);
lean_inc(v_a_1258_);
lean_dec_ref(v___x_1257_);
v___x_1259_ = l_Array_zip___redArg(v_a_1230_, v_a_1258_);
lean_dec(v_a_1258_);
v___x_1260_ = lean_array_get_size(v___x_1259_);
v___x_1261_ = lean_mk_empty_array_with_capacity(v___x_1260_);
lean_inc(v___x_1232_);
v___x_1262_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg(v_fixedParamPerms_1233_, v_xs_1234_, v___x_1259_, v___x_1260_, v___x_1232_, v___x_1261_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_);
lean_dec_ref(v___x_1259_);
if (lean_obj_tag(v___x_1262_) == 0)
{
lean_object* v_a_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1272_; 
v_a_1263_ = lean_ctor_get(v___x_1262_, 0);
v_isSharedCheck_1272_ = !lean_is_exclusive(v___x_1262_);
if (v_isSharedCheck_1272_ == 0)
{
v___x_1265_ = v___x_1262_;
v_isShared_1266_ = v_isSharedCheck_1272_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_a_1263_);
lean_dec(v___x_1262_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1272_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1270_; 
v___x_1267_ = lean_mk_empty_array_with_capacity(v___x_1232_);
v___x_1268_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9(v_preDefs_1235_, v_a_1263_, v___x_1232_, v___x_1267_);
lean_dec(v_a_1263_);
lean_dec_ref(v_preDefs_1235_);
if (v_isShared_1266_ == 0)
{
lean_ctor_set(v___x_1265_, 0, v___x_1268_);
v___x_1270_ = v___x_1265_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v___x_1268_);
v___x_1270_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
return v___x_1270_;
}
}
}
else
{
lean_object* v_a_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1280_; 
lean_dec_ref(v_preDefs_1235_);
lean_dec(v___x_1232_);
v_a_1273_ = lean_ctor_get(v___x_1262_, 0);
v_isSharedCheck_1280_ = !lean_is_exclusive(v___x_1262_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1275_ = v___x_1262_;
v_isShared_1276_ = v_isSharedCheck_1280_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_a_1273_);
lean_dec(v___x_1262_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1280_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v___x_1278_; 
if (v_isShared_1276_ == 0)
{
v___x_1278_ = v___x_1275_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v_a_1273_);
v___x_1278_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
return v___x_1278_;
}
}
}
}
else
{
lean_object* v_a_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1288_; 
lean_dec_ref(v_preDefs_1235_);
lean_dec_ref(v_xs_1234_);
lean_dec_ref(v_fixedParamPerms_1233_);
lean_dec(v___x_1232_);
v_a_1281_ = lean_ctor_get(v___x_1257_, 0);
v_isSharedCheck_1288_ = !lean_is_exclusive(v___x_1257_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1283_ = v___x_1257_;
v_isShared_1284_ = v_isSharedCheck_1288_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_a_1281_);
lean_dec(v___x_1257_);
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
v___jp_1289_:
{
lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; 
lean_inc_ref(v___y_1290_);
lean_inc(v___x_1232_);
v___x_1296_ = lean_apply_1(v___y_1290_, v___x_1232_);
v___x_1297_ = lean_unsigned_to_nat(1u);
v___x_1298_ = lean_nat_add(v_numIndices_1236_, v___x_1297_);
v___x_1299_ = lean_box(0);
v___x_1300_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__2);
v___x_1301_ = lean_mk_array(v___x_1298_, v___x_1300_);
v___x_1302_ = l_Lean_mkAppN(v___x_1296_, v___x_1301_);
lean_dec_ref(v___x_1301_);
v___x_1303_ = lean_array_get_size(v___x_1231_);
v___x_1304_ = l_Lean_Meta_inferArgumentTypesN(v___x_1303_, v___x_1302_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_);
if (lean_obj_tag(v___x_1304_) == 0)
{
lean_object* v_a_1305_; lean_object* v___x_1306_; 
v_a_1305_ = lean_ctor_get(v___x_1304_, 0);
lean_inc(v_a_1305_);
lean_dec_ref(v___x_1304_);
v___x_1306_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg(v___f_1237_, v___x_1231_, v_a_1305_, v_FArgs_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_);
lean_dec_ref(v_FArgs_1291_);
lean_dec(v_a_1305_);
if (lean_obj_tag(v___x_1306_) == 0)
{
lean_object* v_options_1307_; uint8_t v_hasTrace_1308_; 
v_options_1307_ = lean_ctor_get(v___y_1294_, 2);
v_hasTrace_1308_ = lean_ctor_get_uint8(v_options_1307_, sizeof(void*)*1);
if (v_hasTrace_1308_ == 0)
{
lean_object* v_a_1309_; 
lean_dec(v___x_1238_);
v_a_1309_ = lean_ctor_get(v___x_1306_, 0);
lean_inc(v_a_1309_);
lean_dec_ref(v___x_1306_);
v___y_1248_ = v_a_1309_;
v___y_1249_ = v___y_1290_;
v___y_1250_ = v___y_1292_;
v___y_1251_ = v___y_1293_;
v___y_1252_ = v___y_1294_;
v___y_1253_ = v___y_1295_;
goto v___jp_1247_;
}
else
{
lean_object* v_a_1310_; lean_object* v_inheritedTraceOptions_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; uint8_t v___x_1314_; 
v_a_1310_ = lean_ctor_get(v___x_1306_, 0);
lean_inc(v_a_1310_);
lean_dec_ref(v___x_1306_);
v_inheritedTraceOptions_1311_ = lean_ctor_get(v___y_1294_, 13);
v___x_1312_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0___closed__1));
lean_inc(v___x_1238_);
v___x_1313_ = l_Lean_Name_append(v___x_1312_, v___x_1238_);
v___x_1314_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1311_, v_options_1307_, v___x_1313_);
lean_dec(v___x_1313_);
if (v___x_1314_ == 0)
{
lean_dec(v___x_1238_);
v___y_1248_ = v_a_1310_;
v___y_1249_ = v___y_1290_;
v___y_1250_ = v___y_1292_;
v___y_1251_ = v___y_1293_;
v___y_1252_ = v___y_1294_;
v___y_1253_ = v___y_1295_;
goto v___jp_1247_;
}
else
{
lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; 
v___x_1315_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__4);
lean_inc(v_a_1310_);
v___x_1316_ = lean_array_to_list(v_a_1310_);
v___x_1317_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_1316_, v___x_1299_);
v___x_1318_ = l_Lean_MessageData_ofList(v___x_1317_);
v___x_1319_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1319_, 0, v___x_1315_);
lean_ctor_set(v___x_1319_, 1, v___x_1318_);
v___x_1320_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_1238_, v___x_1319_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_);
if (lean_obj_tag(v___x_1320_) == 0)
{
lean_dec_ref(v___x_1320_);
v___y_1248_ = v_a_1310_;
v___y_1249_ = v___y_1290_;
v___y_1250_ = v___y_1292_;
v___y_1251_ = v___y_1293_;
v___y_1252_ = v___y_1294_;
v___y_1253_ = v___y_1295_;
goto v___jp_1247_;
}
else
{
lean_object* v_a_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1328_; 
lean_dec(v_a_1310_);
lean_dec_ref(v___y_1290_);
lean_dec_ref(v_funTypes_1240_);
lean_dec_ref(v_preDefs_1235_);
lean_dec_ref(v_xs_1234_);
lean_dec_ref(v_fixedParamPerms_1233_);
lean_dec(v___x_1232_);
lean_dec_ref(v___x_1231_);
lean_dec_ref(v_recArgInfos_1229_);
v_a_1321_ = lean_ctor_get(v___x_1320_, 0);
v_isSharedCheck_1328_ = !lean_is_exclusive(v___x_1320_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1323_ = v___x_1320_;
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_a_1321_);
lean_dec(v___x_1320_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___x_1326_; 
if (v_isShared_1324_ == 0)
{
v___x_1326_ = v___x_1323_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v_a_1321_);
v___x_1326_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
return v___x_1326_;
}
}
}
}
}
}
else
{
lean_object* v_a_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1336_; 
lean_dec_ref(v___y_1290_);
lean_dec_ref(v_funTypes_1240_);
lean_dec(v___x_1238_);
lean_dec_ref(v_preDefs_1235_);
lean_dec_ref(v_xs_1234_);
lean_dec_ref(v_fixedParamPerms_1233_);
lean_dec(v___x_1232_);
lean_dec_ref(v___x_1231_);
lean_dec_ref(v_recArgInfos_1229_);
v_a_1329_ = lean_ctor_get(v___x_1306_, 0);
v_isSharedCheck_1336_ = !lean_is_exclusive(v___x_1306_);
if (v_isSharedCheck_1336_ == 0)
{
v___x_1331_ = v___x_1306_;
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_a_1329_);
lean_dec(v___x_1306_);
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
else
{
lean_object* v_a_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1344_; 
lean_dec_ref(v_FArgs_1291_);
lean_dec_ref(v___y_1290_);
lean_dec_ref(v_funTypes_1240_);
lean_dec(v___x_1238_);
lean_dec_ref(v___f_1237_);
lean_dec_ref(v_preDefs_1235_);
lean_dec_ref(v_xs_1234_);
lean_dec_ref(v_fixedParamPerms_1233_);
lean_dec(v___x_1232_);
lean_dec_ref(v___x_1231_);
lean_dec_ref(v_recArgInfos_1229_);
v_a_1337_ = lean_ctor_get(v___x_1304_, 0);
v_isSharedCheck_1344_ = !lean_is_exclusive(v___x_1304_);
if (v_isSharedCheck_1344_ == 0)
{
v___x_1339_ = v___x_1304_;
v_isShared_1340_ = v_isSharedCheck_1344_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_a_1337_);
lean_dec(v___x_1304_);
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
v___jp_1345_:
{
if (v_a_1239_ == 0)
{
lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v_levelParams_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; 
v___x_1352_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_1353_ = lean_array_get_borrowed(v___x_1352_, v_preDefs_1235_, v___x_1232_);
v_levelParams_1354_ = lean_ctor_get(v___x_1353_, 1);
v___x_1355_ = lean_box(0);
lean_inc(v_levelParams_1354_);
v___x_1356_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__15(v_levelParams_1354_, v___x_1355_);
v___x_1357_ = lean_array_get_size(v___y_1346_);
v___x_1358_ = lean_mk_empty_array_with_capacity(v___x_1357_);
lean_inc(v___x_1232_);
v___x_1359_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg(v_xs_1234_, v_a_1239_, v_preDefs_1235_, v___x_1356_, v___y_1346_, v___x_1357_, v___x_1232_, v___x_1358_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_);
lean_dec_ref(v___y_1346_);
if (lean_obj_tag(v___x_1359_) == 0)
{
lean_object* v_a_1360_; 
v_a_1360_ = lean_ctor_get(v___x_1359_, 0);
lean_inc(v_a_1360_);
lean_dec_ref(v___x_1359_);
v___y_1290_ = v___y_1347_;
v_FArgs_1291_ = v_a_1360_;
v___y_1292_ = v___y_1348_;
v___y_1293_ = v___y_1349_;
v___y_1294_ = v___y_1350_;
v___y_1295_ = v___y_1351_;
goto v___jp_1289_;
}
else
{
lean_object* v_a_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1368_; 
lean_dec_ref(v___y_1347_);
lean_dec_ref(v_funTypes_1240_);
lean_dec(v___x_1238_);
lean_dec_ref(v___f_1237_);
lean_dec_ref(v_preDefs_1235_);
lean_dec_ref(v_xs_1234_);
lean_dec_ref(v_fixedParamPerms_1233_);
lean_dec(v___x_1232_);
lean_dec_ref(v___x_1231_);
lean_dec_ref(v_recArgInfos_1229_);
v_a_1361_ = lean_ctor_get(v___x_1359_, 0);
v_isSharedCheck_1368_ = !lean_is_exclusive(v___x_1359_);
if (v_isSharedCheck_1368_ == 0)
{
v___x_1363_ = v___x_1359_;
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_a_1361_);
lean_dec(v___x_1359_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v___x_1366_; 
if (v_isShared_1364_ == 0)
{
v___x_1366_ = v___x_1363_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v_a_1361_);
v___x_1366_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
return v___x_1366_;
}
}
}
}
else
{
v___y_1290_ = v___y_1347_;
v_FArgs_1291_ = v___y_1346_;
v___y_1292_ = v___y_1348_;
v___y_1293_ = v___y_1349_;
v___y_1294_ = v___y_1350_;
v___y_1295_ = v___y_1351_;
goto v___jp_1289_;
}
}
v___jp_1369_:
{
lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; 
v___x_1376_ = lean_array_get_size(v_recArgInfos_1229_);
v___x_1377_ = lean_mk_empty_array_with_capacity(v___x_1376_);
lean_inc(v___x_1232_);
lean_inc_ref(v___y_1370_);
lean_inc_ref(v_preDefs_1235_);
lean_inc_ref(v___x_1231_);
lean_inc_ref(v_recArgInfos_1229_);
v___x_1378_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg(v_a_1239_, v_a_1230_, v___y_1371_, v_recArgInfos_1229_, v___x_1231_, v_preDefs_1235_, v___y_1370_, v_recArgInfos_1229_, v___x_1376_, v___x_1232_, v___x_1377_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_);
lean_dec_ref(v___y_1371_);
if (lean_obj_tag(v___x_1378_) == 0)
{
lean_object* v_a_1379_; lean_object* v___x_1380_; 
v_a_1379_ = lean_ctor_get(v___x_1378_, 0);
lean_inc(v_a_1379_);
lean_dec_ref(v___x_1378_);
lean_inc(v___y_1375_);
lean_inc_ref(v___y_1374_);
lean_inc(v___y_1373_);
lean_inc_ref(v___y_1372_);
v___x_1380_ = lean_apply_5(v___f_1228_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_, lean_box(0));
if (lean_obj_tag(v___x_1380_) == 0)
{
lean_object* v_a_1381_; uint8_t v___x_1382_; 
v_a_1381_ = lean_ctor_get(v___x_1380_, 0);
lean_inc(v_a_1381_);
lean_dec_ref(v___x_1380_);
v___x_1382_ = lean_unbox(v_a_1381_);
lean_dec(v_a_1381_);
if (v___x_1382_ == 0)
{
v___y_1346_ = v_a_1379_;
v___y_1347_ = v___y_1370_;
v___y_1348_ = v___y_1372_;
v___y_1349_ = v___y_1373_;
v___y_1350_ = v___y_1374_;
v___y_1351_ = v___y_1375_;
goto v___jp_1345_;
}
else
{
lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; 
v___x_1383_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__6, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__6);
lean_inc(v_a_1379_);
v___x_1384_ = lean_array_to_list(v_a_1379_);
v___x_1385_ = lean_box(0);
v___x_1386_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_1384_, v___x_1385_);
v___x_1387_ = l_Lean_MessageData_ofList(v___x_1386_);
v___x_1388_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1388_, 0, v___x_1383_);
lean_ctor_set(v___x_1388_, 1, v___x_1387_);
lean_inc(v___x_1238_);
v___x_1389_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_1238_, v___x_1388_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_);
if (lean_obj_tag(v___x_1389_) == 0)
{
lean_dec_ref(v___x_1389_);
v___y_1346_ = v_a_1379_;
v___y_1347_ = v___y_1370_;
v___y_1348_ = v___y_1372_;
v___y_1349_ = v___y_1373_;
v___y_1350_ = v___y_1374_;
v___y_1351_ = v___y_1375_;
goto v___jp_1345_;
}
else
{
lean_object* v_a_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1397_; 
lean_dec(v_a_1379_);
lean_dec_ref(v___y_1370_);
lean_dec_ref(v_funTypes_1240_);
lean_dec(v___x_1238_);
lean_dec_ref(v___f_1237_);
lean_dec_ref(v_preDefs_1235_);
lean_dec_ref(v_xs_1234_);
lean_dec_ref(v_fixedParamPerms_1233_);
lean_dec(v___x_1232_);
lean_dec_ref(v___x_1231_);
lean_dec_ref(v_recArgInfos_1229_);
v_a_1390_ = lean_ctor_get(v___x_1389_, 0);
v_isSharedCheck_1397_ = !lean_is_exclusive(v___x_1389_);
if (v_isSharedCheck_1397_ == 0)
{
v___x_1392_ = v___x_1389_;
v_isShared_1393_ = v_isSharedCheck_1397_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_a_1390_);
lean_dec(v___x_1389_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1397_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v___x_1395_; 
if (v_isShared_1393_ == 0)
{
v___x_1395_ = v___x_1392_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v_a_1390_);
v___x_1395_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
return v___x_1395_;
}
}
}
}
}
else
{
lean_object* v_a_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1405_; 
lean_dec(v_a_1379_);
lean_dec_ref(v___y_1370_);
lean_dec_ref(v_funTypes_1240_);
lean_dec(v___x_1238_);
lean_dec_ref(v___f_1237_);
lean_dec_ref(v_preDefs_1235_);
lean_dec_ref(v_xs_1234_);
lean_dec_ref(v_fixedParamPerms_1233_);
lean_dec(v___x_1232_);
lean_dec_ref(v___x_1231_);
lean_dec_ref(v_recArgInfos_1229_);
v_a_1398_ = lean_ctor_get(v___x_1380_, 0);
v_isSharedCheck_1405_ = !lean_is_exclusive(v___x_1380_);
if (v_isSharedCheck_1405_ == 0)
{
v___x_1400_ = v___x_1380_;
v_isShared_1401_ = v_isSharedCheck_1405_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_a_1398_);
lean_dec(v___x_1380_);
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
lean_object* v_a_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1413_; 
lean_dec_ref(v___y_1370_);
lean_dec_ref(v_funTypes_1240_);
lean_dec(v___x_1238_);
lean_dec_ref(v___f_1237_);
lean_dec_ref(v_preDefs_1235_);
lean_dec_ref(v_xs_1234_);
lean_dec_ref(v_fixedParamPerms_1233_);
lean_dec(v___x_1232_);
lean_dec_ref(v___x_1231_);
lean_dec_ref(v_recArgInfos_1229_);
lean_dec_ref(v___f_1228_);
v_a_1406_ = lean_ctor_get(v___x_1378_, 0);
v_isSharedCheck_1413_ = !lean_is_exclusive(v___x_1378_);
if (v_isSharedCheck_1413_ == 0)
{
v___x_1408_ = v___x_1378_;
v_isShared_1409_ = v_isSharedCheck_1413_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_a_1406_);
lean_dec(v___x_1378_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1413_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v___x_1411_; 
if (v_isShared_1409_ == 0)
{
v___x_1411_ = v___x_1408_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v_a_1406_);
v___x_1411_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
return v___x_1411_;
}
}
}
}
v___jp_1414_:
{
lean_object* v___x_1419_; 
v___x_1419_ = l_Lean_Elab_Structural_mkBRecOnConst(v_recArgInfos_1229_, v___x_1231_, v_motives_1241_, v_a_1239_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_);
lean_dec_ref(v_motives_1241_);
if (lean_obj_tag(v___x_1419_) == 0)
{
lean_object* v_a_1420_; lean_object* v___x_1421_; 
v_a_1420_ = lean_ctor_get(v___x_1419_, 0);
lean_inc_n(v_a_1420_, 2);
lean_dec_ref(v___x_1419_);
lean_inc_ref(v___x_1231_);
v___x_1421_ = l_Lean_Elab_Structural_inferBRecOnFTypes(v_recArgInfos_1229_, v___x_1231_, v_a_1420_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_);
if (lean_obj_tag(v___x_1421_) == 0)
{
lean_object* v_a_1422_; lean_object* v___x_1423_; 
v_a_1422_ = lean_ctor_get(v___x_1421_, 0);
lean_inc(v_a_1422_);
lean_dec_ref(v___x_1421_);
lean_inc_ref(v___f_1228_);
lean_inc(v___y_1418_);
lean_inc_ref(v___y_1417_);
lean_inc(v___y_1416_);
lean_inc_ref(v___y_1415_);
v___x_1423_ = lean_apply_5(v___f_1228_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_, lean_box(0));
if (lean_obj_tag(v___x_1423_) == 0)
{
lean_object* v_a_1424_; uint8_t v___x_1425_; 
v_a_1424_ = lean_ctor_get(v___x_1423_, 0);
lean_inc(v_a_1424_);
lean_dec_ref(v___x_1423_);
v___x_1425_ = lean_unbox(v_a_1424_);
lean_dec(v_a_1424_);
if (v___x_1425_ == 0)
{
v___y_1370_ = v_a_1420_;
v___y_1371_ = v_a_1422_;
v___y_1372_ = v___y_1415_;
v___y_1373_ = v___y_1416_;
v___y_1374_ = v___y_1417_;
v___y_1375_ = v___y_1418_;
goto v___jp_1369_;
}
else
{
lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; 
v___x_1426_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__8);
lean_inc(v_a_1422_);
v___x_1427_ = lean_array_to_list(v_a_1422_);
v___x_1428_ = lean_box(0);
v___x_1429_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_1427_, v___x_1428_);
v___x_1430_ = l_Lean_MessageData_ofList(v___x_1429_);
v___x_1431_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1431_, 0, v___x_1426_);
lean_ctor_set(v___x_1431_, 1, v___x_1430_);
lean_inc(v___x_1238_);
v___x_1432_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_1238_, v___x_1431_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_);
if (lean_obj_tag(v___x_1432_) == 0)
{
lean_dec_ref(v___x_1432_);
v___y_1370_ = v_a_1420_;
v___y_1371_ = v_a_1422_;
v___y_1372_ = v___y_1415_;
v___y_1373_ = v___y_1416_;
v___y_1374_ = v___y_1417_;
v___y_1375_ = v___y_1418_;
goto v___jp_1369_;
}
else
{
lean_object* v_a_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1440_; 
lean_dec(v_a_1422_);
lean_dec(v_a_1420_);
lean_dec_ref(v_funTypes_1240_);
lean_dec(v___x_1238_);
lean_dec_ref(v___f_1237_);
lean_dec_ref(v_preDefs_1235_);
lean_dec_ref(v_xs_1234_);
lean_dec_ref(v_fixedParamPerms_1233_);
lean_dec(v___x_1232_);
lean_dec_ref(v___x_1231_);
lean_dec_ref(v_recArgInfos_1229_);
lean_dec_ref(v___f_1228_);
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
lean_dec(v_a_1420_);
lean_dec_ref(v_funTypes_1240_);
lean_dec(v___x_1238_);
lean_dec_ref(v___f_1237_);
lean_dec_ref(v_preDefs_1235_);
lean_dec_ref(v_xs_1234_);
lean_dec_ref(v_fixedParamPerms_1233_);
lean_dec(v___x_1232_);
lean_dec_ref(v___x_1231_);
lean_dec_ref(v_recArgInfos_1229_);
lean_dec_ref(v___f_1228_);
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
lean_dec(v_a_1420_);
lean_dec_ref(v_funTypes_1240_);
lean_dec(v___x_1238_);
lean_dec_ref(v___f_1237_);
lean_dec_ref(v_preDefs_1235_);
lean_dec_ref(v_xs_1234_);
lean_dec_ref(v_fixedParamPerms_1233_);
lean_dec(v___x_1232_);
lean_dec_ref(v___x_1231_);
lean_dec_ref(v_recArgInfos_1229_);
lean_dec_ref(v___f_1228_);
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
else
{
lean_object* v_a_1457_; lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1464_; 
lean_dec_ref(v_funTypes_1240_);
lean_dec(v___x_1238_);
lean_dec_ref(v___f_1237_);
lean_dec_ref(v_preDefs_1235_);
lean_dec_ref(v_xs_1234_);
lean_dec_ref(v_fixedParamPerms_1233_);
lean_dec(v___x_1232_);
lean_dec_ref(v___x_1231_);
lean_dec_ref(v_recArgInfos_1229_);
lean_dec_ref(v___f_1228_);
v_a_1457_ = lean_ctor_get(v___x_1419_, 0);
v_isSharedCheck_1464_ = !lean_is_exclusive(v___x_1419_);
if (v_isSharedCheck_1464_ == 0)
{
v___x_1459_ = v___x_1419_;
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
else
{
lean_inc(v_a_1457_);
lean_dec(v___x_1419_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
lean_object* v___x_1462_; 
if (v_isShared_1460_ == 0)
{
v___x_1462_ = v___x_1459_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v_a_1457_);
v___x_1462_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
return v___x_1462_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___boxed(lean_object** _args){
lean_object* v___f_1497_ = _args[0];
lean_object* v_recArgInfos_1498_ = _args[1];
lean_object* v_a_1499_ = _args[2];
lean_object* v___x_1500_ = _args[3];
lean_object* v___x_1501_ = _args[4];
lean_object* v_fixedParamPerms_1502_ = _args[5];
lean_object* v_xs_1503_ = _args[6];
lean_object* v_preDefs_1504_ = _args[7];
lean_object* v_numIndices_1505_ = _args[8];
lean_object* v___f_1506_ = _args[9];
lean_object* v___x_1507_ = _args[10];
lean_object* v_a_1508_ = _args[11];
lean_object* v_funTypes_1509_ = _args[12];
lean_object* v_motives_1510_ = _args[13];
lean_object* v___y_1511_ = _args[14];
lean_object* v___y_1512_ = _args[15];
lean_object* v___y_1513_ = _args[16];
lean_object* v___y_1514_ = _args[17];
lean_object* v___y_1515_ = _args[18];
_start:
{
uint8_t v_a_28720__boxed_1516_; lean_object* v_res_1517_; 
v_a_28720__boxed_1516_ = lean_unbox(v_a_1508_);
v_res_1517_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2(v___f_1497_, v_recArgInfos_1498_, v_a_1499_, v___x_1500_, v___x_1501_, v_fixedParamPerms_1502_, v_xs_1503_, v_preDefs_1504_, v_numIndices_1505_, v___f_1506_, v___x_1507_, v_a_28720__boxed_1516_, v_funTypes_1509_, v_motives_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_);
lean_dec(v___y_1514_);
lean_dec_ref(v___y_1513_);
lean_dec(v___y_1512_);
lean_dec_ref(v___y_1511_);
lean_dec(v_numIndices_1505_);
lean_dec_ref(v_a_1499_);
return v_res_1517_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___redArg(lean_object* v_a_1518_, lean_object* v_funTypes_1519_, lean_object* v_as_1520_, lean_object* v_i_1521_, lean_object* v_j_1522_, lean_object* v_bs_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_){
_start:
{
lean_object* v_zero_1529_; uint8_t v_isZero_1530_; 
v_zero_1529_ = lean_unsigned_to_nat(0u);
v_isZero_1530_ = lean_nat_dec_eq(v_i_1521_, v_zero_1529_);
if (v_isZero_1530_ == 1)
{
lean_object* v___x_1531_; 
lean_dec(v_j_1522_);
lean_dec(v_i_1521_);
v___x_1531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1531_, 0, v_bs_1523_);
return v___x_1531_;
}
else
{
lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; 
v___x_1532_ = l_Lean_instInhabitedExpr;
v___x_1533_ = lean_array_fget_borrowed(v_as_1520_, v_j_1522_);
v___x_1534_ = lean_array_get_borrowed(v___x_1532_, v_a_1518_, v_j_1522_);
v___x_1535_ = lean_array_get_borrowed(v___x_1532_, v_funTypes_1519_, v_j_1522_);
lean_inc(v___x_1535_);
lean_inc(v___x_1534_);
lean_inc(v___x_1533_);
v___x_1536_ = l_Lean_Elab_Structural_mkIndPredBRecOnMotive(v___x_1533_, v___x_1534_, v___x_1535_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_);
if (lean_obj_tag(v___x_1536_) == 0)
{
lean_object* v_a_1537_; lean_object* v_one_1538_; lean_object* v_n_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; 
v_a_1537_ = lean_ctor_get(v___x_1536_, 0);
lean_inc(v_a_1537_);
lean_dec_ref(v___x_1536_);
v_one_1538_ = lean_unsigned_to_nat(1u);
v_n_1539_ = lean_nat_sub(v_i_1521_, v_one_1538_);
lean_dec(v_i_1521_);
v___x_1540_ = lean_nat_add(v_j_1522_, v_one_1538_);
lean_dec(v_j_1522_);
v___x_1541_ = lean_array_push(v_bs_1523_, v_a_1537_);
v_i_1521_ = v_n_1539_;
v_j_1522_ = v___x_1540_;
v_bs_1523_ = v___x_1541_;
goto _start;
}
else
{
lean_object* v_a_1543_; lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1550_; 
lean_dec_ref(v_bs_1523_);
lean_dec(v_j_1522_);
lean_dec(v_i_1521_);
v_a_1543_ = lean_ctor_get(v___x_1536_, 0);
v_isSharedCheck_1550_ = !lean_is_exclusive(v___x_1536_);
if (v_isSharedCheck_1550_ == 0)
{
v___x_1545_ = v___x_1536_;
v_isShared_1546_ = v_isSharedCheck_1550_;
goto v_resetjp_1544_;
}
else
{
lean_inc(v_a_1543_);
lean_dec(v___x_1536_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1550_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
lean_object* v___x_1548_; 
if (v_isShared_1546_ == 0)
{
v___x_1548_ = v___x_1545_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v_a_1543_);
v___x_1548_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
return v___x_1548_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___redArg___boxed(lean_object* v_a_1551_, lean_object* v_funTypes_1552_, lean_object* v_as_1553_, lean_object* v_i_1554_, lean_object* v_j_1555_, lean_object* v_bs_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_){
_start:
{
lean_object* v_res_1562_; 
v_res_1562_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___redArg(v_a_1551_, v_funTypes_1552_, v_as_1553_, v_i_1554_, v_j_1555_, v_bs_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_);
lean_dec(v___y_1560_);
lean_dec_ref(v___y_1559_);
lean_dec(v___y_1558_);
lean_dec_ref(v___y_1557_);
lean_dec_ref(v_as_1553_);
lean_dec_ref(v_funTypes_1552_);
lean_dec_ref(v_a_1551_);
return v_res_1562_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__3(lean_object* v_recArgInfos_1563_, lean_object* v_a_1564_, lean_object* v___x_1565_, lean_object* v___f_1566_, lean_object* v_funTypes_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_){
_start:
{
lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; 
v___x_1573_ = lean_array_get_size(v_recArgInfos_1563_);
v___x_1574_ = lean_mk_empty_array_with_capacity(v___x_1573_);
v___x_1575_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___redArg(v_a_1564_, v_funTypes_1567_, v_recArgInfos_1563_, v___x_1573_, v___x_1565_, v___x_1574_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_);
if (lean_obj_tag(v___x_1575_) == 0)
{
lean_object* v_a_1576_; lean_object* v___x_1577_; 
v_a_1576_ = lean_ctor_get(v___x_1575_, 0);
lean_inc(v_a_1576_);
lean_dec_ref(v___x_1575_);
lean_inc(v___y_1571_);
lean_inc_ref(v___y_1570_);
lean_inc(v___y_1569_);
lean_inc_ref(v___y_1568_);
v___x_1577_ = lean_apply_7(v___f_1566_, v_funTypes_1567_, v_a_1576_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_, lean_box(0));
return v___x_1577_;
}
else
{
lean_object* v_a_1578_; lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1585_; 
lean_dec_ref(v_funTypes_1567_);
lean_dec_ref(v___f_1566_);
v_a_1578_ = lean_ctor_get(v___x_1575_, 0);
v_isSharedCheck_1585_ = !lean_is_exclusive(v___x_1575_);
if (v_isSharedCheck_1585_ == 0)
{
v___x_1580_ = v___x_1575_;
v_isShared_1581_ = v_isSharedCheck_1585_;
goto v_resetjp_1579_;
}
else
{
lean_inc(v_a_1578_);
lean_dec(v___x_1575_);
v___x_1580_ = lean_box(0);
v_isShared_1581_ = v_isSharedCheck_1585_;
goto v_resetjp_1579_;
}
v_resetjp_1579_:
{
lean_object* v___x_1583_; 
if (v_isShared_1581_ == 0)
{
v___x_1583_ = v___x_1580_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v_a_1578_);
v___x_1583_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
return v___x_1583_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__3___boxed(lean_object* v_recArgInfos_1586_, lean_object* v_a_1587_, lean_object* v___x_1588_, lean_object* v___f_1589_, lean_object* v_funTypes_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_){
_start:
{
lean_object* v_res_1596_; 
v_res_1596_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__3(v_recArgInfos_1586_, v_a_1587_, v___x_1588_, v___f_1589_, v_funTypes_1590_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_);
lean_dec(v___y_1594_);
lean_dec_ref(v___y_1593_);
lean_dec(v___y_1592_);
lean_dec_ref(v___y_1591_);
lean_dec_ref(v_a_1587_);
lean_dec_ref(v_recArgInfos_1586_);
return v_res_1596_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg(lean_object* v_msg_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_){
_start:
{
lean_object* v_ref_1603_; lean_object* v___x_1604_; lean_object* v_a_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1613_; 
v_ref_1603_ = lean_ctor_get(v___y_1600_, 5);
v___x_1604_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11_spec__21(v_msg_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_);
v_a_1605_ = lean_ctor_get(v___x_1604_, 0);
v_isSharedCheck_1613_ = !lean_is_exclusive(v___x_1604_);
if (v_isSharedCheck_1613_ == 0)
{
v___x_1607_ = v___x_1604_;
v_isShared_1608_ = v_isSharedCheck_1613_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_a_1605_);
lean_dec(v___x_1604_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1613_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
lean_object* v___x_1609_; lean_object* v___x_1611_; 
lean_inc(v_ref_1603_);
v___x_1609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1609_, 0, v_ref_1603_);
lean_ctor_set(v___x_1609_, 1, v_a_1605_);
if (v_isShared_1608_ == 0)
{
lean_ctor_set_tag(v___x_1607_, 1);
lean_ctor_set(v___x_1607_, 0, v___x_1609_);
v___x_1611_ = v___x_1607_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v___x_1609_);
v___x_1611_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
return v___x_1611_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg___boxed(lean_object* v_msg_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_){
_start:
{
lean_object* v_res_1620_; 
v_res_1620_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg(v_msg_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_);
lean_dec(v___y_1618_);
lean_dec_ref(v___y_1617_);
lean_dec(v___y_1616_);
lean_dec_ref(v___y_1615_);
return v_res_1620_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1622_; lean_object* v___x_1623_; 
v___x_1622_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__0));
v___x_1623_ = l_Lean_stringToMessageData(v___x_1622_);
return v___x_1623_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__3(void){
_start:
{
lean_object* v___x_1625_; lean_object* v___x_1626_; 
v___x_1625_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__2));
v___x_1626_ = l_Lean_stringToMessageData(v___x_1625_);
return v___x_1626_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4(lean_object* v_constName_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_){
_start:
{
lean_object* v___x_1633_; lean_object* v_env_1634_; lean_object* v___x_1635_; 
v___x_1633_ = lean_st_ref_get(v___y_1631_);
v_env_1634_ = lean_ctor_get(v___x_1633_, 0);
lean_inc_ref(v_env_1634_);
lean_dec(v___x_1633_);
lean_inc(v_constName_1627_);
v___x_1635_ = l_Lean_isInductiveCore_x3f(v_env_1634_, v_constName_1627_);
if (lean_obj_tag(v___x_1635_) == 0)
{
lean_object* v___x_1636_; uint8_t v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; 
v___x_1636_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__1, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__1);
v___x_1637_ = 0;
v___x_1638_ = l_Lean_MessageData_ofConstName(v_constName_1627_, v___x_1637_);
v___x_1639_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1639_, 0, v___x_1636_);
lean_ctor_set(v___x_1639_, 1, v___x_1638_);
v___x_1640_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__3, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__3_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__3);
v___x_1641_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1641_, 0, v___x_1639_);
lean_ctor_set(v___x_1641_, 1, v___x_1640_);
v___x_1642_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg(v___x_1641_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_);
return v___x_1642_;
}
else
{
lean_object* v_val_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1650_; 
lean_dec(v_constName_1627_);
v_val_1643_ = lean_ctor_get(v___x_1635_, 0);
v_isSharedCheck_1650_ = !lean_is_exclusive(v___x_1635_);
if (v_isSharedCheck_1650_ == 0)
{
v___x_1645_ = v___x_1635_;
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_val_1643_);
lean_dec(v___x_1635_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v___x_1648_; 
if (v_isShared_1646_ == 0)
{
lean_ctor_set_tag(v___x_1645_, 0);
v___x_1648_ = v___x_1645_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v_val_1643_);
v___x_1648_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
return v___x_1648_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___boxed(lean_object* v_constName_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_){
_start:
{
lean_object* v_res_1657_; 
v_res_1657_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4(v_constName_1651_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_);
lean_dec(v___y_1655_);
lean_dec_ref(v___y_1654_);
lean_dec(v___y_1653_);
lean_dec_ref(v___y_1652_);
return v_res_1657_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___redArg(lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_as_1660_, lean_object* v_i_1661_, lean_object* v_j_1662_, lean_object* v_bs_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_){
_start:
{
lean_object* v_zero_1669_; uint8_t v_isZero_1670_; 
v_zero_1669_ = lean_unsigned_to_nat(0u);
v_isZero_1670_ = lean_nat_dec_eq(v_i_1661_, v_zero_1669_);
if (v_isZero_1670_ == 1)
{
lean_object* v___x_1671_; 
lean_dec(v_j_1662_);
lean_dec(v_i_1661_);
v___x_1671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1671_, 0, v_bs_1663_);
return v___x_1671_;
}
else
{
lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; 
v___x_1672_ = l_Lean_instInhabitedExpr;
v___x_1673_ = lean_array_fget_borrowed(v_as_1660_, v_j_1662_);
v___x_1674_ = lean_array_get_borrowed(v___x_1672_, v_a_1658_, v_j_1662_);
v___x_1675_ = lean_array_get_borrowed(v___x_1672_, v_a_1659_, v_j_1662_);
lean_inc(v___x_1675_);
lean_inc(v___x_1674_);
lean_inc(v___x_1673_);
v___x_1676_ = l_Lean_Elab_Structural_mkBRecOnMotive(v___x_1673_, v___x_1674_, v___x_1675_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_);
if (lean_obj_tag(v___x_1676_) == 0)
{
lean_object* v_a_1677_; lean_object* v_one_1678_; lean_object* v_n_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; 
v_a_1677_ = lean_ctor_get(v___x_1676_, 0);
lean_inc(v_a_1677_);
lean_dec_ref(v___x_1676_);
v_one_1678_ = lean_unsigned_to_nat(1u);
v_n_1679_ = lean_nat_sub(v_i_1661_, v_one_1678_);
lean_dec(v_i_1661_);
v___x_1680_ = lean_nat_add(v_j_1662_, v_one_1678_);
lean_dec(v_j_1662_);
v___x_1681_ = lean_array_push(v_bs_1663_, v_a_1677_);
v_i_1661_ = v_n_1679_;
v_j_1662_ = v___x_1680_;
v_bs_1663_ = v___x_1681_;
goto _start;
}
else
{
lean_object* v_a_1683_; lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1690_; 
lean_dec_ref(v_bs_1663_);
lean_dec(v_j_1662_);
lean_dec(v_i_1661_);
v_a_1683_ = lean_ctor_get(v___x_1676_, 0);
v_isSharedCheck_1690_ = !lean_is_exclusive(v___x_1676_);
if (v_isSharedCheck_1690_ == 0)
{
v___x_1685_ = v___x_1676_;
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
else
{
lean_inc(v_a_1683_);
lean_dec(v___x_1676_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
v_resetjp_1684_:
{
lean_object* v___x_1688_; 
if (v_isShared_1686_ == 0)
{
v___x_1688_ = v___x_1685_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v_a_1683_);
v___x_1688_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
return v___x_1688_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___redArg___boxed(lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_as_1693_, lean_object* v_i_1694_, lean_object* v_j_1695_, lean_object* v_bs_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_){
_start:
{
lean_object* v_res_1702_; 
v_res_1702_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___redArg(v_a_1691_, v_a_1692_, v_as_1693_, v_i_1694_, v_j_1695_, v_bs_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_);
lean_dec(v___y_1700_);
lean_dec_ref(v___y_1699_);
lean_dec(v___y_1698_);
lean_dec_ref(v___y_1697_);
lean_dec_ref(v_as_1693_);
lean_dec_ref(v_a_1692_);
lean_dec_ref(v_a_1691_);
return v_res_1702_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg(lean_object* v_as_1704_, lean_object* v_lo_1705_, lean_object* v_hi_1706_){
_start:
{
uint8_t v___x_1707_; 
v___x_1707_ = lean_nat_dec_lt(v_lo_1705_, v_hi_1706_);
if (v___x_1707_ == 0)
{
lean_dec(v_lo_1705_);
return v_as_1704_;
}
else
{
lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v_fst_1710_; lean_object* v_snd_1711_; uint8_t v___x_1712_; 
v___x_1708_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg___closed__0));
lean_inc(v_lo_1705_);
v___x_1709_ = l_Array_qpartition___redArg(v_as_1704_, v___x_1708_, v_lo_1705_, v_hi_1706_);
v_fst_1710_ = lean_ctor_get(v___x_1709_, 0);
lean_inc(v_fst_1710_);
v_snd_1711_ = lean_ctor_get(v___x_1709_, 1);
lean_inc(v_snd_1711_);
lean_dec_ref(v___x_1709_);
v___x_1712_ = lean_nat_dec_le(v_hi_1706_, v_fst_1710_);
if (v___x_1712_ == 0)
{
lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; 
v___x_1713_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg(v_snd_1711_, v_lo_1705_, v_fst_1710_);
v___x_1714_ = lean_unsigned_to_nat(1u);
v___x_1715_ = lean_nat_add(v_fst_1710_, v___x_1714_);
lean_dec(v_fst_1710_);
v_as_1704_ = v___x_1713_;
v_lo_1705_ = v___x_1715_;
goto _start;
}
else
{
lean_dec(v_fst_1710_);
lean_dec(v_lo_1705_);
return v_snd_1711_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg___boxed(lean_object* v_as_1717_, lean_object* v_lo_1718_, lean_object* v_hi_1719_){
_start:
{
lean_object* v_res_1720_; 
v_res_1720_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg(v_as_1717_, v_lo_1718_, v_hi_1719_);
lean_dec(v_hi_1719_);
return v_res_1720_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__6(lean_object* v_xs_1721_, lean_object* v_f_1722_, lean_object* v_x_1723_, lean_object* v_as_1724_, size_t v_i_1725_, size_t v_stop_1726_, lean_object* v_b_1727_){
_start:
{
lean_object* v___y_1729_; uint8_t v___x_1733_; 
v___x_1733_ = lean_usize_dec_eq(v_i_1725_, v_stop_1726_);
if (v___x_1733_ == 0)
{
lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; uint8_t v___x_1738_; 
v___x_1734_ = l_Lean_Elab_Structural_instInhabitedRecArgInfo_default;
v___x_1735_ = lean_array_uget_borrowed(v_as_1724_, v_i_1725_);
v___x_1736_ = lean_array_get_borrowed(v___x_1734_, v_xs_1721_, v___x_1735_);
lean_inc_ref(v_f_1722_);
lean_inc(v___x_1736_);
v___x_1737_ = lean_apply_1(v_f_1722_, v___x_1736_);
v___x_1738_ = lean_nat_dec_eq(v___x_1737_, v_x_1723_);
lean_dec(v___x_1737_);
if (v___x_1738_ == 0)
{
v___y_1729_ = v_b_1727_;
goto v___jp_1728_;
}
else
{
lean_object* v___x_1739_; 
lean_inc(v___x_1735_);
v___x_1739_ = lean_array_push(v_b_1727_, v___x_1735_);
v___y_1729_ = v___x_1739_;
goto v___jp_1728_;
}
}
else
{
lean_dec_ref(v_f_1722_);
return v_b_1727_;
}
v___jp_1728_:
{
size_t v___x_1730_; size_t v___x_1731_; 
v___x_1730_ = ((size_t)1ULL);
v___x_1731_ = lean_usize_add(v_i_1725_, v___x_1730_);
v_i_1725_ = v___x_1731_;
v_b_1727_ = v___y_1729_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__6___boxed(lean_object* v_xs_1740_, lean_object* v_f_1741_, lean_object* v_x_1742_, lean_object* v_as_1743_, lean_object* v_i_1744_, lean_object* v_stop_1745_, lean_object* v_b_1746_){
_start:
{
size_t v_i_boxed_1747_; size_t v_stop_boxed_1748_; lean_object* v_res_1749_; 
v_i_boxed_1747_ = lean_unbox_usize(v_i_1744_);
lean_dec(v_i_1744_);
v_stop_boxed_1748_ = lean_unbox_usize(v_stop_1745_);
lean_dec(v_stop_1745_);
v_res_1749_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__6(v_xs_1740_, v_f_1741_, v_x_1742_, v_as_1743_, v_i_boxed_1747_, v_stop_boxed_1748_, v_b_1746_);
lean_dec_ref(v_as_1743_);
lean_dec(v_x_1742_);
lean_dec_ref(v_xs_1740_);
return v_res_1749_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8(lean_object* v_xs_1752_, lean_object* v_f_1753_, size_t v_sz_1754_, size_t v_i_1755_, lean_object* v_bs_1756_){
_start:
{
uint8_t v___x_1757_; 
v___x_1757_ = lean_usize_dec_lt(v_i_1755_, v_sz_1754_);
if (v___x_1757_ == 0)
{
lean_dec_ref(v_f_1753_);
return v_bs_1756_;
}
else
{
lean_object* v_v_1758_; lean_object* v___x_1759_; lean_object* v_bs_x27_1760_; lean_object* v___y_1762_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; uint8_t v___x_1771_; 
v_v_1758_ = lean_array_uget(v_bs_1756_, v_i_1755_);
v___x_1759_ = lean_unsigned_to_nat(0u);
v_bs_x27_1760_ = lean_array_uset(v_bs_1756_, v_i_1755_, v___x_1759_);
v___x_1767_ = lean_array_get_size(v_xs_1752_);
v___x_1768_ = l_Array_range(v___x_1767_);
v___x_1769_ = lean_array_get_size(v___x_1768_);
v___x_1770_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8___closed__0));
v___x_1771_ = lean_nat_dec_lt(v___x_1759_, v___x_1769_);
if (v___x_1771_ == 0)
{
lean_dec_ref(v___x_1768_);
lean_dec(v_v_1758_);
v___y_1762_ = v___x_1770_;
goto v___jp_1761_;
}
else
{
uint8_t v___x_1772_; 
v___x_1772_ = lean_nat_dec_le(v___x_1769_, v___x_1769_);
if (v___x_1772_ == 0)
{
if (v___x_1771_ == 0)
{
lean_dec_ref(v___x_1768_);
lean_dec(v_v_1758_);
v___y_1762_ = v___x_1770_;
goto v___jp_1761_;
}
else
{
size_t v___x_1773_; size_t v___x_1774_; lean_object* v___x_1775_; 
v___x_1773_ = ((size_t)0ULL);
v___x_1774_ = lean_usize_of_nat(v___x_1769_);
lean_inc_ref(v_f_1753_);
v___x_1775_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__6(v_xs_1752_, v_f_1753_, v_v_1758_, v___x_1768_, v___x_1773_, v___x_1774_, v___x_1770_);
lean_dec_ref(v___x_1768_);
lean_dec(v_v_1758_);
v___y_1762_ = v___x_1775_;
goto v___jp_1761_;
}
}
else
{
size_t v___x_1776_; size_t v___x_1777_; lean_object* v___x_1778_; 
v___x_1776_ = ((size_t)0ULL);
v___x_1777_ = lean_usize_of_nat(v___x_1769_);
lean_inc_ref(v_f_1753_);
v___x_1778_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__6(v_xs_1752_, v_f_1753_, v_v_1758_, v___x_1768_, v___x_1776_, v___x_1777_, v___x_1770_);
lean_dec_ref(v___x_1768_);
lean_dec(v_v_1758_);
v___y_1762_ = v___x_1778_;
goto v___jp_1761_;
}
}
v___jp_1761_:
{
size_t v___x_1763_; size_t v___x_1764_; lean_object* v___x_1765_; 
v___x_1763_ = ((size_t)1ULL);
v___x_1764_ = lean_usize_add(v_i_1755_, v___x_1763_);
v___x_1765_ = lean_array_uset(v_bs_x27_1760_, v_i_1755_, v___y_1762_);
v_i_1755_ = v___x_1764_;
v_bs_1756_ = v___x_1765_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8___boxed(lean_object* v_xs_1779_, lean_object* v_f_1780_, lean_object* v_sz_1781_, lean_object* v_i_1782_, lean_object* v_bs_1783_){
_start:
{
size_t v_sz_boxed_1784_; size_t v_i_boxed_1785_; lean_object* v_res_1786_; 
v_sz_boxed_1784_ = lean_unbox_usize(v_sz_1781_);
lean_dec(v_sz_1781_);
v_i_boxed_1785_ = lean_unbox_usize(v_i_1782_);
lean_dec(v_i_1782_);
v_res_1786_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8(v_xs_1779_, v_f_1780_, v_sz_boxed_1784_, v_i_boxed_1785_, v_bs_1783_);
lean_dec_ref(v_xs_1779_);
return v_res_1786_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__11(lean_object* v_as_1787_, size_t v_i_1788_, size_t v_stop_1789_, lean_object* v_b_1790_){
_start:
{
uint8_t v___x_1791_; 
v___x_1791_ = lean_usize_dec_eq(v_i_1788_, v_stop_1789_);
if (v___x_1791_ == 0)
{
lean_object* v___x_1792_; lean_object* v___x_1793_; size_t v___x_1794_; size_t v___x_1795_; 
v___x_1792_ = lean_array_uget_borrowed(v_as_1787_, v_i_1788_);
v___x_1793_ = l_Array_append___redArg(v_b_1790_, v___x_1792_);
v___x_1794_ = ((size_t)1ULL);
v___x_1795_ = lean_usize_add(v_i_1788_, v___x_1794_);
v_i_1788_ = v___x_1795_;
v_b_1790_ = v___x_1793_;
goto _start;
}
else
{
return v_b_1790_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__11___boxed(lean_object* v_as_1797_, lean_object* v_i_1798_, lean_object* v_stop_1799_, lean_object* v_b_1800_){
_start:
{
size_t v_i_boxed_1801_; size_t v_stop_boxed_1802_; lean_object* v_res_1803_; 
v_i_boxed_1801_ = lean_unbox_usize(v_i_1798_);
lean_dec(v_i_1798_);
v_stop_boxed_1802_ = lean_unbox_usize(v_stop_1799_);
lean_dec(v_stop_1799_);
v_res_1803_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__11(v_as_1797_, v_i_boxed_1801_, v_stop_boxed_1802_, v_b_1800_);
lean_dec_ref(v_as_1797_);
return v_res_1803_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__7___closed__0(void){
_start:
{
lean_object* v___x_1804_; 
v___x_1804_ = l_Array_instInhabited(lean_box(0));
return v___x_1804_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__7(lean_object* v_msg_1805_){
_start:
{
lean_object* v___x_1806_; lean_object* v___x_1807_; 
v___x_1806_ = lean_obj_once(&l_panic___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__7___closed__0, &l_panic___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__7___closed__0_once, _init_l_panic___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__7___closed__0);
v___x_1807_ = lean_panic_fn_borrowed(v___x_1806_, v_msg_1805_);
return v___x_1807_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9___redArg(lean_object* v_xs_1808_, lean_object* v_ys_1809_, lean_object* v_x_1810_){
_start:
{
lean_object* v_zero_1811_; uint8_t v_isZero_1812_; 
v_zero_1811_ = lean_unsigned_to_nat(0u);
v_isZero_1812_ = lean_nat_dec_eq(v_x_1810_, v_zero_1811_);
if (v_isZero_1812_ == 1)
{
lean_dec(v_x_1810_);
return v_isZero_1812_;
}
else
{
lean_object* v_one_1813_; lean_object* v_n_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; uint8_t v___x_1817_; 
v_one_1813_ = lean_unsigned_to_nat(1u);
v_n_1814_ = lean_nat_sub(v_x_1810_, v_one_1813_);
lean_dec(v_x_1810_);
v___x_1815_ = lean_array_fget_borrowed(v_xs_1808_, v_n_1814_);
v___x_1816_ = lean_array_fget_borrowed(v_ys_1809_, v_n_1814_);
v___x_1817_ = lean_nat_dec_eq(v___x_1815_, v___x_1816_);
if (v___x_1817_ == 0)
{
lean_dec(v_n_1814_);
return v___x_1817_;
}
else
{
v_x_1810_ = v_n_1814_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9___redArg___boxed(lean_object* v_xs_1819_, lean_object* v_ys_1820_, lean_object* v_x_1821_){
_start:
{
uint8_t v_res_1822_; lean_object* v_r_1823_; 
v_res_1822_ = l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9___redArg(v_xs_1819_, v_ys_1820_, v_x_1821_);
lean_dec_ref(v_ys_1820_);
lean_dec_ref(v_xs_1819_);
v_r_1823_ = lean_box(v_res_1822_);
return v_r_1823_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__2(void){
_start:
{
lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; 
v___x_1826_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__1));
v___x_1827_ = lean_unsigned_to_nat(2u);
v___x_1828_ = lean_unsigned_to_nat(63u);
v___x_1829_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__0));
v___x_1830_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__0));
v___x_1831_ = l_mkPanicMessageWithDecl(v___x_1830_, v___x_1829_, v___x_1828_, v___x_1827_, v___x_1826_);
return v___x_1831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5(lean_object* v_f_1834_, lean_object* v_xs_1835_, lean_object* v_ys_1836_){
_start:
{
size_t v_sz_1840_; size_t v___x_1841_; lean_object* v_positions_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___y_1846_; lean_object* v___y_1852_; lean_object* v___y_1853_; lean_object* v___y_1854_; lean_object* v___y_1855_; lean_object* v___y_1858_; lean_object* v___y_1859_; lean_object* v___y_1860_; lean_object* v___y_1861_; lean_object* v___y_1864_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; uint8_t v___x_1874_; 
v_sz_1840_ = lean_array_size(v_ys_1836_);
v___x_1841_ = ((size_t)0ULL);
v_positions_1842_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8(v_xs_1835_, v_f_1834_, v_sz_1840_, v___x_1841_, v_ys_1836_);
v___x_1843_ = lean_array_get_size(v_xs_1835_);
v___x_1844_ = l_Array_range(v___x_1843_);
v___x_1871_ = lean_unsigned_to_nat(0u);
v___x_1872_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__3));
v___x_1873_ = lean_array_get_size(v_positions_1842_);
v___x_1874_ = lean_nat_dec_lt(v___x_1871_, v___x_1873_);
if (v___x_1874_ == 0)
{
v___y_1864_ = v___x_1872_;
goto v___jp_1863_;
}
else
{
uint8_t v___x_1875_; 
v___x_1875_ = lean_nat_dec_le(v___x_1873_, v___x_1873_);
if (v___x_1875_ == 0)
{
if (v___x_1874_ == 0)
{
v___y_1864_ = v___x_1872_;
goto v___jp_1863_;
}
else
{
size_t v___x_1876_; lean_object* v___x_1877_; 
v___x_1876_ = lean_usize_of_nat(v___x_1873_);
v___x_1877_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__11(v_positions_1842_, v___x_1841_, v___x_1876_, v___x_1872_);
v___y_1864_ = v___x_1877_;
goto v___jp_1863_;
}
}
else
{
size_t v___x_1878_; lean_object* v___x_1879_; 
v___x_1878_ = lean_usize_of_nat(v___x_1873_);
v___x_1879_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__11(v_positions_1842_, v___x_1841_, v___x_1878_, v___x_1872_);
v___y_1864_ = v___x_1879_;
goto v___jp_1863_;
}
}
v___jp_1837_:
{
lean_object* v___x_1838_; lean_object* v___x_1839_; 
v___x_1838_ = lean_obj_once(&l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__2, &l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__2_once, _init_l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__2);
v___x_1839_ = l_panic___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__7(v___x_1838_);
return v___x_1839_;
}
v___jp_1845_:
{
lean_object* v___x_1847_; lean_object* v___x_1848_; uint8_t v___x_1849_; 
v___x_1847_ = lean_array_get_size(v___x_1844_);
v___x_1848_ = lean_array_get_size(v___y_1846_);
v___x_1849_ = lean_nat_dec_eq(v___x_1847_, v___x_1848_);
if (v___x_1849_ == 0)
{
lean_dec_ref(v___y_1846_);
lean_dec_ref(v___x_1844_);
lean_dec_ref(v_positions_1842_);
goto v___jp_1837_;
}
else
{
uint8_t v___x_1850_; 
v___x_1850_ = l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9___redArg(v___x_1844_, v___y_1846_, v___x_1847_);
lean_dec_ref(v___y_1846_);
lean_dec_ref(v___x_1844_);
if (v___x_1850_ == 0)
{
lean_dec_ref(v_positions_1842_);
goto v___jp_1837_;
}
else
{
return v_positions_1842_;
}
}
}
v___jp_1851_:
{
lean_object* v___x_1856_; 
lean_dec(v___y_1854_);
v___x_1856_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg(v___y_1852_, v___y_1853_, v___y_1855_);
lean_dec(v___y_1855_);
v___y_1846_ = v___x_1856_;
goto v___jp_1845_;
}
v___jp_1857_:
{
uint8_t v___x_1862_; 
v___x_1862_ = lean_nat_dec_le(v___y_1861_, v___y_1860_);
if (v___x_1862_ == 0)
{
lean_dec(v___y_1860_);
lean_inc(v___y_1861_);
v___y_1852_ = v___y_1858_;
v___y_1853_ = v___y_1861_;
v___y_1854_ = v___y_1859_;
v___y_1855_ = v___y_1861_;
goto v___jp_1851_;
}
else
{
v___y_1852_ = v___y_1858_;
v___y_1853_ = v___y_1861_;
v___y_1854_ = v___y_1859_;
v___y_1855_ = v___y_1860_;
goto v___jp_1851_;
}
}
v___jp_1863_:
{
lean_object* v___x_1865_; lean_object* v___x_1866_; uint8_t v___x_1867_; 
v___x_1865_ = lean_array_get_size(v___y_1864_);
v___x_1866_ = lean_unsigned_to_nat(0u);
v___x_1867_ = lean_nat_dec_eq(v___x_1865_, v___x_1866_);
if (v___x_1867_ == 0)
{
lean_object* v___x_1868_; lean_object* v___x_1869_; uint8_t v___x_1870_; 
v___x_1868_ = lean_unsigned_to_nat(1u);
v___x_1869_ = lean_nat_sub(v___x_1865_, v___x_1868_);
v___x_1870_ = lean_nat_dec_le(v___x_1866_, v___x_1869_);
if (v___x_1870_ == 0)
{
lean_inc(v___x_1869_);
v___y_1858_ = v___y_1864_;
v___y_1859_ = v___x_1865_;
v___y_1860_ = v___x_1869_;
v___y_1861_ = v___x_1869_;
goto v___jp_1857_;
}
else
{
v___y_1858_ = v___y_1864_;
v___y_1859_ = v___x_1865_;
v___y_1860_ = v___x_1869_;
v___y_1861_ = v___x_1866_;
goto v___jp_1857_;
}
}
else
{
v___y_1846_ = v___y_1864_;
goto v___jp_1845_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___boxed(lean_object* v_f_1880_, lean_object* v_xs_1881_, lean_object* v_ys_1882_){
_start:
{
lean_object* v_res_1883_; 
v_res_1883_ = l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5(v_f_1880_, v_xs_1881_, v_ys_1882_);
lean_dec_ref(v_xs_1881_);
return v_res_1883_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___redArg(lean_object* v_fixedParamPerms_1884_, lean_object* v_xs_1885_, lean_object* v_as_1886_, lean_object* v_i_1887_, lean_object* v_j_1888_, lean_object* v_bs_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_){
_start:
{
lean_object* v_zero_1895_; uint8_t v_isZero_1896_; 
v_zero_1895_ = lean_unsigned_to_nat(0u);
v_isZero_1896_ = lean_nat_dec_eq(v_i_1887_, v_zero_1895_);
if (v_isZero_1896_ == 1)
{
lean_object* v___x_1897_; 
lean_dec(v_j_1888_);
lean_dec(v_i_1887_);
lean_dec_ref(v_xs_1885_);
v___x_1897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1897_, 0, v_bs_1889_);
return v___x_1897_;
}
else
{
lean_object* v_perms_1898_; lean_object* v___x_1899_; lean_object* v_value_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; 
v_perms_1898_ = lean_ctor_get(v_fixedParamPerms_1884_, 1);
v___x_1899_ = lean_array_fget_borrowed(v_as_1886_, v_j_1888_);
v_value_1900_ = lean_ctor_get(v___x_1899_, 7);
v___x_1901_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0, &l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0_once, _init_l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0);
v___x_1902_ = lean_array_get_borrowed(v___x_1901_, v_perms_1898_, v_j_1888_);
lean_inc_ref(v_xs_1885_);
lean_inc_ref(v_value_1900_);
lean_inc(v___x_1902_);
v___x_1903_ = l_Lean_Elab_FixedParamPerm_instantiateLambda(v___x_1902_, v_value_1900_, v_xs_1885_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_);
if (lean_obj_tag(v___x_1903_) == 0)
{
lean_object* v_a_1904_; lean_object* v_one_1905_; lean_object* v_n_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; 
v_a_1904_ = lean_ctor_get(v___x_1903_, 0);
lean_inc(v_a_1904_);
lean_dec_ref(v___x_1903_);
v_one_1905_ = lean_unsigned_to_nat(1u);
v_n_1906_ = lean_nat_sub(v_i_1887_, v_one_1905_);
lean_dec(v_i_1887_);
v___x_1907_ = lean_nat_add(v_j_1888_, v_one_1905_);
lean_dec(v_j_1888_);
v___x_1908_ = lean_array_push(v_bs_1889_, v_a_1904_);
v_i_1887_ = v_n_1906_;
v_j_1888_ = v___x_1907_;
v_bs_1889_ = v___x_1908_;
goto _start;
}
else
{
lean_object* v_a_1910_; lean_object* v___x_1912_; uint8_t v_isShared_1913_; uint8_t v_isSharedCheck_1917_; 
lean_dec_ref(v_bs_1889_);
lean_dec(v_j_1888_);
lean_dec(v_i_1887_);
lean_dec_ref(v_xs_1885_);
v_a_1910_ = lean_ctor_get(v___x_1903_, 0);
v_isSharedCheck_1917_ = !lean_is_exclusive(v___x_1903_);
if (v_isSharedCheck_1917_ == 0)
{
v___x_1912_ = v___x_1903_;
v_isShared_1913_ = v_isSharedCheck_1917_;
goto v_resetjp_1911_;
}
else
{
lean_inc(v_a_1910_);
lean_dec(v___x_1903_);
v___x_1912_ = lean_box(0);
v_isShared_1913_ = v_isSharedCheck_1917_;
goto v_resetjp_1911_;
}
v_resetjp_1911_:
{
lean_object* v___x_1915_; 
if (v_isShared_1913_ == 0)
{
v___x_1915_ = v___x_1912_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v_a_1910_);
v___x_1915_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
return v___x_1915_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___redArg___boxed(lean_object* v_fixedParamPerms_1918_, lean_object* v_xs_1919_, lean_object* v_as_1920_, lean_object* v_i_1921_, lean_object* v_j_1922_, lean_object* v_bs_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_){
_start:
{
lean_object* v_res_1929_; 
v_res_1929_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___redArg(v_fixedParamPerms_1918_, v_xs_1919_, v_as_1920_, v_i_1921_, v_j_1922_, v_bs_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_);
lean_dec(v___y_1927_);
lean_dec_ref(v___y_1926_);
lean_dec(v___y_1925_);
lean_dec_ref(v___y_1924_);
lean_dec_ref(v_as_1920_);
lean_dec_ref(v_fixedParamPerms_1918_);
return v_res_1929_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__0(lean_object* v_a_1930_, lean_object* v_a_1931_){
_start:
{
if (lean_obj_tag(v_a_1930_) == 0)
{
lean_object* v___x_1932_; 
v___x_1932_ = l_List_reverse___redArg(v_a_1931_);
return v___x_1932_;
}
else
{
lean_object* v_head_1933_; lean_object* v_tail_1934_; lean_object* v___x_1936_; uint8_t v_isShared_1937_; uint8_t v_isSharedCheck_1945_; 
v_head_1933_ = lean_ctor_get(v_a_1930_, 0);
v_tail_1934_ = lean_ctor_get(v_a_1930_, 1);
v_isSharedCheck_1945_ = !lean_is_exclusive(v_a_1930_);
if (v_isSharedCheck_1945_ == 0)
{
v___x_1936_ = v_a_1930_;
v_isShared_1937_ = v_isSharedCheck_1945_;
goto v_resetjp_1935_;
}
else
{
lean_inc(v_tail_1934_);
lean_inc(v_head_1933_);
lean_dec(v_a_1930_);
v___x_1936_ = lean_box(0);
v_isShared_1937_ = v_isSharedCheck_1945_;
goto v_resetjp_1935_;
}
v_resetjp_1935_:
{
lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1942_; 
v___x_1938_ = l_Nat_reprFast(v_head_1933_);
v___x_1939_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1939_, 0, v___x_1938_);
v___x_1940_ = l_Lean_MessageData_ofFormat(v___x_1939_);
if (v_isShared_1937_ == 0)
{
lean_ctor_set(v___x_1936_, 1, v_a_1931_);
lean_ctor_set(v___x_1936_, 0, v___x_1940_);
v___x_1942_ = v___x_1936_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v___x_1940_);
lean_ctor_set(v_reuseFailAlloc_1944_, 1, v_a_1931_);
v___x_1942_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
v_a_1930_ = v_tail_1934_;
v_a_1931_ = v___x_1942_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__20(lean_object* v_a_1946_, lean_object* v_a_1947_){
_start:
{
if (lean_obj_tag(v_a_1946_) == 0)
{
lean_object* v___x_1948_; 
v___x_1948_ = l_List_reverse___redArg(v_a_1947_);
return v___x_1948_;
}
else
{
lean_object* v_head_1949_; lean_object* v_tail_1950_; lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_1962_; 
v_head_1949_ = lean_ctor_get(v_a_1946_, 0);
v_tail_1950_ = lean_ctor_get(v_a_1946_, 1);
v_isSharedCheck_1962_ = !lean_is_exclusive(v_a_1946_);
if (v_isSharedCheck_1962_ == 0)
{
v___x_1952_ = v_a_1946_;
v_isShared_1953_ = v_isSharedCheck_1962_;
goto v_resetjp_1951_;
}
else
{
lean_inc(v_tail_1950_);
lean_inc(v_head_1949_);
lean_dec(v_a_1946_);
v___x_1952_ = lean_box(0);
v_isShared_1953_ = v_isSharedCheck_1962_;
goto v_resetjp_1951_;
}
v_resetjp_1951_:
{
lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1959_; 
v___x_1954_ = lean_array_to_list(v_head_1949_);
v___x_1955_ = lean_box(0);
v___x_1956_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__0(v___x_1954_, v___x_1955_);
v___x_1957_ = l_Lean_MessageData_ofList(v___x_1956_);
if (v_isShared_1953_ == 0)
{
lean_ctor_set(v___x_1952_, 1, v_a_1947_);
lean_ctor_set(v___x_1952_, 0, v___x_1957_);
v___x_1959_ = v___x_1952_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v___x_1957_);
lean_ctor_set(v_reuseFailAlloc_1961_, 1, v_a_1947_);
v___x_1959_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
v_a_1946_ = v_tail_1950_;
v_a_1947_ = v___x_1959_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___redArg(lean_object* v_fixedParamPerms_1963_, lean_object* v_xs_1964_, lean_object* v_as_1965_, lean_object* v_i_1966_, lean_object* v_j_1967_, lean_object* v_bs_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_){
_start:
{
lean_object* v_zero_1974_; uint8_t v_isZero_1975_; 
v_zero_1974_ = lean_unsigned_to_nat(0u);
v_isZero_1975_ = lean_nat_dec_eq(v_i_1966_, v_zero_1974_);
if (v_isZero_1975_ == 1)
{
lean_object* v___x_1976_; 
lean_dec(v_j_1967_);
lean_dec(v_i_1966_);
lean_dec_ref(v_xs_1964_);
v___x_1976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1976_, 0, v_bs_1968_);
return v___x_1976_;
}
else
{
lean_object* v_perms_1977_; lean_object* v___x_1978_; lean_object* v_type_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; 
v_perms_1977_ = lean_ctor_get(v_fixedParamPerms_1963_, 1);
v___x_1978_ = lean_array_fget_borrowed(v_as_1965_, v_j_1967_);
v_type_1979_ = lean_ctor_get(v___x_1978_, 6);
v___x_1980_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0, &l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0_once, _init_l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0);
v___x_1981_ = lean_array_get_borrowed(v___x_1980_, v_perms_1977_, v_j_1967_);
lean_inc_ref(v_xs_1964_);
lean_inc_ref(v_type_1979_);
lean_inc(v___x_1981_);
v___x_1982_ = l_Lean_Elab_FixedParamPerm_instantiateForall(v___x_1981_, v_type_1979_, v_xs_1964_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_);
if (lean_obj_tag(v___x_1982_) == 0)
{
lean_object* v_a_1983_; lean_object* v_one_1984_; lean_object* v_n_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; 
v_a_1983_ = lean_ctor_get(v___x_1982_, 0);
lean_inc(v_a_1983_);
lean_dec_ref(v___x_1982_);
v_one_1984_ = lean_unsigned_to_nat(1u);
v_n_1985_ = lean_nat_sub(v_i_1966_, v_one_1984_);
lean_dec(v_i_1966_);
v___x_1986_ = lean_nat_add(v_j_1967_, v_one_1984_);
lean_dec(v_j_1967_);
v___x_1987_ = lean_array_push(v_bs_1968_, v_a_1983_);
v_i_1966_ = v_n_1985_;
v_j_1967_ = v___x_1986_;
v_bs_1968_ = v___x_1987_;
goto _start;
}
else
{
lean_object* v_a_1989_; lean_object* v___x_1991_; uint8_t v_isShared_1992_; uint8_t v_isSharedCheck_1996_; 
lean_dec_ref(v_bs_1968_);
lean_dec(v_j_1967_);
lean_dec(v_i_1966_);
lean_dec_ref(v_xs_1964_);
v_a_1989_ = lean_ctor_get(v___x_1982_, 0);
v_isSharedCheck_1996_ = !lean_is_exclusive(v___x_1982_);
if (v_isSharedCheck_1996_ == 0)
{
v___x_1991_ = v___x_1982_;
v_isShared_1992_ = v_isSharedCheck_1996_;
goto v_resetjp_1990_;
}
else
{
lean_inc(v_a_1989_);
lean_dec(v___x_1982_);
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
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___redArg___boxed(lean_object* v_fixedParamPerms_1997_, lean_object* v_xs_1998_, lean_object* v_as_1999_, lean_object* v_i_2000_, lean_object* v_j_2001_, lean_object* v_bs_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_){
_start:
{
lean_object* v_res_2008_; 
v_res_2008_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___redArg(v_fixedParamPerms_1997_, v_xs_1998_, v_as_1999_, v_i_2000_, v_j_2001_, v_bs_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_);
lean_dec(v___y_2006_);
lean_dec_ref(v___y_2005_);
lean_dec(v___y_2004_);
lean_dec_ref(v___y_2003_);
lean_dec_ref(v_as_1999_);
lean_dec_ref(v_fixedParamPerms_1997_);
return v_res_2008_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__9(void){
_start:
{
lean_object* v___x_2023_; lean_object* v___x_2024_; 
v___x_2023_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__8));
v___x_2024_ = l_Lean_stringToMessageData(v___x_2023_);
return v___x_2024_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__11(void){
_start:
{
lean_object* v___x_2026_; lean_object* v___x_2027_; 
v___x_2026_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__10));
v___x_2027_ = l_Lean_stringToMessageData(v___x_2026_);
return v___x_2027_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion(lean_object* v_preDefs_2028_, lean_object* v_fixedParamPerms_2029_, lean_object* v_xs_2030_, lean_object* v_recArgInfos_2031_, lean_object* v_a_2032_, lean_object* v_a_2033_, lean_object* v_a_2034_, lean_object* v_a_2035_){
_start:
{
lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; 
v___x_2037_ = lean_array_get_size(v_preDefs_2028_);
v___x_2038_ = lean_unsigned_to_nat(0u);
v___x_2039_ = lean_mk_empty_array_with_capacity(v___x_2037_);
lean_inc_ref(v___x_2039_);
lean_inc_ref(v_xs_2030_);
v___x_2040_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___redArg(v_fixedParamPerms_2029_, v_xs_2030_, v_preDefs_2028_, v___x_2037_, v___x_2038_, v___x_2039_, v_a_2032_, v_a_2033_, v_a_2034_, v_a_2035_);
if (lean_obj_tag(v___x_2040_) == 0)
{
lean_object* v_a_2041_; lean_object* v___x_2042_; 
v_a_2041_ = lean_ctor_get(v___x_2040_, 0);
lean_inc(v_a_2041_);
lean_dec_ref(v___x_2040_);
lean_inc_ref(v_xs_2030_);
v___x_2042_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___redArg(v_fixedParamPerms_2029_, v_xs_2030_, v_preDefs_2028_, v___x_2037_, v___x_2038_, v___x_2039_, v_a_2032_, v_a_2033_, v_a_2034_, v_a_2035_);
if (lean_obj_tag(v___x_2042_) == 0)
{
lean_object* v_a_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v_indGroupInst_2046_; lean_object* v_toIndGroupInfo_2047_; lean_object* v_all_2048_; lean_object* v___x_2050_; uint8_t v_isShared_2051_; uint8_t v_isSharedCheck_2134_; 
v_a_2043_ = lean_ctor_get(v___x_2042_, 0);
lean_inc(v_a_2043_);
lean_dec_ref(v___x_2042_);
v___x_2044_ = l_Lean_Elab_Structural_instInhabitedRecArgInfo_default;
v___x_2045_ = lean_array_get_borrowed(v___x_2044_, v_recArgInfos_2031_, v___x_2038_);
v_indGroupInst_2046_ = lean_ctor_get(v___x_2045_, 4);
v_toIndGroupInfo_2047_ = lean_ctor_get(v_indGroupInst_2046_, 0);
lean_inc_ref(v_toIndGroupInfo_2047_);
v_all_2048_ = lean_ctor_get(v_toIndGroupInfo_2047_, 0);
v_isSharedCheck_2134_ = !lean_is_exclusive(v_toIndGroupInfo_2047_);
if (v_isSharedCheck_2134_ == 0)
{
lean_object* v_unused_2135_; 
v_unused_2135_ = lean_ctor_get(v_toIndGroupInfo_2047_, 1);
lean_dec(v_unused_2135_);
v___x_2050_ = v_toIndGroupInfo_2047_;
v_isShared_2051_ = v_isSharedCheck_2134_;
goto v_resetjp_2049_;
}
else
{
lean_inc(v_all_2048_);
lean_dec(v_toIndGroupInfo_2047_);
v___x_2050_ = lean_box(0);
v_isShared_2051_ = v_isSharedCheck_2134_;
goto v_resetjp_2049_;
}
v_resetjp_2049_:
{
lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; 
v___x_2052_ = lean_box(0);
v___x_2053_ = lean_array_get(v___x_2052_, v_all_2048_, v___x_2038_);
lean_dec_ref(v_all_2048_);
v___x_2054_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4(v___x_2053_, v_a_2032_, v_a_2033_, v_a_2034_, v_a_2035_);
if (lean_obj_tag(v___x_2054_) == 0)
{
lean_object* v_a_2055_; lean_object* v___x_2056_; lean_object* v___f_2057_; lean_object* v___x_2058_; lean_object* v_a_2059_; lean_object* v___f_2060_; lean_object* v___f_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___y_2066_; lean_object* v___y_2067_; lean_object* v___y_2068_; lean_object* v___y_2069_; uint8_t v___x_2102_; 
v_a_2055_ = lean_ctor_get(v___x_2054_, 0);
lean_inc(v_a_2055_);
lean_dec_ref(v___x_2054_);
v___x_2056_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__3));
v___f_2057_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__4));
v___x_2058_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0(v___x_2056_, v_a_2032_, v_a_2033_, v_a_2034_, v_a_2035_);
v_a_2059_ = lean_ctor_get(v___x_2058_, 0);
lean_inc(v_a_2059_);
lean_dec_ref(v___x_2058_);
v___f_2060_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__5));
v___f_2061_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__6));
v___x_2062_ = l_Lean_InductiveVal_numTypeFormers(v_a_2055_);
v___x_2063_ = l_Array_range(v___x_2062_);
v___x_2064_ = l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5(v___f_2061_, v_recArgInfos_2031_, v___x_2063_);
v___x_2102_ = lean_unbox(v_a_2059_);
lean_dec(v_a_2059_);
if (v___x_2102_ == 0)
{
lean_del_object(v___x_2050_);
v___y_2066_ = v_a_2032_;
v___y_2067_ = v_a_2033_;
v___y_2068_ = v_a_2034_;
v___y_2069_ = v_a_2035_;
goto v___jp_2065_;
}
else
{
lean_object* v_toConstantVal_2103_; lean_object* v_name_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2108_; 
v_toConstantVal_2103_ = lean_ctor_get(v_a_2055_, 0);
v_name_2104_ = lean_ctor_get(v_toConstantVal_2103_, 0);
v___x_2105_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__9, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__9_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__9);
lean_inc(v_name_2104_);
v___x_2106_ = l_Lean_MessageData_ofName(v_name_2104_);
if (v_isShared_2051_ == 0)
{
lean_ctor_set_tag(v___x_2050_, 7);
lean_ctor_set(v___x_2050_, 1, v___x_2106_);
lean_ctor_set(v___x_2050_, 0, v___x_2105_);
v___x_2108_ = v___x_2050_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2125_; 
v_reuseFailAlloc_2125_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2125_, 0, v___x_2105_);
lean_ctor_set(v_reuseFailAlloc_2125_, 1, v___x_2106_);
v___x_2108_ = v_reuseFailAlloc_2125_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; 
v___x_2109_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__11, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__11_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__11);
v___x_2110_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2110_, 0, v___x_2108_);
lean_ctor_set(v___x_2110_, 1, v___x_2109_);
lean_inc_ref(v___x_2064_);
v___x_2111_ = lean_array_to_list(v___x_2064_);
v___x_2112_ = lean_box(0);
v___x_2113_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__20(v___x_2111_, v___x_2112_);
v___x_2114_ = l_Lean_MessageData_ofList(v___x_2113_);
v___x_2115_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2115_, 0, v___x_2110_);
lean_ctor_set(v___x_2115_, 1, v___x_2114_);
v___x_2116_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_2056_, v___x_2115_, v_a_2032_, v_a_2033_, v_a_2034_, v_a_2035_);
if (lean_obj_tag(v___x_2116_) == 0)
{
lean_dec_ref(v___x_2116_);
v___y_2066_ = v_a_2032_;
v___y_2067_ = v_a_2033_;
v___y_2068_ = v_a_2034_;
v___y_2069_ = v_a_2035_;
goto v___jp_2065_;
}
else
{
lean_object* v_a_2117_; lean_object* v___x_2119_; uint8_t v_isShared_2120_; uint8_t v_isSharedCheck_2124_; 
lean_dec_ref(v___x_2064_);
lean_dec(v_a_2055_);
lean_dec(v_a_2043_);
lean_dec(v_a_2041_);
lean_dec_ref(v_recArgInfos_2031_);
lean_dec_ref(v_xs_2030_);
lean_dec_ref(v_fixedParamPerms_2029_);
lean_dec_ref(v_preDefs_2028_);
v_a_2117_ = lean_ctor_get(v___x_2116_, 0);
v_isSharedCheck_2124_ = !lean_is_exclusive(v___x_2116_);
if (v_isSharedCheck_2124_ == 0)
{
v___x_2119_ = v___x_2116_;
v_isShared_2120_ = v_isSharedCheck_2124_;
goto v_resetjp_2118_;
}
else
{
lean_inc(v_a_2117_);
lean_dec(v___x_2116_);
v___x_2119_ = lean_box(0);
v_isShared_2120_ = v_isSharedCheck_2124_;
goto v_resetjp_2118_;
}
v_resetjp_2118_:
{
lean_object* v___x_2122_; 
if (v_isShared_2120_ == 0)
{
v___x_2122_ = v___x_2119_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2123_; 
v_reuseFailAlloc_2123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2123_, 0, v_a_2117_);
v___x_2122_ = v_reuseFailAlloc_2123_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
return v___x_2122_;
}
}
}
}
}
v___jp_2065_:
{
lean_object* v_toConstantVal_2070_; lean_object* v_numIndices_2071_; lean_object* v_name_2072_; lean_object* v___x_2073_; 
v_toConstantVal_2070_ = lean_ctor_get(v_a_2055_, 0);
lean_inc_ref(v_toConstantVal_2070_);
v_numIndices_2071_ = lean_ctor_get(v_a_2055_, 2);
lean_inc(v_numIndices_2071_);
lean_dec(v_a_2055_);
v_name_2072_ = lean_ctor_get(v_toConstantVal_2070_, 0);
lean_inc(v_name_2072_);
lean_dec_ref(v_toConstantVal_2070_);
v___x_2073_ = l_Lean_Meta_isInductivePredicate(v_name_2072_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_);
if (lean_obj_tag(v___x_2073_) == 0)
{
lean_object* v_a_2074_; lean_object* v___f_2075_; uint8_t v___x_2076_; 
v_a_2074_ = lean_ctor_get(v___x_2073_, 0);
lean_inc_n(v_a_2074_, 2);
lean_dec_ref(v___x_2073_);
lean_inc(v_numIndices_2071_);
lean_inc_ref(v_preDefs_2028_);
lean_inc_ref(v_xs_2030_);
lean_inc_ref(v_fixedParamPerms_2029_);
lean_inc_ref(v___x_2064_);
lean_inc(v_a_2041_);
lean_inc_ref(v_recArgInfos_2031_);
v___f_2075_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___boxed), 19, 12);
lean_closure_set(v___f_2075_, 0, v___f_2057_);
lean_closure_set(v___f_2075_, 1, v_recArgInfos_2031_);
lean_closure_set(v___f_2075_, 2, v_a_2041_);
lean_closure_set(v___f_2075_, 3, v___x_2064_);
lean_closure_set(v___f_2075_, 4, v___x_2038_);
lean_closure_set(v___f_2075_, 5, v_fixedParamPerms_2029_);
lean_closure_set(v___f_2075_, 6, v_xs_2030_);
lean_closure_set(v___f_2075_, 7, v_preDefs_2028_);
lean_closure_set(v___f_2075_, 8, v_numIndices_2071_);
lean_closure_set(v___f_2075_, 9, v___f_2060_);
lean_closure_set(v___f_2075_, 10, v___x_2056_);
lean_closure_set(v___f_2075_, 11, v_a_2074_);
v___x_2076_ = lean_unbox(v_a_2074_);
if (v___x_2076_ == 0)
{
lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; 
lean_dec_ref(v___f_2075_);
v___x_2077_ = lean_array_get_size(v_recArgInfos_2031_);
v___x_2078_ = lean_mk_empty_array_with_capacity(v___x_2077_);
v___x_2079_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___redArg(v_a_2041_, v_a_2043_, v_recArgInfos_2031_, v___x_2077_, v___x_2038_, v___x_2078_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_);
lean_dec(v_a_2043_);
if (lean_obj_tag(v___x_2079_) == 0)
{
lean_object* v_a_2080_; lean_object* v___x_2081_; uint8_t v___x_2082_; lean_object* v___x_2083_; 
v_a_2080_ = lean_ctor_get(v___x_2079_, 0);
lean_inc(v_a_2080_);
lean_dec_ref(v___x_2079_);
v___x_2081_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__7));
v___x_2082_ = lean_unbox(v_a_2074_);
lean_dec(v_a_2074_);
v___x_2083_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2(v___f_2057_, v_recArgInfos_2031_, v_a_2041_, v___x_2064_, v___x_2038_, v_fixedParamPerms_2029_, v_xs_2030_, v_preDefs_2028_, v_numIndices_2071_, v___f_2060_, v___x_2056_, v___x_2082_, v___x_2081_, v_a_2080_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_);
lean_dec(v_numIndices_2071_);
lean_dec(v_a_2041_);
return v___x_2083_;
}
else
{
lean_object* v_a_2084_; lean_object* v___x_2086_; uint8_t v_isShared_2087_; uint8_t v_isSharedCheck_2091_; 
lean_dec(v_a_2074_);
lean_dec(v_numIndices_2071_);
lean_dec_ref(v___x_2064_);
lean_dec(v_a_2041_);
lean_dec_ref(v_recArgInfos_2031_);
lean_dec_ref(v_xs_2030_);
lean_dec_ref(v_fixedParamPerms_2029_);
lean_dec_ref(v_preDefs_2028_);
v_a_2084_ = lean_ctor_get(v___x_2079_, 0);
v_isSharedCheck_2091_ = !lean_is_exclusive(v___x_2079_);
if (v_isSharedCheck_2091_ == 0)
{
v___x_2086_ = v___x_2079_;
v_isShared_2087_ = v_isSharedCheck_2091_;
goto v_resetjp_2085_;
}
else
{
lean_inc(v_a_2084_);
lean_dec(v___x_2079_);
v___x_2086_ = lean_box(0);
v_isShared_2087_ = v_isSharedCheck_2091_;
goto v_resetjp_2085_;
}
v_resetjp_2085_:
{
lean_object* v___x_2089_; 
if (v_isShared_2087_ == 0)
{
v___x_2089_ = v___x_2086_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v_a_2084_);
v___x_2089_ = v_reuseFailAlloc_2090_;
goto v_reusejp_2088_;
}
v_reusejp_2088_:
{
return v___x_2089_;
}
}
}
}
else
{
lean_object* v___f_2092_; lean_object* v___x_2093_; 
lean_dec(v_a_2074_);
lean_dec(v_numIndices_2071_);
lean_dec_ref(v___x_2064_);
lean_dec(v_a_2043_);
lean_dec_ref(v_xs_2030_);
lean_dec_ref(v_fixedParamPerms_2029_);
lean_dec_ref(v_preDefs_2028_);
lean_inc(v_a_2041_);
v___f_2092_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__3___boxed), 10, 4);
lean_closure_set(v___f_2092_, 0, v_recArgInfos_2031_);
lean_closure_set(v___f_2092_, 1, v_a_2041_);
lean_closure_set(v___f_2092_, 2, v___x_2038_);
lean_closure_set(v___f_2092_, 3, v___f_2075_);
v___x_2093_ = l_Lean_Elab_Structural_withFunTypes___redArg(v_a_2041_, v___f_2092_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_);
return v___x_2093_;
}
}
else
{
lean_object* v_a_2094_; lean_object* v___x_2096_; uint8_t v_isShared_2097_; uint8_t v_isSharedCheck_2101_; 
lean_dec(v_numIndices_2071_);
lean_dec_ref(v___x_2064_);
lean_dec(v_a_2043_);
lean_dec(v_a_2041_);
lean_dec_ref(v_recArgInfos_2031_);
lean_dec_ref(v_xs_2030_);
lean_dec_ref(v_fixedParamPerms_2029_);
lean_dec_ref(v_preDefs_2028_);
v_a_2094_ = lean_ctor_get(v___x_2073_, 0);
v_isSharedCheck_2101_ = !lean_is_exclusive(v___x_2073_);
if (v_isSharedCheck_2101_ == 0)
{
v___x_2096_ = v___x_2073_;
v_isShared_2097_ = v_isSharedCheck_2101_;
goto v_resetjp_2095_;
}
else
{
lean_inc(v_a_2094_);
lean_dec(v___x_2073_);
v___x_2096_ = lean_box(0);
v_isShared_2097_ = v_isSharedCheck_2101_;
goto v_resetjp_2095_;
}
v_resetjp_2095_:
{
lean_object* v___x_2099_; 
if (v_isShared_2097_ == 0)
{
v___x_2099_ = v___x_2096_;
goto v_reusejp_2098_;
}
else
{
lean_object* v_reuseFailAlloc_2100_; 
v_reuseFailAlloc_2100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2100_, 0, v_a_2094_);
v___x_2099_ = v_reuseFailAlloc_2100_;
goto v_reusejp_2098_;
}
v_reusejp_2098_:
{
return v___x_2099_;
}
}
}
}
}
else
{
lean_object* v_a_2126_; lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2133_; 
lean_del_object(v___x_2050_);
lean_dec(v_a_2043_);
lean_dec(v_a_2041_);
lean_dec_ref(v_recArgInfos_2031_);
lean_dec_ref(v_xs_2030_);
lean_dec_ref(v_fixedParamPerms_2029_);
lean_dec_ref(v_preDefs_2028_);
v_a_2126_ = lean_ctor_get(v___x_2054_, 0);
v_isSharedCheck_2133_ = !lean_is_exclusive(v___x_2054_);
if (v_isSharedCheck_2133_ == 0)
{
v___x_2128_ = v___x_2054_;
v_isShared_2129_ = v_isSharedCheck_2133_;
goto v_resetjp_2127_;
}
else
{
lean_inc(v_a_2126_);
lean_dec(v___x_2054_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2133_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
lean_object* v___x_2131_; 
if (v_isShared_2129_ == 0)
{
v___x_2131_ = v___x_2128_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v_a_2126_);
v___x_2131_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
return v___x_2131_;
}
}
}
}
}
else
{
lean_object* v_a_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2143_; 
lean_dec(v_a_2041_);
lean_dec_ref(v_recArgInfos_2031_);
lean_dec_ref(v_xs_2030_);
lean_dec_ref(v_fixedParamPerms_2029_);
lean_dec_ref(v_preDefs_2028_);
v_a_2136_ = lean_ctor_get(v___x_2042_, 0);
v_isSharedCheck_2143_ = !lean_is_exclusive(v___x_2042_);
if (v_isSharedCheck_2143_ == 0)
{
v___x_2138_ = v___x_2042_;
v_isShared_2139_ = v_isSharedCheck_2143_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_a_2136_);
lean_dec(v___x_2042_);
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
lean_object* v_a_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2151_; 
lean_dec_ref(v___x_2039_);
lean_dec_ref(v_recArgInfos_2031_);
lean_dec_ref(v_xs_2030_);
lean_dec_ref(v_fixedParamPerms_2029_);
lean_dec_ref(v_preDefs_2028_);
v_a_2144_ = lean_ctor_get(v___x_2040_, 0);
v_isSharedCheck_2151_ = !lean_is_exclusive(v___x_2040_);
if (v_isSharedCheck_2151_ == 0)
{
v___x_2146_ = v___x_2040_;
v_isShared_2147_ = v_isSharedCheck_2151_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_a_2144_);
lean_dec(v___x_2040_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___boxed(lean_object* v_preDefs_2152_, lean_object* v_fixedParamPerms_2153_, lean_object* v_xs_2154_, lean_object* v_recArgInfos_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_, lean_object* v_a_2160_){
_start:
{
lean_object* v_res_2161_; 
v_res_2161_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion(v_preDefs_2152_, v_fixedParamPerms_2153_, v_xs_2154_, v_recArgInfos_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_);
lean_dec(v_a_2159_);
lean_dec_ref(v_a_2158_);
lean_dec(v_a_2157_);
lean_dec_ref(v_a_2156_);
return v_res_2161_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2(lean_object* v_fixedParamPerms_2162_, lean_object* v_xs_2163_, lean_object* v_as_2164_, lean_object* v_i_2165_, lean_object* v_j_2166_, lean_object* v_inv_2167_, lean_object* v_bs_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_){
_start:
{
lean_object* v___x_2174_; 
v___x_2174_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___redArg(v_fixedParamPerms_2162_, v_xs_2163_, v_as_2164_, v_i_2165_, v_j_2166_, v_bs_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_);
return v___x_2174_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___boxed(lean_object* v_fixedParamPerms_2175_, lean_object* v_xs_2176_, lean_object* v_as_2177_, lean_object* v_i_2178_, lean_object* v_j_2179_, lean_object* v_inv_2180_, lean_object* v_bs_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_){
_start:
{
lean_object* v_res_2187_; 
v_res_2187_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2(v_fixedParamPerms_2175_, v_xs_2176_, v_as_2177_, v_i_2178_, v_j_2179_, v_inv_2180_, v_bs_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_);
lean_dec(v___y_2185_);
lean_dec_ref(v___y_2184_);
lean_dec(v___y_2183_);
lean_dec_ref(v___y_2182_);
lean_dec_ref(v_as_2177_);
lean_dec_ref(v_fixedParamPerms_2175_);
return v_res_2187_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3(lean_object* v_fixedParamPerms_2188_, lean_object* v_xs_2189_, lean_object* v_as_2190_, lean_object* v_i_2191_, lean_object* v_j_2192_, lean_object* v_inv_2193_, lean_object* v_bs_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_){
_start:
{
lean_object* v___x_2200_; 
v___x_2200_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___redArg(v_fixedParamPerms_2188_, v_xs_2189_, v_as_2190_, v_i_2191_, v_j_2192_, v_bs_2194_, v___y_2195_, v___y_2196_, v___y_2197_, v___y_2198_);
return v___x_2200_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___boxed(lean_object* v_fixedParamPerms_2201_, lean_object* v_xs_2202_, lean_object* v_as_2203_, lean_object* v_i_2204_, lean_object* v_j_2205_, lean_object* v_inv_2206_, lean_object* v_bs_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_){
_start:
{
lean_object* v_res_2213_; 
v_res_2213_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3(v_fixedParamPerms_2201_, v_xs_2202_, v_as_2203_, v_i_2204_, v_j_2205_, v_inv_2206_, v_bs_2207_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_);
lean_dec(v___y_2211_);
lean_dec_ref(v___y_2210_);
lean_dec(v___y_2209_);
lean_dec_ref(v___y_2208_);
lean_dec_ref(v_as_2203_);
lean_dec_ref(v_fixedParamPerms_2201_);
return v_res_2213_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14(lean_object* v_00_u03b3_2214_, lean_object* v_msg_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_){
_start:
{
lean_object* v___x_2221_; 
v___x_2221_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg(v_msg_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_);
return v___x_2221_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___boxed(lean_object* v_00_u03b3_2222_, lean_object* v_msg_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_){
_start:
{
lean_object* v_res_2229_; 
v_res_2229_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14(v_00_u03b3_2222_, v_msg_2223_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_);
lean_dec(v___y_2227_);
lean_dec_ref(v___y_2226_);
lean_dec(v___y_2225_);
lean_dec_ref(v___y_2224_);
return v_res_2229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6(lean_object* v_00_u03b3_2230_, lean_object* v_00_u03b1_2231_, lean_object* v_f_2232_, lean_object* v_positions_2233_, lean_object* v_ys_2234_, lean_object* v_xs_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_){
_start:
{
lean_object* v___x_2241_; 
v___x_2241_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg(v_f_2232_, v_positions_2233_, v_ys_2234_, v_xs_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_);
return v___x_2241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___boxed(lean_object* v_00_u03b3_2242_, lean_object* v_00_u03b1_2243_, lean_object* v_f_2244_, lean_object* v_positions_2245_, lean_object* v_ys_2246_, lean_object* v_xs_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_){
_start:
{
lean_object* v_res_2253_; 
v_res_2253_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6(v_00_u03b3_2242_, v_00_u03b1_2243_, v_f_2244_, v_positions_2245_, v_ys_2246_, v_xs_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_);
lean_dec(v___y_2251_);
lean_dec_ref(v___y_2250_);
lean_dec(v___y_2249_);
lean_dec_ref(v___y_2248_);
lean_dec_ref(v_xs_2247_);
lean_dec_ref(v_ys_2246_);
lean_dec_ref(v_positions_2245_);
return v_res_2253_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7(lean_object* v___x_2254_, lean_object* v_a_2255_, lean_object* v_a_2256_, lean_object* v_funTypes_2257_, lean_object* v_as_2258_, lean_object* v_i_2259_, lean_object* v_j_2260_, lean_object* v_inv_2261_, lean_object* v_bs_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_){
_start:
{
lean_object* v___x_2268_; 
v___x_2268_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg(v___x_2254_, v_a_2255_, v_a_2256_, v_funTypes_2257_, v_as_2258_, v_i_2259_, v_j_2260_, v_bs_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_);
return v___x_2268_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___boxed(lean_object* v___x_2269_, lean_object* v_a_2270_, lean_object* v_a_2271_, lean_object* v_funTypes_2272_, lean_object* v_as_2273_, lean_object* v_i_2274_, lean_object* v_j_2275_, lean_object* v_inv_2276_, lean_object* v_bs_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_){
_start:
{
lean_object* v_res_2283_; 
v_res_2283_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7(v___x_2269_, v_a_2270_, v_a_2271_, v_funTypes_2272_, v_as_2273_, v_i_2274_, v_j_2275_, v_inv_2276_, v_bs_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_);
lean_dec(v___y_2281_);
lean_dec_ref(v___y_2280_);
lean_dec(v___y_2279_);
lean_dec_ref(v___y_2278_);
lean_dec_ref(v_as_2273_);
return v_res_2283_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8(lean_object* v_fixedParamPerms_2284_, lean_object* v_xs_2285_, lean_object* v_as_2286_, lean_object* v_i_2287_, lean_object* v_j_2288_, lean_object* v_inv_2289_, lean_object* v_bs_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_){
_start:
{
lean_object* v___x_2296_; 
v___x_2296_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg(v_fixedParamPerms_2284_, v_xs_2285_, v_as_2286_, v_i_2287_, v_j_2288_, v_bs_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_);
return v___x_2296_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___boxed(lean_object* v_fixedParamPerms_2297_, lean_object* v_xs_2298_, lean_object* v_as_2299_, lean_object* v_i_2300_, lean_object* v_j_2301_, lean_object* v_inv_2302_, lean_object* v_bs_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_){
_start:
{
lean_object* v_res_2309_; 
v_res_2309_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8(v_fixedParamPerms_2297_, v_xs_2298_, v_as_2299_, v_i_2300_, v_j_2301_, v_inv_2302_, v_bs_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_);
lean_dec(v___y_2307_);
lean_dec_ref(v___y_2306_);
lean_dec(v___y_2305_);
lean_dec_ref(v___y_2304_);
lean_dec_ref(v_as_2299_);
return v_res_2309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12(lean_object* v_00_u03b1_2310_, lean_object* v_preDefs_2311_, lean_object* v_k_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_){
_start:
{
lean_object* v___x_2318_; 
v___x_2318_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v_preDefs_2311_, v_k_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_);
return v___x_2318_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___boxed(lean_object* v_00_u03b1_2319_, lean_object* v_preDefs_2320_, lean_object* v_k_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_){
_start:
{
lean_object* v_res_2327_; 
v_res_2327_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12(v_00_u03b1_2319_, v_preDefs_2320_, v_k_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_);
lean_dec(v___y_2325_);
lean_dec_ref(v___y_2324_);
lean_dec(v___y_2323_);
lean_dec_ref(v___y_2322_);
return v_res_2327_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14(uint8_t v_a_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_, lean_object* v_recArgInfos_2331_, lean_object* v___x_2332_, lean_object* v_preDefs_2333_, lean_object* v_a_2334_, lean_object* v_as_2335_, lean_object* v_i_2336_, lean_object* v_j_2337_, lean_object* v_inv_2338_, lean_object* v_bs_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_){
_start:
{
lean_object* v___x_2345_; 
v___x_2345_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg(v_a_2328_, v_a_2329_, v_a_2330_, v_recArgInfos_2331_, v___x_2332_, v_preDefs_2333_, v_a_2334_, v_as_2335_, v_i_2336_, v_j_2337_, v_bs_2339_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_);
return v___x_2345_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___boxed(lean_object** _args){
lean_object* v_a_2346_ = _args[0];
lean_object* v_a_2347_ = _args[1];
lean_object* v_a_2348_ = _args[2];
lean_object* v_recArgInfos_2349_ = _args[3];
lean_object* v___x_2350_ = _args[4];
lean_object* v_preDefs_2351_ = _args[5];
lean_object* v_a_2352_ = _args[6];
lean_object* v_as_2353_ = _args[7];
lean_object* v_i_2354_ = _args[8];
lean_object* v_j_2355_ = _args[9];
lean_object* v_inv_2356_ = _args[10];
lean_object* v_bs_2357_ = _args[11];
lean_object* v___y_2358_ = _args[12];
lean_object* v___y_2359_ = _args[13];
lean_object* v___y_2360_ = _args[14];
lean_object* v___y_2361_ = _args[15];
lean_object* v___y_2362_ = _args[16];
_start:
{
uint8_t v_a_30348__boxed_2363_; lean_object* v_res_2364_; 
v_a_30348__boxed_2363_ = lean_unbox(v_a_2346_);
v_res_2364_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14(v_a_30348__boxed_2363_, v_a_2347_, v_a_2348_, v_recArgInfos_2349_, v___x_2350_, v_preDefs_2351_, v_a_2352_, v_as_2353_, v_i_2354_, v_j_2355_, v_inv_2356_, v_bs_2357_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_);
lean_dec(v___y_2361_);
lean_dec_ref(v___y_2360_);
lean_dec(v___y_2359_);
lean_dec_ref(v___y_2358_);
lean_dec_ref(v_as_2353_);
lean_dec_ref(v_a_2348_);
lean_dec_ref(v_a_2347_);
return v_res_2364_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16_spec__29(lean_object* v_declName_2365_, uint8_t v_s_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_){
_start:
{
lean_object* v___x_2372_; 
v___x_2372_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16_spec__29___redArg(v_declName_2365_, v_s_2366_, v___y_2368_, v___y_2370_);
return v___x_2372_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16_spec__29___boxed(lean_object* v_declName_2373_, lean_object* v_s_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_){
_start:
{
uint8_t v_s_boxed_2380_; lean_object* v_res_2381_; 
v_s_boxed_2380_ = lean_unbox(v_s_2374_);
v_res_2381_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16_spec__29(v_declName_2373_, v_s_boxed_2380_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_);
lean_dec(v___y_2378_);
lean_dec_ref(v___y_2377_);
lean_dec(v___y_2376_);
lean_dec_ref(v___y_2375_);
return v_res_2381_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17(lean_object* v_xs_2382_, uint8_t v_a_2383_, lean_object* v_preDefs_2384_, lean_object* v___x_2385_, lean_object* v_as_2386_, lean_object* v_i_2387_, lean_object* v_j_2388_, lean_object* v_inv_2389_, lean_object* v_bs_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_){
_start:
{
lean_object* v___x_2396_; 
v___x_2396_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg(v_xs_2382_, v_a_2383_, v_preDefs_2384_, v___x_2385_, v_as_2386_, v_i_2387_, v_j_2388_, v_bs_2390_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_);
return v___x_2396_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___boxed(lean_object* v_xs_2397_, lean_object* v_a_2398_, lean_object* v_preDefs_2399_, lean_object* v___x_2400_, lean_object* v_as_2401_, lean_object* v_i_2402_, lean_object* v_j_2403_, lean_object* v_inv_2404_, lean_object* v_bs_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_){
_start:
{
uint8_t v_a_30397__boxed_2411_; lean_object* v_res_2412_; 
v_a_30397__boxed_2411_ = lean_unbox(v_a_2398_);
v_res_2412_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17(v_xs_2397_, v_a_30397__boxed_2411_, v_preDefs_2399_, v___x_2400_, v_as_2401_, v_i_2402_, v_j_2403_, v_inv_2404_, v_bs_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_);
lean_dec(v___y_2409_);
lean_dec_ref(v___y_2408_);
lean_dec(v___y_2407_);
lean_dec_ref(v___y_2406_);
lean_dec_ref(v_as_2401_);
lean_dec_ref(v_preDefs_2399_);
lean_dec_ref(v_xs_2397_);
return v_res_2412_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18(lean_object* v_a_2413_, lean_object* v_funTypes_2414_, lean_object* v_as_2415_, lean_object* v_i_2416_, lean_object* v_j_2417_, lean_object* v_inv_2418_, lean_object* v_bs_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_){
_start:
{
lean_object* v___x_2425_; 
v___x_2425_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___redArg(v_a_2413_, v_funTypes_2414_, v_as_2415_, v_i_2416_, v_j_2417_, v_bs_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_);
return v___x_2425_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___boxed(lean_object* v_a_2426_, lean_object* v_funTypes_2427_, lean_object* v_as_2428_, lean_object* v_i_2429_, lean_object* v_j_2430_, lean_object* v_inv_2431_, lean_object* v_bs_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_){
_start:
{
lean_object* v_res_2438_; 
v_res_2438_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18(v_a_2426_, v_funTypes_2427_, v_as_2428_, v_i_2429_, v_j_2430_, v_inv_2431_, v_bs_2432_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_);
lean_dec(v___y_2436_);
lean_dec_ref(v___y_2435_);
lean_dec(v___y_2434_);
lean_dec_ref(v___y_2433_);
lean_dec_ref(v_as_2428_);
lean_dec_ref(v_funTypes_2427_);
lean_dec_ref(v_a_2426_);
return v_res_2438_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19(lean_object* v_a_2439_, lean_object* v_a_2440_, lean_object* v_as_2441_, lean_object* v_i_2442_, lean_object* v_j_2443_, lean_object* v_inv_2444_, lean_object* v_bs_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_){
_start:
{
lean_object* v___x_2451_; 
v___x_2451_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___redArg(v_a_2439_, v_a_2440_, v_as_2441_, v_i_2442_, v_j_2443_, v_bs_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_);
return v___x_2451_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___boxed(lean_object* v_a_2452_, lean_object* v_a_2453_, lean_object* v_as_2454_, lean_object* v_i_2455_, lean_object* v_j_2456_, lean_object* v_inv_2457_, lean_object* v_bs_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_){
_start:
{
lean_object* v_res_2464_; 
v_res_2464_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19(v_a_2452_, v_a_2453_, v_as_2454_, v_i_2455_, v_j_2456_, v_inv_2457_, v_bs_2458_, v___y_2459_, v___y_2460_, v___y_2461_, v___y_2462_);
lean_dec(v___y_2462_);
lean_dec_ref(v___y_2461_);
lean_dec(v___y_2460_);
lean_dec_ref(v___y_2459_);
lean_dec_ref(v_as_2454_);
lean_dec_ref(v_a_2453_);
lean_dec_ref(v_a_2452_);
return v_res_2464_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4(lean_object* v_00_u03b1_2465_, lean_object* v_msg_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_){
_start:
{
lean_object* v___x_2472_; 
v___x_2472_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg(v_msg_2466_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_);
return v___x_2472_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___boxed(lean_object* v_00_u03b1_2473_, lean_object* v_msg_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_){
_start:
{
lean_object* v_res_2480_; 
v_res_2480_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4(v_00_u03b1_2473_, v_msg_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_);
lean_dec(v___y_2478_);
lean_dec_ref(v___y_2477_);
lean_dec(v___y_2476_);
lean_dec_ref(v___y_2475_);
return v_res_2480_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9(lean_object* v_xs_2481_, lean_object* v_ys_2482_, lean_object* v_hsz_2483_, lean_object* v_x_2484_, lean_object* v_x_2485_){
_start:
{
uint8_t v___x_2486_; 
v___x_2486_ = l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9___redArg(v_xs_2481_, v_ys_2482_, v_x_2484_);
return v___x_2486_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9___boxed(lean_object* v_xs_2487_, lean_object* v_ys_2488_, lean_object* v_hsz_2489_, lean_object* v_x_2490_, lean_object* v_x_2491_){
_start:
{
uint8_t v_res_2492_; lean_object* v_r_2493_; 
v_res_2492_ = l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9(v_xs_2487_, v_ys_2488_, v_hsz_2489_, v_x_2490_, v_x_2491_);
lean_dec_ref(v_ys_2488_);
lean_dec_ref(v_xs_2487_);
v_r_2493_ = lean_box(v_res_2492_);
return v_r_2493_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10(lean_object* v_n_2494_, lean_object* v_as_2495_, lean_object* v_lo_2496_, lean_object* v_hi_2497_, lean_object* v_w_2498_, lean_object* v_hlo_2499_, lean_object* v_hhi_2500_){
_start:
{
lean_object* v___x_2501_; 
v___x_2501_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg(v_as_2495_, v_lo_2496_, v_hi_2497_);
return v___x_2501_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___boxed(lean_object* v_n_2502_, lean_object* v_as_2503_, lean_object* v_lo_2504_, lean_object* v_hi_2505_, lean_object* v_w_2506_, lean_object* v_hlo_2507_, lean_object* v_hhi_2508_){
_start:
{
lean_object* v_res_2509_; 
v_res_2509_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10(v_n_2502_, v_as_2503_, v_lo_2504_, v_hi_2505_, v_w_2506_, v_hlo_2507_, v_hhi_2508_);
lean_dec(v_hi_2505_);
lean_dec(v_n_2502_);
return v_res_2509_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15(lean_object* v_00_u03b1_2510_, lean_object* v_00_u03b3_2511_, lean_object* v_xs_2512_, lean_object* v_f_2513_, lean_object* v_as_2514_, lean_object* v_bs_2515_, lean_object* v_i_2516_, lean_object* v_cs_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_){
_start:
{
lean_object* v___x_2523_; 
v___x_2523_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15___redArg(v_xs_2512_, v_f_2513_, v_as_2514_, v_bs_2515_, v_i_2516_, v_cs_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_);
return v___x_2523_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15___boxed(lean_object* v_00_u03b1_2524_, lean_object* v_00_u03b3_2525_, lean_object* v_xs_2526_, lean_object* v_f_2527_, lean_object* v_as_2528_, lean_object* v_bs_2529_, lean_object* v_i_2530_, lean_object* v_cs_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_){
_start:
{
lean_object* v_res_2537_; 
v_res_2537_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15(v_00_u03b1_2524_, v_00_u03b3_2525_, v_xs_2526_, v_f_2527_, v_as_2528_, v_bs_2529_, v_i_2530_, v_cs_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_);
lean_dec(v___y_2535_);
lean_dec_ref(v___y_2534_);
lean_dec(v___y_2533_);
lean_dec_ref(v___y_2532_);
lean_dec_ref(v_bs_2529_);
lean_dec_ref(v_as_2528_);
lean_dec_ref(v_xs_2526_);
return v_res_2537_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__24(lean_object* v_env_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_){
_start:
{
lean_object* v___x_2544_; 
v___x_2544_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__24___redArg(v_env_2538_, v___y_2540_, v___y_2542_);
return v___x_2544_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__24___boxed(lean_object* v_env_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_){
_start:
{
lean_object* v_res_2551_; 
v_res_2551_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__24(v_env_2545_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_);
lean_dec(v___y_2549_);
lean_dec_ref(v___y_2548_);
lean_dec(v___y_2547_);
lean_dec_ref(v___y_2546_);
return v_res_2551_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23(lean_object* v_00_u03b1_2552_, lean_object* v_env_2553_, lean_object* v_x_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_){
_start:
{
lean_object* v___x_2560_; 
v___x_2560_ = l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23___redArg(v_env_2553_, v_x_2554_, v___y_2555_, v___y_2556_, v___y_2557_, v___y_2558_);
return v___x_2560_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23___boxed(lean_object* v_00_u03b1_2561_, lean_object* v_env_2562_, lean_object* v_x_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_){
_start:
{
lean_object* v_res_2569_; 
v_res_2569_ = l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23(v_00_u03b1_2561_, v_env_2562_, v_x_2563_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_);
lean_dec(v___y_2567_);
lean_dec_ref(v___y_2566_);
lean_dec(v___y_2565_);
lean_dec_ref(v___y_2564_);
return v_res_2569_;
}
}
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___lam__0(lean_object* v_x_2570_){
_start:
{
uint8_t v___x_2571_; 
v___x_2571_ = 0;
return v___x_2571_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___lam__0___boxed(lean_object* v_x_2572_){
_start:
{
uint8_t v_res_2573_; lean_object* v_r_2574_; 
v_res_2573_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___lam__0(v_x_2572_);
lean_dec(v_x_2572_);
v_r_2574_ = lean_box(v_res_2573_);
return v_r_2574_;
}
}
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___lam__1(lean_object* v_fvarId_2575_, lean_object* v_x_2576_){
_start:
{
uint8_t v___x_2577_; 
v___x_2577_ = l_Lean_instBEqFVarId_beq(v_fvarId_2575_, v_x_2576_);
return v___x_2577_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___lam__1___boxed(lean_object* v_fvarId_2578_, lean_object* v_x_2579_){
_start:
{
uint8_t v_res_2580_; lean_object* v_r_2581_; 
v_res_2580_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___lam__1(v_fvarId_2578_, v_x_2579_);
lean_dec(v_x_2579_);
lean_dec(v_fvarId_2578_);
v_r_2581_ = lean_box(v_res_2580_);
return v_r_2581_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; 
v___x_2583_ = lean_box(0);
v___x_2584_ = lean_unsigned_to_nat(16u);
v___x_2585_ = lean_mk_array(v___x_2584_, v___x_2583_);
return v___x_2585_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; 
v___x_2586_ = lean_obj_once(&l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__1, &l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__1_once, _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__1);
v___x_2587_ = lean_unsigned_to_nat(0u);
v___x_2588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2588_, 0, v___x_2587_);
lean_ctor_set(v___x_2588_, 1, v___x_2586_);
return v___x_2588_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg(lean_object* v_e_2589_, lean_object* v_fvarId_2590_, lean_object* v___y_2591_){
_start:
{
lean_object* v___x_2593_; uint8_t v_fst_2595_; lean_object* v_mctx_2596_; lean_object* v___y_2614_; lean_object* v_mctx_2619_; lean_object* v___f_2620_; lean_object* v___f_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; uint8_t v___x_2624_; 
v___x_2593_ = lean_st_ref_get(v___y_2591_);
v_mctx_2619_ = lean_ctor_get(v___x_2593_, 0);
lean_inc_ref_n(v_mctx_2619_, 2);
lean_dec(v___x_2593_);
v___f_2620_ = ((lean_object*)(l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__0));
v___f_2621_ = lean_alloc_closure((void*)(l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_2621_, 0, v_fvarId_2590_);
v___x_2622_ = lean_obj_once(&l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__2, &l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__2_once, _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__2);
v___x_2623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2623_, 0, v___x_2622_);
lean_ctor_set(v___x_2623_, 1, v_mctx_2619_);
v___x_2624_ = l_Lean_Expr_hasFVar(v_e_2589_);
if (v___x_2624_ == 0)
{
uint8_t v___x_2625_; 
v___x_2625_ = l_Lean_Expr_hasMVar(v_e_2589_);
if (v___x_2625_ == 0)
{
lean_dec_ref(v___x_2623_);
lean_dec_ref(v___f_2621_);
lean_dec_ref(v_e_2589_);
v_fst_2595_ = v___x_2625_;
v_mctx_2596_ = v_mctx_2619_;
goto v___jp_2594_;
}
else
{
lean_object* v___x_2626_; 
lean_dec_ref(v_mctx_2619_);
v___x_2626_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2621_, v___f_2620_, v_e_2589_, v___x_2623_);
v___y_2614_ = v___x_2626_;
goto v___jp_2613_;
}
}
else
{
lean_object* v___x_2627_; 
lean_dec_ref(v_mctx_2619_);
v___x_2627_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2621_, v___f_2620_, v_e_2589_, v___x_2623_);
v___y_2614_ = v___x_2627_;
goto v___jp_2613_;
}
v___jp_2594_:
{
lean_object* v___x_2597_; lean_object* v_cache_2598_; lean_object* v_zetaDeltaFVarIds_2599_; lean_object* v_postponed_2600_; lean_object* v_diag_2601_; lean_object* v___x_2603_; uint8_t v_isShared_2604_; uint8_t v_isSharedCheck_2611_; 
v___x_2597_ = lean_st_ref_take(v___y_2591_);
v_cache_2598_ = lean_ctor_get(v___x_2597_, 1);
v_zetaDeltaFVarIds_2599_ = lean_ctor_get(v___x_2597_, 2);
v_postponed_2600_ = lean_ctor_get(v___x_2597_, 3);
v_diag_2601_ = lean_ctor_get(v___x_2597_, 4);
v_isSharedCheck_2611_ = !lean_is_exclusive(v___x_2597_);
if (v_isSharedCheck_2611_ == 0)
{
lean_object* v_unused_2612_; 
v_unused_2612_ = lean_ctor_get(v___x_2597_, 0);
lean_dec(v_unused_2612_);
v___x_2603_ = v___x_2597_;
v_isShared_2604_ = v_isSharedCheck_2611_;
goto v_resetjp_2602_;
}
else
{
lean_inc(v_diag_2601_);
lean_inc(v_postponed_2600_);
lean_inc(v_zetaDeltaFVarIds_2599_);
lean_inc(v_cache_2598_);
lean_dec(v___x_2597_);
v___x_2603_ = lean_box(0);
v_isShared_2604_ = v_isSharedCheck_2611_;
goto v_resetjp_2602_;
}
v_resetjp_2602_:
{
lean_object* v___x_2606_; 
if (v_isShared_2604_ == 0)
{
lean_ctor_set(v___x_2603_, 0, v_mctx_2596_);
v___x_2606_ = v___x_2603_;
goto v_reusejp_2605_;
}
else
{
lean_object* v_reuseFailAlloc_2610_; 
v_reuseFailAlloc_2610_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2610_, 0, v_mctx_2596_);
lean_ctor_set(v_reuseFailAlloc_2610_, 1, v_cache_2598_);
lean_ctor_set(v_reuseFailAlloc_2610_, 2, v_zetaDeltaFVarIds_2599_);
lean_ctor_set(v_reuseFailAlloc_2610_, 3, v_postponed_2600_);
lean_ctor_set(v_reuseFailAlloc_2610_, 4, v_diag_2601_);
v___x_2606_ = v_reuseFailAlloc_2610_;
goto v_reusejp_2605_;
}
v_reusejp_2605_:
{
lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; 
v___x_2607_ = lean_st_ref_set(v___y_2591_, v___x_2606_);
v___x_2608_ = lean_box(v_fst_2595_);
v___x_2609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2609_, 0, v___x_2608_);
return v___x_2609_;
}
}
}
v___jp_2613_:
{
lean_object* v_snd_2615_; lean_object* v_fst_2616_; lean_object* v_mctx_2617_; uint8_t v___x_2618_; 
v_snd_2615_ = lean_ctor_get(v___y_2614_, 1);
lean_inc(v_snd_2615_);
v_fst_2616_ = lean_ctor_get(v___y_2614_, 0);
lean_inc(v_fst_2616_);
lean_dec_ref(v___y_2614_);
v_mctx_2617_ = lean_ctor_get(v_snd_2615_, 1);
lean_inc_ref(v_mctx_2617_);
lean_dec(v_snd_2615_);
v___x_2618_ = lean_unbox(v_fst_2616_);
lean_dec(v_fst_2616_);
v_fst_2595_ = v___x_2618_;
v_mctx_2596_ = v_mctx_2617_;
goto v___jp_2594_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___boxed(lean_object* v_e_2628_, lean_object* v_fvarId_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_){
_start:
{
lean_object* v_res_2632_; 
v_res_2632_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg(v_e_2628_, v_fvarId_2629_, v___y_2630_);
lean_dec(v___y_2630_);
return v_res_2632_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5(lean_object* v_e_2633_, lean_object* v_fvarId_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_){
_start:
{
lean_object* v___x_2640_; 
v___x_2640_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg(v_e_2633_, v_fvarId_2634_, v___y_2636_);
return v___x_2640_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___boxed(lean_object* v_e_2641_, lean_object* v_fvarId_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_){
_start:
{
lean_object* v_res_2648_; 
v_res_2648_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5(v_e_2641_, v_fvarId_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_);
lean_dec(v___y_2646_);
lean_dec_ref(v___y_2645_);
lean_dec(v___y_2644_);
lean_dec_ref(v___y_2643_);
return v_res_2648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg___lam__0(lean_object* v_k_2649_, lean_object* v_b_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_){
_start:
{
lean_object* v___x_2656_; 
lean_inc(v___y_2654_);
lean_inc_ref(v___y_2653_);
lean_inc(v___y_2652_);
lean_inc_ref(v___y_2651_);
v___x_2656_ = lean_apply_6(v_k_2649_, v_b_2650_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_, lean_box(0));
return v___x_2656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg___lam__0___boxed(lean_object* v_k_2657_, lean_object* v_b_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_){
_start:
{
lean_object* v_res_2664_; 
v_res_2664_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg___lam__0(v_k_2657_, v_b_2658_, v___y_2659_, v___y_2660_, v___y_2661_, v___y_2662_);
lean_dec(v___y_2662_);
lean_dec_ref(v___y_2661_);
lean_dec(v___y_2660_);
lean_dec_ref(v___y_2659_);
return v_res_2664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg(lean_object* v_perm_2665_, lean_object* v_type_2666_, lean_object* v_k_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_){
_start:
{
lean_object* v___f_2673_; lean_object* v___x_2674_; 
v___f_2673_ = lean_alloc_closure((void*)(l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2673_, 0, v_k_2667_);
v___x_2674_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl(lean_box(0), v_perm_2665_, v_type_2666_, v___f_2673_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_);
if (lean_obj_tag(v___x_2674_) == 0)
{
lean_object* v_a_2675_; lean_object* v___x_2677_; uint8_t v_isShared_2678_; uint8_t v_isSharedCheck_2682_; 
v_a_2675_ = lean_ctor_get(v___x_2674_, 0);
v_isSharedCheck_2682_ = !lean_is_exclusive(v___x_2674_);
if (v_isSharedCheck_2682_ == 0)
{
v___x_2677_ = v___x_2674_;
v_isShared_2678_ = v_isSharedCheck_2682_;
goto v_resetjp_2676_;
}
else
{
lean_inc(v_a_2675_);
lean_dec(v___x_2674_);
v___x_2677_ = lean_box(0);
v_isShared_2678_ = v_isSharedCheck_2682_;
goto v_resetjp_2676_;
}
v_resetjp_2676_:
{
lean_object* v___x_2680_; 
if (v_isShared_2678_ == 0)
{
v___x_2680_ = v___x_2677_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v_a_2675_);
v___x_2680_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
return v___x_2680_;
}
}
}
else
{
lean_object* v_a_2683_; lean_object* v___x_2685_; uint8_t v_isShared_2686_; uint8_t v_isSharedCheck_2690_; 
v_a_2683_ = lean_ctor_get(v___x_2674_, 0);
v_isSharedCheck_2690_ = !lean_is_exclusive(v___x_2674_);
if (v_isSharedCheck_2690_ == 0)
{
v___x_2685_ = v___x_2674_;
v_isShared_2686_ = v_isSharedCheck_2690_;
goto v_resetjp_2684_;
}
else
{
lean_inc(v_a_2683_);
lean_dec(v___x_2674_);
v___x_2685_ = lean_box(0);
v_isShared_2686_ = v_isSharedCheck_2690_;
goto v_resetjp_2684_;
}
v_resetjp_2684_:
{
lean_object* v___x_2688_; 
if (v_isShared_2686_ == 0)
{
v___x_2688_ = v___x_2685_;
goto v_reusejp_2687_;
}
else
{
lean_object* v_reuseFailAlloc_2689_; 
v_reuseFailAlloc_2689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2689_, 0, v_a_2683_);
v___x_2688_ = v_reuseFailAlloc_2689_;
goto v_reusejp_2687_;
}
v_reusejp_2687_:
{
return v___x_2688_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg___boxed(lean_object* v_perm_2691_, lean_object* v_type_2692_, lean_object* v_k_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_){
_start:
{
lean_object* v_res_2699_; 
v_res_2699_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg(v_perm_2691_, v_type_2692_, v_k_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_);
lean_dec(v___y_2697_);
lean_dec_ref(v___y_2696_);
lean_dec(v___y_2695_);
lean_dec_ref(v___y_2694_);
return v_res_2699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13(lean_object* v_00_u03b1_2700_, lean_object* v_perm_2701_, lean_object* v_type_2702_, lean_object* v_k_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_){
_start:
{
lean_object* v___x_2709_; 
v___x_2709_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg(v_perm_2701_, v_type_2702_, v_k_2703_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_);
return v___x_2709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___boxed(lean_object* v_00_u03b1_2710_, lean_object* v_perm_2711_, lean_object* v_type_2712_, lean_object* v_k_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_){
_start:
{
lean_object* v_res_2719_; 
v_res_2719_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13(v_00_u03b1_2710_, v_perm_2711_, v_type_2712_, v_k_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_);
lean_dec(v___y_2717_);
lean_dec_ref(v___y_2716_);
lean_dec(v___y_2715_);
lean_dec_ref(v___y_2714_);
return v_res_2719_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1(lean_object* v_a_2720_, lean_object* v_fst_2721_, lean_object* v_fst_2722_, lean_object* v___x_2723_, lean_object* v___x_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_){
_start:
{
lean_object* v___x_2730_; 
lean_inc_ref(v_fst_2721_);
v___x_2730_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion(v_a_2720_, v_fst_2721_, v_fst_2722_, v___x_2723_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_);
if (lean_obj_tag(v___x_2730_) == 0)
{
lean_object* v_a_2731_; lean_object* v___x_2733_; uint8_t v_isShared_2734_; uint8_t v_isSharedCheck_2740_; 
v_a_2731_ = lean_ctor_get(v___x_2730_, 0);
v_isSharedCheck_2740_ = !lean_is_exclusive(v___x_2730_);
if (v_isSharedCheck_2740_ == 0)
{
v___x_2733_ = v___x_2730_;
v_isShared_2734_ = v_isSharedCheck_2740_;
goto v_resetjp_2732_;
}
else
{
lean_inc(v_a_2731_);
lean_dec(v___x_2730_);
v___x_2733_ = lean_box(0);
v_isShared_2734_ = v_isSharedCheck_2740_;
goto v_resetjp_2732_;
}
v_resetjp_2732_:
{
lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2738_; 
v___x_2735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2735_, 0, v_a_2731_);
lean_ctor_set(v___x_2735_, 1, v_fst_2721_);
v___x_2736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2736_, 0, v___x_2724_);
lean_ctor_set(v___x_2736_, 1, v___x_2735_);
if (v_isShared_2734_ == 0)
{
lean_ctor_set(v___x_2733_, 0, v___x_2736_);
v___x_2738_ = v___x_2733_;
goto v_reusejp_2737_;
}
else
{
lean_object* v_reuseFailAlloc_2739_; 
v_reuseFailAlloc_2739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2739_, 0, v___x_2736_);
v___x_2738_ = v_reuseFailAlloc_2739_;
goto v_reusejp_2737_;
}
v_reusejp_2737_:
{
return v___x_2738_;
}
}
}
else
{
lean_object* v_a_2741_; lean_object* v___x_2743_; uint8_t v_isShared_2744_; uint8_t v_isSharedCheck_2748_; 
lean_dec_ref(v___x_2724_);
lean_dec_ref(v_fst_2721_);
v_a_2741_ = lean_ctor_get(v___x_2730_, 0);
v_isSharedCheck_2748_ = !lean_is_exclusive(v___x_2730_);
if (v_isSharedCheck_2748_ == 0)
{
v___x_2743_ = v___x_2730_;
v_isShared_2744_ = v_isSharedCheck_2748_;
goto v_resetjp_2742_;
}
else
{
lean_inc(v_a_2741_);
lean_dec(v___x_2730_);
v___x_2743_ = lean_box(0);
v_isShared_2744_ = v_isSharedCheck_2748_;
goto v_resetjp_2742_;
}
v_resetjp_2742_:
{
lean_object* v___x_2746_; 
if (v_isShared_2744_ == 0)
{
v___x_2746_ = v___x_2743_;
goto v_reusejp_2745_;
}
else
{
lean_object* v_reuseFailAlloc_2747_; 
v_reuseFailAlloc_2747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2747_, 0, v_a_2741_);
v___x_2746_ = v_reuseFailAlloc_2747_;
goto v_reusejp_2745_;
}
v_reusejp_2745_:
{
return v___x_2746_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___boxed(lean_object* v_a_2749_, lean_object* v_fst_2750_, lean_object* v_fst_2751_, lean_object* v___x_2752_, lean_object* v___x_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_){
_start:
{
lean_object* v_res_2759_; 
v_res_2759_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1(v_a_2749_, v_fst_2750_, v_fst_2751_, v___x_2752_, v___x_2753_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_);
lean_dec(v___y_2757_);
lean_dec_ref(v___y_2756_);
lean_dec(v___y_2755_);
lean_dec_ref(v___y_2754_);
return v_res_2759_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__3(size_t v_sz_2760_, size_t v_i_2761_, lean_object* v_bs_2762_){
_start:
{
uint8_t v___x_2763_; 
v___x_2763_ = lean_usize_dec_lt(v_i_2761_, v_sz_2760_);
if (v___x_2763_ == 0)
{
return v_bs_2762_;
}
else
{
lean_object* v_v_2764_; lean_object* v___x_2765_; lean_object* v_bs_x27_2766_; lean_object* v___x_2767_; size_t v___x_2768_; size_t v___x_2769_; lean_object* v___x_2770_; 
v_v_2764_ = lean_array_uget(v_bs_2762_, v_i_2761_);
v___x_2765_ = lean_unsigned_to_nat(0u);
v_bs_x27_2766_ = lean_array_uset(v_bs_2762_, v_i_2761_, v___x_2765_);
v___x_2767_ = l_Lean_Elab_Structural_RecArgInfo_indicesAndRecArgPos(v_v_2764_);
v___x_2768_ = ((size_t)1ULL);
v___x_2769_ = lean_usize_add(v_i_2761_, v___x_2768_);
v___x_2770_ = lean_array_uset(v_bs_x27_2766_, v_i_2761_, v___x_2767_);
v_i_2761_ = v___x_2769_;
v_bs_2762_ = v___x_2770_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__3___boxed(lean_object* v_sz_2772_, lean_object* v_i_2773_, lean_object* v_bs_2774_){
_start:
{
size_t v_sz_boxed_2775_; size_t v_i_boxed_2776_; lean_object* v_res_2777_; 
v_sz_boxed_2775_ = lean_unbox_usize(v_sz_2772_);
lean_dec(v_sz_2772_);
v_i_boxed_2776_ = lean_unbox_usize(v_i_2773_);
lean_dec(v_i_2773_);
v_res_2777_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__3(v_sz_boxed_2775_, v_i_boxed_2776_, v_bs_2774_);
return v_res_2777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___redArg(lean_object* v_lctx_2778_, lean_object* v_localInsts_2779_, lean_object* v_x_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_){
_start:
{
lean_object* v___x_2786_; 
v___x_2786_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_2778_, v_localInsts_2779_, v_x_2780_, v___y_2781_, v___y_2782_, v___y_2783_, v___y_2784_);
if (lean_obj_tag(v___x_2786_) == 0)
{
lean_object* v_a_2787_; lean_object* v___x_2789_; uint8_t v_isShared_2790_; uint8_t v_isSharedCheck_2794_; 
v_a_2787_ = lean_ctor_get(v___x_2786_, 0);
v_isSharedCheck_2794_ = !lean_is_exclusive(v___x_2786_);
if (v_isSharedCheck_2794_ == 0)
{
v___x_2789_ = v___x_2786_;
v_isShared_2790_ = v_isSharedCheck_2794_;
goto v_resetjp_2788_;
}
else
{
lean_inc(v_a_2787_);
lean_dec(v___x_2786_);
v___x_2789_ = lean_box(0);
v_isShared_2790_ = v_isSharedCheck_2794_;
goto v_resetjp_2788_;
}
v_resetjp_2788_:
{
lean_object* v___x_2792_; 
if (v_isShared_2790_ == 0)
{
v___x_2792_ = v___x_2789_;
goto v_reusejp_2791_;
}
else
{
lean_object* v_reuseFailAlloc_2793_; 
v_reuseFailAlloc_2793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2793_, 0, v_a_2787_);
v___x_2792_ = v_reuseFailAlloc_2793_;
goto v_reusejp_2791_;
}
v_reusejp_2791_:
{
return v___x_2792_;
}
}
}
else
{
lean_object* v_a_2795_; lean_object* v___x_2797_; uint8_t v_isShared_2798_; uint8_t v_isSharedCheck_2802_; 
v_a_2795_ = lean_ctor_get(v___x_2786_, 0);
v_isSharedCheck_2802_ = !lean_is_exclusive(v___x_2786_);
if (v_isSharedCheck_2802_ == 0)
{
v___x_2797_ = v___x_2786_;
v_isShared_2798_ = v_isSharedCheck_2802_;
goto v_resetjp_2796_;
}
else
{
lean_inc(v_a_2795_);
lean_dec(v___x_2786_);
v___x_2797_ = lean_box(0);
v_isShared_2798_ = v_isSharedCheck_2802_;
goto v_resetjp_2796_;
}
v_resetjp_2796_:
{
lean_object* v___x_2800_; 
if (v_isShared_2798_ == 0)
{
v___x_2800_ = v___x_2797_;
goto v_reusejp_2799_;
}
else
{
lean_object* v_reuseFailAlloc_2801_; 
v_reuseFailAlloc_2801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2801_, 0, v_a_2795_);
v___x_2800_ = v_reuseFailAlloc_2801_;
goto v_reusejp_2799_;
}
v_reusejp_2799_:
{
return v___x_2800_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___redArg___boxed(lean_object* v_lctx_2803_, lean_object* v_localInsts_2804_, lean_object* v_x_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_){
_start:
{
lean_object* v_res_2811_; 
v_res_2811_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___redArg(v_lctx_2803_, v_localInsts_2804_, v_x_2805_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_);
lean_dec(v___y_2809_);
lean_dec_ref(v___y_2808_);
lean_dec(v___y_2807_);
lean_dec_ref(v___y_2806_);
return v_res_2811_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__12(lean_object* v_as_2812_, size_t v_i_2813_, size_t v_stop_2814_, lean_object* v_b_2815_){
_start:
{
uint8_t v___x_2816_; 
v___x_2816_ = lean_usize_dec_eq(v_i_2813_, v_stop_2814_);
if (v___x_2816_ == 0)
{
lean_object* v___x_2817_; lean_object* v___x_2818_; size_t v___x_2819_; size_t v___x_2820_; 
v___x_2817_ = lean_array_uget_borrowed(v_as_2812_, v_i_2813_);
lean_inc(v___x_2817_);
v___x_2818_ = lean_local_ctx_erase(v_b_2815_, v___x_2817_);
v___x_2819_ = ((size_t)1ULL);
v___x_2820_ = lean_usize_add(v_i_2813_, v___x_2819_);
v_i_2813_ = v___x_2820_;
v_b_2815_ = v___x_2818_;
goto _start;
}
else
{
return v_b_2815_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__12___boxed(lean_object* v_as_2822_, lean_object* v_i_2823_, lean_object* v_stop_2824_, lean_object* v_b_2825_){
_start:
{
size_t v_i_boxed_2826_; size_t v_stop_boxed_2827_; lean_object* v_res_2828_; 
v_i_boxed_2826_ = lean_unbox_usize(v_i_2823_);
lean_dec(v_i_2823_);
v_stop_boxed_2827_ = lean_unbox_usize(v_stop_2824_);
lean_dec(v_stop_2824_);
v_res_2828_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__12(v_as_2822_, v_i_boxed_2826_, v_stop_boxed_2827_, v_b_2825_);
lean_dec_ref(v_as_2822_);
return v_res_2828_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9_spec__11(lean_object* v_a_2829_, lean_object* v_as_2830_, size_t v_i_2831_, size_t v_stop_2832_){
_start:
{
uint8_t v___x_2833_; 
v___x_2833_ = lean_usize_dec_eq(v_i_2831_, v_stop_2832_);
if (v___x_2833_ == 0)
{
lean_object* v___x_2834_; uint8_t v___x_2835_; 
v___x_2834_ = lean_array_uget_borrowed(v_as_2830_, v_i_2831_);
v___x_2835_ = l_Lean_instBEqFVarId_beq(v_a_2829_, v___x_2834_);
if (v___x_2835_ == 0)
{
size_t v___x_2836_; size_t v___x_2837_; 
v___x_2836_ = ((size_t)1ULL);
v___x_2837_ = lean_usize_add(v_i_2831_, v___x_2836_);
v_i_2831_ = v___x_2837_;
goto _start;
}
else
{
return v___x_2835_;
}
}
else
{
uint8_t v___x_2839_; 
v___x_2839_ = 0;
return v___x_2839_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9_spec__11___boxed(lean_object* v_a_2840_, lean_object* v_as_2841_, lean_object* v_i_2842_, lean_object* v_stop_2843_){
_start:
{
size_t v_i_boxed_2844_; size_t v_stop_boxed_2845_; uint8_t v_res_2846_; lean_object* v_r_2847_; 
v_i_boxed_2844_ = lean_unbox_usize(v_i_2842_);
lean_dec(v_i_2842_);
v_stop_boxed_2845_ = lean_unbox_usize(v_stop_2843_);
lean_dec(v_stop_2843_);
v_res_2846_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9_spec__11(v_a_2840_, v_as_2841_, v_i_boxed_2844_, v_stop_boxed_2845_);
lean_dec_ref(v_as_2841_);
lean_dec(v_a_2840_);
v_r_2847_ = lean_box(v_res_2846_);
return v_r_2847_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9(lean_object* v_as_2848_, lean_object* v_a_2849_){
_start:
{
lean_object* v___x_2850_; lean_object* v___x_2851_; uint8_t v___x_2852_; 
v___x_2850_ = lean_unsigned_to_nat(0u);
v___x_2851_ = lean_array_get_size(v_as_2848_);
v___x_2852_ = lean_nat_dec_lt(v___x_2850_, v___x_2851_);
if (v___x_2852_ == 0)
{
return v___x_2852_;
}
else
{
if (v___x_2852_ == 0)
{
return v___x_2852_;
}
else
{
size_t v___x_2853_; size_t v___x_2854_; uint8_t v___x_2855_; 
v___x_2853_ = ((size_t)0ULL);
v___x_2854_ = lean_usize_of_nat(v___x_2851_);
v___x_2855_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9_spec__11(v_a_2849_, v_as_2848_, v___x_2853_, v___x_2854_);
return v___x_2855_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9___boxed(lean_object* v_as_2856_, lean_object* v_a_2857_){
_start:
{
uint8_t v_res_2858_; lean_object* v_r_2859_; 
v_res_2858_ = l_Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9(v_as_2856_, v_a_2857_);
lean_dec(v_a_2857_);
lean_dec_ref(v_as_2856_);
v_r_2859_ = lean_box(v_res_2858_);
return v_r_2859_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__11(lean_object* v_fvarIds_2860_, lean_object* v_as_2861_, size_t v_i_2862_, size_t v_stop_2863_, lean_object* v_b_2864_){
_start:
{
lean_object* v___y_2866_; uint8_t v___x_2870_; 
v___x_2870_ = lean_usize_dec_eq(v_i_2862_, v_stop_2863_);
if (v___x_2870_ == 0)
{
lean_object* v___x_2871_; lean_object* v_fvar_2872_; lean_object* v___x_2873_; uint8_t v___x_2874_; 
v___x_2871_ = lean_array_uget_borrowed(v_as_2861_, v_i_2862_);
v_fvar_2872_ = lean_ctor_get(v___x_2871_, 1);
v___x_2873_ = l_Lean_Expr_fvarId_x21(v_fvar_2872_);
v___x_2874_ = l_Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9(v_fvarIds_2860_, v___x_2873_);
lean_dec(v___x_2873_);
if (v___x_2874_ == 0)
{
lean_object* v___x_2875_; 
lean_inc(v___x_2871_);
v___x_2875_ = lean_array_push(v_b_2864_, v___x_2871_);
v___y_2866_ = v___x_2875_;
goto v___jp_2865_;
}
else
{
v___y_2866_ = v_b_2864_;
goto v___jp_2865_;
}
}
else
{
return v_b_2864_;
}
v___jp_2865_:
{
size_t v___x_2867_; size_t v___x_2868_; 
v___x_2867_ = ((size_t)1ULL);
v___x_2868_ = lean_usize_add(v_i_2862_, v___x_2867_);
v_i_2862_ = v___x_2868_;
v_b_2864_ = v___y_2866_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__11___boxed(lean_object* v_fvarIds_2876_, lean_object* v_as_2877_, lean_object* v_i_2878_, lean_object* v_stop_2879_, lean_object* v_b_2880_){
_start:
{
size_t v_i_boxed_2881_; size_t v_stop_boxed_2882_; lean_object* v_res_2883_; 
v_i_boxed_2881_ = lean_unbox_usize(v_i_2878_);
lean_dec(v_i_2878_);
v_stop_boxed_2882_ = lean_unbox_usize(v_stop_2879_);
lean_dec(v_stop_2879_);
v_res_2883_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__11(v_fvarIds_2876_, v_as_2877_, v_i_boxed_2881_, v_stop_boxed_2882_, v_b_2880_);
lean_dec_ref(v_as_2877_);
lean_dec_ref(v_fvarIds_2876_);
return v_res_2883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___redArg(lean_object* v_fvarIds_2886_, lean_object* v_k_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_){
_start:
{
lean_object* v_lctx_2893_; lean_object* v_localInstances_2894_; lean_object* v___x_2895_; lean_object* v___y_2897_; lean_object* v___x_2912_; uint8_t v___x_2913_; 
v_lctx_2893_ = lean_ctor_get(v___y_2888_, 2);
v_localInstances_2894_ = lean_ctor_get(v___y_2888_, 3);
v___x_2895_ = lean_unsigned_to_nat(0u);
v___x_2912_ = lean_array_get_size(v_fvarIds_2886_);
v___x_2913_ = lean_nat_dec_lt(v___x_2895_, v___x_2912_);
if (v___x_2913_ == 0)
{
lean_inc_ref(v_lctx_2893_);
v___y_2897_ = v_lctx_2893_;
goto v___jp_2896_;
}
else
{
uint8_t v___x_2914_; 
v___x_2914_ = lean_nat_dec_le(v___x_2912_, v___x_2912_);
if (v___x_2914_ == 0)
{
if (v___x_2913_ == 0)
{
lean_inc_ref(v_lctx_2893_);
v___y_2897_ = v_lctx_2893_;
goto v___jp_2896_;
}
else
{
size_t v___x_2915_; size_t v___x_2916_; lean_object* v___x_2917_; 
v___x_2915_ = ((size_t)0ULL);
v___x_2916_ = lean_usize_of_nat(v___x_2912_);
lean_inc_ref(v_lctx_2893_);
v___x_2917_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__12(v_fvarIds_2886_, v___x_2915_, v___x_2916_, v_lctx_2893_);
v___y_2897_ = v___x_2917_;
goto v___jp_2896_;
}
}
else
{
size_t v___x_2918_; size_t v___x_2919_; lean_object* v___x_2920_; 
v___x_2918_ = ((size_t)0ULL);
v___x_2919_ = lean_usize_of_nat(v___x_2912_);
lean_inc_ref(v_lctx_2893_);
v___x_2920_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__12(v_fvarIds_2886_, v___x_2918_, v___x_2919_, v_lctx_2893_);
v___y_2897_ = v___x_2920_;
goto v___jp_2896_;
}
}
v___jp_2896_:
{
lean_object* v___x_2898_; lean_object* v___x_2899_; uint8_t v___x_2900_; 
v___x_2898_ = lean_array_get_size(v_localInstances_2894_);
v___x_2899_ = ((lean_object*)(l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___redArg___closed__0));
v___x_2900_ = lean_nat_dec_lt(v___x_2895_, v___x_2898_);
if (v___x_2900_ == 0)
{
lean_object* v___x_2901_; 
v___x_2901_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___redArg(v___y_2897_, v___x_2899_, v_k_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_);
return v___x_2901_;
}
else
{
uint8_t v___x_2902_; 
v___x_2902_ = lean_nat_dec_le(v___x_2898_, v___x_2898_);
if (v___x_2902_ == 0)
{
if (v___x_2900_ == 0)
{
lean_object* v___x_2903_; 
v___x_2903_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___redArg(v___y_2897_, v___x_2899_, v_k_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_);
return v___x_2903_;
}
else
{
size_t v___x_2904_; size_t v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; 
v___x_2904_ = ((size_t)0ULL);
v___x_2905_ = lean_usize_of_nat(v___x_2898_);
v___x_2906_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__11(v_fvarIds_2886_, v_localInstances_2894_, v___x_2904_, v___x_2905_, v___x_2899_);
v___x_2907_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___redArg(v___y_2897_, v___x_2906_, v_k_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_);
return v___x_2907_;
}
}
else
{
size_t v___x_2908_; size_t v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; 
v___x_2908_ = ((size_t)0ULL);
v___x_2909_ = lean_usize_of_nat(v___x_2898_);
v___x_2910_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__11(v_fvarIds_2886_, v_localInstances_2894_, v___x_2908_, v___x_2909_, v___x_2899_);
v___x_2911_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___redArg(v___y_2897_, v___x_2910_, v_k_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_);
return v___x_2911_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___redArg___boxed(lean_object* v_fvarIds_2921_, lean_object* v_k_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_){
_start:
{
lean_object* v_res_2928_; 
v_res_2928_ = l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___redArg(v_fvarIds_2921_, v_k_2922_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_);
lean_dec(v___y_2926_);
lean_dec_ref(v___y_2925_);
lean_dec(v___y_2924_);
lean_dec_ref(v___y_2923_);
lean_dec_ref(v_fvarIds_2921_);
return v_res_2928_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__14_spec__17_spec__21(lean_object* v_x_2929_, lean_object* v_x_2930_, lean_object* v_x_2931_){
_start:
{
if (lean_obj_tag(v_x_2931_) == 0)
{
lean_dec(v_x_2929_);
return v_x_2930_;
}
else
{
lean_object* v_head_2932_; lean_object* v_tail_2933_; lean_object* v___x_2935_; uint8_t v_isShared_2936_; uint8_t v_isSharedCheck_2943_; 
v_head_2932_ = lean_ctor_get(v_x_2931_, 0);
v_tail_2933_ = lean_ctor_get(v_x_2931_, 1);
v_isSharedCheck_2943_ = !lean_is_exclusive(v_x_2931_);
if (v_isSharedCheck_2943_ == 0)
{
v___x_2935_ = v_x_2931_;
v_isShared_2936_ = v_isSharedCheck_2943_;
goto v_resetjp_2934_;
}
else
{
lean_inc(v_tail_2933_);
lean_inc(v_head_2932_);
lean_dec(v_x_2931_);
v___x_2935_ = lean_box(0);
v_isShared_2936_ = v_isSharedCheck_2943_;
goto v_resetjp_2934_;
}
v_resetjp_2934_:
{
lean_object* v___x_2938_; 
lean_inc(v_x_2929_);
if (v_isShared_2936_ == 0)
{
lean_ctor_set_tag(v___x_2935_, 5);
lean_ctor_set(v___x_2935_, 1, v_x_2929_);
lean_ctor_set(v___x_2935_, 0, v_x_2930_);
v___x_2938_ = v___x_2935_;
goto v_reusejp_2937_;
}
else
{
lean_object* v_reuseFailAlloc_2942_; 
v_reuseFailAlloc_2942_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2942_, 0, v_x_2930_);
lean_ctor_set(v_reuseFailAlloc_2942_, 1, v_x_2929_);
v___x_2938_ = v_reuseFailAlloc_2942_;
goto v_reusejp_2937_;
}
v_reusejp_2937_:
{
lean_object* v___x_2939_; lean_object* v___x_2940_; 
v___x_2939_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(v_head_2932_);
v___x_2940_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2940_, 0, v___x_2938_);
lean_ctor_set(v___x_2940_, 1, v___x_2939_);
v_x_2930_ = v___x_2940_;
v_x_2931_ = v_tail_2933_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__14_spec__17(lean_object* v_x_2944_, lean_object* v_x_2945_, lean_object* v_x_2946_){
_start:
{
if (lean_obj_tag(v_x_2946_) == 0)
{
lean_dec(v_x_2944_);
return v_x_2945_;
}
else
{
lean_object* v_head_2947_; lean_object* v_tail_2948_; lean_object* v___x_2950_; uint8_t v_isShared_2951_; uint8_t v_isSharedCheck_2958_; 
v_head_2947_ = lean_ctor_get(v_x_2946_, 0);
v_tail_2948_ = lean_ctor_get(v_x_2946_, 1);
v_isSharedCheck_2958_ = !lean_is_exclusive(v_x_2946_);
if (v_isSharedCheck_2958_ == 0)
{
v___x_2950_ = v_x_2946_;
v_isShared_2951_ = v_isSharedCheck_2958_;
goto v_resetjp_2949_;
}
else
{
lean_inc(v_tail_2948_);
lean_inc(v_head_2947_);
lean_dec(v_x_2946_);
v___x_2950_ = lean_box(0);
v_isShared_2951_ = v_isSharedCheck_2958_;
goto v_resetjp_2949_;
}
v_resetjp_2949_:
{
lean_object* v___x_2953_; 
lean_inc(v_x_2944_);
if (v_isShared_2951_ == 0)
{
lean_ctor_set_tag(v___x_2950_, 5);
lean_ctor_set(v___x_2950_, 1, v_x_2944_);
lean_ctor_set(v___x_2950_, 0, v_x_2945_);
v___x_2953_ = v___x_2950_;
goto v_reusejp_2952_;
}
else
{
lean_object* v_reuseFailAlloc_2957_; 
v_reuseFailAlloc_2957_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2957_, 0, v_x_2945_);
lean_ctor_set(v_reuseFailAlloc_2957_, 1, v_x_2944_);
v___x_2953_ = v_reuseFailAlloc_2957_;
goto v_reusejp_2952_;
}
v_reusejp_2952_:
{
lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; 
v___x_2954_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(v_head_2947_);
v___x_2955_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2955_, 0, v___x_2953_);
lean_ctor_set(v___x_2955_, 1, v___x_2954_);
v___x_2956_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__14_spec__17_spec__21(v_x_2944_, v___x_2955_, v_tail_2948_);
return v___x_2956_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__14(lean_object* v_x_2959_, lean_object* v_x_2960_){
_start:
{
if (lean_obj_tag(v_x_2959_) == 0)
{
lean_object* v___x_2961_; 
lean_dec(v_x_2960_);
v___x_2961_ = lean_box(0);
return v___x_2961_;
}
else
{
lean_object* v_tail_2962_; 
v_tail_2962_ = lean_ctor_get(v_x_2959_, 1);
if (lean_obj_tag(v_tail_2962_) == 0)
{
lean_object* v_head_2963_; lean_object* v___x_2964_; 
lean_dec(v_x_2960_);
v_head_2963_ = lean_ctor_get(v_x_2959_, 0);
lean_inc(v_head_2963_);
lean_dec_ref(v_x_2959_);
v___x_2964_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(v_head_2963_);
return v___x_2964_;
}
else
{
lean_object* v_head_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; 
lean_inc(v_tail_2962_);
v_head_2965_ = lean_ctor_get(v_x_2959_, 0);
lean_inc(v_head_2965_);
lean_dec_ref(v_x_2959_);
v___x_2966_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(v_head_2965_);
v___x_2967_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__14_spec__17(v_x_2960_, v___x_2966_, v_tail_2962_);
return v___x_2967_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__5(void){
_start:
{
lean_object* v___x_2976_; lean_object* v___x_2977_; 
v___x_2976_ = ((lean_object*)(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__0));
v___x_2977_ = lean_string_length(v___x_2976_);
return v___x_2977_;
}
}
static lean_object* _init_l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__6(void){
_start:
{
lean_object* v___x_2978_; lean_object* v___x_2979_; 
v___x_2978_ = lean_obj_once(&l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__5, &l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__5_once, _init_l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__5);
v___x_2979_ = lean_nat_to_int(v___x_2978_);
return v___x_2979_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10(lean_object* v_xs_2987_){
_start:
{
lean_object* v___x_2988_; lean_object* v___x_2989_; uint8_t v___x_2990_; 
v___x_2988_ = lean_array_get_size(v_xs_2987_);
v___x_2989_ = lean_unsigned_to_nat(0u);
v___x_2990_ = lean_nat_dec_eq(v___x_2988_, v___x_2989_);
if (v___x_2990_ == 0)
{
lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; 
v___x_2991_ = lean_array_to_list(v_xs_2987_);
v___x_2992_ = ((lean_object*)(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__3));
v___x_2993_ = l_Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__14(v___x_2991_, v___x_2992_);
v___x_2994_ = lean_obj_once(&l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__6, &l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__6_once, _init_l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__6);
v___x_2995_ = ((lean_object*)(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__7));
v___x_2996_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2996_, 0, v___x_2995_);
lean_ctor_set(v___x_2996_, 1, v___x_2993_);
v___x_2997_ = ((lean_object*)(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__8));
v___x_2998_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2998_, 0, v___x_2996_);
lean_ctor_set(v___x_2998_, 1, v___x_2997_);
v___x_2999_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2999_, 0, v___x_2994_);
lean_ctor_set(v___x_2999_, 1, v___x_2998_);
v___x_3000_ = l_Std_Format_fill(v___x_2999_);
return v___x_3000_;
}
else
{
lean_object* v___x_3001_; 
lean_dec_ref(v_xs_2987_);
v___x_3001_ = ((lean_object*)(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__10));
return v___x_3001_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__11(size_t v_sz_3002_, size_t v_i_3003_, lean_object* v_bs_3004_){
_start:
{
uint8_t v___x_3005_; 
v___x_3005_ = lean_usize_dec_lt(v_i_3003_, v_sz_3002_);
if (v___x_3005_ == 0)
{
return v_bs_3004_;
}
else
{
lean_object* v_v_3006_; lean_object* v___x_3007_; lean_object* v_bs_x27_3008_; lean_object* v___x_3009_; size_t v___x_3010_; size_t v___x_3011_; lean_object* v___x_3012_; 
v_v_3006_ = lean_array_uget(v_bs_3004_, v_i_3003_);
v___x_3007_ = lean_unsigned_to_nat(0u);
v_bs_x27_3008_ = lean_array_uset(v_bs_3004_, v_i_3003_, v___x_3007_);
v___x_3009_ = l_Lean_mkFVar(v_v_3006_);
v___x_3010_ = ((size_t)1ULL);
v___x_3011_ = lean_usize_add(v_i_3003_, v___x_3010_);
v___x_3012_ = lean_array_uset(v_bs_x27_3008_, v_i_3003_, v___x_3009_);
v_i_3003_ = v___x_3011_;
v_bs_3004_ = v___x_3012_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__11___boxed(lean_object* v_sz_3014_, lean_object* v_i_3015_, lean_object* v_bs_3016_){
_start:
{
size_t v_sz_boxed_3017_; size_t v_i_boxed_3018_; lean_object* v_res_3019_; 
v_sz_boxed_3017_ = lean_unbox_usize(v_sz_3014_);
lean_dec(v_sz_3014_);
v_i_boxed_3018_ = lean_unbox_usize(v_i_3015_);
lean_dec(v_i_3015_);
v_res_3019_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__11(v_sz_boxed_3017_, v_i_boxed_3018_, v_bs_3016_);
return v_res_3019_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg(lean_object* v_fst_3020_, lean_object* v_as_3021_, lean_object* v_i_3022_, lean_object* v_j_3023_, lean_object* v_bs_3024_){
_start:
{
lean_object* v_zero_3025_; uint8_t v_isZero_3026_; 
v_zero_3025_ = lean_unsigned_to_nat(0u);
v_isZero_3026_ = lean_nat_dec_eq(v_i_3022_, v_zero_3025_);
if (v_isZero_3026_ == 1)
{
lean_dec(v_j_3023_);
lean_dec(v_i_3022_);
return v_bs_3024_;
}
else
{
lean_object* v___x_3027_; lean_object* v_fnName_3028_; lean_object* v_recArgPos_3029_; lean_object* v_indicesPos_3030_; lean_object* v_indGroupInst_3031_; lean_object* v_indIdx_3032_; lean_object* v___x_3034_; uint8_t v_isShared_3035_; uint8_t v_isSharedCheck_3047_; 
v___x_3027_ = lean_array_fget(v_as_3021_, v_j_3023_);
v_fnName_3028_ = lean_ctor_get(v___x_3027_, 0);
v_recArgPos_3029_ = lean_ctor_get(v___x_3027_, 2);
v_indicesPos_3030_ = lean_ctor_get(v___x_3027_, 3);
v_indGroupInst_3031_ = lean_ctor_get(v___x_3027_, 4);
v_indIdx_3032_ = lean_ctor_get(v___x_3027_, 5);
v_isSharedCheck_3047_ = !lean_is_exclusive(v___x_3027_);
if (v_isSharedCheck_3047_ == 0)
{
lean_object* v_unused_3048_; 
v_unused_3048_ = lean_ctor_get(v___x_3027_, 1);
lean_dec(v_unused_3048_);
v___x_3034_ = v___x_3027_;
v_isShared_3035_ = v_isSharedCheck_3047_;
goto v_resetjp_3033_;
}
else
{
lean_inc(v_indIdx_3032_);
lean_inc(v_indGroupInst_3031_);
lean_inc(v_indicesPos_3030_);
lean_inc(v_recArgPos_3029_);
lean_inc(v_fnName_3028_);
lean_dec(v___x_3027_);
v___x_3034_ = lean_box(0);
v_isShared_3035_ = v_isSharedCheck_3047_;
goto v_resetjp_3033_;
}
v_resetjp_3033_:
{
lean_object* v_perms_3036_; lean_object* v___x_3037_; lean_object* v_one_3038_; lean_object* v_n_3039_; lean_object* v___x_3040_; lean_object* v___x_3042_; 
v_perms_3036_ = lean_ctor_get(v_fst_3020_, 1);
v___x_3037_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0, &l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0_once, _init_l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0);
v_one_3038_ = lean_unsigned_to_nat(1u);
v_n_3039_ = lean_nat_sub(v_i_3022_, v_one_3038_);
lean_dec(v_i_3022_);
v___x_3040_ = lean_array_get_borrowed(v___x_3037_, v_perms_3036_, v_j_3023_);
lean_inc(v___x_3040_);
if (v_isShared_3035_ == 0)
{
lean_ctor_set(v___x_3034_, 1, v___x_3040_);
v___x_3042_ = v___x_3034_;
goto v_reusejp_3041_;
}
else
{
lean_object* v_reuseFailAlloc_3046_; 
v_reuseFailAlloc_3046_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3046_, 0, v_fnName_3028_);
lean_ctor_set(v_reuseFailAlloc_3046_, 1, v___x_3040_);
lean_ctor_set(v_reuseFailAlloc_3046_, 2, v_recArgPos_3029_);
lean_ctor_set(v_reuseFailAlloc_3046_, 3, v_indicesPos_3030_);
lean_ctor_set(v_reuseFailAlloc_3046_, 4, v_indGroupInst_3031_);
lean_ctor_set(v_reuseFailAlloc_3046_, 5, v_indIdx_3032_);
v___x_3042_ = v_reuseFailAlloc_3046_;
goto v_reusejp_3041_;
}
v_reusejp_3041_:
{
lean_object* v___x_3043_; lean_object* v___x_3044_; 
v___x_3043_ = lean_nat_add(v_j_3023_, v_one_3038_);
lean_dec(v_j_3023_);
v___x_3044_ = lean_array_push(v_bs_3024_, v___x_3042_);
v_i_3022_ = v_n_3039_;
v_j_3023_ = v___x_3043_;
v_bs_3024_ = v___x_3044_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg___boxed(lean_object* v_fst_3049_, lean_object* v_as_3050_, lean_object* v_i_3051_, lean_object* v_j_3052_, lean_object* v_bs_3053_){
_start:
{
lean_object* v_res_3054_; 
v_res_3054_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg(v_fst_3049_, v_as_3050_, v_i_3051_, v_j_3052_, v_bs_3053_);
lean_dec_ref(v_as_3050_);
lean_dec_ref(v_fst_3049_);
return v_res_3054_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__2(size_t v_sz_3055_, size_t v_i_3056_, lean_object* v_bs_3057_){
_start:
{
uint8_t v___x_3058_; 
v___x_3058_ = lean_usize_dec_lt(v_i_3056_, v_sz_3055_);
if (v___x_3058_ == 0)
{
return v_bs_3057_;
}
else
{
lean_object* v_v_3059_; lean_object* v_recArgPos_3060_; lean_object* v___x_3061_; lean_object* v_bs_x27_3062_; size_t v___x_3063_; size_t v___x_3064_; lean_object* v___x_3065_; 
v_v_3059_ = lean_array_uget_borrowed(v_bs_3057_, v_i_3056_);
v_recArgPos_3060_ = lean_ctor_get(v_v_3059_, 2);
lean_inc(v_recArgPos_3060_);
v___x_3061_ = lean_unsigned_to_nat(0u);
v_bs_x27_3062_ = lean_array_uset(v_bs_3057_, v_i_3056_, v___x_3061_);
v___x_3063_ = ((size_t)1ULL);
v___x_3064_ = lean_usize_add(v_i_3056_, v___x_3063_);
v___x_3065_ = lean_array_uset(v_bs_x27_3062_, v_i_3056_, v_recArgPos_3060_);
v_i_3056_ = v___x_3064_;
v_bs_3057_ = v___x_3065_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__2___boxed(lean_object* v_sz_3067_, lean_object* v_i_3068_, lean_object* v_bs_3069_){
_start:
{
size_t v_sz_boxed_3070_; size_t v_i_boxed_3071_; lean_object* v_res_3072_; 
v_sz_boxed_3070_ = lean_unbox_usize(v_sz_3067_);
lean_dec(v_sz_3067_);
v_i_boxed_3071_ = lean_unbox_usize(v_i_3068_);
lean_dec(v_i_3068_);
v_res_3072_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__2(v_sz_boxed_3070_, v_i_boxed_3071_, v_bs_3069_);
return v_res_3072_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__1(void){
_start:
{
lean_object* v___x_3074_; lean_object* v___x_3075_; 
v___x_3074_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__0));
v___x_3075_ = l_Lean_stringToMessageData(v___x_3074_);
return v___x_3075_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__3(void){
_start:
{
lean_object* v___x_3077_; lean_object* v___x_3078_; 
v___x_3077_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__2));
v___x_3078_ = l_Lean_stringToMessageData(v___x_3077_);
return v___x_3078_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__5(void){
_start:
{
lean_object* v___x_3080_; lean_object* v___x_3081_; 
v___x_3080_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__4));
v___x_3081_ = l_Lean_stringToMessageData(v___x_3080_);
return v___x_3081_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6(lean_object* v_a_3082_, lean_object* v_as_3083_, size_t v_sz_3084_, size_t v_i_3085_, lean_object* v_b_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_){
_start:
{
lean_object* v_a_3093_; uint8_t v___x_3097_; 
v___x_3097_ = lean_usize_dec_lt(v_i_3085_, v_sz_3084_);
if (v___x_3097_ == 0)
{
lean_object* v___x_3098_; 
lean_dec_ref(v_a_3082_);
v___x_3098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3098_, 0, v_b_3086_);
return v___x_3098_;
}
else
{
lean_object* v_a_3099_; lean_object* v___x_3100_; 
v_a_3099_ = lean_array_uget_borrowed(v_as_3083_, v_i_3085_);
lean_inc(v_a_3099_);
lean_inc_ref(v_a_3082_);
v___x_3100_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg(v_a_3082_, v_a_3099_, v___y_3088_);
if (lean_obj_tag(v___x_3100_) == 0)
{
lean_object* v_a_3101_; lean_object* v___x_3102_; uint8_t v___x_3103_; 
v_a_3101_ = lean_ctor_get(v___x_3100_, 0);
lean_inc(v_a_3101_);
lean_dec_ref(v___x_3100_);
v___x_3102_ = lean_box(0);
v___x_3103_ = lean_unbox(v_a_3101_);
lean_dec(v_a_3101_);
if (v___x_3103_ == 0)
{
v_a_3093_ = v___x_3102_;
goto v___jp_3092_;
}
else
{
uint8_t v___x_3104_; 
v___x_3104_ = l_Lean_Expr_isFVarOf(v_a_3082_, v_a_3099_);
if (v___x_3104_ == 0)
{
lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; 
v___x_3105_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__1);
lean_inc_ref(v_a_3082_);
v___x_3106_ = l_Lean_indentExpr(v_a_3082_);
v___x_3107_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3107_, 0, v___x_3105_);
lean_ctor_set(v___x_3107_, 1, v___x_3106_);
v___x_3108_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__3);
v___x_3109_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3109_, 0, v___x_3107_);
lean_ctor_set(v___x_3109_, 1, v___x_3108_);
lean_inc(v_a_3099_);
v___x_3110_ = l_Lean_mkFVar(v_a_3099_);
v___x_3111_ = l_Lean_indentExpr(v___x_3110_);
v___x_3112_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3112_, 0, v___x_3109_);
lean_ctor_set(v___x_3112_, 1, v___x_3111_);
v___x_3113_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__5);
v___x_3114_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3114_, 0, v___x_3112_);
lean_ctor_set(v___x_3114_, 1, v___x_3113_);
v___x_3115_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg(v___x_3114_, v___y_3087_, v___y_3088_, v___y_3089_, v___y_3090_);
if (lean_obj_tag(v___x_3115_) == 0)
{
lean_dec_ref(v___x_3115_);
v_a_3093_ = v___x_3102_;
goto v___jp_3092_;
}
else
{
lean_dec_ref(v_a_3082_);
return v___x_3115_;
}
}
else
{
lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; 
v___x_3116_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__1);
lean_inc_ref(v_a_3082_);
v___x_3117_ = l_Lean_indentExpr(v_a_3082_);
v___x_3118_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3118_, 0, v___x_3116_);
lean_ctor_set(v___x_3118_, 1, v___x_3117_);
v___x_3119_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__5);
v___x_3120_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3120_, 0, v___x_3118_);
lean_ctor_set(v___x_3120_, 1, v___x_3119_);
v___x_3121_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg(v___x_3120_, v___y_3087_, v___y_3088_, v___y_3089_, v___y_3090_);
if (lean_obj_tag(v___x_3121_) == 0)
{
lean_dec_ref(v___x_3121_);
v_a_3093_ = v___x_3102_;
goto v___jp_3092_;
}
else
{
lean_dec_ref(v_a_3082_);
return v___x_3121_;
}
}
}
}
else
{
lean_object* v_a_3122_; lean_object* v___x_3124_; uint8_t v_isShared_3125_; uint8_t v_isSharedCheck_3129_; 
lean_dec_ref(v_a_3082_);
v_a_3122_ = lean_ctor_get(v___x_3100_, 0);
v_isSharedCheck_3129_ = !lean_is_exclusive(v___x_3100_);
if (v_isSharedCheck_3129_ == 0)
{
v___x_3124_ = v___x_3100_;
v_isShared_3125_ = v_isSharedCheck_3129_;
goto v_resetjp_3123_;
}
else
{
lean_inc(v_a_3122_);
lean_dec(v___x_3100_);
v___x_3124_ = lean_box(0);
v_isShared_3125_ = v_isSharedCheck_3129_;
goto v_resetjp_3123_;
}
v_resetjp_3123_:
{
lean_object* v___x_3127_; 
if (v_isShared_3125_ == 0)
{
v___x_3127_ = v___x_3124_;
goto v_reusejp_3126_;
}
else
{
lean_object* v_reuseFailAlloc_3128_; 
v_reuseFailAlloc_3128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3128_, 0, v_a_3122_);
v___x_3127_ = v_reuseFailAlloc_3128_;
goto v_reusejp_3126_;
}
v_reusejp_3126_:
{
return v___x_3127_;
}
}
}
}
v___jp_3092_:
{
size_t v___x_3094_; size_t v___x_3095_; 
v___x_3094_ = ((size_t)1ULL);
v___x_3095_ = lean_usize_add(v_i_3085_, v___x_3094_);
v_i_3085_ = v___x_3095_;
v_b_3086_ = v_a_3093_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___boxed(lean_object* v_a_3130_, lean_object* v_as_3131_, lean_object* v_sz_3132_, lean_object* v_i_3133_, lean_object* v_b_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_){
_start:
{
size_t v_sz_boxed_3140_; size_t v_i_boxed_3141_; lean_object* v_res_3142_; 
v_sz_boxed_3140_ = lean_unbox_usize(v_sz_3132_);
lean_dec(v_sz_3132_);
v_i_boxed_3141_ = lean_unbox_usize(v_i_3133_);
lean_dec(v_i_3133_);
v_res_3142_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6(v_a_3130_, v_as_3131_, v_sz_boxed_3140_, v_i_boxed_3141_, v_b_3134_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_);
lean_dec(v___y_3138_);
lean_dec_ref(v___y_3137_);
lean_dec(v___y_3136_);
lean_dec_ref(v___y_3135_);
lean_dec_ref(v_as_3131_);
return v_res_3142_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7(lean_object* v_snd_3143_, lean_object* v_as_3144_, size_t v_sz_3145_, size_t v_i_3146_, lean_object* v_b_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_){
_start:
{
uint8_t v___x_3153_; 
v___x_3153_ = lean_usize_dec_lt(v_i_3146_, v_sz_3145_);
if (v___x_3153_ == 0)
{
lean_object* v___x_3154_; 
v___x_3154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3154_, 0, v_b_3147_);
return v___x_3154_;
}
else
{
lean_object* v___x_3155_; lean_object* v_a_3156_; size_t v_sz_3157_; size_t v___x_3158_; lean_object* v___x_3159_; 
v___x_3155_ = lean_box(0);
v_a_3156_ = lean_array_uget_borrowed(v_as_3144_, v_i_3146_);
v_sz_3157_ = lean_array_size(v_snd_3143_);
v___x_3158_ = ((size_t)0ULL);
lean_inc(v_a_3156_);
v___x_3159_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6(v_a_3156_, v_snd_3143_, v_sz_3157_, v___x_3158_, v___x_3155_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_);
if (lean_obj_tag(v___x_3159_) == 0)
{
size_t v___x_3160_; size_t v___x_3161_; 
lean_dec_ref(v___x_3159_);
v___x_3160_ = ((size_t)1ULL);
v___x_3161_ = lean_usize_add(v_i_3146_, v___x_3160_);
v_i_3146_ = v___x_3161_;
v_b_3147_ = v___x_3155_;
goto _start;
}
else
{
return v___x_3159_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7___boxed(lean_object* v_snd_3163_, lean_object* v_as_3164_, lean_object* v_sz_3165_, lean_object* v_i_3166_, lean_object* v_b_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_){
_start:
{
size_t v_sz_boxed_3173_; size_t v_i_boxed_3174_; lean_object* v_res_3175_; 
v_sz_boxed_3173_ = lean_unbox_usize(v_sz_3165_);
lean_dec(v_sz_3165_);
v_i_boxed_3174_ = lean_unbox_usize(v_i_3166_);
lean_dec(v_i_3166_);
v_res_3175_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7(v_snd_3163_, v_as_3164_, v_sz_boxed_3173_, v_i_boxed_3174_, v_b_3167_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_);
lean_dec(v___y_3171_);
lean_dec_ref(v___y_3170_);
lean_dec(v___y_3169_);
lean_dec_ref(v___y_3168_);
lean_dec_ref(v_as_3164_);
lean_dec_ref(v_snd_3163_);
return v_res_3175_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8(lean_object* v_snd_3176_, lean_object* v_as_3177_, size_t v_sz_3178_, size_t v_i_3179_, lean_object* v_b_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_){
_start:
{
uint8_t v___x_3186_; 
v___x_3186_ = lean_usize_dec_lt(v_i_3179_, v_sz_3178_);
if (v___x_3186_ == 0)
{
lean_object* v___x_3187_; 
v___x_3187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3187_, 0, v_b_3180_);
return v___x_3187_;
}
else
{
lean_object* v_a_3188_; lean_object* v_indGroupInst_3189_; lean_object* v_params_3190_; lean_object* v___x_3191_; size_t v_sz_3192_; size_t v___x_3193_; lean_object* v___x_3194_; 
v_a_3188_ = lean_array_uget_borrowed(v_as_3177_, v_i_3179_);
v_indGroupInst_3189_ = lean_ctor_get(v_a_3188_, 4);
v_params_3190_ = lean_ctor_get(v_indGroupInst_3189_, 2);
v___x_3191_ = lean_box(0);
v_sz_3192_ = lean_array_size(v_params_3190_);
v___x_3193_ = ((size_t)0ULL);
v___x_3194_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7(v_snd_3176_, v_params_3190_, v_sz_3192_, v___x_3193_, v___x_3191_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_);
if (lean_obj_tag(v___x_3194_) == 0)
{
size_t v___x_3195_; size_t v___x_3196_; 
lean_dec_ref(v___x_3194_);
v___x_3195_ = ((size_t)1ULL);
v___x_3196_ = lean_usize_add(v_i_3179_, v___x_3195_);
v_i_3179_ = v___x_3196_;
v_b_3180_ = v___x_3191_;
goto _start;
}
else
{
return v___x_3194_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8___boxed(lean_object* v_snd_3198_, lean_object* v_as_3199_, lean_object* v_sz_3200_, lean_object* v_i_3201_, lean_object* v_b_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_){
_start:
{
size_t v_sz_boxed_3208_; size_t v_i_boxed_3209_; lean_object* v_res_3210_; 
v_sz_boxed_3208_ = lean_unbox_usize(v_sz_3200_);
lean_dec(v_sz_3200_);
v_i_boxed_3209_ = lean_unbox_usize(v_i_3201_);
lean_dec(v_i_3201_);
v_res_3210_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8(v_snd_3198_, v_as_3199_, v_sz_boxed_3208_, v_i_boxed_3209_, v_b_3202_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_);
lean_dec(v___y_3206_);
lean_dec_ref(v___y_3205_);
lean_dec(v___y_3204_);
lean_dec_ref(v___y_3203_);
lean_dec_ref(v_as_3199_);
lean_dec_ref(v_snd_3198_);
return v_res_3210_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__0(void){
_start:
{
lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; 
v___x_3211_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__3));
v___x_3212_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0___closed__1));
v___x_3213_ = l_Lean_Name_append(v___x_3212_, v___x_3211_);
return v___x_3213_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3215_; lean_object* v___x_3216_; 
v___x_3215_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__1));
v___x_3216_ = l_Lean_stringToMessageData(v___x_3215_);
return v___x_3216_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__4(void){
_start:
{
lean_object* v___x_3218_; lean_object* v___x_3219_; 
v___x_3218_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__3));
v___x_3219_ = l_Lean_stringToMessageData(v___x_3218_);
return v___x_3219_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__6(void){
_start:
{
lean_object* v___x_3221_; lean_object* v___x_3222_; 
v___x_3221_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__5));
v___x_3222_ = l_Lean_stringToMessageData(v___x_3221_);
return v___x_3222_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__8(void){
_start:
{
lean_object* v___x_3224_; lean_object* v___x_3225_; 
v___x_3224_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__7));
v___x_3225_ = l_Lean_stringToMessageData(v___x_3224_);
return v___x_3225_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__10(void){
_start:
{
lean_object* v___x_3227_; lean_object* v___x_3228_; 
v___x_3227_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__9));
v___x_3228_ = l_Lean_stringToMessageData(v___x_3227_);
return v___x_3228_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0(size_t v___x_3229_, lean_object* v_a_3230_, lean_object* v_xs_3231_, lean_object* v___x_3232_, lean_object* v_a_3233_, lean_object* v_recArgInfos_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_){
_start:
{
lean_object* v___y_3241_; lean_object* v___y_3242_; lean_object* v___y_3243_; lean_object* v___y_3244_; lean_object* v___y_3245_; lean_object* v___y_3246_; lean_object* v___y_3247_; lean_object* v___x_3260_; lean_object* v___y_3262_; lean_object* v___y_3263_; lean_object* v___y_3264_; lean_object* v___y_3265_; lean_object* v___y_3266_; lean_object* v___y_3267_; lean_object* v___y_3268_; lean_object* v___x_3287_; lean_object* v_a_3288_; size_t v_sz_3289_; lean_object* v___x_3290_; lean_object* v___y_3292_; lean_object* v___y_3293_; lean_object* v___y_3294_; lean_object* v___y_3295_; uint8_t v___x_3354_; 
v___x_3260_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__3));
v___x_3287_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0(v___x_3260_, v___y_3235_, v___y_3236_, v___y_3237_, v___y_3238_);
v_a_3288_ = lean_ctor_get(v___x_3287_, 0);
lean_inc(v_a_3288_);
lean_dec_ref(v___x_3287_);
v_sz_3289_ = lean_array_size(v_recArgInfos_3234_);
lean_inc_ref(v_recArgInfos_3234_);
v___x_3290_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__2(v_sz_3289_, v___x_3229_, v_recArgInfos_3234_);
v___x_3354_ = lean_unbox(v_a_3288_);
lean_dec(v_a_3288_);
if (v___x_3354_ == 0)
{
v___y_3292_ = v___y_3235_;
v___y_3293_ = v___y_3236_;
v___y_3294_ = v___y_3237_;
v___y_3295_ = v___y_3238_;
goto v___jp_3291_;
}
else
{
lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; 
v___x_3355_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__10, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__10);
lean_inc_ref(v___x_3290_);
v___x_3356_ = lean_array_to_list(v___x_3290_);
v___x_3357_ = lean_box(0);
v___x_3358_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__0(v___x_3356_, v___x_3357_);
v___x_3359_ = l_Lean_MessageData_ofList(v___x_3358_);
v___x_3360_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3360_, 0, v___x_3355_);
lean_ctor_set(v___x_3360_, 1, v___x_3359_);
v___x_3361_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_3260_, v___x_3360_, v___y_3235_, v___y_3236_, v___y_3237_, v___y_3238_);
if (lean_obj_tag(v___x_3361_) == 0)
{
lean_dec_ref(v___x_3361_);
v___y_3292_ = v___y_3235_;
v___y_3293_ = v___y_3236_;
v___y_3294_ = v___y_3237_;
v___y_3295_ = v___y_3238_;
goto v___jp_3291_;
}
else
{
lean_object* v_a_3362_; lean_object* v___x_3364_; uint8_t v_isShared_3365_; uint8_t v_isSharedCheck_3369_; 
lean_dec_ref(v___x_3290_);
lean_dec_ref(v_recArgInfos_3234_);
lean_dec_ref(v_a_3233_);
lean_dec(v___x_3232_);
lean_dec_ref(v_xs_3231_);
lean_dec_ref(v_a_3230_);
v_a_3362_ = lean_ctor_get(v___x_3361_, 0);
v_isSharedCheck_3369_ = !lean_is_exclusive(v___x_3361_);
if (v_isSharedCheck_3369_ == 0)
{
v___x_3364_ = v___x_3361_;
v_isShared_3365_ = v_isSharedCheck_3369_;
goto v_resetjp_3363_;
}
else
{
lean_inc(v_a_3362_);
lean_dec(v___x_3361_);
v___x_3364_ = lean_box(0);
v_isShared_3365_ = v_isSharedCheck_3369_;
goto v_resetjp_3363_;
}
v_resetjp_3363_:
{
lean_object* v___x_3367_; 
if (v_isShared_3365_ == 0)
{
v___x_3367_ = v___x_3364_;
goto v_reusejp_3366_;
}
else
{
lean_object* v_reuseFailAlloc_3368_; 
v_reuseFailAlloc_3368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3368_, 0, v_a_3362_);
v___x_3367_ = v_reuseFailAlloc_3368_;
goto v_reusejp_3366_;
}
v_reusejp_3366_:
{
return v___x_3367_;
}
}
}
}
v___jp_3240_:
{
lean_object* v___x_3248_; size_t v_sz_3249_; lean_object* v___x_3250_; 
v___x_3248_ = lean_box(0);
v_sz_3249_ = lean_array_size(v___y_3243_);
v___x_3250_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8(v___y_3242_, v___y_3243_, v_sz_3249_, v___x_3229_, v___x_3248_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_);
lean_dec_ref(v___y_3243_);
if (lean_obj_tag(v___x_3250_) == 0)
{
lean_object* v___x_3251_; 
lean_dec_ref(v___x_3250_);
v___x_3251_ = l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___redArg(v___y_3242_, v___y_3241_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_);
lean_dec_ref(v___y_3242_);
return v___x_3251_;
}
else
{
lean_object* v_a_3252_; lean_object* v___x_3254_; uint8_t v_isShared_3255_; uint8_t v_isSharedCheck_3259_; 
lean_dec_ref(v___y_3242_);
lean_dec_ref(v___y_3241_);
v_a_3252_ = lean_ctor_get(v___x_3250_, 0);
v_isSharedCheck_3259_ = !lean_is_exclusive(v___x_3250_);
if (v_isSharedCheck_3259_ == 0)
{
v___x_3254_ = v___x_3250_;
v_isShared_3255_ = v_isSharedCheck_3259_;
goto v_resetjp_3253_;
}
else
{
lean_inc(v_a_3252_);
lean_dec(v___x_3250_);
v___x_3254_ = lean_box(0);
v_isShared_3255_ = v_isSharedCheck_3259_;
goto v_resetjp_3253_;
}
v_resetjp_3253_:
{
lean_object* v___x_3257_; 
if (v_isShared_3255_ == 0)
{
v___x_3257_ = v___x_3254_;
goto v_reusejp_3256_;
}
else
{
lean_object* v_reuseFailAlloc_3258_; 
v_reuseFailAlloc_3258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3258_, 0, v_a_3252_);
v___x_3257_ = v_reuseFailAlloc_3258_;
goto v_reusejp_3256_;
}
v_reusejp_3256_:
{
return v___x_3257_;
}
}
}
}
v___jp_3261_:
{
lean_object* v_options_3269_; uint8_t v_hasTrace_3270_; 
v_options_3269_ = lean_ctor_get(v___y_3267_, 2);
v_hasTrace_3270_ = lean_ctor_get_uint8(v_options_3269_, sizeof(void*)*1);
if (v_hasTrace_3270_ == 0)
{
v___y_3241_ = v___y_3262_;
v___y_3242_ = v___y_3263_;
v___y_3243_ = v___y_3264_;
v___y_3244_ = v___y_3265_;
v___y_3245_ = v___y_3266_;
v___y_3246_ = v___y_3267_;
v___y_3247_ = v___y_3268_;
goto v___jp_3240_;
}
else
{
lean_object* v_inheritedTraceOptions_3271_; lean_object* v___x_3272_; uint8_t v___x_3273_; 
v_inheritedTraceOptions_3271_ = lean_ctor_get(v___y_3267_, 13);
v___x_3272_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__0);
v___x_3273_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3271_, v_options_3269_, v___x_3272_);
if (v___x_3273_ == 0)
{
v___y_3241_ = v___y_3262_;
v___y_3242_ = v___y_3263_;
v___y_3243_ = v___y_3264_;
v___y_3244_ = v___y_3265_;
v___y_3245_ = v___y_3266_;
v___y_3246_ = v___y_3267_;
v___y_3247_ = v___y_3268_;
goto v___jp_3240_;
}
else
{
lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; 
v___x_3274_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__2);
lean_inc_ref(v___y_3264_);
v___x_3275_ = l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10(v___y_3264_);
v___x_3276_ = l_Lean_MessageData_ofFormat(v___x_3275_);
v___x_3277_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3277_, 0, v___x_3274_);
lean_ctor_set(v___x_3277_, 1, v___x_3276_);
v___x_3278_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_3260_, v___x_3277_, v___y_3265_, v___y_3266_, v___y_3267_, v___y_3268_);
if (lean_obj_tag(v___x_3278_) == 0)
{
lean_dec_ref(v___x_3278_);
v___y_3241_ = v___y_3262_;
v___y_3242_ = v___y_3263_;
v___y_3243_ = v___y_3264_;
v___y_3244_ = v___y_3265_;
v___y_3245_ = v___y_3266_;
v___y_3246_ = v___y_3267_;
v___y_3247_ = v___y_3268_;
goto v___jp_3240_;
}
else
{
lean_object* v_a_3279_; lean_object* v___x_3281_; uint8_t v_isShared_3282_; uint8_t v_isSharedCheck_3286_; 
lean_dec_ref(v___y_3264_);
lean_dec_ref(v___y_3263_);
lean_dec_ref(v___y_3262_);
v_a_3279_ = lean_ctor_get(v___x_3278_, 0);
v_isSharedCheck_3286_ = !lean_is_exclusive(v___x_3278_);
if (v_isSharedCheck_3286_ == 0)
{
v___x_3281_ = v___x_3278_;
v_isShared_3282_ = v_isSharedCheck_3286_;
goto v_resetjp_3280_;
}
else
{
lean_inc(v_a_3279_);
lean_dec(v___x_3278_);
v___x_3281_ = lean_box(0);
v_isShared_3282_ = v_isSharedCheck_3286_;
goto v_resetjp_3280_;
}
v_resetjp_3280_:
{
lean_object* v___x_3284_; 
if (v_isShared_3282_ == 0)
{
v___x_3284_ = v___x_3281_;
goto v_reusejp_3283_;
}
else
{
lean_object* v_reuseFailAlloc_3285_; 
v_reuseFailAlloc_3285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3285_, 0, v_a_3279_);
v___x_3284_ = v_reuseFailAlloc_3285_;
goto v_reusejp_3283_;
}
v_reusejp_3283_:
{
return v___x_3284_;
}
}
}
}
}
}
v___jp_3291_:
{
lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v_snd_3298_; lean_object* v_fst_3299_; lean_object* v___x_3301_; uint8_t v_isShared_3302_; uint8_t v_isSharedCheck_3353_; 
lean_inc_ref(v_recArgInfos_3234_);
v___x_3296_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__3(v_sz_3289_, v___x_3229_, v_recArgInfos_3234_);
lean_inc_ref(v_xs_3231_);
v___x_3297_ = l_Lean_Elab_FixedParamPerms_erase(v_a_3230_, v_xs_3231_, v___x_3296_);
v_snd_3298_ = lean_ctor_get(v___x_3297_, 1);
v_fst_3299_ = lean_ctor_get(v___x_3297_, 0);
v_isSharedCheck_3353_ = !lean_is_exclusive(v___x_3297_);
if (v_isSharedCheck_3353_ == 0)
{
v___x_3301_ = v___x_3297_;
v_isShared_3302_ = v_isSharedCheck_3353_;
goto v_resetjp_3300_;
}
else
{
lean_inc(v_snd_3298_);
lean_inc(v_fst_3299_);
lean_dec(v___x_3297_);
v___x_3301_ = lean_box(0);
v_isShared_3302_ = v_isSharedCheck_3353_;
goto v_resetjp_3300_;
}
v_resetjp_3300_:
{
lean_object* v_fst_3303_; lean_object* v_snd_3304_; lean_object* v___x_3306_; uint8_t v_isShared_3307_; uint8_t v_isSharedCheck_3352_; 
v_fst_3303_ = lean_ctor_get(v_snd_3298_, 0);
v_snd_3304_ = lean_ctor_get(v_snd_3298_, 1);
v_isSharedCheck_3352_ = !lean_is_exclusive(v_snd_3298_);
if (v_isSharedCheck_3352_ == 0)
{
v___x_3306_ = v_snd_3298_;
v_isShared_3307_ = v_isSharedCheck_3352_;
goto v_resetjp_3305_;
}
else
{
lean_inc(v_snd_3304_);
lean_inc(v_fst_3303_);
lean_dec(v_snd_3298_);
v___x_3306_ = lean_box(0);
v_isShared_3307_ = v_isSharedCheck_3352_;
goto v_resetjp_3305_;
}
v_resetjp_3305_:
{
lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___f_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; uint8_t v___x_3314_; 
v___x_3308_ = lean_array_get_size(v_recArgInfos_3234_);
v___x_3309_ = lean_mk_empty_array_with_capacity(v___x_3308_);
v___x_3310_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg(v_fst_3299_, v_recArgInfos_3234_, v___x_3308_, v___x_3232_, v___x_3309_);
lean_dec_ref(v_recArgInfos_3234_);
lean_inc_ref(v___x_3310_);
lean_inc(v_fst_3303_);
v___f_3311_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___boxed), 10, 5);
lean_closure_set(v___f_3311_, 0, v_a_3233_);
lean_closure_set(v___f_3311_, 1, v_fst_3299_);
lean_closure_set(v___f_3311_, 2, v_fst_3303_);
lean_closure_set(v___f_3311_, 3, v___x_3310_);
lean_closure_set(v___f_3311_, 4, v___x_3290_);
v___x_3312_ = lean_array_get_size(v_fst_3303_);
v___x_3313_ = lean_array_get_size(v_xs_3231_);
v___x_3314_ = lean_nat_dec_eq(v___x_3312_, v___x_3313_);
if (v___x_3314_ == 0)
{
lean_object* v___x_3315_; lean_object* v_a_3316_; uint8_t v___x_3317_; 
v___x_3315_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0(v___x_3260_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_);
v_a_3316_ = lean_ctor_get(v___x_3315_, 0);
lean_inc(v_a_3316_);
lean_dec_ref(v___x_3315_);
v___x_3317_ = lean_unbox(v_a_3316_);
lean_dec(v_a_3316_);
if (v___x_3317_ == 0)
{
lean_del_object(v___x_3306_);
lean_dec(v_fst_3303_);
lean_del_object(v___x_3301_);
lean_dec_ref(v_xs_3231_);
v___y_3262_ = v___f_3311_;
v___y_3263_ = v_snd_3304_;
v___y_3264_ = v___x_3310_;
v___y_3265_ = v___y_3292_;
v___y_3266_ = v___y_3293_;
v___y_3267_ = v___y_3294_;
v___y_3268_ = v___y_3295_;
goto v___jp_3261_;
}
else
{
lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3324_; 
v___x_3318_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__4);
v___x_3319_ = lean_array_to_list(v_xs_3231_);
v___x_3320_ = lean_box(0);
v___x_3321_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_3319_, v___x_3320_);
v___x_3322_ = l_Lean_MessageData_ofList(v___x_3321_);
if (v_isShared_3307_ == 0)
{
lean_ctor_set_tag(v___x_3306_, 7);
lean_ctor_set(v___x_3306_, 1, v___x_3322_);
lean_ctor_set(v___x_3306_, 0, v___x_3318_);
v___x_3324_ = v___x_3306_;
goto v_reusejp_3323_;
}
else
{
lean_object* v_reuseFailAlloc_3350_; 
v_reuseFailAlloc_3350_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3350_, 0, v___x_3318_);
lean_ctor_set(v_reuseFailAlloc_3350_, 1, v___x_3322_);
v___x_3324_ = v_reuseFailAlloc_3350_;
goto v_reusejp_3323_;
}
v_reusejp_3323_:
{
lean_object* v___x_3325_; lean_object* v___x_3327_; 
v___x_3325_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__6, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__6);
if (v_isShared_3302_ == 0)
{
lean_ctor_set_tag(v___x_3301_, 7);
lean_ctor_set(v___x_3301_, 1, v___x_3325_);
lean_ctor_set(v___x_3301_, 0, v___x_3324_);
v___x_3327_ = v___x_3301_;
goto v_reusejp_3326_;
}
else
{
lean_object* v_reuseFailAlloc_3349_; 
v_reuseFailAlloc_3349_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3349_, 0, v___x_3324_);
lean_ctor_set(v_reuseFailAlloc_3349_, 1, v___x_3325_);
v___x_3327_ = v_reuseFailAlloc_3349_;
goto v_reusejp_3326_;
}
v_reusejp_3326_:
{
lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; size_t v_sz_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; 
v___x_3328_ = lean_array_to_list(v_fst_3303_);
v___x_3329_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_3328_, v___x_3320_);
v___x_3330_ = l_Lean_MessageData_ofList(v___x_3329_);
v___x_3331_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3331_, 0, v___x_3327_);
lean_ctor_set(v___x_3331_, 1, v___x_3330_);
v___x_3332_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__8);
v___x_3333_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3333_, 0, v___x_3331_);
lean_ctor_set(v___x_3333_, 1, v___x_3332_);
v_sz_3334_ = lean_array_size(v_snd_3304_);
lean_inc(v_snd_3304_);
v___x_3335_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__11(v_sz_3334_, v___x_3229_, v_snd_3304_);
v___x_3336_ = lean_array_to_list(v___x_3335_);
v___x_3337_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_3336_, v___x_3320_);
v___x_3338_ = l_Lean_MessageData_ofList(v___x_3337_);
v___x_3339_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3339_, 0, v___x_3333_);
lean_ctor_set(v___x_3339_, 1, v___x_3338_);
v___x_3340_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_3260_, v___x_3339_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_);
if (lean_obj_tag(v___x_3340_) == 0)
{
lean_dec_ref(v___x_3340_);
v___y_3262_ = v___f_3311_;
v___y_3263_ = v_snd_3304_;
v___y_3264_ = v___x_3310_;
v___y_3265_ = v___y_3292_;
v___y_3266_ = v___y_3293_;
v___y_3267_ = v___y_3294_;
v___y_3268_ = v___y_3295_;
goto v___jp_3261_;
}
else
{
lean_object* v_a_3341_; lean_object* v___x_3343_; uint8_t v_isShared_3344_; uint8_t v_isSharedCheck_3348_; 
lean_dec_ref(v___f_3311_);
lean_dec_ref(v___x_3310_);
lean_dec(v_snd_3304_);
v_a_3341_ = lean_ctor_get(v___x_3340_, 0);
v_isSharedCheck_3348_ = !lean_is_exclusive(v___x_3340_);
if (v_isSharedCheck_3348_ == 0)
{
v___x_3343_ = v___x_3340_;
v_isShared_3344_ = v_isSharedCheck_3348_;
goto v_resetjp_3342_;
}
else
{
lean_inc(v_a_3341_);
lean_dec(v___x_3340_);
v___x_3343_ = lean_box(0);
v_isShared_3344_ = v_isSharedCheck_3348_;
goto v_resetjp_3342_;
}
v_resetjp_3342_:
{
lean_object* v___x_3346_; 
if (v_isShared_3344_ == 0)
{
v___x_3346_ = v___x_3343_;
goto v_reusejp_3345_;
}
else
{
lean_object* v_reuseFailAlloc_3347_; 
v_reuseFailAlloc_3347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3347_, 0, v_a_3341_);
v___x_3346_ = v_reuseFailAlloc_3347_;
goto v_reusejp_3345_;
}
v_reusejp_3345_:
{
return v___x_3346_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3351_; 
lean_dec_ref(v___x_3310_);
lean_del_object(v___x_3306_);
lean_dec(v_fst_3303_);
lean_del_object(v___x_3301_);
lean_dec_ref(v_xs_3231_);
v___x_3351_ = l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___redArg(v_snd_3304_, v___f_3311_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_);
lean_dec(v_snd_3304_);
return v___x_3351_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___boxed(lean_object* v___x_3370_, lean_object* v_a_3371_, lean_object* v_xs_3372_, lean_object* v___x_3373_, lean_object* v_a_3374_, lean_object* v_recArgInfos_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_){
_start:
{
size_t v___x_15811__boxed_3381_; lean_object* v_res_3382_; 
v___x_15811__boxed_3381_ = lean_unbox_usize(v___x_3370_);
lean_dec(v___x_3370_);
v_res_3382_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0(v___x_15811__boxed_3381_, v_a_3371_, v_xs_3372_, v___x_3373_, v_a_3374_, v_recArgInfos_3375_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_);
lean_dec(v___y_3379_);
lean_dec_ref(v___y_3378_);
lean_dec(v___y_3377_);
lean_dec_ref(v___y_3376_);
return v_res_3382_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg(lean_object* v___x_3383_, lean_object* v_xs_3384_, lean_object* v_as_3385_, lean_object* v_i_3386_, lean_object* v_j_3387_, lean_object* v_bs_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_){
_start:
{
lean_object* v_zero_3394_; uint8_t v_isZero_3395_; 
v_zero_3394_ = lean_unsigned_to_nat(0u);
v_isZero_3395_ = lean_nat_dec_eq(v_i_3386_, v_zero_3394_);
if (v_isZero_3395_ == 1)
{
lean_object* v___x_3396_; 
lean_dec(v_j_3387_);
lean_dec(v_i_3386_);
lean_dec_ref(v_xs_3384_);
v___x_3396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3396_, 0, v_bs_3388_);
return v___x_3396_;
}
else
{
lean_object* v___x_3397_; lean_object* v_value_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; 
v___x_3397_ = lean_array_fget_borrowed(v_as_3385_, v_j_3387_);
v_value_3398_ = lean_ctor_get(v___x_3397_, 7);
v___x_3399_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0, &l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0_once, _init_l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0);
v___x_3400_ = lean_array_get_borrowed(v___x_3399_, v___x_3383_, v_j_3387_);
lean_inc_ref(v_xs_3384_);
lean_inc_ref(v_value_3398_);
lean_inc(v___x_3400_);
v___x_3401_ = l_Lean_Elab_FixedParamPerm_instantiateLambda(v___x_3400_, v_value_3398_, v_xs_3384_, v___y_3389_, v___y_3390_, v___y_3391_, v___y_3392_);
if (lean_obj_tag(v___x_3401_) == 0)
{
lean_object* v_a_3402_; lean_object* v_one_3403_; lean_object* v_n_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; 
v_a_3402_ = lean_ctor_get(v___x_3401_, 0);
lean_inc(v_a_3402_);
lean_dec_ref(v___x_3401_);
v_one_3403_ = lean_unsigned_to_nat(1u);
v_n_3404_ = lean_nat_sub(v_i_3386_, v_one_3403_);
lean_dec(v_i_3386_);
v___x_3405_ = lean_nat_add(v_j_3387_, v_one_3403_);
lean_dec(v_j_3387_);
v___x_3406_ = lean_array_push(v_bs_3388_, v_a_3402_);
v_i_3386_ = v_n_3404_;
v_j_3387_ = v___x_3405_;
v_bs_3388_ = v___x_3406_;
goto _start;
}
else
{
lean_object* v_a_3408_; lean_object* v___x_3410_; uint8_t v_isShared_3411_; uint8_t v_isSharedCheck_3415_; 
lean_dec_ref(v_bs_3388_);
lean_dec(v_j_3387_);
lean_dec(v_i_3386_);
lean_dec_ref(v_xs_3384_);
v_a_3408_ = lean_ctor_get(v___x_3401_, 0);
v_isSharedCheck_3415_ = !lean_is_exclusive(v___x_3401_);
if (v_isSharedCheck_3415_ == 0)
{
v___x_3410_ = v___x_3401_;
v_isShared_3411_ = v_isSharedCheck_3415_;
goto v_resetjp_3409_;
}
else
{
lean_inc(v_a_3408_);
lean_dec(v___x_3401_);
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
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg___boxed(lean_object* v___x_3416_, lean_object* v_xs_3417_, lean_object* v_as_3418_, lean_object* v_i_3419_, lean_object* v_j_3420_, lean_object* v_bs_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_){
_start:
{
lean_object* v_res_3427_; 
v_res_3427_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg(v___x_3416_, v_xs_3417_, v_as_3418_, v_i_3419_, v_j_3420_, v_bs_3421_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_);
lean_dec(v___y_3425_);
lean_dec_ref(v___y_3424_);
lean_dec(v___y_3423_);
lean_dec_ref(v___y_3422_);
lean_dec_ref(v_as_3418_);
lean_dec_ref(v___x_3416_);
return v_res_3427_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__2(lean_object* v_a_3428_, lean_object* v_perms_3429_, lean_object* v___x_3430_, lean_object* v_fnNames_3431_, lean_object* v_a_3432_, lean_object* v_termMeasure_x3fs_3433_, size_t v___x_3434_, lean_object* v_xs_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_){
_start:
{
lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; 
v___x_3441_ = lean_array_get_size(v_a_3428_);
v___x_3442_ = lean_mk_empty_array_with_capacity(v___x_3441_);
lean_inc(v___x_3430_);
lean_inc_ref(v_xs_3435_);
v___x_3443_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg(v_perms_3429_, v_xs_3435_, v_a_3428_, v___x_3441_, v___x_3430_, v___x_3442_, v___y_3436_, v___y_3437_, v___y_3438_, v___y_3439_);
if (lean_obj_tag(v___x_3443_) == 0)
{
lean_object* v_a_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; 
v_a_3444_ = lean_ctor_get(v___x_3443_, 0);
lean_inc_n(v_a_3444_, 2);
lean_dec_ref(v___x_3443_);
lean_inc_ref(v_xs_3435_);
lean_inc_ref(v_a_3432_);
lean_inc_ref(v_fnNames_3431_);
v___x_3445_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_findRecArgCandidates___boxed), 10, 5);
lean_closure_set(v___x_3445_, 0, v_fnNames_3431_);
lean_closure_set(v___x_3445_, 1, v_a_3432_);
lean_closure_set(v___x_3445_, 2, v_xs_3435_);
lean_closure_set(v___x_3445_, 3, v_a_3444_);
lean_closure_set(v___x_3445_, 4, v_termMeasure_x3fs_3433_);
lean_inc_ref(v_a_3428_);
v___x_3446_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v_a_3428_, v___x_3445_, v___y_3436_, v___y_3437_, v___y_3438_, v___y_3439_);
if (lean_obj_tag(v___x_3446_) == 0)
{
lean_object* v_a_3447_; lean_object* v___x_3448_; lean_object* v___f_3449_; lean_object* v___x_3450_; 
v_a_3447_ = lean_ctor_get(v___x_3446_, 0);
lean_inc(v_a_3447_);
lean_dec_ref(v___x_3446_);
v___x_3448_ = lean_box_usize(v___x_3434_);
lean_inc_ref(v_xs_3435_);
v___f_3449_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___boxed), 11, 5);
lean_closure_set(v___f_3449_, 0, v___x_3448_);
lean_closure_set(v___f_3449_, 1, v_a_3432_);
lean_closure_set(v___f_3449_, 2, v_xs_3435_);
lean_closure_set(v___f_3449_, 3, v___x_3430_);
lean_closure_set(v___f_3449_, 4, v_a_3428_);
v___x_3450_ = l_Lean_Elab_Structural_tryCandidates___redArg(v_fnNames_3431_, v_xs_3435_, v_a_3444_, v_a_3447_, v___f_3449_, v___y_3436_, v___y_3437_, v___y_3438_, v___y_3439_);
lean_dec_ref(v_fnNames_3431_);
return v___x_3450_;
}
else
{
lean_object* v_a_3451_; lean_object* v___x_3453_; uint8_t v_isShared_3454_; uint8_t v_isSharedCheck_3458_; 
lean_dec(v_a_3444_);
lean_dec_ref(v_xs_3435_);
lean_dec_ref(v_a_3432_);
lean_dec_ref(v_fnNames_3431_);
lean_dec(v___x_3430_);
lean_dec_ref(v_a_3428_);
v_a_3451_ = lean_ctor_get(v___x_3446_, 0);
v_isSharedCheck_3458_ = !lean_is_exclusive(v___x_3446_);
if (v_isSharedCheck_3458_ == 0)
{
v___x_3453_ = v___x_3446_;
v_isShared_3454_ = v_isSharedCheck_3458_;
goto v_resetjp_3452_;
}
else
{
lean_inc(v_a_3451_);
lean_dec(v___x_3446_);
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
else
{
lean_object* v_a_3459_; lean_object* v___x_3461_; uint8_t v_isShared_3462_; uint8_t v_isSharedCheck_3466_; 
lean_dec_ref(v_xs_3435_);
lean_dec_ref(v_termMeasure_x3fs_3433_);
lean_dec_ref(v_a_3432_);
lean_dec_ref(v_fnNames_3431_);
lean_dec(v___x_3430_);
lean_dec_ref(v_a_3428_);
v_a_3459_ = lean_ctor_get(v___x_3443_, 0);
v_isSharedCheck_3466_ = !lean_is_exclusive(v___x_3443_);
if (v_isSharedCheck_3466_ == 0)
{
v___x_3461_ = v___x_3443_;
v_isShared_3462_ = v_isSharedCheck_3466_;
goto v_resetjp_3460_;
}
else
{
lean_inc(v_a_3459_);
lean_dec(v___x_3443_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__2___boxed(lean_object* v_a_3467_, lean_object* v_perms_3468_, lean_object* v___x_3469_, lean_object* v_fnNames_3470_, lean_object* v_a_3471_, lean_object* v_termMeasure_x3fs_3472_, lean_object* v___x_3473_, lean_object* v_xs_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_){
_start:
{
size_t v___x_16168__boxed_3480_; lean_object* v_res_3481_; 
v___x_16168__boxed_3480_ = lean_unbox_usize(v___x_3473_);
lean_dec(v___x_3473_);
v_res_3481_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__2(v_a_3467_, v_perms_3468_, v___x_3469_, v_fnNames_3470_, v_a_3471_, v_termMeasure_x3fs_3472_, v___x_16168__boxed_3480_, v_xs_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_);
lean_dec(v___y_3478_);
lean_dec_ref(v___y_3477_);
lean_dec(v___y_3476_);
lean_dec_ref(v___y_3475_);
lean_dec_ref(v_perms_3468_);
return v_res_3481_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0(size_t v_sz_3482_, size_t v_i_3483_, lean_object* v_bs_3484_){
_start:
{
uint8_t v___x_3485_; 
v___x_3485_ = lean_usize_dec_lt(v_i_3483_, v_sz_3482_);
if (v___x_3485_ == 0)
{
return v_bs_3484_;
}
else
{
lean_object* v_v_3486_; lean_object* v_declName_3487_; lean_object* v___x_3488_; lean_object* v_bs_x27_3489_; size_t v___x_3490_; size_t v___x_3491_; lean_object* v___x_3492_; 
v_v_3486_ = lean_array_uget_borrowed(v_bs_3484_, v_i_3483_);
v_declName_3487_ = lean_ctor_get(v_v_3486_, 3);
lean_inc(v_declName_3487_);
v___x_3488_ = lean_unsigned_to_nat(0u);
v_bs_x27_3489_ = lean_array_uset(v_bs_3484_, v_i_3483_, v___x_3488_);
v___x_3490_ = ((size_t)1ULL);
v___x_3491_ = lean_usize_add(v_i_3483_, v___x_3490_);
v___x_3492_ = lean_array_uset(v_bs_x27_3489_, v_i_3483_, v_declName_3487_);
v_i_3483_ = v___x_3491_;
v_bs_3484_ = v___x_3492_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0___boxed(lean_object* v_sz_3494_, lean_object* v_i_3495_, lean_object* v_bs_3496_){
_start:
{
size_t v_sz_boxed_3497_; size_t v_i_boxed_3498_; lean_object* v_res_3499_; 
v_sz_boxed_3497_ = lean_unbox_usize(v_sz_3494_);
lean_dec(v_sz_3494_);
v_i_boxed_3498_ = lean_unbox_usize(v_i_3495_);
lean_dec(v_i_3495_);
v_res_3499_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0(v_sz_boxed_3497_, v_i_boxed_3498_, v_bs_3496_);
return v_res_3499_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1___redArg(lean_object* v_fnNames_3500_, lean_object* v_numSectionVars_3501_, size_t v_sz_3502_, size_t v_i_3503_, lean_object* v_bs_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_){
_start:
{
uint8_t v___x_3508_; 
v___x_3508_ = lean_usize_dec_lt(v_i_3503_, v_sz_3502_);
if (v___x_3508_ == 0)
{
lean_object* v___x_3509_; 
lean_dec(v_numSectionVars_3501_);
lean_dec_ref(v_fnNames_3500_);
v___x_3509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3509_, 0, v_bs_3504_);
return v___x_3509_;
}
else
{
lean_object* v_v_3510_; lean_object* v_ref_3511_; uint8_t v_kind_3512_; lean_object* v_levelParams_3513_; lean_object* v_modifiers_3514_; lean_object* v_declName_3515_; lean_object* v_binders_3516_; lean_object* v_numSectionVars_3517_; lean_object* v_type_3518_; lean_object* v_value_3519_; lean_object* v_termination_3520_; lean_object* v___x_3522_; uint8_t v_isShared_3523_; uint8_t v_isSharedCheck_3543_; 
v_v_3510_ = lean_array_uget(v_bs_3504_, v_i_3503_);
v_ref_3511_ = lean_ctor_get(v_v_3510_, 0);
v_kind_3512_ = lean_ctor_get_uint8(v_v_3510_, sizeof(void*)*9);
v_levelParams_3513_ = lean_ctor_get(v_v_3510_, 1);
v_modifiers_3514_ = lean_ctor_get(v_v_3510_, 2);
v_declName_3515_ = lean_ctor_get(v_v_3510_, 3);
v_binders_3516_ = lean_ctor_get(v_v_3510_, 4);
v_numSectionVars_3517_ = lean_ctor_get(v_v_3510_, 5);
v_type_3518_ = lean_ctor_get(v_v_3510_, 6);
v_value_3519_ = lean_ctor_get(v_v_3510_, 7);
v_termination_3520_ = lean_ctor_get(v_v_3510_, 8);
v_isSharedCheck_3543_ = !lean_is_exclusive(v_v_3510_);
if (v_isSharedCheck_3543_ == 0)
{
v___x_3522_ = v_v_3510_;
v_isShared_3523_ = v_isSharedCheck_3543_;
goto v_resetjp_3521_;
}
else
{
lean_inc(v_termination_3520_);
lean_inc(v_value_3519_);
lean_inc(v_type_3518_);
lean_inc(v_numSectionVars_3517_);
lean_inc(v_binders_3516_);
lean_inc(v_declName_3515_);
lean_inc(v_modifiers_3514_);
lean_inc(v_levelParams_3513_);
lean_inc(v_ref_3511_);
lean_dec(v_v_3510_);
v___x_3522_ = lean_box(0);
v_isShared_3523_ = v_isSharedCheck_3543_;
goto v_resetjp_3521_;
}
v_resetjp_3521_:
{
lean_object* v___x_3524_; 
lean_inc(v_numSectionVars_3501_);
lean_inc_ref(v_fnNames_3500_);
v___x_3524_ = l_Lean_Elab_Structural_preprocess(v_value_3519_, v_fnNames_3500_, v_numSectionVars_3501_, v___y_3505_, v___y_3506_);
if (lean_obj_tag(v___x_3524_) == 0)
{
lean_object* v_a_3525_; lean_object* v___x_3526_; lean_object* v_bs_x27_3527_; lean_object* v___x_3529_; 
v_a_3525_ = lean_ctor_get(v___x_3524_, 0);
lean_inc(v_a_3525_);
lean_dec_ref(v___x_3524_);
v___x_3526_ = lean_unsigned_to_nat(0u);
v_bs_x27_3527_ = lean_array_uset(v_bs_3504_, v_i_3503_, v___x_3526_);
if (v_isShared_3523_ == 0)
{
lean_ctor_set(v___x_3522_, 7, v_a_3525_);
v___x_3529_ = v___x_3522_;
goto v_reusejp_3528_;
}
else
{
lean_object* v_reuseFailAlloc_3534_; 
v_reuseFailAlloc_3534_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_3534_, 0, v_ref_3511_);
lean_ctor_set(v_reuseFailAlloc_3534_, 1, v_levelParams_3513_);
lean_ctor_set(v_reuseFailAlloc_3534_, 2, v_modifiers_3514_);
lean_ctor_set(v_reuseFailAlloc_3534_, 3, v_declName_3515_);
lean_ctor_set(v_reuseFailAlloc_3534_, 4, v_binders_3516_);
lean_ctor_set(v_reuseFailAlloc_3534_, 5, v_numSectionVars_3517_);
lean_ctor_set(v_reuseFailAlloc_3534_, 6, v_type_3518_);
lean_ctor_set(v_reuseFailAlloc_3534_, 7, v_a_3525_);
lean_ctor_set(v_reuseFailAlloc_3534_, 8, v_termination_3520_);
lean_ctor_set_uint8(v_reuseFailAlloc_3534_, sizeof(void*)*9, v_kind_3512_);
v___x_3529_ = v_reuseFailAlloc_3534_;
goto v_reusejp_3528_;
}
v_reusejp_3528_:
{
size_t v___x_3530_; size_t v___x_3531_; lean_object* v___x_3532_; 
v___x_3530_ = ((size_t)1ULL);
v___x_3531_ = lean_usize_add(v_i_3503_, v___x_3530_);
v___x_3532_ = lean_array_uset(v_bs_x27_3527_, v_i_3503_, v___x_3529_);
v_i_3503_ = v___x_3531_;
v_bs_3504_ = v___x_3532_;
goto _start;
}
}
else
{
lean_object* v_a_3535_; lean_object* v___x_3537_; uint8_t v_isShared_3538_; uint8_t v_isSharedCheck_3542_; 
lean_del_object(v___x_3522_);
lean_dec_ref(v_termination_3520_);
lean_dec_ref(v_type_3518_);
lean_dec(v_numSectionVars_3517_);
lean_dec(v_binders_3516_);
lean_dec(v_declName_3515_);
lean_dec_ref(v_modifiers_3514_);
lean_dec(v_levelParams_3513_);
lean_dec(v_ref_3511_);
lean_dec_ref(v_bs_3504_);
lean_dec(v_numSectionVars_3501_);
lean_dec_ref(v_fnNames_3500_);
v_a_3535_ = lean_ctor_get(v___x_3524_, 0);
v_isSharedCheck_3542_ = !lean_is_exclusive(v___x_3524_);
if (v_isSharedCheck_3542_ == 0)
{
v___x_3537_ = v___x_3524_;
v_isShared_3538_ = v_isSharedCheck_3542_;
goto v_resetjp_3536_;
}
else
{
lean_inc(v_a_3535_);
lean_dec(v___x_3524_);
v___x_3537_ = lean_box(0);
v_isShared_3538_ = v_isSharedCheck_3542_;
goto v_resetjp_3536_;
}
v_resetjp_3536_:
{
lean_object* v___x_3540_; 
if (v_isShared_3538_ == 0)
{
v___x_3540_ = v___x_3537_;
goto v_reusejp_3539_;
}
else
{
lean_object* v_reuseFailAlloc_3541_; 
v_reuseFailAlloc_3541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3541_, 0, v_a_3535_);
v___x_3540_ = v_reuseFailAlloc_3541_;
goto v_reusejp_3539_;
}
v_reusejp_3539_:
{
return v___x_3540_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1___redArg___boxed(lean_object* v_fnNames_3544_, lean_object* v_numSectionVars_3545_, lean_object* v_sz_3546_, lean_object* v_i_3547_, lean_object* v_bs_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_){
_start:
{
size_t v_sz_boxed_3552_; size_t v_i_boxed_3553_; lean_object* v_res_3554_; 
v_sz_boxed_3552_ = lean_unbox_usize(v_sz_3546_);
lean_dec(v_sz_3546_);
v_i_boxed_3553_ = lean_unbox_usize(v_i_3547_);
lean_dec(v_i_3547_);
v_res_3554_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1___redArg(v_fnNames_3544_, v_numSectionVars_3545_, v_sz_boxed_3552_, v_i_boxed_3553_, v_bs_3548_, v___y_3549_, v___y_3550_);
lean_dec(v___y_3550_);
lean_dec_ref(v___y_3549_);
return v_res_3554_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1(lean_object* v_fnNames_3555_, lean_object* v_numSectionVars_3556_, size_t v_sz_3557_, size_t v_i_3558_, lean_object* v_bs_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_){
_start:
{
lean_object* v___x_3565_; 
v___x_3565_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1___redArg(v_fnNames_3555_, v_numSectionVars_3556_, v_sz_3557_, v_i_3558_, v_bs_3559_, v___y_3562_, v___y_3563_);
return v___x_3565_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1___boxed(lean_object* v_fnNames_3566_, lean_object* v_numSectionVars_3567_, lean_object* v_sz_3568_, lean_object* v_i_3569_, lean_object* v_bs_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_){
_start:
{
size_t v_sz_boxed_3576_; size_t v_i_boxed_3577_; lean_object* v_res_3578_; 
v_sz_boxed_3576_ = lean_unbox_usize(v_sz_3568_);
lean_dec(v_sz_3568_);
v_i_boxed_3577_ = lean_unbox_usize(v_i_3569_);
lean_dec(v_i_3569_);
v_res_3578_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1(v_fnNames_3566_, v_numSectionVars_3567_, v_sz_boxed_3576_, v_i_boxed_3577_, v_bs_3570_, v___y_3571_, v___y_3572_, v___y_3573_, v___y_3574_);
lean_dec(v___y_3574_);
lean_dec_ref(v___y_3573_);
lean_dec(v___y_3572_);
lean_dec_ref(v___y_3571_);
return v_res_3578_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos(lean_object* v_preDefs_3579_, lean_object* v_termMeasure_x3fs_3580_, lean_object* v_a_3581_, lean_object* v_a_3582_, lean_object* v_a_3583_, lean_object* v_a_3584_){
_start:
{
lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v_numSectionVars_3589_; size_t v_sz_3590_; size_t v___x_3591_; lean_object* v_fnNames_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; 
v___x_3586_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_3587_ = lean_unsigned_to_nat(0u);
v___x_3588_ = lean_array_get_borrowed(v___x_3586_, v_preDefs_3579_, v___x_3587_);
v_numSectionVars_3589_ = lean_ctor_get(v___x_3588_, 5);
v_sz_3590_ = lean_array_size(v_preDefs_3579_);
v___x_3591_ = ((size_t)0ULL);
lean_inc_ref_n(v_preDefs_3579_, 2);
v_fnNames_3592_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0(v_sz_3590_, v___x_3591_, v_preDefs_3579_);
v___x_3593_ = lean_box_usize(v_sz_3590_);
v___x_3594_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___boxed__const__1));
lean_inc(v_numSectionVars_3589_);
lean_inc_ref(v_fnNames_3592_);
v___x_3595_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1___boxed), 10, 5);
lean_closure_set(v___x_3595_, 0, v_fnNames_3592_);
lean_closure_set(v___x_3595_, 1, v_numSectionVars_3589_);
lean_closure_set(v___x_3595_, 2, v___x_3593_);
lean_closure_set(v___x_3595_, 3, v___x_3594_);
lean_closure_set(v___x_3595_, 4, v_preDefs_3579_);
v___x_3596_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v_preDefs_3579_, v___x_3595_, v_a_3581_, v_a_3582_, v_a_3583_, v_a_3584_);
if (lean_obj_tag(v___x_3596_) == 0)
{
lean_object* v_a_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; 
v_a_3597_ = lean_ctor_get(v___x_3596_, 0);
lean_inc_n(v_a_3597_, 3);
lean_dec_ref(v___x_3596_);
v___x_3598_ = lean_alloc_closure((void*)(l_Lean_Elab_getFixedParamPerms___boxed), 6, 1);
lean_closure_set(v___x_3598_, 0, v_a_3597_);
v___x_3599_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v_a_3597_, v___x_3598_, v_a_3581_, v_a_3582_, v_a_3583_, v_a_3584_);
if (lean_obj_tag(v___x_3599_) == 0)
{
lean_object* v_a_3600_; lean_object* v_perms_3601_; lean_object* v___x_3602_; lean_object* v_type_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___f_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; 
v_a_3600_ = lean_ctor_get(v___x_3599_, 0);
lean_inc(v_a_3600_);
lean_dec_ref(v___x_3599_);
v_perms_3601_ = lean_ctor_get(v_a_3600_, 1);
lean_inc_ref_n(v_perms_3601_, 2);
v___x_3602_ = lean_array_get_borrowed(v___x_3586_, v_a_3597_, v___x_3587_);
v_type_3603_ = lean_ctor_get(v___x_3602_, 6);
lean_inc_ref(v_type_3603_);
v___x_3604_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0, &l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0_once, _init_l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0);
v___x_3605_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___boxed__const__1));
v___f_3606_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__2___boxed), 13, 7);
lean_closure_set(v___f_3606_, 0, v_a_3597_);
lean_closure_set(v___f_3606_, 1, v_perms_3601_);
lean_closure_set(v___f_3606_, 2, v___x_3587_);
lean_closure_set(v___f_3606_, 3, v_fnNames_3592_);
lean_closure_set(v___f_3606_, 4, v_a_3600_);
lean_closure_set(v___f_3606_, 5, v_termMeasure_x3fs_3580_);
lean_closure_set(v___f_3606_, 6, v___x_3605_);
v___x_3607_ = lean_array_get(v___x_3604_, v_perms_3601_, v___x_3587_);
lean_dec_ref(v_perms_3601_);
v___x_3608_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg(v___x_3607_, v_type_3603_, v___f_3606_, v_a_3581_, v_a_3582_, v_a_3583_, v_a_3584_);
return v___x_3608_;
}
else
{
lean_object* v_a_3609_; lean_object* v___x_3611_; uint8_t v_isShared_3612_; uint8_t v_isSharedCheck_3616_; 
lean_dec(v_a_3597_);
lean_dec_ref(v_fnNames_3592_);
lean_dec_ref(v_termMeasure_x3fs_3580_);
v_a_3609_ = lean_ctor_get(v___x_3599_, 0);
v_isSharedCheck_3616_ = !lean_is_exclusive(v___x_3599_);
if (v_isSharedCheck_3616_ == 0)
{
v___x_3611_ = v___x_3599_;
v_isShared_3612_ = v_isSharedCheck_3616_;
goto v_resetjp_3610_;
}
else
{
lean_inc(v_a_3609_);
lean_dec(v___x_3599_);
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
else
{
lean_object* v_a_3617_; lean_object* v___x_3619_; uint8_t v_isShared_3620_; uint8_t v_isSharedCheck_3624_; 
lean_dec_ref(v_fnNames_3592_);
lean_dec_ref(v_termMeasure_x3fs_3580_);
v_a_3617_ = lean_ctor_get(v___x_3596_, 0);
v_isSharedCheck_3624_ = !lean_is_exclusive(v___x_3596_);
if (v_isSharedCheck_3624_ == 0)
{
v___x_3619_ = v___x_3596_;
v_isShared_3620_ = v_isSharedCheck_3624_;
goto v_resetjp_3618_;
}
else
{
lean_inc(v_a_3617_);
lean_dec(v___x_3596_);
v___x_3619_ = lean_box(0);
v_isShared_3620_ = v_isSharedCheck_3624_;
goto v_resetjp_3618_;
}
v_resetjp_3618_:
{
lean_object* v___x_3622_; 
if (v_isShared_3620_ == 0)
{
v___x_3622_ = v___x_3619_;
goto v_reusejp_3621_;
}
else
{
lean_object* v_reuseFailAlloc_3623_; 
v_reuseFailAlloc_3623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3623_, 0, v_a_3617_);
v___x_3622_ = v_reuseFailAlloc_3623_;
goto v_reusejp_3621_;
}
v_reusejp_3621_:
{
return v___x_3622_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___boxed(lean_object* v_preDefs_3625_, lean_object* v_termMeasure_x3fs_3626_, lean_object* v_a_3627_, lean_object* v_a_3628_, lean_object* v_a_3629_, lean_object* v_a_3630_, lean_object* v_a_3631_){
_start:
{
lean_object* v_res_3632_; 
v_res_3632_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos(v_preDefs_3625_, v_termMeasure_x3fs_3626_, v_a_3627_, v_a_3628_, v_a_3629_, v_a_3630_);
lean_dec(v_a_3630_);
lean_dec_ref(v_a_3629_);
lean_dec(v_a_3628_);
lean_dec_ref(v_a_3627_);
return v_res_3632_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4(lean_object* v_fst_3633_, lean_object* v_as_3634_, lean_object* v_i_3635_, lean_object* v_j_3636_, lean_object* v_inv_3637_, lean_object* v_bs_3638_){
_start:
{
lean_object* v___x_3639_; 
v___x_3639_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg(v_fst_3633_, v_as_3634_, v_i_3635_, v_j_3636_, v_bs_3638_);
return v___x_3639_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___boxed(lean_object* v_fst_3640_, lean_object* v_as_3641_, lean_object* v_i_3642_, lean_object* v_j_3643_, lean_object* v_inv_3644_, lean_object* v_bs_3645_){
_start:
{
lean_object* v_res_3646_; 
v_res_3646_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4(v_fst_3640_, v_as_3641_, v_i_3642_, v_j_3643_, v_inv_3644_, v_bs_3645_);
lean_dec_ref(v_as_3641_);
lean_dec_ref(v_fst_3640_);
return v_res_3646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10(lean_object* v_00_u03b1_3647_, lean_object* v_lctx_3648_, lean_object* v_localInsts_3649_, lean_object* v_x_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_){
_start:
{
lean_object* v___x_3656_; 
v___x_3656_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___redArg(v_lctx_3648_, v_localInsts_3649_, v_x_3650_, v___y_3651_, v___y_3652_, v___y_3653_, v___y_3654_);
return v___x_3656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___boxed(lean_object* v_00_u03b1_3657_, lean_object* v_lctx_3658_, lean_object* v_localInsts_3659_, lean_object* v_x_3660_, lean_object* v___y_3661_, lean_object* v___y_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_){
_start:
{
lean_object* v_res_3666_; 
v_res_3666_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10(v_00_u03b1_3657_, v_lctx_3658_, v_localInsts_3659_, v_x_3660_, v___y_3661_, v___y_3662_, v___y_3663_, v___y_3664_);
lean_dec(v___y_3664_);
lean_dec_ref(v___y_3663_);
lean_dec(v___y_3662_);
lean_dec_ref(v___y_3661_);
return v_res_3666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9(lean_object* v_00_u03b1_3667_, lean_object* v_fvarIds_3668_, lean_object* v_k_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_){
_start:
{
lean_object* v___x_3675_; 
v___x_3675_ = l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___redArg(v_fvarIds_3668_, v_k_3669_, v___y_3670_, v___y_3671_, v___y_3672_, v___y_3673_);
return v___x_3675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___boxed(lean_object* v_00_u03b1_3676_, lean_object* v_fvarIds_3677_, lean_object* v_k_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_, lean_object* v___y_3682_, lean_object* v___y_3683_){
_start:
{
lean_object* v_res_3684_; 
v_res_3684_ = l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9(v_00_u03b1_3676_, v_fvarIds_3677_, v_k_3678_, v___y_3679_, v___y_3680_, v___y_3681_, v___y_3682_);
lean_dec(v___y_3682_);
lean_dec_ref(v___y_3681_);
lean_dec(v___y_3680_);
lean_dec_ref(v___y_3679_);
lean_dec_ref(v_fvarIds_3677_);
return v_res_3684_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__15(lean_object* v_a_3685_){
_start:
{
lean_object* v___x_3686_; 
v___x_3686_ = lean_nat_to_int(v_a_3685_);
return v___x_3686_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12(lean_object* v___x_3687_, lean_object* v_xs_3688_, lean_object* v_as_3689_, lean_object* v_i_3690_, lean_object* v_j_3691_, lean_object* v_inv_3692_, lean_object* v_bs_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_){
_start:
{
lean_object* v___x_3699_; 
v___x_3699_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg(v___x_3687_, v_xs_3688_, v_as_3689_, v_i_3690_, v_j_3691_, v_bs_3693_, v___y_3694_, v___y_3695_, v___y_3696_, v___y_3697_);
return v___x_3699_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___boxed(lean_object* v___x_3700_, lean_object* v_xs_3701_, lean_object* v_as_3702_, lean_object* v_i_3703_, lean_object* v_j_3704_, lean_object* v_inv_3705_, lean_object* v_bs_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_){
_start:
{
lean_object* v_res_3712_; 
v_res_3712_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12(v___x_3700_, v_xs_3701_, v_as_3702_, v_i_3703_, v_j_3704_, v_inv_3705_, v_bs_3706_, v___y_3707_, v___y_3708_, v___y_3709_, v___y_3710_);
lean_dec(v___y_3710_);
lean_dec_ref(v___y_3709_);
lean_dec(v___y_3708_);
lean_dec_ref(v___y_3707_);
lean_dec_ref(v_as_3702_);
lean_dec_ref(v___x_3700_);
return v_res_3712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure___lam__0(lean_object* v___x_3713_, lean_object* v_recArgPos_3714_, lean_object* v_xs_3715_, lean_object* v_x_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_){
_start:
{
lean_object* v___x_3722_; uint8_t v___x_3723_; uint8_t v___x_3724_; uint8_t v___x_3725_; lean_object* v___x_3726_; 
v___x_3722_ = lean_array_get_borrowed(v___x_3713_, v_xs_3715_, v_recArgPos_3714_);
v___x_3723_ = 0;
v___x_3724_ = 1;
v___x_3725_ = 1;
lean_inc(v___x_3722_);
v___x_3726_ = l_Lean_Meta_mkLambdaFVars(v_xs_3715_, v___x_3722_, v___x_3723_, v___x_3724_, v___x_3723_, v___x_3724_, v___x_3725_, v___y_3717_, v___y_3718_, v___y_3719_, v___y_3720_);
return v___x_3726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure___lam__0___boxed(lean_object* v___x_3727_, lean_object* v_recArgPos_3728_, lean_object* v_xs_3729_, lean_object* v_x_3730_, lean_object* v___y_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_){
_start:
{
lean_object* v_res_3736_; 
v_res_3736_ = l_Lean_Elab_Structural_reportTermMeasure___lam__0(v___x_3727_, v_recArgPos_3728_, v_xs_3729_, v_x_3730_, v___y_3731_, v___y_3732_, v___y_3733_, v___y_3734_);
lean_dec(v___y_3734_);
lean_dec_ref(v___y_3733_);
lean_dec(v___y_3732_);
lean_dec_ref(v___y_3731_);
lean_dec_ref(v_x_3730_);
lean_dec_ref(v_xs_3729_);
lean_dec(v_recArgPos_3728_);
lean_dec_ref(v___x_3727_);
return v_res_3736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure___lam__1(lean_object* v_xs_3737_, lean_object* v_x_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_){
_start:
{
lean_object* v___x_3744_; lean_object* v___x_3745_; 
v___x_3744_ = lean_array_get_size(v_xs_3737_);
v___x_3745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3745_, 0, v___x_3744_);
return v___x_3745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure___lam__1___boxed(lean_object* v_xs_3746_, lean_object* v_x_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_){
_start:
{
lean_object* v_res_3753_; 
v_res_3753_ = l_Lean_Elab_Structural_reportTermMeasure___lam__1(v_xs_3746_, v_x_3747_, v___y_3748_, v___y_3749_, v___y_3750_, v___y_3751_);
lean_dec(v___y_3751_);
lean_dec_ref(v___y_3750_);
lean_dec(v___y_3749_);
lean_dec_ref(v___y_3748_);
lean_dec_ref(v_x_3747_);
lean_dec_ref(v_xs_3746_);
return v_res_3753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure(lean_object* v_preDef_3765_, lean_object* v_recArgPos_3766_, lean_object* v_a_3767_, lean_object* v_a_3768_, lean_object* v_a_3769_, lean_object* v_a_3770_){
_start:
{
lean_object* v_termination_3772_; lean_object* v_terminationBy_x3f_x3f_3773_; 
v_termination_3772_ = lean_ctor_get(v_preDef_3765_, 8);
lean_inc_ref(v_termination_3772_);
v_terminationBy_x3f_x3f_3773_ = lean_ctor_get(v_termination_3772_, 1);
lean_inc(v_terminationBy_x3f_x3f_3773_);
if (lean_obj_tag(v_terminationBy_x3f_x3f_3773_) == 1)
{
lean_object* v_value_3774_; lean_object* v_extraParams_3775_; lean_object* v___x_3777_; uint8_t v_isShared_3778_; uint8_t v_isSharedCheck_3826_; 
v_value_3774_ = lean_ctor_get(v_preDef_3765_, 7);
lean_inc_ref(v_value_3774_);
lean_dec_ref(v_preDef_3765_);
v_extraParams_3775_ = lean_ctor_get(v_termination_3772_, 5);
v_isSharedCheck_3826_ = !lean_is_exclusive(v_termination_3772_);
if (v_isSharedCheck_3826_ == 0)
{
lean_object* v_unused_3827_; lean_object* v_unused_3828_; lean_object* v_unused_3829_; lean_object* v_unused_3830_; lean_object* v_unused_3831_; 
v_unused_3827_ = lean_ctor_get(v_termination_3772_, 4);
lean_dec(v_unused_3827_);
v_unused_3828_ = lean_ctor_get(v_termination_3772_, 3);
lean_dec(v_unused_3828_);
v_unused_3829_ = lean_ctor_get(v_termination_3772_, 2);
lean_dec(v_unused_3829_);
v_unused_3830_ = lean_ctor_get(v_termination_3772_, 1);
lean_dec(v_unused_3830_);
v_unused_3831_ = lean_ctor_get(v_termination_3772_, 0);
lean_dec(v_unused_3831_);
v___x_3777_ = v_termination_3772_;
v_isShared_3778_ = v_isSharedCheck_3826_;
goto v_resetjp_3776_;
}
else
{
lean_inc(v_extraParams_3775_);
lean_dec(v_termination_3772_);
v___x_3777_ = lean_box(0);
v_isShared_3778_ = v_isSharedCheck_3826_;
goto v_resetjp_3776_;
}
v_resetjp_3776_:
{
lean_object* v_val_3779_; lean_object* v___x_3780_; lean_object* v___f_3781_; uint8_t v___x_3782_; lean_object* v___x_3783_; 
v_val_3779_ = lean_ctor_get(v_terminationBy_x3f_x3f_3773_, 0);
lean_inc(v_val_3779_);
lean_dec_ref(v_terminationBy_x3f_x3f_3773_);
v___x_3780_ = l_Lean_instInhabitedExpr;
v___f_3781_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_reportTermMeasure___lam__0___boxed), 9, 2);
lean_closure_set(v___f_3781_, 0, v___x_3780_);
lean_closure_set(v___f_3781_, 1, v_recArgPos_3766_);
v___x_3782_ = 0;
lean_inc_ref(v_value_3774_);
v___x_3783_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg(v_value_3774_, v___f_3781_, v___x_3782_, v_a_3767_, v_a_3768_, v_a_3769_, v_a_3770_);
if (lean_obj_tag(v___x_3783_) == 0)
{
lean_object* v_a_3784_; lean_object* v___f_3785_; lean_object* v___x_3786_; 
v_a_3784_ = lean_ctor_get(v___x_3783_, 0);
lean_inc(v_a_3784_);
lean_dec_ref(v___x_3783_);
v___f_3785_ = ((lean_object*)(l_Lean_Elab_Structural_reportTermMeasure___closed__0));
v___x_3786_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg(v_value_3774_, v___f_3785_, v___x_3782_, v_a_3767_, v_a_3768_, v_a_3769_, v_a_3770_);
if (lean_obj_tag(v___x_3786_) == 0)
{
lean_object* v_a_3787_; lean_object* v___x_3788_; uint8_t v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; 
v_a_3787_ = lean_ctor_get(v___x_3786_, 0);
lean_inc(v_a_3787_);
lean_dec_ref(v___x_3786_);
v___x_3788_ = lean_box(0);
v___x_3789_ = 1;
v___x_3790_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3790_, 0, v___x_3788_);
lean_ctor_set(v___x_3790_, 1, v_a_3784_);
lean_ctor_set_uint8(v___x_3790_, sizeof(void*)*2, v___x_3789_);
v___x_3791_ = l_Lean_Elab_TerminationMeasure_delab(v_a_3787_, v_extraParams_3775_, v___x_3790_, v_a_3767_, v_a_3768_, v_a_3769_, v_a_3770_);
lean_dec(v_a_3787_);
if (lean_obj_tag(v___x_3791_) == 0)
{
lean_object* v_a_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3797_; 
v_a_3792_ = lean_ctor_get(v___x_3791_, 0);
lean_inc(v_a_3792_);
lean_dec_ref(v___x_3791_);
v___x_3793_ = ((lean_object*)(l_Lean_Elab_Structural_reportTermMeasure___closed__5));
v___x_3794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3794_, 0, v___x_3793_);
lean_ctor_set(v___x_3794_, 1, v_a_3792_);
v___x_3795_ = lean_box(0);
if (v_isShared_3778_ == 0)
{
lean_ctor_set(v___x_3777_, 5, v___x_3795_);
lean_ctor_set(v___x_3777_, 4, v___x_3795_);
lean_ctor_set(v___x_3777_, 3, v___x_3795_);
lean_ctor_set(v___x_3777_, 2, v___x_3795_);
lean_ctor_set(v___x_3777_, 1, v___x_3795_);
lean_ctor_set(v___x_3777_, 0, v___x_3794_);
v___x_3797_ = v___x_3777_;
goto v_reusejp_3796_;
}
else
{
lean_object* v_reuseFailAlloc_3801_; 
v_reuseFailAlloc_3801_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3801_, 0, v___x_3794_);
lean_ctor_set(v_reuseFailAlloc_3801_, 1, v___x_3795_);
lean_ctor_set(v_reuseFailAlloc_3801_, 2, v___x_3795_);
lean_ctor_set(v_reuseFailAlloc_3801_, 3, v___x_3795_);
lean_ctor_set(v_reuseFailAlloc_3801_, 4, v___x_3795_);
lean_ctor_set(v_reuseFailAlloc_3801_, 5, v___x_3795_);
v___x_3797_ = v_reuseFailAlloc_3801_;
goto v_reusejp_3796_;
}
v_reusejp_3796_:
{
lean_object* v___x_3798_; uint8_t v___x_3799_; lean_object* v___x_3800_; 
v___x_3798_ = ((lean_object*)(l_Lean_Elab_Structural_reportTermMeasure___closed__6));
v___x_3799_ = 4;
v___x_3800_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_val_3779_, v___x_3797_, v___x_3795_, v___x_3798_, v___x_3795_, v___x_3799_, v_a_3769_, v_a_3770_);
return v___x_3800_;
}
}
else
{
lean_object* v_a_3802_; lean_object* v___x_3804_; uint8_t v_isShared_3805_; uint8_t v_isSharedCheck_3809_; 
lean_dec(v_val_3779_);
lean_del_object(v___x_3777_);
v_a_3802_ = lean_ctor_get(v___x_3791_, 0);
v_isSharedCheck_3809_ = !lean_is_exclusive(v___x_3791_);
if (v_isSharedCheck_3809_ == 0)
{
v___x_3804_ = v___x_3791_;
v_isShared_3805_ = v_isSharedCheck_3809_;
goto v_resetjp_3803_;
}
else
{
lean_inc(v_a_3802_);
lean_dec(v___x_3791_);
v___x_3804_ = lean_box(0);
v_isShared_3805_ = v_isSharedCheck_3809_;
goto v_resetjp_3803_;
}
v_resetjp_3803_:
{
lean_object* v___x_3807_; 
if (v_isShared_3805_ == 0)
{
v___x_3807_ = v___x_3804_;
goto v_reusejp_3806_;
}
else
{
lean_object* v_reuseFailAlloc_3808_; 
v_reuseFailAlloc_3808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3808_, 0, v_a_3802_);
v___x_3807_ = v_reuseFailAlloc_3808_;
goto v_reusejp_3806_;
}
v_reusejp_3806_:
{
return v___x_3807_;
}
}
}
}
else
{
lean_object* v_a_3810_; lean_object* v___x_3812_; uint8_t v_isShared_3813_; uint8_t v_isSharedCheck_3817_; 
lean_dec(v_a_3784_);
lean_dec(v_val_3779_);
lean_del_object(v___x_3777_);
lean_dec(v_extraParams_3775_);
v_a_3810_ = lean_ctor_get(v___x_3786_, 0);
v_isSharedCheck_3817_ = !lean_is_exclusive(v___x_3786_);
if (v_isSharedCheck_3817_ == 0)
{
v___x_3812_ = v___x_3786_;
v_isShared_3813_ = v_isSharedCheck_3817_;
goto v_resetjp_3811_;
}
else
{
lean_inc(v_a_3810_);
lean_dec(v___x_3786_);
v___x_3812_ = lean_box(0);
v_isShared_3813_ = v_isSharedCheck_3817_;
goto v_resetjp_3811_;
}
v_resetjp_3811_:
{
lean_object* v___x_3815_; 
if (v_isShared_3813_ == 0)
{
v___x_3815_ = v___x_3812_;
goto v_reusejp_3814_;
}
else
{
lean_object* v_reuseFailAlloc_3816_; 
v_reuseFailAlloc_3816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3816_, 0, v_a_3810_);
v___x_3815_ = v_reuseFailAlloc_3816_;
goto v_reusejp_3814_;
}
v_reusejp_3814_:
{
return v___x_3815_;
}
}
}
}
else
{
lean_object* v_a_3818_; lean_object* v___x_3820_; uint8_t v_isShared_3821_; uint8_t v_isSharedCheck_3825_; 
lean_dec(v_val_3779_);
lean_del_object(v___x_3777_);
lean_dec(v_extraParams_3775_);
lean_dec_ref(v_value_3774_);
v_a_3818_ = lean_ctor_get(v___x_3783_, 0);
v_isSharedCheck_3825_ = !lean_is_exclusive(v___x_3783_);
if (v_isSharedCheck_3825_ == 0)
{
v___x_3820_ = v___x_3783_;
v_isShared_3821_ = v_isSharedCheck_3825_;
goto v_resetjp_3819_;
}
else
{
lean_inc(v_a_3818_);
lean_dec(v___x_3783_);
v___x_3820_ = lean_box(0);
v_isShared_3821_ = v_isSharedCheck_3825_;
goto v_resetjp_3819_;
}
v_resetjp_3819_:
{
lean_object* v___x_3823_; 
if (v_isShared_3821_ == 0)
{
v___x_3823_ = v___x_3820_;
goto v_reusejp_3822_;
}
else
{
lean_object* v_reuseFailAlloc_3824_; 
v_reuseFailAlloc_3824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3824_, 0, v_a_3818_);
v___x_3823_ = v_reuseFailAlloc_3824_;
goto v_reusejp_3822_;
}
v_reusejp_3822_:
{
return v___x_3823_;
}
}
}
}
}
else
{
lean_object* v___x_3832_; lean_object* v___x_3833_; 
lean_dec(v_terminationBy_x3f_x3f_3773_);
lean_dec_ref(v_termination_3772_);
lean_dec(v_recArgPos_3766_);
lean_dec_ref(v_preDef_3765_);
v___x_3832_ = lean_box(0);
v___x_3833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3833_, 0, v___x_3832_);
return v___x_3833_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure___boxed(lean_object* v_preDef_3834_, lean_object* v_recArgPos_3835_, lean_object* v_a_3836_, lean_object* v_a_3837_, lean_object* v_a_3838_, lean_object* v_a_3839_, lean_object* v_a_3840_){
_start:
{
lean_object* v_res_3841_; 
v_res_3841_ = l_Lean_Elab_Structural_reportTermMeasure(v_preDef_3834_, v_recArgPos_3835_, v_a_3836_, v_a_3837_, v_a_3838_, v_a_3839_);
lean_dec(v_a_3839_);
lean_dec_ref(v_a_3838_);
lean_dec(v_a_3837_);
lean_dec_ref(v_a_3836_);
return v_res_3841_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___redArg(lean_object* v_as_3842_, size_t v_sz_3843_, size_t v_i_3844_, lean_object* v_b_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_){
_start:
{
uint8_t v___x_3851_; 
v___x_3851_ = lean_usize_dec_lt(v_i_3844_, v_sz_3843_);
if (v___x_3851_ == 0)
{
lean_object* v___x_3852_; 
v___x_3852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3852_, 0, v_b_3845_);
return v___x_3852_;
}
else
{
lean_object* v_a_3853_; lean_object* v_declName_3854_; lean_object* v___x_3855_; 
v_a_3853_ = lean_array_uget_borrowed(v_as_3842_, v_i_3844_);
v_declName_3854_ = lean_ctor_get(v_a_3853_, 3);
lean_inc(v_declName_3854_);
v___x_3855_ = l_Lean_enableRealizationsForConst(v_declName_3854_, v___y_3848_, v___y_3849_);
if (lean_obj_tag(v___x_3855_) == 0)
{
lean_object* v___x_3856_; 
lean_dec_ref(v___x_3855_);
lean_inc(v_declName_3854_);
v___x_3856_ = l_Lean_Meta_generateEagerEqns(v_declName_3854_, v___y_3846_, v___y_3847_, v___y_3848_, v___y_3849_);
if (lean_obj_tag(v___x_3856_) == 0)
{
lean_object* v___x_3857_; size_t v___x_3858_; size_t v___x_3859_; 
lean_dec_ref(v___x_3856_);
v___x_3857_ = lean_box(0);
v___x_3858_ = ((size_t)1ULL);
v___x_3859_ = lean_usize_add(v_i_3844_, v___x_3858_);
v_i_3844_ = v___x_3859_;
v_b_3845_ = v___x_3857_;
goto _start;
}
else
{
return v___x_3856_;
}
}
else
{
return v___x_3855_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___redArg___boxed(lean_object* v_as_3861_, lean_object* v_sz_3862_, lean_object* v_i_3863_, lean_object* v_b_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_){
_start:
{
size_t v_sz_boxed_3870_; size_t v_i_boxed_3871_; lean_object* v_res_3872_; 
v_sz_boxed_3870_ = lean_unbox_usize(v_sz_3862_);
lean_dec(v_sz_3862_);
v_i_boxed_3871_ = lean_unbox_usize(v_i_3863_);
lean_dec(v_i_3863_);
v_res_3872_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___redArg(v_as_3861_, v_sz_boxed_3870_, v_i_boxed_3871_, v_b_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_);
lean_dec(v___y_3868_);
lean_dec_ref(v___y_3867_);
lean_dec(v___y_3866_);
lean_dec_ref(v___y_3865_);
lean_dec_ref(v_as_3861_);
return v_res_3872_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4___lam__0(lean_object* v___x_3873_, lean_object* v_e_3874_){
_start:
{
lean_object* v___x_3875_; lean_object* v___x_3876_; 
v___x_3875_ = l_Lean_indentD(v_e_3874_);
v___x_3876_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3876_, 0, v___x_3873_);
lean_ctor_set(v___x_3876_, 1, v___x_3875_);
return v___x_3876_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4___lam__1(lean_object* v_docCtx_3877_, lean_object* v_a_3878_, uint8_t v___x_3879_, lean_object* v___x_3880_, uint8_t v___x_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_){
_start:
{
lean_object* v___x_3889_; 
v___x_3889_ = l_Lean_Elab_addNonRec(v_docCtx_3877_, v_a_3878_, v___x_3879_, v___x_3880_, v___x_3881_, v___x_3879_, v___x_3881_, v___y_3882_, v___y_3883_, v___y_3884_, v___y_3885_, v___y_3886_, v___y_3887_);
return v___x_3889_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4___lam__1___boxed(lean_object* v_docCtx_3890_, lean_object* v_a_3891_, lean_object* v___x_3892_, lean_object* v___x_3893_, lean_object* v___x_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_){
_start:
{
uint8_t v___x_8569__boxed_3902_; uint8_t v___x_8571__boxed_3903_; lean_object* v_res_3904_; 
v___x_8569__boxed_3902_ = lean_unbox(v___x_3892_);
v___x_8571__boxed_3903_ = lean_unbox(v___x_3894_);
v_res_3904_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4___lam__1(v_docCtx_3890_, v_a_3891_, v___x_8569__boxed_3902_, v___x_3893_, v___x_8571__boxed_3903_, v___y_3895_, v___y_3896_, v___y_3897_, v___y_3898_, v___y_3899_, v___y_3900_);
lean_dec(v___y_3900_);
lean_dec_ref(v___y_3899_);
lean_dec(v___y_3898_);
lean_dec_ref(v___y_3897_);
lean_dec(v___y_3896_);
lean_dec_ref(v___y_3895_);
return v_res_3904_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4___closed__1(void){
_start:
{
lean_object* v___x_3906_; lean_object* v___x_3907_; 
v___x_3906_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4___closed__0));
v___x_3907_ = l_Lean_stringToMessageData(v___x_3906_);
return v___x_3907_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4___closed__2(void){
_start:
{
lean_object* v___x_3908_; lean_object* v___f_3909_; 
v___x_3908_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4___closed__1);
v___f_3909_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4___lam__0), 2, 1);
lean_closure_set(v___f_3909_, 0, v___x_3908_);
return v___f_3909_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4(lean_object* v_names_3910_, lean_object* v_docCtx_3911_, lean_object* v_as_3912_, size_t v_i_3913_, size_t v_stop_3914_, lean_object* v_b_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_){
_start:
{
uint8_t v___x_3923_; 
v___x_3923_ = lean_usize_dec_eq(v_i_3913_, v_stop_3914_);
if (v___x_3923_ == 0)
{
lean_object* v___x_3924_; lean_object* v___x_3925_; 
v___x_3924_ = lean_array_uget_borrowed(v_as_3912_, v_i_3913_);
lean_inc(v___x_3924_);
v___x_3925_ = l_Lean_Elab_eraseRecAppSyntax(v___x_3924_, v___y_3920_, v___y_3921_);
if (lean_obj_tag(v___x_3925_) == 0)
{
lean_object* v_a_3926_; lean_object* v___f_3927_; lean_object* v___x_3928_; uint8_t v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___f_3932_; lean_object* v___x_3933_; 
v_a_3926_ = lean_ctor_get(v___x_3925_, 0);
lean_inc(v_a_3926_);
lean_dec_ref(v___x_3925_);
v___f_3927_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4___closed__2, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4___closed__2);
lean_inc_ref(v_names_3910_);
v___x_3928_ = lean_array_to_list(v_names_3910_);
v___x_3929_ = 1;
v___x_3930_ = lean_box(v___x_3923_);
v___x_3931_ = lean_box(v___x_3929_);
lean_inc(v___y_3917_);
lean_inc_ref(v___y_3916_);
lean_inc_ref(v_docCtx_3911_);
v___f_3932_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4___lam__1___boxed), 12, 7);
lean_closure_set(v___f_3932_, 0, v_docCtx_3911_);
lean_closure_set(v___f_3932_, 1, v_a_3926_);
lean_closure_set(v___f_3932_, 2, v___x_3930_);
lean_closure_set(v___f_3932_, 3, v___x_3928_);
lean_closure_set(v___f_3932_, 4, v___x_3931_);
lean_closure_set(v___f_3932_, 5, v___y_3916_);
lean_closure_set(v___f_3932_, 6, v___y_3917_);
v___x_3933_ = l_Lean_Meta_mapErrorImp___redArg(v___f_3932_, v___f_3927_, v___y_3918_, v___y_3919_, v___y_3920_, v___y_3921_);
if (lean_obj_tag(v___x_3933_) == 0)
{
if (lean_obj_tag(v___x_3933_) == 0)
{
lean_object* v_a_3934_; size_t v___x_3935_; size_t v___x_3936_; 
v_a_3934_ = lean_ctor_get(v___x_3933_, 0);
lean_inc(v_a_3934_);
lean_dec_ref(v___x_3933_);
v___x_3935_ = ((size_t)1ULL);
v___x_3936_ = lean_usize_add(v_i_3913_, v___x_3935_);
v_i_3913_ = v___x_3936_;
v_b_3915_ = v_a_3934_;
goto _start;
}
else
{
lean_dec_ref(v_docCtx_3911_);
lean_dec_ref(v_names_3910_);
return v___x_3933_;
}
}
else
{
lean_object* v_a_3938_; lean_object* v___x_3940_; uint8_t v_isShared_3941_; uint8_t v_isSharedCheck_3945_; 
lean_dec_ref(v_docCtx_3911_);
lean_dec_ref(v_names_3910_);
v_a_3938_ = lean_ctor_get(v___x_3933_, 0);
v_isSharedCheck_3945_ = !lean_is_exclusive(v___x_3933_);
if (v_isSharedCheck_3945_ == 0)
{
v___x_3940_ = v___x_3933_;
v_isShared_3941_ = v_isSharedCheck_3945_;
goto v_resetjp_3939_;
}
else
{
lean_inc(v_a_3938_);
lean_dec(v___x_3933_);
v___x_3940_ = lean_box(0);
v_isShared_3941_ = v_isSharedCheck_3945_;
goto v_resetjp_3939_;
}
v_resetjp_3939_:
{
lean_object* v___x_3943_; 
if (v_isShared_3941_ == 0)
{
v___x_3943_ = v___x_3940_;
goto v_reusejp_3942_;
}
else
{
lean_object* v_reuseFailAlloc_3944_; 
v_reuseFailAlloc_3944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3944_, 0, v_a_3938_);
v___x_3943_ = v_reuseFailAlloc_3944_;
goto v_reusejp_3942_;
}
v_reusejp_3942_:
{
return v___x_3943_;
}
}
}
}
else
{
lean_object* v_a_3946_; lean_object* v___x_3948_; uint8_t v_isShared_3949_; uint8_t v_isSharedCheck_3953_; 
lean_dec_ref(v_docCtx_3911_);
lean_dec_ref(v_names_3910_);
v_a_3946_ = lean_ctor_get(v___x_3925_, 0);
v_isSharedCheck_3953_ = !lean_is_exclusive(v___x_3925_);
if (v_isSharedCheck_3953_ == 0)
{
v___x_3948_ = v___x_3925_;
v_isShared_3949_ = v_isSharedCheck_3953_;
goto v_resetjp_3947_;
}
else
{
lean_inc(v_a_3946_);
lean_dec(v___x_3925_);
v___x_3948_ = lean_box(0);
v_isShared_3949_ = v_isSharedCheck_3953_;
goto v_resetjp_3947_;
}
v_resetjp_3947_:
{
lean_object* v___x_3951_; 
if (v_isShared_3949_ == 0)
{
v___x_3951_ = v___x_3948_;
goto v_reusejp_3950_;
}
else
{
lean_object* v_reuseFailAlloc_3952_; 
v_reuseFailAlloc_3952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3952_, 0, v_a_3946_);
v___x_3951_ = v_reuseFailAlloc_3952_;
goto v_reusejp_3950_;
}
v_reusejp_3950_:
{
return v___x_3951_;
}
}
}
}
else
{
lean_object* v___x_3954_; 
lean_dec_ref(v_docCtx_3911_);
lean_dec_ref(v_names_3910_);
v___x_3954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3954_, 0, v_b_3915_);
return v___x_3954_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4___boxed(lean_object* v_names_3955_, lean_object* v_docCtx_3956_, lean_object* v_as_3957_, lean_object* v_i_3958_, lean_object* v_stop_3959_, lean_object* v_b_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_){
_start:
{
size_t v_i_boxed_3968_; size_t v_stop_boxed_3969_; lean_object* v_res_3970_; 
v_i_boxed_3968_ = lean_unbox_usize(v_i_3958_);
lean_dec(v_i_3958_);
v_stop_boxed_3969_ = lean_unbox_usize(v_stop_3959_);
lean_dec(v_stop_3959_);
v_res_3970_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4(v_names_3955_, v_docCtx_3956_, v_as_3957_, v_i_boxed_3968_, v_stop_boxed_3969_, v_b_3960_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_);
lean_dec(v___y_3966_);
lean_dec_ref(v___y_3965_);
lean_dec(v___y_3964_);
lean_dec_ref(v___y_3963_);
lean_dec(v___y_3962_);
lean_dec_ref(v___y_3961_);
lean_dec_ref(v_as_3957_);
return v_res_3970_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__1(lean_object* v_docCtx_3971_, lean_object* v_a_3972_, lean_object* v_snd_3973_, lean_object* v_as_3974_, size_t v_sz_3975_, size_t v_i_3976_, lean_object* v_b_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_){
_start:
{
uint8_t v___x_3985_; 
v___x_3985_ = lean_usize_dec_lt(v_i_3976_, v_sz_3975_);
if (v___x_3985_ == 0)
{
lean_object* v___x_3986_; 
lean_dec_ref(v_snd_3973_);
lean_dec_ref(v_a_3972_);
lean_dec_ref(v_docCtx_3971_);
v___x_3986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3986_, 0, v_b_3977_);
return v___x_3986_;
}
else
{
lean_object* v_array_3987_; lean_object* v_start_3988_; lean_object* v_stop_3989_; uint8_t v___x_3990_; 
v_array_3987_ = lean_ctor_get(v_b_3977_, 0);
v_start_3988_ = lean_ctor_get(v_b_3977_, 1);
v_stop_3989_ = lean_ctor_get(v_b_3977_, 2);
v___x_3990_ = lean_nat_dec_lt(v_start_3988_, v_stop_3989_);
if (v___x_3990_ == 0)
{
lean_object* v___x_3991_; 
lean_dec_ref(v_snd_3973_);
lean_dec_ref(v_a_3972_);
lean_dec_ref(v_docCtx_3971_);
v___x_3991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3991_, 0, v_b_3977_);
return v___x_3991_;
}
else
{
lean_object* v___x_3993_; uint8_t v_isShared_3994_; uint8_t v_isSharedCheck_4058_; 
lean_inc(v_stop_3989_);
lean_inc(v_start_3988_);
lean_inc_ref(v_array_3987_);
v_isSharedCheck_4058_ = !lean_is_exclusive(v_b_3977_);
if (v_isSharedCheck_4058_ == 0)
{
lean_object* v_unused_4059_; lean_object* v_unused_4060_; lean_object* v_unused_4061_; 
v_unused_4059_ = lean_ctor_get(v_b_3977_, 2);
lean_dec(v_unused_4059_);
v_unused_4060_ = lean_ctor_get(v_b_3977_, 1);
lean_dec(v_unused_4060_);
v_unused_4061_ = lean_ctor_get(v_b_3977_, 0);
lean_dec(v_unused_4061_);
v___x_3993_ = v_b_3977_;
v_isShared_3994_ = v_isSharedCheck_4058_;
goto v_resetjp_3992_;
}
else
{
lean_dec(v_b_3977_);
v___x_3993_ = lean_box(0);
v_isShared_3994_ = v_isSharedCheck_4058_;
goto v_resetjp_3992_;
}
v_resetjp_3992_:
{
lean_object* v_a_3995_; uint8_t v_kind_3996_; lean_object* v_type_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4002_; 
v_a_3995_ = lean_array_uget_borrowed(v_as_3974_, v_i_3976_);
v_kind_3996_ = lean_ctor_get_uint8(v_a_3995_, sizeof(void*)*9);
v_type_3997_ = lean_ctor_get(v_a_3995_, 6);
v___x_3998_ = lean_array_fget(v_array_3987_, v_start_3988_);
v___x_3999_ = lean_unsigned_to_nat(1u);
v___x_4000_ = lean_nat_add(v_start_3988_, v___x_3999_);
lean_dec(v_start_3988_);
if (v_isShared_3994_ == 0)
{
lean_ctor_set(v___x_3993_, 1, v___x_4000_);
v___x_4002_ = v___x_3993_;
goto v_reusejp_4001_;
}
else
{
lean_object* v_reuseFailAlloc_4057_; 
v_reuseFailAlloc_4057_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4057_, 0, v_array_3987_);
lean_ctor_set(v_reuseFailAlloc_4057_, 1, v___x_4000_);
lean_ctor_set(v_reuseFailAlloc_4057_, 2, v_stop_3989_);
v___x_4002_ = v_reuseFailAlloc_4057_;
goto v_reusejp_4001_;
}
v_reusejp_4001_:
{
lean_object* v_preDef_4004_; lean_object* v___y_4005_; lean_object* v___y_4006_; lean_object* v___y_4007_; lean_object* v___y_4008_; lean_object* v___y_4009_; lean_object* v___y_4010_; uint8_t v___x_4023_; 
v___x_4023_ = l_Lean_Elab_DefKind_isTheorem(v_kind_3996_);
if (v___x_4023_ == 0)
{
lean_object* v___x_4024_; 
lean_inc_ref(v_type_3997_);
v___x_4024_ = l_Lean_Meta_isProp(v_type_3997_, v___y_3980_, v___y_3981_, v___y_3982_, v___y_3983_);
if (lean_obj_tag(v___x_4024_) == 0)
{
lean_object* v_a_4025_; uint8_t v___x_4026_; 
v_a_4025_ = lean_ctor_get(v___x_4024_, 0);
lean_inc(v_a_4025_);
lean_dec_ref(v___x_4024_);
v___x_4026_ = lean_unbox(v_a_4025_);
lean_dec(v_a_4025_);
if (v___x_4026_ == 0)
{
lean_object* v___x_4027_; 
lean_inc(v_a_3995_);
v___x_4027_ = l_Lean_Elab_abstractNestedProofs(v_a_3995_, v___x_3990_, v___y_3980_, v___y_3981_, v___y_3982_, v___y_3983_);
if (lean_obj_tag(v___x_4027_) == 0)
{
lean_object* v_a_4028_; size_t v_sz_4029_; size_t v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; 
v_a_4028_ = lean_ctor_get(v___x_4027_, 0);
lean_inc_n(v_a_4028_, 2);
lean_dec_ref(v___x_4027_);
v_sz_4029_ = lean_array_size(v_a_3972_);
v___x_4030_ = ((size_t)0ULL);
lean_inc_ref(v_a_3972_);
v___x_4031_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0(v_sz_4029_, v___x_4030_, v_a_3972_);
lean_inc_ref(v_snd_3973_);
lean_inc(v___x_3998_);
v___x_4032_ = l_Lean_Elab_Structural_registerEqnsInfo(v_a_4028_, v___x_4031_, v___x_3998_, v_snd_3973_, v___y_3982_, v___y_3983_);
if (lean_obj_tag(v___x_4032_) == 0)
{
lean_dec_ref(v___x_4032_);
v_preDef_4004_ = v_a_4028_;
v___y_4005_ = v___y_3978_;
v___y_4006_ = v___y_3979_;
v___y_4007_ = v___y_3980_;
v___y_4008_ = v___y_3981_;
v___y_4009_ = v___y_3982_;
v___y_4010_ = v___y_3983_;
goto v___jp_4003_;
}
else
{
lean_object* v_a_4033_; lean_object* v___x_4035_; uint8_t v_isShared_4036_; uint8_t v_isSharedCheck_4040_; 
lean_dec(v_a_4028_);
lean_dec_ref(v___x_4002_);
lean_dec(v___x_3998_);
lean_dec_ref(v_snd_3973_);
lean_dec_ref(v_a_3972_);
lean_dec_ref(v_docCtx_3971_);
v_a_4033_ = lean_ctor_get(v___x_4032_, 0);
v_isSharedCheck_4040_ = !lean_is_exclusive(v___x_4032_);
if (v_isSharedCheck_4040_ == 0)
{
v___x_4035_ = v___x_4032_;
v_isShared_4036_ = v_isSharedCheck_4040_;
goto v_resetjp_4034_;
}
else
{
lean_inc(v_a_4033_);
lean_dec(v___x_4032_);
v___x_4035_ = lean_box(0);
v_isShared_4036_ = v_isSharedCheck_4040_;
goto v_resetjp_4034_;
}
v_resetjp_4034_:
{
lean_object* v___x_4038_; 
if (v_isShared_4036_ == 0)
{
v___x_4038_ = v___x_4035_;
goto v_reusejp_4037_;
}
else
{
lean_object* v_reuseFailAlloc_4039_; 
v_reuseFailAlloc_4039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4039_, 0, v_a_4033_);
v___x_4038_ = v_reuseFailAlloc_4039_;
goto v_reusejp_4037_;
}
v_reusejp_4037_:
{
return v___x_4038_;
}
}
}
}
else
{
lean_object* v_a_4041_; lean_object* v___x_4043_; uint8_t v_isShared_4044_; uint8_t v_isSharedCheck_4048_; 
lean_dec_ref(v___x_4002_);
lean_dec(v___x_3998_);
lean_dec_ref(v_snd_3973_);
lean_dec_ref(v_a_3972_);
lean_dec_ref(v_docCtx_3971_);
v_a_4041_ = lean_ctor_get(v___x_4027_, 0);
v_isSharedCheck_4048_ = !lean_is_exclusive(v___x_4027_);
if (v_isSharedCheck_4048_ == 0)
{
v___x_4043_ = v___x_4027_;
v_isShared_4044_ = v_isSharedCheck_4048_;
goto v_resetjp_4042_;
}
else
{
lean_inc(v_a_4041_);
lean_dec(v___x_4027_);
v___x_4043_ = lean_box(0);
v_isShared_4044_ = v_isSharedCheck_4048_;
goto v_resetjp_4042_;
}
v_resetjp_4042_:
{
lean_object* v___x_4046_; 
if (v_isShared_4044_ == 0)
{
v___x_4046_ = v___x_4043_;
goto v_reusejp_4045_;
}
else
{
lean_object* v_reuseFailAlloc_4047_; 
v_reuseFailAlloc_4047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4047_, 0, v_a_4041_);
v___x_4046_ = v_reuseFailAlloc_4047_;
goto v_reusejp_4045_;
}
v_reusejp_4045_:
{
return v___x_4046_;
}
}
}
}
else
{
lean_inc(v_a_3995_);
v_preDef_4004_ = v_a_3995_;
v___y_4005_ = v___y_3978_;
v___y_4006_ = v___y_3979_;
v___y_4007_ = v___y_3980_;
v___y_4008_ = v___y_3981_;
v___y_4009_ = v___y_3982_;
v___y_4010_ = v___y_3983_;
goto v___jp_4003_;
}
}
else
{
lean_object* v_a_4049_; lean_object* v___x_4051_; uint8_t v_isShared_4052_; uint8_t v_isSharedCheck_4056_; 
lean_dec_ref(v___x_4002_);
lean_dec(v___x_3998_);
lean_dec_ref(v_snd_3973_);
lean_dec_ref(v_a_3972_);
lean_dec_ref(v_docCtx_3971_);
v_a_4049_ = lean_ctor_get(v___x_4024_, 0);
v_isSharedCheck_4056_ = !lean_is_exclusive(v___x_4024_);
if (v_isSharedCheck_4056_ == 0)
{
v___x_4051_ = v___x_4024_;
v_isShared_4052_ = v_isSharedCheck_4056_;
goto v_resetjp_4050_;
}
else
{
lean_inc(v_a_4049_);
lean_dec(v___x_4024_);
v___x_4051_ = lean_box(0);
v_isShared_4052_ = v_isSharedCheck_4056_;
goto v_resetjp_4050_;
}
v_resetjp_4050_:
{
lean_object* v___x_4054_; 
if (v_isShared_4052_ == 0)
{
v___x_4054_ = v___x_4051_;
goto v_reusejp_4053_;
}
else
{
lean_object* v_reuseFailAlloc_4055_; 
v_reuseFailAlloc_4055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4055_, 0, v_a_4049_);
v___x_4054_ = v_reuseFailAlloc_4055_;
goto v_reusejp_4053_;
}
v_reusejp_4053_:
{
return v___x_4054_;
}
}
}
}
else
{
lean_inc(v_a_3995_);
v_preDef_4004_ = v_a_3995_;
v___y_4005_ = v___y_3978_;
v___y_4006_ = v___y_3979_;
v___y_4007_ = v___y_3980_;
v___y_4008_ = v___y_3981_;
v___y_4009_ = v___y_3982_;
v___y_4010_ = v___y_3983_;
goto v___jp_4003_;
}
v___jp_4003_:
{
lean_object* v___x_4011_; 
lean_inc_ref(v_docCtx_3971_);
v___x_4011_ = l_Lean_Elab_Structural_addSmartUnfoldingDef(v_docCtx_3971_, v_preDef_4004_, v___x_3998_, v___y_4005_, v___y_4006_, v___y_4007_, v___y_4008_, v___y_4009_, v___y_4010_);
if (lean_obj_tag(v___x_4011_) == 0)
{
size_t v___x_4012_; size_t v___x_4013_; 
lean_dec_ref(v___x_4011_);
v___x_4012_ = ((size_t)1ULL);
v___x_4013_ = lean_usize_add(v_i_3976_, v___x_4012_);
v_i_3976_ = v___x_4013_;
v_b_3977_ = v___x_4002_;
goto _start;
}
else
{
lean_object* v_a_4015_; lean_object* v___x_4017_; uint8_t v_isShared_4018_; uint8_t v_isSharedCheck_4022_; 
lean_dec_ref(v___x_4002_);
lean_dec_ref(v_snd_3973_);
lean_dec_ref(v_a_3972_);
lean_dec_ref(v_docCtx_3971_);
v_a_4015_ = lean_ctor_get(v___x_4011_, 0);
v_isSharedCheck_4022_ = !lean_is_exclusive(v___x_4011_);
if (v_isSharedCheck_4022_ == 0)
{
v___x_4017_ = v___x_4011_;
v_isShared_4018_ = v_isSharedCheck_4022_;
goto v_resetjp_4016_;
}
else
{
lean_inc(v_a_4015_);
lean_dec(v___x_4011_);
v___x_4017_ = lean_box(0);
v_isShared_4018_ = v_isSharedCheck_4022_;
goto v_resetjp_4016_;
}
v_resetjp_4016_:
{
lean_object* v___x_4020_; 
if (v_isShared_4018_ == 0)
{
v___x_4020_ = v___x_4017_;
goto v_reusejp_4019_;
}
else
{
lean_object* v_reuseFailAlloc_4021_; 
v_reuseFailAlloc_4021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4021_, 0, v_a_4015_);
v___x_4020_ = v_reuseFailAlloc_4021_;
goto v_reusejp_4019_;
}
v_reusejp_4019_:
{
return v___x_4020_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__1___boxed(lean_object* v_docCtx_4062_, lean_object* v_a_4063_, lean_object* v_snd_4064_, lean_object* v_as_4065_, lean_object* v_sz_4066_, lean_object* v_i_4067_, lean_object* v_b_4068_, lean_object* v___y_4069_, lean_object* v___y_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_){
_start:
{
size_t v_sz_boxed_4076_; size_t v_i_boxed_4077_; lean_object* v_res_4078_; 
v_sz_boxed_4076_ = lean_unbox_usize(v_sz_4066_);
lean_dec(v_sz_4066_);
v_i_boxed_4077_ = lean_unbox_usize(v_i_4067_);
lean_dec(v_i_4067_);
v_res_4078_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__1(v_docCtx_4062_, v_a_4063_, v_snd_4064_, v_as_4065_, v_sz_boxed_4076_, v_i_boxed_4077_, v_b_4068_, v___y_4069_, v___y_4070_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_);
lean_dec(v___y_4074_);
lean_dec_ref(v___y_4073_);
lean_dec(v___y_4072_);
lean_dec_ref(v___y_4071_);
lean_dec(v___y_4070_);
lean_dec_ref(v___y_4069_);
lean_dec_ref(v_as_4065_);
return v_res_4078_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___redArg(size_t v_sz_4079_, size_t v_i_4080_, lean_object* v_bs_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_){
_start:
{
uint8_t v___x_4085_; 
v___x_4085_ = lean_usize_dec_lt(v_i_4080_, v_sz_4079_);
if (v___x_4085_ == 0)
{
lean_object* v___x_4086_; 
v___x_4086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4086_, 0, v_bs_4081_);
return v___x_4086_;
}
else
{
lean_object* v_v_4087_; lean_object* v___x_4088_; 
v_v_4087_ = lean_array_uget_borrowed(v_bs_4081_, v_i_4080_);
lean_inc(v_v_4087_);
v___x_4088_ = l_Lean_Elab_eraseRecAppSyntax(v_v_4087_, v___y_4082_, v___y_4083_);
if (lean_obj_tag(v___x_4088_) == 0)
{
lean_object* v_a_4089_; lean_object* v___x_4090_; lean_object* v_bs_x27_4091_; size_t v___x_4092_; size_t v___x_4093_; lean_object* v___x_4094_; 
v_a_4089_ = lean_ctor_get(v___x_4088_, 0);
lean_inc(v_a_4089_);
lean_dec_ref(v___x_4088_);
v___x_4090_ = lean_unsigned_to_nat(0u);
v_bs_x27_4091_ = lean_array_uset(v_bs_4081_, v_i_4080_, v___x_4090_);
v___x_4092_ = ((size_t)1ULL);
v___x_4093_ = lean_usize_add(v_i_4080_, v___x_4092_);
v___x_4094_ = lean_array_uset(v_bs_x27_4091_, v_i_4080_, v_a_4089_);
v_i_4080_ = v___x_4093_;
v_bs_4081_ = v___x_4094_;
goto _start;
}
else
{
lean_object* v_a_4096_; lean_object* v___x_4098_; uint8_t v_isShared_4099_; uint8_t v_isSharedCheck_4103_; 
lean_dec_ref(v_bs_4081_);
v_a_4096_ = lean_ctor_get(v___x_4088_, 0);
v_isSharedCheck_4103_ = !lean_is_exclusive(v___x_4088_);
if (v_isSharedCheck_4103_ == 0)
{
v___x_4098_ = v___x_4088_;
v_isShared_4099_ = v_isSharedCheck_4103_;
goto v_resetjp_4097_;
}
else
{
lean_inc(v_a_4096_);
lean_dec(v___x_4088_);
v___x_4098_ = lean_box(0);
v_isShared_4099_ = v_isSharedCheck_4103_;
goto v_resetjp_4097_;
}
v_resetjp_4097_:
{
lean_object* v___x_4101_; 
if (v_isShared_4099_ == 0)
{
v___x_4101_ = v___x_4098_;
goto v_reusejp_4100_;
}
else
{
lean_object* v_reuseFailAlloc_4102_; 
v_reuseFailAlloc_4102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4102_, 0, v_a_4096_);
v___x_4101_ = v_reuseFailAlloc_4102_;
goto v_reusejp_4100_;
}
v_reusejp_4100_:
{
return v___x_4101_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___redArg___boxed(lean_object* v_sz_4104_, lean_object* v_i_4105_, lean_object* v_bs_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_){
_start:
{
size_t v_sz_boxed_4110_; size_t v_i_boxed_4111_; lean_object* v_res_4112_; 
v_sz_boxed_4110_ = lean_unbox_usize(v_sz_4104_);
lean_dec(v_sz_4104_);
v_i_boxed_4111_ = lean_unbox_usize(v_i_4105_);
lean_dec(v_i_4105_);
v_res_4112_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___redArg(v_sz_boxed_4110_, v_i_boxed_4111_, v_bs_4106_, v___y_4107_, v___y_4108_);
lean_dec(v___y_4108_);
lean_dec_ref(v___y_4107_);
return v_res_4112_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___redArg(lean_object* v_as_4113_, size_t v_sz_4114_, size_t v_i_4115_, lean_object* v_b_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_){
_start:
{
uint8_t v___x_4122_; 
v___x_4122_ = lean_usize_dec_lt(v_i_4115_, v_sz_4114_);
if (v___x_4122_ == 0)
{
lean_object* v___x_4123_; 
v___x_4123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4123_, 0, v_b_4116_);
return v___x_4123_;
}
else
{
lean_object* v_array_4124_; lean_object* v_start_4125_; lean_object* v_stop_4126_; uint8_t v___x_4127_; 
v_array_4124_ = lean_ctor_get(v_b_4116_, 0);
v_start_4125_ = lean_ctor_get(v_b_4116_, 1);
v_stop_4126_ = lean_ctor_get(v_b_4116_, 2);
v___x_4127_ = lean_nat_dec_lt(v_start_4125_, v_stop_4126_);
if (v___x_4127_ == 0)
{
lean_object* v___x_4128_; 
v___x_4128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4128_, 0, v_b_4116_);
return v___x_4128_;
}
else
{
lean_object* v___x_4130_; uint8_t v_isShared_4131_; uint8_t v_isSharedCheck_4151_; 
lean_inc(v_stop_4126_);
lean_inc(v_start_4125_);
lean_inc_ref(v_array_4124_);
v_isSharedCheck_4151_ = !lean_is_exclusive(v_b_4116_);
if (v_isSharedCheck_4151_ == 0)
{
lean_object* v_unused_4152_; lean_object* v_unused_4153_; lean_object* v_unused_4154_; 
v_unused_4152_ = lean_ctor_get(v_b_4116_, 2);
lean_dec(v_unused_4152_);
v_unused_4153_ = lean_ctor_get(v_b_4116_, 1);
lean_dec(v_unused_4153_);
v_unused_4154_ = lean_ctor_get(v_b_4116_, 0);
lean_dec(v_unused_4154_);
v___x_4130_ = v_b_4116_;
v_isShared_4131_ = v_isSharedCheck_4151_;
goto v_resetjp_4129_;
}
else
{
lean_dec(v_b_4116_);
v___x_4130_ = lean_box(0);
v_isShared_4131_ = v_isSharedCheck_4151_;
goto v_resetjp_4129_;
}
v_resetjp_4129_:
{
lean_object* v_a_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; 
v_a_4132_ = lean_array_uget_borrowed(v_as_4113_, v_i_4115_);
v___x_4133_ = lean_array_fget_borrowed(v_array_4124_, v_start_4125_);
lean_inc(v_a_4132_);
lean_inc(v___x_4133_);
v___x_4134_ = l_Lean_Elab_Structural_reportTermMeasure(v___x_4133_, v_a_4132_, v___y_4117_, v___y_4118_, v___y_4119_, v___y_4120_);
if (lean_obj_tag(v___x_4134_) == 0)
{
lean_object* v___x_4135_; lean_object* v___x_4136_; lean_object* v___x_4138_; 
lean_dec_ref(v___x_4134_);
v___x_4135_ = lean_unsigned_to_nat(1u);
v___x_4136_ = lean_nat_add(v_start_4125_, v___x_4135_);
lean_dec(v_start_4125_);
if (v_isShared_4131_ == 0)
{
lean_ctor_set(v___x_4130_, 1, v___x_4136_);
v___x_4138_ = v___x_4130_;
goto v_reusejp_4137_;
}
else
{
lean_object* v_reuseFailAlloc_4142_; 
v_reuseFailAlloc_4142_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4142_, 0, v_array_4124_);
lean_ctor_set(v_reuseFailAlloc_4142_, 1, v___x_4136_);
lean_ctor_set(v_reuseFailAlloc_4142_, 2, v_stop_4126_);
v___x_4138_ = v_reuseFailAlloc_4142_;
goto v_reusejp_4137_;
}
v_reusejp_4137_:
{
size_t v___x_4139_; size_t v___x_4140_; 
v___x_4139_ = ((size_t)1ULL);
v___x_4140_ = lean_usize_add(v_i_4115_, v___x_4139_);
v_i_4115_ = v___x_4140_;
v_b_4116_ = v___x_4138_;
goto _start;
}
}
else
{
lean_object* v_a_4143_; lean_object* v___x_4145_; uint8_t v_isShared_4146_; uint8_t v_isSharedCheck_4150_; 
lean_del_object(v___x_4130_);
lean_dec(v_stop_4126_);
lean_dec(v_start_4125_);
lean_dec_ref(v_array_4124_);
v_a_4143_ = lean_ctor_get(v___x_4134_, 0);
v_isSharedCheck_4150_ = !lean_is_exclusive(v___x_4134_);
if (v_isSharedCheck_4150_ == 0)
{
v___x_4145_ = v___x_4134_;
v_isShared_4146_ = v_isSharedCheck_4150_;
goto v_resetjp_4144_;
}
else
{
lean_inc(v_a_4143_);
lean_dec(v___x_4134_);
v___x_4145_ = lean_box(0);
v_isShared_4146_ = v_isSharedCheck_4150_;
goto v_resetjp_4144_;
}
v_resetjp_4144_:
{
lean_object* v___x_4148_; 
if (v_isShared_4146_ == 0)
{
v___x_4148_ = v___x_4145_;
goto v_reusejp_4147_;
}
else
{
lean_object* v_reuseFailAlloc_4149_; 
v_reuseFailAlloc_4149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4149_, 0, v_a_4143_);
v___x_4148_ = v_reuseFailAlloc_4149_;
goto v_reusejp_4147_;
}
v_reusejp_4147_:
{
return v___x_4148_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___redArg___boxed(lean_object* v_as_4155_, lean_object* v_sz_4156_, lean_object* v_i_4157_, lean_object* v_b_4158_, lean_object* v___y_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_, lean_object* v___y_4162_, lean_object* v___y_4163_){
_start:
{
size_t v_sz_boxed_4164_; size_t v_i_boxed_4165_; lean_object* v_res_4166_; 
v_sz_boxed_4164_ = lean_unbox_usize(v_sz_4156_);
lean_dec(v_sz_4156_);
v_i_boxed_4165_ = lean_unbox_usize(v_i_4157_);
lean_dec(v_i_4157_);
v_res_4166_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___redArg(v_as_4155_, v_sz_boxed_4164_, v_i_boxed_4165_, v_b_4158_, v___y_4159_, v___y_4160_, v___y_4161_, v___y_4162_);
lean_dec(v___y_4162_);
lean_dec_ref(v___y_4161_);
lean_dec(v___y_4160_);
lean_dec_ref(v___y_4159_);
lean_dec_ref(v_as_4155_);
return v_res_4166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_structuralRecursion(lean_object* v_docCtx_4167_, lean_object* v_preDefs_4168_, lean_object* v_termMeasure_x3fs_4169_, lean_object* v_a_4170_, lean_object* v_a_4171_, lean_object* v_a_4172_, lean_object* v_a_4173_, lean_object* v_a_4174_, lean_object* v_a_4175_){
_start:
{
size_t v_sz_4177_; size_t v___x_4178_; lean_object* v_names_4179_; lean_object* v___x_4180_; 
v_sz_4177_ = lean_array_size(v_preDefs_4168_);
v___x_4178_ = ((size_t)0ULL);
lean_inc_ref_n(v_preDefs_4168_, 2);
v_names_4179_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0(v_sz_4177_, v___x_4178_, v_preDefs_4168_);
v___x_4180_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos(v_preDefs_4168_, v_termMeasure_x3fs_4169_, v_a_4172_, v_a_4173_, v_a_4174_, v_a_4175_);
if (lean_obj_tag(v___x_4180_) == 0)
{
lean_object* v_a_4181_; lean_object* v_snd_4182_; lean_object* v_fst_4183_; lean_object* v_fst_4184_; lean_object* v_snd_4185_; lean_object* v___y_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; size_t v_sz_4220_; lean_object* v___x_4221_; 
v_a_4181_ = lean_ctor_get(v___x_4180_, 0);
lean_inc(v_a_4181_);
lean_dec_ref(v___x_4180_);
v_snd_4182_ = lean_ctor_get(v_a_4181_, 1);
lean_inc(v_snd_4182_);
v_fst_4183_ = lean_ctor_get(v_a_4181_, 0);
lean_inc(v_fst_4183_);
lean_dec(v_a_4181_);
v_fst_4184_ = lean_ctor_get(v_snd_4182_, 0);
lean_inc(v_fst_4184_);
v_snd_4185_ = lean_ctor_get(v_snd_4182_, 1);
lean_inc(v_snd_4185_);
lean_dec(v_snd_4182_);
v___x_4217_ = lean_unsigned_to_nat(0u);
v___x_4218_ = lean_array_get_size(v_preDefs_4168_);
lean_inc_ref(v_preDefs_4168_);
v___x_4219_ = l_Array_toSubarray___redArg(v_preDefs_4168_, v___x_4217_, v___x_4218_);
v_sz_4220_ = lean_array_size(v_fst_4183_);
v___x_4221_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___redArg(v_fst_4183_, v_sz_4220_, v___x_4178_, v___x_4219_, v_a_4172_, v_a_4173_, v_a_4174_, v_a_4175_);
if (lean_obj_tag(v___x_4221_) == 0)
{
lean_object* v___x_4222_; uint8_t v___x_4223_; 
lean_dec_ref(v___x_4221_);
v___x_4222_ = lean_array_get_size(v_fst_4184_);
v___x_4223_ = lean_nat_dec_lt(v___x_4217_, v___x_4222_);
if (v___x_4223_ == 0)
{
lean_dec_ref(v_names_4179_);
goto v___jp_4186_;
}
else
{
lean_object* v___x_4224_; uint8_t v___x_4225_; 
v___x_4224_ = lean_box(0);
v___x_4225_ = lean_nat_dec_le(v___x_4222_, v___x_4222_);
if (v___x_4225_ == 0)
{
if (v___x_4223_ == 0)
{
lean_dec_ref(v_names_4179_);
goto v___jp_4186_;
}
else
{
size_t v___x_4226_; lean_object* v___x_4227_; 
v___x_4226_ = lean_usize_of_nat(v___x_4222_);
lean_inc_ref(v_docCtx_4167_);
v___x_4227_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4(v_names_4179_, v_docCtx_4167_, v_fst_4184_, v___x_4178_, v___x_4226_, v___x_4224_, v_a_4170_, v_a_4171_, v_a_4172_, v_a_4173_, v_a_4174_, v_a_4175_);
v___y_4216_ = v___x_4227_;
goto v___jp_4215_;
}
}
else
{
size_t v___x_4228_; lean_object* v___x_4229_; 
v___x_4228_ = lean_usize_of_nat(v___x_4222_);
lean_inc_ref(v_docCtx_4167_);
v___x_4229_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4(v_names_4179_, v_docCtx_4167_, v_fst_4184_, v___x_4178_, v___x_4228_, v___x_4224_, v_a_4170_, v_a_4171_, v_a_4172_, v_a_4173_, v_a_4174_, v_a_4175_);
v___y_4216_ = v___x_4229_;
goto v___jp_4215_;
}
}
}
else
{
lean_object* v_a_4230_; lean_object* v___x_4232_; uint8_t v_isShared_4233_; uint8_t v_isSharedCheck_4237_; 
lean_dec(v_snd_4185_);
lean_dec(v_fst_4184_);
lean_dec(v_fst_4183_);
lean_dec_ref(v_names_4179_);
lean_dec_ref(v_preDefs_4168_);
lean_dec_ref(v_docCtx_4167_);
v_a_4230_ = lean_ctor_get(v___x_4221_, 0);
v_isSharedCheck_4237_ = !lean_is_exclusive(v___x_4221_);
if (v_isSharedCheck_4237_ == 0)
{
v___x_4232_ = v___x_4221_;
v_isShared_4233_ = v_isSharedCheck_4237_;
goto v_resetjp_4231_;
}
else
{
lean_inc(v_a_4230_);
lean_dec(v___x_4221_);
v___x_4232_ = lean_box(0);
v_isShared_4233_ = v_isSharedCheck_4237_;
goto v_resetjp_4231_;
}
v_resetjp_4231_:
{
lean_object* v___x_4235_; 
if (v_isShared_4233_ == 0)
{
v___x_4235_ = v___x_4232_;
goto v_reusejp_4234_;
}
else
{
lean_object* v_reuseFailAlloc_4236_; 
v_reuseFailAlloc_4236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4236_, 0, v_a_4230_);
v___x_4235_ = v_reuseFailAlloc_4236_;
goto v_reusejp_4234_;
}
v_reusejp_4234_:
{
return v___x_4235_;
}
}
}
v___jp_4186_:
{
lean_object* v___x_4187_; 
v___x_4187_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___redArg(v_sz_4177_, v___x_4178_, v_preDefs_4168_, v_a_4174_, v_a_4175_);
if (lean_obj_tag(v___x_4187_) == 0)
{
lean_object* v_a_4188_; lean_object* v___x_4189_; 
v_a_4188_ = lean_ctor_get(v___x_4187_, 0);
lean_inc_n(v_a_4188_, 2);
lean_dec_ref(v___x_4187_);
lean_inc_ref(v_docCtx_4167_);
v___x_4189_ = l_Lean_Elab_addAndCompilePartialRec(v_docCtx_4167_, v_a_4188_, v_a_4170_, v_a_4171_, v_a_4172_, v_a_4173_, v_a_4174_, v_a_4175_);
if (lean_obj_tag(v___x_4189_) == 0)
{
lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; size_t v_sz_4193_; lean_object* v___x_4194_; 
lean_dec_ref(v___x_4189_);
v___x_4190_ = lean_unsigned_to_nat(0u);
v___x_4191_ = lean_array_get_size(v_fst_4183_);
v___x_4192_ = l_Array_toSubarray___redArg(v_fst_4183_, v___x_4190_, v___x_4191_);
v_sz_4193_ = lean_array_size(v_a_4188_);
lean_inc(v_a_4188_);
v___x_4194_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__1(v_docCtx_4167_, v_a_4188_, v_snd_4185_, v_a_4188_, v_sz_4193_, v___x_4178_, v___x_4192_, v_a_4170_, v_a_4171_, v_a_4172_, v_a_4173_, v_a_4174_, v_a_4175_);
if (lean_obj_tag(v___x_4194_) == 0)
{
lean_object* v___x_4195_; lean_object* v___x_4196_; 
lean_dec_ref(v___x_4194_);
v___x_4195_ = lean_box(0);
v___x_4196_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___redArg(v_a_4188_, v_sz_4193_, v___x_4178_, v___x_4195_, v_a_4172_, v_a_4173_, v_a_4174_, v_a_4175_);
lean_dec(v_a_4188_);
if (lean_obj_tag(v___x_4196_) == 0)
{
uint8_t v___x_4197_; lean_object* v___x_4198_; 
lean_dec_ref(v___x_4196_);
v___x_4197_ = 1;
v___x_4198_ = l_Lean_Elab_applyAttributesOf(v_fst_4184_, v___x_4197_, v_a_4170_, v_a_4171_, v_a_4172_, v_a_4173_, v_a_4174_, v_a_4175_);
lean_dec(v_fst_4184_);
return v___x_4198_;
}
else
{
lean_dec(v_fst_4184_);
return v___x_4196_;
}
}
else
{
lean_object* v_a_4199_; lean_object* v___x_4201_; uint8_t v_isShared_4202_; uint8_t v_isSharedCheck_4206_; 
lean_dec(v_a_4188_);
lean_dec(v_fst_4184_);
v_a_4199_ = lean_ctor_get(v___x_4194_, 0);
v_isSharedCheck_4206_ = !lean_is_exclusive(v___x_4194_);
if (v_isSharedCheck_4206_ == 0)
{
v___x_4201_ = v___x_4194_;
v_isShared_4202_ = v_isSharedCheck_4206_;
goto v_resetjp_4200_;
}
else
{
lean_inc(v_a_4199_);
lean_dec(v___x_4194_);
v___x_4201_ = lean_box(0);
v_isShared_4202_ = v_isSharedCheck_4206_;
goto v_resetjp_4200_;
}
v_resetjp_4200_:
{
lean_object* v___x_4204_; 
if (v_isShared_4202_ == 0)
{
v___x_4204_ = v___x_4201_;
goto v_reusejp_4203_;
}
else
{
lean_object* v_reuseFailAlloc_4205_; 
v_reuseFailAlloc_4205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4205_, 0, v_a_4199_);
v___x_4204_ = v_reuseFailAlloc_4205_;
goto v_reusejp_4203_;
}
v_reusejp_4203_:
{
return v___x_4204_;
}
}
}
}
else
{
lean_dec(v_a_4188_);
lean_dec(v_snd_4185_);
lean_dec(v_fst_4184_);
lean_dec(v_fst_4183_);
lean_dec_ref(v_docCtx_4167_);
return v___x_4189_;
}
}
else
{
lean_object* v_a_4207_; lean_object* v___x_4209_; uint8_t v_isShared_4210_; uint8_t v_isSharedCheck_4214_; 
lean_dec(v_snd_4185_);
lean_dec(v_fst_4184_);
lean_dec(v_fst_4183_);
lean_dec_ref(v_docCtx_4167_);
v_a_4207_ = lean_ctor_get(v___x_4187_, 0);
v_isSharedCheck_4214_ = !lean_is_exclusive(v___x_4187_);
if (v_isSharedCheck_4214_ == 0)
{
v___x_4209_ = v___x_4187_;
v_isShared_4210_ = v_isSharedCheck_4214_;
goto v_resetjp_4208_;
}
else
{
lean_inc(v_a_4207_);
lean_dec(v___x_4187_);
v___x_4209_ = lean_box(0);
v_isShared_4210_ = v_isSharedCheck_4214_;
goto v_resetjp_4208_;
}
v_resetjp_4208_:
{
lean_object* v___x_4212_; 
if (v_isShared_4210_ == 0)
{
v___x_4212_ = v___x_4209_;
goto v_reusejp_4211_;
}
else
{
lean_object* v_reuseFailAlloc_4213_; 
v_reuseFailAlloc_4213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4213_, 0, v_a_4207_);
v___x_4212_ = v_reuseFailAlloc_4213_;
goto v_reusejp_4211_;
}
v_reusejp_4211_:
{
return v___x_4212_;
}
}
}
}
v___jp_4215_:
{
if (lean_obj_tag(v___y_4216_) == 0)
{
lean_dec_ref(v___y_4216_);
goto v___jp_4186_;
}
else
{
lean_dec(v_snd_4185_);
lean_dec(v_fst_4184_);
lean_dec(v_fst_4183_);
lean_dec_ref(v_preDefs_4168_);
lean_dec_ref(v_docCtx_4167_);
return v___y_4216_;
}
}
}
else
{
lean_object* v_a_4238_; lean_object* v___x_4240_; uint8_t v_isShared_4241_; uint8_t v_isSharedCheck_4245_; 
lean_dec_ref(v_names_4179_);
lean_dec_ref(v_preDefs_4168_);
lean_dec_ref(v_docCtx_4167_);
v_a_4238_ = lean_ctor_get(v___x_4180_, 0);
v_isSharedCheck_4245_ = !lean_is_exclusive(v___x_4180_);
if (v_isSharedCheck_4245_ == 0)
{
v___x_4240_ = v___x_4180_;
v_isShared_4241_ = v_isSharedCheck_4245_;
goto v_resetjp_4239_;
}
else
{
lean_inc(v_a_4238_);
lean_dec(v___x_4180_);
v___x_4240_ = lean_box(0);
v_isShared_4241_ = v_isSharedCheck_4245_;
goto v_resetjp_4239_;
}
v_resetjp_4239_:
{
lean_object* v___x_4243_; 
if (v_isShared_4241_ == 0)
{
v___x_4243_ = v___x_4240_;
goto v_reusejp_4242_;
}
else
{
lean_object* v_reuseFailAlloc_4244_; 
v_reuseFailAlloc_4244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4244_, 0, v_a_4238_);
v___x_4243_ = v_reuseFailAlloc_4244_;
goto v_reusejp_4242_;
}
v_reusejp_4242_:
{
return v___x_4243_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_structuralRecursion___boxed(lean_object* v_docCtx_4246_, lean_object* v_preDefs_4247_, lean_object* v_termMeasure_x3fs_4248_, lean_object* v_a_4249_, lean_object* v_a_4250_, lean_object* v_a_4251_, lean_object* v_a_4252_, lean_object* v_a_4253_, lean_object* v_a_4254_, lean_object* v_a_4255_){
_start:
{
lean_object* v_res_4256_; 
v_res_4256_ = l_Lean_Elab_Structural_structuralRecursion(v_docCtx_4246_, v_preDefs_4247_, v_termMeasure_x3fs_4248_, v_a_4249_, v_a_4250_, v_a_4251_, v_a_4252_, v_a_4253_, v_a_4254_);
lean_dec(v_a_4254_);
lean_dec_ref(v_a_4253_);
lean_dec(v_a_4252_);
lean_dec_ref(v_a_4251_);
lean_dec(v_a_4250_);
lean_dec_ref(v_a_4249_);
return v_res_4256_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0(size_t v_sz_4257_, size_t v_i_4258_, lean_object* v_bs_4259_, lean_object* v___y_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_){
_start:
{
lean_object* v___x_4267_; 
v___x_4267_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___redArg(v_sz_4257_, v_i_4258_, v_bs_4259_, v___y_4264_, v___y_4265_);
return v___x_4267_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___boxed(lean_object* v_sz_4268_, lean_object* v_i_4269_, lean_object* v_bs_4270_, lean_object* v___y_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_, lean_object* v___y_4274_, lean_object* v___y_4275_, lean_object* v___y_4276_, lean_object* v___y_4277_){
_start:
{
size_t v_sz_boxed_4278_; size_t v_i_boxed_4279_; lean_object* v_res_4280_; 
v_sz_boxed_4278_ = lean_unbox_usize(v_sz_4268_);
lean_dec(v_sz_4268_);
v_i_boxed_4279_ = lean_unbox_usize(v_i_4269_);
lean_dec(v_i_4269_);
v_res_4280_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0(v_sz_boxed_4278_, v_i_boxed_4279_, v_bs_4270_, v___y_4271_, v___y_4272_, v___y_4273_, v___y_4274_, v___y_4275_, v___y_4276_);
lean_dec(v___y_4276_);
lean_dec_ref(v___y_4275_);
lean_dec(v___y_4274_);
lean_dec_ref(v___y_4273_);
lean_dec(v___y_4272_);
lean_dec_ref(v___y_4271_);
return v_res_4280_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2(lean_object* v_as_4281_, size_t v_sz_4282_, size_t v_i_4283_, lean_object* v_b_4284_, lean_object* v___y_4285_, lean_object* v___y_4286_, lean_object* v___y_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_){
_start:
{
lean_object* v___x_4292_; 
v___x_4292_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___redArg(v_as_4281_, v_sz_4282_, v_i_4283_, v_b_4284_, v___y_4287_, v___y_4288_, v___y_4289_, v___y_4290_);
return v___x_4292_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___boxed(lean_object* v_as_4293_, lean_object* v_sz_4294_, lean_object* v_i_4295_, lean_object* v_b_4296_, lean_object* v___y_4297_, lean_object* v___y_4298_, lean_object* v___y_4299_, lean_object* v___y_4300_, lean_object* v___y_4301_, lean_object* v___y_4302_, lean_object* v___y_4303_){
_start:
{
size_t v_sz_boxed_4304_; size_t v_i_boxed_4305_; lean_object* v_res_4306_; 
v_sz_boxed_4304_ = lean_unbox_usize(v_sz_4294_);
lean_dec(v_sz_4294_);
v_i_boxed_4305_ = lean_unbox_usize(v_i_4295_);
lean_dec(v_i_4295_);
v_res_4306_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2(v_as_4293_, v_sz_boxed_4304_, v_i_boxed_4305_, v_b_4296_, v___y_4297_, v___y_4298_, v___y_4299_, v___y_4300_, v___y_4301_, v___y_4302_);
lean_dec(v___y_4302_);
lean_dec_ref(v___y_4301_);
lean_dec(v___y_4300_);
lean_dec_ref(v___y_4299_);
lean_dec(v___y_4298_);
lean_dec_ref(v___y_4297_);
lean_dec_ref(v_as_4293_);
return v_res_4306_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3(lean_object* v_as_4307_, size_t v_sz_4308_, size_t v_i_4309_, lean_object* v_b_4310_, lean_object* v___y_4311_, lean_object* v___y_4312_, lean_object* v___y_4313_, lean_object* v___y_4314_, lean_object* v___y_4315_, lean_object* v___y_4316_){
_start:
{
lean_object* v___x_4318_; 
v___x_4318_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___redArg(v_as_4307_, v_sz_4308_, v_i_4309_, v_b_4310_, v___y_4313_, v___y_4314_, v___y_4315_, v___y_4316_);
return v___x_4318_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___boxed(lean_object* v_as_4319_, lean_object* v_sz_4320_, lean_object* v_i_4321_, lean_object* v_b_4322_, lean_object* v___y_4323_, lean_object* v___y_4324_, lean_object* v___y_4325_, lean_object* v___y_4326_, lean_object* v___y_4327_, lean_object* v___y_4328_, lean_object* v___y_4329_){
_start:
{
size_t v_sz_boxed_4330_; size_t v_i_boxed_4331_; lean_object* v_res_4332_; 
v_sz_boxed_4330_ = lean_unbox_usize(v_sz_4320_);
lean_dec(v_sz_4320_);
v_i_boxed_4331_ = lean_unbox_usize(v_i_4321_);
lean_dec(v_i_4321_);
v_res_4332_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3(v_as_4319_, v_sz_boxed_4330_, v_i_boxed_4331_, v_b_4322_, v___y_4323_, v___y_4324_, v___y_4325_, v___y_4326_, v___y_4327_, v___y_4328_);
lean_dec(v___y_4328_);
lean_dec_ref(v___y_4327_);
lean_dec(v___y_4326_);
lean_dec_ref(v___y_4325_);
lean_dec(v___y_4324_);
lean_dec_ref(v___y_4323_);
lean_dec_ref(v_as_4319_);
return v_res_4332_;
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
