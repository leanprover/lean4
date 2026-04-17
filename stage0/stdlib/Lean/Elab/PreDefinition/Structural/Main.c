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
lean_dec_ref(v___x_315_);
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
lean_dec_ref(v___x_315_);
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
uint8_t v_a_27606__boxed_515_; lean_object* v_res_516_; 
v_a_27606__boxed_515_ = lean_unbox(v_a_499_);
v_res_516_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg(v_a_27606__boxed_515_, v_a_500_, v_a_501_, v_recArgInfos_502_, v___x_503_, v_preDefs_504_, v_a_505_, v_as_506_, v_i_507_, v_j_508_, v_bs_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_);
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
lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_23898__overap_816_; lean_object* v___x_817_; 
v___x_814_ = lean_obj_once(&l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__5, &l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__5_once, _init_l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__5);
v___x_815_ = l_instInhabitedOfMonad___redArg(v___x_813_, v___x_814_);
v___x_23898__overap_816_ = lean_panic_fn_borrowed(v___x_815_, v_msg_759_);
lean_dec(v___x_815_);
lean_inc(v___y_763_);
lean_inc_ref(v___y_762_);
lean_inc(v___y_761_);
lean_inc_ref(v___y_760_);
v___x_817_ = lean_apply_5(v___x_23898__overap_816_, v___y_760_, v___y_761_, v___y_762_, v___y_763_, lean_box(0));
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
v___x_1024_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__2);
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
v___x_1036_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__3, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__3);
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
v___x_1155_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__2);
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
v___x_1167_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__3, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__3);
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
uint8_t v_a_28559__boxed_1205_; lean_object* v_res_1206_; 
v_a_28559__boxed_1205_ = lean_unbox(v_a_1193_);
v_res_1206_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg(v_xs_1192_, v_a_28559__boxed_1205_, v_preDefs_1194_, v___x_1195_, v_as_1196_, v_i_1197_, v_j_1198_, v_bs_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_);
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
uint8_t v_a_28813__boxed_1516_; lean_object* v_res_1517_; 
v_a_28813__boxed_1516_ = lean_unbox(v_a_1508_);
v_res_1517_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2(v___f_1497_, v_recArgInfos_1498_, v_a_1499_, v___x_1500_, v___x_1501_, v_fixedParamPerms_1502_, v_xs_1503_, v_preDefs_1504_, v_numIndices_1505_, v___f_1506_, v___x_1507_, v_a_28813__boxed_1516_, v_funTypes_1509_, v_motives_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11___redArg(lean_object* v_hi_1703_, lean_object* v_pivot_1704_, lean_object* v_as_1705_, lean_object* v_i_1706_, lean_object* v_k_1707_){
_start:
{
uint8_t v___x_1708_; 
v___x_1708_ = lean_nat_dec_lt(v_k_1707_, v_hi_1703_);
if (v___x_1708_ == 0)
{
lean_object* v___x_1709_; lean_object* v___x_1710_; 
lean_dec(v_k_1707_);
v___x_1709_ = lean_array_fswap(v_as_1705_, v_i_1706_, v_hi_1703_);
v___x_1710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1710_, 0, v_i_1706_);
lean_ctor_set(v___x_1710_, 1, v___x_1709_);
return v___x_1710_;
}
else
{
lean_object* v___x_1711_; uint8_t v___x_1712_; 
v___x_1711_ = lean_array_fget_borrowed(v_as_1705_, v_k_1707_);
v___x_1712_ = l_Nat_blt(v___x_1711_, v_pivot_1704_);
if (v___x_1712_ == 0)
{
lean_object* v___x_1713_; lean_object* v___x_1714_; 
v___x_1713_ = lean_unsigned_to_nat(1u);
v___x_1714_ = lean_nat_add(v_k_1707_, v___x_1713_);
lean_dec(v_k_1707_);
v_k_1707_ = v___x_1714_;
goto _start;
}
else
{
lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; 
v___x_1716_ = lean_array_fswap(v_as_1705_, v_i_1706_, v_k_1707_);
v___x_1717_ = lean_unsigned_to_nat(1u);
v___x_1718_ = lean_nat_add(v_i_1706_, v___x_1717_);
lean_dec(v_i_1706_);
v___x_1719_ = lean_nat_add(v_k_1707_, v___x_1717_);
lean_dec(v_k_1707_);
v_as_1705_ = v___x_1716_;
v_i_1706_ = v___x_1718_;
v_k_1707_ = v___x_1719_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11___redArg___boxed(lean_object* v_hi_1721_, lean_object* v_pivot_1722_, lean_object* v_as_1723_, lean_object* v_i_1724_, lean_object* v_k_1725_){
_start:
{
lean_object* v_res_1726_; 
v_res_1726_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11___redArg(v_hi_1721_, v_pivot_1722_, v_as_1723_, v_i_1724_, v_k_1725_);
lean_dec(v_pivot_1722_);
lean_dec(v_hi_1721_);
return v_res_1726_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg(lean_object* v_n_1727_, lean_object* v_as_1728_, lean_object* v_lo_1729_, lean_object* v_hi_1730_){
_start:
{
lean_object* v___y_1732_; uint8_t v___x_1742_; 
v___x_1742_ = lean_nat_dec_lt(v_lo_1729_, v_hi_1730_);
if (v___x_1742_ == 0)
{
lean_dec(v_lo_1729_);
return v_as_1728_;
}
else
{
lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v_mid_1745_; lean_object* v___y_1747_; lean_object* v___y_1753_; lean_object* v___x_1758_; lean_object* v___x_1759_; uint8_t v___x_1760_; 
v___x_1743_ = lean_nat_add(v_lo_1729_, v_hi_1730_);
v___x_1744_ = lean_unsigned_to_nat(1u);
v_mid_1745_ = lean_nat_shiftr(v___x_1743_, v___x_1744_);
lean_dec(v___x_1743_);
v___x_1758_ = lean_array_fget_borrowed(v_as_1728_, v_mid_1745_);
v___x_1759_ = lean_array_fget_borrowed(v_as_1728_, v_lo_1729_);
v___x_1760_ = l_Nat_blt(v___x_1758_, v___x_1759_);
if (v___x_1760_ == 0)
{
v___y_1753_ = v_as_1728_;
goto v___jp_1752_;
}
else
{
lean_object* v___x_1761_; 
v___x_1761_ = lean_array_fswap(v_as_1728_, v_lo_1729_, v_mid_1745_);
v___y_1753_ = v___x_1761_;
goto v___jp_1752_;
}
v___jp_1746_:
{
lean_object* v___x_1748_; lean_object* v___x_1749_; uint8_t v___x_1750_; 
v___x_1748_ = lean_array_fget_borrowed(v___y_1747_, v_mid_1745_);
v___x_1749_ = lean_array_fget_borrowed(v___y_1747_, v_hi_1730_);
v___x_1750_ = l_Nat_blt(v___x_1748_, v___x_1749_);
if (v___x_1750_ == 0)
{
lean_dec(v_mid_1745_);
v___y_1732_ = v___y_1747_;
goto v___jp_1731_;
}
else
{
lean_object* v___x_1751_; 
v___x_1751_ = lean_array_fswap(v___y_1747_, v_mid_1745_, v_hi_1730_);
lean_dec(v_mid_1745_);
v___y_1732_ = v___x_1751_;
goto v___jp_1731_;
}
}
v___jp_1752_:
{
lean_object* v___x_1754_; lean_object* v___x_1755_; uint8_t v___x_1756_; 
v___x_1754_ = lean_array_fget_borrowed(v___y_1753_, v_hi_1730_);
v___x_1755_ = lean_array_fget_borrowed(v___y_1753_, v_lo_1729_);
v___x_1756_ = l_Nat_blt(v___x_1754_, v___x_1755_);
if (v___x_1756_ == 0)
{
v___y_1747_ = v___y_1753_;
goto v___jp_1746_;
}
else
{
lean_object* v___x_1757_; 
v___x_1757_ = lean_array_fswap(v___y_1753_, v_lo_1729_, v_hi_1730_);
v___y_1747_ = v___x_1757_;
goto v___jp_1746_;
}
}
}
v___jp_1731_:
{
lean_object* v_pivot_1733_; lean_object* v___x_1734_; lean_object* v_fst_1735_; lean_object* v_snd_1736_; uint8_t v___x_1737_; 
v_pivot_1733_ = lean_array_fget(v___y_1732_, v_hi_1730_);
lean_inc_n(v_lo_1729_, 2);
v___x_1734_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11___redArg(v_hi_1730_, v_pivot_1733_, v___y_1732_, v_lo_1729_, v_lo_1729_);
lean_dec(v_pivot_1733_);
v_fst_1735_ = lean_ctor_get(v___x_1734_, 0);
lean_inc(v_fst_1735_);
v_snd_1736_ = lean_ctor_get(v___x_1734_, 1);
lean_inc(v_snd_1736_);
lean_dec_ref(v___x_1734_);
v___x_1737_ = lean_nat_dec_le(v_hi_1730_, v_fst_1735_);
if (v___x_1737_ == 0)
{
lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; 
v___x_1738_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg(v_n_1727_, v_snd_1736_, v_lo_1729_, v_fst_1735_);
v___x_1739_ = lean_unsigned_to_nat(1u);
v___x_1740_ = lean_nat_add(v_fst_1735_, v___x_1739_);
lean_dec(v_fst_1735_);
v_as_1728_ = v___x_1738_;
v_lo_1729_ = v___x_1740_;
goto _start;
}
else
{
lean_dec(v_fst_1735_);
lean_dec(v_lo_1729_);
return v_snd_1736_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg___boxed(lean_object* v_n_1762_, lean_object* v_as_1763_, lean_object* v_lo_1764_, lean_object* v_hi_1765_){
_start:
{
lean_object* v_res_1766_; 
v_res_1766_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg(v_n_1762_, v_as_1763_, v_lo_1764_, v_hi_1765_);
lean_dec(v_hi_1765_);
lean_dec(v_n_1762_);
return v_res_1766_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__6(lean_object* v_xs_1767_, lean_object* v_f_1768_, lean_object* v_x_1769_, lean_object* v_as_1770_, size_t v_i_1771_, size_t v_stop_1772_, lean_object* v_b_1773_){
_start:
{
lean_object* v___y_1775_; uint8_t v___x_1779_; 
v___x_1779_ = lean_usize_dec_eq(v_i_1771_, v_stop_1772_);
if (v___x_1779_ == 0)
{
lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; uint8_t v___x_1784_; 
v___x_1780_ = l_Lean_Elab_Structural_instInhabitedRecArgInfo_default;
v___x_1781_ = lean_array_uget_borrowed(v_as_1770_, v_i_1771_);
v___x_1782_ = lean_array_get_borrowed(v___x_1780_, v_xs_1767_, v___x_1781_);
lean_inc_ref(v_f_1768_);
lean_inc(v___x_1782_);
v___x_1783_ = lean_apply_1(v_f_1768_, v___x_1782_);
v___x_1784_ = lean_nat_dec_eq(v___x_1783_, v_x_1769_);
lean_dec(v___x_1783_);
if (v___x_1784_ == 0)
{
v___y_1775_ = v_b_1773_;
goto v___jp_1774_;
}
else
{
lean_object* v___x_1785_; 
lean_inc(v___x_1781_);
v___x_1785_ = lean_array_push(v_b_1773_, v___x_1781_);
v___y_1775_ = v___x_1785_;
goto v___jp_1774_;
}
}
else
{
lean_dec_ref(v_f_1768_);
return v_b_1773_;
}
v___jp_1774_:
{
size_t v___x_1776_; size_t v___x_1777_; 
v___x_1776_ = ((size_t)1ULL);
v___x_1777_ = lean_usize_add(v_i_1771_, v___x_1776_);
v_i_1771_ = v___x_1777_;
v_b_1773_ = v___y_1775_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__6___boxed(lean_object* v_xs_1786_, lean_object* v_f_1787_, lean_object* v_x_1788_, lean_object* v_as_1789_, lean_object* v_i_1790_, lean_object* v_stop_1791_, lean_object* v_b_1792_){
_start:
{
size_t v_i_boxed_1793_; size_t v_stop_boxed_1794_; lean_object* v_res_1795_; 
v_i_boxed_1793_ = lean_unbox_usize(v_i_1790_);
lean_dec(v_i_1790_);
v_stop_boxed_1794_ = lean_unbox_usize(v_stop_1791_);
lean_dec(v_stop_1791_);
v_res_1795_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__6(v_xs_1786_, v_f_1787_, v_x_1788_, v_as_1789_, v_i_boxed_1793_, v_stop_boxed_1794_, v_b_1792_);
lean_dec_ref(v_as_1789_);
lean_dec(v_x_1788_);
lean_dec_ref(v_xs_1786_);
return v_res_1795_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8(lean_object* v_xs_1798_, lean_object* v_f_1799_, size_t v_sz_1800_, size_t v_i_1801_, lean_object* v_bs_1802_){
_start:
{
uint8_t v___x_1803_; 
v___x_1803_ = lean_usize_dec_lt(v_i_1801_, v_sz_1800_);
if (v___x_1803_ == 0)
{
lean_dec_ref(v_f_1799_);
return v_bs_1802_;
}
else
{
lean_object* v_v_1804_; lean_object* v___x_1805_; lean_object* v_bs_x27_1806_; lean_object* v___y_1808_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; uint8_t v___x_1817_; 
v_v_1804_ = lean_array_uget(v_bs_1802_, v_i_1801_);
v___x_1805_ = lean_unsigned_to_nat(0u);
v_bs_x27_1806_ = lean_array_uset(v_bs_1802_, v_i_1801_, v___x_1805_);
v___x_1813_ = lean_array_get_size(v_xs_1798_);
v___x_1814_ = l_Array_range(v___x_1813_);
v___x_1815_ = lean_array_get_size(v___x_1814_);
v___x_1816_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8___closed__0));
v___x_1817_ = lean_nat_dec_lt(v___x_1805_, v___x_1815_);
if (v___x_1817_ == 0)
{
lean_dec_ref(v___x_1814_);
lean_dec(v_v_1804_);
v___y_1808_ = v___x_1816_;
goto v___jp_1807_;
}
else
{
uint8_t v___x_1818_; 
v___x_1818_ = lean_nat_dec_le(v___x_1815_, v___x_1815_);
if (v___x_1818_ == 0)
{
if (v___x_1817_ == 0)
{
lean_dec_ref(v___x_1814_);
lean_dec(v_v_1804_);
v___y_1808_ = v___x_1816_;
goto v___jp_1807_;
}
else
{
size_t v___x_1819_; size_t v___x_1820_; lean_object* v___x_1821_; 
v___x_1819_ = ((size_t)0ULL);
v___x_1820_ = lean_usize_of_nat(v___x_1815_);
lean_inc_ref(v_f_1799_);
v___x_1821_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__6(v_xs_1798_, v_f_1799_, v_v_1804_, v___x_1814_, v___x_1819_, v___x_1820_, v___x_1816_);
lean_dec_ref(v___x_1814_);
lean_dec(v_v_1804_);
v___y_1808_ = v___x_1821_;
goto v___jp_1807_;
}
}
else
{
size_t v___x_1822_; size_t v___x_1823_; lean_object* v___x_1824_; 
v___x_1822_ = ((size_t)0ULL);
v___x_1823_ = lean_usize_of_nat(v___x_1815_);
lean_inc_ref(v_f_1799_);
v___x_1824_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__6(v_xs_1798_, v_f_1799_, v_v_1804_, v___x_1814_, v___x_1822_, v___x_1823_, v___x_1816_);
lean_dec_ref(v___x_1814_);
lean_dec(v_v_1804_);
v___y_1808_ = v___x_1824_;
goto v___jp_1807_;
}
}
v___jp_1807_:
{
size_t v___x_1809_; size_t v___x_1810_; lean_object* v___x_1811_; 
v___x_1809_ = ((size_t)1ULL);
v___x_1810_ = lean_usize_add(v_i_1801_, v___x_1809_);
v___x_1811_ = lean_array_uset(v_bs_x27_1806_, v_i_1801_, v___y_1808_);
v_i_1801_ = v___x_1810_;
v_bs_1802_ = v___x_1811_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8___boxed(lean_object* v_xs_1825_, lean_object* v_f_1826_, lean_object* v_sz_1827_, lean_object* v_i_1828_, lean_object* v_bs_1829_){
_start:
{
size_t v_sz_boxed_1830_; size_t v_i_boxed_1831_; lean_object* v_res_1832_; 
v_sz_boxed_1830_ = lean_unbox_usize(v_sz_1827_);
lean_dec(v_sz_1827_);
v_i_boxed_1831_ = lean_unbox_usize(v_i_1828_);
lean_dec(v_i_1828_);
v_res_1832_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8(v_xs_1825_, v_f_1826_, v_sz_boxed_1830_, v_i_boxed_1831_, v_bs_1829_);
lean_dec_ref(v_xs_1825_);
return v_res_1832_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__11(lean_object* v_as_1833_, size_t v_i_1834_, size_t v_stop_1835_, lean_object* v_b_1836_){
_start:
{
uint8_t v___x_1837_; 
v___x_1837_ = lean_usize_dec_eq(v_i_1834_, v_stop_1835_);
if (v___x_1837_ == 0)
{
lean_object* v___x_1838_; lean_object* v___x_1839_; size_t v___x_1840_; size_t v___x_1841_; 
v___x_1838_ = lean_array_uget_borrowed(v_as_1833_, v_i_1834_);
v___x_1839_ = l_Array_append___redArg(v_b_1836_, v___x_1838_);
v___x_1840_ = ((size_t)1ULL);
v___x_1841_ = lean_usize_add(v_i_1834_, v___x_1840_);
v_i_1834_ = v___x_1841_;
v_b_1836_ = v___x_1839_;
goto _start;
}
else
{
return v_b_1836_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__11___boxed(lean_object* v_as_1843_, lean_object* v_i_1844_, lean_object* v_stop_1845_, lean_object* v_b_1846_){
_start:
{
size_t v_i_boxed_1847_; size_t v_stop_boxed_1848_; lean_object* v_res_1849_; 
v_i_boxed_1847_ = lean_unbox_usize(v_i_1844_);
lean_dec(v_i_1844_);
v_stop_boxed_1848_ = lean_unbox_usize(v_stop_1845_);
lean_dec(v_stop_1845_);
v_res_1849_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__11(v_as_1843_, v_i_boxed_1847_, v_stop_boxed_1848_, v_b_1846_);
lean_dec_ref(v_as_1843_);
return v_res_1849_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__7___closed__0(void){
_start:
{
lean_object* v___x_1850_; 
v___x_1850_ = l_Array_instInhabited(lean_box(0));
return v___x_1850_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__7(lean_object* v_msg_1851_){
_start:
{
lean_object* v___x_1852_; lean_object* v___x_1853_; 
v___x_1852_ = lean_obj_once(&l_panic___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__7___closed__0, &l_panic___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__7___closed__0_once, _init_l_panic___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__7___closed__0);
v___x_1853_ = lean_panic_fn_borrowed(v___x_1852_, v_msg_1851_);
return v___x_1853_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9___redArg(lean_object* v_xs_1854_, lean_object* v_ys_1855_, lean_object* v_x_1856_){
_start:
{
lean_object* v_zero_1857_; uint8_t v_isZero_1858_; 
v_zero_1857_ = lean_unsigned_to_nat(0u);
v_isZero_1858_ = lean_nat_dec_eq(v_x_1856_, v_zero_1857_);
if (v_isZero_1858_ == 1)
{
lean_dec(v_x_1856_);
return v_isZero_1858_;
}
else
{
lean_object* v_one_1859_; lean_object* v_n_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; uint8_t v___x_1863_; 
v_one_1859_ = lean_unsigned_to_nat(1u);
v_n_1860_ = lean_nat_sub(v_x_1856_, v_one_1859_);
lean_dec(v_x_1856_);
v___x_1861_ = lean_array_fget_borrowed(v_xs_1854_, v_n_1860_);
v___x_1862_ = lean_array_fget_borrowed(v_ys_1855_, v_n_1860_);
v___x_1863_ = lean_nat_dec_eq(v___x_1861_, v___x_1862_);
if (v___x_1863_ == 0)
{
lean_dec(v_n_1860_);
return v___x_1863_;
}
else
{
v_x_1856_ = v_n_1860_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9___redArg___boxed(lean_object* v_xs_1865_, lean_object* v_ys_1866_, lean_object* v_x_1867_){
_start:
{
uint8_t v_res_1868_; lean_object* v_r_1869_; 
v_res_1868_ = l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9___redArg(v_xs_1865_, v_ys_1866_, v_x_1867_);
lean_dec_ref(v_ys_1866_);
lean_dec_ref(v_xs_1865_);
v_r_1869_ = lean_box(v_res_1868_);
return v_r_1869_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__2(void){
_start:
{
lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; 
v___x_1872_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__1));
v___x_1873_ = lean_unsigned_to_nat(2u);
v___x_1874_ = lean_unsigned_to_nat(63u);
v___x_1875_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__0));
v___x_1876_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__0));
v___x_1877_ = l_mkPanicMessageWithDecl(v___x_1876_, v___x_1875_, v___x_1874_, v___x_1873_, v___x_1872_);
return v___x_1877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5(lean_object* v_f_1880_, lean_object* v_xs_1881_, lean_object* v_ys_1882_){
_start:
{
size_t v_sz_1886_; size_t v___x_1887_; lean_object* v_positions_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___y_1892_; lean_object* v___y_1898_; lean_object* v___y_1899_; lean_object* v___y_1900_; lean_object* v___y_1901_; lean_object* v___y_1904_; lean_object* v___y_1905_; lean_object* v___y_1906_; lean_object* v___y_1907_; lean_object* v___y_1910_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; uint8_t v___x_1920_; 
v_sz_1886_ = lean_array_size(v_ys_1882_);
v___x_1887_ = ((size_t)0ULL);
v_positions_1888_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8(v_xs_1881_, v_f_1880_, v_sz_1886_, v___x_1887_, v_ys_1882_);
v___x_1889_ = lean_array_get_size(v_xs_1881_);
v___x_1890_ = l_Array_range(v___x_1889_);
v___x_1917_ = lean_unsigned_to_nat(0u);
v___x_1918_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__3));
v___x_1919_ = lean_array_get_size(v_positions_1888_);
v___x_1920_ = lean_nat_dec_lt(v___x_1917_, v___x_1919_);
if (v___x_1920_ == 0)
{
v___y_1910_ = v___x_1918_;
goto v___jp_1909_;
}
else
{
uint8_t v___x_1921_; 
v___x_1921_ = lean_nat_dec_le(v___x_1919_, v___x_1919_);
if (v___x_1921_ == 0)
{
if (v___x_1920_ == 0)
{
v___y_1910_ = v___x_1918_;
goto v___jp_1909_;
}
else
{
size_t v___x_1922_; lean_object* v___x_1923_; 
v___x_1922_ = lean_usize_of_nat(v___x_1919_);
v___x_1923_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__11(v_positions_1888_, v___x_1887_, v___x_1922_, v___x_1918_);
v___y_1910_ = v___x_1923_;
goto v___jp_1909_;
}
}
else
{
size_t v___x_1924_; lean_object* v___x_1925_; 
v___x_1924_ = lean_usize_of_nat(v___x_1919_);
v___x_1925_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__11(v_positions_1888_, v___x_1887_, v___x_1924_, v___x_1918_);
v___y_1910_ = v___x_1925_;
goto v___jp_1909_;
}
}
v___jp_1883_:
{
lean_object* v___x_1884_; lean_object* v___x_1885_; 
v___x_1884_ = lean_obj_once(&l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__2, &l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__2_once, _init_l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__2);
v___x_1885_ = l_panic___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__7(v___x_1884_);
return v___x_1885_;
}
v___jp_1891_:
{
lean_object* v___x_1893_; lean_object* v___x_1894_; uint8_t v___x_1895_; 
v___x_1893_ = lean_array_get_size(v___x_1890_);
v___x_1894_ = lean_array_get_size(v___y_1892_);
v___x_1895_ = lean_nat_dec_eq(v___x_1893_, v___x_1894_);
if (v___x_1895_ == 0)
{
lean_dec_ref(v___y_1892_);
lean_dec_ref(v___x_1890_);
lean_dec_ref(v_positions_1888_);
goto v___jp_1883_;
}
else
{
uint8_t v___x_1896_; 
v___x_1896_ = l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9___redArg(v___x_1890_, v___y_1892_, v___x_1893_);
lean_dec_ref(v___y_1892_);
lean_dec_ref(v___x_1890_);
if (v___x_1896_ == 0)
{
lean_dec_ref(v_positions_1888_);
goto v___jp_1883_;
}
else
{
return v_positions_1888_;
}
}
}
v___jp_1897_:
{
lean_object* v___x_1902_; 
v___x_1902_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg(v___y_1900_, v___y_1898_, v___y_1899_, v___y_1901_);
lean_dec(v___y_1901_);
lean_dec(v___y_1900_);
v___y_1892_ = v___x_1902_;
goto v___jp_1891_;
}
v___jp_1903_:
{
uint8_t v___x_1908_; 
v___x_1908_ = lean_nat_dec_le(v___y_1907_, v___y_1906_);
if (v___x_1908_ == 0)
{
lean_dec(v___y_1906_);
lean_inc(v___y_1907_);
v___y_1898_ = v___y_1904_;
v___y_1899_ = v___y_1907_;
v___y_1900_ = v___y_1905_;
v___y_1901_ = v___y_1907_;
goto v___jp_1897_;
}
else
{
v___y_1898_ = v___y_1904_;
v___y_1899_ = v___y_1907_;
v___y_1900_ = v___y_1905_;
v___y_1901_ = v___y_1906_;
goto v___jp_1897_;
}
}
v___jp_1909_:
{
lean_object* v___x_1911_; lean_object* v___x_1912_; uint8_t v___x_1913_; 
v___x_1911_ = lean_array_get_size(v___y_1910_);
v___x_1912_ = lean_unsigned_to_nat(0u);
v___x_1913_ = lean_nat_dec_eq(v___x_1911_, v___x_1912_);
if (v___x_1913_ == 0)
{
lean_object* v___x_1914_; lean_object* v___x_1915_; uint8_t v___x_1916_; 
v___x_1914_ = lean_unsigned_to_nat(1u);
v___x_1915_ = lean_nat_sub(v___x_1911_, v___x_1914_);
v___x_1916_ = lean_nat_dec_le(v___x_1912_, v___x_1915_);
if (v___x_1916_ == 0)
{
lean_inc(v___x_1915_);
v___y_1904_ = v___y_1910_;
v___y_1905_ = v___x_1911_;
v___y_1906_ = v___x_1915_;
v___y_1907_ = v___x_1915_;
goto v___jp_1903_;
}
else
{
v___y_1904_ = v___y_1910_;
v___y_1905_ = v___x_1911_;
v___y_1906_ = v___x_1915_;
v___y_1907_ = v___x_1912_;
goto v___jp_1903_;
}
}
else
{
v___y_1892_ = v___y_1910_;
goto v___jp_1891_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___boxed(lean_object* v_f_1926_, lean_object* v_xs_1927_, lean_object* v_ys_1928_){
_start:
{
lean_object* v_res_1929_; 
v_res_1929_ = l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5(v_f_1926_, v_xs_1927_, v_ys_1928_);
lean_dec_ref(v_xs_1927_);
return v_res_1929_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___redArg(lean_object* v_fixedParamPerms_1930_, lean_object* v_xs_1931_, lean_object* v_as_1932_, lean_object* v_i_1933_, lean_object* v_j_1934_, lean_object* v_bs_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_){
_start:
{
lean_object* v_zero_1941_; uint8_t v_isZero_1942_; 
v_zero_1941_ = lean_unsigned_to_nat(0u);
v_isZero_1942_ = lean_nat_dec_eq(v_i_1933_, v_zero_1941_);
if (v_isZero_1942_ == 1)
{
lean_object* v___x_1943_; 
lean_dec(v_j_1934_);
lean_dec(v_i_1933_);
lean_dec_ref(v_xs_1931_);
v___x_1943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1943_, 0, v_bs_1935_);
return v___x_1943_;
}
else
{
lean_object* v_perms_1944_; lean_object* v___x_1945_; lean_object* v_value_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; 
v_perms_1944_ = lean_ctor_get(v_fixedParamPerms_1930_, 1);
v___x_1945_ = lean_array_fget_borrowed(v_as_1932_, v_j_1934_);
v_value_1946_ = lean_ctor_get(v___x_1945_, 7);
v___x_1947_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0, &l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0_once, _init_l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0);
v___x_1948_ = lean_array_get_borrowed(v___x_1947_, v_perms_1944_, v_j_1934_);
lean_inc_ref(v_xs_1931_);
lean_inc_ref(v_value_1946_);
lean_inc(v___x_1948_);
v___x_1949_ = l_Lean_Elab_FixedParamPerm_instantiateLambda(v___x_1948_, v_value_1946_, v_xs_1931_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_);
if (lean_obj_tag(v___x_1949_) == 0)
{
lean_object* v_a_1950_; lean_object* v_one_1951_; lean_object* v_n_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; 
v_a_1950_ = lean_ctor_get(v___x_1949_, 0);
lean_inc(v_a_1950_);
lean_dec_ref(v___x_1949_);
v_one_1951_ = lean_unsigned_to_nat(1u);
v_n_1952_ = lean_nat_sub(v_i_1933_, v_one_1951_);
lean_dec(v_i_1933_);
v___x_1953_ = lean_nat_add(v_j_1934_, v_one_1951_);
lean_dec(v_j_1934_);
v___x_1954_ = lean_array_push(v_bs_1935_, v_a_1950_);
v_i_1933_ = v_n_1952_;
v_j_1934_ = v___x_1953_;
v_bs_1935_ = v___x_1954_;
goto _start;
}
else
{
lean_object* v_a_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1963_; 
lean_dec_ref(v_bs_1935_);
lean_dec(v_j_1934_);
lean_dec(v_i_1933_);
lean_dec_ref(v_xs_1931_);
v_a_1956_ = lean_ctor_get(v___x_1949_, 0);
v_isSharedCheck_1963_ = !lean_is_exclusive(v___x_1949_);
if (v_isSharedCheck_1963_ == 0)
{
v___x_1958_ = v___x_1949_;
v_isShared_1959_ = v_isSharedCheck_1963_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_a_1956_);
lean_dec(v___x_1949_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_1963_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
lean_object* v___x_1961_; 
if (v_isShared_1959_ == 0)
{
v___x_1961_ = v___x_1958_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1962_; 
v_reuseFailAlloc_1962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1962_, 0, v_a_1956_);
v___x_1961_ = v_reuseFailAlloc_1962_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
return v___x_1961_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___redArg___boxed(lean_object* v_fixedParamPerms_1964_, lean_object* v_xs_1965_, lean_object* v_as_1966_, lean_object* v_i_1967_, lean_object* v_j_1968_, lean_object* v_bs_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_){
_start:
{
lean_object* v_res_1975_; 
v_res_1975_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___redArg(v_fixedParamPerms_1964_, v_xs_1965_, v_as_1966_, v_i_1967_, v_j_1968_, v_bs_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_);
lean_dec(v___y_1973_);
lean_dec_ref(v___y_1972_);
lean_dec(v___y_1971_);
lean_dec_ref(v___y_1970_);
lean_dec_ref(v_as_1966_);
lean_dec_ref(v_fixedParamPerms_1964_);
return v_res_1975_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__0(lean_object* v_a_1976_, lean_object* v_a_1977_){
_start:
{
if (lean_obj_tag(v_a_1976_) == 0)
{
lean_object* v___x_1978_; 
v___x_1978_ = l_List_reverse___redArg(v_a_1977_);
return v___x_1978_;
}
else
{
lean_object* v_head_1979_; lean_object* v_tail_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1991_; 
v_head_1979_ = lean_ctor_get(v_a_1976_, 0);
v_tail_1980_ = lean_ctor_get(v_a_1976_, 1);
v_isSharedCheck_1991_ = !lean_is_exclusive(v_a_1976_);
if (v_isSharedCheck_1991_ == 0)
{
v___x_1982_ = v_a_1976_;
v_isShared_1983_ = v_isSharedCheck_1991_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_tail_1980_);
lean_inc(v_head_1979_);
lean_dec(v_a_1976_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_1991_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1988_; 
v___x_1984_ = l_Nat_reprFast(v_head_1979_);
v___x_1985_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1985_, 0, v___x_1984_);
v___x_1986_ = l_Lean_MessageData_ofFormat(v___x_1985_);
if (v_isShared_1983_ == 0)
{
lean_ctor_set(v___x_1982_, 1, v_a_1977_);
lean_ctor_set(v___x_1982_, 0, v___x_1986_);
v___x_1988_ = v___x_1982_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v___x_1986_);
lean_ctor_set(v_reuseFailAlloc_1990_, 1, v_a_1977_);
v___x_1988_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
v_a_1976_ = v_tail_1980_;
v_a_1977_ = v___x_1988_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__20(lean_object* v_a_1992_, lean_object* v_a_1993_){
_start:
{
if (lean_obj_tag(v_a_1992_) == 0)
{
lean_object* v___x_1994_; 
v___x_1994_ = l_List_reverse___redArg(v_a_1993_);
return v___x_1994_;
}
else
{
lean_object* v_head_1995_; lean_object* v_tail_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2008_; 
v_head_1995_ = lean_ctor_get(v_a_1992_, 0);
v_tail_1996_ = lean_ctor_get(v_a_1992_, 1);
v_isSharedCheck_2008_ = !lean_is_exclusive(v_a_1992_);
if (v_isSharedCheck_2008_ == 0)
{
v___x_1998_ = v_a_1992_;
v_isShared_1999_ = v_isSharedCheck_2008_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_tail_1996_);
lean_inc(v_head_1995_);
lean_dec(v_a_1992_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2008_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2005_; 
v___x_2000_ = lean_array_to_list(v_head_1995_);
v___x_2001_ = lean_box(0);
v___x_2002_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__0(v___x_2000_, v___x_2001_);
v___x_2003_ = l_Lean_MessageData_ofList(v___x_2002_);
if (v_isShared_1999_ == 0)
{
lean_ctor_set(v___x_1998_, 1, v_a_1993_);
lean_ctor_set(v___x_1998_, 0, v___x_2003_);
v___x_2005_ = v___x_1998_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v___x_2003_);
lean_ctor_set(v_reuseFailAlloc_2007_, 1, v_a_1993_);
v___x_2005_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
v_a_1992_ = v_tail_1996_;
v_a_1993_ = v___x_2005_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___redArg(lean_object* v_fixedParamPerms_2009_, lean_object* v_xs_2010_, lean_object* v_as_2011_, lean_object* v_i_2012_, lean_object* v_j_2013_, lean_object* v_bs_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_){
_start:
{
lean_object* v_zero_2020_; uint8_t v_isZero_2021_; 
v_zero_2020_ = lean_unsigned_to_nat(0u);
v_isZero_2021_ = lean_nat_dec_eq(v_i_2012_, v_zero_2020_);
if (v_isZero_2021_ == 1)
{
lean_object* v___x_2022_; 
lean_dec(v_j_2013_);
lean_dec(v_i_2012_);
lean_dec_ref(v_xs_2010_);
v___x_2022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2022_, 0, v_bs_2014_);
return v___x_2022_;
}
else
{
lean_object* v_perms_2023_; lean_object* v___x_2024_; lean_object* v_type_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; 
v_perms_2023_ = lean_ctor_get(v_fixedParamPerms_2009_, 1);
v___x_2024_ = lean_array_fget_borrowed(v_as_2011_, v_j_2013_);
v_type_2025_ = lean_ctor_get(v___x_2024_, 6);
v___x_2026_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0, &l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0_once, _init_l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0);
v___x_2027_ = lean_array_get_borrowed(v___x_2026_, v_perms_2023_, v_j_2013_);
lean_inc_ref(v_xs_2010_);
lean_inc_ref(v_type_2025_);
lean_inc(v___x_2027_);
v___x_2028_ = l_Lean_Elab_FixedParamPerm_instantiateForall(v___x_2027_, v_type_2025_, v_xs_2010_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_);
if (lean_obj_tag(v___x_2028_) == 0)
{
lean_object* v_a_2029_; lean_object* v_one_2030_; lean_object* v_n_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; 
v_a_2029_ = lean_ctor_get(v___x_2028_, 0);
lean_inc(v_a_2029_);
lean_dec_ref(v___x_2028_);
v_one_2030_ = lean_unsigned_to_nat(1u);
v_n_2031_ = lean_nat_sub(v_i_2012_, v_one_2030_);
lean_dec(v_i_2012_);
v___x_2032_ = lean_nat_add(v_j_2013_, v_one_2030_);
lean_dec(v_j_2013_);
v___x_2033_ = lean_array_push(v_bs_2014_, v_a_2029_);
v_i_2012_ = v_n_2031_;
v_j_2013_ = v___x_2032_;
v_bs_2014_ = v___x_2033_;
goto _start;
}
else
{
lean_object* v_a_2035_; lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2042_; 
lean_dec_ref(v_bs_2014_);
lean_dec(v_j_2013_);
lean_dec(v_i_2012_);
lean_dec_ref(v_xs_2010_);
v_a_2035_ = lean_ctor_get(v___x_2028_, 0);
v_isSharedCheck_2042_ = !lean_is_exclusive(v___x_2028_);
if (v_isSharedCheck_2042_ == 0)
{
v___x_2037_ = v___x_2028_;
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
else
{
lean_inc(v_a_2035_);
lean_dec(v___x_2028_);
v___x_2037_ = lean_box(0);
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
v_resetjp_2036_:
{
lean_object* v___x_2040_; 
if (v_isShared_2038_ == 0)
{
v___x_2040_ = v___x_2037_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v_a_2035_);
v___x_2040_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
return v___x_2040_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___redArg___boxed(lean_object* v_fixedParamPerms_2043_, lean_object* v_xs_2044_, lean_object* v_as_2045_, lean_object* v_i_2046_, lean_object* v_j_2047_, lean_object* v_bs_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_){
_start:
{
lean_object* v_res_2054_; 
v_res_2054_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___redArg(v_fixedParamPerms_2043_, v_xs_2044_, v_as_2045_, v_i_2046_, v_j_2047_, v_bs_2048_, v___y_2049_, v___y_2050_, v___y_2051_, v___y_2052_);
lean_dec(v___y_2052_);
lean_dec_ref(v___y_2051_);
lean_dec(v___y_2050_);
lean_dec_ref(v___y_2049_);
lean_dec_ref(v_as_2045_);
lean_dec_ref(v_fixedParamPerms_2043_);
return v_res_2054_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__9(void){
_start:
{
lean_object* v___x_2069_; lean_object* v___x_2070_; 
v___x_2069_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__8));
v___x_2070_ = l_Lean_stringToMessageData(v___x_2069_);
return v___x_2070_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__11(void){
_start:
{
lean_object* v___x_2072_; lean_object* v___x_2073_; 
v___x_2072_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__10));
v___x_2073_ = l_Lean_stringToMessageData(v___x_2072_);
return v___x_2073_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion(lean_object* v_preDefs_2074_, lean_object* v_fixedParamPerms_2075_, lean_object* v_xs_2076_, lean_object* v_recArgInfos_2077_, lean_object* v_a_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_, lean_object* v_a_2081_){
_start:
{
lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; 
v___x_2083_ = lean_array_get_size(v_preDefs_2074_);
v___x_2084_ = lean_unsigned_to_nat(0u);
v___x_2085_ = lean_mk_empty_array_with_capacity(v___x_2083_);
lean_inc_ref(v___x_2085_);
lean_inc_ref(v_xs_2076_);
v___x_2086_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___redArg(v_fixedParamPerms_2075_, v_xs_2076_, v_preDefs_2074_, v___x_2083_, v___x_2084_, v___x_2085_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_);
if (lean_obj_tag(v___x_2086_) == 0)
{
lean_object* v_a_2087_; lean_object* v___x_2088_; 
v_a_2087_ = lean_ctor_get(v___x_2086_, 0);
lean_inc(v_a_2087_);
lean_dec_ref(v___x_2086_);
lean_inc_ref(v_xs_2076_);
v___x_2088_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___redArg(v_fixedParamPerms_2075_, v_xs_2076_, v_preDefs_2074_, v___x_2083_, v___x_2084_, v___x_2085_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_);
if (lean_obj_tag(v___x_2088_) == 0)
{
lean_object* v_a_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v_indGroupInst_2092_; lean_object* v_toIndGroupInfo_2093_; lean_object* v_all_2094_; lean_object* v___x_2096_; uint8_t v_isShared_2097_; uint8_t v_isSharedCheck_2180_; 
v_a_2089_ = lean_ctor_get(v___x_2088_, 0);
lean_inc(v_a_2089_);
lean_dec_ref(v___x_2088_);
v___x_2090_ = l_Lean_Elab_Structural_instInhabitedRecArgInfo_default;
v___x_2091_ = lean_array_get_borrowed(v___x_2090_, v_recArgInfos_2077_, v___x_2084_);
v_indGroupInst_2092_ = lean_ctor_get(v___x_2091_, 4);
v_toIndGroupInfo_2093_ = lean_ctor_get(v_indGroupInst_2092_, 0);
lean_inc_ref(v_toIndGroupInfo_2093_);
v_all_2094_ = lean_ctor_get(v_toIndGroupInfo_2093_, 0);
v_isSharedCheck_2180_ = !lean_is_exclusive(v_toIndGroupInfo_2093_);
if (v_isSharedCheck_2180_ == 0)
{
lean_object* v_unused_2181_; 
v_unused_2181_ = lean_ctor_get(v_toIndGroupInfo_2093_, 1);
lean_dec(v_unused_2181_);
v___x_2096_ = v_toIndGroupInfo_2093_;
v_isShared_2097_ = v_isSharedCheck_2180_;
goto v_resetjp_2095_;
}
else
{
lean_inc(v_all_2094_);
lean_dec(v_toIndGroupInfo_2093_);
v___x_2096_ = lean_box(0);
v_isShared_2097_ = v_isSharedCheck_2180_;
goto v_resetjp_2095_;
}
v_resetjp_2095_:
{
lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; 
v___x_2098_ = lean_box(0);
v___x_2099_ = lean_array_get(v___x_2098_, v_all_2094_, v___x_2084_);
lean_dec_ref(v_all_2094_);
v___x_2100_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4(v___x_2099_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_);
if (lean_obj_tag(v___x_2100_) == 0)
{
lean_object* v_a_2101_; lean_object* v___x_2102_; lean_object* v___f_2103_; lean_object* v___x_2104_; lean_object* v_a_2105_; lean_object* v___f_2106_; lean_object* v___f_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___y_2112_; lean_object* v___y_2113_; lean_object* v___y_2114_; lean_object* v___y_2115_; uint8_t v___x_2148_; 
v_a_2101_ = lean_ctor_get(v___x_2100_, 0);
lean_inc(v_a_2101_);
lean_dec_ref(v___x_2100_);
v___x_2102_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__3));
v___f_2103_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__4));
v___x_2104_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0(v___x_2102_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_);
v_a_2105_ = lean_ctor_get(v___x_2104_, 0);
lean_inc(v_a_2105_);
lean_dec_ref(v___x_2104_);
v___f_2106_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__5));
v___f_2107_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__6));
v___x_2108_ = l_Lean_InductiveVal_numTypeFormers(v_a_2101_);
v___x_2109_ = l_Array_range(v___x_2108_);
v___x_2110_ = l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5(v___f_2107_, v_recArgInfos_2077_, v___x_2109_);
v___x_2148_ = lean_unbox(v_a_2105_);
lean_dec(v_a_2105_);
if (v___x_2148_ == 0)
{
lean_del_object(v___x_2096_);
v___y_2112_ = v_a_2078_;
v___y_2113_ = v_a_2079_;
v___y_2114_ = v_a_2080_;
v___y_2115_ = v_a_2081_;
goto v___jp_2111_;
}
else
{
lean_object* v_toConstantVal_2149_; lean_object* v_name_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2154_; 
v_toConstantVal_2149_ = lean_ctor_get(v_a_2101_, 0);
v_name_2150_ = lean_ctor_get(v_toConstantVal_2149_, 0);
v___x_2151_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__9, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__9_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__9);
lean_inc(v_name_2150_);
v___x_2152_ = l_Lean_MessageData_ofName(v_name_2150_);
if (v_isShared_2097_ == 0)
{
lean_ctor_set_tag(v___x_2096_, 7);
lean_ctor_set(v___x_2096_, 1, v___x_2152_);
lean_ctor_set(v___x_2096_, 0, v___x_2151_);
v___x_2154_ = v___x_2096_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v___x_2151_);
lean_ctor_set(v_reuseFailAlloc_2171_, 1, v___x_2152_);
v___x_2154_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; 
v___x_2155_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__11, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__11_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__11);
v___x_2156_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2156_, 0, v___x_2154_);
lean_ctor_set(v___x_2156_, 1, v___x_2155_);
lean_inc_ref(v___x_2110_);
v___x_2157_ = lean_array_to_list(v___x_2110_);
v___x_2158_ = lean_box(0);
v___x_2159_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__20(v___x_2157_, v___x_2158_);
v___x_2160_ = l_Lean_MessageData_ofList(v___x_2159_);
v___x_2161_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2161_, 0, v___x_2156_);
lean_ctor_set(v___x_2161_, 1, v___x_2160_);
v___x_2162_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_2102_, v___x_2161_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_);
if (lean_obj_tag(v___x_2162_) == 0)
{
lean_dec_ref(v___x_2162_);
v___y_2112_ = v_a_2078_;
v___y_2113_ = v_a_2079_;
v___y_2114_ = v_a_2080_;
v___y_2115_ = v_a_2081_;
goto v___jp_2111_;
}
else
{
lean_object* v_a_2163_; lean_object* v___x_2165_; uint8_t v_isShared_2166_; uint8_t v_isSharedCheck_2170_; 
lean_dec_ref(v___x_2110_);
lean_dec(v_a_2101_);
lean_dec(v_a_2089_);
lean_dec(v_a_2087_);
lean_dec_ref(v_recArgInfos_2077_);
lean_dec_ref(v_xs_2076_);
lean_dec_ref(v_fixedParamPerms_2075_);
lean_dec_ref(v_preDefs_2074_);
v_a_2163_ = lean_ctor_get(v___x_2162_, 0);
v_isSharedCheck_2170_ = !lean_is_exclusive(v___x_2162_);
if (v_isSharedCheck_2170_ == 0)
{
v___x_2165_ = v___x_2162_;
v_isShared_2166_ = v_isSharedCheck_2170_;
goto v_resetjp_2164_;
}
else
{
lean_inc(v_a_2163_);
lean_dec(v___x_2162_);
v___x_2165_ = lean_box(0);
v_isShared_2166_ = v_isSharedCheck_2170_;
goto v_resetjp_2164_;
}
v_resetjp_2164_:
{
lean_object* v___x_2168_; 
if (v_isShared_2166_ == 0)
{
v___x_2168_ = v___x_2165_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2169_; 
v_reuseFailAlloc_2169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2169_, 0, v_a_2163_);
v___x_2168_ = v_reuseFailAlloc_2169_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
return v___x_2168_;
}
}
}
}
}
v___jp_2111_:
{
lean_object* v_toConstantVal_2116_; lean_object* v_numIndices_2117_; lean_object* v_name_2118_; lean_object* v___x_2119_; 
v_toConstantVal_2116_ = lean_ctor_get(v_a_2101_, 0);
lean_inc_ref(v_toConstantVal_2116_);
v_numIndices_2117_ = lean_ctor_get(v_a_2101_, 2);
lean_inc(v_numIndices_2117_);
lean_dec(v_a_2101_);
v_name_2118_ = lean_ctor_get(v_toConstantVal_2116_, 0);
lean_inc(v_name_2118_);
lean_dec_ref(v_toConstantVal_2116_);
v___x_2119_ = l_Lean_Meta_isInductivePredicate(v_name_2118_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_);
if (lean_obj_tag(v___x_2119_) == 0)
{
lean_object* v_a_2120_; lean_object* v___f_2121_; uint8_t v___x_2122_; 
v_a_2120_ = lean_ctor_get(v___x_2119_, 0);
lean_inc_n(v_a_2120_, 2);
lean_dec_ref(v___x_2119_);
lean_inc(v_numIndices_2117_);
lean_inc_ref(v_preDefs_2074_);
lean_inc_ref(v_xs_2076_);
lean_inc_ref(v_fixedParamPerms_2075_);
lean_inc_ref(v___x_2110_);
lean_inc(v_a_2087_);
lean_inc_ref(v_recArgInfos_2077_);
v___f_2121_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___boxed), 19, 12);
lean_closure_set(v___f_2121_, 0, v___f_2103_);
lean_closure_set(v___f_2121_, 1, v_recArgInfos_2077_);
lean_closure_set(v___f_2121_, 2, v_a_2087_);
lean_closure_set(v___f_2121_, 3, v___x_2110_);
lean_closure_set(v___f_2121_, 4, v___x_2084_);
lean_closure_set(v___f_2121_, 5, v_fixedParamPerms_2075_);
lean_closure_set(v___f_2121_, 6, v_xs_2076_);
lean_closure_set(v___f_2121_, 7, v_preDefs_2074_);
lean_closure_set(v___f_2121_, 8, v_numIndices_2117_);
lean_closure_set(v___f_2121_, 9, v___f_2106_);
lean_closure_set(v___f_2121_, 10, v___x_2102_);
lean_closure_set(v___f_2121_, 11, v_a_2120_);
v___x_2122_ = lean_unbox(v_a_2120_);
if (v___x_2122_ == 0)
{
lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; 
lean_dec_ref(v___f_2121_);
v___x_2123_ = lean_array_get_size(v_recArgInfos_2077_);
v___x_2124_ = lean_mk_empty_array_with_capacity(v___x_2123_);
v___x_2125_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___redArg(v_a_2087_, v_a_2089_, v_recArgInfos_2077_, v___x_2123_, v___x_2084_, v___x_2124_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_);
lean_dec(v_a_2089_);
if (lean_obj_tag(v___x_2125_) == 0)
{
lean_object* v_a_2126_; lean_object* v___x_2127_; uint8_t v___x_2128_; lean_object* v___x_2129_; 
v_a_2126_ = lean_ctor_get(v___x_2125_, 0);
lean_inc(v_a_2126_);
lean_dec_ref(v___x_2125_);
v___x_2127_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__7));
v___x_2128_ = lean_unbox(v_a_2120_);
lean_dec(v_a_2120_);
v___x_2129_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2(v___f_2103_, v_recArgInfos_2077_, v_a_2087_, v___x_2110_, v___x_2084_, v_fixedParamPerms_2075_, v_xs_2076_, v_preDefs_2074_, v_numIndices_2117_, v___f_2106_, v___x_2102_, v___x_2128_, v___x_2127_, v_a_2126_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_);
lean_dec(v_numIndices_2117_);
lean_dec(v_a_2087_);
return v___x_2129_;
}
else
{
lean_object* v_a_2130_; lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2137_; 
lean_dec(v_a_2120_);
lean_dec(v_numIndices_2117_);
lean_dec_ref(v___x_2110_);
lean_dec(v_a_2087_);
lean_dec_ref(v_recArgInfos_2077_);
lean_dec_ref(v_xs_2076_);
lean_dec_ref(v_fixedParamPerms_2075_);
lean_dec_ref(v_preDefs_2074_);
v_a_2130_ = lean_ctor_get(v___x_2125_, 0);
v_isSharedCheck_2137_ = !lean_is_exclusive(v___x_2125_);
if (v_isSharedCheck_2137_ == 0)
{
v___x_2132_ = v___x_2125_;
v_isShared_2133_ = v_isSharedCheck_2137_;
goto v_resetjp_2131_;
}
else
{
lean_inc(v_a_2130_);
lean_dec(v___x_2125_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2137_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
lean_object* v___x_2135_; 
if (v_isShared_2133_ == 0)
{
v___x_2135_ = v___x_2132_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v_a_2130_);
v___x_2135_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
return v___x_2135_;
}
}
}
}
else
{
lean_object* v___f_2138_; lean_object* v___x_2139_; 
lean_dec(v_a_2120_);
lean_dec(v_numIndices_2117_);
lean_dec_ref(v___x_2110_);
lean_dec(v_a_2089_);
lean_dec_ref(v_xs_2076_);
lean_dec_ref(v_fixedParamPerms_2075_);
lean_dec_ref(v_preDefs_2074_);
lean_inc(v_a_2087_);
v___f_2138_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__3___boxed), 10, 4);
lean_closure_set(v___f_2138_, 0, v_recArgInfos_2077_);
lean_closure_set(v___f_2138_, 1, v_a_2087_);
lean_closure_set(v___f_2138_, 2, v___x_2084_);
lean_closure_set(v___f_2138_, 3, v___f_2121_);
v___x_2139_ = l_Lean_Elab_Structural_withFunTypes___redArg(v_a_2087_, v___f_2138_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_);
return v___x_2139_;
}
}
else
{
lean_object* v_a_2140_; lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2147_; 
lean_dec(v_numIndices_2117_);
lean_dec_ref(v___x_2110_);
lean_dec(v_a_2089_);
lean_dec(v_a_2087_);
lean_dec_ref(v_recArgInfos_2077_);
lean_dec_ref(v_xs_2076_);
lean_dec_ref(v_fixedParamPerms_2075_);
lean_dec_ref(v_preDefs_2074_);
v_a_2140_ = lean_ctor_get(v___x_2119_, 0);
v_isSharedCheck_2147_ = !lean_is_exclusive(v___x_2119_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2142_ = v___x_2119_;
v_isShared_2143_ = v_isSharedCheck_2147_;
goto v_resetjp_2141_;
}
else
{
lean_inc(v_a_2140_);
lean_dec(v___x_2119_);
v___x_2142_ = lean_box(0);
v_isShared_2143_ = v_isSharedCheck_2147_;
goto v_resetjp_2141_;
}
v_resetjp_2141_:
{
lean_object* v___x_2145_; 
if (v_isShared_2143_ == 0)
{
v___x_2145_ = v___x_2142_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v_a_2140_);
v___x_2145_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
return v___x_2145_;
}
}
}
}
}
else
{
lean_object* v_a_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2179_; 
lean_del_object(v___x_2096_);
lean_dec(v_a_2089_);
lean_dec(v_a_2087_);
lean_dec_ref(v_recArgInfos_2077_);
lean_dec_ref(v_xs_2076_);
lean_dec_ref(v_fixedParamPerms_2075_);
lean_dec_ref(v_preDefs_2074_);
v_a_2172_ = lean_ctor_get(v___x_2100_, 0);
v_isSharedCheck_2179_ = !lean_is_exclusive(v___x_2100_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_2174_ = v___x_2100_;
v_isShared_2175_ = v_isSharedCheck_2179_;
goto v_resetjp_2173_;
}
else
{
lean_inc(v_a_2172_);
lean_dec(v___x_2100_);
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
}
else
{
lean_object* v_a_2182_; lean_object* v___x_2184_; uint8_t v_isShared_2185_; uint8_t v_isSharedCheck_2189_; 
lean_dec(v_a_2087_);
lean_dec_ref(v_recArgInfos_2077_);
lean_dec_ref(v_xs_2076_);
lean_dec_ref(v_fixedParamPerms_2075_);
lean_dec_ref(v_preDefs_2074_);
v_a_2182_ = lean_ctor_get(v___x_2088_, 0);
v_isSharedCheck_2189_ = !lean_is_exclusive(v___x_2088_);
if (v_isSharedCheck_2189_ == 0)
{
v___x_2184_ = v___x_2088_;
v_isShared_2185_ = v_isSharedCheck_2189_;
goto v_resetjp_2183_;
}
else
{
lean_inc(v_a_2182_);
lean_dec(v___x_2088_);
v___x_2184_ = lean_box(0);
v_isShared_2185_ = v_isSharedCheck_2189_;
goto v_resetjp_2183_;
}
v_resetjp_2183_:
{
lean_object* v___x_2187_; 
if (v_isShared_2185_ == 0)
{
v___x_2187_ = v___x_2184_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v_a_2182_);
v___x_2187_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
return v___x_2187_;
}
}
}
}
else
{
lean_object* v_a_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2197_; 
lean_dec_ref(v___x_2085_);
lean_dec_ref(v_recArgInfos_2077_);
lean_dec_ref(v_xs_2076_);
lean_dec_ref(v_fixedParamPerms_2075_);
lean_dec_ref(v_preDefs_2074_);
v_a_2190_ = lean_ctor_get(v___x_2086_, 0);
v_isSharedCheck_2197_ = !lean_is_exclusive(v___x_2086_);
if (v_isSharedCheck_2197_ == 0)
{
v___x_2192_ = v___x_2086_;
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_a_2190_);
lean_dec(v___x_2086_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___boxed(lean_object* v_preDefs_2198_, lean_object* v_fixedParamPerms_2199_, lean_object* v_xs_2200_, lean_object* v_recArgInfos_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_, lean_object* v_a_2205_, lean_object* v_a_2206_){
_start:
{
lean_object* v_res_2207_; 
v_res_2207_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion(v_preDefs_2198_, v_fixedParamPerms_2199_, v_xs_2200_, v_recArgInfos_2201_, v_a_2202_, v_a_2203_, v_a_2204_, v_a_2205_);
lean_dec(v_a_2205_);
lean_dec_ref(v_a_2204_);
lean_dec(v_a_2203_);
lean_dec_ref(v_a_2202_);
return v_res_2207_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2(lean_object* v_fixedParamPerms_2208_, lean_object* v_xs_2209_, lean_object* v_as_2210_, lean_object* v_i_2211_, lean_object* v_j_2212_, lean_object* v_inv_2213_, lean_object* v_bs_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_){
_start:
{
lean_object* v___x_2220_; 
v___x_2220_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___redArg(v_fixedParamPerms_2208_, v_xs_2209_, v_as_2210_, v_i_2211_, v_j_2212_, v_bs_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_);
return v___x_2220_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___boxed(lean_object* v_fixedParamPerms_2221_, lean_object* v_xs_2222_, lean_object* v_as_2223_, lean_object* v_i_2224_, lean_object* v_j_2225_, lean_object* v_inv_2226_, lean_object* v_bs_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_){
_start:
{
lean_object* v_res_2233_; 
v_res_2233_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2(v_fixedParamPerms_2221_, v_xs_2222_, v_as_2223_, v_i_2224_, v_j_2225_, v_inv_2226_, v_bs_2227_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_);
lean_dec(v___y_2231_);
lean_dec_ref(v___y_2230_);
lean_dec(v___y_2229_);
lean_dec_ref(v___y_2228_);
lean_dec_ref(v_as_2223_);
lean_dec_ref(v_fixedParamPerms_2221_);
return v_res_2233_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3(lean_object* v_fixedParamPerms_2234_, lean_object* v_xs_2235_, lean_object* v_as_2236_, lean_object* v_i_2237_, lean_object* v_j_2238_, lean_object* v_inv_2239_, lean_object* v_bs_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_){
_start:
{
lean_object* v___x_2246_; 
v___x_2246_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___redArg(v_fixedParamPerms_2234_, v_xs_2235_, v_as_2236_, v_i_2237_, v_j_2238_, v_bs_2240_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_);
return v___x_2246_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___boxed(lean_object* v_fixedParamPerms_2247_, lean_object* v_xs_2248_, lean_object* v_as_2249_, lean_object* v_i_2250_, lean_object* v_j_2251_, lean_object* v_inv_2252_, lean_object* v_bs_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_){
_start:
{
lean_object* v_res_2259_; 
v_res_2259_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3(v_fixedParamPerms_2247_, v_xs_2248_, v_as_2249_, v_i_2250_, v_j_2251_, v_inv_2252_, v_bs_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_);
lean_dec(v___y_2257_);
lean_dec_ref(v___y_2256_);
lean_dec(v___y_2255_);
lean_dec_ref(v___y_2254_);
lean_dec_ref(v_as_2249_);
lean_dec_ref(v_fixedParamPerms_2247_);
return v_res_2259_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14(lean_object* v_00_u03b3_2260_, lean_object* v_msg_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_){
_start:
{
lean_object* v___x_2267_; 
v___x_2267_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg(v_msg_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_);
return v___x_2267_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___boxed(lean_object* v_00_u03b3_2268_, lean_object* v_msg_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_){
_start:
{
lean_object* v_res_2275_; 
v_res_2275_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14(v_00_u03b3_2268_, v_msg_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_);
lean_dec(v___y_2273_);
lean_dec_ref(v___y_2272_);
lean_dec(v___y_2271_);
lean_dec_ref(v___y_2270_);
return v_res_2275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6(lean_object* v_00_u03b3_2276_, lean_object* v_00_u03b1_2277_, lean_object* v_f_2278_, lean_object* v_positions_2279_, lean_object* v_ys_2280_, lean_object* v_xs_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_){
_start:
{
lean_object* v___x_2287_; 
v___x_2287_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg(v_f_2278_, v_positions_2279_, v_ys_2280_, v_xs_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_);
return v___x_2287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___boxed(lean_object* v_00_u03b3_2288_, lean_object* v_00_u03b1_2289_, lean_object* v_f_2290_, lean_object* v_positions_2291_, lean_object* v_ys_2292_, lean_object* v_xs_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_){
_start:
{
lean_object* v_res_2299_; 
v_res_2299_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6(v_00_u03b3_2288_, v_00_u03b1_2289_, v_f_2290_, v_positions_2291_, v_ys_2292_, v_xs_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_);
lean_dec(v___y_2297_);
lean_dec_ref(v___y_2296_);
lean_dec(v___y_2295_);
lean_dec_ref(v___y_2294_);
lean_dec_ref(v_xs_2293_);
lean_dec_ref(v_ys_2292_);
lean_dec_ref(v_positions_2291_);
return v_res_2299_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7(lean_object* v___x_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_, lean_object* v_funTypes_2303_, lean_object* v_as_2304_, lean_object* v_i_2305_, lean_object* v_j_2306_, lean_object* v_inv_2307_, lean_object* v_bs_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_){
_start:
{
lean_object* v___x_2314_; 
v___x_2314_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg(v___x_2300_, v_a_2301_, v_a_2302_, v_funTypes_2303_, v_as_2304_, v_i_2305_, v_j_2306_, v_bs_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_);
return v___x_2314_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___boxed(lean_object* v___x_2315_, lean_object* v_a_2316_, lean_object* v_a_2317_, lean_object* v_funTypes_2318_, lean_object* v_as_2319_, lean_object* v_i_2320_, lean_object* v_j_2321_, lean_object* v_inv_2322_, lean_object* v_bs_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_){
_start:
{
lean_object* v_res_2329_; 
v_res_2329_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7(v___x_2315_, v_a_2316_, v_a_2317_, v_funTypes_2318_, v_as_2319_, v_i_2320_, v_j_2321_, v_inv_2322_, v_bs_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_);
lean_dec(v___y_2327_);
lean_dec_ref(v___y_2326_);
lean_dec(v___y_2325_);
lean_dec_ref(v___y_2324_);
lean_dec_ref(v_as_2319_);
return v_res_2329_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8(lean_object* v_fixedParamPerms_2330_, lean_object* v_xs_2331_, lean_object* v_as_2332_, lean_object* v_i_2333_, lean_object* v_j_2334_, lean_object* v_inv_2335_, lean_object* v_bs_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_){
_start:
{
lean_object* v___x_2342_; 
v___x_2342_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg(v_fixedParamPerms_2330_, v_xs_2331_, v_as_2332_, v_i_2333_, v_j_2334_, v_bs_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_);
return v___x_2342_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___boxed(lean_object* v_fixedParamPerms_2343_, lean_object* v_xs_2344_, lean_object* v_as_2345_, lean_object* v_i_2346_, lean_object* v_j_2347_, lean_object* v_inv_2348_, lean_object* v_bs_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_){
_start:
{
lean_object* v_res_2355_; 
v_res_2355_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8(v_fixedParamPerms_2343_, v_xs_2344_, v_as_2345_, v_i_2346_, v_j_2347_, v_inv_2348_, v_bs_2349_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_);
lean_dec(v___y_2353_);
lean_dec_ref(v___y_2352_);
lean_dec(v___y_2351_);
lean_dec_ref(v___y_2350_);
lean_dec_ref(v_as_2345_);
return v_res_2355_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12(lean_object* v_00_u03b1_2356_, lean_object* v_preDefs_2357_, lean_object* v_k_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_){
_start:
{
lean_object* v___x_2364_; 
v___x_2364_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v_preDefs_2357_, v_k_2358_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_);
return v___x_2364_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___boxed(lean_object* v_00_u03b1_2365_, lean_object* v_preDefs_2366_, lean_object* v_k_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_){
_start:
{
lean_object* v_res_2373_; 
v_res_2373_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12(v_00_u03b1_2365_, v_preDefs_2366_, v_k_2367_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_);
lean_dec(v___y_2371_);
lean_dec_ref(v___y_2370_);
lean_dec(v___y_2369_);
lean_dec_ref(v___y_2368_);
return v_res_2373_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14(uint8_t v_a_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_, lean_object* v_recArgInfos_2377_, lean_object* v___x_2378_, lean_object* v_preDefs_2379_, lean_object* v_a_2380_, lean_object* v_as_2381_, lean_object* v_i_2382_, lean_object* v_j_2383_, lean_object* v_inv_2384_, lean_object* v_bs_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_){
_start:
{
lean_object* v___x_2391_; 
v___x_2391_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg(v_a_2374_, v_a_2375_, v_a_2376_, v_recArgInfos_2377_, v___x_2378_, v_preDefs_2379_, v_a_2380_, v_as_2381_, v_i_2382_, v_j_2383_, v_bs_2385_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_);
return v___x_2391_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___boxed(lean_object** _args){
lean_object* v_a_2392_ = _args[0];
lean_object* v_a_2393_ = _args[1];
lean_object* v_a_2394_ = _args[2];
lean_object* v_recArgInfos_2395_ = _args[3];
lean_object* v___x_2396_ = _args[4];
lean_object* v_preDefs_2397_ = _args[5];
lean_object* v_a_2398_ = _args[6];
lean_object* v_as_2399_ = _args[7];
lean_object* v_i_2400_ = _args[8];
lean_object* v_j_2401_ = _args[9];
lean_object* v_inv_2402_ = _args[10];
lean_object* v_bs_2403_ = _args[11];
lean_object* v___y_2404_ = _args[12];
lean_object* v___y_2405_ = _args[13];
lean_object* v___y_2406_ = _args[14];
lean_object* v___y_2407_ = _args[15];
lean_object* v___y_2408_ = _args[16];
_start:
{
uint8_t v_a_30502__boxed_2409_; lean_object* v_res_2410_; 
v_a_30502__boxed_2409_ = lean_unbox(v_a_2392_);
v_res_2410_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14(v_a_30502__boxed_2409_, v_a_2393_, v_a_2394_, v_recArgInfos_2395_, v___x_2396_, v_preDefs_2397_, v_a_2398_, v_as_2399_, v_i_2400_, v_j_2401_, v_inv_2402_, v_bs_2403_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_);
lean_dec(v___y_2407_);
lean_dec_ref(v___y_2406_);
lean_dec(v___y_2405_);
lean_dec_ref(v___y_2404_);
lean_dec_ref(v_as_2399_);
lean_dec_ref(v_a_2394_);
lean_dec_ref(v_a_2393_);
return v_res_2410_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16_spec__29(lean_object* v_declName_2411_, uint8_t v_s_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_){
_start:
{
lean_object* v___x_2418_; 
v___x_2418_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16_spec__29___redArg(v_declName_2411_, v_s_2412_, v___y_2414_, v___y_2416_);
return v___x_2418_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16_spec__29___boxed(lean_object* v_declName_2419_, lean_object* v_s_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_){
_start:
{
uint8_t v_s_boxed_2426_; lean_object* v_res_2427_; 
v_s_boxed_2426_ = lean_unbox(v_s_2420_);
v_res_2427_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16_spec__29(v_declName_2419_, v_s_boxed_2426_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_);
lean_dec(v___y_2424_);
lean_dec_ref(v___y_2423_);
lean_dec(v___y_2422_);
lean_dec_ref(v___y_2421_);
return v_res_2427_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17(lean_object* v_xs_2428_, uint8_t v_a_2429_, lean_object* v_preDefs_2430_, lean_object* v___x_2431_, lean_object* v_as_2432_, lean_object* v_i_2433_, lean_object* v_j_2434_, lean_object* v_inv_2435_, lean_object* v_bs_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_){
_start:
{
lean_object* v___x_2442_; 
v___x_2442_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg(v_xs_2428_, v_a_2429_, v_preDefs_2430_, v___x_2431_, v_as_2432_, v_i_2433_, v_j_2434_, v_bs_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_);
return v___x_2442_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___boxed(lean_object* v_xs_2443_, lean_object* v_a_2444_, lean_object* v_preDefs_2445_, lean_object* v___x_2446_, lean_object* v_as_2447_, lean_object* v_i_2448_, lean_object* v_j_2449_, lean_object* v_inv_2450_, lean_object* v_bs_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_){
_start:
{
uint8_t v_a_30551__boxed_2457_; lean_object* v_res_2458_; 
v_a_30551__boxed_2457_ = lean_unbox(v_a_2444_);
v_res_2458_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17(v_xs_2443_, v_a_30551__boxed_2457_, v_preDefs_2445_, v___x_2446_, v_as_2447_, v_i_2448_, v_j_2449_, v_inv_2450_, v_bs_2451_, v___y_2452_, v___y_2453_, v___y_2454_, v___y_2455_);
lean_dec(v___y_2455_);
lean_dec_ref(v___y_2454_);
lean_dec(v___y_2453_);
lean_dec_ref(v___y_2452_);
lean_dec_ref(v_as_2447_);
lean_dec_ref(v_preDefs_2445_);
lean_dec_ref(v_xs_2443_);
return v_res_2458_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18(lean_object* v_a_2459_, lean_object* v_funTypes_2460_, lean_object* v_as_2461_, lean_object* v_i_2462_, lean_object* v_j_2463_, lean_object* v_inv_2464_, lean_object* v_bs_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_){
_start:
{
lean_object* v___x_2471_; 
v___x_2471_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___redArg(v_a_2459_, v_funTypes_2460_, v_as_2461_, v_i_2462_, v_j_2463_, v_bs_2465_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_);
return v___x_2471_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___boxed(lean_object* v_a_2472_, lean_object* v_funTypes_2473_, lean_object* v_as_2474_, lean_object* v_i_2475_, lean_object* v_j_2476_, lean_object* v_inv_2477_, lean_object* v_bs_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_){
_start:
{
lean_object* v_res_2484_; 
v_res_2484_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18(v_a_2472_, v_funTypes_2473_, v_as_2474_, v_i_2475_, v_j_2476_, v_inv_2477_, v_bs_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_);
lean_dec(v___y_2482_);
lean_dec_ref(v___y_2481_);
lean_dec(v___y_2480_);
lean_dec_ref(v___y_2479_);
lean_dec_ref(v_as_2474_);
lean_dec_ref(v_funTypes_2473_);
lean_dec_ref(v_a_2472_);
return v_res_2484_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19(lean_object* v_a_2485_, lean_object* v_a_2486_, lean_object* v_as_2487_, lean_object* v_i_2488_, lean_object* v_j_2489_, lean_object* v_inv_2490_, lean_object* v_bs_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_){
_start:
{
lean_object* v___x_2497_; 
v___x_2497_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___redArg(v_a_2485_, v_a_2486_, v_as_2487_, v_i_2488_, v_j_2489_, v_bs_2491_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_);
return v___x_2497_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___boxed(lean_object* v_a_2498_, lean_object* v_a_2499_, lean_object* v_as_2500_, lean_object* v_i_2501_, lean_object* v_j_2502_, lean_object* v_inv_2503_, lean_object* v_bs_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_){
_start:
{
lean_object* v_res_2510_; 
v_res_2510_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19(v_a_2498_, v_a_2499_, v_as_2500_, v_i_2501_, v_j_2502_, v_inv_2503_, v_bs_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_);
lean_dec(v___y_2508_);
lean_dec_ref(v___y_2507_);
lean_dec(v___y_2506_);
lean_dec_ref(v___y_2505_);
lean_dec_ref(v_as_2500_);
lean_dec_ref(v_a_2499_);
lean_dec_ref(v_a_2498_);
return v_res_2510_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4(lean_object* v_00_u03b1_2511_, lean_object* v_msg_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_){
_start:
{
lean_object* v___x_2518_; 
v___x_2518_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg(v_msg_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_);
return v___x_2518_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___boxed(lean_object* v_00_u03b1_2519_, lean_object* v_msg_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_){
_start:
{
lean_object* v_res_2526_; 
v_res_2526_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4(v_00_u03b1_2519_, v_msg_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_);
lean_dec(v___y_2524_);
lean_dec_ref(v___y_2523_);
lean_dec(v___y_2522_);
lean_dec_ref(v___y_2521_);
return v_res_2526_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9(lean_object* v_xs_2527_, lean_object* v_ys_2528_, lean_object* v_hsz_2529_, lean_object* v_x_2530_, lean_object* v_x_2531_){
_start:
{
uint8_t v___x_2532_; 
v___x_2532_ = l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9___redArg(v_xs_2527_, v_ys_2528_, v_x_2530_);
return v___x_2532_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9___boxed(lean_object* v_xs_2533_, lean_object* v_ys_2534_, lean_object* v_hsz_2535_, lean_object* v_x_2536_, lean_object* v_x_2537_){
_start:
{
uint8_t v_res_2538_; lean_object* v_r_2539_; 
v_res_2538_ = l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9(v_xs_2533_, v_ys_2534_, v_hsz_2535_, v_x_2536_, v_x_2537_);
lean_dec_ref(v_ys_2534_);
lean_dec_ref(v_xs_2533_);
v_r_2539_ = lean_box(v_res_2538_);
return v_r_2539_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10(lean_object* v_n_2540_, lean_object* v_as_2541_, lean_object* v_lo_2542_, lean_object* v_hi_2543_, lean_object* v_w_2544_, lean_object* v_hlo_2545_, lean_object* v_hhi_2546_){
_start:
{
lean_object* v___x_2547_; 
v___x_2547_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg(v_n_2540_, v_as_2541_, v_lo_2542_, v_hi_2543_);
return v___x_2547_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___boxed(lean_object* v_n_2548_, lean_object* v_as_2549_, lean_object* v_lo_2550_, lean_object* v_hi_2551_, lean_object* v_w_2552_, lean_object* v_hlo_2553_, lean_object* v_hhi_2554_){
_start:
{
lean_object* v_res_2555_; 
v_res_2555_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10(v_n_2548_, v_as_2549_, v_lo_2550_, v_hi_2551_, v_w_2552_, v_hlo_2553_, v_hhi_2554_);
lean_dec(v_hi_2551_);
lean_dec(v_n_2548_);
return v_res_2555_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15(lean_object* v_00_u03b1_2556_, lean_object* v_00_u03b3_2557_, lean_object* v_xs_2558_, lean_object* v_f_2559_, lean_object* v_as_2560_, lean_object* v_bs_2561_, lean_object* v_i_2562_, lean_object* v_cs_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_){
_start:
{
lean_object* v___x_2569_; 
v___x_2569_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15___redArg(v_xs_2558_, v_f_2559_, v_as_2560_, v_bs_2561_, v_i_2562_, v_cs_2563_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_);
return v___x_2569_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15___boxed(lean_object* v_00_u03b1_2570_, lean_object* v_00_u03b3_2571_, lean_object* v_xs_2572_, lean_object* v_f_2573_, lean_object* v_as_2574_, lean_object* v_bs_2575_, lean_object* v_i_2576_, lean_object* v_cs_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_){
_start:
{
lean_object* v_res_2583_; 
v_res_2583_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15(v_00_u03b1_2570_, v_00_u03b3_2571_, v_xs_2572_, v_f_2573_, v_as_2574_, v_bs_2575_, v_i_2576_, v_cs_2577_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_);
lean_dec(v___y_2581_);
lean_dec_ref(v___y_2580_);
lean_dec(v___y_2579_);
lean_dec_ref(v___y_2578_);
lean_dec_ref(v_bs_2575_);
lean_dec_ref(v_as_2574_);
lean_dec_ref(v_xs_2572_);
return v_res_2583_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25(lean_object* v_env_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_){
_start:
{
lean_object* v___x_2590_; 
v___x_2590_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg(v_env_2584_, v___y_2586_, v___y_2588_);
return v___x_2590_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___boxed(lean_object* v_env_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_){
_start:
{
lean_object* v_res_2597_; 
v_res_2597_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25(v_env_2591_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_);
lean_dec(v___y_2595_);
lean_dec_ref(v___y_2594_);
lean_dec(v___y_2593_);
lean_dec_ref(v___y_2592_);
return v_res_2597_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23(lean_object* v_00_u03b1_2598_, lean_object* v_env_2599_, lean_object* v_x_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_){
_start:
{
lean_object* v___x_2606_; 
v___x_2606_ = l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23___redArg(v_env_2599_, v_x_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_);
return v___x_2606_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23___boxed(lean_object* v_00_u03b1_2607_, lean_object* v_env_2608_, lean_object* v_x_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_){
_start:
{
lean_object* v_res_2615_; 
v_res_2615_ = l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23(v_00_u03b1_2607_, v_env_2608_, v_x_2609_, v___y_2610_, v___y_2611_, v___y_2612_, v___y_2613_);
lean_dec(v___y_2613_);
lean_dec_ref(v___y_2612_);
lean_dec(v___y_2611_);
lean_dec_ref(v___y_2610_);
return v_res_2615_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11(lean_object* v_n_2616_, lean_object* v_lo_2617_, lean_object* v_hi_2618_, lean_object* v_hhi_2619_, lean_object* v_pivot_2620_, lean_object* v_as_2621_, lean_object* v_i_2622_, lean_object* v_k_2623_, lean_object* v_ilo_2624_, lean_object* v_ik_2625_, lean_object* v_w_2626_){
_start:
{
lean_object* v___x_2627_; 
v___x_2627_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11___redArg(v_hi_2618_, v_pivot_2620_, v_as_2621_, v_i_2622_, v_k_2623_);
return v___x_2627_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11___boxed(lean_object* v_n_2628_, lean_object* v_lo_2629_, lean_object* v_hi_2630_, lean_object* v_hhi_2631_, lean_object* v_pivot_2632_, lean_object* v_as_2633_, lean_object* v_i_2634_, lean_object* v_k_2635_, lean_object* v_ilo_2636_, lean_object* v_ik_2637_, lean_object* v_w_2638_){
_start:
{
lean_object* v_res_2639_; 
v_res_2639_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11(v_n_2628_, v_lo_2629_, v_hi_2630_, v_hhi_2631_, v_pivot_2632_, v_as_2633_, v_i_2634_, v_k_2635_, v_ilo_2636_, v_ik_2637_, v_w_2638_);
lean_dec(v_pivot_2632_);
lean_dec(v_hi_2630_);
lean_dec(v_lo_2629_);
lean_dec(v_n_2628_);
return v_res_2639_;
}
}
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___lam__0(lean_object* v_x_2640_){
_start:
{
uint8_t v___x_2641_; 
v___x_2641_ = 0;
return v___x_2641_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___lam__0___boxed(lean_object* v_x_2642_){
_start:
{
uint8_t v_res_2643_; lean_object* v_r_2644_; 
v_res_2643_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___lam__0(v_x_2642_);
lean_dec(v_x_2642_);
v_r_2644_ = lean_box(v_res_2643_);
return v_r_2644_;
}
}
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___lam__1(lean_object* v_fvarId_2645_, lean_object* v_x_2646_){
_start:
{
uint8_t v___x_2647_; 
v___x_2647_ = l_Lean_instBEqFVarId_beq(v_fvarId_2645_, v_x_2646_);
return v___x_2647_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___lam__1___boxed(lean_object* v_fvarId_2648_, lean_object* v_x_2649_){
_start:
{
uint8_t v_res_2650_; lean_object* v_r_2651_; 
v_res_2650_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___lam__1(v_fvarId_2648_, v_x_2649_);
lean_dec(v_x_2649_);
lean_dec(v_fvarId_2648_);
v_r_2651_ = lean_box(v_res_2650_);
return v_r_2651_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; 
v___x_2653_ = lean_box(0);
v___x_2654_ = lean_unsigned_to_nat(16u);
v___x_2655_ = lean_mk_array(v___x_2654_, v___x_2653_);
return v___x_2655_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; 
v___x_2656_ = lean_obj_once(&l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__1, &l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__1_once, _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__1);
v___x_2657_ = lean_unsigned_to_nat(0u);
v___x_2658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2658_, 0, v___x_2657_);
lean_ctor_set(v___x_2658_, 1, v___x_2656_);
return v___x_2658_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg(lean_object* v_e_2659_, lean_object* v_fvarId_2660_, lean_object* v___y_2661_){
_start:
{
lean_object* v___x_2663_; uint8_t v_fst_2665_; lean_object* v_mctx_2666_; lean_object* v___y_2684_; lean_object* v_mctx_2689_; lean_object* v___f_2690_; lean_object* v___f_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; uint8_t v___x_2694_; 
v___x_2663_ = lean_st_ref_get(v___y_2661_);
v_mctx_2689_ = lean_ctor_get(v___x_2663_, 0);
lean_inc_ref_n(v_mctx_2689_, 2);
lean_dec(v___x_2663_);
v___f_2690_ = ((lean_object*)(l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__0));
v___f_2691_ = lean_alloc_closure((void*)(l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_2691_, 0, v_fvarId_2660_);
v___x_2692_ = lean_obj_once(&l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__2, &l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__2_once, _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__2);
v___x_2693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2693_, 0, v___x_2692_);
lean_ctor_set(v___x_2693_, 1, v_mctx_2689_);
v___x_2694_ = l_Lean_Expr_hasFVar(v_e_2659_);
if (v___x_2694_ == 0)
{
uint8_t v___x_2695_; 
v___x_2695_ = l_Lean_Expr_hasMVar(v_e_2659_);
if (v___x_2695_ == 0)
{
lean_dec_ref(v___x_2693_);
lean_dec_ref(v___f_2691_);
lean_dec_ref(v_e_2659_);
v_fst_2665_ = v___x_2695_;
v_mctx_2666_ = v_mctx_2689_;
goto v___jp_2664_;
}
else
{
lean_object* v___x_2696_; 
lean_dec_ref(v_mctx_2689_);
v___x_2696_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2691_, v___f_2690_, v_e_2659_, v___x_2693_);
v___y_2684_ = v___x_2696_;
goto v___jp_2683_;
}
}
else
{
lean_object* v___x_2697_; 
lean_dec_ref(v_mctx_2689_);
v___x_2697_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2691_, v___f_2690_, v_e_2659_, v___x_2693_);
v___y_2684_ = v___x_2697_;
goto v___jp_2683_;
}
v___jp_2664_:
{
lean_object* v___x_2667_; lean_object* v_cache_2668_; lean_object* v_zetaDeltaFVarIds_2669_; lean_object* v_postponed_2670_; lean_object* v_diag_2671_; lean_object* v___x_2673_; uint8_t v_isShared_2674_; uint8_t v_isSharedCheck_2681_; 
v___x_2667_ = lean_st_ref_take(v___y_2661_);
v_cache_2668_ = lean_ctor_get(v___x_2667_, 1);
v_zetaDeltaFVarIds_2669_ = lean_ctor_get(v___x_2667_, 2);
v_postponed_2670_ = lean_ctor_get(v___x_2667_, 3);
v_diag_2671_ = lean_ctor_get(v___x_2667_, 4);
v_isSharedCheck_2681_ = !lean_is_exclusive(v___x_2667_);
if (v_isSharedCheck_2681_ == 0)
{
lean_object* v_unused_2682_; 
v_unused_2682_ = lean_ctor_get(v___x_2667_, 0);
lean_dec(v_unused_2682_);
v___x_2673_ = v___x_2667_;
v_isShared_2674_ = v_isSharedCheck_2681_;
goto v_resetjp_2672_;
}
else
{
lean_inc(v_diag_2671_);
lean_inc(v_postponed_2670_);
lean_inc(v_zetaDeltaFVarIds_2669_);
lean_inc(v_cache_2668_);
lean_dec(v___x_2667_);
v___x_2673_ = lean_box(0);
v_isShared_2674_ = v_isSharedCheck_2681_;
goto v_resetjp_2672_;
}
v_resetjp_2672_:
{
lean_object* v___x_2676_; 
if (v_isShared_2674_ == 0)
{
lean_ctor_set(v___x_2673_, 0, v_mctx_2666_);
v___x_2676_ = v___x_2673_;
goto v_reusejp_2675_;
}
else
{
lean_object* v_reuseFailAlloc_2680_; 
v_reuseFailAlloc_2680_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2680_, 0, v_mctx_2666_);
lean_ctor_set(v_reuseFailAlloc_2680_, 1, v_cache_2668_);
lean_ctor_set(v_reuseFailAlloc_2680_, 2, v_zetaDeltaFVarIds_2669_);
lean_ctor_set(v_reuseFailAlloc_2680_, 3, v_postponed_2670_);
lean_ctor_set(v_reuseFailAlloc_2680_, 4, v_diag_2671_);
v___x_2676_ = v_reuseFailAlloc_2680_;
goto v_reusejp_2675_;
}
v_reusejp_2675_:
{
lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; 
v___x_2677_ = lean_st_ref_set(v___y_2661_, v___x_2676_);
v___x_2678_ = lean_box(v_fst_2665_);
v___x_2679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2679_, 0, v___x_2678_);
return v___x_2679_;
}
}
}
v___jp_2683_:
{
lean_object* v_snd_2685_; lean_object* v_fst_2686_; lean_object* v_mctx_2687_; uint8_t v___x_2688_; 
v_snd_2685_ = lean_ctor_get(v___y_2684_, 1);
lean_inc(v_snd_2685_);
v_fst_2686_ = lean_ctor_get(v___y_2684_, 0);
lean_inc(v_fst_2686_);
lean_dec_ref(v___y_2684_);
v_mctx_2687_ = lean_ctor_get(v_snd_2685_, 1);
lean_inc_ref(v_mctx_2687_);
lean_dec(v_snd_2685_);
v___x_2688_ = lean_unbox(v_fst_2686_);
lean_dec(v_fst_2686_);
v_fst_2665_ = v___x_2688_;
v_mctx_2666_ = v_mctx_2687_;
goto v___jp_2664_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___boxed(lean_object* v_e_2698_, lean_object* v_fvarId_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_){
_start:
{
lean_object* v_res_2702_; 
v_res_2702_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg(v_e_2698_, v_fvarId_2699_, v___y_2700_);
lean_dec(v___y_2700_);
return v_res_2702_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5(lean_object* v_e_2703_, lean_object* v_fvarId_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_){
_start:
{
lean_object* v___x_2710_; 
v___x_2710_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg(v_e_2703_, v_fvarId_2704_, v___y_2706_);
return v___x_2710_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___boxed(lean_object* v_e_2711_, lean_object* v_fvarId_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_){
_start:
{
lean_object* v_res_2718_; 
v_res_2718_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5(v_e_2711_, v_fvarId_2712_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_);
lean_dec(v___y_2716_);
lean_dec_ref(v___y_2715_);
lean_dec(v___y_2714_);
lean_dec_ref(v___y_2713_);
return v_res_2718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg___lam__0(lean_object* v_k_2719_, lean_object* v_b_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_){
_start:
{
lean_object* v___x_2726_; 
lean_inc(v___y_2724_);
lean_inc_ref(v___y_2723_);
lean_inc(v___y_2722_);
lean_inc_ref(v___y_2721_);
v___x_2726_ = lean_apply_6(v_k_2719_, v_b_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_, lean_box(0));
return v___x_2726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg___lam__0___boxed(lean_object* v_k_2727_, lean_object* v_b_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_){
_start:
{
lean_object* v_res_2734_; 
v_res_2734_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg___lam__0(v_k_2727_, v_b_2728_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_);
lean_dec(v___y_2732_);
lean_dec_ref(v___y_2731_);
lean_dec(v___y_2730_);
lean_dec_ref(v___y_2729_);
return v_res_2734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg(lean_object* v_perm_2735_, lean_object* v_type_2736_, lean_object* v_k_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_){
_start:
{
lean_object* v___f_2743_; lean_object* v___x_2744_; 
v___f_2743_ = lean_alloc_closure((void*)(l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2743_, 0, v_k_2737_);
v___x_2744_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl(lean_box(0), v_perm_2735_, v_type_2736_, v___f_2743_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_);
if (lean_obj_tag(v___x_2744_) == 0)
{
lean_object* v_a_2745_; lean_object* v___x_2747_; uint8_t v_isShared_2748_; uint8_t v_isSharedCheck_2752_; 
v_a_2745_ = lean_ctor_get(v___x_2744_, 0);
v_isSharedCheck_2752_ = !lean_is_exclusive(v___x_2744_);
if (v_isSharedCheck_2752_ == 0)
{
v___x_2747_ = v___x_2744_;
v_isShared_2748_ = v_isSharedCheck_2752_;
goto v_resetjp_2746_;
}
else
{
lean_inc(v_a_2745_);
lean_dec(v___x_2744_);
v___x_2747_ = lean_box(0);
v_isShared_2748_ = v_isSharedCheck_2752_;
goto v_resetjp_2746_;
}
v_resetjp_2746_:
{
lean_object* v___x_2750_; 
if (v_isShared_2748_ == 0)
{
v___x_2750_ = v___x_2747_;
goto v_reusejp_2749_;
}
else
{
lean_object* v_reuseFailAlloc_2751_; 
v_reuseFailAlloc_2751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2751_, 0, v_a_2745_);
v___x_2750_ = v_reuseFailAlloc_2751_;
goto v_reusejp_2749_;
}
v_reusejp_2749_:
{
return v___x_2750_;
}
}
}
else
{
lean_object* v_a_2753_; lean_object* v___x_2755_; uint8_t v_isShared_2756_; uint8_t v_isSharedCheck_2760_; 
v_a_2753_ = lean_ctor_get(v___x_2744_, 0);
v_isSharedCheck_2760_ = !lean_is_exclusive(v___x_2744_);
if (v_isSharedCheck_2760_ == 0)
{
v___x_2755_ = v___x_2744_;
v_isShared_2756_ = v_isSharedCheck_2760_;
goto v_resetjp_2754_;
}
else
{
lean_inc(v_a_2753_);
lean_dec(v___x_2744_);
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
v_reuseFailAlloc_2759_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg___boxed(lean_object* v_perm_2761_, lean_object* v_type_2762_, lean_object* v_k_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_){
_start:
{
lean_object* v_res_2769_; 
v_res_2769_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg(v_perm_2761_, v_type_2762_, v_k_2763_, v___y_2764_, v___y_2765_, v___y_2766_, v___y_2767_);
lean_dec(v___y_2767_);
lean_dec_ref(v___y_2766_);
lean_dec(v___y_2765_);
lean_dec_ref(v___y_2764_);
return v_res_2769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13(lean_object* v_00_u03b1_2770_, lean_object* v_perm_2771_, lean_object* v_type_2772_, lean_object* v_k_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_){
_start:
{
lean_object* v___x_2779_; 
v___x_2779_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg(v_perm_2771_, v_type_2772_, v_k_2773_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_);
return v___x_2779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___boxed(lean_object* v_00_u03b1_2780_, lean_object* v_perm_2781_, lean_object* v_type_2782_, lean_object* v_k_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_){
_start:
{
lean_object* v_res_2789_; 
v_res_2789_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13(v_00_u03b1_2780_, v_perm_2781_, v_type_2782_, v_k_2783_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_);
lean_dec(v___y_2787_);
lean_dec_ref(v___y_2786_);
lean_dec(v___y_2785_);
lean_dec_ref(v___y_2784_);
return v_res_2789_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1(lean_object* v_a_2790_, lean_object* v_fst_2791_, lean_object* v_fst_2792_, lean_object* v___x_2793_, lean_object* v___x_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_){
_start:
{
lean_object* v___x_2800_; 
lean_inc_ref(v_fst_2791_);
v___x_2800_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion(v_a_2790_, v_fst_2791_, v_fst_2792_, v___x_2793_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_);
if (lean_obj_tag(v___x_2800_) == 0)
{
lean_object* v_a_2801_; lean_object* v___x_2803_; uint8_t v_isShared_2804_; uint8_t v_isSharedCheck_2810_; 
v_a_2801_ = lean_ctor_get(v___x_2800_, 0);
v_isSharedCheck_2810_ = !lean_is_exclusive(v___x_2800_);
if (v_isSharedCheck_2810_ == 0)
{
v___x_2803_ = v___x_2800_;
v_isShared_2804_ = v_isSharedCheck_2810_;
goto v_resetjp_2802_;
}
else
{
lean_inc(v_a_2801_);
lean_dec(v___x_2800_);
v___x_2803_ = lean_box(0);
v_isShared_2804_ = v_isSharedCheck_2810_;
goto v_resetjp_2802_;
}
v_resetjp_2802_:
{
lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2808_; 
v___x_2805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2805_, 0, v_a_2801_);
lean_ctor_set(v___x_2805_, 1, v_fst_2791_);
v___x_2806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2806_, 0, v___x_2794_);
lean_ctor_set(v___x_2806_, 1, v___x_2805_);
if (v_isShared_2804_ == 0)
{
lean_ctor_set(v___x_2803_, 0, v___x_2806_);
v___x_2808_ = v___x_2803_;
goto v_reusejp_2807_;
}
else
{
lean_object* v_reuseFailAlloc_2809_; 
v_reuseFailAlloc_2809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2809_, 0, v___x_2806_);
v___x_2808_ = v_reuseFailAlloc_2809_;
goto v_reusejp_2807_;
}
v_reusejp_2807_:
{
return v___x_2808_;
}
}
}
else
{
lean_object* v_a_2811_; lean_object* v___x_2813_; uint8_t v_isShared_2814_; uint8_t v_isSharedCheck_2818_; 
lean_dec_ref(v___x_2794_);
lean_dec_ref(v_fst_2791_);
v_a_2811_ = lean_ctor_get(v___x_2800_, 0);
v_isSharedCheck_2818_ = !lean_is_exclusive(v___x_2800_);
if (v_isSharedCheck_2818_ == 0)
{
v___x_2813_ = v___x_2800_;
v_isShared_2814_ = v_isSharedCheck_2818_;
goto v_resetjp_2812_;
}
else
{
lean_inc(v_a_2811_);
lean_dec(v___x_2800_);
v___x_2813_ = lean_box(0);
v_isShared_2814_ = v_isSharedCheck_2818_;
goto v_resetjp_2812_;
}
v_resetjp_2812_:
{
lean_object* v___x_2816_; 
if (v_isShared_2814_ == 0)
{
v___x_2816_ = v___x_2813_;
goto v_reusejp_2815_;
}
else
{
lean_object* v_reuseFailAlloc_2817_; 
v_reuseFailAlloc_2817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2817_, 0, v_a_2811_);
v___x_2816_ = v_reuseFailAlloc_2817_;
goto v_reusejp_2815_;
}
v_reusejp_2815_:
{
return v___x_2816_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___boxed(lean_object* v_a_2819_, lean_object* v_fst_2820_, lean_object* v_fst_2821_, lean_object* v___x_2822_, lean_object* v___x_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_){
_start:
{
lean_object* v_res_2829_; 
v_res_2829_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1(v_a_2819_, v_fst_2820_, v_fst_2821_, v___x_2822_, v___x_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_);
lean_dec(v___y_2827_);
lean_dec_ref(v___y_2826_);
lean_dec(v___y_2825_);
lean_dec_ref(v___y_2824_);
return v_res_2829_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__3(size_t v_sz_2830_, size_t v_i_2831_, lean_object* v_bs_2832_){
_start:
{
uint8_t v___x_2833_; 
v___x_2833_ = lean_usize_dec_lt(v_i_2831_, v_sz_2830_);
if (v___x_2833_ == 0)
{
return v_bs_2832_;
}
else
{
lean_object* v_v_2834_; lean_object* v___x_2835_; lean_object* v_bs_x27_2836_; lean_object* v___x_2837_; size_t v___x_2838_; size_t v___x_2839_; lean_object* v___x_2840_; 
v_v_2834_ = lean_array_uget(v_bs_2832_, v_i_2831_);
v___x_2835_ = lean_unsigned_to_nat(0u);
v_bs_x27_2836_ = lean_array_uset(v_bs_2832_, v_i_2831_, v___x_2835_);
v___x_2837_ = l_Lean_Elab_Structural_RecArgInfo_indicesAndRecArgPos(v_v_2834_);
v___x_2838_ = ((size_t)1ULL);
v___x_2839_ = lean_usize_add(v_i_2831_, v___x_2838_);
v___x_2840_ = lean_array_uset(v_bs_x27_2836_, v_i_2831_, v___x_2837_);
v_i_2831_ = v___x_2839_;
v_bs_2832_ = v___x_2840_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__3___boxed(lean_object* v_sz_2842_, lean_object* v_i_2843_, lean_object* v_bs_2844_){
_start:
{
size_t v_sz_boxed_2845_; size_t v_i_boxed_2846_; lean_object* v_res_2847_; 
v_sz_boxed_2845_ = lean_unbox_usize(v_sz_2842_);
lean_dec(v_sz_2842_);
v_i_boxed_2846_ = lean_unbox_usize(v_i_2843_);
lean_dec(v_i_2843_);
v_res_2847_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__3(v_sz_boxed_2845_, v_i_boxed_2846_, v_bs_2844_);
return v_res_2847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___redArg(lean_object* v_lctx_2848_, lean_object* v_localInsts_2849_, lean_object* v_x_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_){
_start:
{
lean_object* v___x_2856_; 
v___x_2856_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_2848_, v_localInsts_2849_, v_x_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_);
if (lean_obj_tag(v___x_2856_) == 0)
{
lean_object* v_a_2857_; lean_object* v___x_2859_; uint8_t v_isShared_2860_; uint8_t v_isSharedCheck_2864_; 
v_a_2857_ = lean_ctor_get(v___x_2856_, 0);
v_isSharedCheck_2864_ = !lean_is_exclusive(v___x_2856_);
if (v_isSharedCheck_2864_ == 0)
{
v___x_2859_ = v___x_2856_;
v_isShared_2860_ = v_isSharedCheck_2864_;
goto v_resetjp_2858_;
}
else
{
lean_inc(v_a_2857_);
lean_dec(v___x_2856_);
v___x_2859_ = lean_box(0);
v_isShared_2860_ = v_isSharedCheck_2864_;
goto v_resetjp_2858_;
}
v_resetjp_2858_:
{
lean_object* v___x_2862_; 
if (v_isShared_2860_ == 0)
{
v___x_2862_ = v___x_2859_;
goto v_reusejp_2861_;
}
else
{
lean_object* v_reuseFailAlloc_2863_; 
v_reuseFailAlloc_2863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2863_, 0, v_a_2857_);
v___x_2862_ = v_reuseFailAlloc_2863_;
goto v_reusejp_2861_;
}
v_reusejp_2861_:
{
return v___x_2862_;
}
}
}
else
{
lean_object* v_a_2865_; lean_object* v___x_2867_; uint8_t v_isShared_2868_; uint8_t v_isSharedCheck_2872_; 
v_a_2865_ = lean_ctor_get(v___x_2856_, 0);
v_isSharedCheck_2872_ = !lean_is_exclusive(v___x_2856_);
if (v_isSharedCheck_2872_ == 0)
{
v___x_2867_ = v___x_2856_;
v_isShared_2868_ = v_isSharedCheck_2872_;
goto v_resetjp_2866_;
}
else
{
lean_inc(v_a_2865_);
lean_dec(v___x_2856_);
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
v_reuseFailAlloc_2871_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___redArg___boxed(lean_object* v_lctx_2873_, lean_object* v_localInsts_2874_, lean_object* v_x_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_){
_start:
{
lean_object* v_res_2881_; 
v_res_2881_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___redArg(v_lctx_2873_, v_localInsts_2874_, v_x_2875_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_);
lean_dec(v___y_2879_);
lean_dec_ref(v___y_2878_);
lean_dec(v___y_2877_);
lean_dec_ref(v___y_2876_);
return v_res_2881_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__12(lean_object* v_as_2882_, size_t v_i_2883_, size_t v_stop_2884_, lean_object* v_b_2885_){
_start:
{
uint8_t v___x_2886_; 
v___x_2886_ = lean_usize_dec_eq(v_i_2883_, v_stop_2884_);
if (v___x_2886_ == 0)
{
lean_object* v___x_2887_; lean_object* v___x_2888_; size_t v___x_2889_; size_t v___x_2890_; 
v___x_2887_ = lean_array_uget_borrowed(v_as_2882_, v_i_2883_);
lean_inc(v___x_2887_);
v___x_2888_ = lean_local_ctx_erase(v_b_2885_, v___x_2887_);
v___x_2889_ = ((size_t)1ULL);
v___x_2890_ = lean_usize_add(v_i_2883_, v___x_2889_);
v_i_2883_ = v___x_2890_;
v_b_2885_ = v___x_2888_;
goto _start;
}
else
{
return v_b_2885_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__12___boxed(lean_object* v_as_2892_, lean_object* v_i_2893_, lean_object* v_stop_2894_, lean_object* v_b_2895_){
_start:
{
size_t v_i_boxed_2896_; size_t v_stop_boxed_2897_; lean_object* v_res_2898_; 
v_i_boxed_2896_ = lean_unbox_usize(v_i_2893_);
lean_dec(v_i_2893_);
v_stop_boxed_2897_ = lean_unbox_usize(v_stop_2894_);
lean_dec(v_stop_2894_);
v_res_2898_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__12(v_as_2892_, v_i_boxed_2896_, v_stop_boxed_2897_, v_b_2895_);
lean_dec_ref(v_as_2892_);
return v_res_2898_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9_spec__11(lean_object* v_a_2899_, lean_object* v_as_2900_, size_t v_i_2901_, size_t v_stop_2902_){
_start:
{
uint8_t v___x_2903_; 
v___x_2903_ = lean_usize_dec_eq(v_i_2901_, v_stop_2902_);
if (v___x_2903_ == 0)
{
lean_object* v___x_2904_; uint8_t v___x_2905_; 
v___x_2904_ = lean_array_uget_borrowed(v_as_2900_, v_i_2901_);
v___x_2905_ = l_Lean_instBEqFVarId_beq(v_a_2899_, v___x_2904_);
if (v___x_2905_ == 0)
{
size_t v___x_2906_; size_t v___x_2907_; 
v___x_2906_ = ((size_t)1ULL);
v___x_2907_ = lean_usize_add(v_i_2901_, v___x_2906_);
v_i_2901_ = v___x_2907_;
goto _start;
}
else
{
return v___x_2905_;
}
}
else
{
uint8_t v___x_2909_; 
v___x_2909_ = 0;
return v___x_2909_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9_spec__11___boxed(lean_object* v_a_2910_, lean_object* v_as_2911_, lean_object* v_i_2912_, lean_object* v_stop_2913_){
_start:
{
size_t v_i_boxed_2914_; size_t v_stop_boxed_2915_; uint8_t v_res_2916_; lean_object* v_r_2917_; 
v_i_boxed_2914_ = lean_unbox_usize(v_i_2912_);
lean_dec(v_i_2912_);
v_stop_boxed_2915_ = lean_unbox_usize(v_stop_2913_);
lean_dec(v_stop_2913_);
v_res_2916_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9_spec__11(v_a_2910_, v_as_2911_, v_i_boxed_2914_, v_stop_boxed_2915_);
lean_dec_ref(v_as_2911_);
lean_dec(v_a_2910_);
v_r_2917_ = lean_box(v_res_2916_);
return v_r_2917_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9(lean_object* v_as_2918_, lean_object* v_a_2919_){
_start:
{
lean_object* v___x_2920_; lean_object* v___x_2921_; uint8_t v___x_2922_; 
v___x_2920_ = lean_unsigned_to_nat(0u);
v___x_2921_ = lean_array_get_size(v_as_2918_);
v___x_2922_ = lean_nat_dec_lt(v___x_2920_, v___x_2921_);
if (v___x_2922_ == 0)
{
return v___x_2922_;
}
else
{
if (v___x_2922_ == 0)
{
return v___x_2922_;
}
else
{
size_t v___x_2923_; size_t v___x_2924_; uint8_t v___x_2925_; 
v___x_2923_ = ((size_t)0ULL);
v___x_2924_ = lean_usize_of_nat(v___x_2921_);
v___x_2925_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9_spec__11(v_a_2919_, v_as_2918_, v___x_2923_, v___x_2924_);
return v___x_2925_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9___boxed(lean_object* v_as_2926_, lean_object* v_a_2927_){
_start:
{
uint8_t v_res_2928_; lean_object* v_r_2929_; 
v_res_2928_ = l_Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9(v_as_2926_, v_a_2927_);
lean_dec(v_a_2927_);
lean_dec_ref(v_as_2926_);
v_r_2929_ = lean_box(v_res_2928_);
return v_r_2929_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__11(lean_object* v_fvarIds_2930_, lean_object* v_as_2931_, size_t v_i_2932_, size_t v_stop_2933_, lean_object* v_b_2934_){
_start:
{
lean_object* v___y_2936_; uint8_t v___x_2940_; 
v___x_2940_ = lean_usize_dec_eq(v_i_2932_, v_stop_2933_);
if (v___x_2940_ == 0)
{
lean_object* v___x_2941_; lean_object* v_fvar_2942_; lean_object* v___x_2943_; uint8_t v___x_2944_; 
v___x_2941_ = lean_array_uget_borrowed(v_as_2931_, v_i_2932_);
v_fvar_2942_ = lean_ctor_get(v___x_2941_, 1);
v___x_2943_ = l_Lean_Expr_fvarId_x21(v_fvar_2942_);
v___x_2944_ = l_Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9(v_fvarIds_2930_, v___x_2943_);
lean_dec(v___x_2943_);
if (v___x_2944_ == 0)
{
lean_object* v___x_2945_; 
lean_inc(v___x_2941_);
v___x_2945_ = lean_array_push(v_b_2934_, v___x_2941_);
v___y_2936_ = v___x_2945_;
goto v___jp_2935_;
}
else
{
v___y_2936_ = v_b_2934_;
goto v___jp_2935_;
}
}
else
{
return v_b_2934_;
}
v___jp_2935_:
{
size_t v___x_2937_; size_t v___x_2938_; 
v___x_2937_ = ((size_t)1ULL);
v___x_2938_ = lean_usize_add(v_i_2932_, v___x_2937_);
v_i_2932_ = v___x_2938_;
v_b_2934_ = v___y_2936_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__11___boxed(lean_object* v_fvarIds_2946_, lean_object* v_as_2947_, lean_object* v_i_2948_, lean_object* v_stop_2949_, lean_object* v_b_2950_){
_start:
{
size_t v_i_boxed_2951_; size_t v_stop_boxed_2952_; lean_object* v_res_2953_; 
v_i_boxed_2951_ = lean_unbox_usize(v_i_2948_);
lean_dec(v_i_2948_);
v_stop_boxed_2952_ = lean_unbox_usize(v_stop_2949_);
lean_dec(v_stop_2949_);
v_res_2953_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__11(v_fvarIds_2946_, v_as_2947_, v_i_boxed_2951_, v_stop_boxed_2952_, v_b_2950_);
lean_dec_ref(v_as_2947_);
lean_dec_ref(v_fvarIds_2946_);
return v_res_2953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___redArg(lean_object* v_fvarIds_2956_, lean_object* v_k_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_){
_start:
{
lean_object* v_lctx_2963_; lean_object* v_localInstances_2964_; lean_object* v___x_2965_; lean_object* v___y_2967_; lean_object* v___x_2982_; uint8_t v___x_2983_; 
v_lctx_2963_ = lean_ctor_get(v___y_2958_, 2);
v_localInstances_2964_ = lean_ctor_get(v___y_2958_, 3);
v___x_2965_ = lean_unsigned_to_nat(0u);
v___x_2982_ = lean_array_get_size(v_fvarIds_2956_);
v___x_2983_ = lean_nat_dec_lt(v___x_2965_, v___x_2982_);
if (v___x_2983_ == 0)
{
lean_inc_ref(v_lctx_2963_);
v___y_2967_ = v_lctx_2963_;
goto v___jp_2966_;
}
else
{
uint8_t v___x_2984_; 
v___x_2984_ = lean_nat_dec_le(v___x_2982_, v___x_2982_);
if (v___x_2984_ == 0)
{
if (v___x_2983_ == 0)
{
lean_inc_ref(v_lctx_2963_);
v___y_2967_ = v_lctx_2963_;
goto v___jp_2966_;
}
else
{
size_t v___x_2985_; size_t v___x_2986_; lean_object* v___x_2987_; 
v___x_2985_ = ((size_t)0ULL);
v___x_2986_ = lean_usize_of_nat(v___x_2982_);
lean_inc_ref(v_lctx_2963_);
v___x_2987_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__12(v_fvarIds_2956_, v___x_2985_, v___x_2986_, v_lctx_2963_);
v___y_2967_ = v___x_2987_;
goto v___jp_2966_;
}
}
else
{
size_t v___x_2988_; size_t v___x_2989_; lean_object* v___x_2990_; 
v___x_2988_ = ((size_t)0ULL);
v___x_2989_ = lean_usize_of_nat(v___x_2982_);
lean_inc_ref(v_lctx_2963_);
v___x_2990_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__12(v_fvarIds_2956_, v___x_2988_, v___x_2989_, v_lctx_2963_);
v___y_2967_ = v___x_2990_;
goto v___jp_2966_;
}
}
v___jp_2966_:
{
lean_object* v___x_2968_; lean_object* v___x_2969_; uint8_t v___x_2970_; 
v___x_2968_ = lean_array_get_size(v_localInstances_2964_);
v___x_2969_ = ((lean_object*)(l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___redArg___closed__0));
v___x_2970_ = lean_nat_dec_lt(v___x_2965_, v___x_2968_);
if (v___x_2970_ == 0)
{
lean_object* v___x_2971_; 
v___x_2971_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___redArg(v___y_2967_, v___x_2969_, v_k_2957_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_);
return v___x_2971_;
}
else
{
uint8_t v___x_2972_; 
v___x_2972_ = lean_nat_dec_le(v___x_2968_, v___x_2968_);
if (v___x_2972_ == 0)
{
if (v___x_2970_ == 0)
{
lean_object* v___x_2973_; 
v___x_2973_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___redArg(v___y_2967_, v___x_2969_, v_k_2957_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_);
return v___x_2973_;
}
else
{
size_t v___x_2974_; size_t v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; 
v___x_2974_ = ((size_t)0ULL);
v___x_2975_ = lean_usize_of_nat(v___x_2968_);
v___x_2976_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__11(v_fvarIds_2956_, v_localInstances_2964_, v___x_2974_, v___x_2975_, v___x_2969_);
v___x_2977_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___redArg(v___y_2967_, v___x_2976_, v_k_2957_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_);
return v___x_2977_;
}
}
else
{
size_t v___x_2978_; size_t v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; 
v___x_2978_ = ((size_t)0ULL);
v___x_2979_ = lean_usize_of_nat(v___x_2968_);
v___x_2980_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__11(v_fvarIds_2956_, v_localInstances_2964_, v___x_2978_, v___x_2979_, v___x_2969_);
v___x_2981_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___redArg(v___y_2967_, v___x_2980_, v_k_2957_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_);
return v___x_2981_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___redArg___boxed(lean_object* v_fvarIds_2991_, lean_object* v_k_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_){
_start:
{
lean_object* v_res_2998_; 
v_res_2998_ = l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___redArg(v_fvarIds_2991_, v_k_2992_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_);
lean_dec(v___y_2996_);
lean_dec_ref(v___y_2995_);
lean_dec(v___y_2994_);
lean_dec_ref(v___y_2993_);
lean_dec_ref(v_fvarIds_2991_);
return v_res_2998_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__14_spec__17_spec__21(lean_object* v_x_2999_, lean_object* v_x_3000_, lean_object* v_x_3001_){
_start:
{
if (lean_obj_tag(v_x_3001_) == 0)
{
lean_dec(v_x_2999_);
return v_x_3000_;
}
else
{
lean_object* v_head_3002_; lean_object* v_tail_3003_; lean_object* v___x_3005_; uint8_t v_isShared_3006_; uint8_t v_isSharedCheck_3013_; 
v_head_3002_ = lean_ctor_get(v_x_3001_, 0);
v_tail_3003_ = lean_ctor_get(v_x_3001_, 1);
v_isSharedCheck_3013_ = !lean_is_exclusive(v_x_3001_);
if (v_isSharedCheck_3013_ == 0)
{
v___x_3005_ = v_x_3001_;
v_isShared_3006_ = v_isSharedCheck_3013_;
goto v_resetjp_3004_;
}
else
{
lean_inc(v_tail_3003_);
lean_inc(v_head_3002_);
lean_dec(v_x_3001_);
v___x_3005_ = lean_box(0);
v_isShared_3006_ = v_isSharedCheck_3013_;
goto v_resetjp_3004_;
}
v_resetjp_3004_:
{
lean_object* v___x_3008_; 
lean_inc(v_x_2999_);
if (v_isShared_3006_ == 0)
{
lean_ctor_set_tag(v___x_3005_, 5);
lean_ctor_set(v___x_3005_, 1, v_x_2999_);
lean_ctor_set(v___x_3005_, 0, v_x_3000_);
v___x_3008_ = v___x_3005_;
goto v_reusejp_3007_;
}
else
{
lean_object* v_reuseFailAlloc_3012_; 
v_reuseFailAlloc_3012_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3012_, 0, v_x_3000_);
lean_ctor_set(v_reuseFailAlloc_3012_, 1, v_x_2999_);
v___x_3008_ = v_reuseFailAlloc_3012_;
goto v_reusejp_3007_;
}
v_reusejp_3007_:
{
lean_object* v___x_3009_; lean_object* v___x_3010_; 
v___x_3009_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(v_head_3002_);
v___x_3010_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3010_, 0, v___x_3008_);
lean_ctor_set(v___x_3010_, 1, v___x_3009_);
v_x_3000_ = v___x_3010_;
v_x_3001_ = v_tail_3003_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__14_spec__17(lean_object* v_x_3014_, lean_object* v_x_3015_, lean_object* v_x_3016_){
_start:
{
if (lean_obj_tag(v_x_3016_) == 0)
{
lean_dec(v_x_3014_);
return v_x_3015_;
}
else
{
lean_object* v_head_3017_; lean_object* v_tail_3018_; lean_object* v___x_3020_; uint8_t v_isShared_3021_; uint8_t v_isSharedCheck_3028_; 
v_head_3017_ = lean_ctor_get(v_x_3016_, 0);
v_tail_3018_ = lean_ctor_get(v_x_3016_, 1);
v_isSharedCheck_3028_ = !lean_is_exclusive(v_x_3016_);
if (v_isSharedCheck_3028_ == 0)
{
v___x_3020_ = v_x_3016_;
v_isShared_3021_ = v_isSharedCheck_3028_;
goto v_resetjp_3019_;
}
else
{
lean_inc(v_tail_3018_);
lean_inc(v_head_3017_);
lean_dec(v_x_3016_);
v___x_3020_ = lean_box(0);
v_isShared_3021_ = v_isSharedCheck_3028_;
goto v_resetjp_3019_;
}
v_resetjp_3019_:
{
lean_object* v___x_3023_; 
lean_inc(v_x_3014_);
if (v_isShared_3021_ == 0)
{
lean_ctor_set_tag(v___x_3020_, 5);
lean_ctor_set(v___x_3020_, 1, v_x_3014_);
lean_ctor_set(v___x_3020_, 0, v_x_3015_);
v___x_3023_ = v___x_3020_;
goto v_reusejp_3022_;
}
else
{
lean_object* v_reuseFailAlloc_3027_; 
v_reuseFailAlloc_3027_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3027_, 0, v_x_3015_);
lean_ctor_set(v_reuseFailAlloc_3027_, 1, v_x_3014_);
v___x_3023_ = v_reuseFailAlloc_3027_;
goto v_reusejp_3022_;
}
v_reusejp_3022_:
{
lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; 
v___x_3024_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(v_head_3017_);
v___x_3025_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3025_, 0, v___x_3023_);
lean_ctor_set(v___x_3025_, 1, v___x_3024_);
v___x_3026_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__14_spec__17_spec__21(v_x_3014_, v___x_3025_, v_tail_3018_);
return v___x_3026_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__14(lean_object* v_x_3029_, lean_object* v_x_3030_){
_start:
{
if (lean_obj_tag(v_x_3029_) == 0)
{
lean_object* v___x_3031_; 
lean_dec(v_x_3030_);
v___x_3031_ = lean_box(0);
return v___x_3031_;
}
else
{
lean_object* v_tail_3032_; 
v_tail_3032_ = lean_ctor_get(v_x_3029_, 1);
if (lean_obj_tag(v_tail_3032_) == 0)
{
lean_object* v_head_3033_; lean_object* v___x_3034_; 
lean_dec(v_x_3030_);
v_head_3033_ = lean_ctor_get(v_x_3029_, 0);
lean_inc(v_head_3033_);
lean_dec_ref(v_x_3029_);
v___x_3034_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(v_head_3033_);
return v___x_3034_;
}
else
{
lean_object* v_head_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; 
lean_inc(v_tail_3032_);
v_head_3035_ = lean_ctor_get(v_x_3029_, 0);
lean_inc(v_head_3035_);
lean_dec_ref(v_x_3029_);
v___x_3036_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(v_head_3035_);
v___x_3037_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__14_spec__17(v_x_3030_, v___x_3036_, v_tail_3032_);
return v___x_3037_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__5(void){
_start:
{
lean_object* v___x_3046_; lean_object* v___x_3047_; 
v___x_3046_ = ((lean_object*)(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__0));
v___x_3047_ = lean_string_length(v___x_3046_);
return v___x_3047_;
}
}
static lean_object* _init_l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__6(void){
_start:
{
lean_object* v___x_3048_; lean_object* v___x_3049_; 
v___x_3048_ = lean_obj_once(&l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__5, &l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__5_once, _init_l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__5);
v___x_3049_ = lean_nat_to_int(v___x_3048_);
return v___x_3049_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10(lean_object* v_xs_3057_){
_start:
{
lean_object* v___x_3058_; lean_object* v___x_3059_; uint8_t v___x_3060_; 
v___x_3058_ = lean_array_get_size(v_xs_3057_);
v___x_3059_ = lean_unsigned_to_nat(0u);
v___x_3060_ = lean_nat_dec_eq(v___x_3058_, v___x_3059_);
if (v___x_3060_ == 0)
{
lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; 
v___x_3061_ = lean_array_to_list(v_xs_3057_);
v___x_3062_ = ((lean_object*)(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__3));
v___x_3063_ = l_Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__14(v___x_3061_, v___x_3062_);
v___x_3064_ = lean_obj_once(&l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__6, &l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__6_once, _init_l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__6);
v___x_3065_ = ((lean_object*)(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__7));
v___x_3066_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3066_, 0, v___x_3065_);
lean_ctor_set(v___x_3066_, 1, v___x_3063_);
v___x_3067_ = ((lean_object*)(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__8));
v___x_3068_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3068_, 0, v___x_3066_);
lean_ctor_set(v___x_3068_, 1, v___x_3067_);
v___x_3069_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3069_, 0, v___x_3064_);
lean_ctor_set(v___x_3069_, 1, v___x_3068_);
v___x_3070_ = l_Std_Format_fill(v___x_3069_);
return v___x_3070_;
}
else
{
lean_object* v___x_3071_; 
lean_dec_ref(v_xs_3057_);
v___x_3071_ = ((lean_object*)(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__10));
return v___x_3071_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__11(size_t v_sz_3072_, size_t v_i_3073_, lean_object* v_bs_3074_){
_start:
{
uint8_t v___x_3075_; 
v___x_3075_ = lean_usize_dec_lt(v_i_3073_, v_sz_3072_);
if (v___x_3075_ == 0)
{
return v_bs_3074_;
}
else
{
lean_object* v_v_3076_; lean_object* v___x_3077_; lean_object* v_bs_x27_3078_; lean_object* v___x_3079_; size_t v___x_3080_; size_t v___x_3081_; lean_object* v___x_3082_; 
v_v_3076_ = lean_array_uget(v_bs_3074_, v_i_3073_);
v___x_3077_ = lean_unsigned_to_nat(0u);
v_bs_x27_3078_ = lean_array_uset(v_bs_3074_, v_i_3073_, v___x_3077_);
v___x_3079_ = l_Lean_mkFVar(v_v_3076_);
v___x_3080_ = ((size_t)1ULL);
v___x_3081_ = lean_usize_add(v_i_3073_, v___x_3080_);
v___x_3082_ = lean_array_uset(v_bs_x27_3078_, v_i_3073_, v___x_3079_);
v_i_3073_ = v___x_3081_;
v_bs_3074_ = v___x_3082_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__11___boxed(lean_object* v_sz_3084_, lean_object* v_i_3085_, lean_object* v_bs_3086_){
_start:
{
size_t v_sz_boxed_3087_; size_t v_i_boxed_3088_; lean_object* v_res_3089_; 
v_sz_boxed_3087_ = lean_unbox_usize(v_sz_3084_);
lean_dec(v_sz_3084_);
v_i_boxed_3088_ = lean_unbox_usize(v_i_3085_);
lean_dec(v_i_3085_);
v_res_3089_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__11(v_sz_boxed_3087_, v_i_boxed_3088_, v_bs_3086_);
return v_res_3089_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg(lean_object* v_fst_3090_, lean_object* v_as_3091_, lean_object* v_i_3092_, lean_object* v_j_3093_, lean_object* v_bs_3094_){
_start:
{
lean_object* v_zero_3095_; uint8_t v_isZero_3096_; 
v_zero_3095_ = lean_unsigned_to_nat(0u);
v_isZero_3096_ = lean_nat_dec_eq(v_i_3092_, v_zero_3095_);
if (v_isZero_3096_ == 1)
{
lean_dec(v_j_3093_);
lean_dec(v_i_3092_);
return v_bs_3094_;
}
else
{
lean_object* v___x_3097_; lean_object* v_fnName_3098_; lean_object* v_recArgPos_3099_; lean_object* v_indicesPos_3100_; lean_object* v_indGroupInst_3101_; lean_object* v_indIdx_3102_; lean_object* v___x_3104_; uint8_t v_isShared_3105_; uint8_t v_isSharedCheck_3117_; 
v___x_3097_ = lean_array_fget(v_as_3091_, v_j_3093_);
v_fnName_3098_ = lean_ctor_get(v___x_3097_, 0);
v_recArgPos_3099_ = lean_ctor_get(v___x_3097_, 2);
v_indicesPos_3100_ = lean_ctor_get(v___x_3097_, 3);
v_indGroupInst_3101_ = lean_ctor_get(v___x_3097_, 4);
v_indIdx_3102_ = lean_ctor_get(v___x_3097_, 5);
v_isSharedCheck_3117_ = !lean_is_exclusive(v___x_3097_);
if (v_isSharedCheck_3117_ == 0)
{
lean_object* v_unused_3118_; 
v_unused_3118_ = lean_ctor_get(v___x_3097_, 1);
lean_dec(v_unused_3118_);
v___x_3104_ = v___x_3097_;
v_isShared_3105_ = v_isSharedCheck_3117_;
goto v_resetjp_3103_;
}
else
{
lean_inc(v_indIdx_3102_);
lean_inc(v_indGroupInst_3101_);
lean_inc(v_indicesPos_3100_);
lean_inc(v_recArgPos_3099_);
lean_inc(v_fnName_3098_);
lean_dec(v___x_3097_);
v___x_3104_ = lean_box(0);
v_isShared_3105_ = v_isSharedCheck_3117_;
goto v_resetjp_3103_;
}
v_resetjp_3103_:
{
lean_object* v_perms_3106_; lean_object* v___x_3107_; lean_object* v_one_3108_; lean_object* v_n_3109_; lean_object* v___x_3110_; lean_object* v___x_3112_; 
v_perms_3106_ = lean_ctor_get(v_fst_3090_, 1);
v___x_3107_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0, &l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0_once, _init_l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0);
v_one_3108_ = lean_unsigned_to_nat(1u);
v_n_3109_ = lean_nat_sub(v_i_3092_, v_one_3108_);
lean_dec(v_i_3092_);
v___x_3110_ = lean_array_get_borrowed(v___x_3107_, v_perms_3106_, v_j_3093_);
lean_inc(v___x_3110_);
if (v_isShared_3105_ == 0)
{
lean_ctor_set(v___x_3104_, 1, v___x_3110_);
v___x_3112_ = v___x_3104_;
goto v_reusejp_3111_;
}
else
{
lean_object* v_reuseFailAlloc_3116_; 
v_reuseFailAlloc_3116_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3116_, 0, v_fnName_3098_);
lean_ctor_set(v_reuseFailAlloc_3116_, 1, v___x_3110_);
lean_ctor_set(v_reuseFailAlloc_3116_, 2, v_recArgPos_3099_);
lean_ctor_set(v_reuseFailAlloc_3116_, 3, v_indicesPos_3100_);
lean_ctor_set(v_reuseFailAlloc_3116_, 4, v_indGroupInst_3101_);
lean_ctor_set(v_reuseFailAlloc_3116_, 5, v_indIdx_3102_);
v___x_3112_ = v_reuseFailAlloc_3116_;
goto v_reusejp_3111_;
}
v_reusejp_3111_:
{
lean_object* v___x_3113_; lean_object* v___x_3114_; 
v___x_3113_ = lean_nat_add(v_j_3093_, v_one_3108_);
lean_dec(v_j_3093_);
v___x_3114_ = lean_array_push(v_bs_3094_, v___x_3112_);
v_i_3092_ = v_n_3109_;
v_j_3093_ = v___x_3113_;
v_bs_3094_ = v___x_3114_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg___boxed(lean_object* v_fst_3119_, lean_object* v_as_3120_, lean_object* v_i_3121_, lean_object* v_j_3122_, lean_object* v_bs_3123_){
_start:
{
lean_object* v_res_3124_; 
v_res_3124_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg(v_fst_3119_, v_as_3120_, v_i_3121_, v_j_3122_, v_bs_3123_);
lean_dec_ref(v_as_3120_);
lean_dec_ref(v_fst_3119_);
return v_res_3124_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__2(size_t v_sz_3125_, size_t v_i_3126_, lean_object* v_bs_3127_){
_start:
{
uint8_t v___x_3128_; 
v___x_3128_ = lean_usize_dec_lt(v_i_3126_, v_sz_3125_);
if (v___x_3128_ == 0)
{
return v_bs_3127_;
}
else
{
lean_object* v_v_3129_; lean_object* v_recArgPos_3130_; lean_object* v___x_3131_; lean_object* v_bs_x27_3132_; size_t v___x_3133_; size_t v___x_3134_; lean_object* v___x_3135_; 
v_v_3129_ = lean_array_uget_borrowed(v_bs_3127_, v_i_3126_);
v_recArgPos_3130_ = lean_ctor_get(v_v_3129_, 2);
lean_inc(v_recArgPos_3130_);
v___x_3131_ = lean_unsigned_to_nat(0u);
v_bs_x27_3132_ = lean_array_uset(v_bs_3127_, v_i_3126_, v___x_3131_);
v___x_3133_ = ((size_t)1ULL);
v___x_3134_ = lean_usize_add(v_i_3126_, v___x_3133_);
v___x_3135_ = lean_array_uset(v_bs_x27_3132_, v_i_3126_, v_recArgPos_3130_);
v_i_3126_ = v___x_3134_;
v_bs_3127_ = v___x_3135_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__2___boxed(lean_object* v_sz_3137_, lean_object* v_i_3138_, lean_object* v_bs_3139_){
_start:
{
size_t v_sz_boxed_3140_; size_t v_i_boxed_3141_; lean_object* v_res_3142_; 
v_sz_boxed_3140_ = lean_unbox_usize(v_sz_3137_);
lean_dec(v_sz_3137_);
v_i_boxed_3141_ = lean_unbox_usize(v_i_3138_);
lean_dec(v_i_3138_);
v_res_3142_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__2(v_sz_boxed_3140_, v_i_boxed_3141_, v_bs_3139_);
return v_res_3142_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__1(void){
_start:
{
lean_object* v___x_3144_; lean_object* v___x_3145_; 
v___x_3144_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__0));
v___x_3145_ = l_Lean_stringToMessageData(v___x_3144_);
return v___x_3145_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__3(void){
_start:
{
lean_object* v___x_3147_; lean_object* v___x_3148_; 
v___x_3147_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__2));
v___x_3148_ = l_Lean_stringToMessageData(v___x_3147_);
return v___x_3148_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__5(void){
_start:
{
lean_object* v___x_3150_; lean_object* v___x_3151_; 
v___x_3150_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__4));
v___x_3151_ = l_Lean_stringToMessageData(v___x_3150_);
return v___x_3151_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6(lean_object* v_a_3152_, lean_object* v_as_3153_, size_t v_sz_3154_, size_t v_i_3155_, lean_object* v_b_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_){
_start:
{
lean_object* v_a_3163_; uint8_t v___x_3167_; 
v___x_3167_ = lean_usize_dec_lt(v_i_3155_, v_sz_3154_);
if (v___x_3167_ == 0)
{
lean_object* v___x_3168_; 
lean_dec_ref(v_a_3152_);
v___x_3168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3168_, 0, v_b_3156_);
return v___x_3168_;
}
else
{
lean_object* v_a_3169_; lean_object* v___x_3170_; 
v_a_3169_ = lean_array_uget_borrowed(v_as_3153_, v_i_3155_);
lean_inc(v_a_3169_);
lean_inc_ref(v_a_3152_);
v___x_3170_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg(v_a_3152_, v_a_3169_, v___y_3158_);
if (lean_obj_tag(v___x_3170_) == 0)
{
lean_object* v_a_3171_; lean_object* v___x_3172_; uint8_t v___x_3173_; 
v_a_3171_ = lean_ctor_get(v___x_3170_, 0);
lean_inc(v_a_3171_);
lean_dec_ref(v___x_3170_);
v___x_3172_ = lean_box(0);
v___x_3173_ = lean_unbox(v_a_3171_);
lean_dec(v_a_3171_);
if (v___x_3173_ == 0)
{
v_a_3163_ = v___x_3172_;
goto v___jp_3162_;
}
else
{
uint8_t v___x_3174_; 
v___x_3174_ = l_Lean_Expr_isFVarOf(v_a_3152_, v_a_3169_);
if (v___x_3174_ == 0)
{
lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; 
v___x_3175_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__1);
lean_inc_ref(v_a_3152_);
v___x_3176_ = l_Lean_indentExpr(v_a_3152_);
v___x_3177_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3177_, 0, v___x_3175_);
lean_ctor_set(v___x_3177_, 1, v___x_3176_);
v___x_3178_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__3);
v___x_3179_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3179_, 0, v___x_3177_);
lean_ctor_set(v___x_3179_, 1, v___x_3178_);
lean_inc(v_a_3169_);
v___x_3180_ = l_Lean_mkFVar(v_a_3169_);
v___x_3181_ = l_Lean_indentExpr(v___x_3180_);
v___x_3182_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3182_, 0, v___x_3179_);
lean_ctor_set(v___x_3182_, 1, v___x_3181_);
v___x_3183_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__5);
v___x_3184_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3184_, 0, v___x_3182_);
lean_ctor_set(v___x_3184_, 1, v___x_3183_);
v___x_3185_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg(v___x_3184_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_);
if (lean_obj_tag(v___x_3185_) == 0)
{
lean_dec_ref(v___x_3185_);
v_a_3163_ = v___x_3172_;
goto v___jp_3162_;
}
else
{
lean_dec_ref(v_a_3152_);
return v___x_3185_;
}
}
else
{
lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; 
v___x_3186_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__1);
lean_inc_ref(v_a_3152_);
v___x_3187_ = l_Lean_indentExpr(v_a_3152_);
v___x_3188_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3188_, 0, v___x_3186_);
lean_ctor_set(v___x_3188_, 1, v___x_3187_);
v___x_3189_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__5);
v___x_3190_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3190_, 0, v___x_3188_);
lean_ctor_set(v___x_3190_, 1, v___x_3189_);
v___x_3191_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg(v___x_3190_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_);
if (lean_obj_tag(v___x_3191_) == 0)
{
lean_dec_ref(v___x_3191_);
v_a_3163_ = v___x_3172_;
goto v___jp_3162_;
}
else
{
lean_dec_ref(v_a_3152_);
return v___x_3191_;
}
}
}
}
else
{
lean_object* v_a_3192_; lean_object* v___x_3194_; uint8_t v_isShared_3195_; uint8_t v_isSharedCheck_3199_; 
lean_dec_ref(v_a_3152_);
v_a_3192_ = lean_ctor_get(v___x_3170_, 0);
v_isSharedCheck_3199_ = !lean_is_exclusive(v___x_3170_);
if (v_isSharedCheck_3199_ == 0)
{
v___x_3194_ = v___x_3170_;
v_isShared_3195_ = v_isSharedCheck_3199_;
goto v_resetjp_3193_;
}
else
{
lean_inc(v_a_3192_);
lean_dec(v___x_3170_);
v___x_3194_ = lean_box(0);
v_isShared_3195_ = v_isSharedCheck_3199_;
goto v_resetjp_3193_;
}
v_resetjp_3193_:
{
lean_object* v___x_3197_; 
if (v_isShared_3195_ == 0)
{
v___x_3197_ = v___x_3194_;
goto v_reusejp_3196_;
}
else
{
lean_object* v_reuseFailAlloc_3198_; 
v_reuseFailAlloc_3198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3198_, 0, v_a_3192_);
v___x_3197_ = v_reuseFailAlloc_3198_;
goto v_reusejp_3196_;
}
v_reusejp_3196_:
{
return v___x_3197_;
}
}
}
}
v___jp_3162_:
{
size_t v___x_3164_; size_t v___x_3165_; 
v___x_3164_ = ((size_t)1ULL);
v___x_3165_ = lean_usize_add(v_i_3155_, v___x_3164_);
v_i_3155_ = v___x_3165_;
v_b_3156_ = v_a_3163_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___boxed(lean_object* v_a_3200_, lean_object* v_as_3201_, lean_object* v_sz_3202_, lean_object* v_i_3203_, lean_object* v_b_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_){
_start:
{
size_t v_sz_boxed_3210_; size_t v_i_boxed_3211_; lean_object* v_res_3212_; 
v_sz_boxed_3210_ = lean_unbox_usize(v_sz_3202_);
lean_dec(v_sz_3202_);
v_i_boxed_3211_ = lean_unbox_usize(v_i_3203_);
lean_dec(v_i_3203_);
v_res_3212_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6(v_a_3200_, v_as_3201_, v_sz_boxed_3210_, v_i_boxed_3211_, v_b_3204_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_);
lean_dec(v___y_3208_);
lean_dec_ref(v___y_3207_);
lean_dec(v___y_3206_);
lean_dec_ref(v___y_3205_);
lean_dec_ref(v_as_3201_);
return v_res_3212_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7(lean_object* v_snd_3213_, lean_object* v_as_3214_, size_t v_sz_3215_, size_t v_i_3216_, lean_object* v_b_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_){
_start:
{
uint8_t v___x_3223_; 
v___x_3223_ = lean_usize_dec_lt(v_i_3216_, v_sz_3215_);
if (v___x_3223_ == 0)
{
lean_object* v___x_3224_; 
v___x_3224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3224_, 0, v_b_3217_);
return v___x_3224_;
}
else
{
lean_object* v___x_3225_; lean_object* v_a_3226_; size_t v_sz_3227_; size_t v___x_3228_; lean_object* v___x_3229_; 
v___x_3225_ = lean_box(0);
v_a_3226_ = lean_array_uget_borrowed(v_as_3214_, v_i_3216_);
v_sz_3227_ = lean_array_size(v_snd_3213_);
v___x_3228_ = ((size_t)0ULL);
lean_inc(v_a_3226_);
v___x_3229_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6(v_a_3226_, v_snd_3213_, v_sz_3227_, v___x_3228_, v___x_3225_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_);
if (lean_obj_tag(v___x_3229_) == 0)
{
size_t v___x_3230_; size_t v___x_3231_; 
lean_dec_ref(v___x_3229_);
v___x_3230_ = ((size_t)1ULL);
v___x_3231_ = lean_usize_add(v_i_3216_, v___x_3230_);
v_i_3216_ = v___x_3231_;
v_b_3217_ = v___x_3225_;
goto _start;
}
else
{
return v___x_3229_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7___boxed(lean_object* v_snd_3233_, lean_object* v_as_3234_, lean_object* v_sz_3235_, lean_object* v_i_3236_, lean_object* v_b_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_){
_start:
{
size_t v_sz_boxed_3243_; size_t v_i_boxed_3244_; lean_object* v_res_3245_; 
v_sz_boxed_3243_ = lean_unbox_usize(v_sz_3235_);
lean_dec(v_sz_3235_);
v_i_boxed_3244_ = lean_unbox_usize(v_i_3236_);
lean_dec(v_i_3236_);
v_res_3245_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7(v_snd_3233_, v_as_3234_, v_sz_boxed_3243_, v_i_boxed_3244_, v_b_3237_, v___y_3238_, v___y_3239_, v___y_3240_, v___y_3241_);
lean_dec(v___y_3241_);
lean_dec_ref(v___y_3240_);
lean_dec(v___y_3239_);
lean_dec_ref(v___y_3238_);
lean_dec_ref(v_as_3234_);
lean_dec_ref(v_snd_3233_);
return v_res_3245_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8(lean_object* v_snd_3246_, lean_object* v_as_3247_, size_t v_sz_3248_, size_t v_i_3249_, lean_object* v_b_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_){
_start:
{
uint8_t v___x_3256_; 
v___x_3256_ = lean_usize_dec_lt(v_i_3249_, v_sz_3248_);
if (v___x_3256_ == 0)
{
lean_object* v___x_3257_; 
v___x_3257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3257_, 0, v_b_3250_);
return v___x_3257_;
}
else
{
lean_object* v_a_3258_; lean_object* v_indGroupInst_3259_; lean_object* v_params_3260_; lean_object* v___x_3261_; size_t v_sz_3262_; size_t v___x_3263_; lean_object* v___x_3264_; 
v_a_3258_ = lean_array_uget_borrowed(v_as_3247_, v_i_3249_);
v_indGroupInst_3259_ = lean_ctor_get(v_a_3258_, 4);
v_params_3260_ = lean_ctor_get(v_indGroupInst_3259_, 2);
v___x_3261_ = lean_box(0);
v_sz_3262_ = lean_array_size(v_params_3260_);
v___x_3263_ = ((size_t)0ULL);
v___x_3264_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7(v_snd_3246_, v_params_3260_, v_sz_3262_, v___x_3263_, v___x_3261_, v___y_3251_, v___y_3252_, v___y_3253_, v___y_3254_);
if (lean_obj_tag(v___x_3264_) == 0)
{
size_t v___x_3265_; size_t v___x_3266_; 
lean_dec_ref(v___x_3264_);
v___x_3265_ = ((size_t)1ULL);
v___x_3266_ = lean_usize_add(v_i_3249_, v___x_3265_);
v_i_3249_ = v___x_3266_;
v_b_3250_ = v___x_3261_;
goto _start;
}
else
{
return v___x_3264_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8___boxed(lean_object* v_snd_3268_, lean_object* v_as_3269_, lean_object* v_sz_3270_, lean_object* v_i_3271_, lean_object* v_b_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_){
_start:
{
size_t v_sz_boxed_3278_; size_t v_i_boxed_3279_; lean_object* v_res_3280_; 
v_sz_boxed_3278_ = lean_unbox_usize(v_sz_3270_);
lean_dec(v_sz_3270_);
v_i_boxed_3279_ = lean_unbox_usize(v_i_3271_);
lean_dec(v_i_3271_);
v_res_3280_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8(v_snd_3268_, v_as_3269_, v_sz_boxed_3278_, v_i_boxed_3279_, v_b_3272_, v___y_3273_, v___y_3274_, v___y_3275_, v___y_3276_);
lean_dec(v___y_3276_);
lean_dec_ref(v___y_3275_);
lean_dec(v___y_3274_);
lean_dec_ref(v___y_3273_);
lean_dec_ref(v_as_3269_);
lean_dec_ref(v_snd_3268_);
return v_res_3280_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__0(void){
_start:
{
lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; 
v___x_3281_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__3));
v___x_3282_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0___closed__1));
v___x_3283_ = l_Lean_Name_append(v___x_3282_, v___x_3281_);
return v___x_3283_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3285_; lean_object* v___x_3286_; 
v___x_3285_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__1));
v___x_3286_ = l_Lean_stringToMessageData(v___x_3285_);
return v___x_3286_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__4(void){
_start:
{
lean_object* v___x_3288_; lean_object* v___x_3289_; 
v___x_3288_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__3));
v___x_3289_ = l_Lean_stringToMessageData(v___x_3288_);
return v___x_3289_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__6(void){
_start:
{
lean_object* v___x_3291_; lean_object* v___x_3292_; 
v___x_3291_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__5));
v___x_3292_ = l_Lean_stringToMessageData(v___x_3291_);
return v___x_3292_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__8(void){
_start:
{
lean_object* v___x_3294_; lean_object* v___x_3295_; 
v___x_3294_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__7));
v___x_3295_ = l_Lean_stringToMessageData(v___x_3294_);
return v___x_3295_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__10(void){
_start:
{
lean_object* v___x_3297_; lean_object* v___x_3298_; 
v___x_3297_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__9));
v___x_3298_ = l_Lean_stringToMessageData(v___x_3297_);
return v___x_3298_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0(size_t v___x_3299_, lean_object* v_a_3300_, lean_object* v_xs_3301_, lean_object* v___x_3302_, lean_object* v_a_3303_, lean_object* v_recArgInfos_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_){
_start:
{
lean_object* v___y_3311_; lean_object* v___y_3312_; lean_object* v___y_3313_; lean_object* v___y_3314_; lean_object* v___y_3315_; lean_object* v___y_3316_; lean_object* v___y_3317_; lean_object* v___x_3330_; lean_object* v___y_3332_; lean_object* v___y_3333_; lean_object* v___y_3334_; lean_object* v___y_3335_; lean_object* v___y_3336_; lean_object* v___y_3337_; lean_object* v___y_3338_; lean_object* v___x_3357_; lean_object* v_a_3358_; size_t v_sz_3359_; lean_object* v___x_3360_; lean_object* v___y_3362_; lean_object* v___y_3363_; lean_object* v___y_3364_; lean_object* v___y_3365_; uint8_t v___x_3424_; 
v___x_3330_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__3));
v___x_3357_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0(v___x_3330_, v___y_3305_, v___y_3306_, v___y_3307_, v___y_3308_);
v_a_3358_ = lean_ctor_get(v___x_3357_, 0);
lean_inc(v_a_3358_);
lean_dec_ref(v___x_3357_);
v_sz_3359_ = lean_array_size(v_recArgInfos_3304_);
lean_inc_ref(v_recArgInfos_3304_);
v___x_3360_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__2(v_sz_3359_, v___x_3299_, v_recArgInfos_3304_);
v___x_3424_ = lean_unbox(v_a_3358_);
lean_dec(v_a_3358_);
if (v___x_3424_ == 0)
{
v___y_3362_ = v___y_3305_;
v___y_3363_ = v___y_3306_;
v___y_3364_ = v___y_3307_;
v___y_3365_ = v___y_3308_;
goto v___jp_3361_;
}
else
{
lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; 
v___x_3425_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__10, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__10);
lean_inc_ref(v___x_3360_);
v___x_3426_ = lean_array_to_list(v___x_3360_);
v___x_3427_ = lean_box(0);
v___x_3428_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__0(v___x_3426_, v___x_3427_);
v___x_3429_ = l_Lean_MessageData_ofList(v___x_3428_);
v___x_3430_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3430_, 0, v___x_3425_);
lean_ctor_set(v___x_3430_, 1, v___x_3429_);
v___x_3431_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_3330_, v___x_3430_, v___y_3305_, v___y_3306_, v___y_3307_, v___y_3308_);
if (lean_obj_tag(v___x_3431_) == 0)
{
lean_dec_ref(v___x_3431_);
v___y_3362_ = v___y_3305_;
v___y_3363_ = v___y_3306_;
v___y_3364_ = v___y_3307_;
v___y_3365_ = v___y_3308_;
goto v___jp_3361_;
}
else
{
lean_object* v_a_3432_; lean_object* v___x_3434_; uint8_t v_isShared_3435_; uint8_t v_isSharedCheck_3439_; 
lean_dec_ref(v___x_3360_);
lean_dec_ref(v_recArgInfos_3304_);
lean_dec_ref(v_a_3303_);
lean_dec(v___x_3302_);
lean_dec_ref(v_xs_3301_);
lean_dec_ref(v_a_3300_);
v_a_3432_ = lean_ctor_get(v___x_3431_, 0);
v_isSharedCheck_3439_ = !lean_is_exclusive(v___x_3431_);
if (v_isSharedCheck_3439_ == 0)
{
v___x_3434_ = v___x_3431_;
v_isShared_3435_ = v_isSharedCheck_3439_;
goto v_resetjp_3433_;
}
else
{
lean_inc(v_a_3432_);
lean_dec(v___x_3431_);
v___x_3434_ = lean_box(0);
v_isShared_3435_ = v_isSharedCheck_3439_;
goto v_resetjp_3433_;
}
v_resetjp_3433_:
{
lean_object* v___x_3437_; 
if (v_isShared_3435_ == 0)
{
v___x_3437_ = v___x_3434_;
goto v_reusejp_3436_;
}
else
{
lean_object* v_reuseFailAlloc_3438_; 
v_reuseFailAlloc_3438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3438_, 0, v_a_3432_);
v___x_3437_ = v_reuseFailAlloc_3438_;
goto v_reusejp_3436_;
}
v_reusejp_3436_:
{
return v___x_3437_;
}
}
}
}
v___jp_3310_:
{
lean_object* v___x_3318_; size_t v_sz_3319_; lean_object* v___x_3320_; 
v___x_3318_ = lean_box(0);
v_sz_3319_ = lean_array_size(v___y_3313_);
v___x_3320_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8(v___y_3312_, v___y_3313_, v_sz_3319_, v___x_3299_, v___x_3318_, v___y_3314_, v___y_3315_, v___y_3316_, v___y_3317_);
lean_dec_ref(v___y_3313_);
if (lean_obj_tag(v___x_3320_) == 0)
{
lean_object* v___x_3321_; 
lean_dec_ref(v___x_3320_);
v___x_3321_ = l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___redArg(v___y_3312_, v___y_3311_, v___y_3314_, v___y_3315_, v___y_3316_, v___y_3317_);
lean_dec_ref(v___y_3312_);
return v___x_3321_;
}
else
{
lean_object* v_a_3322_; lean_object* v___x_3324_; uint8_t v_isShared_3325_; uint8_t v_isSharedCheck_3329_; 
lean_dec_ref(v___y_3312_);
lean_dec_ref(v___y_3311_);
v_a_3322_ = lean_ctor_get(v___x_3320_, 0);
v_isSharedCheck_3329_ = !lean_is_exclusive(v___x_3320_);
if (v_isSharedCheck_3329_ == 0)
{
v___x_3324_ = v___x_3320_;
v_isShared_3325_ = v_isSharedCheck_3329_;
goto v_resetjp_3323_;
}
else
{
lean_inc(v_a_3322_);
lean_dec(v___x_3320_);
v___x_3324_ = lean_box(0);
v_isShared_3325_ = v_isSharedCheck_3329_;
goto v_resetjp_3323_;
}
v_resetjp_3323_:
{
lean_object* v___x_3327_; 
if (v_isShared_3325_ == 0)
{
v___x_3327_ = v___x_3324_;
goto v_reusejp_3326_;
}
else
{
lean_object* v_reuseFailAlloc_3328_; 
v_reuseFailAlloc_3328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3328_, 0, v_a_3322_);
v___x_3327_ = v_reuseFailAlloc_3328_;
goto v_reusejp_3326_;
}
v_reusejp_3326_:
{
return v___x_3327_;
}
}
}
}
v___jp_3331_:
{
lean_object* v_options_3339_; uint8_t v_hasTrace_3340_; 
v_options_3339_ = lean_ctor_get(v___y_3337_, 2);
v_hasTrace_3340_ = lean_ctor_get_uint8(v_options_3339_, sizeof(void*)*1);
if (v_hasTrace_3340_ == 0)
{
v___y_3311_ = v___y_3332_;
v___y_3312_ = v___y_3333_;
v___y_3313_ = v___y_3334_;
v___y_3314_ = v___y_3335_;
v___y_3315_ = v___y_3336_;
v___y_3316_ = v___y_3337_;
v___y_3317_ = v___y_3338_;
goto v___jp_3310_;
}
else
{
lean_object* v_inheritedTraceOptions_3341_; lean_object* v___x_3342_; uint8_t v___x_3343_; 
v_inheritedTraceOptions_3341_ = lean_ctor_get(v___y_3337_, 13);
v___x_3342_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__0);
v___x_3343_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3341_, v_options_3339_, v___x_3342_);
if (v___x_3343_ == 0)
{
v___y_3311_ = v___y_3332_;
v___y_3312_ = v___y_3333_;
v___y_3313_ = v___y_3334_;
v___y_3314_ = v___y_3335_;
v___y_3315_ = v___y_3336_;
v___y_3316_ = v___y_3337_;
v___y_3317_ = v___y_3338_;
goto v___jp_3310_;
}
else
{
lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; 
v___x_3344_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__2);
lean_inc_ref(v___y_3334_);
v___x_3345_ = l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10(v___y_3334_);
v___x_3346_ = l_Lean_MessageData_ofFormat(v___x_3345_);
v___x_3347_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3347_, 0, v___x_3344_);
lean_ctor_set(v___x_3347_, 1, v___x_3346_);
v___x_3348_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_3330_, v___x_3347_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_);
if (lean_obj_tag(v___x_3348_) == 0)
{
lean_dec_ref(v___x_3348_);
v___y_3311_ = v___y_3332_;
v___y_3312_ = v___y_3333_;
v___y_3313_ = v___y_3334_;
v___y_3314_ = v___y_3335_;
v___y_3315_ = v___y_3336_;
v___y_3316_ = v___y_3337_;
v___y_3317_ = v___y_3338_;
goto v___jp_3310_;
}
else
{
lean_object* v_a_3349_; lean_object* v___x_3351_; uint8_t v_isShared_3352_; uint8_t v_isSharedCheck_3356_; 
lean_dec_ref(v___y_3334_);
lean_dec_ref(v___y_3333_);
lean_dec_ref(v___y_3332_);
v_a_3349_ = lean_ctor_get(v___x_3348_, 0);
v_isSharedCheck_3356_ = !lean_is_exclusive(v___x_3348_);
if (v_isSharedCheck_3356_ == 0)
{
v___x_3351_ = v___x_3348_;
v_isShared_3352_ = v_isSharedCheck_3356_;
goto v_resetjp_3350_;
}
else
{
lean_inc(v_a_3349_);
lean_dec(v___x_3348_);
v___x_3351_ = lean_box(0);
v_isShared_3352_ = v_isSharedCheck_3356_;
goto v_resetjp_3350_;
}
v_resetjp_3350_:
{
lean_object* v___x_3354_; 
if (v_isShared_3352_ == 0)
{
v___x_3354_ = v___x_3351_;
goto v_reusejp_3353_;
}
else
{
lean_object* v_reuseFailAlloc_3355_; 
v_reuseFailAlloc_3355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3355_, 0, v_a_3349_);
v___x_3354_ = v_reuseFailAlloc_3355_;
goto v_reusejp_3353_;
}
v_reusejp_3353_:
{
return v___x_3354_;
}
}
}
}
}
}
v___jp_3361_:
{
lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v_snd_3368_; lean_object* v_fst_3369_; lean_object* v___x_3371_; uint8_t v_isShared_3372_; uint8_t v_isSharedCheck_3423_; 
lean_inc_ref(v_recArgInfos_3304_);
v___x_3366_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__3(v_sz_3359_, v___x_3299_, v_recArgInfos_3304_);
lean_inc_ref(v_xs_3301_);
v___x_3367_ = l_Lean_Elab_FixedParamPerms_erase(v_a_3300_, v_xs_3301_, v___x_3366_);
v_snd_3368_ = lean_ctor_get(v___x_3367_, 1);
v_fst_3369_ = lean_ctor_get(v___x_3367_, 0);
v_isSharedCheck_3423_ = !lean_is_exclusive(v___x_3367_);
if (v_isSharedCheck_3423_ == 0)
{
v___x_3371_ = v___x_3367_;
v_isShared_3372_ = v_isSharedCheck_3423_;
goto v_resetjp_3370_;
}
else
{
lean_inc(v_snd_3368_);
lean_inc(v_fst_3369_);
lean_dec(v___x_3367_);
v___x_3371_ = lean_box(0);
v_isShared_3372_ = v_isSharedCheck_3423_;
goto v_resetjp_3370_;
}
v_resetjp_3370_:
{
lean_object* v_fst_3373_; lean_object* v_snd_3374_; lean_object* v___x_3376_; uint8_t v_isShared_3377_; uint8_t v_isSharedCheck_3422_; 
v_fst_3373_ = lean_ctor_get(v_snd_3368_, 0);
v_snd_3374_ = lean_ctor_get(v_snd_3368_, 1);
v_isSharedCheck_3422_ = !lean_is_exclusive(v_snd_3368_);
if (v_isSharedCheck_3422_ == 0)
{
v___x_3376_ = v_snd_3368_;
v_isShared_3377_ = v_isSharedCheck_3422_;
goto v_resetjp_3375_;
}
else
{
lean_inc(v_snd_3374_);
lean_inc(v_fst_3373_);
lean_dec(v_snd_3368_);
v___x_3376_ = lean_box(0);
v_isShared_3377_ = v_isSharedCheck_3422_;
goto v_resetjp_3375_;
}
v_resetjp_3375_:
{
lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___f_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; uint8_t v___x_3384_; 
v___x_3378_ = lean_array_get_size(v_recArgInfos_3304_);
v___x_3379_ = lean_mk_empty_array_with_capacity(v___x_3378_);
v___x_3380_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg(v_fst_3369_, v_recArgInfos_3304_, v___x_3378_, v___x_3302_, v___x_3379_);
lean_dec_ref(v_recArgInfos_3304_);
lean_inc_ref(v___x_3380_);
lean_inc(v_fst_3373_);
v___f_3381_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___boxed), 10, 5);
lean_closure_set(v___f_3381_, 0, v_a_3303_);
lean_closure_set(v___f_3381_, 1, v_fst_3369_);
lean_closure_set(v___f_3381_, 2, v_fst_3373_);
lean_closure_set(v___f_3381_, 3, v___x_3380_);
lean_closure_set(v___f_3381_, 4, v___x_3360_);
v___x_3382_ = lean_array_get_size(v_fst_3373_);
v___x_3383_ = lean_array_get_size(v_xs_3301_);
v___x_3384_ = lean_nat_dec_eq(v___x_3382_, v___x_3383_);
if (v___x_3384_ == 0)
{
lean_object* v___x_3385_; lean_object* v_a_3386_; uint8_t v___x_3387_; 
v___x_3385_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0(v___x_3330_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_);
v_a_3386_ = lean_ctor_get(v___x_3385_, 0);
lean_inc(v_a_3386_);
lean_dec_ref(v___x_3385_);
v___x_3387_ = lean_unbox(v_a_3386_);
lean_dec(v_a_3386_);
if (v___x_3387_ == 0)
{
lean_del_object(v___x_3376_);
lean_dec(v_fst_3373_);
lean_del_object(v___x_3371_);
lean_dec_ref(v_xs_3301_);
v___y_3332_ = v___f_3381_;
v___y_3333_ = v_snd_3374_;
v___y_3334_ = v___x_3380_;
v___y_3335_ = v___y_3362_;
v___y_3336_ = v___y_3363_;
v___y_3337_ = v___y_3364_;
v___y_3338_ = v___y_3365_;
goto v___jp_3331_;
}
else
{
lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3394_; 
v___x_3388_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__4);
v___x_3389_ = lean_array_to_list(v_xs_3301_);
v___x_3390_ = lean_box(0);
v___x_3391_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_3389_, v___x_3390_);
v___x_3392_ = l_Lean_MessageData_ofList(v___x_3391_);
if (v_isShared_3377_ == 0)
{
lean_ctor_set_tag(v___x_3376_, 7);
lean_ctor_set(v___x_3376_, 1, v___x_3392_);
lean_ctor_set(v___x_3376_, 0, v___x_3388_);
v___x_3394_ = v___x_3376_;
goto v_reusejp_3393_;
}
else
{
lean_object* v_reuseFailAlloc_3420_; 
v_reuseFailAlloc_3420_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3420_, 0, v___x_3388_);
lean_ctor_set(v_reuseFailAlloc_3420_, 1, v___x_3392_);
v___x_3394_ = v_reuseFailAlloc_3420_;
goto v_reusejp_3393_;
}
v_reusejp_3393_:
{
lean_object* v___x_3395_; lean_object* v___x_3397_; 
v___x_3395_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__6, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__6);
if (v_isShared_3372_ == 0)
{
lean_ctor_set_tag(v___x_3371_, 7);
lean_ctor_set(v___x_3371_, 1, v___x_3395_);
lean_ctor_set(v___x_3371_, 0, v___x_3394_);
v___x_3397_ = v___x_3371_;
goto v_reusejp_3396_;
}
else
{
lean_object* v_reuseFailAlloc_3419_; 
v_reuseFailAlloc_3419_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3419_, 0, v___x_3394_);
lean_ctor_set(v_reuseFailAlloc_3419_, 1, v___x_3395_);
v___x_3397_ = v_reuseFailAlloc_3419_;
goto v_reusejp_3396_;
}
v_reusejp_3396_:
{
lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; size_t v_sz_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; 
v___x_3398_ = lean_array_to_list(v_fst_3373_);
v___x_3399_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_3398_, v___x_3390_);
v___x_3400_ = l_Lean_MessageData_ofList(v___x_3399_);
v___x_3401_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3401_, 0, v___x_3397_);
lean_ctor_set(v___x_3401_, 1, v___x_3400_);
v___x_3402_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__8);
v___x_3403_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3403_, 0, v___x_3401_);
lean_ctor_set(v___x_3403_, 1, v___x_3402_);
v_sz_3404_ = lean_array_size(v_snd_3374_);
lean_inc(v_snd_3374_);
v___x_3405_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__11(v_sz_3404_, v___x_3299_, v_snd_3374_);
v___x_3406_ = lean_array_to_list(v___x_3405_);
v___x_3407_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_3406_, v___x_3390_);
v___x_3408_ = l_Lean_MessageData_ofList(v___x_3407_);
v___x_3409_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3409_, 0, v___x_3403_);
lean_ctor_set(v___x_3409_, 1, v___x_3408_);
v___x_3410_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_3330_, v___x_3409_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_);
if (lean_obj_tag(v___x_3410_) == 0)
{
lean_dec_ref(v___x_3410_);
v___y_3332_ = v___f_3381_;
v___y_3333_ = v_snd_3374_;
v___y_3334_ = v___x_3380_;
v___y_3335_ = v___y_3362_;
v___y_3336_ = v___y_3363_;
v___y_3337_ = v___y_3364_;
v___y_3338_ = v___y_3365_;
goto v___jp_3331_;
}
else
{
lean_object* v_a_3411_; lean_object* v___x_3413_; uint8_t v_isShared_3414_; uint8_t v_isSharedCheck_3418_; 
lean_dec_ref(v___f_3381_);
lean_dec_ref(v___x_3380_);
lean_dec(v_snd_3374_);
v_a_3411_ = lean_ctor_get(v___x_3410_, 0);
v_isSharedCheck_3418_ = !lean_is_exclusive(v___x_3410_);
if (v_isSharedCheck_3418_ == 0)
{
v___x_3413_ = v___x_3410_;
v_isShared_3414_ = v_isSharedCheck_3418_;
goto v_resetjp_3412_;
}
else
{
lean_inc(v_a_3411_);
lean_dec(v___x_3410_);
v___x_3413_ = lean_box(0);
v_isShared_3414_ = v_isSharedCheck_3418_;
goto v_resetjp_3412_;
}
v_resetjp_3412_:
{
lean_object* v___x_3416_; 
if (v_isShared_3414_ == 0)
{
v___x_3416_ = v___x_3413_;
goto v_reusejp_3415_;
}
else
{
lean_object* v_reuseFailAlloc_3417_; 
v_reuseFailAlloc_3417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3417_, 0, v_a_3411_);
v___x_3416_ = v_reuseFailAlloc_3417_;
goto v_reusejp_3415_;
}
v_reusejp_3415_:
{
return v___x_3416_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3421_; 
lean_dec_ref(v___x_3380_);
lean_del_object(v___x_3376_);
lean_dec(v_fst_3373_);
lean_del_object(v___x_3371_);
lean_dec_ref(v_xs_3301_);
v___x_3421_ = l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___redArg(v_snd_3374_, v___f_3381_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_);
lean_dec(v_snd_3374_);
return v___x_3421_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___boxed(lean_object* v___x_3440_, lean_object* v_a_3441_, lean_object* v_xs_3442_, lean_object* v___x_3443_, lean_object* v_a_3444_, lean_object* v_recArgInfos_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_){
_start:
{
size_t v___x_15811__boxed_3451_; lean_object* v_res_3452_; 
v___x_15811__boxed_3451_ = lean_unbox_usize(v___x_3440_);
lean_dec(v___x_3440_);
v_res_3452_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0(v___x_15811__boxed_3451_, v_a_3441_, v_xs_3442_, v___x_3443_, v_a_3444_, v_recArgInfos_3445_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_);
lean_dec(v___y_3449_);
lean_dec_ref(v___y_3448_);
lean_dec(v___y_3447_);
lean_dec_ref(v___y_3446_);
return v_res_3452_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg(lean_object* v___x_3453_, lean_object* v_xs_3454_, lean_object* v_as_3455_, lean_object* v_i_3456_, lean_object* v_j_3457_, lean_object* v_bs_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_){
_start:
{
lean_object* v_zero_3464_; uint8_t v_isZero_3465_; 
v_zero_3464_ = lean_unsigned_to_nat(0u);
v_isZero_3465_ = lean_nat_dec_eq(v_i_3456_, v_zero_3464_);
if (v_isZero_3465_ == 1)
{
lean_object* v___x_3466_; 
lean_dec(v_j_3457_);
lean_dec(v_i_3456_);
lean_dec_ref(v_xs_3454_);
v___x_3466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3466_, 0, v_bs_3458_);
return v___x_3466_;
}
else
{
lean_object* v___x_3467_; lean_object* v_value_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; 
v___x_3467_ = lean_array_fget_borrowed(v_as_3455_, v_j_3457_);
v_value_3468_ = lean_ctor_get(v___x_3467_, 7);
v___x_3469_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0, &l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0_once, _init_l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0);
v___x_3470_ = lean_array_get_borrowed(v___x_3469_, v___x_3453_, v_j_3457_);
lean_inc_ref(v_xs_3454_);
lean_inc_ref(v_value_3468_);
lean_inc(v___x_3470_);
v___x_3471_ = l_Lean_Elab_FixedParamPerm_instantiateLambda(v___x_3470_, v_value_3468_, v_xs_3454_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_);
if (lean_obj_tag(v___x_3471_) == 0)
{
lean_object* v_a_3472_; lean_object* v_one_3473_; lean_object* v_n_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; 
v_a_3472_ = lean_ctor_get(v___x_3471_, 0);
lean_inc(v_a_3472_);
lean_dec_ref(v___x_3471_);
v_one_3473_ = lean_unsigned_to_nat(1u);
v_n_3474_ = lean_nat_sub(v_i_3456_, v_one_3473_);
lean_dec(v_i_3456_);
v___x_3475_ = lean_nat_add(v_j_3457_, v_one_3473_);
lean_dec(v_j_3457_);
v___x_3476_ = lean_array_push(v_bs_3458_, v_a_3472_);
v_i_3456_ = v_n_3474_;
v_j_3457_ = v___x_3475_;
v_bs_3458_ = v___x_3476_;
goto _start;
}
else
{
lean_object* v_a_3478_; lean_object* v___x_3480_; uint8_t v_isShared_3481_; uint8_t v_isSharedCheck_3485_; 
lean_dec_ref(v_bs_3458_);
lean_dec(v_j_3457_);
lean_dec(v_i_3456_);
lean_dec_ref(v_xs_3454_);
v_a_3478_ = lean_ctor_get(v___x_3471_, 0);
v_isSharedCheck_3485_ = !lean_is_exclusive(v___x_3471_);
if (v_isSharedCheck_3485_ == 0)
{
v___x_3480_ = v___x_3471_;
v_isShared_3481_ = v_isSharedCheck_3485_;
goto v_resetjp_3479_;
}
else
{
lean_inc(v_a_3478_);
lean_dec(v___x_3471_);
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
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg___boxed(lean_object* v___x_3486_, lean_object* v_xs_3487_, lean_object* v_as_3488_, lean_object* v_i_3489_, lean_object* v_j_3490_, lean_object* v_bs_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_){
_start:
{
lean_object* v_res_3497_; 
v_res_3497_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg(v___x_3486_, v_xs_3487_, v_as_3488_, v_i_3489_, v_j_3490_, v_bs_3491_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_);
lean_dec(v___y_3495_);
lean_dec_ref(v___y_3494_);
lean_dec(v___y_3493_);
lean_dec_ref(v___y_3492_);
lean_dec_ref(v_as_3488_);
lean_dec_ref(v___x_3486_);
return v_res_3497_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__2(lean_object* v_a_3498_, lean_object* v_perms_3499_, lean_object* v___x_3500_, lean_object* v_fnNames_3501_, lean_object* v_a_3502_, lean_object* v_termMeasure_x3fs_3503_, size_t v___x_3504_, lean_object* v_xs_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_){
_start:
{
lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; 
v___x_3511_ = lean_array_get_size(v_a_3498_);
v___x_3512_ = lean_mk_empty_array_with_capacity(v___x_3511_);
lean_inc(v___x_3500_);
lean_inc_ref(v_xs_3505_);
v___x_3513_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg(v_perms_3499_, v_xs_3505_, v_a_3498_, v___x_3511_, v___x_3500_, v___x_3512_, v___y_3506_, v___y_3507_, v___y_3508_, v___y_3509_);
if (lean_obj_tag(v___x_3513_) == 0)
{
lean_object* v_a_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; 
v_a_3514_ = lean_ctor_get(v___x_3513_, 0);
lean_inc_n(v_a_3514_, 2);
lean_dec_ref(v___x_3513_);
lean_inc_ref(v_xs_3505_);
lean_inc_ref(v_a_3502_);
lean_inc_ref(v_fnNames_3501_);
v___x_3515_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_findRecArgCandidates___boxed), 10, 5);
lean_closure_set(v___x_3515_, 0, v_fnNames_3501_);
lean_closure_set(v___x_3515_, 1, v_a_3502_);
lean_closure_set(v___x_3515_, 2, v_xs_3505_);
lean_closure_set(v___x_3515_, 3, v_a_3514_);
lean_closure_set(v___x_3515_, 4, v_termMeasure_x3fs_3503_);
lean_inc_ref(v_a_3498_);
v___x_3516_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v_a_3498_, v___x_3515_, v___y_3506_, v___y_3507_, v___y_3508_, v___y_3509_);
if (lean_obj_tag(v___x_3516_) == 0)
{
lean_object* v_a_3517_; lean_object* v___x_3518_; lean_object* v___f_3519_; lean_object* v___x_3520_; 
v_a_3517_ = lean_ctor_get(v___x_3516_, 0);
lean_inc(v_a_3517_);
lean_dec_ref(v___x_3516_);
v___x_3518_ = lean_box_usize(v___x_3504_);
lean_inc_ref(v_xs_3505_);
v___f_3519_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___boxed), 11, 5);
lean_closure_set(v___f_3519_, 0, v___x_3518_);
lean_closure_set(v___f_3519_, 1, v_a_3502_);
lean_closure_set(v___f_3519_, 2, v_xs_3505_);
lean_closure_set(v___f_3519_, 3, v___x_3500_);
lean_closure_set(v___f_3519_, 4, v_a_3498_);
v___x_3520_ = l_Lean_Elab_Structural_tryCandidates___redArg(v_fnNames_3501_, v_xs_3505_, v_a_3514_, v_a_3517_, v___f_3519_, v___y_3506_, v___y_3507_, v___y_3508_, v___y_3509_);
lean_dec_ref(v_fnNames_3501_);
return v___x_3520_;
}
else
{
lean_object* v_a_3521_; lean_object* v___x_3523_; uint8_t v_isShared_3524_; uint8_t v_isSharedCheck_3528_; 
lean_dec(v_a_3514_);
lean_dec_ref(v_xs_3505_);
lean_dec_ref(v_a_3502_);
lean_dec_ref(v_fnNames_3501_);
lean_dec(v___x_3500_);
lean_dec_ref(v_a_3498_);
v_a_3521_ = lean_ctor_get(v___x_3516_, 0);
v_isSharedCheck_3528_ = !lean_is_exclusive(v___x_3516_);
if (v_isSharedCheck_3528_ == 0)
{
v___x_3523_ = v___x_3516_;
v_isShared_3524_ = v_isSharedCheck_3528_;
goto v_resetjp_3522_;
}
else
{
lean_inc(v_a_3521_);
lean_dec(v___x_3516_);
v___x_3523_ = lean_box(0);
v_isShared_3524_ = v_isSharedCheck_3528_;
goto v_resetjp_3522_;
}
v_resetjp_3522_:
{
lean_object* v___x_3526_; 
if (v_isShared_3524_ == 0)
{
v___x_3526_ = v___x_3523_;
goto v_reusejp_3525_;
}
else
{
lean_object* v_reuseFailAlloc_3527_; 
v_reuseFailAlloc_3527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3527_, 0, v_a_3521_);
v___x_3526_ = v_reuseFailAlloc_3527_;
goto v_reusejp_3525_;
}
v_reusejp_3525_:
{
return v___x_3526_;
}
}
}
}
else
{
lean_object* v_a_3529_; lean_object* v___x_3531_; uint8_t v_isShared_3532_; uint8_t v_isSharedCheck_3536_; 
lean_dec_ref(v_xs_3505_);
lean_dec_ref(v_termMeasure_x3fs_3503_);
lean_dec_ref(v_a_3502_);
lean_dec_ref(v_fnNames_3501_);
lean_dec(v___x_3500_);
lean_dec_ref(v_a_3498_);
v_a_3529_ = lean_ctor_get(v___x_3513_, 0);
v_isSharedCheck_3536_ = !lean_is_exclusive(v___x_3513_);
if (v_isSharedCheck_3536_ == 0)
{
v___x_3531_ = v___x_3513_;
v_isShared_3532_ = v_isSharedCheck_3536_;
goto v_resetjp_3530_;
}
else
{
lean_inc(v_a_3529_);
lean_dec(v___x_3513_);
v___x_3531_ = lean_box(0);
v_isShared_3532_ = v_isSharedCheck_3536_;
goto v_resetjp_3530_;
}
v_resetjp_3530_:
{
lean_object* v___x_3534_; 
if (v_isShared_3532_ == 0)
{
v___x_3534_ = v___x_3531_;
goto v_reusejp_3533_;
}
else
{
lean_object* v_reuseFailAlloc_3535_; 
v_reuseFailAlloc_3535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3535_, 0, v_a_3529_);
v___x_3534_ = v_reuseFailAlloc_3535_;
goto v_reusejp_3533_;
}
v_reusejp_3533_:
{
return v___x_3534_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__2___boxed(lean_object* v_a_3537_, lean_object* v_perms_3538_, lean_object* v___x_3539_, lean_object* v_fnNames_3540_, lean_object* v_a_3541_, lean_object* v_termMeasure_x3fs_3542_, lean_object* v___x_3543_, lean_object* v_xs_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_){
_start:
{
size_t v___x_16168__boxed_3550_; lean_object* v_res_3551_; 
v___x_16168__boxed_3550_ = lean_unbox_usize(v___x_3543_);
lean_dec(v___x_3543_);
v_res_3551_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__2(v_a_3537_, v_perms_3538_, v___x_3539_, v_fnNames_3540_, v_a_3541_, v_termMeasure_x3fs_3542_, v___x_16168__boxed_3550_, v_xs_3544_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_);
lean_dec(v___y_3548_);
lean_dec_ref(v___y_3547_);
lean_dec(v___y_3546_);
lean_dec_ref(v___y_3545_);
lean_dec_ref(v_perms_3538_);
return v_res_3551_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0(size_t v_sz_3552_, size_t v_i_3553_, lean_object* v_bs_3554_){
_start:
{
uint8_t v___x_3555_; 
v___x_3555_ = lean_usize_dec_lt(v_i_3553_, v_sz_3552_);
if (v___x_3555_ == 0)
{
return v_bs_3554_;
}
else
{
lean_object* v_v_3556_; lean_object* v_declName_3557_; lean_object* v___x_3558_; lean_object* v_bs_x27_3559_; size_t v___x_3560_; size_t v___x_3561_; lean_object* v___x_3562_; 
v_v_3556_ = lean_array_uget_borrowed(v_bs_3554_, v_i_3553_);
v_declName_3557_ = lean_ctor_get(v_v_3556_, 3);
lean_inc(v_declName_3557_);
v___x_3558_ = lean_unsigned_to_nat(0u);
v_bs_x27_3559_ = lean_array_uset(v_bs_3554_, v_i_3553_, v___x_3558_);
v___x_3560_ = ((size_t)1ULL);
v___x_3561_ = lean_usize_add(v_i_3553_, v___x_3560_);
v___x_3562_ = lean_array_uset(v_bs_x27_3559_, v_i_3553_, v_declName_3557_);
v_i_3553_ = v___x_3561_;
v_bs_3554_ = v___x_3562_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0___boxed(lean_object* v_sz_3564_, lean_object* v_i_3565_, lean_object* v_bs_3566_){
_start:
{
size_t v_sz_boxed_3567_; size_t v_i_boxed_3568_; lean_object* v_res_3569_; 
v_sz_boxed_3567_ = lean_unbox_usize(v_sz_3564_);
lean_dec(v_sz_3564_);
v_i_boxed_3568_ = lean_unbox_usize(v_i_3565_);
lean_dec(v_i_3565_);
v_res_3569_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0(v_sz_boxed_3567_, v_i_boxed_3568_, v_bs_3566_);
return v_res_3569_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1___redArg(lean_object* v_fnNames_3570_, lean_object* v_numSectionVars_3571_, size_t v_sz_3572_, size_t v_i_3573_, lean_object* v_bs_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_){
_start:
{
uint8_t v___x_3578_; 
v___x_3578_ = lean_usize_dec_lt(v_i_3573_, v_sz_3572_);
if (v___x_3578_ == 0)
{
lean_object* v___x_3579_; 
lean_dec(v_numSectionVars_3571_);
lean_dec_ref(v_fnNames_3570_);
v___x_3579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3579_, 0, v_bs_3574_);
return v___x_3579_;
}
else
{
lean_object* v_v_3580_; lean_object* v_ref_3581_; uint8_t v_kind_3582_; lean_object* v_levelParams_3583_; lean_object* v_modifiers_3584_; lean_object* v_declName_3585_; lean_object* v_binders_3586_; lean_object* v_numSectionVars_3587_; lean_object* v_type_3588_; lean_object* v_value_3589_; lean_object* v_termination_3590_; lean_object* v___x_3592_; uint8_t v_isShared_3593_; uint8_t v_isSharedCheck_3613_; 
v_v_3580_ = lean_array_uget(v_bs_3574_, v_i_3573_);
v_ref_3581_ = lean_ctor_get(v_v_3580_, 0);
v_kind_3582_ = lean_ctor_get_uint8(v_v_3580_, sizeof(void*)*9);
v_levelParams_3583_ = lean_ctor_get(v_v_3580_, 1);
v_modifiers_3584_ = lean_ctor_get(v_v_3580_, 2);
v_declName_3585_ = lean_ctor_get(v_v_3580_, 3);
v_binders_3586_ = lean_ctor_get(v_v_3580_, 4);
v_numSectionVars_3587_ = lean_ctor_get(v_v_3580_, 5);
v_type_3588_ = lean_ctor_get(v_v_3580_, 6);
v_value_3589_ = lean_ctor_get(v_v_3580_, 7);
v_termination_3590_ = lean_ctor_get(v_v_3580_, 8);
v_isSharedCheck_3613_ = !lean_is_exclusive(v_v_3580_);
if (v_isSharedCheck_3613_ == 0)
{
v___x_3592_ = v_v_3580_;
v_isShared_3593_ = v_isSharedCheck_3613_;
goto v_resetjp_3591_;
}
else
{
lean_inc(v_termination_3590_);
lean_inc(v_value_3589_);
lean_inc(v_type_3588_);
lean_inc(v_numSectionVars_3587_);
lean_inc(v_binders_3586_);
lean_inc(v_declName_3585_);
lean_inc(v_modifiers_3584_);
lean_inc(v_levelParams_3583_);
lean_inc(v_ref_3581_);
lean_dec(v_v_3580_);
v___x_3592_ = lean_box(0);
v_isShared_3593_ = v_isSharedCheck_3613_;
goto v_resetjp_3591_;
}
v_resetjp_3591_:
{
lean_object* v___x_3594_; 
lean_inc(v_numSectionVars_3571_);
lean_inc_ref(v_fnNames_3570_);
v___x_3594_ = l_Lean_Elab_Structural_preprocess(v_value_3589_, v_fnNames_3570_, v_numSectionVars_3571_, v___y_3575_, v___y_3576_);
if (lean_obj_tag(v___x_3594_) == 0)
{
lean_object* v_a_3595_; lean_object* v___x_3596_; lean_object* v_bs_x27_3597_; lean_object* v___x_3599_; 
v_a_3595_ = lean_ctor_get(v___x_3594_, 0);
lean_inc(v_a_3595_);
lean_dec_ref(v___x_3594_);
v___x_3596_ = lean_unsigned_to_nat(0u);
v_bs_x27_3597_ = lean_array_uset(v_bs_3574_, v_i_3573_, v___x_3596_);
if (v_isShared_3593_ == 0)
{
lean_ctor_set(v___x_3592_, 7, v_a_3595_);
v___x_3599_ = v___x_3592_;
goto v_reusejp_3598_;
}
else
{
lean_object* v_reuseFailAlloc_3604_; 
v_reuseFailAlloc_3604_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_3604_, 0, v_ref_3581_);
lean_ctor_set(v_reuseFailAlloc_3604_, 1, v_levelParams_3583_);
lean_ctor_set(v_reuseFailAlloc_3604_, 2, v_modifiers_3584_);
lean_ctor_set(v_reuseFailAlloc_3604_, 3, v_declName_3585_);
lean_ctor_set(v_reuseFailAlloc_3604_, 4, v_binders_3586_);
lean_ctor_set(v_reuseFailAlloc_3604_, 5, v_numSectionVars_3587_);
lean_ctor_set(v_reuseFailAlloc_3604_, 6, v_type_3588_);
lean_ctor_set(v_reuseFailAlloc_3604_, 7, v_a_3595_);
lean_ctor_set(v_reuseFailAlloc_3604_, 8, v_termination_3590_);
lean_ctor_set_uint8(v_reuseFailAlloc_3604_, sizeof(void*)*9, v_kind_3582_);
v___x_3599_ = v_reuseFailAlloc_3604_;
goto v_reusejp_3598_;
}
v_reusejp_3598_:
{
size_t v___x_3600_; size_t v___x_3601_; lean_object* v___x_3602_; 
v___x_3600_ = ((size_t)1ULL);
v___x_3601_ = lean_usize_add(v_i_3573_, v___x_3600_);
v___x_3602_ = lean_array_uset(v_bs_x27_3597_, v_i_3573_, v___x_3599_);
v_i_3573_ = v___x_3601_;
v_bs_3574_ = v___x_3602_;
goto _start;
}
}
else
{
lean_object* v_a_3605_; lean_object* v___x_3607_; uint8_t v_isShared_3608_; uint8_t v_isSharedCheck_3612_; 
lean_del_object(v___x_3592_);
lean_dec_ref(v_termination_3590_);
lean_dec_ref(v_type_3588_);
lean_dec(v_numSectionVars_3587_);
lean_dec(v_binders_3586_);
lean_dec(v_declName_3585_);
lean_dec_ref(v_modifiers_3584_);
lean_dec(v_levelParams_3583_);
lean_dec(v_ref_3581_);
lean_dec_ref(v_bs_3574_);
lean_dec(v_numSectionVars_3571_);
lean_dec_ref(v_fnNames_3570_);
v_a_3605_ = lean_ctor_get(v___x_3594_, 0);
v_isSharedCheck_3612_ = !lean_is_exclusive(v___x_3594_);
if (v_isSharedCheck_3612_ == 0)
{
v___x_3607_ = v___x_3594_;
v_isShared_3608_ = v_isSharedCheck_3612_;
goto v_resetjp_3606_;
}
else
{
lean_inc(v_a_3605_);
lean_dec(v___x_3594_);
v___x_3607_ = lean_box(0);
v_isShared_3608_ = v_isSharedCheck_3612_;
goto v_resetjp_3606_;
}
v_resetjp_3606_:
{
lean_object* v___x_3610_; 
if (v_isShared_3608_ == 0)
{
v___x_3610_ = v___x_3607_;
goto v_reusejp_3609_;
}
else
{
lean_object* v_reuseFailAlloc_3611_; 
v_reuseFailAlloc_3611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3611_, 0, v_a_3605_);
v___x_3610_ = v_reuseFailAlloc_3611_;
goto v_reusejp_3609_;
}
v_reusejp_3609_:
{
return v___x_3610_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1___redArg___boxed(lean_object* v_fnNames_3614_, lean_object* v_numSectionVars_3615_, lean_object* v_sz_3616_, lean_object* v_i_3617_, lean_object* v_bs_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_){
_start:
{
size_t v_sz_boxed_3622_; size_t v_i_boxed_3623_; lean_object* v_res_3624_; 
v_sz_boxed_3622_ = lean_unbox_usize(v_sz_3616_);
lean_dec(v_sz_3616_);
v_i_boxed_3623_ = lean_unbox_usize(v_i_3617_);
lean_dec(v_i_3617_);
v_res_3624_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1___redArg(v_fnNames_3614_, v_numSectionVars_3615_, v_sz_boxed_3622_, v_i_boxed_3623_, v_bs_3618_, v___y_3619_, v___y_3620_);
lean_dec(v___y_3620_);
lean_dec_ref(v___y_3619_);
return v_res_3624_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1(lean_object* v_fnNames_3625_, lean_object* v_numSectionVars_3626_, size_t v_sz_3627_, size_t v_i_3628_, lean_object* v_bs_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_){
_start:
{
lean_object* v___x_3635_; 
v___x_3635_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1___redArg(v_fnNames_3625_, v_numSectionVars_3626_, v_sz_3627_, v_i_3628_, v_bs_3629_, v___y_3632_, v___y_3633_);
return v___x_3635_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1___boxed(lean_object* v_fnNames_3636_, lean_object* v_numSectionVars_3637_, lean_object* v_sz_3638_, lean_object* v_i_3639_, lean_object* v_bs_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_){
_start:
{
size_t v_sz_boxed_3646_; size_t v_i_boxed_3647_; lean_object* v_res_3648_; 
v_sz_boxed_3646_ = lean_unbox_usize(v_sz_3638_);
lean_dec(v_sz_3638_);
v_i_boxed_3647_ = lean_unbox_usize(v_i_3639_);
lean_dec(v_i_3639_);
v_res_3648_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1(v_fnNames_3636_, v_numSectionVars_3637_, v_sz_boxed_3646_, v_i_boxed_3647_, v_bs_3640_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_);
lean_dec(v___y_3644_);
lean_dec_ref(v___y_3643_);
lean_dec(v___y_3642_);
lean_dec_ref(v___y_3641_);
return v_res_3648_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos(lean_object* v_preDefs_3649_, lean_object* v_termMeasure_x3fs_3650_, lean_object* v_a_3651_, lean_object* v_a_3652_, lean_object* v_a_3653_, lean_object* v_a_3654_){
_start:
{
lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v_numSectionVars_3659_; size_t v_sz_3660_; size_t v___x_3661_; lean_object* v_fnNames_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; 
v___x_3656_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_3657_ = lean_unsigned_to_nat(0u);
v___x_3658_ = lean_array_get_borrowed(v___x_3656_, v_preDefs_3649_, v___x_3657_);
v_numSectionVars_3659_ = lean_ctor_get(v___x_3658_, 5);
v_sz_3660_ = lean_array_size(v_preDefs_3649_);
v___x_3661_ = ((size_t)0ULL);
lean_inc_ref_n(v_preDefs_3649_, 2);
v_fnNames_3662_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0(v_sz_3660_, v___x_3661_, v_preDefs_3649_);
v___x_3663_ = lean_box_usize(v_sz_3660_);
v___x_3664_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___boxed__const__1));
lean_inc(v_numSectionVars_3659_);
lean_inc_ref(v_fnNames_3662_);
v___x_3665_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1___boxed), 10, 5);
lean_closure_set(v___x_3665_, 0, v_fnNames_3662_);
lean_closure_set(v___x_3665_, 1, v_numSectionVars_3659_);
lean_closure_set(v___x_3665_, 2, v___x_3663_);
lean_closure_set(v___x_3665_, 3, v___x_3664_);
lean_closure_set(v___x_3665_, 4, v_preDefs_3649_);
v___x_3666_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v_preDefs_3649_, v___x_3665_, v_a_3651_, v_a_3652_, v_a_3653_, v_a_3654_);
if (lean_obj_tag(v___x_3666_) == 0)
{
lean_object* v_a_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; 
v_a_3667_ = lean_ctor_get(v___x_3666_, 0);
lean_inc_n(v_a_3667_, 3);
lean_dec_ref(v___x_3666_);
v___x_3668_ = lean_alloc_closure((void*)(l_Lean_Elab_getFixedParamPerms___boxed), 6, 1);
lean_closure_set(v___x_3668_, 0, v_a_3667_);
v___x_3669_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v_a_3667_, v___x_3668_, v_a_3651_, v_a_3652_, v_a_3653_, v_a_3654_);
if (lean_obj_tag(v___x_3669_) == 0)
{
lean_object* v_a_3670_; lean_object* v_perms_3671_; lean_object* v___x_3672_; lean_object* v_type_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___f_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; 
v_a_3670_ = lean_ctor_get(v___x_3669_, 0);
lean_inc(v_a_3670_);
lean_dec_ref(v___x_3669_);
v_perms_3671_ = lean_ctor_get(v_a_3670_, 1);
lean_inc_ref_n(v_perms_3671_, 2);
v___x_3672_ = lean_array_get_borrowed(v___x_3656_, v_a_3667_, v___x_3657_);
v_type_3673_ = lean_ctor_get(v___x_3672_, 6);
lean_inc_ref(v_type_3673_);
v___x_3674_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0, &l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0_once, _init_l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0);
v___x_3675_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___boxed__const__1));
v___f_3676_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__2___boxed), 13, 7);
lean_closure_set(v___f_3676_, 0, v_a_3667_);
lean_closure_set(v___f_3676_, 1, v_perms_3671_);
lean_closure_set(v___f_3676_, 2, v___x_3657_);
lean_closure_set(v___f_3676_, 3, v_fnNames_3662_);
lean_closure_set(v___f_3676_, 4, v_a_3670_);
lean_closure_set(v___f_3676_, 5, v_termMeasure_x3fs_3650_);
lean_closure_set(v___f_3676_, 6, v___x_3675_);
v___x_3677_ = lean_array_get(v___x_3674_, v_perms_3671_, v___x_3657_);
lean_dec_ref(v_perms_3671_);
v___x_3678_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg(v___x_3677_, v_type_3673_, v___f_3676_, v_a_3651_, v_a_3652_, v_a_3653_, v_a_3654_);
return v___x_3678_;
}
else
{
lean_object* v_a_3679_; lean_object* v___x_3681_; uint8_t v_isShared_3682_; uint8_t v_isSharedCheck_3686_; 
lean_dec(v_a_3667_);
lean_dec_ref(v_fnNames_3662_);
lean_dec_ref(v_termMeasure_x3fs_3650_);
v_a_3679_ = lean_ctor_get(v___x_3669_, 0);
v_isSharedCheck_3686_ = !lean_is_exclusive(v___x_3669_);
if (v_isSharedCheck_3686_ == 0)
{
v___x_3681_ = v___x_3669_;
v_isShared_3682_ = v_isSharedCheck_3686_;
goto v_resetjp_3680_;
}
else
{
lean_inc(v_a_3679_);
lean_dec(v___x_3669_);
v___x_3681_ = lean_box(0);
v_isShared_3682_ = v_isSharedCheck_3686_;
goto v_resetjp_3680_;
}
v_resetjp_3680_:
{
lean_object* v___x_3684_; 
if (v_isShared_3682_ == 0)
{
v___x_3684_ = v___x_3681_;
goto v_reusejp_3683_;
}
else
{
lean_object* v_reuseFailAlloc_3685_; 
v_reuseFailAlloc_3685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3685_, 0, v_a_3679_);
v___x_3684_ = v_reuseFailAlloc_3685_;
goto v_reusejp_3683_;
}
v_reusejp_3683_:
{
return v___x_3684_;
}
}
}
}
else
{
lean_object* v_a_3687_; lean_object* v___x_3689_; uint8_t v_isShared_3690_; uint8_t v_isSharedCheck_3694_; 
lean_dec_ref(v_fnNames_3662_);
lean_dec_ref(v_termMeasure_x3fs_3650_);
v_a_3687_ = lean_ctor_get(v___x_3666_, 0);
v_isSharedCheck_3694_ = !lean_is_exclusive(v___x_3666_);
if (v_isSharedCheck_3694_ == 0)
{
v___x_3689_ = v___x_3666_;
v_isShared_3690_ = v_isSharedCheck_3694_;
goto v_resetjp_3688_;
}
else
{
lean_inc(v_a_3687_);
lean_dec(v___x_3666_);
v___x_3689_ = lean_box(0);
v_isShared_3690_ = v_isSharedCheck_3694_;
goto v_resetjp_3688_;
}
v_resetjp_3688_:
{
lean_object* v___x_3692_; 
if (v_isShared_3690_ == 0)
{
v___x_3692_ = v___x_3689_;
goto v_reusejp_3691_;
}
else
{
lean_object* v_reuseFailAlloc_3693_; 
v_reuseFailAlloc_3693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3693_, 0, v_a_3687_);
v___x_3692_ = v_reuseFailAlloc_3693_;
goto v_reusejp_3691_;
}
v_reusejp_3691_:
{
return v___x_3692_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___boxed(lean_object* v_preDefs_3695_, lean_object* v_termMeasure_x3fs_3696_, lean_object* v_a_3697_, lean_object* v_a_3698_, lean_object* v_a_3699_, lean_object* v_a_3700_, lean_object* v_a_3701_){
_start:
{
lean_object* v_res_3702_; 
v_res_3702_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos(v_preDefs_3695_, v_termMeasure_x3fs_3696_, v_a_3697_, v_a_3698_, v_a_3699_, v_a_3700_);
lean_dec(v_a_3700_);
lean_dec_ref(v_a_3699_);
lean_dec(v_a_3698_);
lean_dec_ref(v_a_3697_);
return v_res_3702_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4(lean_object* v_fst_3703_, lean_object* v_as_3704_, lean_object* v_i_3705_, lean_object* v_j_3706_, lean_object* v_inv_3707_, lean_object* v_bs_3708_){
_start:
{
lean_object* v___x_3709_; 
v___x_3709_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg(v_fst_3703_, v_as_3704_, v_i_3705_, v_j_3706_, v_bs_3708_);
return v___x_3709_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___boxed(lean_object* v_fst_3710_, lean_object* v_as_3711_, lean_object* v_i_3712_, lean_object* v_j_3713_, lean_object* v_inv_3714_, lean_object* v_bs_3715_){
_start:
{
lean_object* v_res_3716_; 
v_res_3716_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4(v_fst_3710_, v_as_3711_, v_i_3712_, v_j_3713_, v_inv_3714_, v_bs_3715_);
lean_dec_ref(v_as_3711_);
lean_dec_ref(v_fst_3710_);
return v_res_3716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10(lean_object* v_00_u03b1_3717_, lean_object* v_lctx_3718_, lean_object* v_localInsts_3719_, lean_object* v_x_3720_, lean_object* v___y_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_){
_start:
{
lean_object* v___x_3726_; 
v___x_3726_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___redArg(v_lctx_3718_, v_localInsts_3719_, v_x_3720_, v___y_3721_, v___y_3722_, v___y_3723_, v___y_3724_);
return v___x_3726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___boxed(lean_object* v_00_u03b1_3727_, lean_object* v_lctx_3728_, lean_object* v_localInsts_3729_, lean_object* v_x_3730_, lean_object* v___y_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_){
_start:
{
lean_object* v_res_3736_; 
v_res_3736_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10(v_00_u03b1_3727_, v_lctx_3728_, v_localInsts_3729_, v_x_3730_, v___y_3731_, v___y_3732_, v___y_3733_, v___y_3734_);
lean_dec(v___y_3734_);
lean_dec_ref(v___y_3733_);
lean_dec(v___y_3732_);
lean_dec_ref(v___y_3731_);
return v_res_3736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9(lean_object* v_00_u03b1_3737_, lean_object* v_fvarIds_3738_, lean_object* v_k_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_){
_start:
{
lean_object* v___x_3745_; 
v___x_3745_ = l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___redArg(v_fvarIds_3738_, v_k_3739_, v___y_3740_, v___y_3741_, v___y_3742_, v___y_3743_);
return v___x_3745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___boxed(lean_object* v_00_u03b1_3746_, lean_object* v_fvarIds_3747_, lean_object* v_k_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_){
_start:
{
lean_object* v_res_3754_; 
v_res_3754_ = l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9(v_00_u03b1_3746_, v_fvarIds_3747_, v_k_3748_, v___y_3749_, v___y_3750_, v___y_3751_, v___y_3752_);
lean_dec(v___y_3752_);
lean_dec_ref(v___y_3751_);
lean_dec(v___y_3750_);
lean_dec_ref(v___y_3749_);
lean_dec_ref(v_fvarIds_3747_);
return v_res_3754_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__15(lean_object* v_a_3755_){
_start:
{
lean_object* v___x_3756_; 
v___x_3756_ = lean_nat_to_int(v_a_3755_);
return v___x_3756_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12(lean_object* v___x_3757_, lean_object* v_xs_3758_, lean_object* v_as_3759_, lean_object* v_i_3760_, lean_object* v_j_3761_, lean_object* v_inv_3762_, lean_object* v_bs_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_){
_start:
{
lean_object* v___x_3769_; 
v___x_3769_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg(v___x_3757_, v_xs_3758_, v_as_3759_, v_i_3760_, v_j_3761_, v_bs_3763_, v___y_3764_, v___y_3765_, v___y_3766_, v___y_3767_);
return v___x_3769_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___boxed(lean_object* v___x_3770_, lean_object* v_xs_3771_, lean_object* v_as_3772_, lean_object* v_i_3773_, lean_object* v_j_3774_, lean_object* v_inv_3775_, lean_object* v_bs_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_){
_start:
{
lean_object* v_res_3782_; 
v_res_3782_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12(v___x_3770_, v_xs_3771_, v_as_3772_, v_i_3773_, v_j_3774_, v_inv_3775_, v_bs_3776_, v___y_3777_, v___y_3778_, v___y_3779_, v___y_3780_);
lean_dec(v___y_3780_);
lean_dec_ref(v___y_3779_);
lean_dec(v___y_3778_);
lean_dec_ref(v___y_3777_);
lean_dec_ref(v_as_3772_);
lean_dec_ref(v___x_3770_);
return v_res_3782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure___lam__0(lean_object* v___x_3783_, lean_object* v_recArgPos_3784_, lean_object* v_xs_3785_, lean_object* v_x_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_){
_start:
{
lean_object* v___x_3792_; uint8_t v___x_3793_; uint8_t v___x_3794_; uint8_t v___x_3795_; lean_object* v___x_3796_; 
v___x_3792_ = lean_array_get_borrowed(v___x_3783_, v_xs_3785_, v_recArgPos_3784_);
v___x_3793_ = 0;
v___x_3794_ = 1;
v___x_3795_ = 1;
lean_inc(v___x_3792_);
v___x_3796_ = l_Lean_Meta_mkLambdaFVars(v_xs_3785_, v___x_3792_, v___x_3793_, v___x_3794_, v___x_3793_, v___x_3794_, v___x_3795_, v___y_3787_, v___y_3788_, v___y_3789_, v___y_3790_);
return v___x_3796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure___lam__0___boxed(lean_object* v___x_3797_, lean_object* v_recArgPos_3798_, lean_object* v_xs_3799_, lean_object* v_x_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_){
_start:
{
lean_object* v_res_3806_; 
v_res_3806_ = l_Lean_Elab_Structural_reportTermMeasure___lam__0(v___x_3797_, v_recArgPos_3798_, v_xs_3799_, v_x_3800_, v___y_3801_, v___y_3802_, v___y_3803_, v___y_3804_);
lean_dec(v___y_3804_);
lean_dec_ref(v___y_3803_);
lean_dec(v___y_3802_);
lean_dec_ref(v___y_3801_);
lean_dec_ref(v_x_3800_);
lean_dec_ref(v_xs_3799_);
lean_dec(v_recArgPos_3798_);
lean_dec_ref(v___x_3797_);
return v_res_3806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure___lam__1(lean_object* v_xs_3807_, lean_object* v_x_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_){
_start:
{
lean_object* v___x_3814_; lean_object* v___x_3815_; 
v___x_3814_ = lean_array_get_size(v_xs_3807_);
v___x_3815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3815_, 0, v___x_3814_);
return v___x_3815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure___lam__1___boxed(lean_object* v_xs_3816_, lean_object* v_x_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_){
_start:
{
lean_object* v_res_3823_; 
v_res_3823_ = l_Lean_Elab_Structural_reportTermMeasure___lam__1(v_xs_3816_, v_x_3817_, v___y_3818_, v___y_3819_, v___y_3820_, v___y_3821_);
lean_dec(v___y_3821_);
lean_dec_ref(v___y_3820_);
lean_dec(v___y_3819_);
lean_dec_ref(v___y_3818_);
lean_dec_ref(v_x_3817_);
lean_dec_ref(v_xs_3816_);
return v_res_3823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure(lean_object* v_preDef_3835_, lean_object* v_recArgPos_3836_, lean_object* v_a_3837_, lean_object* v_a_3838_, lean_object* v_a_3839_, lean_object* v_a_3840_){
_start:
{
lean_object* v_termination_3842_; lean_object* v_terminationBy_x3f_x3f_3843_; 
v_termination_3842_ = lean_ctor_get(v_preDef_3835_, 8);
lean_inc_ref(v_termination_3842_);
v_terminationBy_x3f_x3f_3843_ = lean_ctor_get(v_termination_3842_, 1);
lean_inc(v_terminationBy_x3f_x3f_3843_);
if (lean_obj_tag(v_terminationBy_x3f_x3f_3843_) == 1)
{
lean_object* v_value_3844_; lean_object* v_extraParams_3845_; lean_object* v___x_3847_; uint8_t v_isShared_3848_; uint8_t v_isSharedCheck_3896_; 
v_value_3844_ = lean_ctor_get(v_preDef_3835_, 7);
lean_inc_ref(v_value_3844_);
lean_dec_ref(v_preDef_3835_);
v_extraParams_3845_ = lean_ctor_get(v_termination_3842_, 5);
v_isSharedCheck_3896_ = !lean_is_exclusive(v_termination_3842_);
if (v_isSharedCheck_3896_ == 0)
{
lean_object* v_unused_3897_; lean_object* v_unused_3898_; lean_object* v_unused_3899_; lean_object* v_unused_3900_; lean_object* v_unused_3901_; 
v_unused_3897_ = lean_ctor_get(v_termination_3842_, 4);
lean_dec(v_unused_3897_);
v_unused_3898_ = lean_ctor_get(v_termination_3842_, 3);
lean_dec(v_unused_3898_);
v_unused_3899_ = lean_ctor_get(v_termination_3842_, 2);
lean_dec(v_unused_3899_);
v_unused_3900_ = lean_ctor_get(v_termination_3842_, 1);
lean_dec(v_unused_3900_);
v_unused_3901_ = lean_ctor_get(v_termination_3842_, 0);
lean_dec(v_unused_3901_);
v___x_3847_ = v_termination_3842_;
v_isShared_3848_ = v_isSharedCheck_3896_;
goto v_resetjp_3846_;
}
else
{
lean_inc(v_extraParams_3845_);
lean_dec(v_termination_3842_);
v___x_3847_ = lean_box(0);
v_isShared_3848_ = v_isSharedCheck_3896_;
goto v_resetjp_3846_;
}
v_resetjp_3846_:
{
lean_object* v_val_3849_; lean_object* v___x_3850_; lean_object* v___f_3851_; uint8_t v___x_3852_; lean_object* v___x_3853_; 
v_val_3849_ = lean_ctor_get(v_terminationBy_x3f_x3f_3843_, 0);
lean_inc(v_val_3849_);
lean_dec_ref(v_terminationBy_x3f_x3f_3843_);
v___x_3850_ = l_Lean_instInhabitedExpr;
v___f_3851_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_reportTermMeasure___lam__0___boxed), 9, 2);
lean_closure_set(v___f_3851_, 0, v___x_3850_);
lean_closure_set(v___f_3851_, 1, v_recArgPos_3836_);
v___x_3852_ = 0;
lean_inc_ref(v_value_3844_);
v___x_3853_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg(v_value_3844_, v___f_3851_, v___x_3852_, v_a_3837_, v_a_3838_, v_a_3839_, v_a_3840_);
if (lean_obj_tag(v___x_3853_) == 0)
{
lean_object* v_a_3854_; lean_object* v___f_3855_; lean_object* v___x_3856_; 
v_a_3854_ = lean_ctor_get(v___x_3853_, 0);
lean_inc(v_a_3854_);
lean_dec_ref(v___x_3853_);
v___f_3855_ = ((lean_object*)(l_Lean_Elab_Structural_reportTermMeasure___closed__0));
v___x_3856_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg(v_value_3844_, v___f_3855_, v___x_3852_, v_a_3837_, v_a_3838_, v_a_3839_, v_a_3840_);
if (lean_obj_tag(v___x_3856_) == 0)
{
lean_object* v_a_3857_; lean_object* v___x_3858_; uint8_t v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; 
v_a_3857_ = lean_ctor_get(v___x_3856_, 0);
lean_inc(v_a_3857_);
lean_dec_ref(v___x_3856_);
v___x_3858_ = lean_box(0);
v___x_3859_ = 1;
v___x_3860_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3860_, 0, v___x_3858_);
lean_ctor_set(v___x_3860_, 1, v_a_3854_);
lean_ctor_set_uint8(v___x_3860_, sizeof(void*)*2, v___x_3859_);
v___x_3861_ = l_Lean_Elab_TerminationMeasure_delab(v_a_3857_, v_extraParams_3845_, v___x_3860_, v_a_3837_, v_a_3838_, v_a_3839_, v_a_3840_);
lean_dec(v_a_3857_);
if (lean_obj_tag(v___x_3861_) == 0)
{
lean_object* v_a_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3867_; 
v_a_3862_ = lean_ctor_get(v___x_3861_, 0);
lean_inc(v_a_3862_);
lean_dec_ref(v___x_3861_);
v___x_3863_ = ((lean_object*)(l_Lean_Elab_Structural_reportTermMeasure___closed__5));
v___x_3864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3864_, 0, v___x_3863_);
lean_ctor_set(v___x_3864_, 1, v_a_3862_);
v___x_3865_ = lean_box(0);
if (v_isShared_3848_ == 0)
{
lean_ctor_set(v___x_3847_, 5, v___x_3865_);
lean_ctor_set(v___x_3847_, 4, v___x_3865_);
lean_ctor_set(v___x_3847_, 3, v___x_3865_);
lean_ctor_set(v___x_3847_, 2, v___x_3865_);
lean_ctor_set(v___x_3847_, 1, v___x_3865_);
lean_ctor_set(v___x_3847_, 0, v___x_3864_);
v___x_3867_ = v___x_3847_;
goto v_reusejp_3866_;
}
else
{
lean_object* v_reuseFailAlloc_3871_; 
v_reuseFailAlloc_3871_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3871_, 0, v___x_3864_);
lean_ctor_set(v_reuseFailAlloc_3871_, 1, v___x_3865_);
lean_ctor_set(v_reuseFailAlloc_3871_, 2, v___x_3865_);
lean_ctor_set(v_reuseFailAlloc_3871_, 3, v___x_3865_);
lean_ctor_set(v_reuseFailAlloc_3871_, 4, v___x_3865_);
lean_ctor_set(v_reuseFailAlloc_3871_, 5, v___x_3865_);
v___x_3867_ = v_reuseFailAlloc_3871_;
goto v_reusejp_3866_;
}
v_reusejp_3866_:
{
lean_object* v___x_3868_; uint8_t v___x_3869_; lean_object* v___x_3870_; 
v___x_3868_ = ((lean_object*)(l_Lean_Elab_Structural_reportTermMeasure___closed__6));
v___x_3869_ = 4;
v___x_3870_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_val_3849_, v___x_3867_, v___x_3865_, v___x_3868_, v___x_3865_, v___x_3869_, v_a_3839_, v_a_3840_);
return v___x_3870_;
}
}
else
{
lean_object* v_a_3872_; lean_object* v___x_3874_; uint8_t v_isShared_3875_; uint8_t v_isSharedCheck_3879_; 
lean_dec(v_val_3849_);
lean_del_object(v___x_3847_);
v_a_3872_ = lean_ctor_get(v___x_3861_, 0);
v_isSharedCheck_3879_ = !lean_is_exclusive(v___x_3861_);
if (v_isSharedCheck_3879_ == 0)
{
v___x_3874_ = v___x_3861_;
v_isShared_3875_ = v_isSharedCheck_3879_;
goto v_resetjp_3873_;
}
else
{
lean_inc(v_a_3872_);
lean_dec(v___x_3861_);
v___x_3874_ = lean_box(0);
v_isShared_3875_ = v_isSharedCheck_3879_;
goto v_resetjp_3873_;
}
v_resetjp_3873_:
{
lean_object* v___x_3877_; 
if (v_isShared_3875_ == 0)
{
v___x_3877_ = v___x_3874_;
goto v_reusejp_3876_;
}
else
{
lean_object* v_reuseFailAlloc_3878_; 
v_reuseFailAlloc_3878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3878_, 0, v_a_3872_);
v___x_3877_ = v_reuseFailAlloc_3878_;
goto v_reusejp_3876_;
}
v_reusejp_3876_:
{
return v___x_3877_;
}
}
}
}
else
{
lean_object* v_a_3880_; lean_object* v___x_3882_; uint8_t v_isShared_3883_; uint8_t v_isSharedCheck_3887_; 
lean_dec(v_a_3854_);
lean_dec(v_val_3849_);
lean_del_object(v___x_3847_);
lean_dec(v_extraParams_3845_);
v_a_3880_ = lean_ctor_get(v___x_3856_, 0);
v_isSharedCheck_3887_ = !lean_is_exclusive(v___x_3856_);
if (v_isSharedCheck_3887_ == 0)
{
v___x_3882_ = v___x_3856_;
v_isShared_3883_ = v_isSharedCheck_3887_;
goto v_resetjp_3881_;
}
else
{
lean_inc(v_a_3880_);
lean_dec(v___x_3856_);
v___x_3882_ = lean_box(0);
v_isShared_3883_ = v_isSharedCheck_3887_;
goto v_resetjp_3881_;
}
v_resetjp_3881_:
{
lean_object* v___x_3885_; 
if (v_isShared_3883_ == 0)
{
v___x_3885_ = v___x_3882_;
goto v_reusejp_3884_;
}
else
{
lean_object* v_reuseFailAlloc_3886_; 
v_reuseFailAlloc_3886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3886_, 0, v_a_3880_);
v___x_3885_ = v_reuseFailAlloc_3886_;
goto v_reusejp_3884_;
}
v_reusejp_3884_:
{
return v___x_3885_;
}
}
}
}
else
{
lean_object* v_a_3888_; lean_object* v___x_3890_; uint8_t v_isShared_3891_; uint8_t v_isSharedCheck_3895_; 
lean_dec(v_val_3849_);
lean_del_object(v___x_3847_);
lean_dec(v_extraParams_3845_);
lean_dec_ref(v_value_3844_);
v_a_3888_ = lean_ctor_get(v___x_3853_, 0);
v_isSharedCheck_3895_ = !lean_is_exclusive(v___x_3853_);
if (v_isSharedCheck_3895_ == 0)
{
v___x_3890_ = v___x_3853_;
v_isShared_3891_ = v_isSharedCheck_3895_;
goto v_resetjp_3889_;
}
else
{
lean_inc(v_a_3888_);
lean_dec(v___x_3853_);
v___x_3890_ = lean_box(0);
v_isShared_3891_ = v_isSharedCheck_3895_;
goto v_resetjp_3889_;
}
v_resetjp_3889_:
{
lean_object* v___x_3893_; 
if (v_isShared_3891_ == 0)
{
v___x_3893_ = v___x_3890_;
goto v_reusejp_3892_;
}
else
{
lean_object* v_reuseFailAlloc_3894_; 
v_reuseFailAlloc_3894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3894_, 0, v_a_3888_);
v___x_3893_ = v_reuseFailAlloc_3894_;
goto v_reusejp_3892_;
}
v_reusejp_3892_:
{
return v___x_3893_;
}
}
}
}
}
else
{
lean_object* v___x_3902_; lean_object* v___x_3903_; 
lean_dec(v_terminationBy_x3f_x3f_3843_);
lean_dec_ref(v_termination_3842_);
lean_dec(v_recArgPos_3836_);
lean_dec_ref(v_preDef_3835_);
v___x_3902_ = lean_box(0);
v___x_3903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3903_, 0, v___x_3902_);
return v___x_3903_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure___boxed(lean_object* v_preDef_3904_, lean_object* v_recArgPos_3905_, lean_object* v_a_3906_, lean_object* v_a_3907_, lean_object* v_a_3908_, lean_object* v_a_3909_, lean_object* v_a_3910_){
_start:
{
lean_object* v_res_3911_; 
v_res_3911_ = l_Lean_Elab_Structural_reportTermMeasure(v_preDef_3904_, v_recArgPos_3905_, v_a_3906_, v_a_3907_, v_a_3908_, v_a_3909_);
lean_dec(v_a_3909_);
lean_dec_ref(v_a_3908_);
lean_dec(v_a_3907_);
lean_dec_ref(v_a_3906_);
return v_res_3911_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___redArg(lean_object* v_as_3912_, size_t v_sz_3913_, size_t v_i_3914_, lean_object* v_b_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_){
_start:
{
uint8_t v___x_3921_; 
v___x_3921_ = lean_usize_dec_lt(v_i_3914_, v_sz_3913_);
if (v___x_3921_ == 0)
{
lean_object* v___x_3922_; 
v___x_3922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3922_, 0, v_b_3915_);
return v___x_3922_;
}
else
{
lean_object* v_a_3923_; lean_object* v_declName_3924_; lean_object* v___x_3925_; 
v_a_3923_ = lean_array_uget_borrowed(v_as_3912_, v_i_3914_);
v_declName_3924_ = lean_ctor_get(v_a_3923_, 3);
lean_inc(v_declName_3924_);
v___x_3925_ = l_Lean_enableRealizationsForConst(v_declName_3924_, v___y_3918_, v___y_3919_);
if (lean_obj_tag(v___x_3925_) == 0)
{
lean_object* v___x_3926_; 
lean_dec_ref(v___x_3925_);
lean_inc(v_declName_3924_);
v___x_3926_ = l_Lean_Meta_generateEagerEqns(v_declName_3924_, v___y_3916_, v___y_3917_, v___y_3918_, v___y_3919_);
if (lean_obj_tag(v___x_3926_) == 0)
{
lean_object* v___x_3927_; size_t v___x_3928_; size_t v___x_3929_; 
lean_dec_ref(v___x_3926_);
v___x_3927_ = lean_box(0);
v___x_3928_ = ((size_t)1ULL);
v___x_3929_ = lean_usize_add(v_i_3914_, v___x_3928_);
v_i_3914_ = v___x_3929_;
v_b_3915_ = v___x_3927_;
goto _start;
}
else
{
return v___x_3926_;
}
}
else
{
return v___x_3925_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___redArg___boxed(lean_object* v_as_3931_, lean_object* v_sz_3932_, lean_object* v_i_3933_, lean_object* v_b_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_){
_start:
{
size_t v_sz_boxed_3940_; size_t v_i_boxed_3941_; lean_object* v_res_3942_; 
v_sz_boxed_3940_ = lean_unbox_usize(v_sz_3932_);
lean_dec(v_sz_3932_);
v_i_boxed_3941_ = lean_unbox_usize(v_i_3933_);
lean_dec(v_i_3933_);
v_res_3942_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___redArg(v_as_3931_, v_sz_boxed_3940_, v_i_boxed_3941_, v_b_3934_, v___y_3935_, v___y_3936_, v___y_3937_, v___y_3938_);
lean_dec(v___y_3938_);
lean_dec_ref(v___y_3937_);
lean_dec(v___y_3936_);
lean_dec_ref(v___y_3935_);
lean_dec_ref(v_as_3931_);
return v_res_3942_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4___lam__0(lean_object* v___x_3943_, lean_object* v_e_3944_){
_start:
{
lean_object* v___x_3945_; lean_object* v___x_3946_; 
v___x_3945_ = l_Lean_indentD(v_e_3944_);
v___x_3946_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3946_, 0, v___x_3943_);
lean_ctor_set(v___x_3946_, 1, v___x_3945_);
return v___x_3946_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4___lam__1(lean_object* v_docCtx_3947_, lean_object* v_a_3948_, uint8_t v___x_3949_, lean_object* v___x_3950_, uint8_t v___x_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_){
_start:
{
lean_object* v___x_3959_; 
v___x_3959_ = l_Lean_Elab_addNonRec(v_docCtx_3947_, v_a_3948_, v___x_3949_, v___x_3950_, v___x_3951_, v___x_3949_, v___x_3951_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_, v___y_3956_, v___y_3957_);
return v___x_3959_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4___lam__1___boxed(lean_object* v_docCtx_3960_, lean_object* v_a_3961_, lean_object* v___x_3962_, lean_object* v___x_3963_, lean_object* v___x_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_){
_start:
{
uint8_t v___x_8569__boxed_3972_; uint8_t v___x_8571__boxed_3973_; lean_object* v_res_3974_; 
v___x_8569__boxed_3972_ = lean_unbox(v___x_3962_);
v___x_8571__boxed_3973_ = lean_unbox(v___x_3964_);
v_res_3974_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4___lam__1(v_docCtx_3960_, v_a_3961_, v___x_8569__boxed_3972_, v___x_3963_, v___x_8571__boxed_3973_, v___y_3965_, v___y_3966_, v___y_3967_, v___y_3968_, v___y_3969_, v___y_3970_);
lean_dec(v___y_3970_);
lean_dec_ref(v___y_3969_);
lean_dec(v___y_3968_);
lean_dec_ref(v___y_3967_);
lean_dec(v___y_3966_);
lean_dec_ref(v___y_3965_);
return v_res_3974_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4___closed__1(void){
_start:
{
lean_object* v___x_3976_; lean_object* v___x_3977_; 
v___x_3976_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4___closed__0));
v___x_3977_ = l_Lean_stringToMessageData(v___x_3976_);
return v___x_3977_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4___closed__2(void){
_start:
{
lean_object* v___x_3978_; lean_object* v___f_3979_; 
v___x_3978_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4___closed__1);
v___f_3979_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4___lam__0), 2, 1);
lean_closure_set(v___f_3979_, 0, v___x_3978_);
return v___f_3979_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4(lean_object* v_names_3980_, lean_object* v_docCtx_3981_, lean_object* v_as_3982_, size_t v_i_3983_, size_t v_stop_3984_, lean_object* v_b_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_){
_start:
{
uint8_t v___x_3993_; 
v___x_3993_ = lean_usize_dec_eq(v_i_3983_, v_stop_3984_);
if (v___x_3993_ == 0)
{
lean_object* v___x_3994_; lean_object* v___x_3995_; 
v___x_3994_ = lean_array_uget_borrowed(v_as_3982_, v_i_3983_);
lean_inc(v___x_3994_);
v___x_3995_ = l_Lean_Elab_eraseRecAppSyntax(v___x_3994_, v___y_3990_, v___y_3991_);
if (lean_obj_tag(v___x_3995_) == 0)
{
lean_object* v_a_3996_; lean_object* v___f_3997_; lean_object* v___x_3998_; uint8_t v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___f_4002_; lean_object* v___x_4003_; 
v_a_3996_ = lean_ctor_get(v___x_3995_, 0);
lean_inc(v_a_3996_);
lean_dec_ref(v___x_3995_);
v___f_3997_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4___closed__2, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4___closed__2);
lean_inc_ref(v_names_3980_);
v___x_3998_ = lean_array_to_list(v_names_3980_);
v___x_3999_ = 1;
v___x_4000_ = lean_box(v___x_3993_);
v___x_4001_ = lean_box(v___x_3999_);
lean_inc(v___y_3987_);
lean_inc_ref(v___y_3986_);
lean_inc_ref(v_docCtx_3981_);
v___f_4002_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4___lam__1___boxed), 12, 7);
lean_closure_set(v___f_4002_, 0, v_docCtx_3981_);
lean_closure_set(v___f_4002_, 1, v_a_3996_);
lean_closure_set(v___f_4002_, 2, v___x_4000_);
lean_closure_set(v___f_4002_, 3, v___x_3998_);
lean_closure_set(v___f_4002_, 4, v___x_4001_);
lean_closure_set(v___f_4002_, 5, v___y_3986_);
lean_closure_set(v___f_4002_, 6, v___y_3987_);
v___x_4003_ = l_Lean_Meta_mapErrorImp___redArg(v___f_4002_, v___f_3997_, v___y_3988_, v___y_3989_, v___y_3990_, v___y_3991_);
if (lean_obj_tag(v___x_4003_) == 0)
{
if (lean_obj_tag(v___x_4003_) == 0)
{
lean_object* v_a_4004_; size_t v___x_4005_; size_t v___x_4006_; 
v_a_4004_ = lean_ctor_get(v___x_4003_, 0);
lean_inc(v_a_4004_);
lean_dec_ref(v___x_4003_);
v___x_4005_ = ((size_t)1ULL);
v___x_4006_ = lean_usize_add(v_i_3983_, v___x_4005_);
v_i_3983_ = v___x_4006_;
v_b_3985_ = v_a_4004_;
goto _start;
}
else
{
lean_dec_ref(v_docCtx_3981_);
lean_dec_ref(v_names_3980_);
return v___x_4003_;
}
}
else
{
lean_object* v_a_4008_; lean_object* v___x_4010_; uint8_t v_isShared_4011_; uint8_t v_isSharedCheck_4015_; 
lean_dec_ref(v_docCtx_3981_);
lean_dec_ref(v_names_3980_);
v_a_4008_ = lean_ctor_get(v___x_4003_, 0);
v_isSharedCheck_4015_ = !lean_is_exclusive(v___x_4003_);
if (v_isSharedCheck_4015_ == 0)
{
v___x_4010_ = v___x_4003_;
v_isShared_4011_ = v_isSharedCheck_4015_;
goto v_resetjp_4009_;
}
else
{
lean_inc(v_a_4008_);
lean_dec(v___x_4003_);
v___x_4010_ = lean_box(0);
v_isShared_4011_ = v_isSharedCheck_4015_;
goto v_resetjp_4009_;
}
v_resetjp_4009_:
{
lean_object* v___x_4013_; 
if (v_isShared_4011_ == 0)
{
v___x_4013_ = v___x_4010_;
goto v_reusejp_4012_;
}
else
{
lean_object* v_reuseFailAlloc_4014_; 
v_reuseFailAlloc_4014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4014_, 0, v_a_4008_);
v___x_4013_ = v_reuseFailAlloc_4014_;
goto v_reusejp_4012_;
}
v_reusejp_4012_:
{
return v___x_4013_;
}
}
}
}
else
{
lean_object* v_a_4016_; lean_object* v___x_4018_; uint8_t v_isShared_4019_; uint8_t v_isSharedCheck_4023_; 
lean_dec_ref(v_docCtx_3981_);
lean_dec_ref(v_names_3980_);
v_a_4016_ = lean_ctor_get(v___x_3995_, 0);
v_isSharedCheck_4023_ = !lean_is_exclusive(v___x_3995_);
if (v_isSharedCheck_4023_ == 0)
{
v___x_4018_ = v___x_3995_;
v_isShared_4019_ = v_isSharedCheck_4023_;
goto v_resetjp_4017_;
}
else
{
lean_inc(v_a_4016_);
lean_dec(v___x_3995_);
v___x_4018_ = lean_box(0);
v_isShared_4019_ = v_isSharedCheck_4023_;
goto v_resetjp_4017_;
}
v_resetjp_4017_:
{
lean_object* v___x_4021_; 
if (v_isShared_4019_ == 0)
{
v___x_4021_ = v___x_4018_;
goto v_reusejp_4020_;
}
else
{
lean_object* v_reuseFailAlloc_4022_; 
v_reuseFailAlloc_4022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4022_, 0, v_a_4016_);
v___x_4021_ = v_reuseFailAlloc_4022_;
goto v_reusejp_4020_;
}
v_reusejp_4020_:
{
return v___x_4021_;
}
}
}
}
else
{
lean_object* v___x_4024_; 
lean_dec_ref(v_docCtx_3981_);
lean_dec_ref(v_names_3980_);
v___x_4024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4024_, 0, v_b_3985_);
return v___x_4024_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4___boxed(lean_object* v_names_4025_, lean_object* v_docCtx_4026_, lean_object* v_as_4027_, lean_object* v_i_4028_, lean_object* v_stop_4029_, lean_object* v_b_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_){
_start:
{
size_t v_i_boxed_4038_; size_t v_stop_boxed_4039_; lean_object* v_res_4040_; 
v_i_boxed_4038_ = lean_unbox_usize(v_i_4028_);
lean_dec(v_i_4028_);
v_stop_boxed_4039_ = lean_unbox_usize(v_stop_4029_);
lean_dec(v_stop_4029_);
v_res_4040_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4(v_names_4025_, v_docCtx_4026_, v_as_4027_, v_i_boxed_4038_, v_stop_boxed_4039_, v_b_4030_, v___y_4031_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_, v___y_4036_);
lean_dec(v___y_4036_);
lean_dec_ref(v___y_4035_);
lean_dec(v___y_4034_);
lean_dec_ref(v___y_4033_);
lean_dec(v___y_4032_);
lean_dec_ref(v___y_4031_);
lean_dec_ref(v_as_4027_);
return v_res_4040_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__1(lean_object* v_docCtx_4041_, lean_object* v_a_4042_, lean_object* v_snd_4043_, lean_object* v_as_4044_, size_t v_sz_4045_, size_t v_i_4046_, lean_object* v_b_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_, lean_object* v___y_4053_){
_start:
{
uint8_t v___x_4055_; 
v___x_4055_ = lean_usize_dec_lt(v_i_4046_, v_sz_4045_);
if (v___x_4055_ == 0)
{
lean_object* v___x_4056_; 
lean_dec_ref(v_snd_4043_);
lean_dec_ref(v_a_4042_);
lean_dec_ref(v_docCtx_4041_);
v___x_4056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4056_, 0, v_b_4047_);
return v___x_4056_;
}
else
{
lean_object* v_array_4057_; lean_object* v_start_4058_; lean_object* v_stop_4059_; uint8_t v___x_4060_; 
v_array_4057_ = lean_ctor_get(v_b_4047_, 0);
v_start_4058_ = lean_ctor_get(v_b_4047_, 1);
v_stop_4059_ = lean_ctor_get(v_b_4047_, 2);
v___x_4060_ = lean_nat_dec_lt(v_start_4058_, v_stop_4059_);
if (v___x_4060_ == 0)
{
lean_object* v___x_4061_; 
lean_dec_ref(v_snd_4043_);
lean_dec_ref(v_a_4042_);
lean_dec_ref(v_docCtx_4041_);
v___x_4061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4061_, 0, v_b_4047_);
return v___x_4061_;
}
else
{
lean_object* v___x_4063_; uint8_t v_isShared_4064_; uint8_t v_isSharedCheck_4128_; 
lean_inc(v_stop_4059_);
lean_inc(v_start_4058_);
lean_inc_ref(v_array_4057_);
v_isSharedCheck_4128_ = !lean_is_exclusive(v_b_4047_);
if (v_isSharedCheck_4128_ == 0)
{
lean_object* v_unused_4129_; lean_object* v_unused_4130_; lean_object* v_unused_4131_; 
v_unused_4129_ = lean_ctor_get(v_b_4047_, 2);
lean_dec(v_unused_4129_);
v_unused_4130_ = lean_ctor_get(v_b_4047_, 1);
lean_dec(v_unused_4130_);
v_unused_4131_ = lean_ctor_get(v_b_4047_, 0);
lean_dec(v_unused_4131_);
v___x_4063_ = v_b_4047_;
v_isShared_4064_ = v_isSharedCheck_4128_;
goto v_resetjp_4062_;
}
else
{
lean_dec(v_b_4047_);
v___x_4063_ = lean_box(0);
v_isShared_4064_ = v_isSharedCheck_4128_;
goto v_resetjp_4062_;
}
v_resetjp_4062_:
{
lean_object* v_a_4065_; uint8_t v_kind_4066_; lean_object* v_type_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4072_; 
v_a_4065_ = lean_array_uget_borrowed(v_as_4044_, v_i_4046_);
v_kind_4066_ = lean_ctor_get_uint8(v_a_4065_, sizeof(void*)*9);
v_type_4067_ = lean_ctor_get(v_a_4065_, 6);
v___x_4068_ = lean_array_fget(v_array_4057_, v_start_4058_);
v___x_4069_ = lean_unsigned_to_nat(1u);
v___x_4070_ = lean_nat_add(v_start_4058_, v___x_4069_);
lean_dec(v_start_4058_);
if (v_isShared_4064_ == 0)
{
lean_ctor_set(v___x_4063_, 1, v___x_4070_);
v___x_4072_ = v___x_4063_;
goto v_reusejp_4071_;
}
else
{
lean_object* v_reuseFailAlloc_4127_; 
v_reuseFailAlloc_4127_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4127_, 0, v_array_4057_);
lean_ctor_set(v_reuseFailAlloc_4127_, 1, v___x_4070_);
lean_ctor_set(v_reuseFailAlloc_4127_, 2, v_stop_4059_);
v___x_4072_ = v_reuseFailAlloc_4127_;
goto v_reusejp_4071_;
}
v_reusejp_4071_:
{
lean_object* v_preDef_4074_; lean_object* v___y_4075_; lean_object* v___y_4076_; lean_object* v___y_4077_; lean_object* v___y_4078_; lean_object* v___y_4079_; lean_object* v___y_4080_; uint8_t v___x_4093_; 
v___x_4093_ = l_Lean_Elab_DefKind_isTheorem(v_kind_4066_);
if (v___x_4093_ == 0)
{
lean_object* v___x_4094_; 
lean_inc_ref(v_type_4067_);
v___x_4094_ = l_Lean_Meta_isProp(v_type_4067_, v___y_4050_, v___y_4051_, v___y_4052_, v___y_4053_);
if (lean_obj_tag(v___x_4094_) == 0)
{
lean_object* v_a_4095_; uint8_t v___x_4096_; 
v_a_4095_ = lean_ctor_get(v___x_4094_, 0);
lean_inc(v_a_4095_);
lean_dec_ref(v___x_4094_);
v___x_4096_ = lean_unbox(v_a_4095_);
lean_dec(v_a_4095_);
if (v___x_4096_ == 0)
{
lean_object* v___x_4097_; 
lean_inc(v_a_4065_);
v___x_4097_ = l_Lean_Elab_abstractNestedProofs(v_a_4065_, v___x_4060_, v___y_4050_, v___y_4051_, v___y_4052_, v___y_4053_);
if (lean_obj_tag(v___x_4097_) == 0)
{
lean_object* v_a_4098_; size_t v_sz_4099_; size_t v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; 
v_a_4098_ = lean_ctor_get(v___x_4097_, 0);
lean_inc_n(v_a_4098_, 2);
lean_dec_ref(v___x_4097_);
v_sz_4099_ = lean_array_size(v_a_4042_);
v___x_4100_ = ((size_t)0ULL);
lean_inc_ref(v_a_4042_);
v___x_4101_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0(v_sz_4099_, v___x_4100_, v_a_4042_);
lean_inc_ref(v_snd_4043_);
lean_inc(v___x_4068_);
v___x_4102_ = l_Lean_Elab_Structural_registerEqnsInfo(v_a_4098_, v___x_4101_, v___x_4068_, v_snd_4043_, v___y_4052_, v___y_4053_);
if (lean_obj_tag(v___x_4102_) == 0)
{
lean_dec_ref(v___x_4102_);
v_preDef_4074_ = v_a_4098_;
v___y_4075_ = v___y_4048_;
v___y_4076_ = v___y_4049_;
v___y_4077_ = v___y_4050_;
v___y_4078_ = v___y_4051_;
v___y_4079_ = v___y_4052_;
v___y_4080_ = v___y_4053_;
goto v___jp_4073_;
}
else
{
lean_object* v_a_4103_; lean_object* v___x_4105_; uint8_t v_isShared_4106_; uint8_t v_isSharedCheck_4110_; 
lean_dec(v_a_4098_);
lean_dec_ref(v___x_4072_);
lean_dec(v___x_4068_);
lean_dec_ref(v_snd_4043_);
lean_dec_ref(v_a_4042_);
lean_dec_ref(v_docCtx_4041_);
v_a_4103_ = lean_ctor_get(v___x_4102_, 0);
v_isSharedCheck_4110_ = !lean_is_exclusive(v___x_4102_);
if (v_isSharedCheck_4110_ == 0)
{
v___x_4105_ = v___x_4102_;
v_isShared_4106_ = v_isSharedCheck_4110_;
goto v_resetjp_4104_;
}
else
{
lean_inc(v_a_4103_);
lean_dec(v___x_4102_);
v___x_4105_ = lean_box(0);
v_isShared_4106_ = v_isSharedCheck_4110_;
goto v_resetjp_4104_;
}
v_resetjp_4104_:
{
lean_object* v___x_4108_; 
if (v_isShared_4106_ == 0)
{
v___x_4108_ = v___x_4105_;
goto v_reusejp_4107_;
}
else
{
lean_object* v_reuseFailAlloc_4109_; 
v_reuseFailAlloc_4109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4109_, 0, v_a_4103_);
v___x_4108_ = v_reuseFailAlloc_4109_;
goto v_reusejp_4107_;
}
v_reusejp_4107_:
{
return v___x_4108_;
}
}
}
}
else
{
lean_object* v_a_4111_; lean_object* v___x_4113_; uint8_t v_isShared_4114_; uint8_t v_isSharedCheck_4118_; 
lean_dec_ref(v___x_4072_);
lean_dec(v___x_4068_);
lean_dec_ref(v_snd_4043_);
lean_dec_ref(v_a_4042_);
lean_dec_ref(v_docCtx_4041_);
v_a_4111_ = lean_ctor_get(v___x_4097_, 0);
v_isSharedCheck_4118_ = !lean_is_exclusive(v___x_4097_);
if (v_isSharedCheck_4118_ == 0)
{
v___x_4113_ = v___x_4097_;
v_isShared_4114_ = v_isSharedCheck_4118_;
goto v_resetjp_4112_;
}
else
{
lean_inc(v_a_4111_);
lean_dec(v___x_4097_);
v___x_4113_ = lean_box(0);
v_isShared_4114_ = v_isSharedCheck_4118_;
goto v_resetjp_4112_;
}
v_resetjp_4112_:
{
lean_object* v___x_4116_; 
if (v_isShared_4114_ == 0)
{
v___x_4116_ = v___x_4113_;
goto v_reusejp_4115_;
}
else
{
lean_object* v_reuseFailAlloc_4117_; 
v_reuseFailAlloc_4117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4117_, 0, v_a_4111_);
v___x_4116_ = v_reuseFailAlloc_4117_;
goto v_reusejp_4115_;
}
v_reusejp_4115_:
{
return v___x_4116_;
}
}
}
}
else
{
lean_inc(v_a_4065_);
v_preDef_4074_ = v_a_4065_;
v___y_4075_ = v___y_4048_;
v___y_4076_ = v___y_4049_;
v___y_4077_ = v___y_4050_;
v___y_4078_ = v___y_4051_;
v___y_4079_ = v___y_4052_;
v___y_4080_ = v___y_4053_;
goto v___jp_4073_;
}
}
else
{
lean_object* v_a_4119_; lean_object* v___x_4121_; uint8_t v_isShared_4122_; uint8_t v_isSharedCheck_4126_; 
lean_dec_ref(v___x_4072_);
lean_dec(v___x_4068_);
lean_dec_ref(v_snd_4043_);
lean_dec_ref(v_a_4042_);
lean_dec_ref(v_docCtx_4041_);
v_a_4119_ = lean_ctor_get(v___x_4094_, 0);
v_isSharedCheck_4126_ = !lean_is_exclusive(v___x_4094_);
if (v_isSharedCheck_4126_ == 0)
{
v___x_4121_ = v___x_4094_;
v_isShared_4122_ = v_isSharedCheck_4126_;
goto v_resetjp_4120_;
}
else
{
lean_inc(v_a_4119_);
lean_dec(v___x_4094_);
v___x_4121_ = lean_box(0);
v_isShared_4122_ = v_isSharedCheck_4126_;
goto v_resetjp_4120_;
}
v_resetjp_4120_:
{
lean_object* v___x_4124_; 
if (v_isShared_4122_ == 0)
{
v___x_4124_ = v___x_4121_;
goto v_reusejp_4123_;
}
else
{
lean_object* v_reuseFailAlloc_4125_; 
v_reuseFailAlloc_4125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4125_, 0, v_a_4119_);
v___x_4124_ = v_reuseFailAlloc_4125_;
goto v_reusejp_4123_;
}
v_reusejp_4123_:
{
return v___x_4124_;
}
}
}
}
else
{
lean_inc(v_a_4065_);
v_preDef_4074_ = v_a_4065_;
v___y_4075_ = v___y_4048_;
v___y_4076_ = v___y_4049_;
v___y_4077_ = v___y_4050_;
v___y_4078_ = v___y_4051_;
v___y_4079_ = v___y_4052_;
v___y_4080_ = v___y_4053_;
goto v___jp_4073_;
}
v___jp_4073_:
{
lean_object* v___x_4081_; 
lean_inc_ref(v_docCtx_4041_);
v___x_4081_ = l_Lean_Elab_Structural_addSmartUnfoldingDef(v_docCtx_4041_, v_preDef_4074_, v___x_4068_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_);
if (lean_obj_tag(v___x_4081_) == 0)
{
size_t v___x_4082_; size_t v___x_4083_; 
lean_dec_ref(v___x_4081_);
v___x_4082_ = ((size_t)1ULL);
v___x_4083_ = lean_usize_add(v_i_4046_, v___x_4082_);
v_i_4046_ = v___x_4083_;
v_b_4047_ = v___x_4072_;
goto _start;
}
else
{
lean_object* v_a_4085_; lean_object* v___x_4087_; uint8_t v_isShared_4088_; uint8_t v_isSharedCheck_4092_; 
lean_dec_ref(v___x_4072_);
lean_dec_ref(v_snd_4043_);
lean_dec_ref(v_a_4042_);
lean_dec_ref(v_docCtx_4041_);
v_a_4085_ = lean_ctor_get(v___x_4081_, 0);
v_isSharedCheck_4092_ = !lean_is_exclusive(v___x_4081_);
if (v_isSharedCheck_4092_ == 0)
{
v___x_4087_ = v___x_4081_;
v_isShared_4088_ = v_isSharedCheck_4092_;
goto v_resetjp_4086_;
}
else
{
lean_inc(v_a_4085_);
lean_dec(v___x_4081_);
v___x_4087_ = lean_box(0);
v_isShared_4088_ = v_isSharedCheck_4092_;
goto v_resetjp_4086_;
}
v_resetjp_4086_:
{
lean_object* v___x_4090_; 
if (v_isShared_4088_ == 0)
{
v___x_4090_ = v___x_4087_;
goto v_reusejp_4089_;
}
else
{
lean_object* v_reuseFailAlloc_4091_; 
v_reuseFailAlloc_4091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4091_, 0, v_a_4085_);
v___x_4090_ = v_reuseFailAlloc_4091_;
goto v_reusejp_4089_;
}
v_reusejp_4089_:
{
return v___x_4090_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__1___boxed(lean_object* v_docCtx_4132_, lean_object* v_a_4133_, lean_object* v_snd_4134_, lean_object* v_as_4135_, lean_object* v_sz_4136_, lean_object* v_i_4137_, lean_object* v_b_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_){
_start:
{
size_t v_sz_boxed_4146_; size_t v_i_boxed_4147_; lean_object* v_res_4148_; 
v_sz_boxed_4146_ = lean_unbox_usize(v_sz_4136_);
lean_dec(v_sz_4136_);
v_i_boxed_4147_ = lean_unbox_usize(v_i_4137_);
lean_dec(v_i_4137_);
v_res_4148_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__1(v_docCtx_4132_, v_a_4133_, v_snd_4134_, v_as_4135_, v_sz_boxed_4146_, v_i_boxed_4147_, v_b_4138_, v___y_4139_, v___y_4140_, v___y_4141_, v___y_4142_, v___y_4143_, v___y_4144_);
lean_dec(v___y_4144_);
lean_dec_ref(v___y_4143_);
lean_dec(v___y_4142_);
lean_dec_ref(v___y_4141_);
lean_dec(v___y_4140_);
lean_dec_ref(v___y_4139_);
lean_dec_ref(v_as_4135_);
return v_res_4148_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___redArg(size_t v_sz_4149_, size_t v_i_4150_, lean_object* v_bs_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_){
_start:
{
uint8_t v___x_4155_; 
v___x_4155_ = lean_usize_dec_lt(v_i_4150_, v_sz_4149_);
if (v___x_4155_ == 0)
{
lean_object* v___x_4156_; 
v___x_4156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4156_, 0, v_bs_4151_);
return v___x_4156_;
}
else
{
lean_object* v_v_4157_; lean_object* v___x_4158_; 
v_v_4157_ = lean_array_uget_borrowed(v_bs_4151_, v_i_4150_);
lean_inc(v_v_4157_);
v___x_4158_ = l_Lean_Elab_eraseRecAppSyntax(v_v_4157_, v___y_4152_, v___y_4153_);
if (lean_obj_tag(v___x_4158_) == 0)
{
lean_object* v_a_4159_; lean_object* v___x_4160_; lean_object* v_bs_x27_4161_; size_t v___x_4162_; size_t v___x_4163_; lean_object* v___x_4164_; 
v_a_4159_ = lean_ctor_get(v___x_4158_, 0);
lean_inc(v_a_4159_);
lean_dec_ref(v___x_4158_);
v___x_4160_ = lean_unsigned_to_nat(0u);
v_bs_x27_4161_ = lean_array_uset(v_bs_4151_, v_i_4150_, v___x_4160_);
v___x_4162_ = ((size_t)1ULL);
v___x_4163_ = lean_usize_add(v_i_4150_, v___x_4162_);
v___x_4164_ = lean_array_uset(v_bs_x27_4161_, v_i_4150_, v_a_4159_);
v_i_4150_ = v___x_4163_;
v_bs_4151_ = v___x_4164_;
goto _start;
}
else
{
lean_object* v_a_4166_; lean_object* v___x_4168_; uint8_t v_isShared_4169_; uint8_t v_isSharedCheck_4173_; 
lean_dec_ref(v_bs_4151_);
v_a_4166_ = lean_ctor_get(v___x_4158_, 0);
v_isSharedCheck_4173_ = !lean_is_exclusive(v___x_4158_);
if (v_isSharedCheck_4173_ == 0)
{
v___x_4168_ = v___x_4158_;
v_isShared_4169_ = v_isSharedCheck_4173_;
goto v_resetjp_4167_;
}
else
{
lean_inc(v_a_4166_);
lean_dec(v___x_4158_);
v___x_4168_ = lean_box(0);
v_isShared_4169_ = v_isSharedCheck_4173_;
goto v_resetjp_4167_;
}
v_resetjp_4167_:
{
lean_object* v___x_4171_; 
if (v_isShared_4169_ == 0)
{
v___x_4171_ = v___x_4168_;
goto v_reusejp_4170_;
}
else
{
lean_object* v_reuseFailAlloc_4172_; 
v_reuseFailAlloc_4172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4172_, 0, v_a_4166_);
v___x_4171_ = v_reuseFailAlloc_4172_;
goto v_reusejp_4170_;
}
v_reusejp_4170_:
{
return v___x_4171_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___redArg___boxed(lean_object* v_sz_4174_, lean_object* v_i_4175_, lean_object* v_bs_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_){
_start:
{
size_t v_sz_boxed_4180_; size_t v_i_boxed_4181_; lean_object* v_res_4182_; 
v_sz_boxed_4180_ = lean_unbox_usize(v_sz_4174_);
lean_dec(v_sz_4174_);
v_i_boxed_4181_ = lean_unbox_usize(v_i_4175_);
lean_dec(v_i_4175_);
v_res_4182_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___redArg(v_sz_boxed_4180_, v_i_boxed_4181_, v_bs_4176_, v___y_4177_, v___y_4178_);
lean_dec(v___y_4178_);
lean_dec_ref(v___y_4177_);
return v_res_4182_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___redArg(lean_object* v_as_4183_, size_t v_sz_4184_, size_t v_i_4185_, lean_object* v_b_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_){
_start:
{
uint8_t v___x_4192_; 
v___x_4192_ = lean_usize_dec_lt(v_i_4185_, v_sz_4184_);
if (v___x_4192_ == 0)
{
lean_object* v___x_4193_; 
v___x_4193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4193_, 0, v_b_4186_);
return v___x_4193_;
}
else
{
lean_object* v_array_4194_; lean_object* v_start_4195_; lean_object* v_stop_4196_; uint8_t v___x_4197_; 
v_array_4194_ = lean_ctor_get(v_b_4186_, 0);
v_start_4195_ = lean_ctor_get(v_b_4186_, 1);
v_stop_4196_ = lean_ctor_get(v_b_4186_, 2);
v___x_4197_ = lean_nat_dec_lt(v_start_4195_, v_stop_4196_);
if (v___x_4197_ == 0)
{
lean_object* v___x_4198_; 
v___x_4198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4198_, 0, v_b_4186_);
return v___x_4198_;
}
else
{
lean_object* v___x_4200_; uint8_t v_isShared_4201_; uint8_t v_isSharedCheck_4221_; 
lean_inc(v_stop_4196_);
lean_inc(v_start_4195_);
lean_inc_ref(v_array_4194_);
v_isSharedCheck_4221_ = !lean_is_exclusive(v_b_4186_);
if (v_isSharedCheck_4221_ == 0)
{
lean_object* v_unused_4222_; lean_object* v_unused_4223_; lean_object* v_unused_4224_; 
v_unused_4222_ = lean_ctor_get(v_b_4186_, 2);
lean_dec(v_unused_4222_);
v_unused_4223_ = lean_ctor_get(v_b_4186_, 1);
lean_dec(v_unused_4223_);
v_unused_4224_ = lean_ctor_get(v_b_4186_, 0);
lean_dec(v_unused_4224_);
v___x_4200_ = v_b_4186_;
v_isShared_4201_ = v_isSharedCheck_4221_;
goto v_resetjp_4199_;
}
else
{
lean_dec(v_b_4186_);
v___x_4200_ = lean_box(0);
v_isShared_4201_ = v_isSharedCheck_4221_;
goto v_resetjp_4199_;
}
v_resetjp_4199_:
{
lean_object* v_a_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; 
v_a_4202_ = lean_array_uget_borrowed(v_as_4183_, v_i_4185_);
v___x_4203_ = lean_array_fget_borrowed(v_array_4194_, v_start_4195_);
lean_inc(v_a_4202_);
lean_inc(v___x_4203_);
v___x_4204_ = l_Lean_Elab_Structural_reportTermMeasure(v___x_4203_, v_a_4202_, v___y_4187_, v___y_4188_, v___y_4189_, v___y_4190_);
if (lean_obj_tag(v___x_4204_) == 0)
{
lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4208_; 
lean_dec_ref(v___x_4204_);
v___x_4205_ = lean_unsigned_to_nat(1u);
v___x_4206_ = lean_nat_add(v_start_4195_, v___x_4205_);
lean_dec(v_start_4195_);
if (v_isShared_4201_ == 0)
{
lean_ctor_set(v___x_4200_, 1, v___x_4206_);
v___x_4208_ = v___x_4200_;
goto v_reusejp_4207_;
}
else
{
lean_object* v_reuseFailAlloc_4212_; 
v_reuseFailAlloc_4212_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4212_, 0, v_array_4194_);
lean_ctor_set(v_reuseFailAlloc_4212_, 1, v___x_4206_);
lean_ctor_set(v_reuseFailAlloc_4212_, 2, v_stop_4196_);
v___x_4208_ = v_reuseFailAlloc_4212_;
goto v_reusejp_4207_;
}
v_reusejp_4207_:
{
size_t v___x_4209_; size_t v___x_4210_; 
v___x_4209_ = ((size_t)1ULL);
v___x_4210_ = lean_usize_add(v_i_4185_, v___x_4209_);
v_i_4185_ = v___x_4210_;
v_b_4186_ = v___x_4208_;
goto _start;
}
}
else
{
lean_object* v_a_4213_; lean_object* v___x_4215_; uint8_t v_isShared_4216_; uint8_t v_isSharedCheck_4220_; 
lean_del_object(v___x_4200_);
lean_dec(v_stop_4196_);
lean_dec(v_start_4195_);
lean_dec_ref(v_array_4194_);
v_a_4213_ = lean_ctor_get(v___x_4204_, 0);
v_isSharedCheck_4220_ = !lean_is_exclusive(v___x_4204_);
if (v_isSharedCheck_4220_ == 0)
{
v___x_4215_ = v___x_4204_;
v_isShared_4216_ = v_isSharedCheck_4220_;
goto v_resetjp_4214_;
}
else
{
lean_inc(v_a_4213_);
lean_dec(v___x_4204_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___redArg___boxed(lean_object* v_as_4225_, lean_object* v_sz_4226_, lean_object* v_i_4227_, lean_object* v_b_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_){
_start:
{
size_t v_sz_boxed_4234_; size_t v_i_boxed_4235_; lean_object* v_res_4236_; 
v_sz_boxed_4234_ = lean_unbox_usize(v_sz_4226_);
lean_dec(v_sz_4226_);
v_i_boxed_4235_ = lean_unbox_usize(v_i_4227_);
lean_dec(v_i_4227_);
v_res_4236_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___redArg(v_as_4225_, v_sz_boxed_4234_, v_i_boxed_4235_, v_b_4228_, v___y_4229_, v___y_4230_, v___y_4231_, v___y_4232_);
lean_dec(v___y_4232_);
lean_dec_ref(v___y_4231_);
lean_dec(v___y_4230_);
lean_dec_ref(v___y_4229_);
lean_dec_ref(v_as_4225_);
return v_res_4236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_structuralRecursion(lean_object* v_docCtx_4237_, lean_object* v_preDefs_4238_, lean_object* v_termMeasure_x3fs_4239_, lean_object* v_a_4240_, lean_object* v_a_4241_, lean_object* v_a_4242_, lean_object* v_a_4243_, lean_object* v_a_4244_, lean_object* v_a_4245_){
_start:
{
size_t v_sz_4247_; size_t v___x_4248_; lean_object* v_names_4249_; lean_object* v___x_4250_; 
v_sz_4247_ = lean_array_size(v_preDefs_4238_);
v___x_4248_ = ((size_t)0ULL);
lean_inc_ref_n(v_preDefs_4238_, 2);
v_names_4249_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0(v_sz_4247_, v___x_4248_, v_preDefs_4238_);
v___x_4250_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos(v_preDefs_4238_, v_termMeasure_x3fs_4239_, v_a_4242_, v_a_4243_, v_a_4244_, v_a_4245_);
if (lean_obj_tag(v___x_4250_) == 0)
{
lean_object* v_a_4251_; lean_object* v_snd_4252_; lean_object* v_fst_4253_; lean_object* v_fst_4254_; lean_object* v_snd_4255_; lean_object* v___y_4286_; lean_object* v___x_4287_; lean_object* v___x_4288_; lean_object* v___x_4289_; size_t v_sz_4290_; lean_object* v___x_4291_; 
v_a_4251_ = lean_ctor_get(v___x_4250_, 0);
lean_inc(v_a_4251_);
lean_dec_ref(v___x_4250_);
v_snd_4252_ = lean_ctor_get(v_a_4251_, 1);
lean_inc(v_snd_4252_);
v_fst_4253_ = lean_ctor_get(v_a_4251_, 0);
lean_inc(v_fst_4253_);
lean_dec(v_a_4251_);
v_fst_4254_ = lean_ctor_get(v_snd_4252_, 0);
lean_inc(v_fst_4254_);
v_snd_4255_ = lean_ctor_get(v_snd_4252_, 1);
lean_inc(v_snd_4255_);
lean_dec(v_snd_4252_);
v___x_4287_ = lean_unsigned_to_nat(0u);
v___x_4288_ = lean_array_get_size(v_preDefs_4238_);
lean_inc_ref(v_preDefs_4238_);
v___x_4289_ = l_Array_toSubarray___redArg(v_preDefs_4238_, v___x_4287_, v___x_4288_);
v_sz_4290_ = lean_array_size(v_fst_4253_);
v___x_4291_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___redArg(v_fst_4253_, v_sz_4290_, v___x_4248_, v___x_4289_, v_a_4242_, v_a_4243_, v_a_4244_, v_a_4245_);
if (lean_obj_tag(v___x_4291_) == 0)
{
lean_object* v___x_4292_; uint8_t v___x_4293_; 
lean_dec_ref(v___x_4291_);
v___x_4292_ = lean_array_get_size(v_fst_4254_);
v___x_4293_ = lean_nat_dec_lt(v___x_4287_, v___x_4292_);
if (v___x_4293_ == 0)
{
lean_dec_ref(v_names_4249_);
goto v___jp_4256_;
}
else
{
lean_object* v___x_4294_; uint8_t v___x_4295_; 
v___x_4294_ = lean_box(0);
v___x_4295_ = lean_nat_dec_le(v___x_4292_, v___x_4292_);
if (v___x_4295_ == 0)
{
if (v___x_4293_ == 0)
{
lean_dec_ref(v_names_4249_);
goto v___jp_4256_;
}
else
{
size_t v___x_4296_; lean_object* v___x_4297_; 
v___x_4296_ = lean_usize_of_nat(v___x_4292_);
lean_inc_ref(v_docCtx_4237_);
v___x_4297_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4(v_names_4249_, v_docCtx_4237_, v_fst_4254_, v___x_4248_, v___x_4296_, v___x_4294_, v_a_4240_, v_a_4241_, v_a_4242_, v_a_4243_, v_a_4244_, v_a_4245_);
v___y_4286_ = v___x_4297_;
goto v___jp_4285_;
}
}
else
{
size_t v___x_4298_; lean_object* v___x_4299_; 
v___x_4298_ = lean_usize_of_nat(v___x_4292_);
lean_inc_ref(v_docCtx_4237_);
v___x_4299_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4(v_names_4249_, v_docCtx_4237_, v_fst_4254_, v___x_4248_, v___x_4298_, v___x_4294_, v_a_4240_, v_a_4241_, v_a_4242_, v_a_4243_, v_a_4244_, v_a_4245_);
v___y_4286_ = v___x_4299_;
goto v___jp_4285_;
}
}
}
else
{
lean_object* v_a_4300_; lean_object* v___x_4302_; uint8_t v_isShared_4303_; uint8_t v_isSharedCheck_4307_; 
lean_dec(v_snd_4255_);
lean_dec(v_fst_4254_);
lean_dec(v_fst_4253_);
lean_dec_ref(v_names_4249_);
lean_dec_ref(v_preDefs_4238_);
lean_dec_ref(v_docCtx_4237_);
v_a_4300_ = lean_ctor_get(v___x_4291_, 0);
v_isSharedCheck_4307_ = !lean_is_exclusive(v___x_4291_);
if (v_isSharedCheck_4307_ == 0)
{
v___x_4302_ = v___x_4291_;
v_isShared_4303_ = v_isSharedCheck_4307_;
goto v_resetjp_4301_;
}
else
{
lean_inc(v_a_4300_);
lean_dec(v___x_4291_);
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
v___jp_4256_:
{
lean_object* v___x_4257_; 
v___x_4257_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___redArg(v_sz_4247_, v___x_4248_, v_preDefs_4238_, v_a_4244_, v_a_4245_);
if (lean_obj_tag(v___x_4257_) == 0)
{
lean_object* v_a_4258_; lean_object* v___x_4259_; 
v_a_4258_ = lean_ctor_get(v___x_4257_, 0);
lean_inc_n(v_a_4258_, 2);
lean_dec_ref(v___x_4257_);
lean_inc_ref(v_docCtx_4237_);
v___x_4259_ = l_Lean_Elab_addAndCompilePartialRec(v_docCtx_4237_, v_a_4258_, v_a_4240_, v_a_4241_, v_a_4242_, v_a_4243_, v_a_4244_, v_a_4245_);
if (lean_obj_tag(v___x_4259_) == 0)
{
lean_object* v___x_4260_; lean_object* v___x_4261_; lean_object* v___x_4262_; size_t v_sz_4263_; lean_object* v___x_4264_; 
lean_dec_ref(v___x_4259_);
v___x_4260_ = lean_unsigned_to_nat(0u);
v___x_4261_ = lean_array_get_size(v_fst_4253_);
v___x_4262_ = l_Array_toSubarray___redArg(v_fst_4253_, v___x_4260_, v___x_4261_);
v_sz_4263_ = lean_array_size(v_a_4258_);
lean_inc(v_a_4258_);
v___x_4264_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__1(v_docCtx_4237_, v_a_4258_, v_snd_4255_, v_a_4258_, v_sz_4263_, v___x_4248_, v___x_4262_, v_a_4240_, v_a_4241_, v_a_4242_, v_a_4243_, v_a_4244_, v_a_4245_);
if (lean_obj_tag(v___x_4264_) == 0)
{
lean_object* v___x_4265_; lean_object* v___x_4266_; 
lean_dec_ref(v___x_4264_);
v___x_4265_ = lean_box(0);
v___x_4266_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___redArg(v_a_4258_, v_sz_4263_, v___x_4248_, v___x_4265_, v_a_4242_, v_a_4243_, v_a_4244_, v_a_4245_);
lean_dec(v_a_4258_);
if (lean_obj_tag(v___x_4266_) == 0)
{
uint8_t v___x_4267_; lean_object* v___x_4268_; 
lean_dec_ref(v___x_4266_);
v___x_4267_ = 1;
v___x_4268_ = l_Lean_Elab_applyAttributesOf(v_fst_4254_, v___x_4267_, v_a_4240_, v_a_4241_, v_a_4242_, v_a_4243_, v_a_4244_, v_a_4245_);
lean_dec(v_fst_4254_);
return v___x_4268_;
}
else
{
lean_dec(v_fst_4254_);
return v___x_4266_;
}
}
else
{
lean_object* v_a_4269_; lean_object* v___x_4271_; uint8_t v_isShared_4272_; uint8_t v_isSharedCheck_4276_; 
lean_dec(v_a_4258_);
lean_dec(v_fst_4254_);
v_a_4269_ = lean_ctor_get(v___x_4264_, 0);
v_isSharedCheck_4276_ = !lean_is_exclusive(v___x_4264_);
if (v_isSharedCheck_4276_ == 0)
{
v___x_4271_ = v___x_4264_;
v_isShared_4272_ = v_isSharedCheck_4276_;
goto v_resetjp_4270_;
}
else
{
lean_inc(v_a_4269_);
lean_dec(v___x_4264_);
v___x_4271_ = lean_box(0);
v_isShared_4272_ = v_isSharedCheck_4276_;
goto v_resetjp_4270_;
}
v_resetjp_4270_:
{
lean_object* v___x_4274_; 
if (v_isShared_4272_ == 0)
{
v___x_4274_ = v___x_4271_;
goto v_reusejp_4273_;
}
else
{
lean_object* v_reuseFailAlloc_4275_; 
v_reuseFailAlloc_4275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4275_, 0, v_a_4269_);
v___x_4274_ = v_reuseFailAlloc_4275_;
goto v_reusejp_4273_;
}
v_reusejp_4273_:
{
return v___x_4274_;
}
}
}
}
else
{
lean_dec(v_a_4258_);
lean_dec(v_snd_4255_);
lean_dec(v_fst_4254_);
lean_dec(v_fst_4253_);
lean_dec_ref(v_docCtx_4237_);
return v___x_4259_;
}
}
else
{
lean_object* v_a_4277_; lean_object* v___x_4279_; uint8_t v_isShared_4280_; uint8_t v_isSharedCheck_4284_; 
lean_dec(v_snd_4255_);
lean_dec(v_fst_4254_);
lean_dec(v_fst_4253_);
lean_dec_ref(v_docCtx_4237_);
v_a_4277_ = lean_ctor_get(v___x_4257_, 0);
v_isSharedCheck_4284_ = !lean_is_exclusive(v___x_4257_);
if (v_isSharedCheck_4284_ == 0)
{
v___x_4279_ = v___x_4257_;
v_isShared_4280_ = v_isSharedCheck_4284_;
goto v_resetjp_4278_;
}
else
{
lean_inc(v_a_4277_);
lean_dec(v___x_4257_);
v___x_4279_ = lean_box(0);
v_isShared_4280_ = v_isSharedCheck_4284_;
goto v_resetjp_4278_;
}
v_resetjp_4278_:
{
lean_object* v___x_4282_; 
if (v_isShared_4280_ == 0)
{
v___x_4282_ = v___x_4279_;
goto v_reusejp_4281_;
}
else
{
lean_object* v_reuseFailAlloc_4283_; 
v_reuseFailAlloc_4283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4283_, 0, v_a_4277_);
v___x_4282_ = v_reuseFailAlloc_4283_;
goto v_reusejp_4281_;
}
v_reusejp_4281_:
{
return v___x_4282_;
}
}
}
}
v___jp_4285_:
{
if (lean_obj_tag(v___y_4286_) == 0)
{
lean_dec_ref(v___y_4286_);
goto v___jp_4256_;
}
else
{
lean_dec(v_snd_4255_);
lean_dec(v_fst_4254_);
lean_dec(v_fst_4253_);
lean_dec_ref(v_preDefs_4238_);
lean_dec_ref(v_docCtx_4237_);
return v___y_4286_;
}
}
}
else
{
lean_object* v_a_4308_; lean_object* v___x_4310_; uint8_t v_isShared_4311_; uint8_t v_isSharedCheck_4315_; 
lean_dec_ref(v_names_4249_);
lean_dec_ref(v_preDefs_4238_);
lean_dec_ref(v_docCtx_4237_);
v_a_4308_ = lean_ctor_get(v___x_4250_, 0);
v_isSharedCheck_4315_ = !lean_is_exclusive(v___x_4250_);
if (v_isSharedCheck_4315_ == 0)
{
v___x_4310_ = v___x_4250_;
v_isShared_4311_ = v_isSharedCheck_4315_;
goto v_resetjp_4309_;
}
else
{
lean_inc(v_a_4308_);
lean_dec(v___x_4250_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_structuralRecursion___boxed(lean_object* v_docCtx_4316_, lean_object* v_preDefs_4317_, lean_object* v_termMeasure_x3fs_4318_, lean_object* v_a_4319_, lean_object* v_a_4320_, lean_object* v_a_4321_, lean_object* v_a_4322_, lean_object* v_a_4323_, lean_object* v_a_4324_, lean_object* v_a_4325_){
_start:
{
lean_object* v_res_4326_; 
v_res_4326_ = l_Lean_Elab_Structural_structuralRecursion(v_docCtx_4316_, v_preDefs_4317_, v_termMeasure_x3fs_4318_, v_a_4319_, v_a_4320_, v_a_4321_, v_a_4322_, v_a_4323_, v_a_4324_);
lean_dec(v_a_4324_);
lean_dec_ref(v_a_4323_);
lean_dec(v_a_4322_);
lean_dec_ref(v_a_4321_);
lean_dec(v_a_4320_);
lean_dec_ref(v_a_4319_);
return v_res_4326_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0(size_t v_sz_4327_, size_t v_i_4328_, lean_object* v_bs_4329_, lean_object* v___y_4330_, lean_object* v___y_4331_, lean_object* v___y_4332_, lean_object* v___y_4333_, lean_object* v___y_4334_, lean_object* v___y_4335_){
_start:
{
lean_object* v___x_4337_; 
v___x_4337_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___redArg(v_sz_4327_, v_i_4328_, v_bs_4329_, v___y_4334_, v___y_4335_);
return v___x_4337_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___boxed(lean_object* v_sz_4338_, lean_object* v_i_4339_, lean_object* v_bs_4340_, lean_object* v___y_4341_, lean_object* v___y_4342_, lean_object* v___y_4343_, lean_object* v___y_4344_, lean_object* v___y_4345_, lean_object* v___y_4346_, lean_object* v___y_4347_){
_start:
{
size_t v_sz_boxed_4348_; size_t v_i_boxed_4349_; lean_object* v_res_4350_; 
v_sz_boxed_4348_ = lean_unbox_usize(v_sz_4338_);
lean_dec(v_sz_4338_);
v_i_boxed_4349_ = lean_unbox_usize(v_i_4339_);
lean_dec(v_i_4339_);
v_res_4350_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0(v_sz_boxed_4348_, v_i_boxed_4349_, v_bs_4340_, v___y_4341_, v___y_4342_, v___y_4343_, v___y_4344_, v___y_4345_, v___y_4346_);
lean_dec(v___y_4346_);
lean_dec_ref(v___y_4345_);
lean_dec(v___y_4344_);
lean_dec_ref(v___y_4343_);
lean_dec(v___y_4342_);
lean_dec_ref(v___y_4341_);
return v_res_4350_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2(lean_object* v_as_4351_, size_t v_sz_4352_, size_t v_i_4353_, lean_object* v_b_4354_, lean_object* v___y_4355_, lean_object* v___y_4356_, lean_object* v___y_4357_, lean_object* v___y_4358_, lean_object* v___y_4359_, lean_object* v___y_4360_){
_start:
{
lean_object* v___x_4362_; 
v___x_4362_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___redArg(v_as_4351_, v_sz_4352_, v_i_4353_, v_b_4354_, v___y_4357_, v___y_4358_, v___y_4359_, v___y_4360_);
return v___x_4362_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___boxed(lean_object* v_as_4363_, lean_object* v_sz_4364_, lean_object* v_i_4365_, lean_object* v_b_4366_, lean_object* v___y_4367_, lean_object* v___y_4368_, lean_object* v___y_4369_, lean_object* v___y_4370_, lean_object* v___y_4371_, lean_object* v___y_4372_, lean_object* v___y_4373_){
_start:
{
size_t v_sz_boxed_4374_; size_t v_i_boxed_4375_; lean_object* v_res_4376_; 
v_sz_boxed_4374_ = lean_unbox_usize(v_sz_4364_);
lean_dec(v_sz_4364_);
v_i_boxed_4375_ = lean_unbox_usize(v_i_4365_);
lean_dec(v_i_4365_);
v_res_4376_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2(v_as_4363_, v_sz_boxed_4374_, v_i_boxed_4375_, v_b_4366_, v___y_4367_, v___y_4368_, v___y_4369_, v___y_4370_, v___y_4371_, v___y_4372_);
lean_dec(v___y_4372_);
lean_dec_ref(v___y_4371_);
lean_dec(v___y_4370_);
lean_dec_ref(v___y_4369_);
lean_dec(v___y_4368_);
lean_dec_ref(v___y_4367_);
lean_dec_ref(v_as_4363_);
return v_res_4376_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3(lean_object* v_as_4377_, size_t v_sz_4378_, size_t v_i_4379_, lean_object* v_b_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_, lean_object* v___y_4383_, lean_object* v___y_4384_, lean_object* v___y_4385_, lean_object* v___y_4386_){
_start:
{
lean_object* v___x_4388_; 
v___x_4388_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___redArg(v_as_4377_, v_sz_4378_, v_i_4379_, v_b_4380_, v___y_4383_, v___y_4384_, v___y_4385_, v___y_4386_);
return v___x_4388_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___boxed(lean_object* v_as_4389_, lean_object* v_sz_4390_, lean_object* v_i_4391_, lean_object* v_b_4392_, lean_object* v___y_4393_, lean_object* v___y_4394_, lean_object* v___y_4395_, lean_object* v___y_4396_, lean_object* v___y_4397_, lean_object* v___y_4398_, lean_object* v___y_4399_){
_start:
{
size_t v_sz_boxed_4400_; size_t v_i_boxed_4401_; lean_object* v_res_4402_; 
v_sz_boxed_4400_ = lean_unbox_usize(v_sz_4390_);
lean_dec(v_sz_4390_);
v_i_boxed_4401_ = lean_unbox_usize(v_i_4391_);
lean_dec(v_i_4391_);
v_res_4402_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3(v_as_4389_, v_sz_boxed_4400_, v_i_boxed_4401_, v_b_4392_, v___y_4393_, v___y_4394_, v___y_4395_, v___y_4396_, v___y_4397_, v___y_4398_);
lean_dec(v___y_4398_);
lean_dec_ref(v___y_4397_);
lean_dec(v___y_4396_);
lean_dec_ref(v___y_4395_);
lean_dec(v___y_4394_);
lean_dec_ref(v___y_4393_);
lean_dec_ref(v_as_4389_);
return v_res_4402_;
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
