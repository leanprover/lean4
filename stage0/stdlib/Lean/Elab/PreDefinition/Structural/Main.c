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
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
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
lean_object* lean_mk_array(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__15(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__3;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__3___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__24___redArg(lean_object* v_as_166_, size_t v_i_167_, size_t v_stop_168_, lean_object* v_b_169_, lean_object* v___y_170_, lean_object* v___y_171_){
_start:
{
uint8_t v___x_173_; 
v___x_173_ = lean_usize_dec_eq(v_i_167_, v_stop_168_);
if (v___x_173_ == 0)
{
lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_174_ = lean_array_uget_borrowed(v_as_166_, v_i_167_);
v___x_175_ = l_Lean_Elab_addAsAxiom___redArg(v___x_174_, v___y_170_, v___y_171_);
if (lean_obj_tag(v___x_175_) == 0)
{
lean_object* v_a_176_; size_t v___x_177_; size_t v___x_178_; 
v_a_176_ = lean_ctor_get(v___x_175_, 0);
lean_inc(v_a_176_);
lean_dec_ref_known(v___x_175_, 1);
v___x_177_ = ((size_t)1ULL);
v___x_178_ = lean_usize_add(v_i_167_, v___x_177_);
v_i_167_ = v___x_178_;
v_b_169_ = v_a_176_;
goto _start;
}
else
{
return v___x_175_;
}
}
else
{
lean_object* v___x_180_; 
v___x_180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_180_, 0, v_b_169_);
return v___x_180_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__24___redArg___boxed(lean_object* v_as_181_, lean_object* v_i_182_, lean_object* v_stop_183_, lean_object* v_b_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_){
_start:
{
size_t v_i_boxed_188_; size_t v_stop_boxed_189_; lean_object* v_res_190_; 
v_i_boxed_188_ = lean_unbox_usize(v_i_182_);
lean_dec(v_i_182_);
v_stop_boxed_189_ = lean_unbox_usize(v_stop_183_);
lean_dec(v_stop_183_);
v_res_190_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__24___redArg(v_as_181_, v_i_boxed_188_, v_stop_boxed_189_, v_b_184_, v___y_185_, v___y_186_);
lean_dec(v___y_186_);
lean_dec_ref(v___y_185_);
lean_dec_ref(v_as_181_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__24(lean_object* v_as_191_, size_t v_i_192_, size_t v_stop_193_, lean_object* v_b_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__24___redArg(v_as_191_, v_i_192_, v_stop_193_, v_b_194_, v___y_197_, v___y_198_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__24___boxed(lean_object* v_as_201_, lean_object* v_i_202_, lean_object* v_stop_203_, lean_object* v_b_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_){
_start:
{
size_t v_i_boxed_210_; size_t v_stop_boxed_211_; lean_object* v_res_212_; 
v_i_boxed_210_ = lean_unbox_usize(v_i_202_);
lean_dec(v_i_202_);
v_stop_boxed_211_ = lean_unbox_usize(v_stop_203_);
lean_dec(v_stop_203_);
v_res_212_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__24(v_as_201_, v_i_boxed_210_, v_stop_boxed_211_, v_b_204_, v___y_205_, v___y_206_, v___y_207_, v___y_208_);
lean_dec(v___y_208_);
lean_dec_ref(v___y_207_);
lean_dec(v___y_206_);
lean_dec_ref(v___y_205_);
lean_dec_ref(v_as_201_);
return v_res_212_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__0(void){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_213_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__1(void){
_start:
{
lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_214_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__0, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__0);
v___x_215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_215_, 0, v___x_214_);
return v___x_215_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__2(void){
_start:
{
lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_216_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__1, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__1);
v___x_217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_217_, 0, v___x_216_);
lean_ctor_set(v___x_217_, 1, v___x_216_);
return v___x_217_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__3(void){
_start:
{
lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_218_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__1, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__1);
v___x_219_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_219_, 0, v___x_218_);
lean_ctor_set(v___x_219_, 1, v___x_218_);
lean_ctor_set(v___x_219_, 2, v___x_218_);
lean_ctor_set(v___x_219_, 3, v___x_218_);
lean_ctor_set(v___x_219_, 4, v___x_218_);
lean_ctor_set(v___x_219_, 5, v___x_218_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg(lean_object* v_env_220_, lean_object* v___y_221_, lean_object* v___y_222_){
_start:
{
lean_object* v___x_224_; lean_object* v_nextMacroScope_225_; lean_object* v_ngen_226_; lean_object* v_auxDeclNGen_227_; lean_object* v_traceState_228_; lean_object* v_messages_229_; lean_object* v_infoState_230_; lean_object* v_snapshotTasks_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_257_; 
v___x_224_ = lean_st_ref_take(v___y_222_);
v_nextMacroScope_225_ = lean_ctor_get(v___x_224_, 1);
v_ngen_226_ = lean_ctor_get(v___x_224_, 2);
v_auxDeclNGen_227_ = lean_ctor_get(v___x_224_, 3);
v_traceState_228_ = lean_ctor_get(v___x_224_, 4);
v_messages_229_ = lean_ctor_get(v___x_224_, 6);
v_infoState_230_ = lean_ctor_get(v___x_224_, 7);
v_snapshotTasks_231_ = lean_ctor_get(v___x_224_, 8);
v_isSharedCheck_257_ = !lean_is_exclusive(v___x_224_);
if (v_isSharedCheck_257_ == 0)
{
lean_object* v_unused_258_; lean_object* v_unused_259_; 
v_unused_258_ = lean_ctor_get(v___x_224_, 5);
lean_dec(v_unused_258_);
v_unused_259_ = lean_ctor_get(v___x_224_, 0);
lean_dec(v_unused_259_);
v___x_233_ = v___x_224_;
v_isShared_234_ = v_isSharedCheck_257_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_snapshotTasks_231_);
lean_inc(v_infoState_230_);
lean_inc(v_messages_229_);
lean_inc(v_traceState_228_);
lean_inc(v_auxDeclNGen_227_);
lean_inc(v_ngen_226_);
lean_inc(v_nextMacroScope_225_);
lean_dec(v___x_224_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_257_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
lean_object* v___x_235_; lean_object* v___x_237_; 
v___x_235_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__2);
if (v_isShared_234_ == 0)
{
lean_ctor_set(v___x_233_, 5, v___x_235_);
lean_ctor_set(v___x_233_, 0, v_env_220_);
v___x_237_ = v___x_233_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v_env_220_);
lean_ctor_set(v_reuseFailAlloc_256_, 1, v_nextMacroScope_225_);
lean_ctor_set(v_reuseFailAlloc_256_, 2, v_ngen_226_);
lean_ctor_set(v_reuseFailAlloc_256_, 3, v_auxDeclNGen_227_);
lean_ctor_set(v_reuseFailAlloc_256_, 4, v_traceState_228_);
lean_ctor_set(v_reuseFailAlloc_256_, 5, v___x_235_);
lean_ctor_set(v_reuseFailAlloc_256_, 6, v_messages_229_);
lean_ctor_set(v_reuseFailAlloc_256_, 7, v_infoState_230_);
lean_ctor_set(v_reuseFailAlloc_256_, 8, v_snapshotTasks_231_);
v___x_237_ = v_reuseFailAlloc_256_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v_mctx_240_; lean_object* v_zetaDeltaFVarIds_241_; lean_object* v_postponed_242_; lean_object* v_diag_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_254_; 
v___x_238_ = lean_st_ref_put(v___y_222_, v___x_237_);
v___x_239_ = lean_st_ref_take(v___y_221_);
v_mctx_240_ = lean_ctor_get(v___x_239_, 0);
v_zetaDeltaFVarIds_241_ = lean_ctor_get(v___x_239_, 2);
v_postponed_242_ = lean_ctor_get(v___x_239_, 3);
v_diag_243_ = lean_ctor_get(v___x_239_, 4);
v_isSharedCheck_254_ = !lean_is_exclusive(v___x_239_);
if (v_isSharedCheck_254_ == 0)
{
lean_object* v_unused_255_; 
v_unused_255_ = lean_ctor_get(v___x_239_, 1);
lean_dec(v_unused_255_);
v___x_245_ = v___x_239_;
v_isShared_246_ = v_isSharedCheck_254_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_diag_243_);
lean_inc(v_postponed_242_);
lean_inc(v_zetaDeltaFVarIds_241_);
lean_inc(v_mctx_240_);
lean_dec(v___x_239_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_254_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v___x_247_; lean_object* v___x_249_; 
v___x_247_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__3, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__3);
if (v_isShared_246_ == 0)
{
lean_ctor_set(v___x_245_, 1, v___x_247_);
v___x_249_ = v___x_245_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v_mctx_240_);
lean_ctor_set(v_reuseFailAlloc_253_, 1, v___x_247_);
lean_ctor_set(v_reuseFailAlloc_253_, 2, v_zetaDeltaFVarIds_241_);
lean_ctor_set(v_reuseFailAlloc_253_, 3, v_postponed_242_);
lean_ctor_set(v_reuseFailAlloc_253_, 4, v_diag_243_);
v___x_249_ = v_reuseFailAlloc_253_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_250_ = lean_st_ref_put(v___y_221_, v___x_249_);
v___x_251_ = lean_box(0);
v___x_252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_252_, 0, v___x_251_);
return v___x_252_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___boxed(lean_object* v_env_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg(v_env_260_, v___y_261_, v___y_262_);
lean_dec(v___y_262_);
lean_dec(v___y_261_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23___redArg(lean_object* v_env_265_, lean_object* v_x_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_){
_start:
{
lean_object* v___x_272_; lean_object* v_env_273_; lean_object* v_a_275_; lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_272_ = lean_st_ref_get(v___y_270_);
v_env_273_ = lean_ctor_get(v___x_272_, 0);
lean_inc_ref(v_env_273_);
lean_dec(v___x_272_);
v___x_285_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg(v_env_265_, v___y_268_, v___y_270_);
lean_dec_ref(v___x_285_);
lean_inc(v___y_270_);
lean_inc_ref(v___y_269_);
lean_inc(v___y_268_);
lean_inc_ref(v___y_267_);
v___x_286_ = lean_apply_5(v_x_266_, v___y_267_, v___y_268_, v___y_269_, v___y_270_, lean_box(0));
if (lean_obj_tag(v___x_286_) == 0)
{
lean_object* v_a_287_; lean_object* v___x_288_; lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_295_; 
v_a_287_ = lean_ctor_get(v___x_286_, 0);
lean_inc(v_a_287_);
lean_dec_ref_known(v___x_286_, 1);
v___x_288_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg(v_env_273_, v___y_268_, v___y_270_);
v_isSharedCheck_295_ = !lean_is_exclusive(v___x_288_);
if (v_isSharedCheck_295_ == 0)
{
lean_object* v_unused_296_; 
v_unused_296_ = lean_ctor_get(v___x_288_, 0);
lean_dec(v_unused_296_);
v___x_290_ = v___x_288_;
v_isShared_291_ = v_isSharedCheck_295_;
goto v_resetjp_289_;
}
else
{
lean_dec(v___x_288_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_295_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
lean_object* v___x_293_; 
if (v_isShared_291_ == 0)
{
lean_ctor_set(v___x_290_, 0, v_a_287_);
v___x_293_ = v___x_290_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v_a_287_);
v___x_293_ = v_reuseFailAlloc_294_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
return v___x_293_;
}
}
}
else
{
lean_object* v_a_297_; 
v_a_297_ = lean_ctor_get(v___x_286_, 0);
lean_inc(v_a_297_);
lean_dec_ref_known(v___x_286_, 1);
v_a_275_ = v_a_297_;
goto v___jp_274_;
}
v___jp_274_:
{
lean_object* v___x_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_283_; 
v___x_276_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg(v_env_273_, v___y_268_, v___y_270_);
v_isSharedCheck_283_ = !lean_is_exclusive(v___x_276_);
if (v_isSharedCheck_283_ == 0)
{
lean_object* v_unused_284_; 
v_unused_284_ = lean_ctor_get(v___x_276_, 0);
lean_dec(v_unused_284_);
v___x_278_ = v___x_276_;
v_isShared_279_ = v_isSharedCheck_283_;
goto v_resetjp_277_;
}
else
{
lean_dec(v___x_276_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_283_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v___x_281_; 
if (v_isShared_279_ == 0)
{
lean_ctor_set_tag(v___x_278_, 1);
lean_ctor_set(v___x_278_, 0, v_a_275_);
v___x_281_ = v___x_278_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v_a_275_);
v___x_281_ = v_reuseFailAlloc_282_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
return v___x_281_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23___redArg___boxed(lean_object* v_env_298_, lean_object* v_x_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23___redArg(v_env_298_, v_x_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_);
lean_dec(v___y_303_);
lean_dec_ref(v___y_302_);
lean_dec(v___y_301_);
lean_dec_ref(v___y_300_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___lam__1(lean_object* v___x_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_){
_start:
{
lean_object* v___x_312_; 
v___x_312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_312_, 0, v___x_306_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___lam__1___boxed(lean_object* v___x_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___lam__1(v___x_313_, v___y_314_, v___y_315_, v___y_316_, v___y_317_);
lean_dec(v___y_317_);
lean_dec_ref(v___y_316_);
lean_dec(v___y_315_);
lean_dec_ref(v___y_314_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___lam__0(lean_object* v___y_320_, lean_object* v_k_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_){
_start:
{
lean_object* v___x_327_; 
lean_inc(v___y_325_);
lean_inc_ref(v___y_324_);
lean_inc(v___y_323_);
lean_inc_ref(v___y_322_);
v___x_327_ = lean_apply_5(v___y_320_, v___y_322_, v___y_323_, v___y_324_, v___y_325_, lean_box(0));
if (lean_obj_tag(v___x_327_) == 0)
{
lean_object* v___x_328_; 
lean_dec_ref_known(v___x_327_, 1);
v___x_328_ = lean_apply_5(v_k_321_, v___y_322_, v___y_323_, v___y_324_, v___y_325_, lean_box(0));
return v___x_328_;
}
else
{
lean_object* v_a_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_336_; 
lean_dec(v___y_325_);
lean_dec_ref(v___y_324_);
lean_dec(v___y_323_);
lean_dec_ref(v___y_322_);
lean_dec_ref(v_k_321_);
v_a_329_ = lean_ctor_get(v___x_327_, 0);
v_isSharedCheck_336_ = !lean_is_exclusive(v___x_327_);
if (v_isSharedCheck_336_ == 0)
{
v___x_331_ = v___x_327_;
v_isShared_332_ = v_isSharedCheck_336_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_a_329_);
lean_dec(v___x_327_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_336_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
lean_object* v___x_334_; 
if (v_isShared_332_ == 0)
{
v___x_334_ = v___x_331_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v_a_329_);
v___x_334_ = v_reuseFailAlloc_335_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
return v___x_334_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___lam__0___boxed(lean_object* v___y_337_, lean_object* v_k_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___lam__0(v___y_337_, v_k_338_, v___y_339_, v___y_340_, v___y_341_, v___y_342_);
return v_res_344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(lean_object* v_preDefs_349_, lean_object* v_k_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_){
_start:
{
lean_object* v___y_357_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; uint8_t v___x_366_; 
v___x_363_ = lean_unsigned_to_nat(0u);
v___x_364_ = lean_array_get_size(v_preDefs_349_);
v___x_365_ = lean_box(0);
v___x_366_ = lean_nat_dec_lt(v___x_363_, v___x_364_);
if (v___x_366_ == 0)
{
lean_object* v___f_367_; 
lean_dec_ref(v_preDefs_349_);
v___f_367_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___closed__0));
v___y_357_ = v___f_367_;
goto v___jp_356_;
}
else
{
uint8_t v___x_368_; 
v___x_368_ = lean_nat_dec_le(v___x_364_, v___x_364_);
if (v___x_368_ == 0)
{
if (v___x_366_ == 0)
{
lean_object* v___f_369_; 
lean_dec_ref(v_preDefs_349_);
v___f_369_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___closed__0));
v___y_357_ = v___f_369_;
goto v___jp_356_;
}
else
{
size_t v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_370_ = lean_usize_of_nat(v___x_364_);
v___x_371_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___boxed__const__1));
v___x_372_ = lean_box_usize(v___x_370_);
v___x_373_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__24___boxed), 9, 4);
lean_closure_set(v___x_373_, 0, v_preDefs_349_);
lean_closure_set(v___x_373_, 1, v___x_371_);
lean_closure_set(v___x_373_, 2, v___x_372_);
lean_closure_set(v___x_373_, 3, v___x_365_);
v___y_357_ = v___x_373_;
goto v___jp_356_;
}
}
else
{
size_t v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_374_ = lean_usize_of_nat(v___x_364_);
v___x_375_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___boxed__const__1));
v___x_376_ = lean_box_usize(v___x_374_);
v___x_377_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__24___boxed), 9, 4);
lean_closure_set(v___x_377_, 0, v_preDefs_349_);
lean_closure_set(v___x_377_, 1, v___x_375_);
lean_closure_set(v___x_377_, 2, v___x_376_);
lean_closure_set(v___x_377_, 3, v___x_365_);
v___y_357_ = v___x_377_;
goto v___jp_356_;
}
}
v___jp_356_:
{
lean_object* v___x_358_; lean_object* v_env_359_; lean_object* v___f_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_358_ = lean_st_ref_get(v___y_354_);
v_env_359_ = lean_ctor_get(v___x_358_, 0);
lean_inc_ref(v_env_359_);
lean_dec(v___x_358_);
v___f_360_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_360_, 0, v___y_357_);
lean_closure_set(v___f_360_, 1, v_k_350_);
v___x_361_ = l_Lean_Environment_unlockAsync(v_env_359_);
v___x_362_ = l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23___redArg(v___x_361_, v___f_360_, v___y_351_, v___y_352_, v___y_353_, v___y_354_);
return v___x_362_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___boxed(lean_object* v_preDefs_378_, lean_object* v_k_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v_preDefs_378_, v_k_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_);
lean_dec(v___y_383_);
lean_dec_ref(v___y_382_);
lean_dec(v___y_381_);
lean_dec_ref(v___y_380_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13(lean_object* v_as_386_, size_t v_i_387_, size_t v_stop_388_, lean_object* v_b_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_){
_start:
{
uint8_t v___x_395_; 
v___x_395_ = lean_usize_dec_eq(v_i_387_, v_stop_388_);
if (v___x_395_ == 0)
{
lean_object* v___x_21530__overap_396_; lean_object* v___x_397_; 
v___x_21530__overap_396_ = lean_array_uget_borrowed(v_as_386_, v_i_387_);
lean_inc(v___x_21530__overap_396_);
lean_inc(v___y_393_);
lean_inc_ref(v___y_392_);
lean_inc(v___y_391_);
lean_inc_ref(v___y_390_);
v___x_397_ = lean_apply_5(v___x_21530__overap_396_, v___y_390_, v___y_391_, v___y_392_, v___y_393_, lean_box(0));
if (lean_obj_tag(v___x_397_) == 0)
{
lean_object* v_a_398_; size_t v___x_399_; size_t v___x_400_; 
v_a_398_ = lean_ctor_get(v___x_397_, 0);
lean_inc(v_a_398_);
lean_dec_ref_known(v___x_397_, 1);
v___x_399_ = ((size_t)1ULL);
v___x_400_ = lean_usize_add(v_i_387_, v___x_399_);
v_i_387_ = v___x_400_;
v_b_389_ = v_a_398_;
goto _start;
}
else
{
return v___x_397_;
}
}
else
{
lean_object* v___x_402_; 
v___x_402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_402_, 0, v_b_389_);
return v___x_402_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13___boxed(lean_object* v_as_403_, lean_object* v_i_404_, lean_object* v_stop_405_, lean_object* v_b_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_){
_start:
{
size_t v_i_boxed_412_; size_t v_stop_boxed_413_; lean_object* v_res_414_; 
v_i_boxed_412_ = lean_unbox_usize(v_i_404_);
lean_dec(v_i_404_);
v_stop_boxed_413_ = lean_unbox_usize(v_stop_405_);
lean_dec(v_stop_405_);
v_res_414_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13(v_as_403_, v_i_boxed_412_, v_stop_boxed_413_, v_b_406_, v___y_407_, v___y_408_, v___y_409_, v___y_410_);
lean_dec(v___y_410_);
lean_dec_ref(v___y_409_);
lean_dec(v___y_408_);
lean_dec_ref(v___y_407_);
lean_dec_ref(v_as_403_);
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
v___x_590_ = lean_st_ref_put(v___y_551_, v___x_589_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___lam__0(lean_object* v_fixedParamPerms_644_, lean_object* v___x_645_, lean_object* v___x_646_, lean_object* v_xs_647_, lean_object* v_snd_648_, uint8_t v___x_649_, lean_object* v_ys_650_, lean_object* v_x_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_){
_start:
{
lean_object* v_perms_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; uint8_t v___x_661_; uint8_t v___x_662_; lean_object* v___x_663_; 
v_perms_657_ = lean_ctor_get(v_fixedParamPerms_644_, 1);
v___x_658_ = lean_array_get_borrowed(v___x_645_, v_perms_657_, v___x_646_);
lean_inc_ref(v_ys_650_);
lean_inc(v___x_658_);
v___x_659_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v___x_658_, v_xs_647_, v_ys_650_);
v___x_660_ = l_Lean_Expr_beta(v_snd_648_, v_ys_650_);
v___x_661_ = 0;
v___x_662_ = 1;
v___x_663_ = l_Lean_Meta_mkLambdaFVars(v___x_659_, v___x_660_, v___x_661_, v___x_649_, v___x_661_, v___x_649_, v___x_662_, v___y_652_, v___y_653_, v___y_654_, v___y_655_);
lean_dec_ref(v___x_659_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___lam__0___boxed(lean_object* v_fixedParamPerms_664_, lean_object* v___x_665_, lean_object* v___x_666_, lean_object* v_xs_667_, lean_object* v_snd_668_, lean_object* v___x_669_, lean_object* v_ys_670_, lean_object* v_x_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_){
_start:
{
uint8_t v___x_27703__boxed_677_; lean_object* v_res_678_; 
v___x_27703__boxed_677_ = lean_unbox(v___x_669_);
v_res_678_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___lam__0(v_fixedParamPerms_664_, v___x_665_, v___x_666_, v_xs_667_, v_snd_668_, v___x_27703__boxed_677_, v_ys_670_, v_x_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_);
lean_dec(v___y_675_);
lean_dec_ref(v___y_674_);
lean_dec(v___y_673_);
lean_dec_ref(v___y_672_);
lean_dec_ref(v_x_671_);
lean_dec_ref(v_xs_667_);
lean_dec(v___x_666_);
lean_dec_ref(v___x_665_);
lean_dec_ref(v_fixedParamPerms_664_);
return v_res_678_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_679_; 
v___x_679_ = l_Array_instInhabited(lean_box(0));
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg(lean_object* v_fixedParamPerms_680_, lean_object* v_xs_681_, size_t v_sz_682_, size_t v_i_683_, lean_object* v_bs_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_){
_start:
{
uint8_t v___x_690_; 
v___x_690_ = lean_usize_dec_lt(v_i_683_, v_sz_682_);
if (v___x_690_ == 0)
{
lean_object* v___x_691_; 
lean_dec_ref(v_xs_681_);
lean_dec_ref(v_fixedParamPerms_680_);
v___x_691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_691_, 0, v_bs_684_);
return v___x_691_;
}
else
{
lean_object* v_v_692_; lean_object* v_fst_693_; lean_object* v_snd_694_; lean_object* v___x_695_; lean_object* v_bs_x27_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___f_700_; uint8_t v___x_701_; lean_object* v___x_702_; 
v_v_692_ = lean_array_uget_borrowed(v_bs_684_, v_i_683_);
v_fst_693_ = lean_ctor_get(v_v_692_, 0);
lean_inc(v_fst_693_);
v_snd_694_ = lean_ctor_get(v_v_692_, 1);
lean_inc(v_snd_694_);
v___x_695_ = lean_unsigned_to_nat(0u);
v_bs_x27_696_ = lean_array_uset(v_bs_684_, v_i_683_, v___x_695_);
v___x_697_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0);
v___x_698_ = lean_usize_to_nat(v_i_683_);
v___x_699_ = lean_box(v___x_690_);
lean_inc_ref(v_xs_681_);
lean_inc_ref(v_fixedParamPerms_680_);
v___f_700_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___lam__0___boxed), 13, 6);
lean_closure_set(v___f_700_, 0, v_fixedParamPerms_680_);
lean_closure_set(v___f_700_, 1, v___x_697_);
lean_closure_set(v___f_700_, 2, v___x_698_);
lean_closure_set(v___f_700_, 3, v_xs_681_);
lean_closure_set(v___f_700_, 4, v_snd_694_);
lean_closure_set(v___f_700_, 5, v___x_699_);
v___x_701_ = 0;
v___x_702_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg(v_fst_693_, v___f_700_, v___x_701_, v___y_685_, v___y_686_, v___y_687_, v___y_688_);
if (lean_obj_tag(v___x_702_) == 0)
{
lean_object* v_a_703_; size_t v___x_704_; size_t v___x_705_; lean_object* v___x_706_; 
v_a_703_ = lean_ctor_get(v___x_702_, 0);
lean_inc(v_a_703_);
lean_dec_ref_known(v___x_702_, 1);
v___x_704_ = ((size_t)1ULL);
v___x_705_ = lean_usize_add(v_i_683_, v___x_704_);
v___x_706_ = lean_array_uset(v_bs_x27_696_, v_i_683_, v_a_703_);
v_i_683_ = v___x_705_;
v_bs_684_ = v___x_706_;
goto _start;
}
else
{
lean_object* v_a_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_715_; 
lean_dec_ref(v_bs_x27_696_);
lean_dec_ref(v_xs_681_);
lean_dec_ref(v_fixedParamPerms_680_);
v_a_708_ = lean_ctor_get(v___x_702_, 0);
v_isSharedCheck_715_ = !lean_is_exclusive(v___x_702_);
if (v_isSharedCheck_715_ == 0)
{
v___x_710_ = v___x_702_;
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_a_708_);
lean_dec(v___x_702_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v___x_713_; 
if (v_isShared_711_ == 0)
{
v___x_713_ = v___x_710_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v_a_708_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
return v___x_713_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___boxed(lean_object* v_fixedParamPerms_716_, lean_object* v_xs_717_, lean_object* v_sz_718_, lean_object* v_i_719_, lean_object* v_bs_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_){
_start:
{
size_t v_sz_boxed_726_; size_t v_i_boxed_727_; lean_object* v_res_728_; 
v_sz_boxed_726_ = lean_unbox_usize(v_sz_718_);
lean_dec(v_sz_718_);
v_i_boxed_727_ = lean_unbox_usize(v_i_719_);
lean_dec(v_i_719_);
v_res_728_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg(v_fixedParamPerms_716_, v_xs_717_, v_sz_boxed_726_, v_i_boxed_727_, v_bs_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_);
lean_dec(v___y_724_);
lean_dec_ref(v___y_723_);
lean_dec(v___y_722_);
lean_dec_ref(v___y_721_);
return v_res_728_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(lean_object* v_a_729_, lean_object* v_a_730_){
_start:
{
if (lean_obj_tag(v_a_729_) == 0)
{
lean_object* v___x_731_; 
v___x_731_ = l_List_reverse___redArg(v_a_730_);
return v___x_731_;
}
else
{
lean_object* v_head_732_; lean_object* v_tail_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_742_; 
v_head_732_ = lean_ctor_get(v_a_729_, 0);
v_tail_733_ = lean_ctor_get(v_a_729_, 1);
v_isSharedCheck_742_ = !lean_is_exclusive(v_a_729_);
if (v_isSharedCheck_742_ == 0)
{
v___x_735_ = v_a_729_;
v_isShared_736_ = v_isSharedCheck_742_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_tail_733_);
lean_inc(v_head_732_);
lean_dec(v_a_729_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_742_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v___x_737_; lean_object* v___x_739_; 
v___x_737_ = l_Lean_MessageData_ofExpr(v_head_732_);
if (v_isShared_736_ == 0)
{
lean_ctor_set(v___x_735_, 1, v_a_730_);
lean_ctor_set(v___x_735_, 0, v___x_737_);
v___x_739_ = v___x_735_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v___x_737_);
lean_ctor_set(v_reuseFailAlloc_741_, 1, v_a_730_);
v___x_739_ = v_reuseFailAlloc_741_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
v_a_729_ = v_tail_733_;
v_a_730_ = v___x_739_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16_spec__29___redArg(lean_object* v_declName_743_, uint8_t v_s_744_, lean_object* v___y_745_, lean_object* v___y_746_){
_start:
{
lean_object* v___x_748_; lean_object* v_env_749_; lean_object* v_nextMacroScope_750_; lean_object* v_ngen_751_; lean_object* v_auxDeclNGen_752_; lean_object* v_traceState_753_; lean_object* v_messages_754_; lean_object* v_infoState_755_; lean_object* v_snapshotTasks_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_785_; 
v___x_748_ = lean_st_ref_take(v___y_746_);
v_env_749_ = lean_ctor_get(v___x_748_, 0);
v_nextMacroScope_750_ = lean_ctor_get(v___x_748_, 1);
v_ngen_751_ = lean_ctor_get(v___x_748_, 2);
v_auxDeclNGen_752_ = lean_ctor_get(v___x_748_, 3);
v_traceState_753_ = lean_ctor_get(v___x_748_, 4);
v_messages_754_ = lean_ctor_get(v___x_748_, 6);
v_infoState_755_ = lean_ctor_get(v___x_748_, 7);
v_snapshotTasks_756_ = lean_ctor_get(v___x_748_, 8);
v_isSharedCheck_785_ = !lean_is_exclusive(v___x_748_);
if (v_isSharedCheck_785_ == 0)
{
lean_object* v_unused_786_; 
v_unused_786_ = lean_ctor_get(v___x_748_, 5);
lean_dec(v_unused_786_);
v___x_758_ = v___x_748_;
v_isShared_759_ = v_isSharedCheck_785_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_snapshotTasks_756_);
lean_inc(v_infoState_755_);
lean_inc(v_messages_754_);
lean_inc(v_traceState_753_);
lean_inc(v_auxDeclNGen_752_);
lean_inc(v_ngen_751_);
lean_inc(v_nextMacroScope_750_);
lean_inc(v_env_749_);
lean_dec(v___x_748_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_785_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
uint8_t v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_765_; 
v___x_760_ = 0;
v___x_761_ = lean_box(0);
v___x_762_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_749_, v_declName_743_, v_s_744_, v___x_760_, v___x_761_);
v___x_763_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__2);
if (v_isShared_759_ == 0)
{
lean_ctor_set(v___x_758_, 5, v___x_763_);
lean_ctor_set(v___x_758_, 0, v___x_762_);
v___x_765_ = v___x_758_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v___x_762_);
lean_ctor_set(v_reuseFailAlloc_784_, 1, v_nextMacroScope_750_);
lean_ctor_set(v_reuseFailAlloc_784_, 2, v_ngen_751_);
lean_ctor_set(v_reuseFailAlloc_784_, 3, v_auxDeclNGen_752_);
lean_ctor_set(v_reuseFailAlloc_784_, 4, v_traceState_753_);
lean_ctor_set(v_reuseFailAlloc_784_, 5, v___x_763_);
lean_ctor_set(v_reuseFailAlloc_784_, 6, v_messages_754_);
lean_ctor_set(v_reuseFailAlloc_784_, 7, v_infoState_755_);
lean_ctor_set(v_reuseFailAlloc_784_, 8, v_snapshotTasks_756_);
v___x_765_ = v_reuseFailAlloc_784_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v_mctx_768_; lean_object* v_zetaDeltaFVarIds_769_; lean_object* v_postponed_770_; lean_object* v_diag_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_782_; 
v___x_766_ = lean_st_ref_put(v___y_746_, v___x_765_);
v___x_767_ = lean_st_ref_take(v___y_745_);
v_mctx_768_ = lean_ctor_get(v___x_767_, 0);
v_zetaDeltaFVarIds_769_ = lean_ctor_get(v___x_767_, 2);
v_postponed_770_ = lean_ctor_get(v___x_767_, 3);
v_diag_771_ = lean_ctor_get(v___x_767_, 4);
v_isSharedCheck_782_ = !lean_is_exclusive(v___x_767_);
if (v_isSharedCheck_782_ == 0)
{
lean_object* v_unused_783_; 
v_unused_783_ = lean_ctor_get(v___x_767_, 1);
lean_dec(v_unused_783_);
v___x_773_ = v___x_767_;
v_isShared_774_ = v_isSharedCheck_782_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_diag_771_);
lean_inc(v_postponed_770_);
lean_inc(v_zetaDeltaFVarIds_769_);
lean_inc(v_mctx_768_);
lean_dec(v___x_767_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_782_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v___x_775_; lean_object* v___x_777_; 
v___x_775_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__3, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__3);
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 1, v___x_775_);
v___x_777_ = v___x_773_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v_mctx_768_);
lean_ctor_set(v_reuseFailAlloc_781_, 1, v___x_775_);
lean_ctor_set(v_reuseFailAlloc_781_, 2, v_zetaDeltaFVarIds_769_);
lean_ctor_set(v_reuseFailAlloc_781_, 3, v_postponed_770_);
lean_ctor_set(v_reuseFailAlloc_781_, 4, v_diag_771_);
v___x_777_ = v_reuseFailAlloc_781_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_778_ = lean_st_ref_put(v___y_745_, v___x_777_);
v___x_779_ = lean_box(0);
v___x_780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_780_, 0, v___x_779_);
return v___x_780_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16_spec__29___redArg___boxed(lean_object* v_declName_787_, lean_object* v_s_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_){
_start:
{
uint8_t v_s_boxed_792_; lean_object* v_res_793_; 
v_s_boxed_792_ = lean_unbox(v_s_788_);
v_res_793_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16_spec__29___redArg(v_declName_787_, v_s_boxed_792_, v___y_789_, v___y_790_);
lean_dec(v___y_790_);
lean_dec(v___y_789_);
return v_res_793_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16(lean_object* v_declName_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_){
_start:
{
uint8_t v___x_800_; lean_object* v___x_801_; 
v___x_800_ = 0;
v___x_801_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16_spec__29___redArg(v_declName_794_, v___x_800_, v___y_796_, v___y_798_);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16___boxed(lean_object* v_declName_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_){
_start:
{
lean_object* v_res_808_; 
v_res_808_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16(v_declName_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_);
lean_dec(v___y_806_);
lean_dec_ref(v___y_805_);
lean_dec(v___y_804_);
lean_dec_ref(v___y_803_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg(lean_object* v_xs_812_, uint8_t v_a_813_, lean_object* v_preDefs_814_, lean_object* v___x_815_, size_t v_sz_816_, size_t v_i_817_, lean_object* v_bs_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_){
_start:
{
uint8_t v___x_824_; 
v___x_824_ = lean_usize_dec_lt(v_i_817_, v_sz_816_);
if (v___x_824_ == 0)
{
lean_object* v___x_825_; 
lean_dec(v___x_815_);
v___x_825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_825_, 0, v_bs_818_);
return v___x_825_;
}
else
{
lean_object* v_v_826_; lean_object* v___x_827_; lean_object* v_bs_x27_828_; lean_object* v_a_830_; lean_object* v___y_836_; uint8_t v___x_846_; lean_object* v___x_847_; 
v_v_826_ = lean_array_uget(v_bs_818_, v_i_817_);
v___x_827_ = lean_unsigned_to_nat(0u);
v_bs_x27_828_ = lean_array_uset(v_bs_818_, v_i_817_, v___x_827_);
v___x_846_ = 1;
v___x_847_ = l_Lean_Meta_mkLambdaFVars(v_xs_812_, v_v_826_, v_a_813_, v___x_824_, v_a_813_, v___x_824_, v___x_846_, v___y_819_, v___y_820_, v___y_821_, v___y_822_);
if (lean_obj_tag(v___x_847_) == 0)
{
lean_object* v_a_848_; lean_object* v___x_849_; 
v_a_848_ = lean_ctor_get(v___x_847_, 0);
lean_inc(v_a_848_);
lean_dec_ref_known(v___x_847_, 1);
v___x_849_ = l_Lean_Elab_eraseRecAppSyntaxExpr(v_a_848_, v___y_821_, v___y_822_);
if (lean_obj_tag(v___x_849_) == 0)
{
lean_object* v_a_850_; lean_object* v___x_851_; 
v_a_850_ = lean_ctor_get(v___x_849_, 0);
lean_inc_n(v_a_850_, 2);
lean_dec_ref_known(v___x_849_, 1);
lean_inc(v___y_822_);
lean_inc_ref(v___y_821_);
lean_inc(v___y_820_);
lean_inc_ref(v___y_819_);
v___x_851_ = lean_infer_type(v_a_850_, v___y_819_, v___y_820_, v___y_821_, v___y_822_);
if (lean_obj_tag(v___x_851_) == 0)
{
lean_object* v_a_852_; lean_object* v___x_853_; 
v_a_852_ = lean_ctor_get(v___x_851_, 0);
lean_inc(v_a_852_);
lean_dec_ref_known(v___x_851_, 1);
v___x_853_ = l_Lean_Meta_letToHave(v_a_852_, v___y_819_, v___y_820_, v___y_821_, v___y_822_);
if (lean_obj_tag(v___x_853_) == 0)
{
lean_object* v_a_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_937_; 
v_a_854_ = lean_ctor_get(v___x_853_, 0);
v_isSharedCheck_937_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_937_ == 0)
{
v___x_856_ = v___x_853_;
v_isShared_857_ = v_isSharedCheck_937_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_a_854_);
lean_dec(v___x_853_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_937_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v_modifiers_862_; lean_object* v_levelParams_863_; lean_object* v_declName_864_; lean_object* v_env_865_; uint8_t v_isUnsafe_866_; lean_object* v___x_867_; lean_object* v___x_868_; uint32_t v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; uint8_t v___y_873_; 
v___x_858_ = lean_st_ref_get(v___y_822_);
v___x_859_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_860_ = lean_usize_to_nat(v_i_817_);
v___x_861_ = lean_array_get_borrowed(v___x_859_, v_preDefs_814_, v___x_860_);
lean_dec(v___x_860_);
v_modifiers_862_ = lean_ctor_get(v___x_861_, 2);
v_levelParams_863_ = lean_ctor_get(v___x_861_, 1);
v_declName_864_ = lean_ctor_get(v___x_861_, 3);
v_env_865_ = lean_ctor_get(v___x_858_, 0);
lean_inc_ref(v_env_865_);
lean_dec(v___x_858_);
v_isUnsafe_866_ = lean_ctor_get_uint8(v_modifiers_862_, sizeof(void*)*3 + 4);
v___x_867_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg___closed__1));
lean_inc(v_declName_864_);
v___x_868_ = l_Lean_Name_append(v_declName_864_, v___x_867_);
lean_inc(v_a_850_);
v___x_869_ = l_Lean_getMaxHeight(v_env_865_, v_a_850_);
lean_inc(v_levelParams_863_);
lean_inc(v___x_868_);
v___x_870_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_870_, 0, v___x_868_);
lean_ctor_set(v___x_870_, 1, v_levelParams_863_);
lean_ctor_set(v___x_870_, 2, v_a_854_);
v___x_871_ = lean_box(1);
if (v_isUnsafe_866_ == 0)
{
uint8_t v___x_935_; 
v___x_935_ = 1;
v___y_873_ = v___x_935_;
goto v___jp_872_;
}
else
{
uint8_t v___x_936_; 
v___x_936_ = 0;
v___y_873_ = v___x_936_;
goto v___jp_872_;
}
v___jp_872_:
{
lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_878_; 
v___x_874_ = lean_box(0);
lean_inc(v___x_868_);
v___x_875_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_875_, 0, v___x_868_);
lean_ctor_set(v___x_875_, 1, v___x_874_);
v___x_876_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_876_, 0, v___x_870_);
lean_ctor_set(v___x_876_, 1, v_a_850_);
lean_ctor_set(v___x_876_, 2, v___x_871_);
lean_ctor_set(v___x_876_, 3, v___x_875_);
lean_ctor_set_uint8(v___x_876_, sizeof(void*)*4, v___y_873_);
if (v_isShared_857_ == 0)
{
lean_ctor_set_tag(v___x_856_, 1);
lean_ctor_set(v___x_856_, 0, v___x_876_);
v___x_878_ = v___x_856_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v___x_876_);
v___x_878_ = v_reuseFailAlloc_934_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
lean_object* v___x_879_; 
v___x_879_ = l_Lean_addDecl(v___x_878_, v_a_813_, v___y_821_, v___y_822_);
if (lean_obj_tag(v___x_879_) == 0)
{
lean_object* v___x_880_; lean_object* v_env_881_; lean_object* v_nextMacroScope_882_; lean_object* v_ngen_883_; lean_object* v_auxDeclNGen_884_; lean_object* v_traceState_885_; lean_object* v_messages_886_; lean_object* v_infoState_887_; lean_object* v_snapshotTasks_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_924_; 
lean_dec_ref_known(v___x_879_, 1);
v___x_880_ = lean_st_ref_take(v___y_822_);
v_env_881_ = lean_ctor_get(v___x_880_, 0);
v_nextMacroScope_882_ = lean_ctor_get(v___x_880_, 1);
v_ngen_883_ = lean_ctor_get(v___x_880_, 2);
v_auxDeclNGen_884_ = lean_ctor_get(v___x_880_, 3);
v_traceState_885_ = lean_ctor_get(v___x_880_, 4);
v_messages_886_ = lean_ctor_get(v___x_880_, 6);
v_infoState_887_ = lean_ctor_get(v___x_880_, 7);
v_snapshotTasks_888_ = lean_ctor_get(v___x_880_, 8);
v_isSharedCheck_924_ = !lean_is_exclusive(v___x_880_);
if (v_isSharedCheck_924_ == 0)
{
lean_object* v_unused_925_; 
v_unused_925_ = lean_ctor_get(v___x_880_, 5);
lean_dec(v_unused_925_);
v___x_890_ = v___x_880_;
v_isShared_891_ = v_isSharedCheck_924_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_snapshotTasks_888_);
lean_inc(v_infoState_887_);
lean_inc(v_messages_886_);
lean_inc(v_traceState_885_);
lean_inc(v_auxDeclNGen_884_);
lean_inc(v_ngen_883_);
lean_inc(v_nextMacroScope_882_);
lean_inc(v_env_881_);
lean_dec(v___x_880_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_924_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_895_; 
lean_inc(v___x_868_);
v___x_892_ = l_Lean_setDefHeightOverride(v_env_881_, v___x_868_, v___x_869_);
v___x_893_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__2);
if (v_isShared_891_ == 0)
{
lean_ctor_set(v___x_890_, 5, v___x_893_);
lean_ctor_set(v___x_890_, 0, v___x_892_);
v___x_895_ = v___x_890_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v___x_892_);
lean_ctor_set(v_reuseFailAlloc_923_, 1, v_nextMacroScope_882_);
lean_ctor_set(v_reuseFailAlloc_923_, 2, v_ngen_883_);
lean_ctor_set(v_reuseFailAlloc_923_, 3, v_auxDeclNGen_884_);
lean_ctor_set(v_reuseFailAlloc_923_, 4, v_traceState_885_);
lean_ctor_set(v_reuseFailAlloc_923_, 5, v___x_893_);
lean_ctor_set(v_reuseFailAlloc_923_, 6, v_messages_886_);
lean_ctor_set(v_reuseFailAlloc_923_, 7, v_infoState_887_);
lean_ctor_set(v_reuseFailAlloc_923_, 8, v_snapshotTasks_888_);
v___x_895_ = v_reuseFailAlloc_923_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v_mctx_898_; lean_object* v_zetaDeltaFVarIds_899_; lean_object* v_postponed_900_; lean_object* v_diag_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_921_; 
v___x_896_ = lean_st_ref_put(v___y_822_, v___x_895_);
v___x_897_ = lean_st_ref_take(v___y_820_);
v_mctx_898_ = lean_ctor_get(v___x_897_, 0);
v_zetaDeltaFVarIds_899_ = lean_ctor_get(v___x_897_, 2);
v_postponed_900_ = lean_ctor_get(v___x_897_, 3);
v_diag_901_ = lean_ctor_get(v___x_897_, 4);
v_isSharedCheck_921_ = !lean_is_exclusive(v___x_897_);
if (v_isSharedCheck_921_ == 0)
{
lean_object* v_unused_922_; 
v_unused_922_ = lean_ctor_get(v___x_897_, 1);
lean_dec(v_unused_922_);
v___x_903_ = v___x_897_;
v_isShared_904_ = v_isSharedCheck_921_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_diag_901_);
lean_inc(v_postponed_900_);
lean_inc(v_zetaDeltaFVarIds_899_);
lean_inc(v_mctx_898_);
lean_dec(v___x_897_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_921_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
lean_object* v___x_905_; lean_object* v___x_907_; 
v___x_905_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__3, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__3);
if (v_isShared_904_ == 0)
{
lean_ctor_set(v___x_903_, 1, v___x_905_);
v___x_907_ = v___x_903_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v_mctx_898_);
lean_ctor_set(v_reuseFailAlloc_920_, 1, v___x_905_);
lean_ctor_set(v_reuseFailAlloc_920_, 2, v_zetaDeltaFVarIds_899_);
lean_ctor_set(v_reuseFailAlloc_920_, 3, v_postponed_900_);
lean_ctor_set(v_reuseFailAlloc_920_, 4, v_diag_901_);
v___x_907_ = v_reuseFailAlloc_920_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_908_ = lean_st_ref_put(v___y_820_, v___x_907_);
lean_inc(v___x_868_);
v___x_909_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16(v___x_868_, v___y_819_, v___y_820_, v___y_821_, v___y_822_);
if (lean_obj_tag(v___x_909_) == 0)
{
lean_object* v___x_910_; lean_object* v___x_911_; 
lean_dec_ref_known(v___x_909_, 1);
lean_inc(v___x_815_);
v___x_910_ = l_Lean_mkConst(v___x_868_, v___x_815_);
v___x_911_ = l_Lean_mkAppN(v___x_910_, v_xs_812_);
v_a_830_ = v___x_911_;
goto v___jp_829_;
}
else
{
lean_object* v_a_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_919_; 
lean_dec(v___x_868_);
lean_dec_ref(v_bs_x27_828_);
lean_dec(v___x_815_);
v_a_912_ = lean_ctor_get(v___x_909_, 0);
v_isSharedCheck_919_ = !lean_is_exclusive(v___x_909_);
if (v_isSharedCheck_919_ == 0)
{
v___x_914_ = v___x_909_;
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_a_912_);
lean_dec(v___x_909_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___x_917_; 
if (v_isShared_915_ == 0)
{
v___x_917_ = v___x_914_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v_a_912_);
v___x_917_ = v_reuseFailAlloc_918_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
return v___x_917_;
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
lean_object* v_a_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_933_; 
lean_dec(v___x_868_);
lean_dec_ref(v_bs_x27_828_);
lean_dec(v___x_815_);
v_a_926_ = lean_ctor_get(v___x_879_, 0);
v_isSharedCheck_933_ = !lean_is_exclusive(v___x_879_);
if (v_isSharedCheck_933_ == 0)
{
v___x_928_ = v___x_879_;
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_a_926_);
lean_dec(v___x_879_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v___x_931_; 
if (v_isShared_929_ == 0)
{
v___x_931_ = v___x_928_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v_a_926_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_850_);
v___y_836_ = v___x_853_;
goto v___jp_835_;
}
}
else
{
lean_dec(v_a_850_);
v___y_836_ = v___x_851_;
goto v___jp_835_;
}
}
else
{
v___y_836_ = v___x_849_;
goto v___jp_835_;
}
}
else
{
v___y_836_ = v___x_847_;
goto v___jp_835_;
}
v___jp_829_:
{
size_t v___x_831_; size_t v___x_832_; lean_object* v___x_833_; 
v___x_831_ = ((size_t)1ULL);
v___x_832_ = lean_usize_add(v_i_817_, v___x_831_);
v___x_833_ = lean_array_uset(v_bs_x27_828_, v_i_817_, v_a_830_);
v_i_817_ = v___x_832_;
v_bs_818_ = v___x_833_;
goto _start;
}
v___jp_835_:
{
if (lean_obj_tag(v___y_836_) == 0)
{
lean_object* v_a_837_; 
v_a_837_ = lean_ctor_get(v___y_836_, 0);
lean_inc(v_a_837_);
lean_dec_ref_known(v___y_836_, 1);
v_a_830_ = v_a_837_;
goto v___jp_829_;
}
else
{
lean_object* v_a_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_845_; 
lean_dec_ref(v_bs_x27_828_);
lean_dec(v___x_815_);
v_a_838_ = lean_ctor_get(v___y_836_, 0);
v_isSharedCheck_845_ = !lean_is_exclusive(v___y_836_);
if (v_isSharedCheck_845_ == 0)
{
v___x_840_ = v___y_836_;
v_isShared_841_ = v_isSharedCheck_845_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_a_838_);
lean_dec(v___y_836_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_845_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
lean_object* v___x_843_; 
if (v_isShared_841_ == 0)
{
v___x_843_ = v___x_840_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v_a_838_);
v___x_843_ = v_reuseFailAlloc_844_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
return v___x_843_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg___boxed(lean_object* v_xs_938_, lean_object* v_a_939_, lean_object* v_preDefs_940_, lean_object* v___x_941_, lean_object* v_sz_942_, lean_object* v_i_943_, lean_object* v_bs_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_){
_start:
{
uint8_t v_a_27952__boxed_950_; size_t v_sz_boxed_951_; size_t v_i_boxed_952_; lean_object* v_res_953_; 
v_a_27952__boxed_950_ = lean_unbox(v_a_939_);
v_sz_boxed_951_ = lean_unbox_usize(v_sz_942_);
lean_dec(v_sz_942_);
v_i_boxed_952_ = lean_unbox_usize(v_i_943_);
lean_dec(v_i_943_);
v_res_953_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg(v_xs_938_, v_a_27952__boxed_950_, v_preDefs_940_, v___x_941_, v_sz_boxed_951_, v_i_boxed_952_, v_bs_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_);
lean_dec(v___y_948_);
lean_dec_ref(v___y_947_);
lean_dec(v___y_946_);
lean_dec_ref(v___y_945_);
lean_dec_ref(v_preDefs_940_);
lean_dec_ref(v_xs_938_);
return v_res_953_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__0(void){
_start:
{
lean_object* v___x_954_; 
v___x_954_ = l_instMonadEIO(lean_box(0));
return v___x_954_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__5(void){
_start:
{
lean_object* v___x_959_; 
v___x_959_ = l_Array_instInhabited(lean_box(0));
return v___x_959_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg(lean_object* v_msg_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_){
_start:
{
lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v_toApplicative_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_1029_; 
v___x_966_ = lean_obj_once(&l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__0, &l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__0_once, _init_l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__0);
v___x_967_ = l_StateRefT_x27_instMonad___redArg(v___x_966_);
v_toApplicative_968_ = lean_ctor_get(v___x_967_, 0);
v_isSharedCheck_1029_ = !lean_is_exclusive(v___x_967_);
if (v_isSharedCheck_1029_ == 0)
{
lean_object* v_unused_1030_; 
v_unused_1030_ = lean_ctor_get(v___x_967_, 1);
lean_dec(v_unused_1030_);
v___x_970_ = v___x_967_;
v_isShared_971_ = v_isSharedCheck_1029_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_toApplicative_968_);
lean_dec(v___x_967_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_1029_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v_toFunctor_972_; lean_object* v_toSeq_973_; lean_object* v_toSeqLeft_974_; lean_object* v_toSeqRight_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_1027_; 
v_toFunctor_972_ = lean_ctor_get(v_toApplicative_968_, 0);
v_toSeq_973_ = lean_ctor_get(v_toApplicative_968_, 2);
v_toSeqLeft_974_ = lean_ctor_get(v_toApplicative_968_, 3);
v_toSeqRight_975_ = lean_ctor_get(v_toApplicative_968_, 4);
v_isSharedCheck_1027_ = !lean_is_exclusive(v_toApplicative_968_);
if (v_isSharedCheck_1027_ == 0)
{
lean_object* v_unused_1028_; 
v_unused_1028_ = lean_ctor_get(v_toApplicative_968_, 1);
lean_dec(v_unused_1028_);
v___x_977_ = v_toApplicative_968_;
v_isShared_978_ = v_isSharedCheck_1027_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_toSeqRight_975_);
lean_inc(v_toSeqLeft_974_);
lean_inc(v_toSeq_973_);
lean_inc(v_toFunctor_972_);
lean_dec(v_toApplicative_968_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_1027_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v___f_979_; lean_object* v___f_980_; lean_object* v___f_981_; lean_object* v___f_982_; lean_object* v___x_983_; lean_object* v___f_984_; lean_object* v___f_985_; lean_object* v___f_986_; lean_object* v___x_988_; 
v___f_979_ = ((lean_object*)(l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__1));
v___f_980_ = ((lean_object*)(l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__2));
lean_inc_ref(v_toFunctor_972_);
v___f_981_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_981_, 0, v_toFunctor_972_);
v___f_982_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_982_, 0, v_toFunctor_972_);
v___x_983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_983_, 0, v___f_981_);
lean_ctor_set(v___x_983_, 1, v___f_982_);
v___f_984_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_984_, 0, v_toSeqRight_975_);
v___f_985_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_985_, 0, v_toSeqLeft_974_);
v___f_986_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_986_, 0, v_toSeq_973_);
if (v_isShared_978_ == 0)
{
lean_ctor_set(v___x_977_, 4, v___f_984_);
lean_ctor_set(v___x_977_, 3, v___f_985_);
lean_ctor_set(v___x_977_, 2, v___f_986_);
lean_ctor_set(v___x_977_, 1, v___f_979_);
lean_ctor_set(v___x_977_, 0, v___x_983_);
v___x_988_ = v___x_977_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_1026_; 
v_reuseFailAlloc_1026_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1026_, 0, v___x_983_);
lean_ctor_set(v_reuseFailAlloc_1026_, 1, v___f_979_);
lean_ctor_set(v_reuseFailAlloc_1026_, 2, v___f_986_);
lean_ctor_set(v_reuseFailAlloc_1026_, 3, v___f_985_);
lean_ctor_set(v_reuseFailAlloc_1026_, 4, v___f_984_);
v___x_988_ = v_reuseFailAlloc_1026_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
lean_object* v___x_990_; 
if (v_isShared_971_ == 0)
{
lean_ctor_set(v___x_970_, 1, v___f_980_);
lean_ctor_set(v___x_970_, 0, v___x_988_);
v___x_990_ = v___x_970_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v___x_988_);
lean_ctor_set(v_reuseFailAlloc_1025_, 1, v___f_980_);
v___x_990_ = v_reuseFailAlloc_1025_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
lean_object* v___x_991_; lean_object* v_toApplicative_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_1023_; 
v___x_991_ = l_StateRefT_x27_instMonad___redArg(v___x_990_);
v_toApplicative_992_ = lean_ctor_get(v___x_991_, 0);
v_isSharedCheck_1023_ = !lean_is_exclusive(v___x_991_);
if (v_isSharedCheck_1023_ == 0)
{
lean_object* v_unused_1024_; 
v_unused_1024_ = lean_ctor_get(v___x_991_, 1);
lean_dec(v_unused_1024_);
v___x_994_ = v___x_991_;
v_isShared_995_ = v_isSharedCheck_1023_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_toApplicative_992_);
lean_dec(v___x_991_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_1023_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
lean_object* v_toFunctor_996_; lean_object* v_toSeq_997_; lean_object* v_toSeqLeft_998_; lean_object* v_toSeqRight_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1021_; 
v_toFunctor_996_ = lean_ctor_get(v_toApplicative_992_, 0);
v_toSeq_997_ = lean_ctor_get(v_toApplicative_992_, 2);
v_toSeqLeft_998_ = lean_ctor_get(v_toApplicative_992_, 3);
v_toSeqRight_999_ = lean_ctor_get(v_toApplicative_992_, 4);
v_isSharedCheck_1021_ = !lean_is_exclusive(v_toApplicative_992_);
if (v_isSharedCheck_1021_ == 0)
{
lean_object* v_unused_1022_; 
v_unused_1022_ = lean_ctor_get(v_toApplicative_992_, 1);
lean_dec(v_unused_1022_);
v___x_1001_ = v_toApplicative_992_;
v_isShared_1002_ = v_isSharedCheck_1021_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_toSeqRight_999_);
lean_inc(v_toSeqLeft_998_);
lean_inc(v_toSeq_997_);
lean_inc(v_toFunctor_996_);
lean_dec(v_toApplicative_992_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1021_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v___f_1003_; lean_object* v___f_1004_; lean_object* v___f_1005_; lean_object* v___f_1006_; lean_object* v___x_1007_; lean_object* v___f_1008_; lean_object* v___f_1009_; lean_object* v___f_1010_; lean_object* v___x_1012_; 
v___f_1003_ = ((lean_object*)(l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__3));
v___f_1004_ = ((lean_object*)(l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__4));
lean_inc_ref(v_toFunctor_996_);
v___f_1005_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1005_, 0, v_toFunctor_996_);
v___f_1006_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1006_, 0, v_toFunctor_996_);
v___x_1007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1007_, 0, v___f_1005_);
lean_ctor_set(v___x_1007_, 1, v___f_1006_);
v___f_1008_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1008_, 0, v_toSeqRight_999_);
v___f_1009_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1009_, 0, v_toSeqLeft_998_);
v___f_1010_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1010_, 0, v_toSeq_997_);
if (v_isShared_1002_ == 0)
{
lean_ctor_set(v___x_1001_, 4, v___f_1008_);
lean_ctor_set(v___x_1001_, 3, v___f_1009_);
lean_ctor_set(v___x_1001_, 2, v___f_1010_);
lean_ctor_set(v___x_1001_, 1, v___f_1003_);
lean_ctor_set(v___x_1001_, 0, v___x_1007_);
v___x_1012_ = v___x_1001_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v___x_1007_);
lean_ctor_set(v_reuseFailAlloc_1020_, 1, v___f_1003_);
lean_ctor_set(v_reuseFailAlloc_1020_, 2, v___f_1010_);
lean_ctor_set(v_reuseFailAlloc_1020_, 3, v___f_1009_);
lean_ctor_set(v_reuseFailAlloc_1020_, 4, v___f_1008_);
v___x_1012_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
lean_object* v___x_1014_; 
if (v_isShared_995_ == 0)
{
lean_ctor_set(v___x_994_, 1, v___f_1004_);
lean_ctor_set(v___x_994_, 0, v___x_1012_);
v___x_1014_ = v___x_994_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v___x_1012_);
lean_ctor_set(v_reuseFailAlloc_1019_, 1, v___f_1004_);
v___x_1014_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_23673__overap_1017_; lean_object* v___x_1018_; 
v___x_1015_ = lean_obj_once(&l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__5, &l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__5_once, _init_l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__5);
v___x_1016_ = l_instInhabitedOfMonad___redArg(v___x_1014_, v___x_1015_);
v___x_23673__overap_1017_ = lean_panic_fn_borrowed(v___x_1016_, v_msg_960_);
lean_dec(v___x_1016_);
lean_inc(v___y_964_);
lean_inc_ref(v___y_963_);
lean_inc(v___y_962_);
lean_inc_ref(v___y_961_);
v___x_1018_ = lean_apply_5(v___x_23673__overap_1017_, v___y_961_, v___y_962_, v___y_963_, v___y_964_, lean_box(0));
return v___x_1018_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___boxed(lean_object* v_msg_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg(v_msg_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_);
lean_dec(v___y_1035_);
lean_dec_ref(v___y_1034_);
lean_dec(v___y_1033_);
lean_dec_ref(v___y_1032_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__13(lean_object* v_xs_1038_, size_t v_sz_1039_, size_t v_i_1040_, lean_object* v_bs_1041_){
_start:
{
uint8_t v___x_1042_; 
v___x_1042_ = lean_usize_dec_lt(v_i_1040_, v_sz_1039_);
if (v___x_1042_ == 0)
{
return v_bs_1041_;
}
else
{
lean_object* v___x_1043_; lean_object* v_v_1044_; lean_object* v___x_1045_; lean_object* v_bs_x27_1046_; lean_object* v___x_1047_; size_t v___x_1048_; size_t v___x_1049_; lean_object* v___x_1050_; 
v___x_1043_ = l_Lean_instInhabitedExpr;
v_v_1044_ = lean_array_uget(v_bs_1041_, v_i_1040_);
v___x_1045_ = lean_unsigned_to_nat(0u);
v_bs_x27_1046_ = lean_array_uset(v_bs_1041_, v_i_1040_, v___x_1045_);
v___x_1047_ = lean_array_get_borrowed(v___x_1043_, v_xs_1038_, v_v_1044_);
lean_dec(v_v_1044_);
v___x_1048_ = ((size_t)1ULL);
v___x_1049_ = lean_usize_add(v_i_1040_, v___x_1048_);
lean_inc(v___x_1047_);
v___x_1050_ = lean_array_uset(v_bs_x27_1046_, v_i_1040_, v___x_1047_);
v_i_1040_ = v___x_1049_;
v_bs_1041_ = v___x_1050_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__13___boxed(lean_object* v_xs_1052_, lean_object* v_sz_1053_, lean_object* v_i_1054_, lean_object* v_bs_1055_){
_start:
{
size_t v_sz_boxed_1056_; size_t v_i_boxed_1057_; lean_object* v_res_1058_; 
v_sz_boxed_1056_ = lean_unbox_usize(v_sz_1053_);
lean_dec(v_sz_1053_);
v_i_boxed_1057_ = lean_unbox_usize(v_i_1054_);
lean_dec(v_i_1054_);
v_res_1058_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__13(v_xs_1052_, v_sz_boxed_1056_, v_i_boxed_1057_, v_bs_1055_);
lean_dec_ref(v_xs_1052_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15___redArg(lean_object* v_xs_1059_, lean_object* v_f_1060_, lean_object* v_as_1061_, lean_object* v_bs_1062_, lean_object* v_i_1063_, lean_object* v_cs_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_){
_start:
{
lean_object* v___x_1070_; uint8_t v___x_1071_; 
v___x_1070_ = lean_array_get_size(v_as_1061_);
v___x_1071_ = lean_nat_dec_lt(v_i_1063_, v___x_1070_);
if (v___x_1071_ == 0)
{
lean_object* v___x_1072_; 
lean_dec(v_i_1063_);
lean_dec_ref(v_f_1060_);
v___x_1072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1072_, 0, v_cs_1064_);
return v___x_1072_;
}
else
{
lean_object* v___x_1073_; uint8_t v___x_1074_; 
v___x_1073_ = lean_array_get_size(v_bs_1062_);
v___x_1074_ = lean_nat_dec_lt(v_i_1063_, v___x_1073_);
if (v___x_1074_ == 0)
{
lean_object* v___x_1075_; 
lean_dec(v_i_1063_);
lean_dec_ref(v_f_1060_);
v___x_1075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1075_, 0, v_cs_1064_);
return v___x_1075_;
}
else
{
lean_object* v_a_1076_; lean_object* v_b_1077_; size_t v_sz_1078_; size_t v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; 
v_a_1076_ = lean_array_fget_borrowed(v_as_1061_, v_i_1063_);
v_b_1077_ = lean_array_fget_borrowed(v_bs_1062_, v_i_1063_);
v_sz_1078_ = lean_array_size(v_b_1077_);
v___x_1079_ = ((size_t)0ULL);
lean_inc(v_b_1077_);
v___x_1080_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__13(v_xs_1059_, v_sz_1078_, v___x_1079_, v_b_1077_);
lean_inc_ref(v_f_1060_);
lean_inc(v___y_1068_);
lean_inc_ref(v___y_1067_);
lean_inc(v___y_1066_);
lean_inc_ref(v___y_1065_);
lean_inc(v_a_1076_);
v___x_1081_ = lean_apply_7(v_f_1060_, v_a_1076_, v___x_1080_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_, lean_box(0));
if (lean_obj_tag(v___x_1081_) == 0)
{
lean_object* v_a_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; 
v_a_1082_ = lean_ctor_get(v___x_1081_, 0);
lean_inc(v_a_1082_);
lean_dec_ref_known(v___x_1081_, 1);
v___x_1083_ = lean_unsigned_to_nat(1u);
v___x_1084_ = lean_nat_add(v_i_1063_, v___x_1083_);
lean_dec(v_i_1063_);
v___x_1085_ = lean_array_push(v_cs_1064_, v_a_1082_);
v_i_1063_ = v___x_1084_;
v_cs_1064_ = v___x_1085_;
goto _start;
}
else
{
lean_object* v_a_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1094_; 
lean_dec_ref(v_cs_1064_);
lean_dec(v_i_1063_);
lean_dec_ref(v_f_1060_);
v_a_1087_ = lean_ctor_get(v___x_1081_, 0);
v_isSharedCheck_1094_ = !lean_is_exclusive(v___x_1081_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1089_ = v___x_1081_;
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_a_1087_);
lean_dec(v___x_1081_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1092_; 
if (v_isShared_1090_ == 0)
{
v___x_1092_ = v___x_1089_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_a_1087_);
v___x_1092_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
return v___x_1092_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15___redArg___boxed(lean_object* v_xs_1095_, lean_object* v_f_1096_, lean_object* v_as_1097_, lean_object* v_bs_1098_, lean_object* v_i_1099_, lean_object* v_cs_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_){
_start:
{
lean_object* v_res_1106_; 
v_res_1106_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15___redArg(v_xs_1095_, v_f_1096_, v_as_1097_, v_bs_1098_, v_i_1099_, v_cs_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_);
lean_dec(v___y_1104_);
lean_dec_ref(v___y_1103_);
lean_dec(v___y_1102_);
lean_dec_ref(v___y_1101_);
lean_dec_ref(v_bs_1098_);
lean_dec_ref(v_as_1097_);
lean_dec_ref(v_xs_1095_);
return v_res_1106_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1110_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__2));
v___x_1111_ = lean_unsigned_to_nat(2u);
v___x_1112_ = lean_unsigned_to_nat(73u);
v___x_1113_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__1));
v___x_1114_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__0));
v___x_1115_ = l_mkPanicMessageWithDecl(v___x_1114_, v___x_1113_, v___x_1112_, v___x_1111_, v___x_1110_);
return v___x_1115_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; 
v___x_1117_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__4));
v___x_1118_ = lean_unsigned_to_nat(2u);
v___x_1119_ = lean_unsigned_to_nat(74u);
v___x_1120_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__1));
v___x_1121_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__0));
v___x_1122_ = l_mkPanicMessageWithDecl(v___x_1121_, v___x_1120_, v___x_1119_, v___x_1118_, v___x_1117_);
return v___x_1122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg(lean_object* v_f_1125_, lean_object* v_positions_1126_, lean_object* v_ys_1127_, lean_object* v_xs_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_){
_start:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; uint8_t v___x_1136_; 
v___x_1134_ = lean_array_get_size(v_positions_1126_);
v___x_1135_ = lean_array_get_size(v_ys_1127_);
v___x_1136_ = lean_nat_dec_eq(v___x_1134_, v___x_1135_);
if (v___x_1136_ == 0)
{
lean_object* v___x_1137_; lean_object* v___x_1138_; 
lean_dec_ref(v_f_1125_);
v___x_1137_ = lean_obj_once(&l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__3, &l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__3_once, _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__3);
v___x_1138_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg(v___x_1137_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_);
return v___x_1138_;
}
else
{
lean_object* v___x_1139_; lean_object* v___x_1140_; uint8_t v___x_1141_; 
v___x_1139_ = l_Lean_Elab_Structural_Positions_numIndices(v_positions_1126_);
v___x_1140_ = lean_array_get_size(v_xs_1128_);
v___x_1141_ = lean_nat_dec_eq(v___x_1139_, v___x_1140_);
lean_dec(v___x_1139_);
if (v___x_1141_ == 0)
{
lean_object* v___x_1142_; lean_object* v___x_1143_; 
lean_dec_ref(v_f_1125_);
v___x_1142_ = lean_obj_once(&l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__5, &l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__5_once, _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__5);
v___x_1143_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg(v___x_1142_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_);
return v___x_1143_;
}
else
{
lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; 
v___x_1144_ = lean_unsigned_to_nat(0u);
v___x_1145_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__6));
v___x_1146_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15___redArg(v_xs_1128_, v_f_1125_, v_ys_1127_, v_positions_1126_, v___x_1144_, v___x_1145_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_);
return v___x_1146_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___boxed(lean_object* v_f_1147_, lean_object* v_positions_1148_, lean_object* v_ys_1149_, lean_object* v_xs_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_){
_start:
{
lean_object* v_res_1156_; 
v_res_1156_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg(v_f_1147_, v_positions_1148_, v_ys_1149_, v_xs_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_);
lean_dec(v___y_1154_);
lean_dec_ref(v___y_1153_);
lean_dec(v___y_1152_);
lean_dec_ref(v___y_1151_);
lean_dec_ref(v_xs_1150_);
lean_dec_ref(v_ys_1149_);
lean_dec_ref(v_positions_1148_);
return v_res_1156_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__15(lean_object* v_a_1157_, lean_object* v_a_1158_){
_start:
{
if (lean_obj_tag(v_a_1157_) == 0)
{
lean_object* v___x_1159_; 
v___x_1159_ = l_List_reverse___redArg(v_a_1158_);
return v___x_1159_;
}
else
{
lean_object* v_head_1160_; lean_object* v_tail_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1170_; 
v_head_1160_ = lean_ctor_get(v_a_1157_, 0);
v_tail_1161_ = lean_ctor_get(v_a_1157_, 1);
v_isSharedCheck_1170_ = !lean_is_exclusive(v_a_1157_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1163_ = v_a_1157_;
v_isShared_1164_ = v_isSharedCheck_1170_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_tail_1161_);
lean_inc(v_head_1160_);
lean_dec(v_a_1157_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1170_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v___x_1165_; lean_object* v___x_1167_; 
v___x_1165_ = l_Lean_mkLevelParam(v_head_1160_);
if (v_isShared_1164_ == 0)
{
lean_ctor_set(v___x_1163_, 1, v_a_1158_);
lean_ctor_set(v___x_1163_, 0, v___x_1165_);
v___x_1167_ = v___x_1163_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v___x_1165_);
lean_ctor_set(v_reuseFailAlloc_1169_, 1, v_a_1158_);
v___x_1167_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
v_a_1157_ = v_tail_1161_;
v_a_1158_ = v___x_1167_;
goto _start;
}
}
}
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
lean_inc_ref(v___y_1381_);
lean_inc_ref(v_preDefs_1249_);
lean_inc_ref(v___x_1244_);
lean_inc_ref_n(v_recArgInfos_1242_, 2);
v___x_1388_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg(v_a_1253_, v_a_1243_, v___y_1382_, v_recArgInfos_1242_, v___x_1244_, v_preDefs_1249_, v___y_1381_, v_sz_1387_, v___x_1245_, v_recArgInfos_1242_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_);
lean_dec_ref(v___y_1382_);
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
v___y_1358_ = v___y_1381_;
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
v___y_1358_ = v___y_1381_;
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
lean_dec_ref(v___y_1381_);
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
lean_dec_ref(v___y_1381_);
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
lean_dec_ref(v___y_1381_);
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
v___y_1381_ = v_a_1430_;
v___y_1382_ = v_a_1432_;
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
v___y_1381_ = v_a_1430_;
v___y_1382_ = v_a_1432_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__6(lean_object* v_xs_1811_, lean_object* v_f_1812_, lean_object* v_x_1813_, lean_object* v_as_1814_, size_t v_i_1815_, size_t v_stop_1816_, lean_object* v_b_1817_){
_start:
{
lean_object* v___y_1819_; uint8_t v___x_1823_; 
v___x_1823_ = lean_usize_dec_eq(v_i_1815_, v_stop_1816_);
if (v___x_1823_ == 0)
{
lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; uint8_t v___x_1828_; 
v___x_1824_ = l_Lean_Elab_Structural_instInhabitedRecArgInfo_default;
v___x_1825_ = lean_array_uget_borrowed(v_as_1814_, v_i_1815_);
v___x_1826_ = lean_array_get_borrowed(v___x_1824_, v_xs_1811_, v___x_1825_);
lean_inc_ref(v_f_1812_);
lean_inc(v___x_1826_);
v___x_1827_ = lean_apply_1(v_f_1812_, v___x_1826_);
v___x_1828_ = lean_nat_dec_eq(v___x_1827_, v_x_1813_);
lean_dec(v___x_1827_);
if (v___x_1828_ == 0)
{
v___y_1819_ = v_b_1817_;
goto v___jp_1818_;
}
else
{
lean_object* v___x_1829_; 
lean_inc(v___x_1825_);
v___x_1829_ = lean_array_push(v_b_1817_, v___x_1825_);
v___y_1819_ = v___x_1829_;
goto v___jp_1818_;
}
}
else
{
lean_dec_ref(v_f_1812_);
return v_b_1817_;
}
v___jp_1818_:
{
size_t v___x_1820_; size_t v___x_1821_; 
v___x_1820_ = ((size_t)1ULL);
v___x_1821_ = lean_usize_add(v_i_1815_, v___x_1820_);
v_i_1815_ = v___x_1821_;
v_b_1817_ = v___y_1819_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__6___boxed(lean_object* v_xs_1830_, lean_object* v_f_1831_, lean_object* v_x_1832_, lean_object* v_as_1833_, lean_object* v_i_1834_, lean_object* v_stop_1835_, lean_object* v_b_1836_){
_start:
{
size_t v_i_boxed_1837_; size_t v_stop_boxed_1838_; lean_object* v_res_1839_; 
v_i_boxed_1837_ = lean_unbox_usize(v_i_1834_);
lean_dec(v_i_1834_);
v_stop_boxed_1838_ = lean_unbox_usize(v_stop_1835_);
lean_dec(v_stop_1835_);
v_res_1839_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__6(v_xs_1830_, v_f_1831_, v_x_1832_, v_as_1833_, v_i_boxed_1837_, v_stop_boxed_1838_, v_b_1836_);
lean_dec_ref(v_as_1833_);
lean_dec(v_x_1832_);
lean_dec_ref(v_xs_1830_);
return v_res_1839_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8(lean_object* v_xs_1842_, lean_object* v_f_1843_, size_t v_sz_1844_, size_t v_i_1845_, lean_object* v_bs_1846_){
_start:
{
uint8_t v___x_1847_; 
v___x_1847_ = lean_usize_dec_lt(v_i_1845_, v_sz_1844_);
if (v___x_1847_ == 0)
{
lean_dec_ref(v_f_1843_);
return v_bs_1846_;
}
else
{
lean_object* v_v_1848_; lean_object* v___x_1849_; lean_object* v_bs_x27_1850_; lean_object* v___y_1852_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; uint8_t v___x_1861_; 
v_v_1848_ = lean_array_uget(v_bs_1846_, v_i_1845_);
v___x_1849_ = lean_unsigned_to_nat(0u);
v_bs_x27_1850_ = lean_array_uset(v_bs_1846_, v_i_1845_, v___x_1849_);
v___x_1857_ = lean_array_get_size(v_xs_1842_);
v___x_1858_ = l_Array_range(v___x_1857_);
v___x_1859_ = lean_array_get_size(v___x_1858_);
v___x_1860_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8___closed__0));
v___x_1861_ = lean_nat_dec_lt(v___x_1849_, v___x_1859_);
if (v___x_1861_ == 0)
{
lean_dec_ref(v___x_1858_);
lean_dec(v_v_1848_);
v___y_1852_ = v___x_1860_;
goto v___jp_1851_;
}
else
{
uint8_t v___x_1862_; 
v___x_1862_ = lean_nat_dec_le(v___x_1859_, v___x_1859_);
if (v___x_1862_ == 0)
{
if (v___x_1861_ == 0)
{
lean_dec_ref(v___x_1858_);
lean_dec(v_v_1848_);
v___y_1852_ = v___x_1860_;
goto v___jp_1851_;
}
else
{
size_t v___x_1863_; size_t v___x_1864_; lean_object* v___x_1865_; 
v___x_1863_ = ((size_t)0ULL);
v___x_1864_ = lean_usize_of_nat(v___x_1859_);
lean_inc_ref(v_f_1843_);
v___x_1865_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__6(v_xs_1842_, v_f_1843_, v_v_1848_, v___x_1858_, v___x_1863_, v___x_1864_, v___x_1860_);
lean_dec_ref(v___x_1858_);
lean_dec(v_v_1848_);
v___y_1852_ = v___x_1865_;
goto v___jp_1851_;
}
}
else
{
size_t v___x_1866_; size_t v___x_1867_; lean_object* v___x_1868_; 
v___x_1866_ = ((size_t)0ULL);
v___x_1867_ = lean_usize_of_nat(v___x_1859_);
lean_inc_ref(v_f_1843_);
v___x_1868_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__6(v_xs_1842_, v_f_1843_, v_v_1848_, v___x_1858_, v___x_1866_, v___x_1867_, v___x_1860_);
lean_dec_ref(v___x_1858_);
lean_dec(v_v_1848_);
v___y_1852_ = v___x_1868_;
goto v___jp_1851_;
}
}
v___jp_1851_:
{
size_t v___x_1853_; size_t v___x_1854_; lean_object* v___x_1855_; 
v___x_1853_ = ((size_t)1ULL);
v___x_1854_ = lean_usize_add(v_i_1845_, v___x_1853_);
v___x_1855_ = lean_array_uset(v_bs_x27_1850_, v_i_1845_, v___y_1852_);
v_i_1845_ = v___x_1854_;
v_bs_1846_ = v___x_1855_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8___boxed(lean_object* v_xs_1869_, lean_object* v_f_1870_, lean_object* v_sz_1871_, lean_object* v_i_1872_, lean_object* v_bs_1873_){
_start:
{
size_t v_sz_boxed_1874_; size_t v_i_boxed_1875_; lean_object* v_res_1876_; 
v_sz_boxed_1874_ = lean_unbox_usize(v_sz_1871_);
lean_dec(v_sz_1871_);
v_i_boxed_1875_ = lean_unbox_usize(v_i_1872_);
lean_dec(v_i_1872_);
v_res_1876_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8(v_xs_1869_, v_f_1870_, v_sz_boxed_1874_, v_i_boxed_1875_, v_bs_1873_);
lean_dec_ref(v_xs_1869_);
return v_res_1876_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11___redArg(lean_object* v_hi_1877_, lean_object* v_pivot_1878_, lean_object* v_as_1879_, lean_object* v_i_1880_, lean_object* v_k_1881_){
_start:
{
uint8_t v___x_1882_; 
v___x_1882_ = lean_nat_dec_lt(v_k_1881_, v_hi_1877_);
if (v___x_1882_ == 0)
{
lean_object* v___x_1883_; lean_object* v___x_1884_; 
lean_dec(v_k_1881_);
v___x_1883_ = lean_array_fswap(v_as_1879_, v_i_1880_, v_hi_1877_);
v___x_1884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1884_, 0, v_i_1880_);
lean_ctor_set(v___x_1884_, 1, v___x_1883_);
return v___x_1884_;
}
else
{
lean_object* v___x_1885_; uint8_t v___x_1886_; 
v___x_1885_ = lean_array_fget_borrowed(v_as_1879_, v_k_1881_);
v___x_1886_ = l_Nat_blt(v___x_1885_, v_pivot_1878_);
if (v___x_1886_ == 0)
{
lean_object* v___x_1887_; lean_object* v___x_1888_; 
v___x_1887_ = lean_unsigned_to_nat(1u);
v___x_1888_ = lean_nat_add(v_k_1881_, v___x_1887_);
lean_dec(v_k_1881_);
v_k_1881_ = v___x_1888_;
goto _start;
}
else
{
lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; 
v___x_1890_ = lean_array_fswap(v_as_1879_, v_i_1880_, v_k_1881_);
v___x_1891_ = lean_unsigned_to_nat(1u);
v___x_1892_ = lean_nat_add(v_i_1880_, v___x_1891_);
lean_dec(v_i_1880_);
v___x_1893_ = lean_nat_add(v_k_1881_, v___x_1891_);
lean_dec(v_k_1881_);
v_as_1879_ = v___x_1890_;
v_i_1880_ = v___x_1892_;
v_k_1881_ = v___x_1893_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11___redArg___boxed(lean_object* v_hi_1895_, lean_object* v_pivot_1896_, lean_object* v_as_1897_, lean_object* v_i_1898_, lean_object* v_k_1899_){
_start:
{
lean_object* v_res_1900_; 
v_res_1900_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11___redArg(v_hi_1895_, v_pivot_1896_, v_as_1897_, v_i_1898_, v_k_1899_);
lean_dec(v_pivot_1896_);
lean_dec(v_hi_1895_);
return v_res_1900_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg(lean_object* v_n_1901_, lean_object* v_as_1902_, lean_object* v_lo_1903_, lean_object* v_hi_1904_){
_start:
{
lean_object* v___y_1906_; uint8_t v___x_1916_; 
v___x_1916_ = lean_nat_dec_lt(v_lo_1903_, v_hi_1904_);
if (v___x_1916_ == 0)
{
lean_dec(v_lo_1903_);
return v_as_1902_;
}
else
{
lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v_mid_1919_; lean_object* v___y_1921_; lean_object* v___y_1927_; lean_object* v___x_1932_; lean_object* v___x_1933_; uint8_t v___x_1934_; 
v___x_1917_ = lean_nat_add(v_lo_1903_, v_hi_1904_);
v___x_1918_ = lean_unsigned_to_nat(1u);
v_mid_1919_ = lean_nat_shiftr(v___x_1917_, v___x_1918_);
lean_dec(v___x_1917_);
v___x_1932_ = lean_array_fget_borrowed(v_as_1902_, v_mid_1919_);
v___x_1933_ = lean_array_fget_borrowed(v_as_1902_, v_lo_1903_);
v___x_1934_ = l_Nat_blt(v___x_1932_, v___x_1933_);
if (v___x_1934_ == 0)
{
v___y_1927_ = v_as_1902_;
goto v___jp_1926_;
}
else
{
lean_object* v___x_1935_; 
v___x_1935_ = lean_array_fswap(v_as_1902_, v_lo_1903_, v_mid_1919_);
v___y_1927_ = v___x_1935_;
goto v___jp_1926_;
}
v___jp_1920_:
{
lean_object* v___x_1922_; lean_object* v___x_1923_; uint8_t v___x_1924_; 
v___x_1922_ = lean_array_fget_borrowed(v___y_1921_, v_mid_1919_);
v___x_1923_ = lean_array_fget_borrowed(v___y_1921_, v_hi_1904_);
v___x_1924_ = l_Nat_blt(v___x_1922_, v___x_1923_);
if (v___x_1924_ == 0)
{
lean_dec(v_mid_1919_);
v___y_1906_ = v___y_1921_;
goto v___jp_1905_;
}
else
{
lean_object* v___x_1925_; 
v___x_1925_ = lean_array_fswap(v___y_1921_, v_mid_1919_, v_hi_1904_);
lean_dec(v_mid_1919_);
v___y_1906_ = v___x_1925_;
goto v___jp_1905_;
}
}
v___jp_1926_:
{
lean_object* v___x_1928_; lean_object* v___x_1929_; uint8_t v___x_1930_; 
v___x_1928_ = lean_array_fget_borrowed(v___y_1927_, v_hi_1904_);
v___x_1929_ = lean_array_fget_borrowed(v___y_1927_, v_lo_1903_);
v___x_1930_ = l_Nat_blt(v___x_1928_, v___x_1929_);
if (v___x_1930_ == 0)
{
v___y_1921_ = v___y_1927_;
goto v___jp_1920_;
}
else
{
lean_object* v___x_1931_; 
v___x_1931_ = lean_array_fswap(v___y_1927_, v_lo_1903_, v_hi_1904_);
v___y_1921_ = v___x_1931_;
goto v___jp_1920_;
}
}
}
v___jp_1905_:
{
lean_object* v_pivot_1907_; lean_object* v___x_1908_; lean_object* v_fst_1909_; lean_object* v_snd_1910_; uint8_t v___x_1911_; 
v_pivot_1907_ = lean_array_fget(v___y_1906_, v_hi_1904_);
lean_inc_n(v_lo_1903_, 2);
v___x_1908_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11___redArg(v_hi_1904_, v_pivot_1907_, v___y_1906_, v_lo_1903_, v_lo_1903_);
lean_dec(v_pivot_1907_);
v_fst_1909_ = lean_ctor_get(v___x_1908_, 0);
lean_inc(v_fst_1909_);
v_snd_1910_ = lean_ctor_get(v___x_1908_, 1);
lean_inc(v_snd_1910_);
lean_dec_ref(v___x_1908_);
v___x_1911_ = lean_nat_dec_le(v_hi_1904_, v_fst_1909_);
if (v___x_1911_ == 0)
{
lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; 
v___x_1912_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg(v_n_1901_, v_snd_1910_, v_lo_1903_, v_fst_1909_);
v___x_1913_ = lean_unsigned_to_nat(1u);
v___x_1914_ = lean_nat_add(v_fst_1909_, v___x_1913_);
lean_dec(v_fst_1909_);
v_as_1902_ = v___x_1912_;
v_lo_1903_ = v___x_1914_;
goto _start;
}
else
{
lean_dec(v_fst_1909_);
lean_dec(v_lo_1903_);
return v_snd_1910_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg___boxed(lean_object* v_n_1936_, lean_object* v_as_1937_, lean_object* v_lo_1938_, lean_object* v_hi_1939_){
_start:
{
lean_object* v_res_1940_; 
v_res_1940_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg(v_n_1936_, v_as_1937_, v_lo_1938_, v_hi_1939_);
lean_dec(v_hi_1939_);
lean_dec(v_n_1936_);
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
v___x_2010_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg(v___y_2008_, v___y_2007_, v___y_2006_, v___y_2009_);
lean_dec(v___y_2009_);
lean_dec(v___y_2008_);
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
v___y_2006_ = v___y_2015_;
v___y_2007_ = v___y_2013_;
v___y_2008_ = v___y_2014_;
v___y_2009_ = v___y_2015_;
goto v___jp_2005_;
}
else
{
v___y_2006_ = v___y_2015_;
v___y_2007_ = v___y_2013_;
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
v___y_2013_ = v___y_2018_;
v___y_2014_ = v___x_2019_;
v___y_2015_ = v___x_2023_;
goto v___jp_2011_;
}
else
{
v___y_2012_ = v___x_2023_;
v___y_2013_ = v___y_2018_;
v___y_2014_ = v___x_2019_;
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
lean_object* v_cellCount_2670_; lean_object* v___x_2671_; 
v_cellCount_2670_ = lean_unsigned_to_nat(16u);
v___x_2671_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_2670_);
return v___x_2671_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v_cellCount_2672_; lean_object* v___x_2673_; 
v_cellCount_2672_ = lean_unsigned_to_nat(16u);
v___x_2673_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_2672_);
return v___x_2673_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; 
v___x_2674_ = lean_obj_once(&l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__2, &l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__2_once, _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__2);
v___x_2675_ = lean_obj_once(&l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__1, &l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__1_once, _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__1);
v___x_2676_ = lean_unsigned_to_nat(0u);
v___x_2677_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2677_, 0, v___x_2676_);
lean_ctor_set(v___x_2677_, 1, v___x_2675_);
lean_ctor_set(v___x_2677_, 2, v___x_2674_);
return v___x_2677_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg(lean_object* v_e_2678_, lean_object* v_fvarId_2679_, lean_object* v___y_2680_){
_start:
{
lean_object* v___x_2682_; uint8_t v_fst_2684_; lean_object* v_mctx_2685_; lean_object* v___y_2703_; lean_object* v_mctx_2708_; lean_object* v___f_2709_; lean_object* v___f_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; uint8_t v___x_2713_; 
v___x_2682_ = lean_st_ref_get(v___y_2680_);
v_mctx_2708_ = lean_ctor_get(v___x_2682_, 0);
lean_inc_ref_n(v_mctx_2708_, 2);
lean_dec(v___x_2682_);
v___f_2709_ = ((lean_object*)(l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__0));
v___f_2710_ = lean_alloc_closure((void*)(l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_2710_, 0, v_fvarId_2679_);
v___x_2711_ = lean_obj_once(&l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__3, &l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__3_once, _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__3);
v___x_2712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2712_, 0, v___x_2711_);
lean_ctor_set(v___x_2712_, 1, v_mctx_2708_);
v___x_2713_ = l_Lean_Expr_hasFVar(v_e_2678_);
if (v___x_2713_ == 0)
{
uint8_t v___x_2714_; 
v___x_2714_ = l_Lean_Expr_hasMVar(v_e_2678_);
if (v___x_2714_ == 0)
{
lean_dec_ref_known(v___x_2712_, 2);
lean_dec_ref(v___f_2710_);
lean_dec_ref(v_e_2678_);
v_fst_2684_ = v___x_2714_;
v_mctx_2685_ = v_mctx_2708_;
goto v___jp_2683_;
}
else
{
lean_object* v___x_2715_; 
lean_dec_ref(v_mctx_2708_);
v___x_2715_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2710_, v___f_2709_, v_e_2678_, v___x_2712_);
v___y_2703_ = v___x_2715_;
goto v___jp_2702_;
}
}
else
{
lean_object* v___x_2716_; 
lean_dec_ref(v_mctx_2708_);
v___x_2716_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2710_, v___f_2709_, v_e_2678_, v___x_2712_);
v___y_2703_ = v___x_2716_;
goto v___jp_2702_;
}
v___jp_2683_:
{
lean_object* v___x_2686_; lean_object* v_cache_2687_; lean_object* v_zetaDeltaFVarIds_2688_; lean_object* v_postponed_2689_; lean_object* v_diag_2690_; lean_object* v___x_2692_; uint8_t v_isShared_2693_; uint8_t v_isSharedCheck_2700_; 
v___x_2686_ = lean_st_ref_take(v___y_2680_);
v_cache_2687_ = lean_ctor_get(v___x_2686_, 1);
v_zetaDeltaFVarIds_2688_ = lean_ctor_get(v___x_2686_, 2);
v_postponed_2689_ = lean_ctor_get(v___x_2686_, 3);
v_diag_2690_ = lean_ctor_get(v___x_2686_, 4);
v_isSharedCheck_2700_ = !lean_is_exclusive(v___x_2686_);
if (v_isSharedCheck_2700_ == 0)
{
lean_object* v_unused_2701_; 
v_unused_2701_ = lean_ctor_get(v___x_2686_, 0);
lean_dec(v_unused_2701_);
v___x_2692_ = v___x_2686_;
v_isShared_2693_ = v_isSharedCheck_2700_;
goto v_resetjp_2691_;
}
else
{
lean_inc(v_diag_2690_);
lean_inc(v_postponed_2689_);
lean_inc(v_zetaDeltaFVarIds_2688_);
lean_inc(v_cache_2687_);
lean_dec(v___x_2686_);
v___x_2692_ = lean_box(0);
v_isShared_2693_ = v_isSharedCheck_2700_;
goto v_resetjp_2691_;
}
v_resetjp_2691_:
{
lean_object* v___x_2695_; 
if (v_isShared_2693_ == 0)
{
lean_ctor_set(v___x_2692_, 0, v_mctx_2685_);
v___x_2695_ = v___x_2692_;
goto v_reusejp_2694_;
}
else
{
lean_object* v_reuseFailAlloc_2699_; 
v_reuseFailAlloc_2699_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2699_, 0, v_mctx_2685_);
lean_ctor_set(v_reuseFailAlloc_2699_, 1, v_cache_2687_);
lean_ctor_set(v_reuseFailAlloc_2699_, 2, v_zetaDeltaFVarIds_2688_);
lean_ctor_set(v_reuseFailAlloc_2699_, 3, v_postponed_2689_);
lean_ctor_set(v_reuseFailAlloc_2699_, 4, v_diag_2690_);
v___x_2695_ = v_reuseFailAlloc_2699_;
goto v_reusejp_2694_;
}
v_reusejp_2694_:
{
lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; 
v___x_2696_ = lean_st_ref_put(v___y_2680_, v___x_2695_);
v___x_2697_ = lean_box(v_fst_2684_);
v___x_2698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2698_, 0, v___x_2697_);
return v___x_2698_;
}
}
}
v___jp_2702_:
{
lean_object* v_snd_2704_; lean_object* v_fst_2705_; lean_object* v_mctx_2706_; uint8_t v___x_2707_; 
v_snd_2704_ = lean_ctor_get(v___y_2703_, 1);
lean_inc(v_snd_2704_);
v_fst_2705_ = lean_ctor_get(v___y_2703_, 0);
lean_inc(v_fst_2705_);
lean_dec_ref(v___y_2703_);
v_mctx_2706_ = lean_ctor_get(v_snd_2704_, 1);
lean_inc_ref(v_mctx_2706_);
lean_dec(v_snd_2704_);
v___x_2707_ = lean_unbox(v_fst_2705_);
lean_dec(v_fst_2705_);
v_fst_2684_ = v___x_2707_;
v_mctx_2685_ = v_mctx_2706_;
goto v___jp_2683_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___redArg(lean_object* v_lctx_2849_, lean_object* v_localInsts_2850_, lean_object* v_x_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_){
_start:
{
lean_object* v___x_2857_; 
v___x_2857_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_2849_, v_localInsts_2850_, v_x_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_);
if (lean_obj_tag(v___x_2857_) == 0)
{
lean_object* v_a_2858_; lean_object* v___x_2860_; uint8_t v_isShared_2861_; uint8_t v_isSharedCheck_2865_; 
v_a_2858_ = lean_ctor_get(v___x_2857_, 0);
v_isSharedCheck_2865_ = !lean_is_exclusive(v___x_2857_);
if (v_isSharedCheck_2865_ == 0)
{
v___x_2860_ = v___x_2857_;
v_isShared_2861_ = v_isSharedCheck_2865_;
goto v_resetjp_2859_;
}
else
{
lean_inc(v_a_2858_);
lean_dec(v___x_2857_);
v___x_2860_ = lean_box(0);
v_isShared_2861_ = v_isSharedCheck_2865_;
goto v_resetjp_2859_;
}
v_resetjp_2859_:
{
lean_object* v___x_2863_; 
if (v_isShared_2861_ == 0)
{
v___x_2863_ = v___x_2860_;
goto v_reusejp_2862_;
}
else
{
lean_object* v_reuseFailAlloc_2864_; 
v_reuseFailAlloc_2864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2864_, 0, v_a_2858_);
v___x_2863_ = v_reuseFailAlloc_2864_;
goto v_reusejp_2862_;
}
v_reusejp_2862_:
{
return v___x_2863_;
}
}
}
else
{
lean_object* v_a_2866_; lean_object* v___x_2868_; uint8_t v_isShared_2869_; uint8_t v_isSharedCheck_2873_; 
v_a_2866_ = lean_ctor_get(v___x_2857_, 0);
v_isSharedCheck_2873_ = !lean_is_exclusive(v___x_2857_);
if (v_isSharedCheck_2873_ == 0)
{
v___x_2868_ = v___x_2857_;
v_isShared_2869_ = v_isSharedCheck_2873_;
goto v_resetjp_2867_;
}
else
{
lean_inc(v_a_2866_);
lean_dec(v___x_2857_);
v___x_2868_ = lean_box(0);
v_isShared_2869_ = v_isSharedCheck_2873_;
goto v_resetjp_2867_;
}
v_resetjp_2867_:
{
lean_object* v___x_2871_; 
if (v_isShared_2869_ == 0)
{
v___x_2871_ = v___x_2868_;
goto v_reusejp_2870_;
}
else
{
lean_object* v_reuseFailAlloc_2872_; 
v_reuseFailAlloc_2872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2872_, 0, v_a_2866_);
v___x_2871_ = v_reuseFailAlloc_2872_;
goto v_reusejp_2870_;
}
v_reusejp_2870_:
{
return v___x_2871_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___redArg___boxed(lean_object* v_lctx_2874_, lean_object* v_localInsts_2875_, lean_object* v_x_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_){
_start:
{
lean_object* v_res_2882_; 
v_res_2882_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___redArg(v_lctx_2874_, v_localInsts_2875_, v_x_2876_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec(v___y_2878_);
lean_dec_ref(v___y_2877_);
return v_res_2882_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__12(lean_object* v_as_2883_, size_t v_i_2884_, size_t v_stop_2885_, lean_object* v_b_2886_){
_start:
{
uint8_t v___x_2887_; 
v___x_2887_ = lean_usize_dec_eq(v_i_2884_, v_stop_2885_);
if (v___x_2887_ == 0)
{
lean_object* v___x_2888_; lean_object* v___x_2889_; size_t v___x_2890_; size_t v___x_2891_; 
v___x_2888_ = lean_array_uget_borrowed(v_as_2883_, v_i_2884_);
lean_inc(v___x_2888_);
v___x_2889_ = lean_local_ctx_erase(v_b_2886_, v___x_2888_);
v___x_2890_ = ((size_t)1ULL);
v___x_2891_ = lean_usize_add(v_i_2884_, v___x_2890_);
v_i_2884_ = v___x_2891_;
v_b_2886_ = v___x_2889_;
goto _start;
}
else
{
return v_b_2886_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__12___boxed(lean_object* v_as_2893_, lean_object* v_i_2894_, lean_object* v_stop_2895_, lean_object* v_b_2896_){
_start:
{
size_t v_i_boxed_2897_; size_t v_stop_boxed_2898_; lean_object* v_res_2899_; 
v_i_boxed_2897_ = lean_unbox_usize(v_i_2894_);
lean_dec(v_i_2894_);
v_stop_boxed_2898_ = lean_unbox_usize(v_stop_2895_);
lean_dec(v_stop_2895_);
v_res_2899_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__12(v_as_2893_, v_i_boxed_2897_, v_stop_boxed_2898_, v_b_2896_);
lean_dec_ref(v_as_2893_);
return v_res_2899_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9_spec__11(lean_object* v_a_2900_, lean_object* v_as_2901_, size_t v_i_2902_, size_t v_stop_2903_){
_start:
{
uint8_t v___x_2904_; 
v___x_2904_ = lean_usize_dec_eq(v_i_2902_, v_stop_2903_);
if (v___x_2904_ == 0)
{
lean_object* v___x_2905_; uint8_t v___x_2906_; 
v___x_2905_ = lean_array_uget_borrowed(v_as_2901_, v_i_2902_);
v___x_2906_ = l_Lean_instBEqFVarId_beq(v_a_2900_, v___x_2905_);
if (v___x_2906_ == 0)
{
size_t v___x_2907_; size_t v___x_2908_; 
v___x_2907_ = ((size_t)1ULL);
v___x_2908_ = lean_usize_add(v_i_2902_, v___x_2907_);
v_i_2902_ = v___x_2908_;
goto _start;
}
else
{
return v___x_2906_;
}
}
else
{
uint8_t v___x_2910_; 
v___x_2910_ = 0;
return v___x_2910_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9_spec__11___boxed(lean_object* v_a_2911_, lean_object* v_as_2912_, lean_object* v_i_2913_, lean_object* v_stop_2914_){
_start:
{
size_t v_i_boxed_2915_; size_t v_stop_boxed_2916_; uint8_t v_res_2917_; lean_object* v_r_2918_; 
v_i_boxed_2915_ = lean_unbox_usize(v_i_2913_);
lean_dec(v_i_2913_);
v_stop_boxed_2916_ = lean_unbox_usize(v_stop_2914_);
lean_dec(v_stop_2914_);
v_res_2917_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9_spec__11(v_a_2911_, v_as_2912_, v_i_boxed_2915_, v_stop_boxed_2916_);
lean_dec_ref(v_as_2912_);
lean_dec(v_a_2911_);
v_r_2918_ = lean_box(v_res_2917_);
return v_r_2918_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9(lean_object* v_as_2919_, lean_object* v_a_2920_){
_start:
{
lean_object* v___x_2921_; lean_object* v___x_2922_; uint8_t v___x_2923_; 
v___x_2921_ = lean_unsigned_to_nat(0u);
v___x_2922_ = lean_array_get_size(v_as_2919_);
v___x_2923_ = lean_nat_dec_lt(v___x_2921_, v___x_2922_);
if (v___x_2923_ == 0)
{
return v___x_2923_;
}
else
{
if (v___x_2923_ == 0)
{
return v___x_2923_;
}
else
{
size_t v___x_2924_; size_t v___x_2925_; uint8_t v___x_2926_; 
v___x_2924_ = ((size_t)0ULL);
v___x_2925_ = lean_usize_of_nat(v___x_2922_);
v___x_2926_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9_spec__11(v_a_2920_, v_as_2919_, v___x_2924_, v___x_2925_);
return v___x_2926_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9___boxed(lean_object* v_as_2927_, lean_object* v_a_2928_){
_start:
{
uint8_t v_res_2929_; lean_object* v_r_2930_; 
v_res_2929_ = l_Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9(v_as_2927_, v_a_2928_);
lean_dec(v_a_2928_);
lean_dec_ref(v_as_2927_);
v_r_2930_ = lean_box(v_res_2929_);
return v_r_2930_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__11(lean_object* v_fvarIds_2931_, lean_object* v_as_2932_, size_t v_i_2933_, size_t v_stop_2934_, lean_object* v_b_2935_){
_start:
{
lean_object* v___y_2937_; uint8_t v___x_2941_; 
v___x_2941_ = lean_usize_dec_eq(v_i_2933_, v_stop_2934_);
if (v___x_2941_ == 0)
{
lean_object* v___x_2942_; lean_object* v_fvar_2943_; lean_object* v___x_2944_; uint8_t v___x_2945_; 
v___x_2942_ = lean_array_uget_borrowed(v_as_2932_, v_i_2933_);
v_fvar_2943_ = lean_ctor_get(v___x_2942_, 1);
v___x_2944_ = l_Lean_Expr_fvarId_x21(v_fvar_2943_);
v___x_2945_ = l_Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9(v_fvarIds_2931_, v___x_2944_);
lean_dec(v___x_2944_);
if (v___x_2945_ == 0)
{
lean_object* v___x_2946_; 
lean_inc(v___x_2942_);
v___x_2946_ = lean_array_push(v_b_2935_, v___x_2942_);
v___y_2937_ = v___x_2946_;
goto v___jp_2936_;
}
else
{
v___y_2937_ = v_b_2935_;
goto v___jp_2936_;
}
}
else
{
return v_b_2935_;
}
v___jp_2936_:
{
size_t v___x_2938_; size_t v___x_2939_; 
v___x_2938_ = ((size_t)1ULL);
v___x_2939_ = lean_usize_add(v_i_2933_, v___x_2938_);
v_i_2933_ = v___x_2939_;
v_b_2935_ = v___y_2937_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__11___boxed(lean_object* v_fvarIds_2947_, lean_object* v_as_2948_, lean_object* v_i_2949_, lean_object* v_stop_2950_, lean_object* v_b_2951_){
_start:
{
size_t v_i_boxed_2952_; size_t v_stop_boxed_2953_; lean_object* v_res_2954_; 
v_i_boxed_2952_ = lean_unbox_usize(v_i_2949_);
lean_dec(v_i_2949_);
v_stop_boxed_2953_ = lean_unbox_usize(v_stop_2950_);
lean_dec(v_stop_2950_);
v_res_2954_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__11(v_fvarIds_2947_, v_as_2948_, v_i_boxed_2952_, v_stop_boxed_2953_, v_b_2951_);
lean_dec_ref(v_as_2948_);
lean_dec_ref(v_fvarIds_2947_);
return v_res_2954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___redArg(lean_object* v_fvarIds_2957_, lean_object* v_k_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_){
_start:
{
lean_object* v_lctx_2964_; lean_object* v_localInstances_2965_; lean_object* v___x_2966_; lean_object* v___y_2968_; lean_object* v___x_2983_; uint8_t v___x_2984_; 
v_lctx_2964_ = lean_ctor_get(v___y_2959_, 2);
v_localInstances_2965_ = lean_ctor_get(v___y_2959_, 3);
v___x_2966_ = lean_unsigned_to_nat(0u);
v___x_2983_ = lean_array_get_size(v_fvarIds_2957_);
v___x_2984_ = lean_nat_dec_lt(v___x_2966_, v___x_2983_);
if (v___x_2984_ == 0)
{
lean_inc_ref(v_lctx_2964_);
v___y_2968_ = v_lctx_2964_;
goto v___jp_2967_;
}
else
{
uint8_t v___x_2985_; 
v___x_2985_ = lean_nat_dec_le(v___x_2983_, v___x_2983_);
if (v___x_2985_ == 0)
{
if (v___x_2984_ == 0)
{
lean_inc_ref(v_lctx_2964_);
v___y_2968_ = v_lctx_2964_;
goto v___jp_2967_;
}
else
{
size_t v___x_2986_; size_t v___x_2987_; lean_object* v___x_2988_; 
v___x_2986_ = ((size_t)0ULL);
v___x_2987_ = lean_usize_of_nat(v___x_2983_);
lean_inc_ref(v_lctx_2964_);
v___x_2988_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__12(v_fvarIds_2957_, v___x_2986_, v___x_2987_, v_lctx_2964_);
v___y_2968_ = v___x_2988_;
goto v___jp_2967_;
}
}
else
{
size_t v___x_2989_; size_t v___x_2990_; lean_object* v___x_2991_; 
v___x_2989_ = ((size_t)0ULL);
v___x_2990_ = lean_usize_of_nat(v___x_2983_);
lean_inc_ref(v_lctx_2964_);
v___x_2991_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__12(v_fvarIds_2957_, v___x_2989_, v___x_2990_, v_lctx_2964_);
v___y_2968_ = v___x_2991_;
goto v___jp_2967_;
}
}
v___jp_2967_:
{
lean_object* v___x_2969_; lean_object* v___x_2970_; uint8_t v___x_2971_; 
v___x_2969_ = lean_array_get_size(v_localInstances_2965_);
v___x_2970_ = ((lean_object*)(l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___redArg___closed__0));
v___x_2971_ = lean_nat_dec_lt(v___x_2966_, v___x_2969_);
if (v___x_2971_ == 0)
{
lean_object* v___x_2972_; 
v___x_2972_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___redArg(v___y_2968_, v___x_2970_, v_k_2958_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_);
return v___x_2972_;
}
else
{
uint8_t v___x_2973_; 
v___x_2973_ = lean_nat_dec_le(v___x_2969_, v___x_2969_);
if (v___x_2973_ == 0)
{
if (v___x_2971_ == 0)
{
lean_object* v___x_2974_; 
v___x_2974_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___redArg(v___y_2968_, v___x_2970_, v_k_2958_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_);
return v___x_2974_;
}
else
{
size_t v___x_2975_; size_t v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; 
v___x_2975_ = ((size_t)0ULL);
v___x_2976_ = lean_usize_of_nat(v___x_2969_);
v___x_2977_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__11(v_fvarIds_2957_, v_localInstances_2965_, v___x_2975_, v___x_2976_, v___x_2970_);
v___x_2978_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___redArg(v___y_2968_, v___x_2977_, v_k_2958_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_);
return v___x_2978_;
}
}
else
{
size_t v___x_2979_; size_t v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; 
v___x_2979_ = ((size_t)0ULL);
v___x_2980_ = lean_usize_of_nat(v___x_2969_);
v___x_2981_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__11(v_fvarIds_2957_, v_localInstances_2965_, v___x_2979_, v___x_2980_, v___x_2970_);
v___x_2982_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___redArg(v___y_2968_, v___x_2981_, v_k_2958_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_);
return v___x_2982_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___redArg___boxed(lean_object* v_fvarIds_2992_, lean_object* v_k_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_){
_start:
{
lean_object* v_res_2999_; 
v_res_2999_ = l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___redArg(v_fvarIds_2992_, v_k_2993_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_);
lean_dec(v___y_2997_);
lean_dec_ref(v___y_2996_);
lean_dec(v___y_2995_);
lean_dec_ref(v___y_2994_);
lean_dec_ref(v_fvarIds_2992_);
return v_res_2999_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__3(size_t v_sz_3000_, size_t v_i_3001_, lean_object* v_bs_3002_){
_start:
{
uint8_t v___x_3003_; 
v___x_3003_ = lean_usize_dec_lt(v_i_3001_, v_sz_3000_);
if (v___x_3003_ == 0)
{
return v_bs_3002_;
}
else
{
lean_object* v_v_3004_; lean_object* v___x_3005_; lean_object* v_bs_x27_3006_; lean_object* v___x_3007_; size_t v___x_3008_; size_t v___x_3009_; lean_object* v___x_3010_; 
v_v_3004_ = lean_array_uget(v_bs_3002_, v_i_3001_);
v___x_3005_ = lean_unsigned_to_nat(0u);
v_bs_x27_3006_ = lean_array_uset(v_bs_3002_, v_i_3001_, v___x_3005_);
v___x_3007_ = l_Lean_Elab_Structural_RecArgInfo_indicesAndRecArgPos(v_v_3004_);
v___x_3008_ = ((size_t)1ULL);
v___x_3009_ = lean_usize_add(v_i_3001_, v___x_3008_);
v___x_3010_ = lean_array_uset(v_bs_x27_3006_, v_i_3001_, v___x_3007_);
v_i_3001_ = v___x_3009_;
v_bs_3002_ = v___x_3010_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__3___boxed(lean_object* v_sz_3012_, lean_object* v_i_3013_, lean_object* v_bs_3014_){
_start:
{
size_t v_sz_boxed_3015_; size_t v_i_boxed_3016_; lean_object* v_res_3017_; 
v_sz_boxed_3015_ = lean_unbox_usize(v_sz_3012_);
lean_dec(v_sz_3012_);
v_i_boxed_3016_ = lean_unbox_usize(v_i_3013_);
lean_dec(v_i_3013_);
v_res_3017_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__3(v_sz_boxed_3015_, v_i_boxed_3016_, v_bs_3014_);
return v_res_3017_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__14_spec__17_spec__21(lean_object* v_x_3018_, lean_object* v_x_3019_, lean_object* v_x_3020_){
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
lean_object* v___x_3028_; lean_object* v___x_3029_; 
v___x_3028_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(v_head_3021_);
v___x_3029_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3029_, 0, v___x_3027_);
lean_ctor_set(v___x_3029_, 1, v___x_3028_);
v_x_3019_ = v___x_3029_;
v_x_3020_ = v_tail_3022_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__14_spec__17(lean_object* v_x_3033_, lean_object* v_x_3034_, lean_object* v_x_3035_){
_start:
{
if (lean_obj_tag(v_x_3035_) == 0)
{
lean_dec(v_x_3033_);
return v_x_3034_;
}
else
{
lean_object* v_head_3036_; lean_object* v_tail_3037_; lean_object* v___x_3039_; uint8_t v_isShared_3040_; uint8_t v_isSharedCheck_3047_; 
v_head_3036_ = lean_ctor_get(v_x_3035_, 0);
v_tail_3037_ = lean_ctor_get(v_x_3035_, 1);
v_isSharedCheck_3047_ = !lean_is_exclusive(v_x_3035_);
if (v_isSharedCheck_3047_ == 0)
{
v___x_3039_ = v_x_3035_;
v_isShared_3040_ = v_isSharedCheck_3047_;
goto v_resetjp_3038_;
}
else
{
lean_inc(v_tail_3037_);
lean_inc(v_head_3036_);
lean_dec(v_x_3035_);
v___x_3039_ = lean_box(0);
v_isShared_3040_ = v_isSharedCheck_3047_;
goto v_resetjp_3038_;
}
v_resetjp_3038_:
{
lean_object* v___x_3042_; 
lean_inc(v_x_3033_);
if (v_isShared_3040_ == 0)
{
lean_ctor_set_tag(v___x_3039_, 5);
lean_ctor_set(v___x_3039_, 1, v_x_3033_);
lean_ctor_set(v___x_3039_, 0, v_x_3034_);
v___x_3042_ = v___x_3039_;
goto v_reusejp_3041_;
}
else
{
lean_object* v_reuseFailAlloc_3046_; 
v_reuseFailAlloc_3046_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3046_, 0, v_x_3034_);
lean_ctor_set(v_reuseFailAlloc_3046_, 1, v_x_3033_);
v___x_3042_ = v_reuseFailAlloc_3046_;
goto v_reusejp_3041_;
}
v_reusejp_3041_:
{
lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; 
v___x_3043_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(v_head_3036_);
v___x_3044_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3044_, 0, v___x_3042_);
lean_ctor_set(v___x_3044_, 1, v___x_3043_);
v___x_3045_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__14_spec__17_spec__21(v_x_3033_, v___x_3044_, v_tail_3037_);
return v___x_3045_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__14(lean_object* v_x_3048_, lean_object* v_x_3049_){
_start:
{
if (lean_obj_tag(v_x_3048_) == 0)
{
lean_object* v___x_3050_; 
lean_dec(v_x_3049_);
v___x_3050_ = lean_box(0);
return v___x_3050_;
}
else
{
lean_object* v_tail_3051_; 
v_tail_3051_ = lean_ctor_get(v_x_3048_, 1);
if (lean_obj_tag(v_tail_3051_) == 0)
{
lean_object* v_head_3052_; lean_object* v___x_3053_; 
lean_dec(v_x_3049_);
v_head_3052_ = lean_ctor_get(v_x_3048_, 0);
lean_inc(v_head_3052_);
lean_dec_ref_known(v_x_3048_, 2);
v___x_3053_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(v_head_3052_);
return v___x_3053_;
}
else
{
lean_object* v_head_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; 
lean_inc(v_tail_3051_);
v_head_3054_ = lean_ctor_get(v_x_3048_, 0);
lean_inc(v_head_3054_);
lean_dec_ref_known(v_x_3048_, 2);
v___x_3055_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(v_head_3054_);
v___x_3056_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__14_spec__17(v_x_3049_, v___x_3055_, v_tail_3051_);
return v___x_3056_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__5(void){
_start:
{
lean_object* v___x_3065_; lean_object* v___x_3066_; 
v___x_3065_ = ((lean_object*)(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__0));
v___x_3066_ = lean_string_length(v___x_3065_);
return v___x_3066_;
}
}
static lean_object* _init_l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__6(void){
_start:
{
lean_object* v___x_3067_; lean_object* v___x_3068_; 
v___x_3067_ = lean_obj_once(&l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__5, &l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__5_once, _init_l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__5);
v___x_3068_ = lean_nat_to_int(v___x_3067_);
return v___x_3068_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10(lean_object* v_xs_3076_){
_start:
{
lean_object* v___x_3077_; lean_object* v___x_3078_; uint8_t v___x_3079_; 
v___x_3077_ = lean_array_get_size(v_xs_3076_);
v___x_3078_ = lean_unsigned_to_nat(0u);
v___x_3079_ = lean_nat_dec_eq(v___x_3077_, v___x_3078_);
if (v___x_3079_ == 0)
{
lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; 
v___x_3080_ = lean_array_to_list(v_xs_3076_);
v___x_3081_ = ((lean_object*)(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__3));
v___x_3082_ = l_Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__14(v___x_3080_, v___x_3081_);
v___x_3083_ = lean_obj_once(&l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__6, &l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__6_once, _init_l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__6);
v___x_3084_ = ((lean_object*)(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__7));
v___x_3085_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3085_, 0, v___x_3084_);
lean_ctor_set(v___x_3085_, 1, v___x_3082_);
v___x_3086_ = ((lean_object*)(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__8));
v___x_3087_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3087_, 0, v___x_3085_);
lean_ctor_set(v___x_3087_, 1, v___x_3086_);
v___x_3088_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3088_, 0, v___x_3083_);
lean_ctor_set(v___x_3088_, 1, v___x_3087_);
v___x_3089_ = l_Std_Format_fill(v___x_3088_);
return v___x_3089_;
}
else
{
lean_object* v___x_3090_; 
lean_dec_ref(v_xs_3076_);
v___x_3090_ = ((lean_object*)(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__10));
return v___x_3090_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__11(size_t v_sz_3091_, size_t v_i_3092_, lean_object* v_bs_3093_){
_start:
{
uint8_t v___x_3094_; 
v___x_3094_ = lean_usize_dec_lt(v_i_3092_, v_sz_3091_);
if (v___x_3094_ == 0)
{
return v_bs_3093_;
}
else
{
lean_object* v_v_3095_; lean_object* v___x_3096_; lean_object* v_bs_x27_3097_; lean_object* v___x_3098_; size_t v___x_3099_; size_t v___x_3100_; lean_object* v___x_3101_; 
v_v_3095_ = lean_array_uget(v_bs_3093_, v_i_3092_);
v___x_3096_ = lean_unsigned_to_nat(0u);
v_bs_x27_3097_ = lean_array_uset(v_bs_3093_, v_i_3092_, v___x_3096_);
v___x_3098_ = l_Lean_mkFVar(v_v_3095_);
v___x_3099_ = ((size_t)1ULL);
v___x_3100_ = lean_usize_add(v_i_3092_, v___x_3099_);
v___x_3101_ = lean_array_uset(v_bs_x27_3097_, v_i_3092_, v___x_3098_);
v_i_3092_ = v___x_3100_;
v_bs_3093_ = v___x_3101_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__11___boxed(lean_object* v_sz_3103_, lean_object* v_i_3104_, lean_object* v_bs_3105_){
_start:
{
size_t v_sz_boxed_3106_; size_t v_i_boxed_3107_; lean_object* v_res_3108_; 
v_sz_boxed_3106_ = lean_unbox_usize(v_sz_3103_);
lean_dec(v_sz_3103_);
v_i_boxed_3107_ = lean_unbox_usize(v_i_3104_);
lean_dec(v_i_3104_);
v_res_3108_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__11(v_sz_boxed_3106_, v_i_boxed_3107_, v_bs_3105_);
return v_res_3108_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__2(size_t v_sz_3109_, size_t v_i_3110_, lean_object* v_bs_3111_){
_start:
{
uint8_t v___x_3112_; 
v___x_3112_ = lean_usize_dec_lt(v_i_3110_, v_sz_3109_);
if (v___x_3112_ == 0)
{
return v_bs_3111_;
}
else
{
lean_object* v_v_3113_; lean_object* v_recArgPos_3114_; lean_object* v___x_3115_; lean_object* v_bs_x27_3116_; size_t v___x_3117_; size_t v___x_3118_; lean_object* v___x_3119_; 
v_v_3113_ = lean_array_uget_borrowed(v_bs_3111_, v_i_3110_);
v_recArgPos_3114_ = lean_ctor_get(v_v_3113_, 2);
lean_inc(v_recArgPos_3114_);
v___x_3115_ = lean_unsigned_to_nat(0u);
v_bs_x27_3116_ = lean_array_uset(v_bs_3111_, v_i_3110_, v___x_3115_);
v___x_3117_ = ((size_t)1ULL);
v___x_3118_ = lean_usize_add(v_i_3110_, v___x_3117_);
v___x_3119_ = lean_array_uset(v_bs_x27_3116_, v_i_3110_, v_recArgPos_3114_);
v_i_3110_ = v___x_3118_;
v_bs_3111_ = v___x_3119_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__2___boxed(lean_object* v_sz_3121_, lean_object* v_i_3122_, lean_object* v_bs_3123_){
_start:
{
size_t v_sz_boxed_3124_; size_t v_i_boxed_3125_; lean_object* v_res_3126_; 
v_sz_boxed_3124_ = lean_unbox_usize(v_sz_3121_);
lean_dec(v_sz_3121_);
v_i_boxed_3125_ = lean_unbox_usize(v_i_3122_);
lean_dec(v_i_3122_);
v_res_3126_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__2(v_sz_boxed_3124_, v_i_boxed_3125_, v_bs_3123_);
return v_res_3126_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__1(void){
_start:
{
lean_object* v___x_3128_; lean_object* v___x_3129_; 
v___x_3128_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__0));
v___x_3129_ = l_Lean_stringToMessageData(v___x_3128_);
return v___x_3129_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__3(void){
_start:
{
lean_object* v___x_3131_; lean_object* v___x_3132_; 
v___x_3131_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__2));
v___x_3132_ = l_Lean_stringToMessageData(v___x_3131_);
return v___x_3132_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__5(void){
_start:
{
lean_object* v___x_3134_; lean_object* v___x_3135_; 
v___x_3134_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__4));
v___x_3135_ = l_Lean_stringToMessageData(v___x_3134_);
return v___x_3135_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6(lean_object* v_a_3136_, lean_object* v_as_3137_, size_t v_sz_3138_, size_t v_i_3139_, lean_object* v_b_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_){
_start:
{
lean_object* v_a_3147_; uint8_t v___x_3151_; 
v___x_3151_ = lean_usize_dec_lt(v_i_3139_, v_sz_3138_);
if (v___x_3151_ == 0)
{
lean_object* v___x_3152_; 
lean_dec_ref(v_a_3136_);
v___x_3152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3152_, 0, v_b_3140_);
return v___x_3152_;
}
else
{
lean_object* v_a_3153_; lean_object* v___x_3154_; 
v_a_3153_ = lean_array_uget_borrowed(v_as_3137_, v_i_3139_);
lean_inc(v_a_3153_);
lean_inc_ref(v_a_3136_);
v___x_3154_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg(v_a_3136_, v_a_3153_, v___y_3142_);
if (lean_obj_tag(v___x_3154_) == 0)
{
lean_object* v_a_3155_; lean_object* v___x_3156_; uint8_t v___x_3157_; 
v_a_3155_ = lean_ctor_get(v___x_3154_, 0);
lean_inc(v_a_3155_);
lean_dec_ref_known(v___x_3154_, 1);
v___x_3156_ = lean_box(0);
v___x_3157_ = lean_unbox(v_a_3155_);
lean_dec(v_a_3155_);
if (v___x_3157_ == 0)
{
v_a_3147_ = v___x_3156_;
goto v___jp_3146_;
}
else
{
uint8_t v___x_3158_; 
v___x_3158_ = l_Lean_Expr_isFVarOf(v_a_3136_, v_a_3153_);
if (v___x_3158_ == 0)
{
lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; 
v___x_3159_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__1);
lean_inc_ref(v_a_3136_);
v___x_3160_ = l_Lean_indentExpr(v_a_3136_);
v___x_3161_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3161_, 0, v___x_3159_);
lean_ctor_set(v___x_3161_, 1, v___x_3160_);
v___x_3162_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__3);
v___x_3163_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3163_, 0, v___x_3161_);
lean_ctor_set(v___x_3163_, 1, v___x_3162_);
lean_inc(v_a_3153_);
v___x_3164_ = l_Lean_mkFVar(v_a_3153_);
v___x_3165_ = l_Lean_indentExpr(v___x_3164_);
v___x_3166_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3166_, 0, v___x_3163_);
lean_ctor_set(v___x_3166_, 1, v___x_3165_);
v___x_3167_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__5);
v___x_3168_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3168_, 0, v___x_3166_);
lean_ctor_set(v___x_3168_, 1, v___x_3167_);
v___x_3169_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg(v___x_3168_, v___y_3141_, v___y_3142_, v___y_3143_, v___y_3144_);
if (lean_obj_tag(v___x_3169_) == 0)
{
lean_dec_ref_known(v___x_3169_, 1);
v_a_3147_ = v___x_3156_;
goto v___jp_3146_;
}
else
{
lean_dec_ref(v_a_3136_);
return v___x_3169_;
}
}
else
{
lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; 
v___x_3170_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__1);
lean_inc_ref(v_a_3136_);
v___x_3171_ = l_Lean_indentExpr(v_a_3136_);
v___x_3172_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3172_, 0, v___x_3170_);
lean_ctor_set(v___x_3172_, 1, v___x_3171_);
v___x_3173_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__5);
v___x_3174_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3174_, 0, v___x_3172_);
lean_ctor_set(v___x_3174_, 1, v___x_3173_);
v___x_3175_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg(v___x_3174_, v___y_3141_, v___y_3142_, v___y_3143_, v___y_3144_);
if (lean_obj_tag(v___x_3175_) == 0)
{
lean_dec_ref_known(v___x_3175_, 1);
v_a_3147_ = v___x_3156_;
goto v___jp_3146_;
}
else
{
lean_dec_ref(v_a_3136_);
return v___x_3175_;
}
}
}
}
else
{
lean_object* v_a_3176_; lean_object* v___x_3178_; uint8_t v_isShared_3179_; uint8_t v_isSharedCheck_3183_; 
lean_dec_ref(v_a_3136_);
v_a_3176_ = lean_ctor_get(v___x_3154_, 0);
v_isSharedCheck_3183_ = !lean_is_exclusive(v___x_3154_);
if (v_isSharedCheck_3183_ == 0)
{
v___x_3178_ = v___x_3154_;
v_isShared_3179_ = v_isSharedCheck_3183_;
goto v_resetjp_3177_;
}
else
{
lean_inc(v_a_3176_);
lean_dec(v___x_3154_);
v___x_3178_ = lean_box(0);
v_isShared_3179_ = v_isSharedCheck_3183_;
goto v_resetjp_3177_;
}
v_resetjp_3177_:
{
lean_object* v___x_3181_; 
if (v_isShared_3179_ == 0)
{
v___x_3181_ = v___x_3178_;
goto v_reusejp_3180_;
}
else
{
lean_object* v_reuseFailAlloc_3182_; 
v_reuseFailAlloc_3182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3182_, 0, v_a_3176_);
v___x_3181_ = v_reuseFailAlloc_3182_;
goto v_reusejp_3180_;
}
v_reusejp_3180_:
{
return v___x_3181_;
}
}
}
}
v___jp_3146_:
{
size_t v___x_3148_; size_t v___x_3149_; 
v___x_3148_ = ((size_t)1ULL);
v___x_3149_ = lean_usize_add(v_i_3139_, v___x_3148_);
v_i_3139_ = v___x_3149_;
v_b_3140_ = v_a_3147_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___boxed(lean_object* v_a_3184_, lean_object* v_as_3185_, lean_object* v_sz_3186_, lean_object* v_i_3187_, lean_object* v_b_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_){
_start:
{
size_t v_sz_boxed_3194_; size_t v_i_boxed_3195_; lean_object* v_res_3196_; 
v_sz_boxed_3194_ = lean_unbox_usize(v_sz_3186_);
lean_dec(v_sz_3186_);
v_i_boxed_3195_ = lean_unbox_usize(v_i_3187_);
lean_dec(v_i_3187_);
v_res_3196_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6(v_a_3184_, v_as_3185_, v_sz_boxed_3194_, v_i_boxed_3195_, v_b_3188_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_);
lean_dec(v___y_3192_);
lean_dec_ref(v___y_3191_);
lean_dec(v___y_3190_);
lean_dec_ref(v___y_3189_);
lean_dec_ref(v_as_3185_);
return v_res_3196_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7(lean_object* v_snd_3197_, lean_object* v_as_3198_, size_t v_sz_3199_, size_t v_i_3200_, lean_object* v_b_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_){
_start:
{
uint8_t v___x_3207_; 
v___x_3207_ = lean_usize_dec_lt(v_i_3200_, v_sz_3199_);
if (v___x_3207_ == 0)
{
lean_object* v___x_3208_; 
v___x_3208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3208_, 0, v_b_3201_);
return v___x_3208_;
}
else
{
lean_object* v___x_3209_; lean_object* v_a_3210_; size_t v_sz_3211_; size_t v___x_3212_; lean_object* v___x_3213_; 
v___x_3209_ = lean_box(0);
v_a_3210_ = lean_array_uget_borrowed(v_as_3198_, v_i_3200_);
v_sz_3211_ = lean_array_size(v_snd_3197_);
v___x_3212_ = ((size_t)0ULL);
lean_inc(v_a_3210_);
v___x_3213_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6(v_a_3210_, v_snd_3197_, v_sz_3211_, v___x_3212_, v___x_3209_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_);
if (lean_obj_tag(v___x_3213_) == 0)
{
size_t v___x_3214_; size_t v___x_3215_; 
lean_dec_ref_known(v___x_3213_, 1);
v___x_3214_ = ((size_t)1ULL);
v___x_3215_ = lean_usize_add(v_i_3200_, v___x_3214_);
v_i_3200_ = v___x_3215_;
v_b_3201_ = v___x_3209_;
goto _start;
}
else
{
return v___x_3213_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7___boxed(lean_object* v_snd_3217_, lean_object* v_as_3218_, lean_object* v_sz_3219_, lean_object* v_i_3220_, lean_object* v_b_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_){
_start:
{
size_t v_sz_boxed_3227_; size_t v_i_boxed_3228_; lean_object* v_res_3229_; 
v_sz_boxed_3227_ = lean_unbox_usize(v_sz_3219_);
lean_dec(v_sz_3219_);
v_i_boxed_3228_ = lean_unbox_usize(v_i_3220_);
lean_dec(v_i_3220_);
v_res_3229_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7(v_snd_3217_, v_as_3218_, v_sz_boxed_3227_, v_i_boxed_3228_, v_b_3221_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_);
lean_dec(v___y_3225_);
lean_dec_ref(v___y_3224_);
lean_dec(v___y_3223_);
lean_dec_ref(v___y_3222_);
lean_dec_ref(v_as_3218_);
lean_dec_ref(v_snd_3217_);
return v_res_3229_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8(lean_object* v_snd_3230_, lean_object* v_as_3231_, size_t v_sz_3232_, size_t v_i_3233_, lean_object* v_b_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_){
_start:
{
uint8_t v___x_3240_; 
v___x_3240_ = lean_usize_dec_lt(v_i_3233_, v_sz_3232_);
if (v___x_3240_ == 0)
{
lean_object* v___x_3241_; 
v___x_3241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3241_, 0, v_b_3234_);
return v___x_3241_;
}
else
{
lean_object* v_a_3242_; lean_object* v_indGroupInst_3243_; lean_object* v_params_3244_; lean_object* v___x_3245_; size_t v_sz_3246_; size_t v___x_3247_; lean_object* v___x_3248_; 
v_a_3242_ = lean_array_uget_borrowed(v_as_3231_, v_i_3233_);
v_indGroupInst_3243_ = lean_ctor_get(v_a_3242_, 4);
v_params_3244_ = lean_ctor_get(v_indGroupInst_3243_, 2);
v___x_3245_ = lean_box(0);
v_sz_3246_ = lean_array_size(v_params_3244_);
v___x_3247_ = ((size_t)0ULL);
v___x_3248_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7(v_snd_3230_, v_params_3244_, v_sz_3246_, v___x_3247_, v___x_3245_, v___y_3235_, v___y_3236_, v___y_3237_, v___y_3238_);
if (lean_obj_tag(v___x_3248_) == 0)
{
size_t v___x_3249_; size_t v___x_3250_; 
lean_dec_ref_known(v___x_3248_, 1);
v___x_3249_ = ((size_t)1ULL);
v___x_3250_ = lean_usize_add(v_i_3233_, v___x_3249_);
v_i_3233_ = v___x_3250_;
v_b_3234_ = v___x_3245_;
goto _start;
}
else
{
return v___x_3248_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8___boxed(lean_object* v_snd_3252_, lean_object* v_as_3253_, lean_object* v_sz_3254_, lean_object* v_i_3255_, lean_object* v_b_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_){
_start:
{
size_t v_sz_boxed_3262_; size_t v_i_boxed_3263_; lean_object* v_res_3264_; 
v_sz_boxed_3262_ = lean_unbox_usize(v_sz_3254_);
lean_dec(v_sz_3254_);
v_i_boxed_3263_ = lean_unbox_usize(v_i_3255_);
lean_dec(v_i_3255_);
v_res_3264_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8(v_snd_3252_, v_as_3253_, v_sz_boxed_3262_, v_i_boxed_3263_, v_b_3256_, v___y_3257_, v___y_3258_, v___y_3259_, v___y_3260_);
lean_dec(v___y_3260_);
lean_dec_ref(v___y_3259_);
lean_dec(v___y_3258_);
lean_dec_ref(v___y_3257_);
lean_dec_ref(v_as_3253_);
lean_dec_ref(v_snd_3252_);
return v_res_3264_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg(lean_object* v_fst_3265_, size_t v_sz_3266_, size_t v_i_3267_, lean_object* v_bs_3268_){
_start:
{
uint8_t v___x_3269_; 
v___x_3269_ = lean_usize_dec_lt(v_i_3267_, v_sz_3266_);
if (v___x_3269_ == 0)
{
return v_bs_3268_;
}
else
{
lean_object* v_v_3270_; lean_object* v_fnName_3271_; lean_object* v_recArgPos_3272_; lean_object* v_indicesPos_3273_; lean_object* v_indGroupInst_3274_; lean_object* v_indIdx_3275_; lean_object* v___x_3277_; uint8_t v_isShared_3278_; uint8_t v_isSharedCheck_3292_; 
v_v_3270_ = lean_array_uget(v_bs_3268_, v_i_3267_);
v_fnName_3271_ = lean_ctor_get(v_v_3270_, 0);
v_recArgPos_3272_ = lean_ctor_get(v_v_3270_, 2);
v_indicesPos_3273_ = lean_ctor_get(v_v_3270_, 3);
v_indGroupInst_3274_ = lean_ctor_get(v_v_3270_, 4);
v_indIdx_3275_ = lean_ctor_get(v_v_3270_, 5);
v_isSharedCheck_3292_ = !lean_is_exclusive(v_v_3270_);
if (v_isSharedCheck_3292_ == 0)
{
lean_object* v_unused_3293_; 
v_unused_3293_ = lean_ctor_get(v_v_3270_, 1);
lean_dec(v_unused_3293_);
v___x_3277_ = v_v_3270_;
v_isShared_3278_ = v_isSharedCheck_3292_;
goto v_resetjp_3276_;
}
else
{
lean_inc(v_indIdx_3275_);
lean_inc(v_indGroupInst_3274_);
lean_inc(v_indicesPos_3273_);
lean_inc(v_recArgPos_3272_);
lean_inc(v_fnName_3271_);
lean_dec(v_v_3270_);
v___x_3277_ = lean_box(0);
v_isShared_3278_ = v_isSharedCheck_3292_;
goto v_resetjp_3276_;
}
v_resetjp_3276_:
{
lean_object* v_perms_3279_; lean_object* v___x_3280_; lean_object* v_bs_x27_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3286_; 
v_perms_3279_ = lean_ctor_get(v_fst_3265_, 1);
v___x_3280_ = lean_unsigned_to_nat(0u);
v_bs_x27_3281_ = lean_array_uset(v_bs_3268_, v_i_3267_, v___x_3280_);
v___x_3282_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0);
v___x_3283_ = lean_usize_to_nat(v_i_3267_);
v___x_3284_ = lean_array_get_borrowed(v___x_3282_, v_perms_3279_, v___x_3283_);
lean_dec(v___x_3283_);
lean_inc(v___x_3284_);
if (v_isShared_3278_ == 0)
{
lean_ctor_set(v___x_3277_, 1, v___x_3284_);
v___x_3286_ = v___x_3277_;
goto v_reusejp_3285_;
}
else
{
lean_object* v_reuseFailAlloc_3291_; 
v_reuseFailAlloc_3291_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3291_, 0, v_fnName_3271_);
lean_ctor_set(v_reuseFailAlloc_3291_, 1, v___x_3284_);
lean_ctor_set(v_reuseFailAlloc_3291_, 2, v_recArgPos_3272_);
lean_ctor_set(v_reuseFailAlloc_3291_, 3, v_indicesPos_3273_);
lean_ctor_set(v_reuseFailAlloc_3291_, 4, v_indGroupInst_3274_);
lean_ctor_set(v_reuseFailAlloc_3291_, 5, v_indIdx_3275_);
v___x_3286_ = v_reuseFailAlloc_3291_;
goto v_reusejp_3285_;
}
v_reusejp_3285_:
{
size_t v___x_3287_; size_t v___x_3288_; lean_object* v___x_3289_; 
v___x_3287_ = ((size_t)1ULL);
v___x_3288_ = lean_usize_add(v_i_3267_, v___x_3287_);
v___x_3289_ = lean_array_uset(v_bs_x27_3281_, v_i_3267_, v___x_3286_);
v_i_3267_ = v___x_3288_;
v_bs_3268_ = v___x_3289_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg___boxed(lean_object* v_fst_3294_, lean_object* v_sz_3295_, lean_object* v_i_3296_, lean_object* v_bs_3297_){
_start:
{
size_t v_sz_boxed_3298_; size_t v_i_boxed_3299_; lean_object* v_res_3300_; 
v_sz_boxed_3298_ = lean_unbox_usize(v_sz_3295_);
lean_dec(v_sz_3295_);
v_i_boxed_3299_ = lean_unbox_usize(v_i_3296_);
lean_dec(v_i_3296_);
v_res_3300_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg(v_fst_3294_, v_sz_boxed_3298_, v_i_boxed_3299_, v_bs_3297_);
lean_dec_ref(v_fst_3294_);
return v_res_3300_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__0(void){
_start:
{
lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; 
v___x_3301_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__3));
v___x_3302_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0___closed__1));
v___x_3303_ = l_Lean_Name_append(v___x_3302_, v___x_3301_);
return v___x_3303_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3305_; lean_object* v___x_3306_; 
v___x_3305_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__1));
v___x_3306_ = l_Lean_stringToMessageData(v___x_3305_);
return v___x_3306_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__4(void){
_start:
{
lean_object* v___x_3308_; lean_object* v___x_3309_; 
v___x_3308_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__3));
v___x_3309_ = l_Lean_stringToMessageData(v___x_3308_);
return v___x_3309_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__6(void){
_start:
{
lean_object* v___x_3311_; lean_object* v___x_3312_; 
v___x_3311_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__5));
v___x_3312_ = l_Lean_stringToMessageData(v___x_3311_);
return v___x_3312_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__8(void){
_start:
{
lean_object* v___x_3314_; lean_object* v___x_3315_; 
v___x_3314_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__7));
v___x_3315_ = l_Lean_stringToMessageData(v___x_3314_);
return v___x_3315_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__10(void){
_start:
{
lean_object* v___x_3317_; lean_object* v___x_3318_; 
v___x_3317_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__9));
v___x_3318_ = l_Lean_stringToMessageData(v___x_3317_);
return v___x_3318_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0(size_t v___x_3319_, lean_object* v_a_3320_, lean_object* v_xs_3321_, lean_object* v_a_3322_, lean_object* v_recArgInfos_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_){
_start:
{
lean_object* v___y_3330_; lean_object* v___y_3331_; lean_object* v___y_3332_; lean_object* v___y_3333_; lean_object* v___y_3334_; lean_object* v___y_3335_; lean_object* v___y_3336_; lean_object* v___x_3349_; lean_object* v___y_3351_; lean_object* v___y_3352_; lean_object* v___y_3353_; lean_object* v___y_3354_; lean_object* v___y_3355_; lean_object* v___y_3356_; lean_object* v___y_3357_; lean_object* v___x_3376_; lean_object* v_a_3377_; size_t v_sz_3378_; lean_object* v___x_3379_; lean_object* v___y_3381_; lean_object* v___y_3382_; lean_object* v___y_3383_; lean_object* v___y_3384_; uint8_t v___x_3441_; 
v___x_3349_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__3));
v___x_3376_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0(v___x_3349_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_);
v_a_3377_ = lean_ctor_get(v___x_3376_, 0);
lean_inc(v_a_3377_);
lean_dec_ref(v___x_3376_);
v_sz_3378_ = lean_array_size(v_recArgInfos_3323_);
lean_inc_ref(v_recArgInfos_3323_);
v___x_3379_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__2(v_sz_3378_, v___x_3319_, v_recArgInfos_3323_);
v___x_3441_ = lean_unbox(v_a_3377_);
lean_dec(v_a_3377_);
if (v___x_3441_ == 0)
{
v___y_3381_ = v___y_3324_;
v___y_3382_ = v___y_3325_;
v___y_3383_ = v___y_3326_;
v___y_3384_ = v___y_3327_;
goto v___jp_3380_;
}
else
{
lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; 
v___x_3442_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__10, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__10);
lean_inc_ref(v___x_3379_);
v___x_3443_ = lean_array_to_list(v___x_3379_);
v___x_3444_ = lean_box(0);
v___x_3445_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__0(v___x_3443_, v___x_3444_);
v___x_3446_ = l_Lean_MessageData_ofList(v___x_3445_);
v___x_3447_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3447_, 0, v___x_3442_);
lean_ctor_set(v___x_3447_, 1, v___x_3446_);
v___x_3448_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_3349_, v___x_3447_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_);
if (lean_obj_tag(v___x_3448_) == 0)
{
lean_dec_ref_known(v___x_3448_, 1);
v___y_3381_ = v___y_3324_;
v___y_3382_ = v___y_3325_;
v___y_3383_ = v___y_3326_;
v___y_3384_ = v___y_3327_;
goto v___jp_3380_;
}
else
{
lean_object* v_a_3449_; lean_object* v___x_3451_; uint8_t v_isShared_3452_; uint8_t v_isSharedCheck_3456_; 
lean_dec_ref(v___x_3379_);
lean_dec_ref(v_recArgInfos_3323_);
lean_dec_ref(v_a_3322_);
lean_dec_ref(v_xs_3321_);
lean_dec_ref(v_a_3320_);
v_a_3449_ = lean_ctor_get(v___x_3448_, 0);
v_isSharedCheck_3456_ = !lean_is_exclusive(v___x_3448_);
if (v_isSharedCheck_3456_ == 0)
{
v___x_3451_ = v___x_3448_;
v_isShared_3452_ = v_isSharedCheck_3456_;
goto v_resetjp_3450_;
}
else
{
lean_inc(v_a_3449_);
lean_dec(v___x_3448_);
v___x_3451_ = lean_box(0);
v_isShared_3452_ = v_isSharedCheck_3456_;
goto v_resetjp_3450_;
}
v_resetjp_3450_:
{
lean_object* v___x_3454_; 
if (v_isShared_3452_ == 0)
{
v___x_3454_ = v___x_3451_;
goto v_reusejp_3453_;
}
else
{
lean_object* v_reuseFailAlloc_3455_; 
v_reuseFailAlloc_3455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3455_, 0, v_a_3449_);
v___x_3454_ = v_reuseFailAlloc_3455_;
goto v_reusejp_3453_;
}
v_reusejp_3453_:
{
return v___x_3454_;
}
}
}
}
v___jp_3329_:
{
lean_object* v___x_3337_; size_t v_sz_3338_; lean_object* v___x_3339_; 
v___x_3337_ = lean_box(0);
v_sz_3338_ = lean_array_size(v___y_3331_);
v___x_3339_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8(v___y_3330_, v___y_3331_, v_sz_3338_, v___x_3319_, v___x_3337_, v___y_3333_, v___y_3334_, v___y_3335_, v___y_3336_);
lean_dec_ref(v___y_3331_);
if (lean_obj_tag(v___x_3339_) == 0)
{
lean_object* v___x_3340_; 
lean_dec_ref_known(v___x_3339_, 1);
v___x_3340_ = l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___redArg(v___y_3330_, v___y_3332_, v___y_3333_, v___y_3334_, v___y_3335_, v___y_3336_);
lean_dec_ref(v___y_3330_);
return v___x_3340_;
}
else
{
lean_object* v_a_3341_; lean_object* v___x_3343_; uint8_t v_isShared_3344_; uint8_t v_isSharedCheck_3348_; 
lean_dec_ref(v___y_3332_);
lean_dec_ref(v___y_3330_);
v_a_3341_ = lean_ctor_get(v___x_3339_, 0);
v_isSharedCheck_3348_ = !lean_is_exclusive(v___x_3339_);
if (v_isSharedCheck_3348_ == 0)
{
v___x_3343_ = v___x_3339_;
v_isShared_3344_ = v_isSharedCheck_3348_;
goto v_resetjp_3342_;
}
else
{
lean_inc(v_a_3341_);
lean_dec(v___x_3339_);
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
v___jp_3350_:
{
lean_object* v_options_3358_; uint8_t v_hasTrace_3359_; 
v_options_3358_ = lean_ctor_get(v___y_3356_, 2);
v_hasTrace_3359_ = lean_ctor_get_uint8(v_options_3358_, sizeof(void*)*1);
if (v_hasTrace_3359_ == 0)
{
v___y_3330_ = v___y_3351_;
v___y_3331_ = v___y_3352_;
v___y_3332_ = v___y_3353_;
v___y_3333_ = v___y_3354_;
v___y_3334_ = v___y_3355_;
v___y_3335_ = v___y_3356_;
v___y_3336_ = v___y_3357_;
goto v___jp_3329_;
}
else
{
lean_object* v_inheritedTraceOptions_3360_; lean_object* v___x_3361_; uint8_t v___x_3362_; 
v_inheritedTraceOptions_3360_ = lean_ctor_get(v___y_3356_, 13);
v___x_3361_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__0);
v___x_3362_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3360_, v_options_3358_, v___x_3361_);
if (v___x_3362_ == 0)
{
v___y_3330_ = v___y_3351_;
v___y_3331_ = v___y_3352_;
v___y_3332_ = v___y_3353_;
v___y_3333_ = v___y_3354_;
v___y_3334_ = v___y_3355_;
v___y_3335_ = v___y_3356_;
v___y_3336_ = v___y_3357_;
goto v___jp_3329_;
}
else
{
lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; 
v___x_3363_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__2);
lean_inc_ref(v___y_3352_);
v___x_3364_ = l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10(v___y_3352_);
v___x_3365_ = l_Lean_MessageData_ofFormat(v___x_3364_);
v___x_3366_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3366_, 0, v___x_3363_);
lean_ctor_set(v___x_3366_, 1, v___x_3365_);
v___x_3367_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_3349_, v___x_3366_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_);
if (lean_obj_tag(v___x_3367_) == 0)
{
lean_dec_ref_known(v___x_3367_, 1);
v___y_3330_ = v___y_3351_;
v___y_3331_ = v___y_3352_;
v___y_3332_ = v___y_3353_;
v___y_3333_ = v___y_3354_;
v___y_3334_ = v___y_3355_;
v___y_3335_ = v___y_3356_;
v___y_3336_ = v___y_3357_;
goto v___jp_3329_;
}
else
{
lean_object* v_a_3368_; lean_object* v___x_3370_; uint8_t v_isShared_3371_; uint8_t v_isSharedCheck_3375_; 
lean_dec_ref(v___y_3353_);
lean_dec_ref(v___y_3352_);
lean_dec_ref(v___y_3351_);
v_a_3368_ = lean_ctor_get(v___x_3367_, 0);
v_isSharedCheck_3375_ = !lean_is_exclusive(v___x_3367_);
if (v_isSharedCheck_3375_ == 0)
{
v___x_3370_ = v___x_3367_;
v_isShared_3371_ = v_isSharedCheck_3375_;
goto v_resetjp_3369_;
}
else
{
lean_inc(v_a_3368_);
lean_dec(v___x_3367_);
v___x_3370_ = lean_box(0);
v_isShared_3371_ = v_isSharedCheck_3375_;
goto v_resetjp_3369_;
}
v_resetjp_3369_:
{
lean_object* v___x_3373_; 
if (v_isShared_3371_ == 0)
{
v___x_3373_ = v___x_3370_;
goto v_reusejp_3372_;
}
else
{
lean_object* v_reuseFailAlloc_3374_; 
v_reuseFailAlloc_3374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3374_, 0, v_a_3368_);
v___x_3373_ = v_reuseFailAlloc_3374_;
goto v_reusejp_3372_;
}
v_reusejp_3372_:
{
return v___x_3373_;
}
}
}
}
}
}
v___jp_3380_:
{
lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v_snd_3387_; lean_object* v_fst_3388_; lean_object* v___x_3390_; uint8_t v_isShared_3391_; uint8_t v_isSharedCheck_3440_; 
lean_inc_ref(v_recArgInfos_3323_);
v___x_3385_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__3(v_sz_3378_, v___x_3319_, v_recArgInfos_3323_);
lean_inc_ref(v_xs_3321_);
v___x_3386_ = l_Lean_Elab_FixedParamPerms_erase(v_a_3320_, v_xs_3321_, v___x_3385_);
v_snd_3387_ = lean_ctor_get(v___x_3386_, 1);
v_fst_3388_ = lean_ctor_get(v___x_3386_, 0);
v_isSharedCheck_3440_ = !lean_is_exclusive(v___x_3386_);
if (v_isSharedCheck_3440_ == 0)
{
v___x_3390_ = v___x_3386_;
v_isShared_3391_ = v_isSharedCheck_3440_;
goto v_resetjp_3389_;
}
else
{
lean_inc(v_snd_3387_);
lean_inc(v_fst_3388_);
lean_dec(v___x_3386_);
v___x_3390_ = lean_box(0);
v_isShared_3391_ = v_isSharedCheck_3440_;
goto v_resetjp_3389_;
}
v_resetjp_3389_:
{
lean_object* v_fst_3392_; lean_object* v_snd_3393_; lean_object* v___x_3395_; uint8_t v_isShared_3396_; uint8_t v_isSharedCheck_3439_; 
v_fst_3392_ = lean_ctor_get(v_snd_3387_, 0);
v_snd_3393_ = lean_ctor_get(v_snd_3387_, 1);
v_isSharedCheck_3439_ = !lean_is_exclusive(v_snd_3387_);
if (v_isSharedCheck_3439_ == 0)
{
v___x_3395_ = v_snd_3387_;
v_isShared_3396_ = v_isSharedCheck_3439_;
goto v_resetjp_3394_;
}
else
{
lean_inc(v_snd_3393_);
lean_inc(v_fst_3392_);
lean_dec(v_snd_3387_);
v___x_3395_ = lean_box(0);
v_isShared_3396_ = v_isSharedCheck_3439_;
goto v_resetjp_3394_;
}
v_resetjp_3394_:
{
lean_object* v___x_3397_; lean_object* v___f_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; uint8_t v___x_3401_; 
v___x_3397_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg(v_fst_3388_, v_sz_3378_, v___x_3319_, v_recArgInfos_3323_);
lean_inc_ref(v___x_3397_);
lean_inc(v_fst_3392_);
v___f_3398_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___boxed), 10, 5);
lean_closure_set(v___f_3398_, 0, v_a_3322_);
lean_closure_set(v___f_3398_, 1, v_fst_3388_);
lean_closure_set(v___f_3398_, 2, v_fst_3392_);
lean_closure_set(v___f_3398_, 3, v___x_3397_);
lean_closure_set(v___f_3398_, 4, v___x_3379_);
v___x_3399_ = lean_array_get_size(v_fst_3392_);
v___x_3400_ = lean_array_get_size(v_xs_3321_);
v___x_3401_ = lean_nat_dec_eq(v___x_3399_, v___x_3400_);
if (v___x_3401_ == 0)
{
lean_object* v___x_3402_; lean_object* v_a_3403_; uint8_t v___x_3404_; 
v___x_3402_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0(v___x_3349_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_);
v_a_3403_ = lean_ctor_get(v___x_3402_, 0);
lean_inc(v_a_3403_);
lean_dec_ref(v___x_3402_);
v___x_3404_ = lean_unbox(v_a_3403_);
lean_dec(v_a_3403_);
if (v___x_3404_ == 0)
{
lean_del_object(v___x_3395_);
lean_dec(v_fst_3392_);
lean_del_object(v___x_3390_);
lean_dec_ref(v_xs_3321_);
v___y_3351_ = v_snd_3393_;
v___y_3352_ = v___x_3397_;
v___y_3353_ = v___f_3398_;
v___y_3354_ = v___y_3381_;
v___y_3355_ = v___y_3382_;
v___y_3356_ = v___y_3383_;
v___y_3357_ = v___y_3384_;
goto v___jp_3350_;
}
else
{
lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3411_; 
v___x_3405_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__4);
v___x_3406_ = lean_array_to_list(v_xs_3321_);
v___x_3407_ = lean_box(0);
v___x_3408_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_3406_, v___x_3407_);
v___x_3409_ = l_Lean_MessageData_ofList(v___x_3408_);
if (v_isShared_3396_ == 0)
{
lean_ctor_set_tag(v___x_3395_, 7);
lean_ctor_set(v___x_3395_, 1, v___x_3409_);
lean_ctor_set(v___x_3395_, 0, v___x_3405_);
v___x_3411_ = v___x_3395_;
goto v_reusejp_3410_;
}
else
{
lean_object* v_reuseFailAlloc_3437_; 
v_reuseFailAlloc_3437_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3437_, 0, v___x_3405_);
lean_ctor_set(v_reuseFailAlloc_3437_, 1, v___x_3409_);
v___x_3411_ = v_reuseFailAlloc_3437_;
goto v_reusejp_3410_;
}
v_reusejp_3410_:
{
lean_object* v___x_3412_; lean_object* v___x_3414_; 
v___x_3412_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__6, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__6);
if (v_isShared_3391_ == 0)
{
lean_ctor_set_tag(v___x_3390_, 7);
lean_ctor_set(v___x_3390_, 1, v___x_3412_);
lean_ctor_set(v___x_3390_, 0, v___x_3411_);
v___x_3414_ = v___x_3390_;
goto v_reusejp_3413_;
}
else
{
lean_object* v_reuseFailAlloc_3436_; 
v_reuseFailAlloc_3436_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3436_, 0, v___x_3411_);
lean_ctor_set(v_reuseFailAlloc_3436_, 1, v___x_3412_);
v___x_3414_ = v_reuseFailAlloc_3436_;
goto v_reusejp_3413_;
}
v_reusejp_3413_:
{
lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; size_t v_sz_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; 
v___x_3415_ = lean_array_to_list(v_fst_3392_);
v___x_3416_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_3415_, v___x_3407_);
v___x_3417_ = l_Lean_MessageData_ofList(v___x_3416_);
v___x_3418_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3418_, 0, v___x_3414_);
lean_ctor_set(v___x_3418_, 1, v___x_3417_);
v___x_3419_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__8);
v___x_3420_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3420_, 0, v___x_3418_);
lean_ctor_set(v___x_3420_, 1, v___x_3419_);
v_sz_3421_ = lean_array_size(v_snd_3393_);
lean_inc(v_snd_3393_);
v___x_3422_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__11(v_sz_3421_, v___x_3319_, v_snd_3393_);
v___x_3423_ = lean_array_to_list(v___x_3422_);
v___x_3424_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_3423_, v___x_3407_);
v___x_3425_ = l_Lean_MessageData_ofList(v___x_3424_);
v___x_3426_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3426_, 0, v___x_3420_);
lean_ctor_set(v___x_3426_, 1, v___x_3425_);
v___x_3427_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_3349_, v___x_3426_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_);
if (lean_obj_tag(v___x_3427_) == 0)
{
lean_dec_ref_known(v___x_3427_, 1);
v___y_3351_ = v_snd_3393_;
v___y_3352_ = v___x_3397_;
v___y_3353_ = v___f_3398_;
v___y_3354_ = v___y_3381_;
v___y_3355_ = v___y_3382_;
v___y_3356_ = v___y_3383_;
v___y_3357_ = v___y_3384_;
goto v___jp_3350_;
}
else
{
lean_object* v_a_3428_; lean_object* v___x_3430_; uint8_t v_isShared_3431_; uint8_t v_isSharedCheck_3435_; 
lean_dec_ref(v___f_3398_);
lean_dec_ref(v___x_3397_);
lean_dec(v_snd_3393_);
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
}
}
}
else
{
lean_object* v___x_3438_; 
lean_dec_ref(v___x_3397_);
lean_del_object(v___x_3395_);
lean_dec(v_fst_3392_);
lean_del_object(v___x_3390_);
lean_dec_ref(v_xs_3321_);
v___x_3438_ = l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___redArg(v_snd_3393_, v___f_3398_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_);
lean_dec(v_snd_3393_);
return v___x_3438_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___boxed(lean_object* v___x_3457_, lean_object* v_a_3458_, lean_object* v_xs_3459_, lean_object* v_a_3460_, lean_object* v_recArgInfos_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_){
_start:
{
size_t v___x_15785__boxed_3467_; lean_object* v_res_3468_; 
v___x_15785__boxed_3467_ = lean_unbox_usize(v___x_3457_);
lean_dec(v___x_3457_);
v_res_3468_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0(v___x_15785__boxed_3467_, v_a_3458_, v_xs_3459_, v_a_3460_, v_recArgInfos_3461_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_);
lean_dec(v___y_3465_);
lean_dec_ref(v___y_3464_);
lean_dec(v___y_3463_);
lean_dec_ref(v___y_3462_);
return v_res_3468_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg(lean_object* v___x_3469_, lean_object* v_xs_3470_, size_t v_sz_3471_, size_t v_i_3472_, lean_object* v_bs_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_){
_start:
{
uint8_t v___x_3479_; 
v___x_3479_ = lean_usize_dec_lt(v_i_3472_, v_sz_3471_);
if (v___x_3479_ == 0)
{
lean_object* v___x_3480_; 
lean_dec_ref(v_xs_3470_);
v___x_3480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3480_, 0, v_bs_3473_);
return v___x_3480_;
}
else
{
lean_object* v_v_3481_; lean_object* v_value_3482_; lean_object* v___x_3483_; lean_object* v_bs_x27_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; 
v_v_3481_ = lean_array_uget_borrowed(v_bs_3473_, v_i_3472_);
v_value_3482_ = lean_ctor_get(v_v_3481_, 7);
lean_inc_ref(v_value_3482_);
v___x_3483_ = lean_unsigned_to_nat(0u);
v_bs_x27_3484_ = lean_array_uset(v_bs_3473_, v_i_3472_, v___x_3483_);
v___x_3485_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0);
v___x_3486_ = lean_usize_to_nat(v_i_3472_);
v___x_3487_ = lean_array_get_borrowed(v___x_3485_, v___x_3469_, v___x_3486_);
lean_dec(v___x_3486_);
lean_inc_ref(v_xs_3470_);
lean_inc(v___x_3487_);
v___x_3488_ = l_Lean_Elab_FixedParamPerm_instantiateLambda(v___x_3487_, v_value_3482_, v_xs_3470_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_);
if (lean_obj_tag(v___x_3488_) == 0)
{
lean_object* v_a_3489_; size_t v___x_3490_; size_t v___x_3491_; lean_object* v___x_3492_; 
v_a_3489_ = lean_ctor_get(v___x_3488_, 0);
lean_inc(v_a_3489_);
lean_dec_ref_known(v___x_3488_, 1);
v___x_3490_ = ((size_t)1ULL);
v___x_3491_ = lean_usize_add(v_i_3472_, v___x_3490_);
v___x_3492_ = lean_array_uset(v_bs_x27_3484_, v_i_3472_, v_a_3489_);
v_i_3472_ = v___x_3491_;
v_bs_3473_ = v___x_3492_;
goto _start;
}
else
{
lean_object* v_a_3494_; lean_object* v___x_3496_; uint8_t v_isShared_3497_; uint8_t v_isSharedCheck_3501_; 
lean_dec_ref(v_bs_x27_3484_);
lean_dec_ref(v_xs_3470_);
v_a_3494_ = lean_ctor_get(v___x_3488_, 0);
v_isSharedCheck_3501_ = !lean_is_exclusive(v___x_3488_);
if (v_isSharedCheck_3501_ == 0)
{
v___x_3496_ = v___x_3488_;
v_isShared_3497_ = v_isSharedCheck_3501_;
goto v_resetjp_3495_;
}
else
{
lean_inc(v_a_3494_);
lean_dec(v___x_3488_);
v___x_3496_ = lean_box(0);
v_isShared_3497_ = v_isSharedCheck_3501_;
goto v_resetjp_3495_;
}
v_resetjp_3495_:
{
lean_object* v___x_3499_; 
if (v_isShared_3497_ == 0)
{
v___x_3499_ = v___x_3496_;
goto v_reusejp_3498_;
}
else
{
lean_object* v_reuseFailAlloc_3500_; 
v_reuseFailAlloc_3500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3500_, 0, v_a_3494_);
v___x_3499_ = v_reuseFailAlloc_3500_;
goto v_reusejp_3498_;
}
v_reusejp_3498_:
{
return v___x_3499_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg___boxed(lean_object* v___x_3502_, lean_object* v_xs_3503_, lean_object* v_sz_3504_, lean_object* v_i_3505_, lean_object* v_bs_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_){
_start:
{
size_t v_sz_boxed_3512_; size_t v_i_boxed_3513_; lean_object* v_res_3514_; 
v_sz_boxed_3512_ = lean_unbox_usize(v_sz_3504_);
lean_dec(v_sz_3504_);
v_i_boxed_3513_ = lean_unbox_usize(v_i_3505_);
lean_dec(v_i_3505_);
v_res_3514_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg(v___x_3502_, v_xs_3503_, v_sz_boxed_3512_, v_i_boxed_3513_, v_bs_3506_, v___y_3507_, v___y_3508_, v___y_3509_, v___y_3510_);
lean_dec(v___y_3510_);
lean_dec_ref(v___y_3509_);
lean_dec(v___y_3508_);
lean_dec_ref(v___y_3507_);
lean_dec_ref(v___x_3502_);
return v_res_3514_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__2(lean_object* v_a_3515_, lean_object* v_perms_3516_, size_t v___x_3517_, lean_object* v_fnNames_3518_, lean_object* v_a_3519_, lean_object* v_termMeasure_x3fs_3520_, lean_object* v_xs_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_){
_start:
{
size_t v_sz_3527_; lean_object* v___x_3528_; 
v_sz_3527_ = lean_array_size(v_a_3515_);
lean_inc_ref(v_a_3515_);
lean_inc_ref(v_xs_3521_);
v___x_3528_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg(v_perms_3516_, v_xs_3521_, v_sz_3527_, v___x_3517_, v_a_3515_, v___y_3522_, v___y_3523_, v___y_3524_, v___y_3525_);
if (lean_obj_tag(v___x_3528_) == 0)
{
lean_object* v_a_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; 
v_a_3529_ = lean_ctor_get(v___x_3528_, 0);
lean_inc_n(v_a_3529_, 2);
lean_dec_ref_known(v___x_3528_, 1);
lean_inc_ref(v_xs_3521_);
lean_inc_ref(v_a_3519_);
lean_inc_ref(v_fnNames_3518_);
v___x_3530_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_findRecArgCandidates___boxed), 10, 5);
lean_closure_set(v___x_3530_, 0, v_fnNames_3518_);
lean_closure_set(v___x_3530_, 1, v_a_3519_);
lean_closure_set(v___x_3530_, 2, v_xs_3521_);
lean_closure_set(v___x_3530_, 3, v_a_3529_);
lean_closure_set(v___x_3530_, 4, v_termMeasure_x3fs_3520_);
lean_inc_ref(v_a_3515_);
v___x_3531_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v_a_3515_, v___x_3530_, v___y_3522_, v___y_3523_, v___y_3524_, v___y_3525_);
if (lean_obj_tag(v___x_3531_) == 0)
{
lean_object* v_a_3532_; lean_object* v___x_3533_; lean_object* v___f_3534_; lean_object* v___x_3535_; 
v_a_3532_ = lean_ctor_get(v___x_3531_, 0);
lean_inc(v_a_3532_);
lean_dec_ref_known(v___x_3531_, 1);
v___x_3533_ = lean_box_usize(v___x_3517_);
lean_inc_ref(v_xs_3521_);
v___f_3534_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___boxed), 10, 4);
lean_closure_set(v___f_3534_, 0, v___x_3533_);
lean_closure_set(v___f_3534_, 1, v_a_3519_);
lean_closure_set(v___f_3534_, 2, v_xs_3521_);
lean_closure_set(v___f_3534_, 3, v_a_3515_);
v___x_3535_ = l_Lean_Elab_Structural_tryCandidates___redArg(v_fnNames_3518_, v_xs_3521_, v_a_3529_, v_a_3532_, v___f_3534_, v___y_3522_, v___y_3523_, v___y_3524_, v___y_3525_);
lean_dec_ref(v_fnNames_3518_);
return v___x_3535_;
}
else
{
lean_object* v_a_3536_; lean_object* v___x_3538_; uint8_t v_isShared_3539_; uint8_t v_isSharedCheck_3543_; 
lean_dec(v_a_3529_);
lean_dec_ref(v_xs_3521_);
lean_dec_ref(v_a_3519_);
lean_dec_ref(v_fnNames_3518_);
lean_dec_ref(v_a_3515_);
v_a_3536_ = lean_ctor_get(v___x_3531_, 0);
v_isSharedCheck_3543_ = !lean_is_exclusive(v___x_3531_);
if (v_isSharedCheck_3543_ == 0)
{
v___x_3538_ = v___x_3531_;
v_isShared_3539_ = v_isSharedCheck_3543_;
goto v_resetjp_3537_;
}
else
{
lean_inc(v_a_3536_);
lean_dec(v___x_3531_);
v___x_3538_ = lean_box(0);
v_isShared_3539_ = v_isSharedCheck_3543_;
goto v_resetjp_3537_;
}
v_resetjp_3537_:
{
lean_object* v___x_3541_; 
if (v_isShared_3539_ == 0)
{
v___x_3541_ = v___x_3538_;
goto v_reusejp_3540_;
}
else
{
lean_object* v_reuseFailAlloc_3542_; 
v_reuseFailAlloc_3542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3542_, 0, v_a_3536_);
v___x_3541_ = v_reuseFailAlloc_3542_;
goto v_reusejp_3540_;
}
v_reusejp_3540_:
{
return v___x_3541_;
}
}
}
}
else
{
lean_object* v_a_3544_; lean_object* v___x_3546_; uint8_t v_isShared_3547_; uint8_t v_isSharedCheck_3551_; 
lean_dec_ref(v_xs_3521_);
lean_dec_ref(v_termMeasure_x3fs_3520_);
lean_dec_ref(v_a_3519_);
lean_dec_ref(v_fnNames_3518_);
lean_dec_ref(v_a_3515_);
v_a_3544_ = lean_ctor_get(v___x_3528_, 0);
v_isSharedCheck_3551_ = !lean_is_exclusive(v___x_3528_);
if (v_isSharedCheck_3551_ == 0)
{
v___x_3546_ = v___x_3528_;
v_isShared_3547_ = v_isSharedCheck_3551_;
goto v_resetjp_3545_;
}
else
{
lean_inc(v_a_3544_);
lean_dec(v___x_3528_);
v___x_3546_ = lean_box(0);
v_isShared_3547_ = v_isSharedCheck_3551_;
goto v_resetjp_3545_;
}
v_resetjp_3545_:
{
lean_object* v___x_3549_; 
if (v_isShared_3547_ == 0)
{
v___x_3549_ = v___x_3546_;
goto v_reusejp_3548_;
}
else
{
lean_object* v_reuseFailAlloc_3550_; 
v_reuseFailAlloc_3550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3550_, 0, v_a_3544_);
v___x_3549_ = v_reuseFailAlloc_3550_;
goto v_reusejp_3548_;
}
v_reusejp_3548_:
{
return v___x_3549_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__2___boxed(lean_object* v_a_3552_, lean_object* v_perms_3553_, lean_object* v___x_3554_, lean_object* v_fnNames_3555_, lean_object* v_a_3556_, lean_object* v_termMeasure_x3fs_3557_, lean_object* v_xs_3558_, lean_object* v___y_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_){
_start:
{
size_t v___x_16137__boxed_3564_; lean_object* v_res_3565_; 
v___x_16137__boxed_3564_ = lean_unbox_usize(v___x_3554_);
lean_dec(v___x_3554_);
v_res_3565_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__2(v_a_3552_, v_perms_3553_, v___x_16137__boxed_3564_, v_fnNames_3555_, v_a_3556_, v_termMeasure_x3fs_3557_, v_xs_3558_, v___y_3559_, v___y_3560_, v___y_3561_, v___y_3562_);
lean_dec(v___y_3562_);
lean_dec_ref(v___y_3561_);
lean_dec(v___y_3560_);
lean_dec_ref(v___y_3559_);
lean_dec_ref(v_perms_3553_);
return v_res_3565_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0(size_t v_sz_3566_, size_t v_i_3567_, lean_object* v_bs_3568_){
_start:
{
uint8_t v___x_3569_; 
v___x_3569_ = lean_usize_dec_lt(v_i_3567_, v_sz_3566_);
if (v___x_3569_ == 0)
{
return v_bs_3568_;
}
else
{
lean_object* v_v_3570_; lean_object* v_declName_3571_; lean_object* v___x_3572_; lean_object* v_bs_x27_3573_; size_t v___x_3574_; size_t v___x_3575_; lean_object* v___x_3576_; 
v_v_3570_ = lean_array_uget_borrowed(v_bs_3568_, v_i_3567_);
v_declName_3571_ = lean_ctor_get(v_v_3570_, 3);
lean_inc(v_declName_3571_);
v___x_3572_ = lean_unsigned_to_nat(0u);
v_bs_x27_3573_ = lean_array_uset(v_bs_3568_, v_i_3567_, v___x_3572_);
v___x_3574_ = ((size_t)1ULL);
v___x_3575_ = lean_usize_add(v_i_3567_, v___x_3574_);
v___x_3576_ = lean_array_uset(v_bs_x27_3573_, v_i_3567_, v_declName_3571_);
v_i_3567_ = v___x_3575_;
v_bs_3568_ = v___x_3576_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0___boxed(lean_object* v_sz_3578_, lean_object* v_i_3579_, lean_object* v_bs_3580_){
_start:
{
size_t v_sz_boxed_3581_; size_t v_i_boxed_3582_; lean_object* v_res_3583_; 
v_sz_boxed_3581_ = lean_unbox_usize(v_sz_3578_);
lean_dec(v_sz_3578_);
v_i_boxed_3582_ = lean_unbox_usize(v_i_3579_);
lean_dec(v_i_3579_);
v_res_3583_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0(v_sz_boxed_3581_, v_i_boxed_3582_, v_bs_3580_);
return v_res_3583_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1___redArg(lean_object* v_fnNames_3584_, lean_object* v_numSectionVars_3585_, size_t v_sz_3586_, size_t v_i_3587_, lean_object* v_bs_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_){
_start:
{
uint8_t v___x_3592_; 
v___x_3592_ = lean_usize_dec_lt(v_i_3587_, v_sz_3586_);
if (v___x_3592_ == 0)
{
lean_object* v___x_3593_; 
lean_dec(v_numSectionVars_3585_);
lean_dec_ref(v_fnNames_3584_);
v___x_3593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3593_, 0, v_bs_3588_);
return v___x_3593_;
}
else
{
lean_object* v_v_3594_; lean_object* v_ref_3595_; uint8_t v_kind_3596_; lean_object* v_levelParams_3597_; lean_object* v_modifiers_3598_; lean_object* v_declName_3599_; lean_object* v_binders_3600_; lean_object* v_numSectionVars_3601_; lean_object* v_type_3602_; lean_object* v_value_3603_; lean_object* v_termination_3604_; lean_object* v___x_3606_; uint8_t v_isShared_3607_; uint8_t v_isSharedCheck_3627_; 
v_v_3594_ = lean_array_uget(v_bs_3588_, v_i_3587_);
v_ref_3595_ = lean_ctor_get(v_v_3594_, 0);
v_kind_3596_ = lean_ctor_get_uint8(v_v_3594_, sizeof(void*)*9);
v_levelParams_3597_ = lean_ctor_get(v_v_3594_, 1);
v_modifiers_3598_ = lean_ctor_get(v_v_3594_, 2);
v_declName_3599_ = lean_ctor_get(v_v_3594_, 3);
v_binders_3600_ = lean_ctor_get(v_v_3594_, 4);
v_numSectionVars_3601_ = lean_ctor_get(v_v_3594_, 5);
v_type_3602_ = lean_ctor_get(v_v_3594_, 6);
v_value_3603_ = lean_ctor_get(v_v_3594_, 7);
v_termination_3604_ = lean_ctor_get(v_v_3594_, 8);
v_isSharedCheck_3627_ = !lean_is_exclusive(v_v_3594_);
if (v_isSharedCheck_3627_ == 0)
{
v___x_3606_ = v_v_3594_;
v_isShared_3607_ = v_isSharedCheck_3627_;
goto v_resetjp_3605_;
}
else
{
lean_inc(v_termination_3604_);
lean_inc(v_value_3603_);
lean_inc(v_type_3602_);
lean_inc(v_numSectionVars_3601_);
lean_inc(v_binders_3600_);
lean_inc(v_declName_3599_);
lean_inc(v_modifiers_3598_);
lean_inc(v_levelParams_3597_);
lean_inc(v_ref_3595_);
lean_dec(v_v_3594_);
v___x_3606_ = lean_box(0);
v_isShared_3607_ = v_isSharedCheck_3627_;
goto v_resetjp_3605_;
}
v_resetjp_3605_:
{
lean_object* v___x_3608_; 
lean_inc(v_numSectionVars_3585_);
lean_inc_ref(v_fnNames_3584_);
v___x_3608_ = l_Lean_Elab_Structural_preprocess(v_value_3603_, v_fnNames_3584_, v_numSectionVars_3585_, v___y_3589_, v___y_3590_);
if (lean_obj_tag(v___x_3608_) == 0)
{
lean_object* v_a_3609_; lean_object* v___x_3610_; lean_object* v_bs_x27_3611_; lean_object* v___x_3613_; 
v_a_3609_ = lean_ctor_get(v___x_3608_, 0);
lean_inc(v_a_3609_);
lean_dec_ref_known(v___x_3608_, 1);
v___x_3610_ = lean_unsigned_to_nat(0u);
v_bs_x27_3611_ = lean_array_uset(v_bs_3588_, v_i_3587_, v___x_3610_);
if (v_isShared_3607_ == 0)
{
lean_ctor_set(v___x_3606_, 7, v_a_3609_);
v___x_3613_ = v___x_3606_;
goto v_reusejp_3612_;
}
else
{
lean_object* v_reuseFailAlloc_3618_; 
v_reuseFailAlloc_3618_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_3618_, 0, v_ref_3595_);
lean_ctor_set(v_reuseFailAlloc_3618_, 1, v_levelParams_3597_);
lean_ctor_set(v_reuseFailAlloc_3618_, 2, v_modifiers_3598_);
lean_ctor_set(v_reuseFailAlloc_3618_, 3, v_declName_3599_);
lean_ctor_set(v_reuseFailAlloc_3618_, 4, v_binders_3600_);
lean_ctor_set(v_reuseFailAlloc_3618_, 5, v_numSectionVars_3601_);
lean_ctor_set(v_reuseFailAlloc_3618_, 6, v_type_3602_);
lean_ctor_set(v_reuseFailAlloc_3618_, 7, v_a_3609_);
lean_ctor_set(v_reuseFailAlloc_3618_, 8, v_termination_3604_);
lean_ctor_set_uint8(v_reuseFailAlloc_3618_, sizeof(void*)*9, v_kind_3596_);
v___x_3613_ = v_reuseFailAlloc_3618_;
goto v_reusejp_3612_;
}
v_reusejp_3612_:
{
size_t v___x_3614_; size_t v___x_3615_; lean_object* v___x_3616_; 
v___x_3614_ = ((size_t)1ULL);
v___x_3615_ = lean_usize_add(v_i_3587_, v___x_3614_);
v___x_3616_ = lean_array_uset(v_bs_x27_3611_, v_i_3587_, v___x_3613_);
v_i_3587_ = v___x_3615_;
v_bs_3588_ = v___x_3616_;
goto _start;
}
}
else
{
lean_object* v_a_3619_; lean_object* v___x_3621_; uint8_t v_isShared_3622_; uint8_t v_isSharedCheck_3626_; 
lean_del_object(v___x_3606_);
lean_dec_ref(v_termination_3604_);
lean_dec_ref(v_type_3602_);
lean_dec(v_numSectionVars_3601_);
lean_dec(v_binders_3600_);
lean_dec(v_declName_3599_);
lean_dec_ref(v_modifiers_3598_);
lean_dec(v_levelParams_3597_);
lean_dec(v_ref_3595_);
lean_dec_ref(v_bs_3588_);
lean_dec(v_numSectionVars_3585_);
lean_dec_ref(v_fnNames_3584_);
v_a_3619_ = lean_ctor_get(v___x_3608_, 0);
v_isSharedCheck_3626_ = !lean_is_exclusive(v___x_3608_);
if (v_isSharedCheck_3626_ == 0)
{
v___x_3621_ = v___x_3608_;
v_isShared_3622_ = v_isSharedCheck_3626_;
goto v_resetjp_3620_;
}
else
{
lean_inc(v_a_3619_);
lean_dec(v___x_3608_);
v___x_3621_ = lean_box(0);
v_isShared_3622_ = v_isSharedCheck_3626_;
goto v_resetjp_3620_;
}
v_resetjp_3620_:
{
lean_object* v___x_3624_; 
if (v_isShared_3622_ == 0)
{
v___x_3624_ = v___x_3621_;
goto v_reusejp_3623_;
}
else
{
lean_object* v_reuseFailAlloc_3625_; 
v_reuseFailAlloc_3625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3625_, 0, v_a_3619_);
v___x_3624_ = v_reuseFailAlloc_3625_;
goto v_reusejp_3623_;
}
v_reusejp_3623_:
{
return v___x_3624_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1___redArg___boxed(lean_object* v_fnNames_3628_, lean_object* v_numSectionVars_3629_, lean_object* v_sz_3630_, lean_object* v_i_3631_, lean_object* v_bs_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_){
_start:
{
size_t v_sz_boxed_3636_; size_t v_i_boxed_3637_; lean_object* v_res_3638_; 
v_sz_boxed_3636_ = lean_unbox_usize(v_sz_3630_);
lean_dec(v_sz_3630_);
v_i_boxed_3637_ = lean_unbox_usize(v_i_3631_);
lean_dec(v_i_3631_);
v_res_3638_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1___redArg(v_fnNames_3628_, v_numSectionVars_3629_, v_sz_boxed_3636_, v_i_boxed_3637_, v_bs_3632_, v___y_3633_, v___y_3634_);
lean_dec(v___y_3634_);
lean_dec_ref(v___y_3633_);
return v_res_3638_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1(lean_object* v_fnNames_3639_, lean_object* v_numSectionVars_3640_, size_t v_sz_3641_, size_t v_i_3642_, lean_object* v_bs_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_){
_start:
{
lean_object* v___x_3649_; 
v___x_3649_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1___redArg(v_fnNames_3639_, v_numSectionVars_3640_, v_sz_3641_, v_i_3642_, v_bs_3643_, v___y_3646_, v___y_3647_);
return v___x_3649_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1___boxed(lean_object* v_fnNames_3650_, lean_object* v_numSectionVars_3651_, lean_object* v_sz_3652_, lean_object* v_i_3653_, lean_object* v_bs_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_){
_start:
{
size_t v_sz_boxed_3660_; size_t v_i_boxed_3661_; lean_object* v_res_3662_; 
v_sz_boxed_3660_ = lean_unbox_usize(v_sz_3652_);
lean_dec(v_sz_3652_);
v_i_boxed_3661_ = lean_unbox_usize(v_i_3653_);
lean_dec(v_i_3653_);
v_res_3662_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1(v_fnNames_3650_, v_numSectionVars_3651_, v_sz_boxed_3660_, v_i_boxed_3661_, v_bs_3654_, v___y_3655_, v___y_3656_, v___y_3657_, v___y_3658_);
lean_dec(v___y_3658_);
lean_dec_ref(v___y_3657_);
lean_dec(v___y_3656_);
lean_dec_ref(v___y_3655_);
return v_res_3662_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos(lean_object* v_preDefs_3663_, lean_object* v_termMeasure_x3fs_3664_, lean_object* v_a_3665_, lean_object* v_a_3666_, lean_object* v_a_3667_, lean_object* v_a_3668_){
_start:
{
lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v_numSectionVars_3673_; size_t v_sz_3674_; size_t v___x_3675_; lean_object* v_fnNames_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; 
v___x_3670_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_3671_ = lean_unsigned_to_nat(0u);
v___x_3672_ = lean_array_get_borrowed(v___x_3670_, v_preDefs_3663_, v___x_3671_);
v_numSectionVars_3673_ = lean_ctor_get(v___x_3672_, 5);
v_sz_3674_ = lean_array_size(v_preDefs_3663_);
v___x_3675_ = ((size_t)0ULL);
lean_inc_ref_n(v_preDefs_3663_, 2);
v_fnNames_3676_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0(v_sz_3674_, v___x_3675_, v_preDefs_3663_);
v___x_3677_ = lean_box_usize(v_sz_3674_);
v___x_3678_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___boxed__const__1));
lean_inc(v_numSectionVars_3673_);
lean_inc_ref(v_fnNames_3676_);
v___x_3679_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1___boxed), 10, 5);
lean_closure_set(v___x_3679_, 0, v_fnNames_3676_);
lean_closure_set(v___x_3679_, 1, v_numSectionVars_3673_);
lean_closure_set(v___x_3679_, 2, v___x_3677_);
lean_closure_set(v___x_3679_, 3, v___x_3678_);
lean_closure_set(v___x_3679_, 4, v_preDefs_3663_);
v___x_3680_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v_preDefs_3663_, v___x_3679_, v_a_3665_, v_a_3666_, v_a_3667_, v_a_3668_);
if (lean_obj_tag(v___x_3680_) == 0)
{
lean_object* v_a_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; 
v_a_3681_ = lean_ctor_get(v___x_3680_, 0);
lean_inc_n(v_a_3681_, 3);
lean_dec_ref_known(v___x_3680_, 1);
v___x_3682_ = lean_alloc_closure((void*)(l_Lean_Elab_getFixedParamPerms___boxed), 6, 1);
lean_closure_set(v___x_3682_, 0, v_a_3681_);
v___x_3683_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v_a_3681_, v___x_3682_, v_a_3665_, v_a_3666_, v_a_3667_, v_a_3668_);
if (lean_obj_tag(v___x_3683_) == 0)
{
lean_object* v_a_3684_; lean_object* v_perms_3685_; lean_object* v___x_3686_; lean_object* v_type_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___f_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; 
v_a_3684_ = lean_ctor_get(v___x_3683_, 0);
lean_inc(v_a_3684_);
lean_dec_ref_known(v___x_3683_, 1);
v_perms_3685_ = lean_ctor_get(v_a_3684_, 1);
lean_inc_ref_n(v_perms_3685_, 2);
v___x_3686_ = lean_array_get_borrowed(v___x_3670_, v_a_3681_, v___x_3671_);
v_type_3687_ = lean_ctor_get(v___x_3686_, 6);
lean_inc_ref(v_type_3687_);
v___x_3688_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0);
v___x_3689_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___boxed__const__1));
v___f_3690_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__2___boxed), 12, 6);
lean_closure_set(v___f_3690_, 0, v_a_3681_);
lean_closure_set(v___f_3690_, 1, v_perms_3685_);
lean_closure_set(v___f_3690_, 2, v___x_3689_);
lean_closure_set(v___f_3690_, 3, v_fnNames_3676_);
lean_closure_set(v___f_3690_, 4, v_a_3684_);
lean_closure_set(v___f_3690_, 5, v_termMeasure_x3fs_3664_);
v___x_3691_ = lean_array_get(v___x_3688_, v_perms_3685_, v___x_3671_);
lean_dec_ref(v_perms_3685_);
v___x_3692_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg(v___x_3691_, v_type_3687_, v___f_3690_, v_a_3665_, v_a_3666_, v_a_3667_, v_a_3668_);
return v___x_3692_;
}
else
{
lean_object* v_a_3693_; lean_object* v___x_3695_; uint8_t v_isShared_3696_; uint8_t v_isSharedCheck_3700_; 
lean_dec(v_a_3681_);
lean_dec_ref(v_fnNames_3676_);
lean_dec_ref(v_termMeasure_x3fs_3664_);
v_a_3693_ = lean_ctor_get(v___x_3683_, 0);
v_isSharedCheck_3700_ = !lean_is_exclusive(v___x_3683_);
if (v_isSharedCheck_3700_ == 0)
{
v___x_3695_ = v___x_3683_;
v_isShared_3696_ = v_isSharedCheck_3700_;
goto v_resetjp_3694_;
}
else
{
lean_inc(v_a_3693_);
lean_dec(v___x_3683_);
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
else
{
lean_object* v_a_3701_; lean_object* v___x_3703_; uint8_t v_isShared_3704_; uint8_t v_isSharedCheck_3708_; 
lean_dec_ref(v_fnNames_3676_);
lean_dec_ref(v_termMeasure_x3fs_3664_);
v_a_3701_ = lean_ctor_get(v___x_3680_, 0);
v_isSharedCheck_3708_ = !lean_is_exclusive(v___x_3680_);
if (v_isSharedCheck_3708_ == 0)
{
v___x_3703_ = v___x_3680_;
v_isShared_3704_ = v_isSharedCheck_3708_;
goto v_resetjp_3702_;
}
else
{
lean_inc(v_a_3701_);
lean_dec(v___x_3680_);
v___x_3703_ = lean_box(0);
v_isShared_3704_ = v_isSharedCheck_3708_;
goto v_resetjp_3702_;
}
v_resetjp_3702_:
{
lean_object* v___x_3706_; 
if (v_isShared_3704_ == 0)
{
v___x_3706_ = v___x_3703_;
goto v_reusejp_3705_;
}
else
{
lean_object* v_reuseFailAlloc_3707_; 
v_reuseFailAlloc_3707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3707_, 0, v_a_3701_);
v___x_3706_ = v_reuseFailAlloc_3707_;
goto v_reusejp_3705_;
}
v_reusejp_3705_:
{
return v___x_3706_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___boxed(lean_object* v_preDefs_3709_, lean_object* v_termMeasure_x3fs_3710_, lean_object* v_a_3711_, lean_object* v_a_3712_, lean_object* v_a_3713_, lean_object* v_a_3714_, lean_object* v_a_3715_){
_start:
{
lean_object* v_res_3716_; 
v_res_3716_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos(v_preDefs_3709_, v_termMeasure_x3fs_3710_, v_a_3711_, v_a_3712_, v_a_3713_, v_a_3714_);
lean_dec(v_a_3714_);
lean_dec_ref(v_a_3713_);
lean_dec(v_a_3712_);
lean_dec_ref(v_a_3711_);
return v_res_3716_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4(lean_object* v_fst_3717_, lean_object* v_as_3718_, size_t v_sz_3719_, size_t v_i_3720_, lean_object* v_bs_3721_){
_start:
{
lean_object* v___x_3722_; 
v___x_3722_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg(v_fst_3717_, v_sz_3719_, v_i_3720_, v_bs_3721_);
return v___x_3722_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___boxed(lean_object* v_fst_3723_, lean_object* v_as_3724_, lean_object* v_sz_3725_, lean_object* v_i_3726_, lean_object* v_bs_3727_){
_start:
{
size_t v_sz_boxed_3728_; size_t v_i_boxed_3729_; lean_object* v_res_3730_; 
v_sz_boxed_3728_ = lean_unbox_usize(v_sz_3725_);
lean_dec(v_sz_3725_);
v_i_boxed_3729_ = lean_unbox_usize(v_i_3726_);
lean_dec(v_i_3726_);
v_res_3730_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4(v_fst_3723_, v_as_3724_, v_sz_boxed_3728_, v_i_boxed_3729_, v_bs_3727_);
lean_dec_ref(v_as_3724_);
lean_dec_ref(v_fst_3723_);
return v_res_3730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10(lean_object* v_00_u03b1_3731_, lean_object* v_lctx_3732_, lean_object* v_localInsts_3733_, lean_object* v_x_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_){
_start:
{
lean_object* v___x_3740_; 
v___x_3740_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___redArg(v_lctx_3732_, v_localInsts_3733_, v_x_3734_, v___y_3735_, v___y_3736_, v___y_3737_, v___y_3738_);
return v___x_3740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___boxed(lean_object* v_00_u03b1_3741_, lean_object* v_lctx_3742_, lean_object* v_localInsts_3743_, lean_object* v_x_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_){
_start:
{
lean_object* v_res_3750_; 
v_res_3750_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10(v_00_u03b1_3741_, v_lctx_3742_, v_localInsts_3743_, v_x_3744_, v___y_3745_, v___y_3746_, v___y_3747_, v___y_3748_);
lean_dec(v___y_3748_);
lean_dec_ref(v___y_3747_);
lean_dec(v___y_3746_);
lean_dec_ref(v___y_3745_);
return v_res_3750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9(lean_object* v_00_u03b1_3751_, lean_object* v_fvarIds_3752_, lean_object* v_k_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_){
_start:
{
lean_object* v___x_3759_; 
v___x_3759_ = l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___redArg(v_fvarIds_3752_, v_k_3753_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_);
return v___x_3759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___boxed(lean_object* v_00_u03b1_3760_, lean_object* v_fvarIds_3761_, lean_object* v_k_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_){
_start:
{
lean_object* v_res_3768_; 
v_res_3768_ = l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9(v_00_u03b1_3760_, v_fvarIds_3761_, v_k_3762_, v___y_3763_, v___y_3764_, v___y_3765_, v___y_3766_);
lean_dec(v___y_3766_);
lean_dec_ref(v___y_3765_);
lean_dec(v___y_3764_);
lean_dec_ref(v___y_3763_);
lean_dec_ref(v_fvarIds_3761_);
return v_res_3768_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__15(lean_object* v_a_3769_){
_start:
{
lean_object* v___x_3770_; 
v___x_3770_ = lean_nat_to_int(v_a_3769_);
return v___x_3770_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12(lean_object* v___x_3771_, lean_object* v_xs_3772_, lean_object* v_as_3773_, size_t v_sz_3774_, size_t v_i_3775_, lean_object* v_bs_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_){
_start:
{
lean_object* v___x_3782_; 
v___x_3782_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg(v___x_3771_, v_xs_3772_, v_sz_3774_, v_i_3775_, v_bs_3776_, v___y_3777_, v___y_3778_, v___y_3779_, v___y_3780_);
return v___x_3782_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___boxed(lean_object* v___x_3783_, lean_object* v_xs_3784_, lean_object* v_as_3785_, lean_object* v_sz_3786_, lean_object* v_i_3787_, lean_object* v_bs_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_){
_start:
{
size_t v_sz_boxed_3794_; size_t v_i_boxed_3795_; lean_object* v_res_3796_; 
v_sz_boxed_3794_ = lean_unbox_usize(v_sz_3786_);
lean_dec(v_sz_3786_);
v_i_boxed_3795_ = lean_unbox_usize(v_i_3787_);
lean_dec(v_i_3787_);
v_res_3796_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12(v___x_3783_, v_xs_3784_, v_as_3785_, v_sz_boxed_3794_, v_i_boxed_3795_, v_bs_3788_, v___y_3789_, v___y_3790_, v___y_3791_, v___y_3792_);
lean_dec(v___y_3792_);
lean_dec_ref(v___y_3791_);
lean_dec(v___y_3790_);
lean_dec_ref(v___y_3789_);
lean_dec_ref(v_as_3785_);
lean_dec_ref(v___x_3783_);
return v_res_3796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure___lam__0(lean_object* v___x_3797_, lean_object* v_recArgPos_3798_, lean_object* v_xs_3799_, lean_object* v_x_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_){
_start:
{
lean_object* v___x_3806_; uint8_t v___x_3807_; uint8_t v___x_3808_; uint8_t v___x_3809_; lean_object* v___x_3810_; 
v___x_3806_ = lean_array_get_borrowed(v___x_3797_, v_xs_3799_, v_recArgPos_3798_);
v___x_3807_ = 0;
v___x_3808_ = 1;
v___x_3809_ = 1;
lean_inc(v___x_3806_);
v___x_3810_ = l_Lean_Meta_mkLambdaFVars(v_xs_3799_, v___x_3806_, v___x_3807_, v___x_3808_, v___x_3807_, v___x_3808_, v___x_3809_, v___y_3801_, v___y_3802_, v___y_3803_, v___y_3804_);
return v___x_3810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure___lam__0___boxed(lean_object* v___x_3811_, lean_object* v_recArgPos_3812_, lean_object* v_xs_3813_, lean_object* v_x_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_){
_start:
{
lean_object* v_res_3820_; 
v_res_3820_ = l_Lean_Elab_Structural_reportTermMeasure___lam__0(v___x_3811_, v_recArgPos_3812_, v_xs_3813_, v_x_3814_, v___y_3815_, v___y_3816_, v___y_3817_, v___y_3818_);
lean_dec(v___y_3818_);
lean_dec_ref(v___y_3817_);
lean_dec(v___y_3816_);
lean_dec_ref(v___y_3815_);
lean_dec_ref(v_x_3814_);
lean_dec_ref(v_xs_3813_);
lean_dec(v_recArgPos_3812_);
lean_dec_ref(v___x_3811_);
return v_res_3820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure___lam__1(lean_object* v_xs_3821_, lean_object* v_x_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_){
_start:
{
lean_object* v___x_3828_; lean_object* v___x_3829_; 
v___x_3828_ = lean_array_get_size(v_xs_3821_);
v___x_3829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3829_, 0, v___x_3828_);
return v___x_3829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure___lam__1___boxed(lean_object* v_xs_3830_, lean_object* v_x_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_){
_start:
{
lean_object* v_res_3837_; 
v_res_3837_ = l_Lean_Elab_Structural_reportTermMeasure___lam__1(v_xs_3830_, v_x_3831_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_);
lean_dec(v___y_3835_);
lean_dec_ref(v___y_3834_);
lean_dec(v___y_3833_);
lean_dec_ref(v___y_3832_);
lean_dec_ref(v_x_3831_);
lean_dec_ref(v_xs_3830_);
return v_res_3837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure(lean_object* v_preDef_3849_, lean_object* v_recArgPos_3850_, lean_object* v_a_3851_, lean_object* v_a_3852_, lean_object* v_a_3853_, lean_object* v_a_3854_){
_start:
{
lean_object* v_termination_3856_; lean_object* v_terminationBy_x3f_x3f_3857_; 
v_termination_3856_ = lean_ctor_get(v_preDef_3849_, 8);
lean_inc_ref(v_termination_3856_);
v_terminationBy_x3f_x3f_3857_ = lean_ctor_get(v_termination_3856_, 1);
lean_inc(v_terminationBy_x3f_x3f_3857_);
if (lean_obj_tag(v_terminationBy_x3f_x3f_3857_) == 1)
{
lean_object* v_value_3858_; lean_object* v_extraParams_3859_; lean_object* v___x_3861_; uint8_t v_isShared_3862_; uint8_t v_isSharedCheck_3911_; 
v_value_3858_ = lean_ctor_get(v_preDef_3849_, 7);
lean_inc_ref(v_value_3858_);
lean_dec_ref(v_preDef_3849_);
v_extraParams_3859_ = lean_ctor_get(v_termination_3856_, 5);
v_isSharedCheck_3911_ = !lean_is_exclusive(v_termination_3856_);
if (v_isSharedCheck_3911_ == 0)
{
lean_object* v_unused_3912_; lean_object* v_unused_3913_; lean_object* v_unused_3914_; lean_object* v_unused_3915_; lean_object* v_unused_3916_; 
v_unused_3912_ = lean_ctor_get(v_termination_3856_, 4);
lean_dec(v_unused_3912_);
v_unused_3913_ = lean_ctor_get(v_termination_3856_, 3);
lean_dec(v_unused_3913_);
v_unused_3914_ = lean_ctor_get(v_termination_3856_, 2);
lean_dec(v_unused_3914_);
v_unused_3915_ = lean_ctor_get(v_termination_3856_, 1);
lean_dec(v_unused_3915_);
v_unused_3916_ = lean_ctor_get(v_termination_3856_, 0);
lean_dec(v_unused_3916_);
v___x_3861_ = v_termination_3856_;
v_isShared_3862_ = v_isSharedCheck_3911_;
goto v_resetjp_3860_;
}
else
{
lean_inc(v_extraParams_3859_);
lean_dec(v_termination_3856_);
v___x_3861_ = lean_box(0);
v_isShared_3862_ = v_isSharedCheck_3911_;
goto v_resetjp_3860_;
}
v_resetjp_3860_:
{
lean_object* v_val_3863_; lean_object* v___x_3864_; lean_object* v___f_3865_; uint8_t v___x_3866_; lean_object* v___x_3867_; 
v_val_3863_ = lean_ctor_get(v_terminationBy_x3f_x3f_3857_, 0);
lean_inc(v_val_3863_);
lean_dec_ref_known(v_terminationBy_x3f_x3f_3857_, 1);
v___x_3864_ = l_Lean_instInhabitedExpr;
v___f_3865_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_reportTermMeasure___lam__0___boxed), 9, 2);
lean_closure_set(v___f_3865_, 0, v___x_3864_);
lean_closure_set(v___f_3865_, 1, v_recArgPos_3850_);
v___x_3866_ = 0;
lean_inc_ref(v_value_3858_);
v___x_3867_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg(v_value_3858_, v___f_3865_, v___x_3866_, v_a_3851_, v_a_3852_, v_a_3853_, v_a_3854_);
if (lean_obj_tag(v___x_3867_) == 0)
{
lean_object* v_a_3868_; lean_object* v___f_3869_; lean_object* v___x_3870_; 
v_a_3868_ = lean_ctor_get(v___x_3867_, 0);
lean_inc(v_a_3868_);
lean_dec_ref_known(v___x_3867_, 1);
v___f_3869_ = ((lean_object*)(l_Lean_Elab_Structural_reportTermMeasure___closed__0));
v___x_3870_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg(v_value_3858_, v___f_3869_, v___x_3866_, v_a_3851_, v_a_3852_, v_a_3853_, v_a_3854_);
if (lean_obj_tag(v___x_3870_) == 0)
{
lean_object* v_a_3871_; lean_object* v___x_3872_; uint8_t v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; 
v_a_3871_ = lean_ctor_get(v___x_3870_, 0);
lean_inc(v_a_3871_);
lean_dec_ref_known(v___x_3870_, 1);
v___x_3872_ = lean_box(0);
v___x_3873_ = 1;
v___x_3874_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3874_, 0, v___x_3872_);
lean_ctor_set(v___x_3874_, 1, v_a_3868_);
lean_ctor_set_uint8(v___x_3874_, sizeof(void*)*2, v___x_3873_);
v___x_3875_ = l_Lean_Elab_TerminationMeasure_delab(v_a_3871_, v_extraParams_3859_, v___x_3874_, v_a_3851_, v_a_3852_, v_a_3853_, v_a_3854_);
lean_dec(v_a_3871_);
if (lean_obj_tag(v___x_3875_) == 0)
{
lean_object* v_a_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3881_; 
v_a_3876_ = lean_ctor_get(v___x_3875_, 0);
lean_inc(v_a_3876_);
lean_dec_ref_known(v___x_3875_, 1);
v___x_3877_ = ((lean_object*)(l_Lean_Elab_Structural_reportTermMeasure___closed__5));
v___x_3878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3878_, 0, v___x_3877_);
lean_ctor_set(v___x_3878_, 1, v_a_3876_);
v___x_3879_ = lean_box(0);
if (v_isShared_3862_ == 0)
{
lean_ctor_set(v___x_3861_, 5, v___x_3879_);
lean_ctor_set(v___x_3861_, 4, v___x_3879_);
lean_ctor_set(v___x_3861_, 3, v___x_3879_);
lean_ctor_set(v___x_3861_, 2, v___x_3879_);
lean_ctor_set(v___x_3861_, 1, v___x_3879_);
lean_ctor_set(v___x_3861_, 0, v___x_3878_);
v___x_3881_ = v___x_3861_;
goto v_reusejp_3880_;
}
else
{
lean_object* v_reuseFailAlloc_3886_; 
v_reuseFailAlloc_3886_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3886_, 0, v___x_3878_);
lean_ctor_set(v_reuseFailAlloc_3886_, 1, v___x_3879_);
lean_ctor_set(v_reuseFailAlloc_3886_, 2, v___x_3879_);
lean_ctor_set(v_reuseFailAlloc_3886_, 3, v___x_3879_);
lean_ctor_set(v_reuseFailAlloc_3886_, 4, v___x_3879_);
lean_ctor_set(v_reuseFailAlloc_3886_, 5, v___x_3879_);
v___x_3881_ = v_reuseFailAlloc_3886_;
goto v_reusejp_3880_;
}
v_reusejp_3880_:
{
lean_object* v___x_3882_; uint8_t v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; 
v___x_3882_ = ((lean_object*)(l_Lean_Elab_Structural_reportTermMeasure___closed__6));
v___x_3883_ = 4;
v___x_3884_ = l_Lean_MessageData_nil;
v___x_3885_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_val_3863_, v___x_3881_, v___x_3879_, v___x_3882_, v___x_3879_, v___x_3883_, v___x_3884_, v_a_3853_, v_a_3854_);
return v___x_3885_;
}
}
else
{
lean_object* v_a_3887_; lean_object* v___x_3889_; uint8_t v_isShared_3890_; uint8_t v_isSharedCheck_3894_; 
lean_dec(v_val_3863_);
lean_del_object(v___x_3861_);
v_a_3887_ = lean_ctor_get(v___x_3875_, 0);
v_isSharedCheck_3894_ = !lean_is_exclusive(v___x_3875_);
if (v_isSharedCheck_3894_ == 0)
{
v___x_3889_ = v___x_3875_;
v_isShared_3890_ = v_isSharedCheck_3894_;
goto v_resetjp_3888_;
}
else
{
lean_inc(v_a_3887_);
lean_dec(v___x_3875_);
v___x_3889_ = lean_box(0);
v_isShared_3890_ = v_isSharedCheck_3894_;
goto v_resetjp_3888_;
}
v_resetjp_3888_:
{
lean_object* v___x_3892_; 
if (v_isShared_3890_ == 0)
{
v___x_3892_ = v___x_3889_;
goto v_reusejp_3891_;
}
else
{
lean_object* v_reuseFailAlloc_3893_; 
v_reuseFailAlloc_3893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3893_, 0, v_a_3887_);
v___x_3892_ = v_reuseFailAlloc_3893_;
goto v_reusejp_3891_;
}
v_reusejp_3891_:
{
return v___x_3892_;
}
}
}
}
else
{
lean_object* v_a_3895_; lean_object* v___x_3897_; uint8_t v_isShared_3898_; uint8_t v_isSharedCheck_3902_; 
lean_dec(v_a_3868_);
lean_dec(v_val_3863_);
lean_del_object(v___x_3861_);
lean_dec(v_extraParams_3859_);
v_a_3895_ = lean_ctor_get(v___x_3870_, 0);
v_isSharedCheck_3902_ = !lean_is_exclusive(v___x_3870_);
if (v_isSharedCheck_3902_ == 0)
{
v___x_3897_ = v___x_3870_;
v_isShared_3898_ = v_isSharedCheck_3902_;
goto v_resetjp_3896_;
}
else
{
lean_inc(v_a_3895_);
lean_dec(v___x_3870_);
v___x_3897_ = lean_box(0);
v_isShared_3898_ = v_isSharedCheck_3902_;
goto v_resetjp_3896_;
}
v_resetjp_3896_:
{
lean_object* v___x_3900_; 
if (v_isShared_3898_ == 0)
{
v___x_3900_ = v___x_3897_;
goto v_reusejp_3899_;
}
else
{
lean_object* v_reuseFailAlloc_3901_; 
v_reuseFailAlloc_3901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3901_, 0, v_a_3895_);
v___x_3900_ = v_reuseFailAlloc_3901_;
goto v_reusejp_3899_;
}
v_reusejp_3899_:
{
return v___x_3900_;
}
}
}
}
else
{
lean_object* v_a_3903_; lean_object* v___x_3905_; uint8_t v_isShared_3906_; uint8_t v_isSharedCheck_3910_; 
lean_dec(v_val_3863_);
lean_del_object(v___x_3861_);
lean_dec(v_extraParams_3859_);
lean_dec_ref(v_value_3858_);
v_a_3903_ = lean_ctor_get(v___x_3867_, 0);
v_isSharedCheck_3910_ = !lean_is_exclusive(v___x_3867_);
if (v_isSharedCheck_3910_ == 0)
{
v___x_3905_ = v___x_3867_;
v_isShared_3906_ = v_isSharedCheck_3910_;
goto v_resetjp_3904_;
}
else
{
lean_inc(v_a_3903_);
lean_dec(v___x_3867_);
v___x_3905_ = lean_box(0);
v_isShared_3906_ = v_isSharedCheck_3910_;
goto v_resetjp_3904_;
}
v_resetjp_3904_:
{
lean_object* v___x_3908_; 
if (v_isShared_3906_ == 0)
{
v___x_3908_ = v___x_3905_;
goto v_reusejp_3907_;
}
else
{
lean_object* v_reuseFailAlloc_3909_; 
v_reuseFailAlloc_3909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3909_, 0, v_a_3903_);
v___x_3908_ = v_reuseFailAlloc_3909_;
goto v_reusejp_3907_;
}
v_reusejp_3907_:
{
return v___x_3908_;
}
}
}
}
}
else
{
lean_object* v___x_3917_; lean_object* v___x_3918_; 
lean_dec(v_terminationBy_x3f_x3f_3857_);
lean_dec_ref(v_termination_3856_);
lean_dec(v_recArgPos_3850_);
lean_dec_ref(v_preDef_3849_);
v___x_3917_ = lean_box(0);
v___x_3918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3918_, 0, v___x_3917_);
return v___x_3918_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure___boxed(lean_object* v_preDef_3919_, lean_object* v_recArgPos_3920_, lean_object* v_a_3921_, lean_object* v_a_3922_, lean_object* v_a_3923_, lean_object* v_a_3924_, lean_object* v_a_3925_){
_start:
{
lean_object* v_res_3926_; 
v_res_3926_ = l_Lean_Elab_Structural_reportTermMeasure(v_preDef_3919_, v_recArgPos_3920_, v_a_3921_, v_a_3922_, v_a_3923_, v_a_3924_);
lean_dec(v_a_3924_);
lean_dec_ref(v_a_3923_);
lean_dec(v_a_3922_);
lean_dec_ref(v_a_3921_);
return v_res_3926_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___redArg(lean_object* v_as_3927_, size_t v_sz_3928_, size_t v_i_3929_, lean_object* v_b_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_){
_start:
{
uint8_t v___x_3936_; 
v___x_3936_ = lean_usize_dec_lt(v_i_3929_, v_sz_3928_);
if (v___x_3936_ == 0)
{
lean_object* v___x_3937_; 
v___x_3937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3937_, 0, v_b_3930_);
return v___x_3937_;
}
else
{
lean_object* v_a_3938_; lean_object* v_declName_3939_; lean_object* v___x_3940_; 
v_a_3938_ = lean_array_uget_borrowed(v_as_3927_, v_i_3929_);
v_declName_3939_ = lean_ctor_get(v_a_3938_, 3);
lean_inc(v_declName_3939_);
v___x_3940_ = l_Lean_Meta_saveEqnAffectingOptions(v_declName_3939_, v___y_3931_, v___y_3932_, v___y_3933_, v___y_3934_);
if (lean_obj_tag(v___x_3940_) == 0)
{
lean_object* v___x_3941_; size_t v___x_3942_; size_t v___x_3943_; 
lean_dec_ref_known(v___x_3940_, 1);
v___x_3941_ = lean_box(0);
v___x_3942_ = ((size_t)1ULL);
v___x_3943_ = lean_usize_add(v_i_3929_, v___x_3942_);
v_i_3929_ = v___x_3943_;
v_b_3930_ = v___x_3941_;
goto _start;
}
else
{
return v___x_3940_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___redArg___boxed(lean_object* v_as_3945_, lean_object* v_sz_3946_, lean_object* v_i_3947_, lean_object* v_b_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_){
_start:
{
size_t v_sz_boxed_3954_; size_t v_i_boxed_3955_; lean_object* v_res_3956_; 
v_sz_boxed_3954_ = lean_unbox_usize(v_sz_3946_);
lean_dec(v_sz_3946_);
v_i_boxed_3955_ = lean_unbox_usize(v_i_3947_);
lean_dec(v_i_3947_);
v_res_3956_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___redArg(v_as_3945_, v_sz_boxed_3954_, v_i_boxed_3955_, v_b_3948_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_);
lean_dec(v___y_3952_);
lean_dec_ref(v___y_3951_);
lean_dec(v___y_3950_);
lean_dec_ref(v___y_3949_);
lean_dec_ref(v_as_3945_);
return v_res_3956_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__1(lean_object* v_docCtx_3957_, lean_object* v_a_3958_, lean_object* v_snd_3959_, lean_object* v_as_3960_, size_t v_sz_3961_, size_t v_i_3962_, lean_object* v_b_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_){
_start:
{
uint8_t v___x_3971_; 
v___x_3971_ = lean_usize_dec_lt(v_i_3962_, v_sz_3961_);
if (v___x_3971_ == 0)
{
lean_object* v___x_3972_; 
lean_dec_ref(v_snd_3959_);
lean_dec_ref(v_a_3958_);
lean_dec_ref(v_docCtx_3957_);
v___x_3972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3972_, 0, v_b_3963_);
return v___x_3972_;
}
else
{
lean_object* v_array_3973_; lean_object* v_start_3974_; lean_object* v_stop_3975_; uint8_t v___x_3976_; 
v_array_3973_ = lean_ctor_get(v_b_3963_, 0);
v_start_3974_ = lean_ctor_get(v_b_3963_, 1);
v_stop_3975_ = lean_ctor_get(v_b_3963_, 2);
v___x_3976_ = lean_nat_dec_lt(v_start_3974_, v_stop_3975_);
if (v___x_3976_ == 0)
{
lean_object* v___x_3977_; 
lean_dec_ref(v_snd_3959_);
lean_dec_ref(v_a_3958_);
lean_dec_ref(v_docCtx_3957_);
v___x_3977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3977_, 0, v_b_3963_);
return v___x_3977_;
}
else
{
lean_object* v___x_3979_; uint8_t v_isShared_3980_; uint8_t v_isSharedCheck_4044_; 
lean_inc(v_stop_3975_);
lean_inc(v_start_3974_);
lean_inc_ref(v_array_3973_);
v_isSharedCheck_4044_ = !lean_is_exclusive(v_b_3963_);
if (v_isSharedCheck_4044_ == 0)
{
lean_object* v_unused_4045_; lean_object* v_unused_4046_; lean_object* v_unused_4047_; 
v_unused_4045_ = lean_ctor_get(v_b_3963_, 2);
lean_dec(v_unused_4045_);
v_unused_4046_ = lean_ctor_get(v_b_3963_, 1);
lean_dec(v_unused_4046_);
v_unused_4047_ = lean_ctor_get(v_b_3963_, 0);
lean_dec(v_unused_4047_);
v___x_3979_ = v_b_3963_;
v_isShared_3980_ = v_isSharedCheck_4044_;
goto v_resetjp_3978_;
}
else
{
lean_dec(v_b_3963_);
v___x_3979_ = lean_box(0);
v_isShared_3980_ = v_isSharedCheck_4044_;
goto v_resetjp_3978_;
}
v_resetjp_3978_:
{
lean_object* v_a_3981_; uint8_t v_kind_3982_; lean_object* v_type_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3988_; 
v_a_3981_ = lean_array_uget_borrowed(v_as_3960_, v_i_3962_);
v_kind_3982_ = lean_ctor_get_uint8(v_a_3981_, sizeof(void*)*9);
v_type_3983_ = lean_ctor_get(v_a_3981_, 6);
v___x_3984_ = lean_array_fget(v_array_3973_, v_start_3974_);
v___x_3985_ = lean_unsigned_to_nat(1u);
v___x_3986_ = lean_nat_add(v_start_3974_, v___x_3985_);
lean_dec(v_start_3974_);
if (v_isShared_3980_ == 0)
{
lean_ctor_set(v___x_3979_, 1, v___x_3986_);
v___x_3988_ = v___x_3979_;
goto v_reusejp_3987_;
}
else
{
lean_object* v_reuseFailAlloc_4043_; 
v_reuseFailAlloc_4043_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4043_, 0, v_array_3973_);
lean_ctor_set(v_reuseFailAlloc_4043_, 1, v___x_3986_);
lean_ctor_set(v_reuseFailAlloc_4043_, 2, v_stop_3975_);
v___x_3988_ = v_reuseFailAlloc_4043_;
goto v_reusejp_3987_;
}
v_reusejp_3987_:
{
lean_object* v_preDef_3990_; lean_object* v___y_3991_; lean_object* v___y_3992_; lean_object* v___y_3993_; lean_object* v___y_3994_; lean_object* v___y_3995_; lean_object* v___y_3996_; uint8_t v___x_4009_; 
v___x_4009_ = l_Lean_Elab_DefKind_isTheorem(v_kind_3982_);
if (v___x_4009_ == 0)
{
lean_object* v___x_4010_; 
lean_inc_ref(v_type_3983_);
v___x_4010_ = l_Lean_Meta_isProp(v_type_3983_, v___y_3966_, v___y_3967_, v___y_3968_, v___y_3969_);
if (lean_obj_tag(v___x_4010_) == 0)
{
lean_object* v_a_4011_; uint8_t v___x_4012_; 
v_a_4011_ = lean_ctor_get(v___x_4010_, 0);
lean_inc(v_a_4011_);
lean_dec_ref_known(v___x_4010_, 1);
v___x_4012_ = lean_unbox(v_a_4011_);
lean_dec(v_a_4011_);
if (v___x_4012_ == 0)
{
lean_object* v___x_4013_; 
lean_inc(v_a_3981_);
v___x_4013_ = l_Lean_Elab_abstractNestedProofs(v_a_3981_, v___x_3976_, v___y_3966_, v___y_3967_, v___y_3968_, v___y_3969_);
if (lean_obj_tag(v___x_4013_) == 0)
{
lean_object* v_a_4014_; size_t v_sz_4015_; size_t v___x_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; 
v_a_4014_ = lean_ctor_get(v___x_4013_, 0);
lean_inc_n(v_a_4014_, 2);
lean_dec_ref_known(v___x_4013_, 1);
v_sz_4015_ = lean_array_size(v_a_3958_);
v___x_4016_ = ((size_t)0ULL);
lean_inc_ref(v_a_3958_);
v___x_4017_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0(v_sz_4015_, v___x_4016_, v_a_3958_);
lean_inc_ref(v_snd_3959_);
lean_inc(v___x_3984_);
v___x_4018_ = l_Lean_Elab_Structural_registerEqnsInfo(v_a_4014_, v___x_4017_, v___x_3984_, v_snd_3959_, v___y_3968_, v___y_3969_);
if (lean_obj_tag(v___x_4018_) == 0)
{
lean_dec_ref_known(v___x_4018_, 1);
v_preDef_3990_ = v_a_4014_;
v___y_3991_ = v___y_3964_;
v___y_3992_ = v___y_3965_;
v___y_3993_ = v___y_3966_;
v___y_3994_ = v___y_3967_;
v___y_3995_ = v___y_3968_;
v___y_3996_ = v___y_3969_;
goto v___jp_3989_;
}
else
{
lean_object* v_a_4019_; lean_object* v___x_4021_; uint8_t v_isShared_4022_; uint8_t v_isSharedCheck_4026_; 
lean_dec(v_a_4014_);
lean_dec_ref(v___x_3988_);
lean_dec(v___x_3984_);
lean_dec_ref(v_snd_3959_);
lean_dec_ref(v_a_3958_);
lean_dec_ref(v_docCtx_3957_);
v_a_4019_ = lean_ctor_get(v___x_4018_, 0);
v_isSharedCheck_4026_ = !lean_is_exclusive(v___x_4018_);
if (v_isSharedCheck_4026_ == 0)
{
v___x_4021_ = v___x_4018_;
v_isShared_4022_ = v_isSharedCheck_4026_;
goto v_resetjp_4020_;
}
else
{
lean_inc(v_a_4019_);
lean_dec(v___x_4018_);
v___x_4021_ = lean_box(0);
v_isShared_4022_ = v_isSharedCheck_4026_;
goto v_resetjp_4020_;
}
v_resetjp_4020_:
{
lean_object* v___x_4024_; 
if (v_isShared_4022_ == 0)
{
v___x_4024_ = v___x_4021_;
goto v_reusejp_4023_;
}
else
{
lean_object* v_reuseFailAlloc_4025_; 
v_reuseFailAlloc_4025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4025_, 0, v_a_4019_);
v___x_4024_ = v_reuseFailAlloc_4025_;
goto v_reusejp_4023_;
}
v_reusejp_4023_:
{
return v___x_4024_;
}
}
}
}
else
{
lean_object* v_a_4027_; lean_object* v___x_4029_; uint8_t v_isShared_4030_; uint8_t v_isSharedCheck_4034_; 
lean_dec_ref(v___x_3988_);
lean_dec(v___x_3984_);
lean_dec_ref(v_snd_3959_);
lean_dec_ref(v_a_3958_);
lean_dec_ref(v_docCtx_3957_);
v_a_4027_ = lean_ctor_get(v___x_4013_, 0);
v_isSharedCheck_4034_ = !lean_is_exclusive(v___x_4013_);
if (v_isSharedCheck_4034_ == 0)
{
v___x_4029_ = v___x_4013_;
v_isShared_4030_ = v_isSharedCheck_4034_;
goto v_resetjp_4028_;
}
else
{
lean_inc(v_a_4027_);
lean_dec(v___x_4013_);
v___x_4029_ = lean_box(0);
v_isShared_4030_ = v_isSharedCheck_4034_;
goto v_resetjp_4028_;
}
v_resetjp_4028_:
{
lean_object* v___x_4032_; 
if (v_isShared_4030_ == 0)
{
v___x_4032_ = v___x_4029_;
goto v_reusejp_4031_;
}
else
{
lean_object* v_reuseFailAlloc_4033_; 
v_reuseFailAlloc_4033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4033_, 0, v_a_4027_);
v___x_4032_ = v_reuseFailAlloc_4033_;
goto v_reusejp_4031_;
}
v_reusejp_4031_:
{
return v___x_4032_;
}
}
}
}
else
{
lean_inc(v_a_3981_);
v_preDef_3990_ = v_a_3981_;
v___y_3991_ = v___y_3964_;
v___y_3992_ = v___y_3965_;
v___y_3993_ = v___y_3966_;
v___y_3994_ = v___y_3967_;
v___y_3995_ = v___y_3968_;
v___y_3996_ = v___y_3969_;
goto v___jp_3989_;
}
}
else
{
lean_object* v_a_4035_; lean_object* v___x_4037_; uint8_t v_isShared_4038_; uint8_t v_isSharedCheck_4042_; 
lean_dec_ref(v___x_3988_);
lean_dec(v___x_3984_);
lean_dec_ref(v_snd_3959_);
lean_dec_ref(v_a_3958_);
lean_dec_ref(v_docCtx_3957_);
v_a_4035_ = lean_ctor_get(v___x_4010_, 0);
v_isSharedCheck_4042_ = !lean_is_exclusive(v___x_4010_);
if (v_isSharedCheck_4042_ == 0)
{
v___x_4037_ = v___x_4010_;
v_isShared_4038_ = v_isSharedCheck_4042_;
goto v_resetjp_4036_;
}
else
{
lean_inc(v_a_4035_);
lean_dec(v___x_4010_);
v___x_4037_ = lean_box(0);
v_isShared_4038_ = v_isSharedCheck_4042_;
goto v_resetjp_4036_;
}
v_resetjp_4036_:
{
lean_object* v___x_4040_; 
if (v_isShared_4038_ == 0)
{
v___x_4040_ = v___x_4037_;
goto v_reusejp_4039_;
}
else
{
lean_object* v_reuseFailAlloc_4041_; 
v_reuseFailAlloc_4041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4041_, 0, v_a_4035_);
v___x_4040_ = v_reuseFailAlloc_4041_;
goto v_reusejp_4039_;
}
v_reusejp_4039_:
{
return v___x_4040_;
}
}
}
}
else
{
lean_inc(v_a_3981_);
v_preDef_3990_ = v_a_3981_;
v___y_3991_ = v___y_3964_;
v___y_3992_ = v___y_3965_;
v___y_3993_ = v___y_3966_;
v___y_3994_ = v___y_3967_;
v___y_3995_ = v___y_3968_;
v___y_3996_ = v___y_3969_;
goto v___jp_3989_;
}
v___jp_3989_:
{
lean_object* v___x_3997_; 
lean_inc_ref(v_docCtx_3957_);
v___x_3997_ = l_Lean_Elab_Structural_addSmartUnfoldingDef(v_docCtx_3957_, v_preDef_3990_, v___x_3984_, v___y_3991_, v___y_3992_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_);
if (lean_obj_tag(v___x_3997_) == 0)
{
size_t v___x_3998_; size_t v___x_3999_; 
lean_dec_ref_known(v___x_3997_, 1);
v___x_3998_ = ((size_t)1ULL);
v___x_3999_ = lean_usize_add(v_i_3962_, v___x_3998_);
v_i_3962_ = v___x_3999_;
v_b_3963_ = v___x_3988_;
goto _start;
}
else
{
lean_object* v_a_4001_; lean_object* v___x_4003_; uint8_t v_isShared_4004_; uint8_t v_isSharedCheck_4008_; 
lean_dec_ref(v___x_3988_);
lean_dec_ref(v_snd_3959_);
lean_dec_ref(v_a_3958_);
lean_dec_ref(v_docCtx_3957_);
v_a_4001_ = lean_ctor_get(v___x_3997_, 0);
v_isSharedCheck_4008_ = !lean_is_exclusive(v___x_3997_);
if (v_isSharedCheck_4008_ == 0)
{
v___x_4003_ = v___x_3997_;
v_isShared_4004_ = v_isSharedCheck_4008_;
goto v_resetjp_4002_;
}
else
{
lean_inc(v_a_4001_);
lean_dec(v___x_3997_);
v___x_4003_ = lean_box(0);
v_isShared_4004_ = v_isSharedCheck_4008_;
goto v_resetjp_4002_;
}
v_resetjp_4002_:
{
lean_object* v___x_4006_; 
if (v_isShared_4004_ == 0)
{
v___x_4006_ = v___x_4003_;
goto v_reusejp_4005_;
}
else
{
lean_object* v_reuseFailAlloc_4007_; 
v_reuseFailAlloc_4007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4007_, 0, v_a_4001_);
v___x_4006_ = v_reuseFailAlloc_4007_;
goto v_reusejp_4005_;
}
v_reusejp_4005_:
{
return v___x_4006_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__1___boxed(lean_object* v_docCtx_4048_, lean_object* v_a_4049_, lean_object* v_snd_4050_, lean_object* v_as_4051_, lean_object* v_sz_4052_, lean_object* v_i_4053_, lean_object* v_b_4054_, lean_object* v___y_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_){
_start:
{
size_t v_sz_boxed_4062_; size_t v_i_boxed_4063_; lean_object* v_res_4064_; 
v_sz_boxed_4062_ = lean_unbox_usize(v_sz_4052_);
lean_dec(v_sz_4052_);
v_i_boxed_4063_ = lean_unbox_usize(v_i_4053_);
lean_dec(v_i_4053_);
v_res_4064_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__1(v_docCtx_4048_, v_a_4049_, v_snd_4050_, v_as_4051_, v_sz_boxed_4062_, v_i_boxed_4063_, v_b_4054_, v___y_4055_, v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_, v___y_4060_);
lean_dec(v___y_4060_);
lean_dec_ref(v___y_4059_);
lean_dec(v___y_4058_);
lean_dec_ref(v___y_4057_);
lean_dec(v___y_4056_);
lean_dec_ref(v___y_4055_);
lean_dec_ref(v_as_4051_);
return v_res_4064_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4___redArg(lean_object* v_as_4065_, size_t v_sz_4066_, size_t v_i_4067_, lean_object* v_b_4068_, lean_object* v___y_4069_, lean_object* v___y_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_){
_start:
{
uint8_t v___x_4074_; 
v___x_4074_ = lean_usize_dec_lt(v_i_4067_, v_sz_4066_);
if (v___x_4074_ == 0)
{
lean_object* v___x_4075_; 
v___x_4075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4075_, 0, v_b_4068_);
return v___x_4075_;
}
else
{
lean_object* v_array_4076_; lean_object* v_start_4077_; lean_object* v_stop_4078_; uint8_t v___x_4079_; 
v_array_4076_ = lean_ctor_get(v_b_4068_, 0);
v_start_4077_ = lean_ctor_get(v_b_4068_, 1);
v_stop_4078_ = lean_ctor_get(v_b_4068_, 2);
v___x_4079_ = lean_nat_dec_lt(v_start_4077_, v_stop_4078_);
if (v___x_4079_ == 0)
{
lean_object* v___x_4080_; 
v___x_4080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4080_, 0, v_b_4068_);
return v___x_4080_;
}
else
{
lean_object* v___x_4082_; uint8_t v_isShared_4083_; uint8_t v_isSharedCheck_4103_; 
lean_inc(v_stop_4078_);
lean_inc(v_start_4077_);
lean_inc_ref(v_array_4076_);
v_isSharedCheck_4103_ = !lean_is_exclusive(v_b_4068_);
if (v_isSharedCheck_4103_ == 0)
{
lean_object* v_unused_4104_; lean_object* v_unused_4105_; lean_object* v_unused_4106_; 
v_unused_4104_ = lean_ctor_get(v_b_4068_, 2);
lean_dec(v_unused_4104_);
v_unused_4105_ = lean_ctor_get(v_b_4068_, 1);
lean_dec(v_unused_4105_);
v_unused_4106_ = lean_ctor_get(v_b_4068_, 0);
lean_dec(v_unused_4106_);
v___x_4082_ = v_b_4068_;
v_isShared_4083_ = v_isSharedCheck_4103_;
goto v_resetjp_4081_;
}
else
{
lean_dec(v_b_4068_);
v___x_4082_ = lean_box(0);
v_isShared_4083_ = v_isSharedCheck_4103_;
goto v_resetjp_4081_;
}
v_resetjp_4081_:
{
lean_object* v_a_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; 
v_a_4084_ = lean_array_uget_borrowed(v_as_4065_, v_i_4067_);
v___x_4085_ = lean_array_fget_borrowed(v_array_4076_, v_start_4077_);
lean_inc(v_a_4084_);
lean_inc(v___x_4085_);
v___x_4086_ = l_Lean_Elab_Structural_reportTermMeasure(v___x_4085_, v_a_4084_, v___y_4069_, v___y_4070_, v___y_4071_, v___y_4072_);
if (lean_obj_tag(v___x_4086_) == 0)
{
lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4090_; 
lean_dec_ref_known(v___x_4086_, 1);
v___x_4087_ = lean_unsigned_to_nat(1u);
v___x_4088_ = lean_nat_add(v_start_4077_, v___x_4087_);
lean_dec(v_start_4077_);
if (v_isShared_4083_ == 0)
{
lean_ctor_set(v___x_4082_, 1, v___x_4088_);
v___x_4090_ = v___x_4082_;
goto v_reusejp_4089_;
}
else
{
lean_object* v_reuseFailAlloc_4094_; 
v_reuseFailAlloc_4094_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4094_, 0, v_array_4076_);
lean_ctor_set(v_reuseFailAlloc_4094_, 1, v___x_4088_);
lean_ctor_set(v_reuseFailAlloc_4094_, 2, v_stop_4078_);
v___x_4090_ = v_reuseFailAlloc_4094_;
goto v_reusejp_4089_;
}
v_reusejp_4089_:
{
size_t v___x_4091_; size_t v___x_4092_; 
v___x_4091_ = ((size_t)1ULL);
v___x_4092_ = lean_usize_add(v_i_4067_, v___x_4091_);
v_i_4067_ = v___x_4092_;
v_b_4068_ = v___x_4090_;
goto _start;
}
}
else
{
lean_object* v_a_4095_; lean_object* v___x_4097_; uint8_t v_isShared_4098_; uint8_t v_isSharedCheck_4102_; 
lean_del_object(v___x_4082_);
lean_dec(v_stop_4078_);
lean_dec(v_start_4077_);
lean_dec_ref(v_array_4076_);
v_a_4095_ = lean_ctor_get(v___x_4086_, 0);
v_isSharedCheck_4102_ = !lean_is_exclusive(v___x_4086_);
if (v_isSharedCheck_4102_ == 0)
{
v___x_4097_ = v___x_4086_;
v_isShared_4098_ = v_isSharedCheck_4102_;
goto v_resetjp_4096_;
}
else
{
lean_inc(v_a_4095_);
lean_dec(v___x_4086_);
v___x_4097_ = lean_box(0);
v_isShared_4098_ = v_isSharedCheck_4102_;
goto v_resetjp_4096_;
}
v_resetjp_4096_:
{
lean_object* v___x_4100_; 
if (v_isShared_4098_ == 0)
{
v___x_4100_ = v___x_4097_;
goto v_reusejp_4099_;
}
else
{
lean_object* v_reuseFailAlloc_4101_; 
v_reuseFailAlloc_4101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4101_, 0, v_a_4095_);
v___x_4100_ = v_reuseFailAlloc_4101_;
goto v_reusejp_4099_;
}
v_reusejp_4099_:
{
return v___x_4100_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4___redArg___boxed(lean_object* v_as_4107_, lean_object* v_sz_4108_, lean_object* v_i_4109_, lean_object* v_b_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_){
_start:
{
size_t v_sz_boxed_4116_; size_t v_i_boxed_4117_; lean_object* v_res_4118_; 
v_sz_boxed_4116_ = lean_unbox_usize(v_sz_4108_);
lean_dec(v_sz_4108_);
v_i_boxed_4117_ = lean_unbox_usize(v_i_4109_);
lean_dec(v_i_4109_);
v_res_4118_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4___redArg(v_as_4107_, v_sz_boxed_4116_, v_i_boxed_4117_, v_b_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_);
lean_dec(v___y_4114_);
lean_dec_ref(v___y_4113_);
lean_dec(v___y_4112_);
lean_dec_ref(v___y_4111_);
lean_dec_ref(v_as_4107_);
return v_res_4118_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___lam__0(lean_object* v___x_4119_, lean_object* v_e_4120_){
_start:
{
lean_object* v___x_4121_; lean_object* v___x_4122_; 
v___x_4121_ = l_Lean_indentD(v_e_4120_);
v___x_4122_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4122_, 0, v___x_4119_);
lean_ctor_set(v___x_4122_, 1, v___x_4121_);
return v___x_4122_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___lam__1(lean_object* v_docCtx_4123_, lean_object* v_a_4124_, uint8_t v___x_4125_, lean_object* v___x_4126_, uint8_t v___x_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_){
_start:
{
lean_object* v___x_4135_; 
v___x_4135_ = l_Lean_Elab_addNonRec(v_docCtx_4123_, v_a_4124_, v___x_4125_, v___x_4126_, v___x_4127_, v___x_4125_, v___x_4127_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_, v___y_4132_, v___y_4133_);
return v___x_4135_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___lam__1___boxed(lean_object* v_docCtx_4136_, lean_object* v_a_4137_, lean_object* v___x_4138_, lean_object* v___x_4139_, lean_object* v___x_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_){
_start:
{
uint8_t v___x_9634__boxed_4148_; uint8_t v___x_9636__boxed_4149_; lean_object* v_res_4150_; 
v___x_9634__boxed_4148_ = lean_unbox(v___x_4138_);
v___x_9636__boxed_4149_ = lean_unbox(v___x_4140_);
v_res_4150_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___lam__1(v_docCtx_4136_, v_a_4137_, v___x_9634__boxed_4148_, v___x_4139_, v___x_9636__boxed_4149_, v___y_4141_, v___y_4142_, v___y_4143_, v___y_4144_, v___y_4145_, v___y_4146_);
lean_dec(v___y_4146_);
lean_dec_ref(v___y_4145_);
lean_dec(v___y_4144_);
lean_dec_ref(v___y_4143_);
lean_dec(v___y_4142_);
lean_dec_ref(v___y_4141_);
return v_res_4150_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__1(void){
_start:
{
lean_object* v___x_4152_; lean_object* v___x_4153_; 
v___x_4152_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__0));
v___x_4153_ = l_Lean_stringToMessageData(v___x_4152_);
return v___x_4153_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__2(void){
_start:
{
lean_object* v___x_4154_; lean_object* v___f_4155_; 
v___x_4154_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__1);
v___f_4155_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___lam__0), 2, 1);
lean_closure_set(v___f_4155_, 0, v___x_4154_);
return v___f_4155_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5(lean_object* v_names_4156_, lean_object* v_docCtx_4157_, lean_object* v_as_4158_, size_t v_i_4159_, size_t v_stop_4160_, lean_object* v_b_4161_, lean_object* v___y_4162_, lean_object* v___y_4163_, lean_object* v___y_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_){
_start:
{
uint8_t v___x_4169_; 
v___x_4169_ = lean_usize_dec_eq(v_i_4159_, v_stop_4160_);
if (v___x_4169_ == 0)
{
lean_object* v___x_4170_; lean_object* v___x_4171_; 
v___x_4170_ = lean_array_uget_borrowed(v_as_4158_, v_i_4159_);
lean_inc(v___x_4170_);
v___x_4171_ = l_Lean_Elab_eraseRecAppSyntax(v___x_4170_, v___y_4166_, v___y_4167_);
if (lean_obj_tag(v___x_4171_) == 0)
{
lean_object* v_a_4172_; lean_object* v___f_4173_; lean_object* v___x_4174_; uint8_t v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___f_4178_; lean_object* v___x_4179_; 
v_a_4172_ = lean_ctor_get(v___x_4171_, 0);
lean_inc(v_a_4172_);
lean_dec_ref_known(v___x_4171_, 1);
v___f_4173_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__2);
lean_inc_ref(v_names_4156_);
v___x_4174_ = lean_array_to_list(v_names_4156_);
v___x_4175_ = 1;
v___x_4176_ = lean_box(v___x_4169_);
v___x_4177_ = lean_box(v___x_4175_);
lean_inc(v___y_4163_);
lean_inc_ref(v___y_4162_);
lean_inc_ref(v_docCtx_4157_);
v___f_4178_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___lam__1___boxed), 12, 7);
lean_closure_set(v___f_4178_, 0, v_docCtx_4157_);
lean_closure_set(v___f_4178_, 1, v_a_4172_);
lean_closure_set(v___f_4178_, 2, v___x_4176_);
lean_closure_set(v___f_4178_, 3, v___x_4174_);
lean_closure_set(v___f_4178_, 4, v___x_4177_);
lean_closure_set(v___f_4178_, 5, v___y_4162_);
lean_closure_set(v___f_4178_, 6, v___y_4163_);
v___x_4179_ = l_Lean_Meta_mapErrorImp___redArg(v___f_4178_, v___f_4173_, v___y_4164_, v___y_4165_, v___y_4166_, v___y_4167_);
if (lean_obj_tag(v___x_4179_) == 0)
{
if (lean_obj_tag(v___x_4179_) == 0)
{
lean_object* v_a_4180_; size_t v___x_4181_; size_t v___x_4182_; 
v_a_4180_ = lean_ctor_get(v___x_4179_, 0);
lean_inc(v_a_4180_);
lean_dec_ref_known(v___x_4179_, 1);
v___x_4181_ = ((size_t)1ULL);
v___x_4182_ = lean_usize_add(v_i_4159_, v___x_4181_);
v_i_4159_ = v___x_4182_;
v_b_4161_ = v_a_4180_;
goto _start;
}
else
{
lean_dec_ref(v_docCtx_4157_);
lean_dec_ref(v_names_4156_);
return v___x_4179_;
}
}
else
{
lean_object* v_a_4184_; lean_object* v___x_4186_; uint8_t v_isShared_4187_; uint8_t v_isSharedCheck_4191_; 
lean_dec_ref(v_docCtx_4157_);
lean_dec_ref(v_names_4156_);
v_a_4184_ = lean_ctor_get(v___x_4179_, 0);
v_isSharedCheck_4191_ = !lean_is_exclusive(v___x_4179_);
if (v_isSharedCheck_4191_ == 0)
{
v___x_4186_ = v___x_4179_;
v_isShared_4187_ = v_isSharedCheck_4191_;
goto v_resetjp_4185_;
}
else
{
lean_inc(v_a_4184_);
lean_dec(v___x_4179_);
v___x_4186_ = lean_box(0);
v_isShared_4187_ = v_isSharedCheck_4191_;
goto v_resetjp_4185_;
}
v_resetjp_4185_:
{
lean_object* v___x_4189_; 
if (v_isShared_4187_ == 0)
{
v___x_4189_ = v___x_4186_;
goto v_reusejp_4188_;
}
else
{
lean_object* v_reuseFailAlloc_4190_; 
v_reuseFailAlloc_4190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4190_, 0, v_a_4184_);
v___x_4189_ = v_reuseFailAlloc_4190_;
goto v_reusejp_4188_;
}
v_reusejp_4188_:
{
return v___x_4189_;
}
}
}
}
else
{
lean_object* v_a_4192_; lean_object* v___x_4194_; uint8_t v_isShared_4195_; uint8_t v_isSharedCheck_4199_; 
lean_dec_ref(v_docCtx_4157_);
lean_dec_ref(v_names_4156_);
v_a_4192_ = lean_ctor_get(v___x_4171_, 0);
v_isSharedCheck_4199_ = !lean_is_exclusive(v___x_4171_);
if (v_isSharedCheck_4199_ == 0)
{
v___x_4194_ = v___x_4171_;
v_isShared_4195_ = v_isSharedCheck_4199_;
goto v_resetjp_4193_;
}
else
{
lean_inc(v_a_4192_);
lean_dec(v___x_4171_);
v___x_4194_ = lean_box(0);
v_isShared_4195_ = v_isSharedCheck_4199_;
goto v_resetjp_4193_;
}
v_resetjp_4193_:
{
lean_object* v___x_4197_; 
if (v_isShared_4195_ == 0)
{
v___x_4197_ = v___x_4194_;
goto v_reusejp_4196_;
}
else
{
lean_object* v_reuseFailAlloc_4198_; 
v_reuseFailAlloc_4198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4198_, 0, v_a_4192_);
v___x_4197_ = v_reuseFailAlloc_4198_;
goto v_reusejp_4196_;
}
v_reusejp_4196_:
{
return v___x_4197_;
}
}
}
}
else
{
lean_object* v___x_4200_; 
lean_dec_ref(v_docCtx_4157_);
lean_dec_ref(v_names_4156_);
v___x_4200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4200_, 0, v_b_4161_);
return v___x_4200_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___boxed(lean_object* v_names_4201_, lean_object* v_docCtx_4202_, lean_object* v_as_4203_, lean_object* v_i_4204_, lean_object* v_stop_4205_, lean_object* v_b_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_){
_start:
{
size_t v_i_boxed_4214_; size_t v_stop_boxed_4215_; lean_object* v_res_4216_; 
v_i_boxed_4214_ = lean_unbox_usize(v_i_4204_);
lean_dec(v_i_4204_);
v_stop_boxed_4215_ = lean_unbox_usize(v_stop_4205_);
lean_dec(v_stop_4205_);
v_res_4216_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5(v_names_4201_, v_docCtx_4202_, v_as_4203_, v_i_boxed_4214_, v_stop_boxed_4215_, v_b_4206_, v___y_4207_, v___y_4208_, v___y_4209_, v___y_4210_, v___y_4211_, v___y_4212_);
lean_dec(v___y_4212_);
lean_dec_ref(v___y_4211_);
lean_dec(v___y_4210_);
lean_dec_ref(v___y_4209_);
lean_dec(v___y_4208_);
lean_dec_ref(v___y_4207_);
lean_dec_ref(v_as_4203_);
return v_res_4216_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___redArg(size_t v_sz_4217_, size_t v_i_4218_, lean_object* v_bs_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_){
_start:
{
uint8_t v___x_4223_; 
v___x_4223_ = lean_usize_dec_lt(v_i_4218_, v_sz_4217_);
if (v___x_4223_ == 0)
{
lean_object* v___x_4224_; 
v___x_4224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4224_, 0, v_bs_4219_);
return v___x_4224_;
}
else
{
lean_object* v_v_4225_; lean_object* v___x_4226_; 
v_v_4225_ = lean_array_uget_borrowed(v_bs_4219_, v_i_4218_);
lean_inc(v_v_4225_);
v___x_4226_ = l_Lean_Elab_eraseRecAppSyntax(v_v_4225_, v___y_4220_, v___y_4221_);
if (lean_obj_tag(v___x_4226_) == 0)
{
lean_object* v_a_4227_; lean_object* v___x_4228_; lean_object* v_bs_x27_4229_; size_t v___x_4230_; size_t v___x_4231_; lean_object* v___x_4232_; 
v_a_4227_ = lean_ctor_get(v___x_4226_, 0);
lean_inc(v_a_4227_);
lean_dec_ref_known(v___x_4226_, 1);
v___x_4228_ = lean_unsigned_to_nat(0u);
v_bs_x27_4229_ = lean_array_uset(v_bs_4219_, v_i_4218_, v___x_4228_);
v___x_4230_ = ((size_t)1ULL);
v___x_4231_ = lean_usize_add(v_i_4218_, v___x_4230_);
v___x_4232_ = lean_array_uset(v_bs_x27_4229_, v_i_4218_, v_a_4227_);
v_i_4218_ = v___x_4231_;
v_bs_4219_ = v___x_4232_;
goto _start;
}
else
{
lean_object* v_a_4234_; lean_object* v___x_4236_; uint8_t v_isShared_4237_; uint8_t v_isSharedCheck_4241_; 
lean_dec_ref(v_bs_4219_);
v_a_4234_ = lean_ctor_get(v___x_4226_, 0);
v_isSharedCheck_4241_ = !lean_is_exclusive(v___x_4226_);
if (v_isSharedCheck_4241_ == 0)
{
v___x_4236_ = v___x_4226_;
v_isShared_4237_ = v_isSharedCheck_4241_;
goto v_resetjp_4235_;
}
else
{
lean_inc(v_a_4234_);
lean_dec(v___x_4226_);
v___x_4236_ = lean_box(0);
v_isShared_4237_ = v_isSharedCheck_4241_;
goto v_resetjp_4235_;
}
v_resetjp_4235_:
{
lean_object* v___x_4239_; 
if (v_isShared_4237_ == 0)
{
v___x_4239_ = v___x_4236_;
goto v_reusejp_4238_;
}
else
{
lean_object* v_reuseFailAlloc_4240_; 
v_reuseFailAlloc_4240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4240_, 0, v_a_4234_);
v___x_4239_ = v_reuseFailAlloc_4240_;
goto v_reusejp_4238_;
}
v_reusejp_4238_:
{
return v___x_4239_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___redArg___boxed(lean_object* v_sz_4242_, lean_object* v_i_4243_, lean_object* v_bs_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_){
_start:
{
size_t v_sz_boxed_4248_; size_t v_i_boxed_4249_; lean_object* v_res_4250_; 
v_sz_boxed_4248_ = lean_unbox_usize(v_sz_4242_);
lean_dec(v_sz_4242_);
v_i_boxed_4249_ = lean_unbox_usize(v_i_4243_);
lean_dec(v_i_4243_);
v_res_4250_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___redArg(v_sz_boxed_4248_, v_i_boxed_4249_, v_bs_4244_, v___y_4245_, v___y_4246_);
lean_dec(v___y_4246_);
lean_dec_ref(v___y_4245_);
return v_res_4250_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___redArg(lean_object* v_as_4251_, size_t v_sz_4252_, size_t v_i_4253_, lean_object* v_b_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_){
_start:
{
uint8_t v___x_4258_; 
v___x_4258_ = lean_usize_dec_lt(v_i_4253_, v_sz_4252_);
if (v___x_4258_ == 0)
{
lean_object* v___x_4259_; 
v___x_4259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4259_, 0, v_b_4254_);
return v___x_4259_;
}
else
{
lean_object* v_a_4260_; lean_object* v_declName_4261_; lean_object* v___x_4262_; 
v_a_4260_ = lean_array_uget_borrowed(v_as_4251_, v_i_4253_);
v_declName_4261_ = lean_ctor_get(v_a_4260_, 3);
lean_inc(v_declName_4261_);
v___x_4262_ = l_Lean_enableRealizationsForConst(v_declName_4261_, v___y_4255_, v___y_4256_);
if (lean_obj_tag(v___x_4262_) == 0)
{
lean_object* v___x_4263_; size_t v___x_4264_; size_t v___x_4265_; 
lean_dec_ref_known(v___x_4262_, 1);
v___x_4263_ = lean_box(0);
v___x_4264_ = ((size_t)1ULL);
v___x_4265_ = lean_usize_add(v_i_4253_, v___x_4264_);
v_i_4253_ = v___x_4265_;
v_b_4254_ = v___x_4263_;
goto _start;
}
else
{
return v___x_4262_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___redArg___boxed(lean_object* v_as_4267_, lean_object* v_sz_4268_, lean_object* v_i_4269_, lean_object* v_b_4270_, lean_object* v___y_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_){
_start:
{
size_t v_sz_boxed_4274_; size_t v_i_boxed_4275_; lean_object* v_res_4276_; 
v_sz_boxed_4274_ = lean_unbox_usize(v_sz_4268_);
lean_dec(v_sz_4268_);
v_i_boxed_4275_ = lean_unbox_usize(v_i_4269_);
lean_dec(v_i_4269_);
v_res_4276_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___redArg(v_as_4267_, v_sz_boxed_4274_, v_i_boxed_4275_, v_b_4270_, v___y_4271_, v___y_4272_);
lean_dec(v___y_4272_);
lean_dec_ref(v___y_4271_);
lean_dec_ref(v_as_4267_);
return v_res_4276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_structuralRecursion(lean_object* v_docCtx_4277_, lean_object* v_preDefs_4278_, lean_object* v_termMeasure_x3fs_4279_, lean_object* v_a_4280_, lean_object* v_a_4281_, lean_object* v_a_4282_, lean_object* v_a_4283_, lean_object* v_a_4284_, lean_object* v_a_4285_){
_start:
{
size_t v_sz_4287_; size_t v___x_4288_; lean_object* v_names_4289_; lean_object* v___x_4290_; 
v_sz_4287_ = lean_array_size(v_preDefs_4278_);
v___x_4288_ = ((size_t)0ULL);
lean_inc_ref_n(v_preDefs_4278_, 2);
v_names_4289_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0(v_sz_4287_, v___x_4288_, v_preDefs_4278_);
v___x_4290_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos(v_preDefs_4278_, v_termMeasure_x3fs_4279_, v_a_4282_, v_a_4283_, v_a_4284_, v_a_4285_);
if (lean_obj_tag(v___x_4290_) == 0)
{
lean_object* v_a_4291_; lean_object* v_snd_4292_; lean_object* v_fst_4293_; lean_object* v_fst_4294_; lean_object* v_snd_4295_; lean_object* v___y_4327_; lean_object* v___x_4328_; lean_object* v___x_4329_; lean_object* v___x_4330_; size_t v_sz_4331_; lean_object* v___x_4332_; 
v_a_4291_ = lean_ctor_get(v___x_4290_, 0);
lean_inc(v_a_4291_);
lean_dec_ref_known(v___x_4290_, 1);
v_snd_4292_ = lean_ctor_get(v_a_4291_, 1);
lean_inc(v_snd_4292_);
v_fst_4293_ = lean_ctor_get(v_a_4291_, 0);
lean_inc(v_fst_4293_);
lean_dec(v_a_4291_);
v_fst_4294_ = lean_ctor_get(v_snd_4292_, 0);
lean_inc(v_fst_4294_);
v_snd_4295_ = lean_ctor_get(v_snd_4292_, 1);
lean_inc(v_snd_4295_);
lean_dec(v_snd_4292_);
v___x_4328_ = lean_unsigned_to_nat(0u);
v___x_4329_ = lean_array_get_size(v_preDefs_4278_);
lean_inc_ref(v_preDefs_4278_);
v___x_4330_ = l_Array_toSubarray___redArg(v_preDefs_4278_, v___x_4328_, v___x_4329_);
v_sz_4331_ = lean_array_size(v_fst_4293_);
v___x_4332_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4___redArg(v_fst_4293_, v_sz_4331_, v___x_4288_, v___x_4330_, v_a_4282_, v_a_4283_, v_a_4284_, v_a_4285_);
if (lean_obj_tag(v___x_4332_) == 0)
{
lean_object* v___x_4333_; uint8_t v___x_4334_; 
lean_dec_ref_known(v___x_4332_, 1);
v___x_4333_ = lean_array_get_size(v_fst_4294_);
v___x_4334_ = lean_nat_dec_lt(v___x_4328_, v___x_4333_);
if (v___x_4334_ == 0)
{
lean_dec_ref(v_names_4289_);
goto v___jp_4296_;
}
else
{
lean_object* v___x_4335_; uint8_t v___x_4336_; 
v___x_4335_ = lean_box(0);
v___x_4336_ = lean_nat_dec_le(v___x_4333_, v___x_4333_);
if (v___x_4336_ == 0)
{
if (v___x_4334_ == 0)
{
lean_dec_ref(v_names_4289_);
goto v___jp_4296_;
}
else
{
size_t v___x_4337_; lean_object* v___x_4338_; 
v___x_4337_ = lean_usize_of_nat(v___x_4333_);
lean_inc_ref(v_docCtx_4277_);
v___x_4338_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5(v_names_4289_, v_docCtx_4277_, v_fst_4294_, v___x_4288_, v___x_4337_, v___x_4335_, v_a_4280_, v_a_4281_, v_a_4282_, v_a_4283_, v_a_4284_, v_a_4285_);
v___y_4327_ = v___x_4338_;
goto v___jp_4326_;
}
}
else
{
size_t v___x_4339_; lean_object* v___x_4340_; 
v___x_4339_ = lean_usize_of_nat(v___x_4333_);
lean_inc_ref(v_docCtx_4277_);
v___x_4340_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5(v_names_4289_, v_docCtx_4277_, v_fst_4294_, v___x_4288_, v___x_4339_, v___x_4335_, v_a_4280_, v_a_4281_, v_a_4282_, v_a_4283_, v_a_4284_, v_a_4285_);
v___y_4327_ = v___x_4340_;
goto v___jp_4326_;
}
}
}
else
{
lean_object* v_a_4341_; lean_object* v___x_4343_; uint8_t v_isShared_4344_; uint8_t v_isSharedCheck_4348_; 
lean_dec(v_snd_4295_);
lean_dec(v_fst_4294_);
lean_dec(v_fst_4293_);
lean_dec_ref(v_names_4289_);
lean_dec_ref(v_preDefs_4278_);
lean_dec_ref(v_docCtx_4277_);
v_a_4341_ = lean_ctor_get(v___x_4332_, 0);
v_isSharedCheck_4348_ = !lean_is_exclusive(v___x_4332_);
if (v_isSharedCheck_4348_ == 0)
{
v___x_4343_ = v___x_4332_;
v_isShared_4344_ = v_isSharedCheck_4348_;
goto v_resetjp_4342_;
}
else
{
lean_inc(v_a_4341_);
lean_dec(v___x_4332_);
v___x_4343_ = lean_box(0);
v_isShared_4344_ = v_isSharedCheck_4348_;
goto v_resetjp_4342_;
}
v_resetjp_4342_:
{
lean_object* v___x_4346_; 
if (v_isShared_4344_ == 0)
{
v___x_4346_ = v___x_4343_;
goto v_reusejp_4345_;
}
else
{
lean_object* v_reuseFailAlloc_4347_; 
v_reuseFailAlloc_4347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4347_, 0, v_a_4341_);
v___x_4346_ = v_reuseFailAlloc_4347_;
goto v_reusejp_4345_;
}
v_reusejp_4345_:
{
return v___x_4346_;
}
}
}
v___jp_4296_:
{
lean_object* v___x_4297_; 
v___x_4297_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___redArg(v_sz_4287_, v___x_4288_, v_preDefs_4278_, v_a_4284_, v_a_4285_);
if (lean_obj_tag(v___x_4297_) == 0)
{
lean_object* v_a_4298_; lean_object* v___x_4299_; 
v_a_4298_ = lean_ctor_get(v___x_4297_, 0);
lean_inc_n(v_a_4298_, 2);
lean_dec_ref_known(v___x_4297_, 1);
lean_inc_ref(v_docCtx_4277_);
v___x_4299_ = l_Lean_Elab_addAndCompilePartialRec(v_docCtx_4277_, v_a_4298_, v_a_4280_, v_a_4281_, v_a_4282_, v_a_4283_, v_a_4284_, v_a_4285_);
if (lean_obj_tag(v___x_4299_) == 0)
{
lean_object* v___x_4300_; lean_object* v___x_4301_; lean_object* v___x_4302_; size_t v_sz_4303_; lean_object* v___x_4304_; 
lean_dec_ref_known(v___x_4299_, 1);
v___x_4300_ = lean_unsigned_to_nat(0u);
v___x_4301_ = lean_array_get_size(v_fst_4293_);
v___x_4302_ = l_Array_toSubarray___redArg(v_fst_4293_, v___x_4300_, v___x_4301_);
v_sz_4303_ = lean_array_size(v_a_4298_);
lean_inc(v_a_4298_);
v___x_4304_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__1(v_docCtx_4277_, v_a_4298_, v_snd_4295_, v_a_4298_, v_sz_4303_, v___x_4288_, v___x_4302_, v_a_4280_, v_a_4281_, v_a_4282_, v_a_4283_, v_a_4284_, v_a_4285_);
if (lean_obj_tag(v___x_4304_) == 0)
{
lean_object* v___x_4305_; lean_object* v___x_4306_; 
lean_dec_ref_known(v___x_4304_, 1);
v___x_4305_ = lean_box(0);
v___x_4306_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___redArg(v_a_4298_, v_sz_4303_, v___x_4288_, v___x_4305_, v_a_4282_, v_a_4283_, v_a_4284_, v_a_4285_);
if (lean_obj_tag(v___x_4306_) == 0)
{
lean_object* v___x_4307_; 
lean_dec_ref_known(v___x_4306_, 1);
v___x_4307_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___redArg(v_a_4298_, v_sz_4303_, v___x_4288_, v___x_4305_, v_a_4284_, v_a_4285_);
lean_dec(v_a_4298_);
if (lean_obj_tag(v___x_4307_) == 0)
{
uint8_t v___x_4308_; lean_object* v___x_4309_; 
lean_dec_ref_known(v___x_4307_, 1);
v___x_4308_ = 1;
v___x_4309_ = l_Lean_Elab_applyAttributesOf(v_fst_4294_, v___x_4308_, v_a_4280_, v_a_4281_, v_a_4282_, v_a_4283_, v_a_4284_, v_a_4285_);
lean_dec(v_fst_4294_);
return v___x_4309_;
}
else
{
lean_dec(v_fst_4294_);
return v___x_4307_;
}
}
else
{
lean_dec(v_a_4298_);
lean_dec(v_fst_4294_);
return v___x_4306_;
}
}
else
{
lean_object* v_a_4310_; lean_object* v___x_4312_; uint8_t v_isShared_4313_; uint8_t v_isSharedCheck_4317_; 
lean_dec(v_a_4298_);
lean_dec(v_fst_4294_);
v_a_4310_ = lean_ctor_get(v___x_4304_, 0);
v_isSharedCheck_4317_ = !lean_is_exclusive(v___x_4304_);
if (v_isSharedCheck_4317_ == 0)
{
v___x_4312_ = v___x_4304_;
v_isShared_4313_ = v_isSharedCheck_4317_;
goto v_resetjp_4311_;
}
else
{
lean_inc(v_a_4310_);
lean_dec(v___x_4304_);
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
}
else
{
lean_dec(v_a_4298_);
lean_dec(v_snd_4295_);
lean_dec(v_fst_4294_);
lean_dec(v_fst_4293_);
lean_dec_ref(v_docCtx_4277_);
return v___x_4299_;
}
}
else
{
lean_object* v_a_4318_; lean_object* v___x_4320_; uint8_t v_isShared_4321_; uint8_t v_isSharedCheck_4325_; 
lean_dec(v_snd_4295_);
lean_dec(v_fst_4294_);
lean_dec(v_fst_4293_);
lean_dec_ref(v_docCtx_4277_);
v_a_4318_ = lean_ctor_get(v___x_4297_, 0);
v_isSharedCheck_4325_ = !lean_is_exclusive(v___x_4297_);
if (v_isSharedCheck_4325_ == 0)
{
v___x_4320_ = v___x_4297_;
v_isShared_4321_ = v_isSharedCheck_4325_;
goto v_resetjp_4319_;
}
else
{
lean_inc(v_a_4318_);
lean_dec(v___x_4297_);
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
v___jp_4326_:
{
if (lean_obj_tag(v___y_4327_) == 0)
{
lean_dec_ref_known(v___y_4327_, 1);
goto v___jp_4296_;
}
else
{
lean_dec(v_snd_4295_);
lean_dec(v_fst_4294_);
lean_dec(v_fst_4293_);
lean_dec_ref(v_preDefs_4278_);
lean_dec_ref(v_docCtx_4277_);
return v___y_4327_;
}
}
}
else
{
lean_object* v_a_4349_; lean_object* v___x_4351_; uint8_t v_isShared_4352_; uint8_t v_isSharedCheck_4356_; 
lean_dec_ref(v_names_4289_);
lean_dec_ref(v_preDefs_4278_);
lean_dec_ref(v_docCtx_4277_);
v_a_4349_ = lean_ctor_get(v___x_4290_, 0);
v_isSharedCheck_4356_ = !lean_is_exclusive(v___x_4290_);
if (v_isSharedCheck_4356_ == 0)
{
v___x_4351_ = v___x_4290_;
v_isShared_4352_ = v_isSharedCheck_4356_;
goto v_resetjp_4350_;
}
else
{
lean_inc(v_a_4349_);
lean_dec(v___x_4290_);
v___x_4351_ = lean_box(0);
v_isShared_4352_ = v_isSharedCheck_4356_;
goto v_resetjp_4350_;
}
v_resetjp_4350_:
{
lean_object* v___x_4354_; 
if (v_isShared_4352_ == 0)
{
v___x_4354_ = v___x_4351_;
goto v_reusejp_4353_;
}
else
{
lean_object* v_reuseFailAlloc_4355_; 
v_reuseFailAlloc_4355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4355_, 0, v_a_4349_);
v___x_4354_ = v_reuseFailAlloc_4355_;
goto v_reusejp_4353_;
}
v_reusejp_4353_:
{
return v___x_4354_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_structuralRecursion___boxed(lean_object* v_docCtx_4357_, lean_object* v_preDefs_4358_, lean_object* v_termMeasure_x3fs_4359_, lean_object* v_a_4360_, lean_object* v_a_4361_, lean_object* v_a_4362_, lean_object* v_a_4363_, lean_object* v_a_4364_, lean_object* v_a_4365_, lean_object* v_a_4366_){
_start:
{
lean_object* v_res_4367_; 
v_res_4367_ = l_Lean_Elab_Structural_structuralRecursion(v_docCtx_4357_, v_preDefs_4358_, v_termMeasure_x3fs_4359_, v_a_4360_, v_a_4361_, v_a_4362_, v_a_4363_, v_a_4364_, v_a_4365_);
lean_dec(v_a_4365_);
lean_dec_ref(v_a_4364_);
lean_dec(v_a_4363_);
lean_dec_ref(v_a_4362_);
lean_dec(v_a_4361_);
lean_dec_ref(v_a_4360_);
return v_res_4367_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0(size_t v_sz_4368_, size_t v_i_4369_, lean_object* v_bs_4370_, lean_object* v___y_4371_, lean_object* v___y_4372_, lean_object* v___y_4373_, lean_object* v___y_4374_, lean_object* v___y_4375_, lean_object* v___y_4376_){
_start:
{
lean_object* v___x_4378_; 
v___x_4378_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___redArg(v_sz_4368_, v_i_4369_, v_bs_4370_, v___y_4375_, v___y_4376_);
return v___x_4378_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___boxed(lean_object* v_sz_4379_, lean_object* v_i_4380_, lean_object* v_bs_4381_, lean_object* v___y_4382_, lean_object* v___y_4383_, lean_object* v___y_4384_, lean_object* v___y_4385_, lean_object* v___y_4386_, lean_object* v___y_4387_, lean_object* v___y_4388_){
_start:
{
size_t v_sz_boxed_4389_; size_t v_i_boxed_4390_; lean_object* v_res_4391_; 
v_sz_boxed_4389_ = lean_unbox_usize(v_sz_4379_);
lean_dec(v_sz_4379_);
v_i_boxed_4390_ = lean_unbox_usize(v_i_4380_);
lean_dec(v_i_4380_);
v_res_4391_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0(v_sz_boxed_4389_, v_i_boxed_4390_, v_bs_4381_, v___y_4382_, v___y_4383_, v___y_4384_, v___y_4385_, v___y_4386_, v___y_4387_);
lean_dec(v___y_4387_);
lean_dec_ref(v___y_4386_);
lean_dec(v___y_4385_);
lean_dec_ref(v___y_4384_);
lean_dec(v___y_4383_);
lean_dec_ref(v___y_4382_);
return v_res_4391_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2(lean_object* v_as_4392_, size_t v_sz_4393_, size_t v_i_4394_, lean_object* v_b_4395_, lean_object* v___y_4396_, lean_object* v___y_4397_, lean_object* v___y_4398_, lean_object* v___y_4399_, lean_object* v___y_4400_, lean_object* v___y_4401_){
_start:
{
lean_object* v___x_4403_; 
v___x_4403_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___redArg(v_as_4392_, v_sz_4393_, v_i_4394_, v_b_4395_, v___y_4398_, v___y_4399_, v___y_4400_, v___y_4401_);
return v___x_4403_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___boxed(lean_object* v_as_4404_, lean_object* v_sz_4405_, lean_object* v_i_4406_, lean_object* v_b_4407_, lean_object* v___y_4408_, lean_object* v___y_4409_, lean_object* v___y_4410_, lean_object* v___y_4411_, lean_object* v___y_4412_, lean_object* v___y_4413_, lean_object* v___y_4414_){
_start:
{
size_t v_sz_boxed_4415_; size_t v_i_boxed_4416_; lean_object* v_res_4417_; 
v_sz_boxed_4415_ = lean_unbox_usize(v_sz_4405_);
lean_dec(v_sz_4405_);
v_i_boxed_4416_ = lean_unbox_usize(v_i_4406_);
lean_dec(v_i_4406_);
v_res_4417_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2(v_as_4404_, v_sz_boxed_4415_, v_i_boxed_4416_, v_b_4407_, v___y_4408_, v___y_4409_, v___y_4410_, v___y_4411_, v___y_4412_, v___y_4413_);
lean_dec(v___y_4413_);
lean_dec_ref(v___y_4412_);
lean_dec(v___y_4411_);
lean_dec_ref(v___y_4410_);
lean_dec(v___y_4409_);
lean_dec_ref(v___y_4408_);
lean_dec_ref(v_as_4404_);
return v_res_4417_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3(lean_object* v_as_4418_, size_t v_sz_4419_, size_t v_i_4420_, lean_object* v_b_4421_, lean_object* v___y_4422_, lean_object* v___y_4423_, lean_object* v___y_4424_, lean_object* v___y_4425_, lean_object* v___y_4426_, lean_object* v___y_4427_){
_start:
{
lean_object* v___x_4429_; 
v___x_4429_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___redArg(v_as_4418_, v_sz_4419_, v_i_4420_, v_b_4421_, v___y_4426_, v___y_4427_);
return v___x_4429_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___boxed(lean_object* v_as_4430_, lean_object* v_sz_4431_, lean_object* v_i_4432_, lean_object* v_b_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_){
_start:
{
size_t v_sz_boxed_4441_; size_t v_i_boxed_4442_; lean_object* v_res_4443_; 
v_sz_boxed_4441_ = lean_unbox_usize(v_sz_4431_);
lean_dec(v_sz_4431_);
v_i_boxed_4442_ = lean_unbox_usize(v_i_4432_);
lean_dec(v_i_4432_);
v_res_4443_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3(v_as_4430_, v_sz_boxed_4441_, v_i_boxed_4442_, v_b_4433_, v___y_4434_, v___y_4435_, v___y_4436_, v___y_4437_, v___y_4438_, v___y_4439_);
lean_dec(v___y_4439_);
lean_dec_ref(v___y_4438_);
lean_dec(v___y_4437_);
lean_dec_ref(v___y_4436_);
lean_dec(v___y_4435_);
lean_dec_ref(v___y_4434_);
lean_dec_ref(v_as_4430_);
return v_res_4443_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4(lean_object* v_as_4444_, size_t v_sz_4445_, size_t v_i_4446_, lean_object* v_b_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_, lean_object* v___y_4452_, lean_object* v___y_4453_){
_start:
{
lean_object* v___x_4455_; 
v___x_4455_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4___redArg(v_as_4444_, v_sz_4445_, v_i_4446_, v_b_4447_, v___y_4450_, v___y_4451_, v___y_4452_, v___y_4453_);
return v___x_4455_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4___boxed(lean_object* v_as_4456_, lean_object* v_sz_4457_, lean_object* v_i_4458_, lean_object* v_b_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_, lean_object* v___y_4463_, lean_object* v___y_4464_, lean_object* v___y_4465_, lean_object* v___y_4466_){
_start:
{
size_t v_sz_boxed_4467_; size_t v_i_boxed_4468_; lean_object* v_res_4469_; 
v_sz_boxed_4467_ = lean_unbox_usize(v_sz_4457_);
lean_dec(v_sz_4457_);
v_i_boxed_4468_ = lean_unbox_usize(v_i_4458_);
lean_dec(v_i_4458_);
v_res_4469_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4(v_as_4456_, v_sz_boxed_4467_, v_i_boxed_4468_, v_b_4459_, v___y_4460_, v___y_4461_, v___y_4462_, v___y_4463_, v___y_4464_, v___y_4465_);
lean_dec(v___y_4465_);
lean_dec_ref(v___y_4464_);
lean_dec(v___y_4463_);
lean_dec_ref(v___y_4462_);
lean_dec(v___y_4461_);
lean_dec_ref(v___y_4460_);
lean_dec_ref(v_as_4456_);
return v_res_4469_;
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
