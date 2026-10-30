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
extern lean_object* l_Lean_Elab_instInhabitedPreDefinition_default;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_Elab_eraseRecAppSyntaxExpr(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Elab_ensureNoRecFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_letToHave(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint32_t l_Lean_getMaxHeight(lean_object*, lean_object*);
lean_object* l_Lean_addDecl(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_setDefHeightOverride(lean_object*, lean_object*, uint32_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Elab_FixedParamPerm_instantiateForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVarOf(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_Environment_unlockAsync(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Elab_addAsAxiom___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_PProdN_mkLambdas___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_withEnv___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_enableRealizationsForConst(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Structural_instInhabitedRecArgInfo_default;
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
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInductivePredicate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_zip___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_mkBRecOnApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Elab_Structural_mkBRecOnF___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_mkIndPredBRecOnF___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_mkBRecOnConst(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_mkBRecOnMotive(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_mkIndPredBRecOnMotive(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17_spec__30___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17_spec__30___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17_spec__30___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17_spec__30___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17_spec__30___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17_spec__30___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__0;
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__1;
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__2;
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_f"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(253, 65, 185, 154, 193, 83, 240, 170)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___redArg(lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__24___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__24___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__24(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__20___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__3(lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__22(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__21___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17_spec__30(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__20(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__21(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17_spec__30___redArg___closed__0(void){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_161_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17_spec__30___redArg___closed__1(void){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_162_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17_spec__30___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17_spec__30___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17_spec__30___redArg___closed__0);
v___x_163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_163_, 0, v___x_162_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17_spec__30___redArg(){
_start:
{
lean_object* v___x_165_; 
v___x_165_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17_spec__30___redArg___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17_spec__30___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17_spec__30___redArg___closed__1);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17_spec__30___redArg___boxed(lean_object* v___dummy_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17_spec__30___redArg();
return v_res_167_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__0(void){
_start:
{
lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_168_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17_spec__30___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17_spec__30___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17_spec__30___redArg___closed__0);
v___x_169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_169_, 0, v___x_168_);
return v___x_169_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__1(void){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_170_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__0);
v___x_171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_171_, 0, v___x_170_);
lean_ctor_set(v___x_171_, 1, v___x_170_);
return v___x_171_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__2(void){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17_spec__30___redArg();
return v___x_172_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__3(void){
_start:
{
lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_173_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__0);
v___x_174_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__2);
v___x_175_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_175_, 0, v___x_174_);
lean_ctor_set(v___x_175_, 1, v___x_173_);
lean_ctor_set(v___x_175_, 2, v___x_173_);
lean_ctor_set(v___x_175_, 3, v___x_173_);
lean_ctor_set(v___x_175_, 4, v___x_173_);
lean_ctor_set(v___x_175_, 5, v___x_173_);
lean_ctor_set(v___x_175_, 6, v___x_173_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg(lean_object* v_declName_176_, uint8_t v_s_177_, lean_object* v___y_178_, lean_object* v___y_179_){
_start:
{
lean_object* v___x_181_; lean_object* v_env_182_; lean_object* v_nextMacroScope_183_; lean_object* v_ngen_184_; lean_object* v_auxDeclNGen_185_; lean_object* v_traceState_186_; lean_object* v_recordedDeps_187_; lean_object* v_messages_188_; lean_object* v_infoState_189_; lean_object* v_snapshotTasks_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_219_; 
v___x_181_ = lean_st_ref_take(v___y_179_);
v_env_182_ = lean_ctor_get(v___x_181_, 0);
v_nextMacroScope_183_ = lean_ctor_get(v___x_181_, 1);
v_ngen_184_ = lean_ctor_get(v___x_181_, 2);
v_auxDeclNGen_185_ = lean_ctor_get(v___x_181_, 3);
v_traceState_186_ = lean_ctor_get(v___x_181_, 4);
v_recordedDeps_187_ = lean_ctor_get(v___x_181_, 6);
v_messages_188_ = lean_ctor_get(v___x_181_, 7);
v_infoState_189_ = lean_ctor_get(v___x_181_, 8);
v_snapshotTasks_190_ = lean_ctor_get(v___x_181_, 9);
v_isSharedCheck_219_ = !lean_is_exclusive(v___x_181_);
if (v_isSharedCheck_219_ == 0)
{
lean_object* v_unused_220_; 
v_unused_220_ = lean_ctor_get(v___x_181_, 5);
lean_dec(v_unused_220_);
v___x_192_ = v___x_181_;
v_isShared_193_ = v_isSharedCheck_219_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_snapshotTasks_190_);
lean_inc(v_infoState_189_);
lean_inc(v_messages_188_);
lean_inc(v_recordedDeps_187_);
lean_inc(v_traceState_186_);
lean_inc(v_auxDeclNGen_185_);
lean_inc(v_ngen_184_);
lean_inc(v_nextMacroScope_183_);
lean_inc(v_env_182_);
lean_dec(v___x_181_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_219_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
uint8_t v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_199_; 
v___x_194_ = 0;
v___x_195_ = lean_box(0);
v___x_196_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_182_, v_declName_176_, v_s_177_, v___x_194_, v___x_195_);
v___x_197_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__1);
if (v_isShared_193_ == 0)
{
lean_ctor_set(v___x_192_, 5, v___x_197_);
lean_ctor_set(v___x_192_, 0, v___x_196_);
v___x_199_ = v___x_192_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v___x_196_);
lean_ctor_set(v_reuseFailAlloc_218_, 1, v_nextMacroScope_183_);
lean_ctor_set(v_reuseFailAlloc_218_, 2, v_ngen_184_);
lean_ctor_set(v_reuseFailAlloc_218_, 3, v_auxDeclNGen_185_);
lean_ctor_set(v_reuseFailAlloc_218_, 4, v_traceState_186_);
lean_ctor_set(v_reuseFailAlloc_218_, 5, v___x_197_);
lean_ctor_set(v_reuseFailAlloc_218_, 6, v_recordedDeps_187_);
lean_ctor_set(v_reuseFailAlloc_218_, 7, v_messages_188_);
lean_ctor_set(v_reuseFailAlloc_218_, 8, v_infoState_189_);
lean_ctor_set(v_reuseFailAlloc_218_, 9, v_snapshotTasks_190_);
v___x_199_ = v_reuseFailAlloc_218_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v_mctx_202_; lean_object* v_zetaDeltaFVarIds_203_; lean_object* v_postponed_204_; lean_object* v_diag_205_; lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_216_; 
v___x_200_ = lean_st_ref_put(v___y_179_, v___x_199_);
v___x_201_ = lean_st_ref_take(v___y_178_);
v_mctx_202_ = lean_ctor_get(v___x_201_, 0);
v_zetaDeltaFVarIds_203_ = lean_ctor_get(v___x_201_, 2);
v_postponed_204_ = lean_ctor_get(v___x_201_, 3);
v_diag_205_ = lean_ctor_get(v___x_201_, 4);
v_isSharedCheck_216_ = !lean_is_exclusive(v___x_201_);
if (v_isSharedCheck_216_ == 0)
{
lean_object* v_unused_217_; 
v_unused_217_ = lean_ctor_get(v___x_201_, 1);
lean_dec(v_unused_217_);
v___x_207_ = v___x_201_;
v_isShared_208_ = v_isSharedCheck_216_;
goto v_resetjp_206_;
}
else
{
lean_inc(v_diag_205_);
lean_inc(v_postponed_204_);
lean_inc(v_zetaDeltaFVarIds_203_);
lean_inc(v_mctx_202_);
lean_dec(v___x_201_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_216_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_212_; 
v___x_209_ = lean_box(0);
v___x_210_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__3);
if (v_isShared_208_ == 0)
{
lean_ctor_set(v___x_207_, 1, v___x_210_);
v___x_212_ = v___x_207_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v_mctx_202_);
lean_ctor_set(v_reuseFailAlloc_215_, 1, v___x_210_);
lean_ctor_set(v_reuseFailAlloc_215_, 2, v_zetaDeltaFVarIds_203_);
lean_ctor_set(v_reuseFailAlloc_215_, 3, v_postponed_204_);
lean_ctor_set(v_reuseFailAlloc_215_, 4, v_diag_205_);
v___x_212_ = v_reuseFailAlloc_215_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_213_ = lean_st_ref_put(v___y_178_, v___x_212_);
v___x_214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_214_, 0, v___x_209_);
return v___x_214_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___boxed(lean_object* v_declName_221_, lean_object* v_s_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_){
_start:
{
uint8_t v_s_boxed_226_; lean_object* v_res_227_; 
v_s_boxed_226_ = lean_unbox(v_s_222_);
v_res_227_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg(v_declName_221_, v_s_boxed_226_, v___y_223_, v___y_224_);
lean_dec(v___y_224_);
lean_dec(v___y_223_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18(lean_object* v_declName_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_){
_start:
{
uint8_t v___x_234_; lean_object* v___x_235_; 
v___x_234_ = 0;
v___x_235_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg(v_declName_228_, v___x_234_, v___y_230_, v___y_232_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___boxed(lean_object* v_declName_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18(v_declName_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_);
lean_dec(v___y_240_);
lean_dec_ref(v___y_239_);
lean_dec(v___y_238_);
lean_dec_ref(v___y_237_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16(size_t v_sz_243_, size_t v_i_244_, lean_object* v_bs_245_){
_start:
{
uint8_t v___x_246_; 
v___x_246_ = lean_usize_dec_lt(v_i_244_, v_sz_243_);
if (v___x_246_ == 0)
{
return v_bs_245_;
}
else
{
lean_object* v_v_247_; lean_object* v_declName_248_; lean_object* v___x_249_; lean_object* v_bs_x27_250_; size_t v___x_251_; size_t v___x_252_; lean_object* v___x_253_; 
v_v_247_ = lean_array_uget_borrowed(v_bs_245_, v_i_244_);
v_declName_248_ = lean_ctor_get(v_v_247_, 3);
lean_inc(v_declName_248_);
v___x_249_ = lean_unsigned_to_nat(0u);
v_bs_x27_250_ = lean_array_uset(v_bs_245_, v_i_244_, v___x_249_);
v___x_251_ = ((size_t)1ULL);
v___x_252_ = lean_usize_add(v_i_244_, v___x_251_);
v___x_253_ = lean_array_uset(v_bs_x27_250_, v_i_244_, v_declName_248_);
v_i_244_ = v___x_252_;
v_bs_245_ = v___x_253_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16___boxed(lean_object* v_sz_255_, lean_object* v_i_256_, lean_object* v_bs_257_){
_start:
{
size_t v_sz_boxed_258_; size_t v_i_boxed_259_; lean_object* v_res_260_; 
v_sz_boxed_258_ = lean_unbox_usize(v_sz_255_);
lean_dec(v_sz_255_);
v_i_boxed_259_ = lean_unbox_usize(v_i_256_);
lean_dec(v_i_256_);
v_res_260_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16(v_sz_boxed_258_, v_i_boxed_259_, v_bs_257_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___redArg(lean_object* v_preDefs_264_, lean_object* v_xs_265_, uint8_t v_a_266_, lean_object* v___x_267_, size_t v_sz_268_, size_t v_i_269_, lean_object* v_bs_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_){
_start:
{
uint8_t v___x_276_; 
v___x_276_ = lean_usize_dec_lt(v_i_269_, v_sz_268_);
if (v___x_276_ == 0)
{
lean_object* v___x_277_; 
lean_dec(v___x_267_);
lean_dec_ref(v_preDefs_264_);
v___x_277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_277_, 0, v_bs_270_);
return v___x_277_;
}
else
{
lean_object* v___x_278_; lean_object* v_v_279_; lean_object* v___x_280_; lean_object* v_bs_x27_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v_levelParams_284_; lean_object* v_modifiers_285_; lean_object* v_declName_286_; lean_object* v___x_287_; lean_object* v___x_288_; uint8_t v___x_289_; lean_object* v___x_290_; 
v___x_278_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v_v_279_ = lean_array_uget(v_bs_270_, v_i_269_);
v___x_280_ = lean_unsigned_to_nat(0u);
v_bs_x27_281_ = lean_array_uset(v_bs_270_, v_i_269_, v___x_280_);
v___x_282_ = lean_usize_to_nat(v_i_269_);
v___x_283_ = lean_array_get_borrowed(v___x_278_, v_preDefs_264_, v___x_282_);
lean_dec(v___x_282_);
v_levelParams_284_ = lean_ctor_get(v___x_283_, 1);
v_modifiers_285_ = lean_ctor_get(v___x_283_, 2);
v_declName_286_ = lean_ctor_get(v___x_283_, 3);
v___x_287_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___redArg___closed__1));
lean_inc(v_declName_286_);
v___x_288_ = l_Lean_Name_append(v_declName_286_, v___x_287_);
v___x_289_ = 1;
v___x_290_ = l_Lean_Meta_mkLambdaFVars(v_xs_265_, v_v_279_, v_a_266_, v___x_276_, v_a_266_, v___x_276_, v___x_289_, v___y_271_, v___y_272_, v___y_273_, v___y_274_);
if (lean_obj_tag(v___x_290_) == 0)
{
lean_object* v_a_291_; lean_object* v___x_292_; 
v_a_291_ = lean_ctor_get(v___x_290_, 0);
lean_inc(v_a_291_);
lean_dec_ref_known(v___x_290_, 1);
v___x_292_ = l_Lean_Elab_eraseRecAppSyntaxExpr(v_a_291_, v___y_273_, v___y_274_);
if (lean_obj_tag(v___x_292_) == 0)
{
lean_object* v_a_293_; size_t v_sz_294_; size_t v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v_a_293_ = lean_ctor_get(v___x_292_, 0);
lean_inc_n(v_a_293_, 2);
lean_dec_ref_known(v___x_292_, 1);
v_sz_294_ = lean_array_size(v_preDefs_264_);
v___x_295_ = ((size_t)0ULL);
lean_inc_ref(v_preDefs_264_);
v___x_296_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16(v_sz_294_, v___x_295_, v_preDefs_264_);
v___x_297_ = l_Lean_Elab_ensureNoRecFn(v___x_296_, v_a_293_, v___y_271_, v___y_272_, v___y_273_, v___y_274_);
if (lean_obj_tag(v___x_297_) == 0)
{
lean_object* v___x_298_; 
lean_dec_ref_known(v___x_297_, 1);
lean_inc(v___y_274_);
lean_inc_ref(v___y_273_);
lean_inc(v___y_272_);
lean_inc_ref(v___y_271_);
lean_inc(v_a_293_);
v___x_298_ = lean_infer_type(v_a_293_, v___y_271_, v___y_272_, v___y_273_, v___y_274_);
if (lean_obj_tag(v___x_298_) == 0)
{
lean_object* v_a_299_; lean_object* v___x_300_; 
v_a_299_ = lean_ctor_get(v___x_298_, 0);
lean_inc(v_a_299_);
lean_dec_ref_known(v___x_298_, 1);
v___x_300_ = l_Lean_Meta_letToHave(v_a_299_, v___y_271_, v___y_272_, v___y_273_, v___y_274_);
if (lean_obj_tag(v___x_300_) == 0)
{
lean_object* v_a_301_; lean_object* v___x_302_; lean_object* v_env_303_; uint8_t v_isUnsafe_304_; uint32_t v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; uint8_t v___y_309_; 
v_a_301_ = lean_ctor_get(v___x_300_, 0);
lean_inc(v_a_301_);
lean_dec_ref_known(v___x_300_, 1);
v___x_302_ = lean_st_ref_get(v___y_274_);
v_env_303_ = lean_ctor_get(v___x_302_, 0);
lean_inc_ref(v_env_303_);
lean_dec(v___x_302_);
v_isUnsafe_304_ = lean_ctor_get_uint8(v_modifiers_285_, sizeof(void*)*3 + 4);
lean_inc(v_a_293_);
v___x_305_ = l_Lean_getMaxHeight(v_env_303_, v_a_293_);
lean_inc(v_levelParams_284_);
lean_inc(v___x_288_);
v___x_306_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_306_, 0, v___x_288_);
lean_ctor_set(v___x_306_, 1, v_levelParams_284_);
lean_ctor_set(v___x_306_, 2, v_a_301_);
v___x_307_ = lean_box(1);
if (v_isUnsafe_304_ == 0)
{
uint8_t v___x_374_; 
v___x_374_ = 1;
v___y_309_ = v___x_374_;
goto v___jp_308_;
}
else
{
uint8_t v___x_375_; 
v___x_375_ = 0;
v___y_309_ = v___x_375_;
goto v___jp_308_;
}
v___jp_308_:
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_310_ = lean_box(0);
lean_inc(v___x_288_);
v___x_311_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_311_, 0, v___x_288_);
lean_ctor_set(v___x_311_, 1, v___x_310_);
v___x_312_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_312_, 0, v___x_306_);
lean_ctor_set(v___x_312_, 1, v_a_293_);
lean_ctor_set(v___x_312_, 2, v___x_307_);
lean_ctor_set(v___x_312_, 3, v___x_311_);
lean_ctor_set_uint8(v___x_312_, sizeof(void*)*4, v___y_309_);
v___x_313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_313_, 0, v___x_312_);
v___x_314_ = l_Lean_addDecl(v___x_313_, v_a_266_, v___y_273_, v___y_274_);
if (lean_obj_tag(v___x_314_) == 0)
{
lean_object* v___x_315_; lean_object* v_env_316_; lean_object* v_nextMacroScope_317_; lean_object* v_ngen_318_; lean_object* v_auxDeclNGen_319_; lean_object* v_traceState_320_; lean_object* v_recordedDeps_321_; lean_object* v_messages_322_; lean_object* v_infoState_323_; lean_object* v_snapshotTasks_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_364_; 
lean_dec_ref_known(v___x_314_, 1);
v___x_315_ = lean_st_ref_take(v___y_274_);
v_env_316_ = lean_ctor_get(v___x_315_, 0);
v_nextMacroScope_317_ = lean_ctor_get(v___x_315_, 1);
v_ngen_318_ = lean_ctor_get(v___x_315_, 2);
v_auxDeclNGen_319_ = lean_ctor_get(v___x_315_, 3);
v_traceState_320_ = lean_ctor_get(v___x_315_, 4);
v_recordedDeps_321_ = lean_ctor_get(v___x_315_, 6);
v_messages_322_ = lean_ctor_get(v___x_315_, 7);
v_infoState_323_ = lean_ctor_get(v___x_315_, 8);
v_snapshotTasks_324_ = lean_ctor_get(v___x_315_, 9);
v_isSharedCheck_364_ = !lean_is_exclusive(v___x_315_);
if (v_isSharedCheck_364_ == 0)
{
lean_object* v_unused_365_; 
v_unused_365_ = lean_ctor_get(v___x_315_, 5);
lean_dec(v_unused_365_);
v___x_326_ = v___x_315_;
v_isShared_327_ = v_isSharedCheck_364_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_snapshotTasks_324_);
lean_inc(v_infoState_323_);
lean_inc(v_messages_322_);
lean_inc(v_recordedDeps_321_);
lean_inc(v_traceState_320_);
lean_inc(v_auxDeclNGen_319_);
lean_inc(v_ngen_318_);
lean_inc(v_nextMacroScope_317_);
lean_inc(v_env_316_);
lean_dec(v___x_315_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_364_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_331_; 
lean_inc(v___x_288_);
v___x_328_ = l_Lean_setDefHeightOverride(v_env_316_, v___x_288_, v___x_305_);
v___x_329_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__1);
if (v_isShared_327_ == 0)
{
lean_ctor_set(v___x_326_, 5, v___x_329_);
lean_ctor_set(v___x_326_, 0, v___x_328_);
v___x_331_ = v___x_326_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v___x_328_);
lean_ctor_set(v_reuseFailAlloc_363_, 1, v_nextMacroScope_317_);
lean_ctor_set(v_reuseFailAlloc_363_, 2, v_ngen_318_);
lean_ctor_set(v_reuseFailAlloc_363_, 3, v_auxDeclNGen_319_);
lean_ctor_set(v_reuseFailAlloc_363_, 4, v_traceState_320_);
lean_ctor_set(v_reuseFailAlloc_363_, 5, v___x_329_);
lean_ctor_set(v_reuseFailAlloc_363_, 6, v_recordedDeps_321_);
lean_ctor_set(v_reuseFailAlloc_363_, 7, v_messages_322_);
lean_ctor_set(v_reuseFailAlloc_363_, 8, v_infoState_323_);
lean_ctor_set(v_reuseFailAlloc_363_, 9, v_snapshotTasks_324_);
v___x_331_ = v_reuseFailAlloc_363_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v_mctx_334_; lean_object* v_zetaDeltaFVarIds_335_; lean_object* v_postponed_336_; lean_object* v_diag_337_; lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_361_; 
v___x_332_ = lean_st_ref_put(v___y_274_, v___x_331_);
v___x_333_ = lean_st_ref_take(v___y_272_);
v_mctx_334_ = lean_ctor_get(v___x_333_, 0);
v_zetaDeltaFVarIds_335_ = lean_ctor_get(v___x_333_, 2);
v_postponed_336_ = lean_ctor_get(v___x_333_, 3);
v_diag_337_ = lean_ctor_get(v___x_333_, 4);
v_isSharedCheck_361_ = !lean_is_exclusive(v___x_333_);
if (v_isSharedCheck_361_ == 0)
{
lean_object* v_unused_362_; 
v_unused_362_ = lean_ctor_get(v___x_333_, 1);
lean_dec(v_unused_362_);
v___x_339_ = v___x_333_;
v_isShared_340_ = v_isSharedCheck_361_;
goto v_resetjp_338_;
}
else
{
lean_inc(v_diag_337_);
lean_inc(v_postponed_336_);
lean_inc(v_zetaDeltaFVarIds_335_);
lean_inc(v_mctx_334_);
lean_dec(v___x_333_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_361_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
lean_object* v___x_341_; lean_object* v___x_343_; 
v___x_341_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__3);
if (v_isShared_340_ == 0)
{
lean_ctor_set(v___x_339_, 1, v___x_341_);
v___x_343_ = v___x_339_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v_mctx_334_);
lean_ctor_set(v_reuseFailAlloc_360_, 1, v___x_341_);
lean_ctor_set(v_reuseFailAlloc_360_, 2, v_zetaDeltaFVarIds_335_);
lean_ctor_set(v_reuseFailAlloc_360_, 3, v_postponed_336_);
lean_ctor_set(v_reuseFailAlloc_360_, 4, v_diag_337_);
v___x_343_ = v_reuseFailAlloc_360_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_344_ = lean_st_ref_put(v___y_272_, v___x_343_);
lean_inc(v___x_288_);
v___x_345_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18(v___x_288_, v___y_271_, v___y_272_, v___y_273_, v___y_274_);
if (lean_obj_tag(v___x_345_) == 0)
{
lean_object* v___x_346_; lean_object* v___x_347_; size_t v___x_348_; size_t v___x_349_; lean_object* v___x_350_; 
lean_dec_ref_known(v___x_345_, 1);
lean_inc(v___x_267_);
v___x_346_ = l_Lean_mkConst(v___x_288_, v___x_267_);
v___x_347_ = l_Lean_mkAppN(v___x_346_, v_xs_265_);
v___x_348_ = ((size_t)1ULL);
v___x_349_ = lean_usize_add(v_i_269_, v___x_348_);
v___x_350_ = lean_array_uset(v_bs_x27_281_, v_i_269_, v___x_347_);
v_i_269_ = v___x_349_;
v_bs_270_ = v___x_350_;
goto _start;
}
else
{
lean_object* v_a_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_359_; 
lean_dec(v___x_288_);
lean_dec_ref(v_bs_x27_281_);
lean_dec(v___x_267_);
lean_dec_ref(v_preDefs_264_);
v_a_352_ = lean_ctor_get(v___x_345_, 0);
v_isSharedCheck_359_ = !lean_is_exclusive(v___x_345_);
if (v_isSharedCheck_359_ == 0)
{
v___x_354_ = v___x_345_;
v_isShared_355_ = v_isSharedCheck_359_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_a_352_);
lean_dec(v___x_345_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_359_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v___x_357_; 
if (v_isShared_355_ == 0)
{
v___x_357_ = v___x_354_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v_a_352_);
v___x_357_ = v_reuseFailAlloc_358_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
return v___x_357_;
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
lean_object* v_a_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_373_; 
lean_dec(v___x_288_);
lean_dec_ref(v_bs_x27_281_);
lean_dec(v___x_267_);
lean_dec_ref(v_preDefs_264_);
v_a_366_ = lean_ctor_get(v___x_314_, 0);
v_isSharedCheck_373_ = !lean_is_exclusive(v___x_314_);
if (v_isSharedCheck_373_ == 0)
{
v___x_368_ = v___x_314_;
v_isShared_369_ = v_isSharedCheck_373_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_a_366_);
lean_dec(v___x_314_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_373_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_371_; 
if (v_isShared_369_ == 0)
{
v___x_371_ = v___x_368_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v_a_366_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
}
}
}
else
{
lean_object* v_a_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_383_; 
lean_dec(v_a_293_);
lean_dec(v___x_288_);
lean_dec_ref(v_bs_x27_281_);
lean_dec(v___x_267_);
lean_dec_ref(v_preDefs_264_);
v_a_376_ = lean_ctor_get(v___x_300_, 0);
v_isSharedCheck_383_ = !lean_is_exclusive(v___x_300_);
if (v_isSharedCheck_383_ == 0)
{
v___x_378_ = v___x_300_;
v_isShared_379_ = v_isSharedCheck_383_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_a_376_);
lean_dec(v___x_300_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_383_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
lean_object* v___x_381_; 
if (v_isShared_379_ == 0)
{
v___x_381_ = v___x_378_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v_a_376_);
v___x_381_ = v_reuseFailAlloc_382_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
return v___x_381_;
}
}
}
}
else
{
lean_object* v_a_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_391_; 
lean_dec(v_a_293_);
lean_dec(v___x_288_);
lean_dec_ref(v_bs_x27_281_);
lean_dec(v___x_267_);
lean_dec_ref(v_preDefs_264_);
v_a_384_ = lean_ctor_get(v___x_298_, 0);
v_isSharedCheck_391_ = !lean_is_exclusive(v___x_298_);
if (v_isSharedCheck_391_ == 0)
{
v___x_386_ = v___x_298_;
v_isShared_387_ = v_isSharedCheck_391_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_a_384_);
lean_dec(v___x_298_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_391_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v___x_389_; 
if (v_isShared_387_ == 0)
{
v___x_389_ = v___x_386_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v_a_384_);
v___x_389_ = v_reuseFailAlloc_390_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
return v___x_389_;
}
}
}
}
else
{
lean_object* v_a_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_399_; 
lean_dec(v_a_293_);
lean_dec(v___x_288_);
lean_dec_ref(v_bs_x27_281_);
lean_dec(v___x_267_);
lean_dec_ref(v_preDefs_264_);
v_a_392_ = lean_ctor_get(v___x_297_, 0);
v_isSharedCheck_399_ = !lean_is_exclusive(v___x_297_);
if (v_isSharedCheck_399_ == 0)
{
v___x_394_ = v___x_297_;
v_isShared_395_ = v_isSharedCheck_399_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_a_392_);
lean_dec(v___x_297_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_399_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v___x_397_; 
if (v_isShared_395_ == 0)
{
v___x_397_ = v___x_394_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v_a_392_);
v___x_397_ = v_reuseFailAlloc_398_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
return v___x_397_;
}
}
}
}
else
{
lean_object* v_a_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_407_; 
lean_dec(v___x_288_);
lean_dec_ref(v_bs_x27_281_);
lean_dec(v___x_267_);
lean_dec_ref(v_preDefs_264_);
v_a_400_ = lean_ctor_get(v___x_292_, 0);
v_isSharedCheck_407_ = !lean_is_exclusive(v___x_292_);
if (v_isSharedCheck_407_ == 0)
{
v___x_402_ = v___x_292_;
v_isShared_403_ = v_isSharedCheck_407_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_a_400_);
lean_dec(v___x_292_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_407_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___x_405_; 
if (v_isShared_403_ == 0)
{
v___x_405_ = v___x_402_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v_a_400_);
v___x_405_ = v_reuseFailAlloc_406_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
return v___x_405_;
}
}
}
}
else
{
lean_object* v_a_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_415_; 
lean_dec(v___x_288_);
lean_dec_ref(v_bs_x27_281_);
lean_dec(v___x_267_);
lean_dec_ref(v_preDefs_264_);
v_a_408_ = lean_ctor_get(v___x_290_, 0);
v_isSharedCheck_415_ = !lean_is_exclusive(v___x_290_);
if (v_isSharedCheck_415_ == 0)
{
v___x_410_ = v___x_290_;
v_isShared_411_ = v_isSharedCheck_415_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_a_408_);
lean_dec(v___x_290_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_415_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
lean_object* v___x_413_; 
if (v_isShared_411_ == 0)
{
v___x_413_ = v___x_410_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v_a_408_);
v___x_413_ = v_reuseFailAlloc_414_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
return v___x_413_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___redArg___boxed(lean_object* v_preDefs_416_, lean_object* v_xs_417_, lean_object* v_a_418_, lean_object* v___x_419_, lean_object* v_sz_420_, lean_object* v_i_421_, lean_object* v_bs_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_){
_start:
{
uint8_t v_a_26136__boxed_428_; size_t v_sz_boxed_429_; size_t v_i_boxed_430_; lean_object* v_res_431_; 
v_a_26136__boxed_428_ = lean_unbox(v_a_418_);
v_sz_boxed_429_ = lean_unbox_usize(v_sz_420_);
lean_dec(v_sz_420_);
v_i_boxed_430_ = lean_unbox_usize(v_i_421_);
lean_dec(v_i_421_);
v_res_431_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___redArg(v_preDefs_416_, v_xs_417_, v_a_26136__boxed_428_, v___x_419_, v_sz_boxed_429_, v_i_boxed_430_, v_bs_422_, v___y_423_, v___y_424_, v___y_425_, v___y_426_);
lean_dec(v___y_426_);
lean_dec_ref(v___y_425_);
lean_dec(v___y_424_);
lean_dec_ref(v___y_423_);
lean_dec_ref(v_xs_417_);
return v_res_431_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13(lean_object* v_as_432_, size_t v_i_433_, size_t v_stop_434_, lean_object* v_b_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_){
_start:
{
uint8_t v___x_441_; 
v___x_441_ = lean_usize_dec_eq(v_i_433_, v_stop_434_);
if (v___x_441_ == 0)
{
lean_object* v___x_20165__overap_442_; lean_object* v___x_443_; 
v___x_20165__overap_442_ = lean_array_uget_borrowed(v_as_432_, v_i_433_);
lean_inc(v___x_20165__overap_442_);
lean_inc(v___y_439_);
lean_inc_ref(v___y_438_);
lean_inc(v___y_437_);
lean_inc_ref(v___y_436_);
v___x_443_ = lean_apply_5(v___x_20165__overap_442_, v___y_436_, v___y_437_, v___y_438_, v___y_439_, lean_box(0));
if (lean_obj_tag(v___x_443_) == 0)
{
lean_object* v_a_444_; size_t v___x_445_; size_t v___x_446_; 
v_a_444_ = lean_ctor_get(v___x_443_, 0);
lean_inc(v_a_444_);
lean_dec_ref_known(v___x_443_, 1);
v___x_445_ = ((size_t)1ULL);
v___x_446_ = lean_usize_add(v_i_433_, v___x_445_);
v_i_433_ = v___x_446_;
v_b_435_ = v_a_444_;
goto _start;
}
else
{
return v___x_443_;
}
}
else
{
lean_object* v___x_448_; 
v___x_448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_448_, 0, v_b_435_);
return v___x_448_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13___boxed(lean_object* v_as_449_, lean_object* v_i_450_, lean_object* v_stop_451_, lean_object* v_b_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_){
_start:
{
size_t v_i_boxed_458_; size_t v_stop_boxed_459_; lean_object* v_res_460_; 
v_i_boxed_458_ = lean_unbox_usize(v_i_450_);
lean_dec(v_i_450_);
v_stop_boxed_459_ = lean_unbox_usize(v_stop_451_);
lean_dec(v_stop_451_);
v_res_460_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13(v_as_449_, v_i_boxed_458_, v_stop_boxed_459_, v_b_452_, v___y_453_, v___y_454_, v___y_455_, v___y_456_);
lean_dec(v___y_456_);
lean_dec_ref(v___y_455_);
lean_dec(v___y_454_);
lean_dec_ref(v___y_453_);
lean_dec_ref(v_as_449_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__24___redArg(lean_object* v_as_461_, size_t v_i_462_, size_t v_stop_463_, lean_object* v_b_464_, lean_object* v___y_465_, lean_object* v___y_466_){
_start:
{
uint8_t v___x_468_; 
v___x_468_ = lean_usize_dec_eq(v_i_462_, v_stop_463_);
if (v___x_468_ == 0)
{
lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_469_ = lean_array_uget_borrowed(v_as_461_, v_i_462_);
lean_inc(v___x_469_);
v___x_470_ = l_Lean_Elab_addAsAxiom___redArg(v___x_469_, v___y_465_, v___y_466_);
if (lean_obj_tag(v___x_470_) == 0)
{
lean_object* v_a_471_; size_t v___x_472_; size_t v___x_473_; 
v_a_471_ = lean_ctor_get(v___x_470_, 0);
lean_inc(v_a_471_);
lean_dec_ref_known(v___x_470_, 1);
v___x_472_ = ((size_t)1ULL);
v___x_473_ = lean_usize_add(v_i_462_, v___x_472_);
v_i_462_ = v___x_473_;
v_b_464_ = v_a_471_;
goto _start;
}
else
{
return v___x_470_;
}
}
else
{
lean_object* v___x_475_; 
v___x_475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_475_, 0, v_b_464_);
return v___x_475_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__24___redArg___boxed(lean_object* v_as_476_, lean_object* v_i_477_, lean_object* v_stop_478_, lean_object* v_b_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_){
_start:
{
size_t v_i_boxed_483_; size_t v_stop_boxed_484_; lean_object* v_res_485_; 
v_i_boxed_483_ = lean_unbox_usize(v_i_477_);
lean_dec(v_i_477_);
v_stop_boxed_484_ = lean_unbox_usize(v_stop_478_);
lean_dec(v_stop_478_);
v_res_485_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__24___redArg(v_as_476_, v_i_boxed_483_, v_stop_boxed_484_, v_b_479_, v___y_480_, v___y_481_);
lean_dec(v___y_481_);
lean_dec_ref(v___y_480_);
lean_dec_ref(v_as_476_);
return v_res_485_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__24(lean_object* v_as_486_, size_t v_i_487_, size_t v_stop_488_, lean_object* v_b_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__24___redArg(v_as_486_, v_i_487_, v_stop_488_, v_b_489_, v___y_492_, v___y_493_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__24___boxed(lean_object* v_as_496_, lean_object* v_i_497_, lean_object* v_stop_498_, lean_object* v_b_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_){
_start:
{
size_t v_i_boxed_505_; size_t v_stop_boxed_506_; lean_object* v_res_507_; 
v_i_boxed_505_ = lean_unbox_usize(v_i_497_);
lean_dec(v_i_497_);
v_stop_boxed_506_ = lean_unbox_usize(v_stop_498_);
lean_dec(v_stop_498_);
v_res_507_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__24(v_as_496_, v_i_boxed_505_, v_stop_boxed_506_, v_b_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_);
lean_dec(v___y_503_);
lean_dec_ref(v___y_502_);
lean_dec(v___y_501_);
lean_dec_ref(v___y_500_);
lean_dec_ref(v_as_496_);
return v_res_507_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg(lean_object* v_env_508_, lean_object* v___y_509_, lean_object* v___y_510_){
_start:
{
lean_object* v___x_512_; lean_object* v_nextMacroScope_513_; lean_object* v_ngen_514_; lean_object* v_auxDeclNGen_515_; lean_object* v_traceState_516_; lean_object* v_recordedDeps_517_; lean_object* v_messages_518_; lean_object* v_infoState_519_; lean_object* v_snapshotTasks_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_546_; 
v___x_512_ = lean_st_ref_take(v___y_510_);
v_nextMacroScope_513_ = lean_ctor_get(v___x_512_, 1);
v_ngen_514_ = lean_ctor_get(v___x_512_, 2);
v_auxDeclNGen_515_ = lean_ctor_get(v___x_512_, 3);
v_traceState_516_ = lean_ctor_get(v___x_512_, 4);
v_recordedDeps_517_ = lean_ctor_get(v___x_512_, 6);
v_messages_518_ = lean_ctor_get(v___x_512_, 7);
v_infoState_519_ = lean_ctor_get(v___x_512_, 8);
v_snapshotTasks_520_ = lean_ctor_get(v___x_512_, 9);
v_isSharedCheck_546_ = !lean_is_exclusive(v___x_512_);
if (v_isSharedCheck_546_ == 0)
{
lean_object* v_unused_547_; lean_object* v_unused_548_; 
v_unused_547_ = lean_ctor_get(v___x_512_, 5);
lean_dec(v_unused_547_);
v_unused_548_ = lean_ctor_get(v___x_512_, 0);
lean_dec(v_unused_548_);
v___x_522_ = v___x_512_;
v_isShared_523_ = v_isSharedCheck_546_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_snapshotTasks_520_);
lean_inc(v_infoState_519_);
lean_inc(v_messages_518_);
lean_inc(v_recordedDeps_517_);
lean_inc(v_traceState_516_);
lean_inc(v_auxDeclNGen_515_);
lean_inc(v_ngen_514_);
lean_inc(v_nextMacroScope_513_);
lean_dec(v___x_512_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_546_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v___x_524_; lean_object* v___x_526_; 
v___x_524_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__1);
if (v_isShared_523_ == 0)
{
lean_ctor_set(v___x_522_, 5, v___x_524_);
lean_ctor_set(v___x_522_, 0, v_env_508_);
v___x_526_ = v___x_522_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_env_508_);
lean_ctor_set(v_reuseFailAlloc_545_, 1, v_nextMacroScope_513_);
lean_ctor_set(v_reuseFailAlloc_545_, 2, v_ngen_514_);
lean_ctor_set(v_reuseFailAlloc_545_, 3, v_auxDeclNGen_515_);
lean_ctor_set(v_reuseFailAlloc_545_, 4, v_traceState_516_);
lean_ctor_set(v_reuseFailAlloc_545_, 5, v___x_524_);
lean_ctor_set(v_reuseFailAlloc_545_, 6, v_recordedDeps_517_);
lean_ctor_set(v_reuseFailAlloc_545_, 7, v_messages_518_);
lean_ctor_set(v_reuseFailAlloc_545_, 8, v_infoState_519_);
lean_ctor_set(v_reuseFailAlloc_545_, 9, v_snapshotTasks_520_);
v___x_526_ = v_reuseFailAlloc_545_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v_mctx_529_; lean_object* v_zetaDeltaFVarIds_530_; lean_object* v_postponed_531_; lean_object* v_diag_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_543_; 
v___x_527_ = lean_st_ref_put(v___y_510_, v___x_526_);
v___x_528_ = lean_st_ref_take(v___y_509_);
v_mctx_529_ = lean_ctor_get(v___x_528_, 0);
v_zetaDeltaFVarIds_530_ = lean_ctor_get(v___x_528_, 2);
v_postponed_531_ = lean_ctor_get(v___x_528_, 3);
v_diag_532_ = lean_ctor_get(v___x_528_, 4);
v_isSharedCheck_543_ = !lean_is_exclusive(v___x_528_);
if (v_isSharedCheck_543_ == 0)
{
lean_object* v_unused_544_; 
v_unused_544_ = lean_ctor_get(v___x_528_, 1);
lean_dec(v_unused_544_);
v___x_534_ = v___x_528_;
v_isShared_535_ = v_isSharedCheck_543_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_diag_532_);
lean_inc(v_postponed_531_);
lean_inc(v_zetaDeltaFVarIds_530_);
lean_inc(v_mctx_529_);
lean_dec(v___x_528_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_543_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_539_; 
v___x_536_ = lean_box(0);
v___x_537_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__3);
if (v_isShared_535_ == 0)
{
lean_ctor_set(v___x_534_, 1, v___x_537_);
v___x_539_ = v___x_534_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v_mctx_529_);
lean_ctor_set(v_reuseFailAlloc_542_, 1, v___x_537_);
lean_ctor_set(v_reuseFailAlloc_542_, 2, v_zetaDeltaFVarIds_530_);
lean_ctor_set(v_reuseFailAlloc_542_, 3, v_postponed_531_);
lean_ctor_set(v_reuseFailAlloc_542_, 4, v_diag_532_);
v___x_539_ = v_reuseFailAlloc_542_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_540_ = lean_st_ref_put(v___y_509_, v___x_539_);
v___x_541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_541_, 0, v___x_536_);
return v___x_541_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___boxed(lean_object* v_env_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg(v_env_549_, v___y_550_, v___y_551_);
lean_dec(v___y_551_);
lean_dec(v___y_550_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23___redArg(lean_object* v_env_554_, lean_object* v_x_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_){
_start:
{
lean_object* v___x_561_; lean_object* v_env_562_; lean_object* v_a_564_; lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_561_ = lean_st_ref_get(v___y_559_);
v_env_562_ = lean_ctor_get(v___x_561_, 0);
lean_inc_ref(v_env_562_);
lean_dec(v___x_561_);
v___x_574_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg(v_env_554_, v___y_557_, v___y_559_);
lean_dec_ref(v___x_574_);
lean_inc(v___y_559_);
lean_inc_ref(v___y_558_);
lean_inc(v___y_557_);
lean_inc_ref(v___y_556_);
v___x_575_ = lean_apply_5(v_x_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_, lean_box(0));
if (lean_obj_tag(v___x_575_) == 0)
{
lean_object* v_a_576_; lean_object* v___x_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_584_; 
v_a_576_ = lean_ctor_get(v___x_575_, 0);
lean_inc(v_a_576_);
lean_dec_ref_known(v___x_575_, 1);
v___x_577_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg(v_env_562_, v___y_557_, v___y_559_);
v_isSharedCheck_584_ = !lean_is_exclusive(v___x_577_);
if (v_isSharedCheck_584_ == 0)
{
lean_object* v_unused_585_; 
v_unused_585_ = lean_ctor_get(v___x_577_, 0);
lean_dec(v_unused_585_);
v___x_579_ = v___x_577_;
v_isShared_580_ = v_isSharedCheck_584_;
goto v_resetjp_578_;
}
else
{
lean_dec(v___x_577_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_584_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
lean_object* v___x_582_; 
if (v_isShared_580_ == 0)
{
lean_ctor_set(v___x_579_, 0, v_a_576_);
v___x_582_ = v___x_579_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v_a_576_);
v___x_582_ = v_reuseFailAlloc_583_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
return v___x_582_;
}
}
}
else
{
lean_object* v_a_586_; 
v_a_586_ = lean_ctor_get(v___x_575_, 0);
lean_inc(v_a_586_);
lean_dec_ref_known(v___x_575_, 1);
v_a_564_ = v_a_586_;
goto v___jp_563_;
}
v___jp_563_:
{
lean_object* v___x_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_572_; 
v___x_565_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg(v_env_562_, v___y_557_, v___y_559_);
v_isSharedCheck_572_ = !lean_is_exclusive(v___x_565_);
if (v_isSharedCheck_572_ == 0)
{
lean_object* v_unused_573_; 
v_unused_573_ = lean_ctor_get(v___x_565_, 0);
lean_dec(v_unused_573_);
v___x_567_ = v___x_565_;
v_isShared_568_ = v_isSharedCheck_572_;
goto v_resetjp_566_;
}
else
{
lean_dec(v___x_565_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_572_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v___x_570_; 
if (v_isShared_568_ == 0)
{
lean_ctor_set_tag(v___x_567_, 1);
lean_ctor_set(v___x_567_, 0, v_a_564_);
v___x_570_ = v___x_567_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v_a_564_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
return v___x_570_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23___redArg___boxed(lean_object* v_env_587_, lean_object* v_x_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23___redArg(v_env_587_, v_x_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_);
lean_dec(v___y_592_);
lean_dec_ref(v___y_591_);
lean_dec(v___y_590_);
lean_dec_ref(v___y_589_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___lam__1(lean_object* v___x_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_){
_start:
{
lean_object* v___x_601_; 
v___x_601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_601_, 0, v___x_595_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___lam__1___boxed(lean_object* v___x_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_){
_start:
{
lean_object* v_res_608_; 
v_res_608_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___lam__1(v___x_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_);
lean_dec(v___y_606_);
lean_dec_ref(v___y_605_);
lean_dec(v___y_604_);
lean_dec_ref(v___y_603_);
return v_res_608_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___lam__0(lean_object* v___y_609_, lean_object* v_k_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_){
_start:
{
lean_object* v___x_616_; 
lean_inc(v___y_614_);
lean_inc_ref(v___y_613_);
lean_inc(v___y_612_);
lean_inc_ref(v___y_611_);
v___x_616_ = lean_apply_5(v___y_609_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, lean_box(0));
if (lean_obj_tag(v___x_616_) == 0)
{
lean_object* v___x_617_; 
lean_dec_ref_known(v___x_616_, 1);
v___x_617_ = lean_apply_5(v_k_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, lean_box(0));
return v___x_617_;
}
else
{
lean_object* v_a_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_625_; 
lean_dec(v___y_614_);
lean_dec_ref(v___y_613_);
lean_dec(v___y_612_);
lean_dec_ref(v___y_611_);
lean_dec_ref(v_k_610_);
v_a_618_ = lean_ctor_get(v___x_616_, 0);
v_isSharedCheck_625_ = !lean_is_exclusive(v___x_616_);
if (v_isSharedCheck_625_ == 0)
{
v___x_620_ = v___x_616_;
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_a_618_);
lean_dec(v___x_616_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v___x_623_; 
if (v_isShared_621_ == 0)
{
v___x_623_ = v___x_620_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_a_618_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
return v___x_623_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___lam__0___boxed(lean_object* v___y_626_, lean_object* v_k_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_){
_start:
{
lean_object* v_res_633_; 
v_res_633_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___lam__0(v___y_626_, v_k_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_);
return v_res_633_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(lean_object* v_preDefs_638_, lean_object* v_k_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_){
_start:
{
lean_object* v___y_646_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; uint8_t v___x_655_; 
v___x_652_ = lean_unsigned_to_nat(0u);
v___x_653_ = lean_array_get_size(v_preDefs_638_);
v___x_654_ = lean_box(0);
v___x_655_ = lean_nat_dec_lt(v___x_652_, v___x_653_);
if (v___x_655_ == 0)
{
lean_object* v___f_656_; 
lean_dec_ref(v_preDefs_638_);
v___f_656_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___closed__0));
v___y_646_ = v___f_656_;
goto v___jp_645_;
}
else
{
size_t v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_657_ = lean_usize_of_nat(v___x_653_);
v___x_658_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___boxed__const__1));
v___x_659_ = lean_box_usize(v___x_657_);
v___x_660_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__24___boxed), 9, 4);
lean_closure_set(v___x_660_, 0, v_preDefs_638_);
lean_closure_set(v___x_660_, 1, v___x_658_);
lean_closure_set(v___x_660_, 2, v___x_659_);
lean_closure_set(v___x_660_, 3, v___x_654_);
v___y_646_ = v___x_660_;
goto v___jp_645_;
}
v___jp_645_:
{
lean_object* v___f_647_; lean_object* v___x_648_; lean_object* v_env_649_; lean_object* v___x_650_; lean_object* v___x_651_; 
v___f_647_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_647_, 0, v___y_646_);
lean_closure_set(v___f_647_, 1, v_k_639_);
v___x_648_ = lean_st_ref_get(v___y_643_);
v_env_649_ = lean_ctor_get(v___x_648_, 0);
lean_inc_ref(v_env_649_);
lean_dec(v___x_648_);
v___x_650_ = l_Lean_Environment_unlockAsync(v_env_649_);
v___x_651_ = l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23___redArg(v___x_650_, v___f_647_, v___y_640_, v___y_641_, v___y_642_, v___y_643_);
return v___x_651_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___boxed(lean_object* v_preDefs_661_, lean_object* v_k_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v_preDefs_661_, v_k_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_);
lean_dec(v___y_666_);
lean_dec_ref(v___y_665_);
lean_dec(v___y_664_);
lean_dec_ref(v___y_663_);
return v_res_668_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg___closed__0(void){
_start:
{
lean_object* v___x_669_; lean_object* v_dummy_670_; 
v___x_669_ = lean_box(0);
v_dummy_670_ = l_Lean_Expr_sort___override(v___x_669_);
return v_dummy_670_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg(uint8_t v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_recArgInfos_674_, lean_object* v___x_675_, lean_object* v_preDefs_676_, lean_object* v_a_677_, size_t v_sz_678_, size_t v_i_679_, lean_object* v_bs_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_){
_start:
{
uint8_t v___x_686_; 
v___x_686_ = lean_usize_dec_lt(v_i_679_, v_sz_678_);
if (v___x_686_ == 0)
{
lean_object* v___x_687_; 
lean_dec_ref(v_a_677_);
lean_dec_ref(v_preDefs_676_);
lean_dec_ref(v___x_675_);
lean_dec_ref(v_recArgInfos_674_);
v___x_687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_687_, 0, v_bs_680_);
return v___x_687_;
}
else
{
lean_object* v___x_688_; lean_object* v_v_689_; lean_object* v___x_690_; lean_object* v_bs_x27_691_; lean_object* v_a_693_; lean_object* v___x_698_; 
v___x_688_ = l_Lean_instInhabitedExpr;
v_v_689_ = lean_array_uget(v_bs_680_, v_i_679_);
v___x_690_ = lean_unsigned_to_nat(0u);
v_bs_x27_691_ = lean_array_uset(v_bs_680_, v_i_679_, v___x_690_);
v___x_698_ = lean_usize_to_nat(v_i_679_);
if (v_a_671_ == 0)
{
lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_699_ = lean_array_get_borrowed(v___x_688_, v_a_672_, v___x_698_);
v___x_700_ = lean_array_get_borrowed(v___x_688_, v_a_673_, v___x_698_);
lean_dec(v___x_698_);
lean_inc(v___x_700_);
lean_inc(v___x_699_);
lean_inc_ref(v___x_675_);
lean_inc_ref(v_recArgInfos_674_);
v___x_701_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnF___boxed), 10, 5);
lean_closure_set(v___x_701_, 0, v_recArgInfos_674_);
lean_closure_set(v___x_701_, 1, v___x_675_);
lean_closure_set(v___x_701_, 2, v_v_689_);
lean_closure_set(v___x_701_, 3, v___x_699_);
lean_closure_set(v___x_701_, 4, v___x_700_);
lean_inc_ref(v_preDefs_676_);
v___x_702_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v_preDefs_676_, v___x_701_, v___y_681_, v___y_682_, v___y_683_, v___y_684_);
if (lean_obj_tag(v___x_702_) == 0)
{
lean_object* v_a_703_; 
v_a_703_ = lean_ctor_get(v___x_702_, 0);
lean_inc(v_a_703_);
lean_dec_ref_known(v___x_702_, 1);
v_a_693_ = v_a_703_;
goto v___jp_692_;
}
else
{
lean_object* v_a_704_; lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_711_; 
lean_dec_ref(v_bs_x27_691_);
lean_dec_ref(v_a_677_);
lean_dec_ref(v_preDefs_676_);
lean_dec_ref(v___x_675_);
lean_dec_ref(v_recArgInfos_674_);
v_a_704_ = lean_ctor_get(v___x_702_, 0);
v_isSharedCheck_711_ = !lean_is_exclusive(v___x_702_);
if (v_isSharedCheck_711_ == 0)
{
v___x_706_ = v___x_702_;
v_isShared_707_ = v_isSharedCheck_711_;
goto v_resetjp_705_;
}
else
{
lean_inc(v_a_704_);
lean_dec(v___x_702_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_711_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
lean_object* v___x_709_; 
if (v_isShared_707_ == 0)
{
v___x_709_ = v___x_706_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v_a_704_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
}
}
else
{
lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v_dummy_715_; lean_object* v_nargs_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_712_ = lean_array_get_borrowed(v___x_688_, v_a_672_, v___x_698_);
v___x_713_ = lean_array_get_borrowed(v___x_688_, v_a_673_, v___x_698_);
lean_dec(v___x_698_);
lean_inc_ref(v_a_677_);
v___x_714_ = lean_apply_1(v_a_677_, v___x_690_);
v_dummy_715_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg___closed__0);
v_nargs_716_ = l_Lean_Expr_getAppNumArgs(v___x_714_);
lean_inc(v_nargs_716_);
v___x_717_ = lean_mk_array(v_nargs_716_, v_dummy_715_);
v___x_718_ = lean_unsigned_to_nat(1u);
v___x_719_ = lean_nat_sub(v_nargs_716_, v___x_718_);
lean_dec(v_nargs_716_);
v___x_720_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___x_714_, v___x_717_, v___x_719_);
lean_inc(v___x_713_);
lean_inc(v___x_712_);
lean_inc_ref(v___x_675_);
lean_inc_ref(v_recArgInfos_674_);
v___x_721_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkIndPredBRecOnF___boxed), 11, 6);
lean_closure_set(v___x_721_, 0, v_recArgInfos_674_);
lean_closure_set(v___x_721_, 1, v___x_675_);
lean_closure_set(v___x_721_, 2, v_v_689_);
lean_closure_set(v___x_721_, 3, v___x_712_);
lean_closure_set(v___x_721_, 4, v___x_713_);
lean_closure_set(v___x_721_, 5, v___x_720_);
lean_inc_ref(v_preDefs_676_);
v___x_722_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v_preDefs_676_, v___x_721_, v___y_681_, v___y_682_, v___y_683_, v___y_684_);
if (lean_obj_tag(v___x_722_) == 0)
{
lean_object* v_a_723_; lean_object* v_fst_724_; lean_object* v_snd_725_; lean_object* v___x_726_; uint8_t v___x_727_; 
v_a_723_ = lean_ctor_get(v___x_722_, 0);
lean_inc(v_a_723_);
lean_dec_ref_known(v___x_722_, 1);
v_fst_724_ = lean_ctor_get(v_a_723_, 0);
lean_inc(v_fst_724_);
v_snd_725_ = lean_ctor_get(v_a_723_, 1);
lean_inc(v_snd_725_);
lean_dec(v_a_723_);
v___x_726_ = lean_array_get_size(v_snd_725_);
v___x_727_ = lean_nat_dec_lt(v___x_690_, v___x_726_);
if (v___x_727_ == 0)
{
lean_dec(v_snd_725_);
v_a_693_ = v_fst_724_;
goto v___jp_692_;
}
else
{
lean_object* v___x_728_; size_t v___x_729_; size_t v___x_730_; lean_object* v___x_731_; 
v___x_728_ = lean_box(0);
v___x_729_ = ((size_t)0ULL);
v___x_730_ = lean_usize_of_nat(v___x_726_);
v___x_731_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13(v_snd_725_, v___x_729_, v___x_730_, v___x_728_, v___y_681_, v___y_682_, v___y_683_, v___y_684_);
lean_dec(v_snd_725_);
if (lean_obj_tag(v___x_731_) == 0)
{
lean_dec_ref_known(v___x_731_, 1);
v_a_693_ = v_fst_724_;
goto v___jp_692_;
}
else
{
lean_object* v_a_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_739_; 
lean_dec(v_fst_724_);
lean_dec_ref(v_bs_x27_691_);
lean_dec_ref(v_a_677_);
lean_dec_ref(v_preDefs_676_);
lean_dec_ref(v___x_675_);
lean_dec_ref(v_recArgInfos_674_);
v_a_732_ = lean_ctor_get(v___x_731_, 0);
v_isSharedCheck_739_ = !lean_is_exclusive(v___x_731_);
if (v_isSharedCheck_739_ == 0)
{
v___x_734_ = v___x_731_;
v_isShared_735_ = v_isSharedCheck_739_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_a_732_);
lean_dec(v___x_731_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_739_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
lean_object* v___x_737_; 
if (v_isShared_735_ == 0)
{
v___x_737_ = v___x_734_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v_a_732_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
return v___x_737_;
}
}
}
}
}
else
{
lean_object* v_a_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_747_; 
lean_dec_ref(v_bs_x27_691_);
lean_dec_ref(v_a_677_);
lean_dec_ref(v_preDefs_676_);
lean_dec_ref(v___x_675_);
lean_dec_ref(v_recArgInfos_674_);
v_a_740_ = lean_ctor_get(v___x_722_, 0);
v_isSharedCheck_747_ = !lean_is_exclusive(v___x_722_);
if (v_isSharedCheck_747_ == 0)
{
v___x_742_ = v___x_722_;
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_a_740_);
lean_dec(v___x_722_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v___x_745_; 
if (v_isShared_743_ == 0)
{
v___x_745_ = v___x_742_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v_a_740_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
return v___x_745_;
}
}
}
}
v___jp_692_:
{
size_t v___x_694_; size_t v___x_695_; lean_object* v___x_696_; 
v___x_694_ = ((size_t)1ULL);
v___x_695_ = lean_usize_add(v_i_679_, v___x_694_);
v___x_696_ = lean_array_uset(v_bs_x27_691_, v_i_679_, v_a_693_);
v_i_679_ = v___x_695_;
v_bs_680_ = v___x_696_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg___boxed(lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_recArgInfos_751_, lean_object* v___x_752_, lean_object* v_preDefs_753_, lean_object* v_a_754_, lean_object* v_sz_755_, lean_object* v_i_756_, lean_object* v_bs_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_){
_start:
{
uint8_t v_a_26739__boxed_763_; size_t v_sz_boxed_764_; size_t v_i_boxed_765_; lean_object* v_res_766_; 
v_a_26739__boxed_763_ = lean_unbox(v_a_748_);
v_sz_boxed_764_ = lean_unbox_usize(v_sz_755_);
lean_dec(v_sz_755_);
v_i_boxed_765_ = lean_unbox_usize(v_i_756_);
lean_dec(v_i_756_);
v_res_766_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg(v_a_26739__boxed_763_, v_a_749_, v_a_750_, v_recArgInfos_751_, v___x_752_, v_preDefs_753_, v_a_754_, v_sz_boxed_764_, v_i_boxed_765_, v_bs_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_);
lean_dec(v___y_761_);
lean_dec_ref(v___y_760_);
lean_dec(v___y_759_);
lean_dec_ref(v___y_758_);
lean_dec_ref(v_a_750_);
lean_dec_ref(v_a_749_);
return v_res_766_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11_spec__21(lean_object* v_msgData_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_){
_start:
{
lean_object* v___x_773_; lean_object* v_env_774_; uint8_t v___x_775_; lean_object* v_env_776_; lean_object* v___x_777_; lean_object* v_toCold_778_; lean_object* v_mctx_779_; lean_object* v_lctx_780_; lean_object* v_options_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_773_ = lean_st_ref_get(v___y_771_);
v_env_774_ = lean_ctor_get(v___x_773_, 0);
lean_inc_ref(v_env_774_);
lean_dec(v___x_773_);
v___x_775_ = 0;
v_env_776_ = l_Lean_Environment_setRecordingDeps(v_env_774_, v___x_775_);
v___x_777_ = lean_st_ref_get(v___y_769_);
v_toCold_778_ = lean_ctor_get(v___y_770_, 0);
v_mctx_779_ = lean_ctor_get(v___x_777_, 0);
lean_inc_ref(v_mctx_779_);
lean_dec(v___x_777_);
v_lctx_780_ = lean_ctor_get(v___y_768_, 2);
v_options_781_ = lean_ctor_get(v_toCold_778_, 2);
lean_inc_ref(v_options_781_);
lean_inc_ref(v_lctx_780_);
v___x_782_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_782_, 0, v_env_776_);
lean_ctor_set(v___x_782_, 1, v_mctx_779_);
lean_ctor_set(v___x_782_, 2, v_lctx_780_);
lean_ctor_set(v___x_782_, 3, v_options_781_);
v___x_783_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_783_, 0, v___x_782_);
lean_ctor_set(v___x_783_, 1, v_msgData_767_);
v___x_784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_784_, 0, v___x_783_);
return v___x_784_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11_spec__21___boxed(lean_object* v_msgData_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_){
_start:
{
lean_object* v_res_791_; 
v_res_791_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11_spec__21(v_msgData_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_);
lean_dec(v___y_789_);
lean_dec_ref(v___y_788_);
lean_dec(v___y_787_);
lean_dec_ref(v___y_786_);
return v_res_791_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___closed__0(void){
_start:
{
lean_object* v___x_792_; double v___x_793_; 
v___x_792_ = lean_unsigned_to_nat(0u);
v___x_793_ = lean_float_of_nat(v___x_792_);
return v___x_793_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(lean_object* v_cls_797_, lean_object* v_msg_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_){
_start:
{
lean_object* v_ref_804_; lean_object* v___x_805_; lean_object* v_a_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_851_; 
v_ref_804_ = lean_ctor_get(v___y_801_, 2);
v___x_805_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11_spec__21(v_msg_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_);
v_a_806_ = lean_ctor_get(v___x_805_, 0);
v_isSharedCheck_851_ = !lean_is_exclusive(v___x_805_);
if (v_isSharedCheck_851_ == 0)
{
v___x_808_ = v___x_805_;
v_isShared_809_ = v_isSharedCheck_851_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_a_806_);
lean_dec(v___x_805_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_851_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_810_; lean_object* v_traceState_811_; lean_object* v_env_812_; lean_object* v_nextMacroScope_813_; lean_object* v_ngen_814_; lean_object* v_auxDeclNGen_815_; lean_object* v_cache_816_; lean_object* v_recordedDeps_817_; lean_object* v_messages_818_; lean_object* v_infoState_819_; lean_object* v_snapshotTasks_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_850_; 
v___x_810_ = lean_st_ref_take(v___y_802_);
v_traceState_811_ = lean_ctor_get(v___x_810_, 4);
v_env_812_ = lean_ctor_get(v___x_810_, 0);
v_nextMacroScope_813_ = lean_ctor_get(v___x_810_, 1);
v_ngen_814_ = lean_ctor_get(v___x_810_, 2);
v_auxDeclNGen_815_ = lean_ctor_get(v___x_810_, 3);
v_cache_816_ = lean_ctor_get(v___x_810_, 5);
v_recordedDeps_817_ = lean_ctor_get(v___x_810_, 6);
v_messages_818_ = lean_ctor_get(v___x_810_, 7);
v_infoState_819_ = lean_ctor_get(v___x_810_, 8);
v_snapshotTasks_820_ = lean_ctor_get(v___x_810_, 9);
v_isSharedCheck_850_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_850_ == 0)
{
v___x_822_ = v___x_810_;
v_isShared_823_ = v_isSharedCheck_850_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_snapshotTasks_820_);
lean_inc(v_infoState_819_);
lean_inc(v_messages_818_);
lean_inc(v_recordedDeps_817_);
lean_inc(v_cache_816_);
lean_inc(v_traceState_811_);
lean_inc(v_auxDeclNGen_815_);
lean_inc(v_ngen_814_);
lean_inc(v_nextMacroScope_813_);
lean_inc(v_env_812_);
lean_dec(v___x_810_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_850_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
uint64_t v_tid_824_; lean_object* v_traces_825_; lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_849_; 
v_tid_824_ = lean_ctor_get_uint64(v_traceState_811_, sizeof(void*)*1);
v_traces_825_ = lean_ctor_get(v_traceState_811_, 0);
v_isSharedCheck_849_ = !lean_is_exclusive(v_traceState_811_);
if (v_isSharedCheck_849_ == 0)
{
v___x_827_ = v_traceState_811_;
v_isShared_828_ = v_isSharedCheck_849_;
goto v_resetjp_826_;
}
else
{
lean_inc(v_traces_825_);
lean_dec(v_traceState_811_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_849_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
lean_object* v___x_829_; lean_object* v___x_830_; double v___x_831_; uint8_t v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_840_; 
v___x_829_ = lean_box(0);
v___x_830_ = lean_box(0);
v___x_831_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___closed__0);
v___x_832_ = 0;
v___x_833_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___closed__1));
v___x_834_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_834_, 0, v_cls_797_);
lean_ctor_set(v___x_834_, 1, v___x_830_);
lean_ctor_set(v___x_834_, 2, v___x_833_);
lean_ctor_set_float(v___x_834_, sizeof(void*)*3, v___x_831_);
lean_ctor_set_float(v___x_834_, sizeof(void*)*3 + 8, v___x_831_);
lean_ctor_set_uint8(v___x_834_, sizeof(void*)*3 + 16, v___x_832_);
v___x_835_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___closed__2));
v___x_836_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_836_, 0, v___x_834_);
lean_ctor_set(v___x_836_, 1, v_a_806_);
lean_ctor_set(v___x_836_, 2, v___x_835_);
lean_inc(v_ref_804_);
v___x_837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_837_, 0, v_ref_804_);
lean_ctor_set(v___x_837_, 1, v___x_836_);
v___x_838_ = l_Lean_PersistentArray_push___redArg(v_traces_825_, v___x_837_);
if (v_isShared_828_ == 0)
{
lean_ctor_set(v___x_827_, 0, v___x_838_);
v___x_840_ = v___x_827_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v___x_838_);
lean_ctor_set_uint64(v_reuseFailAlloc_848_, sizeof(void*)*1, v_tid_824_);
v___x_840_ = v_reuseFailAlloc_848_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
lean_object* v___x_842_; 
if (v_isShared_823_ == 0)
{
lean_ctor_set(v___x_822_, 4, v___x_840_);
v___x_842_ = v___x_822_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v_env_812_);
lean_ctor_set(v_reuseFailAlloc_847_, 1, v_nextMacroScope_813_);
lean_ctor_set(v_reuseFailAlloc_847_, 2, v_ngen_814_);
lean_ctor_set(v_reuseFailAlloc_847_, 3, v_auxDeclNGen_815_);
lean_ctor_set(v_reuseFailAlloc_847_, 4, v___x_840_);
lean_ctor_set(v_reuseFailAlloc_847_, 5, v_cache_816_);
lean_ctor_set(v_reuseFailAlloc_847_, 6, v_recordedDeps_817_);
lean_ctor_set(v_reuseFailAlloc_847_, 7, v_messages_818_);
lean_ctor_set(v_reuseFailAlloc_847_, 8, v_infoState_819_);
lean_ctor_set(v_reuseFailAlloc_847_, 9, v_snapshotTasks_820_);
v___x_842_ = v_reuseFailAlloc_847_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
lean_object* v___x_843_; lean_object* v___x_845_; 
v___x_843_ = lean_st_ref_put(v___y_802_, v___x_842_);
if (v_isShared_809_ == 0)
{
lean_ctor_set(v___x_808_, 0, v___x_829_);
v___x_845_ = v___x_808_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v___x_829_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___boxed(lean_object* v_cls_852_, lean_object* v_msg_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_){
_start:
{
lean_object* v_res_859_; 
v_res_859_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v_cls_852_, v_msg_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_);
lean_dec(v___y_857_);
lean_dec_ref(v___y_856_);
lean_dec(v___y_855_);
lean_dec_ref(v___y_854_);
return v_res_859_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9(lean_object* v_as_860_, lean_object* v_bs_861_, lean_object* v_i_862_, lean_object* v_cs_863_){
_start:
{
lean_object* v___x_864_; uint8_t v___x_865_; 
v___x_864_ = lean_array_get_size(v_as_860_);
v___x_865_ = lean_nat_dec_lt(v_i_862_, v___x_864_);
if (v___x_865_ == 0)
{
lean_dec(v_i_862_);
return v_cs_863_;
}
else
{
lean_object* v___x_866_; uint8_t v___x_867_; 
v___x_866_ = lean_array_get_size(v_bs_861_);
v___x_867_ = lean_nat_dec_lt(v_i_862_, v___x_866_);
if (v___x_867_ == 0)
{
lean_dec(v_i_862_);
return v_cs_863_;
}
else
{
lean_object* v_a_868_; lean_object* v_ref_869_; uint8_t v_kind_870_; lean_object* v_levelParams_871_; lean_object* v_modifiers_872_; lean_object* v_declName_873_; lean_object* v_binders_874_; lean_object* v_numSectionVars_875_; lean_object* v_type_876_; lean_object* v_termination_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_889_; 
v_a_868_ = lean_array_fget(v_as_860_, v_i_862_);
v_ref_869_ = lean_ctor_get(v_a_868_, 0);
v_kind_870_ = lean_ctor_get_uint8(v_a_868_, sizeof(void*)*9);
v_levelParams_871_ = lean_ctor_get(v_a_868_, 1);
v_modifiers_872_ = lean_ctor_get(v_a_868_, 2);
v_declName_873_ = lean_ctor_get(v_a_868_, 3);
v_binders_874_ = lean_ctor_get(v_a_868_, 4);
v_numSectionVars_875_ = lean_ctor_get(v_a_868_, 5);
v_type_876_ = lean_ctor_get(v_a_868_, 6);
v_termination_877_ = lean_ctor_get(v_a_868_, 8);
v_isSharedCheck_889_ = !lean_is_exclusive(v_a_868_);
if (v_isSharedCheck_889_ == 0)
{
lean_object* v_unused_890_; 
v_unused_890_ = lean_ctor_get(v_a_868_, 7);
lean_dec(v_unused_890_);
v___x_879_ = v_a_868_;
v_isShared_880_ = v_isSharedCheck_889_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_termination_877_);
lean_inc(v_type_876_);
lean_inc(v_numSectionVars_875_);
lean_inc(v_binders_874_);
lean_inc(v_declName_873_);
lean_inc(v_modifiers_872_);
lean_inc(v_levelParams_871_);
lean_inc(v_ref_869_);
lean_dec(v_a_868_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_889_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v_b_881_; lean_object* v___x_883_; 
v_b_881_ = lean_array_fget_borrowed(v_bs_861_, v_i_862_);
lean_inc(v_b_881_);
if (v_isShared_880_ == 0)
{
lean_ctor_set(v___x_879_, 7, v_b_881_);
v___x_883_ = v___x_879_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v_ref_869_);
lean_ctor_set(v_reuseFailAlloc_888_, 1, v_levelParams_871_);
lean_ctor_set(v_reuseFailAlloc_888_, 2, v_modifiers_872_);
lean_ctor_set(v_reuseFailAlloc_888_, 3, v_declName_873_);
lean_ctor_set(v_reuseFailAlloc_888_, 4, v_binders_874_);
lean_ctor_set(v_reuseFailAlloc_888_, 5, v_numSectionVars_875_);
lean_ctor_set(v_reuseFailAlloc_888_, 6, v_type_876_);
lean_ctor_set(v_reuseFailAlloc_888_, 7, v_b_881_);
lean_ctor_set(v_reuseFailAlloc_888_, 8, v_termination_877_);
lean_ctor_set_uint8(v_reuseFailAlloc_888_, sizeof(void*)*9, v_kind_870_);
v___x_883_ = v_reuseFailAlloc_888_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; 
v___x_884_ = lean_unsigned_to_nat(1u);
v___x_885_ = lean_nat_add(v_i_862_, v___x_884_);
lean_dec(v_i_862_);
v___x_886_ = lean_array_push(v_cs_863_, v___x_883_);
v_i_862_ = v___x_885_;
v_cs_863_ = v___x_886_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9___boxed(lean_object* v_as_891_, lean_object* v_bs_892_, lean_object* v_i_893_, lean_object* v_cs_894_){
_start:
{
lean_object* v_res_895_; 
v_res_895_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9(v_as_891_, v_bs_892_, v_i_893_, v_cs_894_);
lean_dec_ref(v_bs_892_);
lean_dec_ref(v_as_891_);
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___lam__0(lean_object* v_fixedParamPerms_896_, lean_object* v___x_897_, lean_object* v___x_898_, lean_object* v_xs_899_, lean_object* v_snd_900_, uint8_t v___x_901_, lean_object* v_ys_902_, lean_object* v_x_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_){
_start:
{
lean_object* v_perms_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; uint8_t v___x_913_; uint8_t v___x_914_; lean_object* v___x_915_; 
v_perms_909_ = lean_ctor_get(v_fixedParamPerms_896_, 1);
v___x_910_ = lean_array_get_borrowed(v___x_897_, v_perms_909_, v___x_898_);
lean_inc_ref(v_ys_902_);
lean_inc(v___x_910_);
v___x_911_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v___x_910_, v_xs_899_, v_ys_902_);
v___x_912_ = l_Lean_Expr_beta(v_snd_900_, v_ys_902_);
v___x_913_ = 0;
v___x_914_ = 1;
v___x_915_ = l_Lean_Meta_mkLambdaFVars(v___x_911_, v___x_912_, v___x_913_, v___x_901_, v___x_913_, v___x_901_, v___x_914_, v___y_904_, v___y_905_, v___y_906_, v___y_907_);
lean_dec_ref(v___x_911_);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___lam__0___boxed(lean_object* v_fixedParamPerms_916_, lean_object* v___x_917_, lean_object* v___x_918_, lean_object* v_xs_919_, lean_object* v_snd_920_, lean_object* v___x_921_, lean_object* v_ys_922_, lean_object* v_x_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_){
_start:
{
uint8_t v___x_27050__boxed_929_; lean_object* v_res_930_; 
v___x_27050__boxed_929_ = lean_unbox(v___x_921_);
v_res_930_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___lam__0(v_fixedParamPerms_916_, v___x_917_, v___x_918_, v_xs_919_, v_snd_920_, v___x_27050__boxed_929_, v_ys_922_, v_x_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_);
lean_dec(v___y_927_);
lean_dec_ref(v___y_926_);
lean_dec(v___y_925_);
lean_dec_ref(v___y_924_);
lean_dec_ref(v_x_923_);
lean_dec_ref(v_xs_919_);
lean_dec(v___x_918_);
lean_dec_ref(v___x_917_);
lean_dec_ref(v_fixedParamPerms_916_);
return v_res_930_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_931_; 
v___x_931_ = l_Array_instInhabited___redArg();
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg(lean_object* v_fixedParamPerms_932_, lean_object* v_xs_933_, size_t v_sz_934_, size_t v_i_935_, lean_object* v_bs_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_){
_start:
{
uint8_t v___x_942_; 
v___x_942_ = lean_usize_dec_lt(v_i_935_, v_sz_934_);
if (v___x_942_ == 0)
{
lean_object* v___x_943_; 
lean_dec_ref(v_xs_933_);
lean_dec_ref(v_fixedParamPerms_932_);
v___x_943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_943_, 0, v_bs_936_);
return v___x_943_;
}
else
{
lean_object* v_v_944_; lean_object* v_fst_945_; lean_object* v_snd_946_; lean_object* v___x_947_; lean_object* v_bs_x27_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___f_952_; uint8_t v___x_953_; lean_object* v___x_954_; 
v_v_944_ = lean_array_uget_borrowed(v_bs_936_, v_i_935_);
v_fst_945_ = lean_ctor_get(v_v_944_, 0);
lean_inc(v_fst_945_);
v_snd_946_ = lean_ctor_get(v_v_944_, 1);
lean_inc(v_snd_946_);
v___x_947_ = lean_unsigned_to_nat(0u);
v_bs_x27_948_ = lean_array_uset(v_bs_936_, v_i_935_, v___x_947_);
v___x_949_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0);
v___x_950_ = lean_usize_to_nat(v_i_935_);
v___x_951_ = lean_box(v___x_942_);
lean_inc_ref(v_xs_933_);
lean_inc_ref(v_fixedParamPerms_932_);
v___f_952_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___lam__0___boxed), 13, 6);
lean_closure_set(v___f_952_, 0, v_fixedParamPerms_932_);
lean_closure_set(v___f_952_, 1, v___x_949_);
lean_closure_set(v___f_952_, 2, v___x_950_);
lean_closure_set(v___f_952_, 3, v_xs_933_);
lean_closure_set(v___f_952_, 4, v_snd_946_);
lean_closure_set(v___f_952_, 5, v___x_951_);
v___x_953_ = 0;
v___x_954_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg(v_fst_945_, v___f_952_, v___x_953_, v___y_937_, v___y_938_, v___y_939_, v___y_940_);
if (lean_obj_tag(v___x_954_) == 0)
{
lean_object* v_a_955_; size_t v___x_956_; size_t v___x_957_; lean_object* v___x_958_; 
v_a_955_ = lean_ctor_get(v___x_954_, 0);
lean_inc(v_a_955_);
lean_dec_ref_known(v___x_954_, 1);
v___x_956_ = ((size_t)1ULL);
v___x_957_ = lean_usize_add(v_i_935_, v___x_956_);
v___x_958_ = lean_array_uset(v_bs_x27_948_, v_i_935_, v_a_955_);
v_i_935_ = v___x_957_;
v_bs_936_ = v___x_958_;
goto _start;
}
else
{
lean_object* v_a_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_967_; 
lean_dec_ref(v_bs_x27_948_);
lean_dec_ref(v_xs_933_);
lean_dec_ref(v_fixedParamPerms_932_);
v_a_960_ = lean_ctor_get(v___x_954_, 0);
v_isSharedCheck_967_ = !lean_is_exclusive(v___x_954_);
if (v_isSharedCheck_967_ == 0)
{
v___x_962_ = v___x_954_;
v_isShared_963_ = v_isSharedCheck_967_;
goto v_resetjp_961_;
}
else
{
lean_inc(v_a_960_);
lean_dec(v___x_954_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_967_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
lean_object* v___x_965_; 
if (v_isShared_963_ == 0)
{
v___x_965_ = v___x_962_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v_a_960_);
v___x_965_ = v_reuseFailAlloc_966_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
return v___x_965_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___boxed(lean_object* v_fixedParamPerms_968_, lean_object* v_xs_969_, lean_object* v_sz_970_, lean_object* v_i_971_, lean_object* v_bs_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_){
_start:
{
size_t v_sz_boxed_978_; size_t v_i_boxed_979_; lean_object* v_res_980_; 
v_sz_boxed_978_ = lean_unbox_usize(v_sz_970_);
lean_dec(v_sz_970_);
v_i_boxed_979_ = lean_unbox_usize(v_i_971_);
lean_dec(v_i_971_);
v_res_980_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg(v_fixedParamPerms_968_, v_xs_969_, v_sz_boxed_978_, v_i_boxed_979_, v_bs_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_);
lean_dec(v___y_976_);
lean_dec_ref(v___y_975_);
lean_dec(v___y_974_);
lean_dec_ref(v___y_973_);
return v_res_980_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(lean_object* v_a_981_, lean_object* v_a_982_){
_start:
{
if (lean_obj_tag(v_a_981_) == 0)
{
lean_object* v___x_983_; 
v___x_983_ = l_List_reverse___redArg(v_a_982_);
return v___x_983_;
}
else
{
lean_object* v_head_984_; lean_object* v_tail_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_994_; 
v_head_984_ = lean_ctor_get(v_a_981_, 0);
v_tail_985_ = lean_ctor_get(v_a_981_, 1);
v_isSharedCheck_994_ = !lean_is_exclusive(v_a_981_);
if (v_isSharedCheck_994_ == 0)
{
v___x_987_ = v_a_981_;
v_isShared_988_ = v_isSharedCheck_994_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_tail_985_);
lean_inc(v_head_984_);
lean_dec(v_a_981_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_994_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___x_989_; lean_object* v___x_991_; 
v___x_989_ = l_Lean_MessageData_ofExpr(v_head_984_);
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 1, v_a_982_);
lean_ctor_set(v___x_987_, 0, v___x_989_);
v___x_991_ = v___x_987_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v___x_989_);
lean_ctor_set(v_reuseFailAlloc_993_, 1, v_a_982_);
v___x_991_ = v_reuseFailAlloc_993_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
v_a_981_ = v_tail_985_;
v_a_982_ = v___x_991_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__15(lean_object* v_a_995_, lean_object* v_a_996_){
_start:
{
if (lean_obj_tag(v_a_995_) == 0)
{
lean_object* v___x_997_; 
v___x_997_ = l_List_reverse___redArg(v_a_996_);
return v___x_997_;
}
else
{
lean_object* v_head_998_; lean_object* v_tail_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1008_; 
v_head_998_ = lean_ctor_get(v_a_995_, 0);
v_tail_999_ = lean_ctor_get(v_a_995_, 1);
v_isSharedCheck_1008_ = !lean_is_exclusive(v_a_995_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_1001_ = v_a_995_;
v_isShared_1002_ = v_isSharedCheck_1008_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_tail_999_);
lean_inc(v_head_998_);
lean_dec(v_a_995_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1008_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v___x_1003_; lean_object* v___x_1005_; 
v___x_1003_ = l_Lean_mkLevelParam(v_head_998_);
if (v_isShared_1002_ == 0)
{
lean_ctor_set(v___x_1001_, 1, v_a_996_);
lean_ctor_set(v___x_1001_, 0, v___x_1003_);
v___x_1005_ = v___x_1001_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v___x_1003_);
lean_ctor_set(v_reuseFailAlloc_1007_, 1, v_a_996_);
v___x_1005_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
v_a_995_ = v_tail_999_;
v_a_996_ = v___x_1005_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__0(void){
_start:
{
lean_object* v___x_1009_; 
v___x_1009_ = l_instMonadEIO___redArg();
return v___x_1009_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg(lean_object* v_msg_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_){
_start:
{
lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v_toApplicative_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1083_; 
v___x_1020_ = lean_obj_once(&l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__0, &l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__0_once, _init_l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__0);
v___x_1021_ = l_StateRefT_x27_instMonad___redArg(v___x_1020_);
v_toApplicative_1022_ = lean_ctor_get(v___x_1021_, 0);
v_isSharedCheck_1083_ = !lean_is_exclusive(v___x_1021_);
if (v_isSharedCheck_1083_ == 0)
{
lean_object* v_unused_1084_; 
v_unused_1084_ = lean_ctor_get(v___x_1021_, 1);
lean_dec(v_unused_1084_);
v___x_1024_ = v___x_1021_;
v_isShared_1025_ = v_isSharedCheck_1083_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_toApplicative_1022_);
lean_dec(v___x_1021_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1083_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v_toFunctor_1026_; lean_object* v_toSeq_1027_; lean_object* v_toSeqLeft_1028_; lean_object* v_toSeqRight_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1081_; 
v_toFunctor_1026_ = lean_ctor_get(v_toApplicative_1022_, 0);
v_toSeq_1027_ = lean_ctor_get(v_toApplicative_1022_, 2);
v_toSeqLeft_1028_ = lean_ctor_get(v_toApplicative_1022_, 3);
v_toSeqRight_1029_ = lean_ctor_get(v_toApplicative_1022_, 4);
v_isSharedCheck_1081_ = !lean_is_exclusive(v_toApplicative_1022_);
if (v_isSharedCheck_1081_ == 0)
{
lean_object* v_unused_1082_; 
v_unused_1082_ = lean_ctor_get(v_toApplicative_1022_, 1);
lean_dec(v_unused_1082_);
v___x_1031_ = v_toApplicative_1022_;
v_isShared_1032_ = v_isSharedCheck_1081_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_toSeqRight_1029_);
lean_inc(v_toSeqLeft_1028_);
lean_inc(v_toSeq_1027_);
lean_inc(v_toFunctor_1026_);
lean_dec(v_toApplicative_1022_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1081_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v___f_1033_; lean_object* v___f_1034_; lean_object* v___f_1035_; lean_object* v___f_1036_; lean_object* v___x_1037_; lean_object* v___f_1038_; lean_object* v___f_1039_; lean_object* v___f_1040_; lean_object* v___x_1042_; 
v___f_1033_ = ((lean_object*)(l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__1));
v___f_1034_ = ((lean_object*)(l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__2));
lean_inc_ref(v_toFunctor_1026_);
v___f_1035_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1035_, 0, v_toFunctor_1026_);
v___f_1036_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1036_, 0, v_toFunctor_1026_);
v___x_1037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1037_, 0, v___f_1035_);
lean_ctor_set(v___x_1037_, 1, v___f_1036_);
v___f_1038_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1038_, 0, v_toSeqRight_1029_);
v___f_1039_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1039_, 0, v_toSeqLeft_1028_);
v___f_1040_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1040_, 0, v_toSeq_1027_);
if (v_isShared_1032_ == 0)
{
lean_ctor_set(v___x_1031_, 4, v___f_1038_);
lean_ctor_set(v___x_1031_, 3, v___f_1039_);
lean_ctor_set(v___x_1031_, 2, v___f_1040_);
lean_ctor_set(v___x_1031_, 1, v___f_1033_);
lean_ctor_set(v___x_1031_, 0, v___x_1037_);
v___x_1042_ = v___x_1031_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v___x_1037_);
lean_ctor_set(v_reuseFailAlloc_1080_, 1, v___f_1033_);
lean_ctor_set(v_reuseFailAlloc_1080_, 2, v___f_1040_);
lean_ctor_set(v_reuseFailAlloc_1080_, 3, v___f_1039_);
lean_ctor_set(v_reuseFailAlloc_1080_, 4, v___f_1038_);
v___x_1042_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
lean_object* v___x_1044_; 
if (v_isShared_1025_ == 0)
{
lean_ctor_set(v___x_1024_, 1, v___f_1034_);
lean_ctor_set(v___x_1024_, 0, v___x_1042_);
v___x_1044_ = v___x_1024_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v___x_1042_);
lean_ctor_set(v_reuseFailAlloc_1079_, 1, v___f_1034_);
v___x_1044_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
lean_object* v___x_1045_; lean_object* v_toApplicative_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1077_; 
v___x_1045_ = l_StateRefT_x27_instMonad___redArg(v___x_1044_);
v_toApplicative_1046_ = lean_ctor_get(v___x_1045_, 0);
v_isSharedCheck_1077_ = !lean_is_exclusive(v___x_1045_);
if (v_isSharedCheck_1077_ == 0)
{
lean_object* v_unused_1078_; 
v_unused_1078_ = lean_ctor_get(v___x_1045_, 1);
lean_dec(v_unused_1078_);
v___x_1048_ = v___x_1045_;
v_isShared_1049_ = v_isSharedCheck_1077_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_toApplicative_1046_);
lean_dec(v___x_1045_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1077_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v_toFunctor_1050_; lean_object* v_toSeq_1051_; lean_object* v_toSeqLeft_1052_; lean_object* v_toSeqRight_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1075_; 
v_toFunctor_1050_ = lean_ctor_get(v_toApplicative_1046_, 0);
v_toSeq_1051_ = lean_ctor_get(v_toApplicative_1046_, 2);
v_toSeqLeft_1052_ = lean_ctor_get(v_toApplicative_1046_, 3);
v_toSeqRight_1053_ = lean_ctor_get(v_toApplicative_1046_, 4);
v_isSharedCheck_1075_ = !lean_is_exclusive(v_toApplicative_1046_);
if (v_isSharedCheck_1075_ == 0)
{
lean_object* v_unused_1076_; 
v_unused_1076_ = lean_ctor_get(v_toApplicative_1046_, 1);
lean_dec(v_unused_1076_);
v___x_1055_ = v_toApplicative_1046_;
v_isShared_1056_ = v_isSharedCheck_1075_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_toSeqRight_1053_);
lean_inc(v_toSeqLeft_1052_);
lean_inc(v_toSeq_1051_);
lean_inc(v_toFunctor_1050_);
lean_dec(v_toApplicative_1046_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1075_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___f_1057_; lean_object* v___f_1058_; lean_object* v___f_1059_; lean_object* v___f_1060_; lean_object* v___x_1061_; lean_object* v___f_1062_; lean_object* v___f_1063_; lean_object* v___f_1064_; lean_object* v___x_1066_; 
v___f_1057_ = ((lean_object*)(l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__3));
v___f_1058_ = ((lean_object*)(l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__4));
lean_inc_ref(v_toFunctor_1050_);
v___f_1059_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1059_, 0, v_toFunctor_1050_);
v___f_1060_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1060_, 0, v_toFunctor_1050_);
v___x_1061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1061_, 0, v___f_1059_);
lean_ctor_set(v___x_1061_, 1, v___f_1060_);
v___f_1062_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1062_, 0, v_toSeqRight_1053_);
v___f_1063_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1063_, 0, v_toSeqLeft_1052_);
v___f_1064_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1064_, 0, v_toSeq_1051_);
if (v_isShared_1056_ == 0)
{
lean_ctor_set(v___x_1055_, 4, v___f_1062_);
lean_ctor_set(v___x_1055_, 3, v___f_1063_);
lean_ctor_set(v___x_1055_, 2, v___f_1064_);
lean_ctor_set(v___x_1055_, 1, v___f_1057_);
lean_ctor_set(v___x_1055_, 0, v___x_1061_);
v___x_1066_ = v___x_1055_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v___x_1061_);
lean_ctor_set(v_reuseFailAlloc_1074_, 1, v___f_1057_);
lean_ctor_set(v_reuseFailAlloc_1074_, 2, v___f_1064_);
lean_ctor_set(v_reuseFailAlloc_1074_, 3, v___f_1063_);
lean_ctor_set(v_reuseFailAlloc_1074_, 4, v___f_1062_);
v___x_1066_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
lean_object* v___x_1068_; 
if (v_isShared_1049_ == 0)
{
lean_ctor_set(v___x_1048_, 1, v___f_1058_);
lean_ctor_set(v___x_1048_, 0, v___x_1066_);
v___x_1068_ = v___x_1048_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v___x_1066_);
lean_ctor_set(v_reuseFailAlloc_1073_, 1, v___f_1058_);
v___x_1068_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_22455__overap_1071_; lean_object* v___x_1072_; 
v___x_1069_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0);
v___x_1070_ = l_instInhabitedOfMonad___redArg(v___x_1068_, v___x_1069_);
v___x_22455__overap_1071_ = lean_panic_fn_borrowed(v___x_1070_, v_msg_1014_);
lean_dec(v___x_1070_);
lean_inc(v___y_1018_);
lean_inc_ref(v___y_1017_);
lean_inc(v___y_1016_);
lean_inc_ref(v___y_1015_);
v___x_1072_ = lean_apply_5(v___x_22455__overap_1071_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, lean_box(0));
return v___x_1072_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___boxed(lean_object* v_msg_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_){
_start:
{
lean_object* v_res_1091_; 
v_res_1091_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg(v_msg_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_);
lean_dec(v___y_1089_);
lean_dec_ref(v___y_1088_);
lean_dec(v___y_1087_);
lean_dec_ref(v___y_1086_);
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__13(lean_object* v_xs_1092_, size_t v_sz_1093_, size_t v_i_1094_, lean_object* v_bs_1095_){
_start:
{
uint8_t v___x_1096_; 
v___x_1096_ = lean_usize_dec_lt(v_i_1094_, v_sz_1093_);
if (v___x_1096_ == 0)
{
return v_bs_1095_;
}
else
{
lean_object* v___x_1097_; lean_object* v_v_1098_; lean_object* v___x_1099_; lean_object* v_bs_x27_1100_; lean_object* v___x_1101_; size_t v___x_1102_; size_t v___x_1103_; lean_object* v___x_1104_; 
v___x_1097_ = l_Lean_instInhabitedExpr;
v_v_1098_ = lean_array_uget(v_bs_1095_, v_i_1094_);
v___x_1099_ = lean_unsigned_to_nat(0u);
v_bs_x27_1100_ = lean_array_uset(v_bs_1095_, v_i_1094_, v___x_1099_);
v___x_1101_ = lean_array_get_borrowed(v___x_1097_, v_xs_1092_, v_v_1098_);
lean_dec(v_v_1098_);
v___x_1102_ = ((size_t)1ULL);
v___x_1103_ = lean_usize_add(v_i_1094_, v___x_1102_);
lean_inc(v___x_1101_);
v___x_1104_ = lean_array_uset(v_bs_x27_1100_, v_i_1094_, v___x_1101_);
v_i_1094_ = v___x_1103_;
v_bs_1095_ = v___x_1104_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__13___boxed(lean_object* v_xs_1106_, lean_object* v_sz_1107_, lean_object* v_i_1108_, lean_object* v_bs_1109_){
_start:
{
size_t v_sz_boxed_1110_; size_t v_i_boxed_1111_; lean_object* v_res_1112_; 
v_sz_boxed_1110_ = lean_unbox_usize(v_sz_1107_);
lean_dec(v_sz_1107_);
v_i_boxed_1111_ = lean_unbox_usize(v_i_1108_);
lean_dec(v_i_1108_);
v_res_1112_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__13(v_xs_1106_, v_sz_boxed_1110_, v_i_boxed_1111_, v_bs_1109_);
lean_dec_ref(v_xs_1106_);
return v_res_1112_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15___redArg(lean_object* v_xs_1113_, lean_object* v_f_1114_, lean_object* v_as_1115_, lean_object* v_bs_1116_, lean_object* v_i_1117_, lean_object* v_cs_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_){
_start:
{
lean_object* v___x_1124_; uint8_t v___x_1125_; 
v___x_1124_ = lean_array_get_size(v_as_1115_);
v___x_1125_ = lean_nat_dec_lt(v_i_1117_, v___x_1124_);
if (v___x_1125_ == 0)
{
lean_object* v___x_1126_; 
lean_dec(v_i_1117_);
lean_dec_ref(v_f_1114_);
v___x_1126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1126_, 0, v_cs_1118_);
return v___x_1126_;
}
else
{
lean_object* v___x_1127_; uint8_t v___x_1128_; 
v___x_1127_ = lean_array_get_size(v_bs_1116_);
v___x_1128_ = lean_nat_dec_lt(v_i_1117_, v___x_1127_);
if (v___x_1128_ == 0)
{
lean_object* v___x_1129_; 
lean_dec(v_i_1117_);
lean_dec_ref(v_f_1114_);
v___x_1129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1129_, 0, v_cs_1118_);
return v___x_1129_;
}
else
{
lean_object* v_a_1130_; lean_object* v_b_1131_; size_t v_sz_1132_; size_t v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; 
v_a_1130_ = lean_array_fget_borrowed(v_as_1115_, v_i_1117_);
v_b_1131_ = lean_array_fget_borrowed(v_bs_1116_, v_i_1117_);
v_sz_1132_ = lean_array_size(v_b_1131_);
v___x_1133_ = ((size_t)0ULL);
lean_inc(v_b_1131_);
v___x_1134_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__13(v_xs_1113_, v_sz_1132_, v___x_1133_, v_b_1131_);
lean_inc_ref(v_f_1114_);
lean_inc(v___y_1122_);
lean_inc_ref(v___y_1121_);
lean_inc(v___y_1120_);
lean_inc_ref(v___y_1119_);
lean_inc(v_a_1130_);
v___x_1135_ = lean_apply_7(v_f_1114_, v_a_1130_, v___x_1134_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_, lean_box(0));
if (lean_obj_tag(v___x_1135_) == 0)
{
lean_object* v_a_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
v_a_1136_ = lean_ctor_get(v___x_1135_, 0);
lean_inc(v_a_1136_);
lean_dec_ref_known(v___x_1135_, 1);
v___x_1137_ = lean_unsigned_to_nat(1u);
v___x_1138_ = lean_nat_add(v_i_1117_, v___x_1137_);
lean_dec(v_i_1117_);
v___x_1139_ = lean_array_push(v_cs_1118_, v_a_1136_);
v_i_1117_ = v___x_1138_;
v_cs_1118_ = v___x_1139_;
goto _start;
}
else
{
lean_object* v_a_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1148_; 
lean_dec_ref(v_cs_1118_);
lean_dec(v_i_1117_);
lean_dec_ref(v_f_1114_);
v_a_1141_ = lean_ctor_get(v___x_1135_, 0);
v_isSharedCheck_1148_ = !lean_is_exclusive(v___x_1135_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1143_ = v___x_1135_;
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_a_1141_);
lean_dec(v___x_1135_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v___x_1146_; 
if (v_isShared_1144_ == 0)
{
v___x_1146_ = v___x_1143_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v_a_1141_);
v___x_1146_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
return v___x_1146_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15___redArg___boxed(lean_object* v_xs_1149_, lean_object* v_f_1150_, lean_object* v_as_1151_, lean_object* v_bs_1152_, lean_object* v_i_1153_, lean_object* v_cs_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_){
_start:
{
lean_object* v_res_1160_; 
v_res_1160_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15___redArg(v_xs_1149_, v_f_1150_, v_as_1151_, v_bs_1152_, v_i_1153_, v_cs_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_);
lean_dec(v___y_1158_);
lean_dec_ref(v___y_1157_);
lean_dec(v___y_1156_);
lean_dec_ref(v___y_1155_);
lean_dec_ref(v_bs_1152_);
lean_dec_ref(v_as_1151_);
lean_dec_ref(v_xs_1149_);
return v_res_1160_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; 
v___x_1164_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__2));
v___x_1165_ = lean_unsigned_to_nat(2u);
v___x_1166_ = lean_unsigned_to_nat(73u);
v___x_1167_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__1));
v___x_1168_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__0));
v___x_1169_ = l_mkPanicMessageWithDecl(v___x_1168_, v___x_1167_, v___x_1166_, v___x_1165_, v___x_1164_);
return v___x_1169_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; 
v___x_1171_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__4));
v___x_1172_ = lean_unsigned_to_nat(2u);
v___x_1173_ = lean_unsigned_to_nat(74u);
v___x_1174_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__1));
v___x_1175_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__0));
v___x_1176_ = l_mkPanicMessageWithDecl(v___x_1175_, v___x_1174_, v___x_1173_, v___x_1172_, v___x_1171_);
return v___x_1176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg(lean_object* v_f_1179_, lean_object* v_positions_1180_, lean_object* v_ys_1181_, lean_object* v_xs_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_){
_start:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; uint8_t v___x_1190_; 
v___x_1188_ = lean_array_get_size(v_positions_1180_);
v___x_1189_ = lean_array_get_size(v_ys_1181_);
v___x_1190_ = lean_nat_dec_eq(v___x_1188_, v___x_1189_);
if (v___x_1190_ == 0)
{
lean_object* v___x_1191_; lean_object* v___x_1192_; 
lean_dec_ref(v_f_1179_);
v___x_1191_ = lean_obj_once(&l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__3, &l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__3_once, _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__3);
v___x_1192_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg(v___x_1191_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_);
return v___x_1192_;
}
else
{
lean_object* v___x_1193_; lean_object* v___x_1194_; uint8_t v___x_1195_; 
v___x_1193_ = l_Lean_Elab_Structural_Positions_numIndices(v_positions_1180_);
v___x_1194_ = lean_array_get_size(v_xs_1182_);
v___x_1195_ = lean_nat_dec_eq(v___x_1193_, v___x_1194_);
lean_dec(v___x_1193_);
if (v___x_1195_ == 0)
{
lean_object* v___x_1196_; lean_object* v___x_1197_; 
lean_dec_ref(v_f_1179_);
v___x_1196_ = lean_obj_once(&l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__5, &l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__5_once, _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__5);
v___x_1197_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg(v___x_1196_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_);
return v___x_1197_;
}
else
{
lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1198_ = lean_unsigned_to_nat(0u);
v___x_1199_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__6));
v___x_1200_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15___redArg(v_xs_1182_, v_f_1179_, v_ys_1181_, v_positions_1180_, v___x_1198_, v___x_1199_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_);
return v___x_1200_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___boxed(lean_object* v_f_1201_, lean_object* v_positions_1202_, lean_object* v_ys_1203_, lean_object* v_xs_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_){
_start:
{
lean_object* v_res_1210_; 
v_res_1210_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg(v_f_1201_, v_positions_1202_, v_ys_1203_, v_xs_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_);
lean_dec(v___y_1208_);
lean_dec_ref(v___y_1207_);
lean_dec(v___y_1206_);
lean_dec_ref(v___y_1205_);
lean_dec_ref(v_xs_1204_);
lean_dec_ref(v_ys_1203_);
lean_dec_ref(v_positions_1202_);
return v_res_1210_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg(lean_object* v___x_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_funTypes_1214_, size_t v_sz_1215_, size_t v_i_1216_, lean_object* v_bs_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_){
_start:
{
uint8_t v___x_1223_; 
v___x_1223_ = lean_usize_dec_lt(v_i_1216_, v_sz_1215_);
if (v___x_1223_ == 0)
{
lean_object* v___x_1224_; 
lean_dec_ref(v_funTypes_1214_);
lean_dec_ref(v_a_1213_);
lean_dec_ref(v_a_1212_);
lean_dec_ref(v___x_1211_);
v___x_1224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1224_, 0, v_bs_1217_);
return v___x_1224_;
}
else
{
lean_object* v_v_1225_; lean_object* v_fst_1226_; lean_object* v_snd_1227_; lean_object* v___x_1228_; lean_object* v_bs_x27_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; 
v_v_1225_ = lean_array_uget_borrowed(v_bs_1217_, v_i_1216_);
v_fst_1226_ = lean_ctor_get(v_v_1225_, 0);
lean_inc(v_fst_1226_);
v_snd_1227_ = lean_ctor_get(v_v_1225_, 1);
lean_inc(v_snd_1227_);
v___x_1228_ = lean_unsigned_to_nat(0u);
v_bs_x27_1229_ = lean_array_uset(v_bs_1217_, v_i_1216_, v___x_1228_);
v___x_1230_ = lean_usize_to_nat(v_i_1216_);
lean_inc_ref(v_funTypes_1214_);
lean_inc_ref(v_a_1213_);
lean_inc_ref(v_a_1212_);
lean_inc_ref(v___x_1211_);
v___x_1231_ = l_Lean_Elab_Structural_mkBRecOnApp(v___x_1211_, v___x_1230_, v_a_1212_, v_a_1213_, v_funTypes_1214_, v_fst_1226_, v_snd_1227_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_);
if (lean_obj_tag(v___x_1231_) == 0)
{
lean_object* v_a_1232_; size_t v___x_1233_; size_t v___x_1234_; lean_object* v___x_1235_; 
v_a_1232_ = lean_ctor_get(v___x_1231_, 0);
lean_inc(v_a_1232_);
lean_dec_ref_known(v___x_1231_, 1);
v___x_1233_ = ((size_t)1ULL);
v___x_1234_ = lean_usize_add(v_i_1216_, v___x_1233_);
v___x_1235_ = lean_array_uset(v_bs_x27_1229_, v_i_1216_, v_a_1232_);
v_i_1216_ = v___x_1234_;
v_bs_1217_ = v___x_1235_;
goto _start;
}
else
{
lean_object* v_a_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1244_; 
lean_dec_ref(v_bs_x27_1229_);
lean_dec_ref(v_funTypes_1214_);
lean_dec_ref(v_a_1213_);
lean_dec_ref(v_a_1212_);
lean_dec_ref(v___x_1211_);
v_a_1237_ = lean_ctor_get(v___x_1231_, 0);
v_isSharedCheck_1244_ = !lean_is_exclusive(v___x_1231_);
if (v_isSharedCheck_1244_ == 0)
{
v___x_1239_ = v___x_1231_;
v_isShared_1240_ = v_isSharedCheck_1244_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_a_1237_);
lean_dec(v___x_1231_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1244_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v___x_1242_; 
if (v_isShared_1240_ == 0)
{
v___x_1242_ = v___x_1239_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v_a_1237_);
v___x_1242_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
return v___x_1242_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg___boxed(lean_object* v___x_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_, lean_object* v_funTypes_1248_, lean_object* v_sz_1249_, lean_object* v_i_1250_, lean_object* v_bs_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_){
_start:
{
size_t v_sz_boxed_1257_; size_t v_i_boxed_1258_; lean_object* v_res_1259_; 
v_sz_boxed_1257_ = lean_unbox_usize(v_sz_1249_);
lean_dec(v_sz_1249_);
v_i_boxed_1258_ = lean_unbox_usize(v_i_1250_);
lean_dec(v_i_1250_);
v_res_1259_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg(v___x_1245_, v_a_1246_, v_a_1247_, v_funTypes_1248_, v_sz_boxed_1257_, v_i_boxed_1258_, v_bs_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_);
lean_dec(v___y_1255_);
lean_dec_ref(v___y_1254_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
return v_res_1259_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__2(void){
_start:
{
lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; 
v___x_1263_ = lean_box(0);
v___x_1264_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__1));
v___x_1265_ = l_Lean_Expr_const___override(v___x_1264_, v___x_1263_);
return v___x_1265_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__4(void){
_start:
{
lean_object* v___x_1267_; lean_object* v___x_1268_; 
v___x_1267_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__3));
v___x_1268_ = l_Lean_stringToMessageData(v___x_1267_);
return v___x_1268_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__6(void){
_start:
{
lean_object* v___x_1270_; lean_object* v___x_1271_; 
v___x_1270_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__5));
v___x_1271_ = l_Lean_stringToMessageData(v___x_1270_);
return v___x_1271_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__8(void){
_start:
{
lean_object* v___x_1273_; lean_object* v___x_1274_; 
v___x_1273_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__7));
v___x_1274_ = l_Lean_stringToMessageData(v___x_1273_);
return v___x_1274_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__10(void){
_start:
{
lean_object* v___x_1276_; lean_object* v___x_1277_; 
v___x_1276_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__9));
v___x_1277_ = l_Lean_stringToMessageData(v___x_1276_);
return v___x_1277_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__12(void){
_start:
{
lean_object* v___x_1279_; lean_object* v___x_1280_; 
v___x_1279_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__11));
v___x_1280_ = l_Lean_stringToMessageData(v___x_1279_);
return v___x_1280_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2(lean_object* v_recArgInfos_1281_, lean_object* v_a_1282_, lean_object* v___x_1283_, size_t v___x_1284_, lean_object* v_fixedParamPerms_1285_, lean_object* v_xs_1286_, lean_object* v___x_1287_, lean_object* v_preDefs_1288_, lean_object* v_numIndices_1289_, lean_object* v___f_1290_, lean_object* v___x_1291_, uint8_t v_a_1292_, lean_object* v___x_1293_, lean_object* v___f_1294_, lean_object* v_funTypes_1295_, lean_object* v_motives_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_){
_start:
{
lean_object* v___y_1303_; lean_object* v___y_1304_; lean_object* v___y_1305_; lean_object* v___y_1306_; lean_object* v___y_1307_; lean_object* v___y_1308_; lean_object* v___y_1343_; lean_object* v_FArgs_1344_; lean_object* v___y_1345_; lean_object* v___y_1346_; lean_object* v___y_1347_; lean_object* v___y_1348_; lean_object* v___y_1400_; lean_object* v___y_1401_; lean_object* v___y_1402_; lean_object* v___y_1403_; lean_object* v___y_1404_; lean_object* v___y_1405_; lean_object* v___y_1422_; lean_object* v___y_1423_; lean_object* v___y_1424_; lean_object* v___y_1425_; lean_object* v___y_1426_; lean_object* v___y_1427_; lean_object* v___x_1512_; 
lean_inc_ref(v___f_1294_);
lean_inc(v___y_1300_);
lean_inc_ref(v___y_1299_);
lean_inc(v___y_1298_);
lean_inc_ref(v___y_1297_);
v___x_1512_ = lean_apply_5(v___f_1294_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, lean_box(0));
if (lean_obj_tag(v___x_1512_) == 0)
{
lean_object* v_a_1513_; uint8_t v___x_1514_; 
v_a_1513_ = lean_ctor_get(v___x_1512_, 0);
lean_inc(v_a_1513_);
lean_dec_ref_known(v___x_1512_, 1);
v___x_1514_ = lean_unbox(v_a_1513_);
lean_dec(v_a_1513_);
if (v___x_1514_ == 0)
{
goto v___jp_1465_;
}
else
{
lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; 
v___x_1515_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__10, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__10);
lean_inc_ref(v_funTypes_1295_);
v___x_1516_ = lean_array_to_list(v_funTypes_1295_);
v___x_1517_ = lean_box(0);
v___x_1518_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_1516_, v___x_1517_);
v___x_1519_ = l_Lean_MessageData_ofList(v___x_1518_);
v___x_1520_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1520_, 0, v___x_1515_);
lean_ctor_set(v___x_1520_, 1, v___x_1519_);
v___x_1521_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__12, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__12_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__12);
v___x_1522_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1522_, 0, v___x_1520_);
lean_ctor_set(v___x_1522_, 1, v___x_1521_);
lean_inc_ref(v_motives_1296_);
v___x_1523_ = lean_array_to_list(v_motives_1296_);
v___x_1524_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_1523_, v___x_1517_);
v___x_1525_ = l_Lean_MessageData_ofList(v___x_1524_);
v___x_1526_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1526_, 0, v___x_1522_);
lean_ctor_set(v___x_1526_, 1, v___x_1525_);
lean_inc(v___x_1291_);
v___x_1527_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_1291_, v___x_1526_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_);
if (lean_obj_tag(v___x_1527_) == 0)
{
lean_dec_ref_known(v___x_1527_, 1);
goto v___jp_1465_;
}
else
{
lean_object* v_a_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1535_; 
lean_dec_ref(v_motives_1296_);
lean_dec_ref(v_funTypes_1295_);
lean_dec_ref(v___f_1294_);
lean_dec(v___x_1291_);
lean_dec_ref(v___f_1290_);
lean_dec_ref(v_preDefs_1288_);
lean_dec(v___x_1287_);
lean_dec_ref(v_xs_1286_);
lean_dec_ref(v_fixedParamPerms_1285_);
lean_dec_ref(v___x_1283_);
lean_dec_ref(v_recArgInfos_1281_);
v_a_1528_ = lean_ctor_get(v___x_1527_, 0);
v_isSharedCheck_1535_ = !lean_is_exclusive(v___x_1527_);
if (v_isSharedCheck_1535_ == 0)
{
v___x_1530_ = v___x_1527_;
v_isShared_1531_ = v_isSharedCheck_1535_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_a_1528_);
lean_dec(v___x_1527_);
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
else
{
lean_object* v_a_1536_; lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1543_; 
lean_dec_ref(v_motives_1296_);
lean_dec_ref(v_funTypes_1295_);
lean_dec_ref(v___f_1294_);
lean_dec(v___x_1291_);
lean_dec_ref(v___f_1290_);
lean_dec_ref(v_preDefs_1288_);
lean_dec(v___x_1287_);
lean_dec_ref(v_xs_1286_);
lean_dec_ref(v_fixedParamPerms_1285_);
lean_dec_ref(v___x_1283_);
lean_dec_ref(v_recArgInfos_1281_);
v_a_1536_ = lean_ctor_get(v___x_1512_, 0);
v_isSharedCheck_1543_ = !lean_is_exclusive(v___x_1512_);
if (v_isSharedCheck_1543_ == 0)
{
v___x_1538_ = v___x_1512_;
v_isShared_1539_ = v_isSharedCheck_1543_;
goto v_resetjp_1537_;
}
else
{
lean_inc(v_a_1536_);
lean_dec(v___x_1512_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1543_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
lean_object* v___x_1541_; 
if (v_isShared_1539_ == 0)
{
v___x_1541_ = v___x_1538_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v_a_1536_);
v___x_1541_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1540_;
}
v_reusejp_1540_:
{
return v___x_1541_;
}
}
}
v___jp_1302_:
{
lean_object* v___x_1309_; size_t v_sz_1310_; lean_object* v___x_1311_; 
v___x_1309_ = l_Array_zip___redArg(v_recArgInfos_1281_, v_a_1282_);
lean_dec_ref(v_recArgInfos_1281_);
v_sz_1310_ = lean_array_size(v___x_1309_);
v___x_1311_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg(v___x_1283_, v___y_1303_, v___y_1304_, v_funTypes_1295_, v_sz_1310_, v___x_1284_, v___x_1309_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_);
if (lean_obj_tag(v___x_1311_) == 0)
{
lean_object* v_a_1312_; lean_object* v___x_1313_; size_t v_sz_1314_; lean_object* v___x_1315_; 
v_a_1312_ = lean_ctor_get(v___x_1311_, 0);
lean_inc(v_a_1312_);
lean_dec_ref_known(v___x_1311_, 1);
v___x_1313_ = l_Array_zip___redArg(v_a_1282_, v_a_1312_);
lean_dec(v_a_1312_);
v_sz_1314_ = lean_array_size(v___x_1313_);
v___x_1315_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg(v_fixedParamPerms_1285_, v_xs_1286_, v_sz_1314_, v___x_1284_, v___x_1313_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_);
if (lean_obj_tag(v___x_1315_) == 0)
{
lean_object* v_a_1316_; lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1325_; 
v_a_1316_ = lean_ctor_get(v___x_1315_, 0);
v_isSharedCheck_1325_ = !lean_is_exclusive(v___x_1315_);
if (v_isSharedCheck_1325_ == 0)
{
v___x_1318_ = v___x_1315_;
v_isShared_1319_ = v_isSharedCheck_1325_;
goto v_resetjp_1317_;
}
else
{
lean_inc(v_a_1316_);
lean_dec(v___x_1315_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1325_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1323_; 
v___x_1320_ = lean_mk_empty_array_with_capacity(v___x_1287_);
v___x_1321_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9(v_preDefs_1288_, v_a_1316_, v___x_1287_, v___x_1320_);
lean_dec(v_a_1316_);
lean_dec_ref(v_preDefs_1288_);
if (v_isShared_1319_ == 0)
{
lean_ctor_set(v___x_1318_, 0, v___x_1321_);
v___x_1323_ = v___x_1318_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v___x_1321_);
v___x_1323_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
return v___x_1323_;
}
}
}
else
{
lean_object* v_a_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1333_; 
lean_dec_ref(v_preDefs_1288_);
lean_dec(v___x_1287_);
v_a_1326_ = lean_ctor_get(v___x_1315_, 0);
v_isSharedCheck_1333_ = !lean_is_exclusive(v___x_1315_);
if (v_isSharedCheck_1333_ == 0)
{
v___x_1328_ = v___x_1315_;
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_a_1326_);
lean_dec(v___x_1315_);
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
else
{
lean_object* v_a_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1341_; 
lean_dec_ref(v_preDefs_1288_);
lean_dec(v___x_1287_);
lean_dec_ref(v_xs_1286_);
lean_dec_ref(v_fixedParamPerms_1285_);
v_a_1334_ = lean_ctor_get(v___x_1311_, 0);
v_isSharedCheck_1341_ = !lean_is_exclusive(v___x_1311_);
if (v_isSharedCheck_1341_ == 0)
{
v___x_1336_ = v___x_1311_;
v_isShared_1337_ = v_isSharedCheck_1341_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_a_1334_);
lean_dec(v___x_1311_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1341_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
lean_object* v___x_1339_; 
if (v_isShared_1337_ == 0)
{
v___x_1339_ = v___x_1336_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v_a_1334_);
v___x_1339_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
return v___x_1339_;
}
}
}
}
v___jp_1342_:
{
lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; 
lean_inc_ref(v___y_1343_);
lean_inc(v___x_1287_);
v___x_1349_ = lean_apply_1(v___y_1343_, v___x_1287_);
v___x_1350_ = lean_unsigned_to_nat(1u);
v___x_1351_ = lean_nat_add(v_numIndices_1289_, v___x_1350_);
v___x_1352_ = lean_box(0);
v___x_1353_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__2);
v___x_1354_ = lean_mk_array(v___x_1351_, v___x_1353_);
v___x_1355_ = l_Lean_mkAppN(v___x_1349_, v___x_1354_);
lean_dec_ref(v___x_1354_);
v___x_1356_ = lean_array_get_size(v___x_1283_);
v___x_1357_ = l_Lean_Meta_inferArgumentTypesN(v___x_1356_, v___x_1355_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_);
if (lean_obj_tag(v___x_1357_) == 0)
{
lean_object* v_a_1358_; lean_object* v___x_1359_; 
v_a_1358_ = lean_ctor_get(v___x_1357_, 0);
lean_inc(v_a_1358_);
lean_dec_ref_known(v___x_1357_, 1);
v___x_1359_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg(v___f_1290_, v___x_1283_, v_a_1358_, v_FArgs_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_);
lean_dec_ref(v_FArgs_1344_);
lean_dec(v_a_1358_);
if (lean_obj_tag(v___x_1359_) == 0)
{
lean_object* v_toCold_1360_; lean_object* v_options_1361_; uint8_t v_hasTrace_1362_; 
v_toCold_1360_ = lean_ctor_get(v___y_1347_, 0);
v_options_1361_ = lean_ctor_get(v_toCold_1360_, 2);
v_hasTrace_1362_ = lean_ctor_get_uint8(v_options_1361_, sizeof(void*)*1);
if (v_hasTrace_1362_ == 0)
{
lean_object* v_a_1363_; 
lean_dec(v___x_1291_);
v_a_1363_ = lean_ctor_get(v___x_1359_, 0);
lean_inc(v_a_1363_);
lean_dec_ref_known(v___x_1359_, 1);
v___y_1303_ = v___y_1343_;
v___y_1304_ = v_a_1363_;
v___y_1305_ = v___y_1345_;
v___y_1306_ = v___y_1346_;
v___y_1307_ = v___y_1347_;
v___y_1308_ = v___y_1348_;
goto v___jp_1302_;
}
else
{
lean_object* v_a_1364_; lean_object* v_inheritedTraceOptions_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; uint8_t v___x_1368_; 
v_a_1364_ = lean_ctor_get(v___x_1359_, 0);
lean_inc(v_a_1364_);
lean_dec_ref_known(v___x_1359_, 1);
v_inheritedTraceOptions_1365_ = lean_ctor_get(v_toCold_1360_, 11);
v___x_1366_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___closed__1));
lean_inc(v___x_1291_);
v___x_1367_ = l_Lean_Name_append(v___x_1366_, v___x_1291_);
v___x_1368_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1365_, v_options_1361_, v___x_1367_);
lean_dec(v___x_1367_);
if (v___x_1368_ == 0)
{
lean_dec(v___x_1291_);
v___y_1303_ = v___y_1343_;
v___y_1304_ = v_a_1364_;
v___y_1305_ = v___y_1345_;
v___y_1306_ = v___y_1346_;
v___y_1307_ = v___y_1347_;
v___y_1308_ = v___y_1348_;
goto v___jp_1302_;
}
else
{
lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; 
v___x_1369_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__4);
lean_inc(v_a_1364_);
v___x_1370_ = lean_array_to_list(v_a_1364_);
v___x_1371_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_1370_, v___x_1352_);
v___x_1372_ = l_Lean_MessageData_ofList(v___x_1371_);
v___x_1373_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1373_, 0, v___x_1369_);
lean_ctor_set(v___x_1373_, 1, v___x_1372_);
v___x_1374_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_1291_, v___x_1373_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_);
if (lean_obj_tag(v___x_1374_) == 0)
{
lean_dec_ref_known(v___x_1374_, 1);
v___y_1303_ = v___y_1343_;
v___y_1304_ = v_a_1364_;
v___y_1305_ = v___y_1345_;
v___y_1306_ = v___y_1346_;
v___y_1307_ = v___y_1347_;
v___y_1308_ = v___y_1348_;
goto v___jp_1302_;
}
else
{
lean_object* v_a_1375_; lean_object* v___x_1377_; uint8_t v_isShared_1378_; uint8_t v_isSharedCheck_1382_; 
lean_dec(v_a_1364_);
lean_dec_ref(v___y_1343_);
lean_dec_ref(v_funTypes_1295_);
lean_dec_ref(v_preDefs_1288_);
lean_dec(v___x_1287_);
lean_dec_ref(v_xs_1286_);
lean_dec_ref(v_fixedParamPerms_1285_);
lean_dec_ref(v___x_1283_);
lean_dec_ref(v_recArgInfos_1281_);
v_a_1375_ = lean_ctor_get(v___x_1374_, 0);
v_isSharedCheck_1382_ = !lean_is_exclusive(v___x_1374_);
if (v_isSharedCheck_1382_ == 0)
{
v___x_1377_ = v___x_1374_;
v_isShared_1378_ = v_isSharedCheck_1382_;
goto v_resetjp_1376_;
}
else
{
lean_inc(v_a_1375_);
lean_dec(v___x_1374_);
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
}
}
else
{
lean_object* v_a_1383_; lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1390_; 
lean_dec_ref(v___y_1343_);
lean_dec_ref(v_funTypes_1295_);
lean_dec(v___x_1291_);
lean_dec_ref(v_preDefs_1288_);
lean_dec(v___x_1287_);
lean_dec_ref(v_xs_1286_);
lean_dec_ref(v_fixedParamPerms_1285_);
lean_dec_ref(v___x_1283_);
lean_dec_ref(v_recArgInfos_1281_);
v_a_1383_ = lean_ctor_get(v___x_1359_, 0);
v_isSharedCheck_1390_ = !lean_is_exclusive(v___x_1359_);
if (v_isSharedCheck_1390_ == 0)
{
v___x_1385_ = v___x_1359_;
v_isShared_1386_ = v_isSharedCheck_1390_;
goto v_resetjp_1384_;
}
else
{
lean_inc(v_a_1383_);
lean_dec(v___x_1359_);
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
else
{
lean_object* v_a_1391_; lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1398_; 
lean_dec_ref(v_FArgs_1344_);
lean_dec_ref(v___y_1343_);
lean_dec_ref(v_funTypes_1295_);
lean_dec(v___x_1291_);
lean_dec_ref(v___f_1290_);
lean_dec_ref(v_preDefs_1288_);
lean_dec(v___x_1287_);
lean_dec_ref(v_xs_1286_);
lean_dec_ref(v_fixedParamPerms_1285_);
lean_dec_ref(v___x_1283_);
lean_dec_ref(v_recArgInfos_1281_);
v_a_1391_ = lean_ctor_get(v___x_1357_, 0);
v_isSharedCheck_1398_ = !lean_is_exclusive(v___x_1357_);
if (v_isSharedCheck_1398_ == 0)
{
v___x_1393_ = v___x_1357_;
v_isShared_1394_ = v_isSharedCheck_1398_;
goto v_resetjp_1392_;
}
else
{
lean_inc(v_a_1391_);
lean_dec(v___x_1357_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1398_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
lean_object* v___x_1396_; 
if (v_isShared_1394_ == 0)
{
v___x_1396_ = v___x_1393_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v_a_1391_);
v___x_1396_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
return v___x_1396_;
}
}
}
}
v___jp_1399_:
{
if (v_a_1292_ == 0)
{
lean_object* v___x_1406_; lean_object* v_levelParams_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; size_t v_sz_1410_; lean_object* v___x_1411_; 
v___x_1406_ = lean_array_get_borrowed(v___x_1293_, v_preDefs_1288_, v___x_1287_);
v_levelParams_1407_ = lean_ctor_get(v___x_1406_, 1);
v___x_1408_ = lean_box(0);
lean_inc(v_levelParams_1407_);
v___x_1409_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__15(v_levelParams_1407_, v___x_1408_);
v_sz_1410_ = lean_array_size(v___y_1401_);
lean_inc_ref(v_preDefs_1288_);
v___x_1411_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___redArg(v_preDefs_1288_, v_xs_1286_, v_a_1292_, v___x_1409_, v_sz_1410_, v___x_1284_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_);
if (lean_obj_tag(v___x_1411_) == 0)
{
lean_object* v_a_1412_; 
v_a_1412_ = lean_ctor_get(v___x_1411_, 0);
lean_inc(v_a_1412_);
lean_dec_ref_known(v___x_1411_, 1);
v___y_1343_ = v___y_1400_;
v_FArgs_1344_ = v_a_1412_;
v___y_1345_ = v___y_1402_;
v___y_1346_ = v___y_1403_;
v___y_1347_ = v___y_1404_;
v___y_1348_ = v___y_1405_;
goto v___jp_1342_;
}
else
{
lean_object* v_a_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1420_; 
lean_dec_ref(v___y_1400_);
lean_dec_ref(v_funTypes_1295_);
lean_dec(v___x_1291_);
lean_dec_ref(v___f_1290_);
lean_dec_ref(v_preDefs_1288_);
lean_dec(v___x_1287_);
lean_dec_ref(v_xs_1286_);
lean_dec_ref(v_fixedParamPerms_1285_);
lean_dec_ref(v___x_1283_);
lean_dec_ref(v_recArgInfos_1281_);
v_a_1413_ = lean_ctor_get(v___x_1411_, 0);
v_isSharedCheck_1420_ = !lean_is_exclusive(v___x_1411_);
if (v_isSharedCheck_1420_ == 0)
{
v___x_1415_ = v___x_1411_;
v_isShared_1416_ = v_isSharedCheck_1420_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_a_1413_);
lean_dec(v___x_1411_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1420_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v___x_1418_; 
if (v_isShared_1416_ == 0)
{
v___x_1418_ = v___x_1415_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v_a_1413_);
v___x_1418_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
return v___x_1418_;
}
}
}
}
else
{
v___y_1343_ = v___y_1400_;
v_FArgs_1344_ = v___y_1401_;
v___y_1345_ = v___y_1402_;
v___y_1346_ = v___y_1403_;
v___y_1347_ = v___y_1404_;
v___y_1348_ = v___y_1405_;
goto v___jp_1342_;
}
}
v___jp_1421_:
{
size_t v_sz_1428_; lean_object* v___x_1429_; 
v_sz_1428_ = lean_array_size(v_recArgInfos_1281_);
lean_inc_ref(v___y_1422_);
lean_inc_ref(v_preDefs_1288_);
lean_inc_ref(v___x_1283_);
lean_inc_ref_n(v_recArgInfos_1281_, 2);
v___x_1429_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg(v_a_1292_, v_a_1282_, v___y_1423_, v_recArgInfos_1281_, v___x_1283_, v_preDefs_1288_, v___y_1422_, v_sz_1428_, v___x_1284_, v_recArgInfos_1281_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_);
lean_dec_ref(v___y_1423_);
if (lean_obj_tag(v___x_1429_) == 0)
{
lean_object* v_a_1430_; lean_object* v___x_1431_; 
v_a_1430_ = lean_ctor_get(v___x_1429_, 0);
lean_inc(v_a_1430_);
lean_dec_ref_known(v___x_1429_, 1);
lean_inc(v___y_1427_);
lean_inc_ref(v___y_1426_);
lean_inc(v___y_1425_);
lean_inc_ref(v___y_1424_);
v___x_1431_ = lean_apply_5(v___f_1294_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_, lean_box(0));
if (lean_obj_tag(v___x_1431_) == 0)
{
lean_object* v_a_1432_; uint8_t v___x_1433_; 
v_a_1432_ = lean_ctor_get(v___x_1431_, 0);
lean_inc(v_a_1432_);
lean_dec_ref_known(v___x_1431_, 1);
v___x_1433_ = lean_unbox(v_a_1432_);
lean_dec(v_a_1432_);
if (v___x_1433_ == 0)
{
v___y_1400_ = v___y_1422_;
v___y_1401_ = v_a_1430_;
v___y_1402_ = v___y_1424_;
v___y_1403_ = v___y_1425_;
v___y_1404_ = v___y_1426_;
v___y_1405_ = v___y_1427_;
goto v___jp_1399_;
}
else
{
lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; 
v___x_1434_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__6, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__6);
lean_inc(v_a_1430_);
v___x_1435_ = lean_array_to_list(v_a_1430_);
v___x_1436_ = lean_box(0);
v___x_1437_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_1435_, v___x_1436_);
v___x_1438_ = l_Lean_MessageData_ofList(v___x_1437_);
v___x_1439_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1439_, 0, v___x_1434_);
lean_ctor_set(v___x_1439_, 1, v___x_1438_);
lean_inc(v___x_1291_);
v___x_1440_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_1291_, v___x_1439_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_);
if (lean_obj_tag(v___x_1440_) == 0)
{
lean_dec_ref_known(v___x_1440_, 1);
v___y_1400_ = v___y_1422_;
v___y_1401_ = v_a_1430_;
v___y_1402_ = v___y_1424_;
v___y_1403_ = v___y_1425_;
v___y_1404_ = v___y_1426_;
v___y_1405_ = v___y_1427_;
goto v___jp_1399_;
}
else
{
lean_object* v_a_1441_; lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1448_; 
lean_dec(v_a_1430_);
lean_dec_ref(v___y_1422_);
lean_dec_ref(v_funTypes_1295_);
lean_dec(v___x_1291_);
lean_dec_ref(v___f_1290_);
lean_dec_ref(v_preDefs_1288_);
lean_dec(v___x_1287_);
lean_dec_ref(v_xs_1286_);
lean_dec_ref(v_fixedParamPerms_1285_);
lean_dec_ref(v___x_1283_);
lean_dec_ref(v_recArgInfos_1281_);
v_a_1441_ = lean_ctor_get(v___x_1440_, 0);
v_isSharedCheck_1448_ = !lean_is_exclusive(v___x_1440_);
if (v_isSharedCheck_1448_ == 0)
{
v___x_1443_ = v___x_1440_;
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
else
{
lean_inc(v_a_1441_);
lean_dec(v___x_1440_);
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
}
else
{
lean_object* v_a_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1456_; 
lean_dec(v_a_1430_);
lean_dec_ref(v___y_1422_);
lean_dec_ref(v_funTypes_1295_);
lean_dec(v___x_1291_);
lean_dec_ref(v___f_1290_);
lean_dec_ref(v_preDefs_1288_);
lean_dec(v___x_1287_);
lean_dec_ref(v_xs_1286_);
lean_dec_ref(v_fixedParamPerms_1285_);
lean_dec_ref(v___x_1283_);
lean_dec_ref(v_recArgInfos_1281_);
v_a_1449_ = lean_ctor_get(v___x_1431_, 0);
v_isSharedCheck_1456_ = !lean_is_exclusive(v___x_1431_);
if (v_isSharedCheck_1456_ == 0)
{
v___x_1451_ = v___x_1431_;
v_isShared_1452_ = v_isSharedCheck_1456_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_a_1449_);
lean_dec(v___x_1431_);
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
lean_dec_ref(v___y_1422_);
lean_dec_ref(v_funTypes_1295_);
lean_dec_ref(v___f_1294_);
lean_dec(v___x_1291_);
lean_dec_ref(v___f_1290_);
lean_dec_ref(v_preDefs_1288_);
lean_dec(v___x_1287_);
lean_dec_ref(v_xs_1286_);
lean_dec_ref(v_fixedParamPerms_1285_);
lean_dec_ref(v___x_1283_);
lean_dec_ref(v_recArgInfos_1281_);
v_a_1457_ = lean_ctor_get(v___x_1429_, 0);
v_isSharedCheck_1464_ = !lean_is_exclusive(v___x_1429_);
if (v_isSharedCheck_1464_ == 0)
{
v___x_1459_ = v___x_1429_;
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
else
{
lean_inc(v_a_1457_);
lean_dec(v___x_1429_);
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
v___jp_1465_:
{
lean_object* v___x_1466_; 
v___x_1466_ = l_Lean_Elab_Structural_mkBRecOnConst(v_recArgInfos_1281_, v___x_1283_, v_motives_1296_, v_a_1292_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_);
lean_dec_ref(v_motives_1296_);
if (lean_obj_tag(v___x_1466_) == 0)
{
lean_object* v_a_1467_; lean_object* v___x_1468_; 
v_a_1467_ = lean_ctor_get(v___x_1466_, 0);
lean_inc_n(v_a_1467_, 2);
lean_dec_ref_known(v___x_1466_, 1);
lean_inc_ref(v___x_1283_);
v___x_1468_ = l_Lean_Elab_Structural_inferBRecOnFTypes(v_recArgInfos_1281_, v___x_1283_, v_a_1467_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_);
if (lean_obj_tag(v___x_1468_) == 0)
{
lean_object* v_a_1469_; lean_object* v___x_1470_; 
v_a_1469_ = lean_ctor_get(v___x_1468_, 0);
lean_inc(v_a_1469_);
lean_dec_ref_known(v___x_1468_, 1);
lean_inc_ref(v___f_1294_);
lean_inc(v___y_1300_);
lean_inc_ref(v___y_1299_);
lean_inc(v___y_1298_);
lean_inc_ref(v___y_1297_);
v___x_1470_ = lean_apply_5(v___f_1294_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, lean_box(0));
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
v___y_1422_ = v_a_1467_;
v___y_1423_ = v_a_1469_;
v___y_1424_ = v___y_1297_;
v___y_1425_ = v___y_1298_;
v___y_1426_ = v___y_1299_;
v___y_1427_ = v___y_1300_;
goto v___jp_1421_;
}
else
{
lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; 
v___x_1473_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__8);
lean_inc(v_a_1469_);
v___x_1474_ = lean_array_to_list(v_a_1469_);
v___x_1475_ = lean_box(0);
v___x_1476_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_1474_, v___x_1475_);
v___x_1477_ = l_Lean_MessageData_ofList(v___x_1476_);
v___x_1478_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1478_, 0, v___x_1473_);
lean_ctor_set(v___x_1478_, 1, v___x_1477_);
lean_inc(v___x_1291_);
v___x_1479_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_1291_, v___x_1478_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_);
if (lean_obj_tag(v___x_1479_) == 0)
{
lean_dec_ref_known(v___x_1479_, 1);
v___y_1422_ = v_a_1467_;
v___y_1423_ = v_a_1469_;
v___y_1424_ = v___y_1297_;
v___y_1425_ = v___y_1298_;
v___y_1426_ = v___y_1299_;
v___y_1427_ = v___y_1300_;
goto v___jp_1421_;
}
else
{
lean_object* v_a_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1487_; 
lean_dec(v_a_1469_);
lean_dec(v_a_1467_);
lean_dec_ref(v_funTypes_1295_);
lean_dec_ref(v___f_1294_);
lean_dec(v___x_1291_);
lean_dec_ref(v___f_1290_);
lean_dec_ref(v_preDefs_1288_);
lean_dec(v___x_1287_);
lean_dec_ref(v_xs_1286_);
lean_dec_ref(v_fixedParamPerms_1285_);
lean_dec_ref(v___x_1283_);
lean_dec_ref(v_recArgInfos_1281_);
v_a_1480_ = lean_ctor_get(v___x_1479_, 0);
v_isSharedCheck_1487_ = !lean_is_exclusive(v___x_1479_);
if (v_isSharedCheck_1487_ == 0)
{
v___x_1482_ = v___x_1479_;
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_a_1480_);
lean_dec(v___x_1479_);
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
}
else
{
lean_object* v_a_1488_; lean_object* v___x_1490_; uint8_t v_isShared_1491_; uint8_t v_isSharedCheck_1495_; 
lean_dec(v_a_1469_);
lean_dec(v_a_1467_);
lean_dec_ref(v_funTypes_1295_);
lean_dec_ref(v___f_1294_);
lean_dec(v___x_1291_);
lean_dec_ref(v___f_1290_);
lean_dec_ref(v_preDefs_1288_);
lean_dec(v___x_1287_);
lean_dec_ref(v_xs_1286_);
lean_dec_ref(v_fixedParamPerms_1285_);
lean_dec_ref(v___x_1283_);
lean_dec_ref(v_recArgInfos_1281_);
v_a_1488_ = lean_ctor_get(v___x_1470_, 0);
v_isSharedCheck_1495_ = !lean_is_exclusive(v___x_1470_);
if (v_isSharedCheck_1495_ == 0)
{
v___x_1490_ = v___x_1470_;
v_isShared_1491_ = v_isSharedCheck_1495_;
goto v_resetjp_1489_;
}
else
{
lean_inc(v_a_1488_);
lean_dec(v___x_1470_);
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
lean_dec(v_a_1467_);
lean_dec_ref(v_funTypes_1295_);
lean_dec_ref(v___f_1294_);
lean_dec(v___x_1291_);
lean_dec_ref(v___f_1290_);
lean_dec_ref(v_preDefs_1288_);
lean_dec(v___x_1287_);
lean_dec_ref(v_xs_1286_);
lean_dec_ref(v_fixedParamPerms_1285_);
lean_dec_ref(v___x_1283_);
lean_dec_ref(v_recArgInfos_1281_);
v_a_1496_ = lean_ctor_get(v___x_1468_, 0);
v_isSharedCheck_1503_ = !lean_is_exclusive(v___x_1468_);
if (v_isSharedCheck_1503_ == 0)
{
v___x_1498_ = v___x_1468_;
v_isShared_1499_ = v_isSharedCheck_1503_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_a_1496_);
lean_dec(v___x_1468_);
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
else
{
lean_object* v_a_1504_; lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1511_; 
lean_dec_ref(v_funTypes_1295_);
lean_dec_ref(v___f_1294_);
lean_dec(v___x_1291_);
lean_dec_ref(v___f_1290_);
lean_dec_ref(v_preDefs_1288_);
lean_dec(v___x_1287_);
lean_dec_ref(v_xs_1286_);
lean_dec_ref(v_fixedParamPerms_1285_);
lean_dec_ref(v___x_1283_);
lean_dec_ref(v_recArgInfos_1281_);
v_a_1504_ = lean_ctor_get(v___x_1466_, 0);
v_isSharedCheck_1511_ = !lean_is_exclusive(v___x_1466_);
if (v_isSharedCheck_1511_ == 0)
{
v___x_1506_ = v___x_1466_;
v_isShared_1507_ = v_isSharedCheck_1511_;
goto v_resetjp_1505_;
}
else
{
lean_inc(v_a_1504_);
lean_dec(v___x_1466_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1511_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
lean_object* v___x_1509_; 
if (v_isShared_1507_ == 0)
{
v___x_1509_ = v___x_1506_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v_a_1504_);
v___x_1509_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
return v___x_1509_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___boxed(lean_object** _args){
lean_object* v_recArgInfos_1544_ = _args[0];
lean_object* v_a_1545_ = _args[1];
lean_object* v___x_1546_ = _args[2];
lean_object* v___x_1547_ = _args[3];
lean_object* v_fixedParamPerms_1548_ = _args[4];
lean_object* v_xs_1549_ = _args[5];
lean_object* v___x_1550_ = _args[6];
lean_object* v_preDefs_1551_ = _args[7];
lean_object* v_numIndices_1552_ = _args[8];
lean_object* v___f_1553_ = _args[9];
lean_object* v___x_1554_ = _args[10];
lean_object* v_a_1555_ = _args[11];
lean_object* v___x_1556_ = _args[12];
lean_object* v___f_1557_ = _args[13];
lean_object* v_funTypes_1558_ = _args[14];
lean_object* v_motives_1559_ = _args[15];
lean_object* v___y_1560_ = _args[16];
lean_object* v___y_1561_ = _args[17];
lean_object* v___y_1562_ = _args[18];
lean_object* v___y_1563_ = _args[19];
lean_object* v___y_1564_ = _args[20];
_start:
{
size_t v___x_27633__boxed_1565_; uint8_t v_a_27637__boxed_1566_; lean_object* v_res_1567_; 
v___x_27633__boxed_1565_ = lean_unbox_usize(v___x_1547_);
lean_dec(v___x_1547_);
v_a_27637__boxed_1566_ = lean_unbox(v_a_1555_);
v_res_1567_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2(v_recArgInfos_1544_, v_a_1545_, v___x_1546_, v___x_27633__boxed_1565_, v_fixedParamPerms_1548_, v_xs_1549_, v___x_1550_, v_preDefs_1551_, v_numIndices_1552_, v___f_1553_, v___x_1554_, v_a_27637__boxed_1566_, v___x_1556_, v___f_1557_, v_funTypes_1558_, v_motives_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_);
lean_dec(v___y_1563_);
lean_dec_ref(v___y_1562_);
lean_dec(v___y_1561_);
lean_dec_ref(v___y_1560_);
lean_dec_ref(v___x_1556_);
lean_dec(v_numIndices_1552_);
lean_dec_ref(v_a_1545_);
return v_res_1567_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__20___redArg(lean_object* v_a_1568_, lean_object* v_funTypes_1569_, size_t v_sz_1570_, size_t v_i_1571_, lean_object* v_bs_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_){
_start:
{
uint8_t v___x_1578_; 
v___x_1578_ = lean_usize_dec_lt(v_i_1571_, v_sz_1570_);
if (v___x_1578_ == 0)
{
lean_object* v___x_1579_; 
v___x_1579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1579_, 0, v_bs_1572_);
return v___x_1579_;
}
else
{
lean_object* v___x_1580_; lean_object* v_v_1581_; lean_object* v___x_1582_; lean_object* v_bs_x27_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; 
v___x_1580_ = l_Lean_instInhabitedExpr;
v_v_1581_ = lean_array_uget(v_bs_1572_, v_i_1571_);
v___x_1582_ = lean_unsigned_to_nat(0u);
v_bs_x27_1583_ = lean_array_uset(v_bs_1572_, v_i_1571_, v___x_1582_);
v___x_1584_ = lean_usize_to_nat(v_i_1571_);
v___x_1585_ = lean_array_get_borrowed(v___x_1580_, v_a_1568_, v___x_1584_);
v___x_1586_ = lean_array_get_borrowed(v___x_1580_, v_funTypes_1569_, v___x_1584_);
lean_dec(v___x_1584_);
lean_inc(v___x_1586_);
lean_inc(v___x_1585_);
v___x_1587_ = l_Lean_Elab_Structural_mkIndPredBRecOnMotive(v_v_1581_, v___x_1585_, v___x_1586_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_);
if (lean_obj_tag(v___x_1587_) == 0)
{
lean_object* v_a_1588_; size_t v___x_1589_; size_t v___x_1590_; lean_object* v___x_1591_; 
v_a_1588_ = lean_ctor_get(v___x_1587_, 0);
lean_inc(v_a_1588_);
lean_dec_ref_known(v___x_1587_, 1);
v___x_1589_ = ((size_t)1ULL);
v___x_1590_ = lean_usize_add(v_i_1571_, v___x_1589_);
v___x_1591_ = lean_array_uset(v_bs_x27_1583_, v_i_1571_, v_a_1588_);
v_i_1571_ = v___x_1590_;
v_bs_1572_ = v___x_1591_;
goto _start;
}
else
{
lean_object* v_a_1593_; lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1600_; 
lean_dec_ref(v_bs_x27_1583_);
v_a_1593_ = lean_ctor_get(v___x_1587_, 0);
v_isSharedCheck_1600_ = !lean_is_exclusive(v___x_1587_);
if (v_isSharedCheck_1600_ == 0)
{
v___x_1595_ = v___x_1587_;
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
else
{
lean_inc(v_a_1593_);
lean_dec(v___x_1587_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
lean_object* v___x_1598_; 
if (v_isShared_1596_ == 0)
{
v___x_1598_ = v___x_1595_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v_a_1593_);
v___x_1598_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
return v___x_1598_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__20___redArg___boxed(lean_object* v_a_1601_, lean_object* v_funTypes_1602_, lean_object* v_sz_1603_, lean_object* v_i_1604_, lean_object* v_bs_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_){
_start:
{
size_t v_sz_boxed_1611_; size_t v_i_boxed_1612_; lean_object* v_res_1613_; 
v_sz_boxed_1611_ = lean_unbox_usize(v_sz_1603_);
lean_dec(v_sz_1603_);
v_i_boxed_1612_ = lean_unbox_usize(v_i_1604_);
lean_dec(v_i_1604_);
v_res_1613_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__20___redArg(v_a_1601_, v_funTypes_1602_, v_sz_boxed_1611_, v_i_boxed_1612_, v_bs_1605_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_);
lean_dec(v___y_1609_);
lean_dec_ref(v___y_1608_);
lean_dec(v___y_1607_);
lean_dec_ref(v___y_1606_);
lean_dec_ref(v_funTypes_1602_);
lean_dec_ref(v_a_1601_);
return v_res_1613_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__3(lean_object* v_recArgInfos_1614_, lean_object* v_a_1615_, size_t v___x_1616_, lean_object* v___f_1617_, lean_object* v_funTypes_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_){
_start:
{
size_t v_sz_1624_; lean_object* v___x_1625_; 
v_sz_1624_ = lean_array_size(v_recArgInfos_1614_);
v___x_1625_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__20___redArg(v_a_1615_, v_funTypes_1618_, v_sz_1624_, v___x_1616_, v_recArgInfos_1614_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_);
if (lean_obj_tag(v___x_1625_) == 0)
{
lean_object* v_a_1626_; lean_object* v___x_1627_; 
v_a_1626_ = lean_ctor_get(v___x_1625_, 0);
lean_inc(v_a_1626_);
lean_dec_ref_known(v___x_1625_, 1);
lean_inc(v___y_1622_);
lean_inc_ref(v___y_1621_);
lean_inc(v___y_1620_);
lean_inc_ref(v___y_1619_);
v___x_1627_ = lean_apply_7(v___f_1617_, v_funTypes_1618_, v_a_1626_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_, lean_box(0));
return v___x_1627_;
}
else
{
lean_object* v_a_1628_; lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1635_; 
lean_dec_ref(v_funTypes_1618_);
lean_dec_ref(v___f_1617_);
v_a_1628_ = lean_ctor_get(v___x_1625_, 0);
v_isSharedCheck_1635_ = !lean_is_exclusive(v___x_1625_);
if (v_isSharedCheck_1635_ == 0)
{
v___x_1630_ = v___x_1625_;
v_isShared_1631_ = v_isSharedCheck_1635_;
goto v_resetjp_1629_;
}
else
{
lean_inc(v_a_1628_);
lean_dec(v___x_1625_);
v___x_1630_ = lean_box(0);
v_isShared_1631_ = v_isSharedCheck_1635_;
goto v_resetjp_1629_;
}
v_resetjp_1629_:
{
lean_object* v___x_1633_; 
if (v_isShared_1631_ == 0)
{
v___x_1633_ = v___x_1630_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v_a_1628_);
v___x_1633_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
return v___x_1633_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__3___boxed(lean_object* v_recArgInfos_1636_, lean_object* v_a_1637_, lean_object* v___x_1638_, lean_object* v___f_1639_, lean_object* v_funTypes_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_){
_start:
{
size_t v___x_28223__boxed_1646_; lean_object* v_res_1647_; 
v___x_28223__boxed_1646_ = lean_unbox_usize(v___x_1638_);
lean_dec(v___x_1638_);
v_res_1647_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__3(v_recArgInfos_1636_, v_a_1637_, v___x_28223__boxed_1646_, v___f_1639_, v_funTypes_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_);
lean_dec(v___y_1644_);
lean_dec_ref(v___y_1643_);
lean_dec(v___y_1642_);
lean_dec_ref(v___y_1641_);
lean_dec_ref(v_a_1637_);
return v_res_1647_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg(lean_object* v_msg_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_){
_start:
{
lean_object* v_ref_1654_; lean_object* v___x_1655_; lean_object* v_a_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1664_; 
v_ref_1654_ = lean_ctor_get(v___y_1651_, 2);
v___x_1655_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11_spec__21(v_msg_1648_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_);
v_a_1656_ = lean_ctor_get(v___x_1655_, 0);
v_isSharedCheck_1664_ = !lean_is_exclusive(v___x_1655_);
if (v_isSharedCheck_1664_ == 0)
{
v___x_1658_ = v___x_1655_;
v_isShared_1659_ = v_isSharedCheck_1664_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_a_1656_);
lean_dec(v___x_1655_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1664_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
lean_object* v___x_1660_; lean_object* v___x_1662_; 
lean_inc(v_ref_1654_);
v___x_1660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1660_, 0, v_ref_1654_);
lean_ctor_set(v___x_1660_, 1, v_a_1656_);
if (v_isShared_1659_ == 0)
{
lean_ctor_set_tag(v___x_1658_, 1);
lean_ctor_set(v___x_1658_, 0, v___x_1660_);
v___x_1662_ = v___x_1658_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v___x_1660_);
v___x_1662_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
return v___x_1662_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg___boxed(lean_object* v_msg_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_){
_start:
{
lean_object* v_res_1671_; 
v_res_1671_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg(v_msg_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_);
lean_dec(v___y_1669_);
lean_dec_ref(v___y_1668_);
lean_dec(v___y_1667_);
lean_dec_ref(v___y_1666_);
return v_res_1671_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1673_; lean_object* v___x_1674_; 
v___x_1673_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__0));
v___x_1674_ = l_Lean_stringToMessageData(v___x_1673_);
return v___x_1674_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__3(void){
_start:
{
lean_object* v___x_1676_; lean_object* v___x_1677_; 
v___x_1676_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__2));
v___x_1677_ = l_Lean_stringToMessageData(v___x_1676_);
return v___x_1677_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4(lean_object* v_constName_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_){
_start:
{
lean_object* v___x_1684_; lean_object* v_env_1685_; lean_object* v___x_1686_; 
v___x_1684_ = lean_st_ref_get(v___y_1682_);
v_env_1685_ = lean_ctor_get(v___x_1684_, 0);
lean_inc_ref(v_env_1685_);
lean_dec(v___x_1684_);
lean_inc(v_constName_1678_);
v___x_1686_ = l_Lean_isInductiveCore_x3f(v_env_1685_, v_constName_1678_);
if (lean_obj_tag(v___x_1686_) == 0)
{
lean_object* v___x_1687_; uint8_t v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; 
v___x_1687_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__1, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__1);
v___x_1688_ = 0;
v___x_1689_ = l_Lean_MessageData_ofConstName(v_constName_1678_, v___x_1688_);
v___x_1690_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1690_, 0, v___x_1687_);
lean_ctor_set(v___x_1690_, 1, v___x_1689_);
v___x_1691_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__3, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__3_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__3);
v___x_1692_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1692_, 0, v___x_1690_);
lean_ctor_set(v___x_1692_, 1, v___x_1691_);
v___x_1693_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg(v___x_1692_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_);
return v___x_1693_;
}
else
{
lean_object* v_val_1694_; lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1701_; 
lean_dec(v_constName_1678_);
v_val_1694_ = lean_ctor_get(v___x_1686_, 0);
v_isSharedCheck_1701_ = !lean_is_exclusive(v___x_1686_);
if (v_isSharedCheck_1701_ == 0)
{
v___x_1696_ = v___x_1686_;
v_isShared_1697_ = v_isSharedCheck_1701_;
goto v_resetjp_1695_;
}
else
{
lean_inc(v_val_1694_);
lean_dec(v___x_1686_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1701_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
lean_object* v___x_1699_; 
if (v_isShared_1697_ == 0)
{
lean_ctor_set_tag(v___x_1696_, 0);
v___x_1699_ = v___x_1696_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v_val_1694_);
v___x_1699_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
return v___x_1699_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___boxed(lean_object* v_constName_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_){
_start:
{
lean_object* v_res_1708_; 
v_res_1708_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4(v_constName_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_);
lean_dec(v___y_1706_);
lean_dec_ref(v___y_1705_);
lean_dec(v___y_1704_);
lean_dec_ref(v___y_1703_);
return v_res_1708_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___redArg(lean_object* v_fixedParamPerms_1709_, lean_object* v_xs_1710_, size_t v_sz_1711_, size_t v_i_1712_, lean_object* v_bs_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_){
_start:
{
uint8_t v___x_1719_; 
v___x_1719_ = lean_usize_dec_lt(v_i_1712_, v_sz_1711_);
if (v___x_1719_ == 0)
{
lean_object* v___x_1720_; 
lean_dec_ref(v_xs_1710_);
v___x_1720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1720_, 0, v_bs_1713_);
return v___x_1720_;
}
else
{
lean_object* v_v_1721_; lean_object* v_perms_1722_; lean_object* v_type_1723_; lean_object* v___x_1724_; lean_object* v_bs_x27_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; 
v_v_1721_ = lean_array_uget_borrowed(v_bs_1713_, v_i_1712_);
v_perms_1722_ = lean_ctor_get(v_fixedParamPerms_1709_, 1);
v_type_1723_ = lean_ctor_get(v_v_1721_, 6);
lean_inc_ref(v_type_1723_);
v___x_1724_ = lean_unsigned_to_nat(0u);
v_bs_x27_1725_ = lean_array_uset(v_bs_1713_, v_i_1712_, v___x_1724_);
v___x_1726_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0);
v___x_1727_ = lean_usize_to_nat(v_i_1712_);
v___x_1728_ = lean_array_get_borrowed(v___x_1726_, v_perms_1722_, v___x_1727_);
lean_dec(v___x_1727_);
lean_inc_ref(v_xs_1710_);
lean_inc(v___x_1728_);
v___x_1729_ = l_Lean_Elab_FixedParamPerm_instantiateForall(v___x_1728_, v_type_1723_, v_xs_1710_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_);
if (lean_obj_tag(v___x_1729_) == 0)
{
lean_object* v_a_1730_; size_t v___x_1731_; size_t v___x_1732_; lean_object* v___x_1733_; 
v_a_1730_ = lean_ctor_get(v___x_1729_, 0);
lean_inc(v_a_1730_);
lean_dec_ref_known(v___x_1729_, 1);
v___x_1731_ = ((size_t)1ULL);
v___x_1732_ = lean_usize_add(v_i_1712_, v___x_1731_);
v___x_1733_ = lean_array_uset(v_bs_x27_1725_, v_i_1712_, v_a_1730_);
v_i_1712_ = v___x_1732_;
v_bs_1713_ = v___x_1733_;
goto _start;
}
else
{
lean_object* v_a_1735_; lean_object* v___x_1737_; uint8_t v_isShared_1738_; uint8_t v_isSharedCheck_1742_; 
lean_dec_ref(v_bs_x27_1725_);
lean_dec_ref(v_xs_1710_);
v_a_1735_ = lean_ctor_get(v___x_1729_, 0);
v_isSharedCheck_1742_ = !lean_is_exclusive(v___x_1729_);
if (v_isSharedCheck_1742_ == 0)
{
v___x_1737_ = v___x_1729_;
v_isShared_1738_ = v_isSharedCheck_1742_;
goto v_resetjp_1736_;
}
else
{
lean_inc(v_a_1735_);
lean_dec(v___x_1729_);
v___x_1737_ = lean_box(0);
v_isShared_1738_ = v_isSharedCheck_1742_;
goto v_resetjp_1736_;
}
v_resetjp_1736_:
{
lean_object* v___x_1740_; 
if (v_isShared_1738_ == 0)
{
v___x_1740_ = v___x_1737_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1741_; 
v_reuseFailAlloc_1741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1741_, 0, v_a_1735_);
v___x_1740_ = v_reuseFailAlloc_1741_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
return v___x_1740_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___redArg___boxed(lean_object* v_fixedParamPerms_1743_, lean_object* v_xs_1744_, lean_object* v_sz_1745_, lean_object* v_i_1746_, lean_object* v_bs_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_){
_start:
{
size_t v_sz_boxed_1753_; size_t v_i_boxed_1754_; lean_object* v_res_1755_; 
v_sz_boxed_1753_ = lean_unbox_usize(v_sz_1745_);
lean_dec(v_sz_1745_);
v_i_boxed_1754_ = lean_unbox_usize(v_i_1746_);
lean_dec(v_i_1746_);
v_res_1755_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___redArg(v_fixedParamPerms_1743_, v_xs_1744_, v_sz_boxed_1753_, v_i_boxed_1754_, v_bs_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_);
lean_dec(v___y_1751_);
lean_dec_ref(v___y_1750_);
lean_dec(v___y_1749_);
lean_dec_ref(v___y_1748_);
lean_dec_ref(v_fixedParamPerms_1743_);
return v_res_1755_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___redArg(lean_object* v_fixedParamPerms_1756_, lean_object* v_xs_1757_, size_t v_sz_1758_, size_t v_i_1759_, lean_object* v_bs_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_){
_start:
{
uint8_t v___x_1766_; 
v___x_1766_ = lean_usize_dec_lt(v_i_1759_, v_sz_1758_);
if (v___x_1766_ == 0)
{
lean_object* v___x_1767_; 
lean_dec_ref(v_xs_1757_);
v___x_1767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1767_, 0, v_bs_1760_);
return v___x_1767_;
}
else
{
lean_object* v_v_1768_; lean_object* v_perms_1769_; lean_object* v_value_1770_; lean_object* v___x_1771_; lean_object* v_bs_x27_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; 
v_v_1768_ = lean_array_uget_borrowed(v_bs_1760_, v_i_1759_);
v_perms_1769_ = lean_ctor_get(v_fixedParamPerms_1756_, 1);
v_value_1770_ = lean_ctor_get(v_v_1768_, 7);
lean_inc_ref(v_value_1770_);
v___x_1771_ = lean_unsigned_to_nat(0u);
v_bs_x27_1772_ = lean_array_uset(v_bs_1760_, v_i_1759_, v___x_1771_);
v___x_1773_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0);
v___x_1774_ = lean_usize_to_nat(v_i_1759_);
v___x_1775_ = lean_array_get_borrowed(v___x_1773_, v_perms_1769_, v___x_1774_);
lean_dec(v___x_1774_);
lean_inc_ref(v_xs_1757_);
lean_inc(v___x_1775_);
v___x_1776_ = l_Lean_Elab_FixedParamPerm_instantiateLambda(v___x_1775_, v_value_1770_, v_xs_1757_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_);
if (lean_obj_tag(v___x_1776_) == 0)
{
lean_object* v_a_1777_; size_t v___x_1778_; size_t v___x_1779_; lean_object* v___x_1780_; 
v_a_1777_ = lean_ctor_get(v___x_1776_, 0);
lean_inc(v_a_1777_);
lean_dec_ref_known(v___x_1776_, 1);
v___x_1778_ = ((size_t)1ULL);
v___x_1779_ = lean_usize_add(v_i_1759_, v___x_1778_);
v___x_1780_ = lean_array_uset(v_bs_x27_1772_, v_i_1759_, v_a_1777_);
v_i_1759_ = v___x_1779_;
v_bs_1760_ = v___x_1780_;
goto _start;
}
else
{
lean_object* v_a_1782_; lean_object* v___x_1784_; uint8_t v_isShared_1785_; uint8_t v_isSharedCheck_1789_; 
lean_dec_ref(v_bs_x27_1772_);
lean_dec_ref(v_xs_1757_);
v_a_1782_ = lean_ctor_get(v___x_1776_, 0);
v_isSharedCheck_1789_ = !lean_is_exclusive(v___x_1776_);
if (v_isSharedCheck_1789_ == 0)
{
v___x_1784_ = v___x_1776_;
v_isShared_1785_ = v_isSharedCheck_1789_;
goto v_resetjp_1783_;
}
else
{
lean_inc(v_a_1782_);
lean_dec(v___x_1776_);
v___x_1784_ = lean_box(0);
v_isShared_1785_ = v_isSharedCheck_1789_;
goto v_resetjp_1783_;
}
v_resetjp_1783_:
{
lean_object* v___x_1787_; 
if (v_isShared_1785_ == 0)
{
v___x_1787_ = v___x_1784_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v_a_1782_);
v___x_1787_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
return v___x_1787_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___redArg___boxed(lean_object* v_fixedParamPerms_1790_, lean_object* v_xs_1791_, lean_object* v_sz_1792_, lean_object* v_i_1793_, lean_object* v_bs_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_){
_start:
{
size_t v_sz_boxed_1800_; size_t v_i_boxed_1801_; lean_object* v_res_1802_; 
v_sz_boxed_1800_ = lean_unbox_usize(v_sz_1792_);
lean_dec(v_sz_1792_);
v_i_boxed_1801_ = lean_unbox_usize(v_i_1793_);
lean_dec(v_i_1793_);
v_res_1802_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___redArg(v_fixedParamPerms_1790_, v_xs_1791_, v_sz_boxed_1800_, v_i_boxed_1801_, v_bs_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_);
lean_dec(v___y_1798_);
lean_dec_ref(v___y_1797_);
lean_dec(v___y_1796_);
lean_dec_ref(v___y_1795_);
lean_dec_ref(v_fixedParamPerms_1790_);
return v_res_1802_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__0(lean_object* v_a_1803_, lean_object* v_a_1804_){
_start:
{
if (lean_obj_tag(v_a_1803_) == 0)
{
lean_object* v___x_1805_; 
v___x_1805_ = l_List_reverse___redArg(v_a_1804_);
return v___x_1805_;
}
else
{
lean_object* v_head_1806_; lean_object* v_tail_1807_; lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1818_; 
v_head_1806_ = lean_ctor_get(v_a_1803_, 0);
v_tail_1807_ = lean_ctor_get(v_a_1803_, 1);
v_isSharedCheck_1818_ = !lean_is_exclusive(v_a_1803_);
if (v_isSharedCheck_1818_ == 0)
{
v___x_1809_ = v_a_1803_;
v_isShared_1810_ = v_isSharedCheck_1818_;
goto v_resetjp_1808_;
}
else
{
lean_inc(v_tail_1807_);
lean_inc(v_head_1806_);
lean_dec(v_a_1803_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1818_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1815_; 
v___x_1811_ = l_Nat_reprFast(v_head_1806_);
v___x_1812_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1812_, 0, v___x_1811_);
v___x_1813_ = l_Lean_MessageData_ofFormat(v___x_1812_);
if (v_isShared_1810_ == 0)
{
lean_ctor_set(v___x_1809_, 1, v_a_1804_);
lean_ctor_set(v___x_1809_, 0, v___x_1813_);
v___x_1815_ = v___x_1809_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v___x_1813_);
lean_ctor_set(v_reuseFailAlloc_1817_, 1, v_a_1804_);
v___x_1815_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1814_;
}
v_reusejp_1814_:
{
v_a_1803_ = v_tail_1807_;
v_a_1804_ = v___x_1815_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__22(lean_object* v_a_1819_, lean_object* v_a_1820_){
_start:
{
if (lean_obj_tag(v_a_1819_) == 0)
{
lean_object* v___x_1821_; 
v___x_1821_ = l_List_reverse___redArg(v_a_1820_);
return v___x_1821_;
}
else
{
lean_object* v_head_1822_; lean_object* v_tail_1823_; lean_object* v___x_1825_; uint8_t v_isShared_1826_; uint8_t v_isSharedCheck_1835_; 
v_head_1822_ = lean_ctor_get(v_a_1819_, 0);
v_tail_1823_ = lean_ctor_get(v_a_1819_, 1);
v_isSharedCheck_1835_ = !lean_is_exclusive(v_a_1819_);
if (v_isSharedCheck_1835_ == 0)
{
v___x_1825_ = v_a_1819_;
v_isShared_1826_ = v_isSharedCheck_1835_;
goto v_resetjp_1824_;
}
else
{
lean_inc(v_tail_1823_);
lean_inc(v_head_1822_);
lean_dec(v_a_1819_);
v___x_1825_ = lean_box(0);
v_isShared_1826_ = v_isSharedCheck_1835_;
goto v_resetjp_1824_;
}
v_resetjp_1824_:
{
lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1832_; 
v___x_1827_ = lean_array_to_list(v_head_1822_);
v___x_1828_ = lean_box(0);
v___x_1829_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__0(v___x_1827_, v___x_1828_);
v___x_1830_ = l_Lean_MessageData_ofList(v___x_1829_);
if (v_isShared_1826_ == 0)
{
lean_ctor_set(v___x_1825_, 1, v_a_1820_);
lean_ctor_set(v___x_1825_, 0, v___x_1830_);
v___x_1832_ = v___x_1825_;
goto v_reusejp_1831_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v___x_1830_);
lean_ctor_set(v_reuseFailAlloc_1834_, 1, v_a_1820_);
v___x_1832_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1831_;
}
v_reusejp_1831_:
{
v_a_1819_ = v_tail_1823_;
v_a_1820_ = v___x_1832_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__21___redArg(lean_object* v_a_1836_, lean_object* v_a_1837_, size_t v_sz_1838_, size_t v_i_1839_, lean_object* v_bs_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_){
_start:
{
uint8_t v___x_1846_; 
v___x_1846_ = lean_usize_dec_lt(v_i_1839_, v_sz_1838_);
if (v___x_1846_ == 0)
{
lean_object* v___x_1847_; 
v___x_1847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1847_, 0, v_bs_1840_);
return v___x_1847_;
}
else
{
lean_object* v___x_1848_; lean_object* v_v_1849_; lean_object* v___x_1850_; lean_object* v_bs_x27_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; 
v___x_1848_ = l_Lean_instInhabitedExpr;
v_v_1849_ = lean_array_uget(v_bs_1840_, v_i_1839_);
v___x_1850_ = lean_unsigned_to_nat(0u);
v_bs_x27_1851_ = lean_array_uset(v_bs_1840_, v_i_1839_, v___x_1850_);
v___x_1852_ = lean_usize_to_nat(v_i_1839_);
v___x_1853_ = lean_array_get_borrowed(v___x_1848_, v_a_1836_, v___x_1852_);
v___x_1854_ = lean_array_get_borrowed(v___x_1848_, v_a_1837_, v___x_1852_);
lean_dec(v___x_1852_);
lean_inc(v___x_1854_);
lean_inc(v___x_1853_);
v___x_1855_ = l_Lean_Elab_Structural_mkBRecOnMotive(v_v_1849_, v___x_1853_, v___x_1854_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_);
if (lean_obj_tag(v___x_1855_) == 0)
{
lean_object* v_a_1856_; size_t v___x_1857_; size_t v___x_1858_; lean_object* v___x_1859_; 
v_a_1856_ = lean_ctor_get(v___x_1855_, 0);
lean_inc(v_a_1856_);
lean_dec_ref_known(v___x_1855_, 1);
v___x_1857_ = ((size_t)1ULL);
v___x_1858_ = lean_usize_add(v_i_1839_, v___x_1857_);
v___x_1859_ = lean_array_uset(v_bs_x27_1851_, v_i_1839_, v_a_1856_);
v_i_1839_ = v___x_1858_;
v_bs_1840_ = v___x_1859_;
goto _start;
}
else
{
lean_object* v_a_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1868_; 
lean_dec_ref(v_bs_x27_1851_);
v_a_1861_ = lean_ctor_get(v___x_1855_, 0);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1855_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1863_ = v___x_1855_;
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_a_1861_);
lean_dec(v___x_1855_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v___x_1866_; 
if (v_isShared_1864_ == 0)
{
v___x_1866_ = v___x_1863_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v_a_1861_);
v___x_1866_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
return v___x_1866_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__21___redArg___boxed(lean_object* v_a_1869_, lean_object* v_a_1870_, lean_object* v_sz_1871_, lean_object* v_i_1872_, lean_object* v_bs_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_){
_start:
{
size_t v_sz_boxed_1879_; size_t v_i_boxed_1880_; lean_object* v_res_1881_; 
v_sz_boxed_1879_ = lean_unbox_usize(v_sz_1871_);
lean_dec(v_sz_1871_);
v_i_boxed_1880_ = lean_unbox_usize(v_i_1872_);
lean_dec(v_i_1872_);
v_res_1881_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__21___redArg(v_a_1869_, v_a_1870_, v_sz_boxed_1879_, v_i_boxed_1880_, v_bs_1873_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_);
lean_dec(v___y_1877_);
lean_dec_ref(v___y_1876_);
lean_dec(v___y_1875_);
lean_dec_ref(v___y_1874_);
lean_dec_ref(v_a_1870_);
lean_dec_ref(v_a_1869_);
return v_res_1881_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11___redArg(lean_object* v_hi_1882_, lean_object* v_pivot_1883_, lean_object* v_as_1884_, lean_object* v_i_1885_, lean_object* v_k_1886_){
_start:
{
uint8_t v___x_1887_; 
v___x_1887_ = lean_nat_dec_lt(v_k_1886_, v_hi_1882_);
if (v___x_1887_ == 0)
{
lean_object* v___x_1888_; lean_object* v___x_1889_; 
lean_dec(v_k_1886_);
v___x_1888_ = lean_array_fswap(v_as_1884_, v_i_1885_, v_hi_1882_);
v___x_1889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1889_, 0, v_i_1885_);
lean_ctor_set(v___x_1889_, 1, v___x_1888_);
return v___x_1889_;
}
else
{
lean_object* v___x_1890_; uint8_t v___x_1891_; 
v___x_1890_ = lean_array_fget_borrowed(v_as_1884_, v_k_1886_);
v___x_1891_ = l_Nat_blt(v___x_1890_, v_pivot_1883_);
if (v___x_1891_ == 0)
{
lean_object* v___x_1892_; lean_object* v___x_1893_; 
v___x_1892_ = lean_unsigned_to_nat(1u);
v___x_1893_ = lean_nat_add(v_k_1886_, v___x_1892_);
lean_dec(v_k_1886_);
v_k_1886_ = v___x_1893_;
goto _start;
}
else
{
lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; 
v___x_1895_ = lean_array_fswap(v_as_1884_, v_i_1885_, v_k_1886_);
v___x_1896_ = lean_unsigned_to_nat(1u);
v___x_1897_ = lean_nat_add(v_i_1885_, v___x_1896_);
lean_dec(v_i_1885_);
v___x_1898_ = lean_nat_add(v_k_1886_, v___x_1896_);
lean_dec(v_k_1886_);
v_as_1884_ = v___x_1895_;
v_i_1885_ = v___x_1897_;
v_k_1886_ = v___x_1898_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11___redArg___boxed(lean_object* v_hi_1900_, lean_object* v_pivot_1901_, lean_object* v_as_1902_, lean_object* v_i_1903_, lean_object* v_k_1904_){
_start:
{
lean_object* v_res_1905_; 
v_res_1905_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11___redArg(v_hi_1900_, v_pivot_1901_, v_as_1902_, v_i_1903_, v_k_1904_);
lean_dec(v_pivot_1901_);
lean_dec(v_hi_1900_);
return v_res_1905_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg(lean_object* v_n_1906_, lean_object* v_as_1907_, lean_object* v_lo_1908_, lean_object* v_hi_1909_){
_start:
{
lean_object* v___y_1911_; uint8_t v___x_1921_; 
v___x_1921_ = lean_nat_dec_lt(v_lo_1908_, v_hi_1909_);
if (v___x_1921_ == 0)
{
lean_dec(v_lo_1908_);
return v_as_1907_;
}
else
{
lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v_mid_1924_; lean_object* v___y_1926_; lean_object* v___y_1932_; lean_object* v___x_1937_; lean_object* v___x_1938_; uint8_t v___x_1939_; 
v___x_1922_ = lean_nat_add(v_lo_1908_, v_hi_1909_);
v___x_1923_ = lean_unsigned_to_nat(1u);
v_mid_1924_ = lean_nat_shiftr(v___x_1922_, v___x_1923_);
lean_dec(v___x_1922_);
v___x_1937_ = lean_array_fget_borrowed(v_as_1907_, v_mid_1924_);
v___x_1938_ = lean_array_fget_borrowed(v_as_1907_, v_lo_1908_);
v___x_1939_ = l_Nat_blt(v___x_1937_, v___x_1938_);
if (v___x_1939_ == 0)
{
v___y_1932_ = v_as_1907_;
goto v___jp_1931_;
}
else
{
lean_object* v___x_1940_; 
v___x_1940_ = lean_array_fswap(v_as_1907_, v_lo_1908_, v_mid_1924_);
v___y_1932_ = v___x_1940_;
goto v___jp_1931_;
}
v___jp_1925_:
{
lean_object* v___x_1927_; lean_object* v___x_1928_; uint8_t v___x_1929_; 
v___x_1927_ = lean_array_fget_borrowed(v___y_1926_, v_mid_1924_);
v___x_1928_ = lean_array_fget_borrowed(v___y_1926_, v_hi_1909_);
v___x_1929_ = l_Nat_blt(v___x_1927_, v___x_1928_);
if (v___x_1929_ == 0)
{
lean_dec(v_mid_1924_);
v___y_1911_ = v___y_1926_;
goto v___jp_1910_;
}
else
{
lean_object* v___x_1930_; 
v___x_1930_ = lean_array_fswap(v___y_1926_, v_mid_1924_, v_hi_1909_);
lean_dec(v_mid_1924_);
v___y_1911_ = v___x_1930_;
goto v___jp_1910_;
}
}
v___jp_1931_:
{
lean_object* v___x_1933_; lean_object* v___x_1934_; uint8_t v___x_1935_; 
v___x_1933_ = lean_array_fget_borrowed(v___y_1932_, v_hi_1909_);
v___x_1934_ = lean_array_fget_borrowed(v___y_1932_, v_lo_1908_);
v___x_1935_ = l_Nat_blt(v___x_1933_, v___x_1934_);
if (v___x_1935_ == 0)
{
v___y_1926_ = v___y_1932_;
goto v___jp_1925_;
}
else
{
lean_object* v___x_1936_; 
v___x_1936_ = lean_array_fswap(v___y_1932_, v_lo_1908_, v_hi_1909_);
v___y_1926_ = v___x_1936_;
goto v___jp_1925_;
}
}
}
v___jp_1910_:
{
lean_object* v_pivot_1912_; lean_object* v___x_1913_; lean_object* v_fst_1914_; lean_object* v_snd_1915_; uint8_t v___x_1916_; 
v_pivot_1912_ = lean_array_fget(v___y_1911_, v_hi_1909_);
lean_inc_n(v_lo_1908_, 2);
v___x_1913_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11___redArg(v_hi_1909_, v_pivot_1912_, v___y_1911_, v_lo_1908_, v_lo_1908_);
lean_dec(v_pivot_1912_);
v_fst_1914_ = lean_ctor_get(v___x_1913_, 0);
lean_inc(v_fst_1914_);
v_snd_1915_ = lean_ctor_get(v___x_1913_, 1);
lean_inc(v_snd_1915_);
lean_dec_ref(v___x_1913_);
v___x_1916_ = lean_nat_dec_le(v_hi_1909_, v_fst_1914_);
if (v___x_1916_ == 0)
{
lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; 
v___x_1917_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg(v_n_1906_, v_snd_1915_, v_lo_1908_, v_fst_1914_);
v___x_1918_ = lean_unsigned_to_nat(1u);
v___x_1919_ = lean_nat_add(v_fst_1914_, v___x_1918_);
lean_dec(v_fst_1914_);
v_as_1907_ = v___x_1917_;
v_lo_1908_ = v___x_1919_;
goto _start;
}
else
{
lean_dec(v_fst_1914_);
lean_dec(v_lo_1908_);
return v_snd_1915_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg___boxed(lean_object* v_n_1941_, lean_object* v_as_1942_, lean_object* v_lo_1943_, lean_object* v_hi_1944_){
_start:
{
lean_object* v_res_1945_; 
v_res_1945_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg(v_n_1941_, v_as_1942_, v_lo_1943_, v_hi_1944_);
lean_dec(v_hi_1944_);
lean_dec(v_n_1941_);
return v_res_1945_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__6(lean_object* v_xs_1946_, lean_object* v_f_1947_, lean_object* v_x_1948_, lean_object* v_as_1949_, size_t v_i_1950_, size_t v_stop_1951_, lean_object* v_b_1952_){
_start:
{
lean_object* v___y_1954_; uint8_t v___x_1958_; 
v___x_1958_ = lean_usize_dec_eq(v_i_1950_, v_stop_1951_);
if (v___x_1958_ == 0)
{
lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; uint8_t v___x_1963_; 
v___x_1959_ = l_Lean_Elab_Structural_instInhabitedRecArgInfo_default;
v___x_1960_ = lean_array_uget_borrowed(v_as_1949_, v_i_1950_);
v___x_1961_ = lean_array_get_borrowed(v___x_1959_, v_xs_1946_, v___x_1960_);
lean_inc_ref(v_f_1947_);
lean_inc(v___x_1961_);
v___x_1962_ = lean_apply_1(v_f_1947_, v___x_1961_);
v___x_1963_ = lean_nat_dec_eq(v___x_1962_, v_x_1948_);
lean_dec(v___x_1962_);
if (v___x_1963_ == 0)
{
v___y_1954_ = v_b_1952_;
goto v___jp_1953_;
}
else
{
lean_object* v___x_1964_; 
lean_inc(v___x_1960_);
v___x_1964_ = lean_array_push(v_b_1952_, v___x_1960_);
v___y_1954_ = v___x_1964_;
goto v___jp_1953_;
}
}
else
{
lean_dec_ref(v_f_1947_);
return v_b_1952_;
}
v___jp_1953_:
{
size_t v___x_1955_; size_t v___x_1956_; 
v___x_1955_ = ((size_t)1ULL);
v___x_1956_ = lean_usize_add(v_i_1950_, v___x_1955_);
v_i_1950_ = v___x_1956_;
v_b_1952_ = v___y_1954_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__6___boxed(lean_object* v_xs_1965_, lean_object* v_f_1966_, lean_object* v_x_1967_, lean_object* v_as_1968_, lean_object* v_i_1969_, lean_object* v_stop_1970_, lean_object* v_b_1971_){
_start:
{
size_t v_i_boxed_1972_; size_t v_stop_boxed_1973_; lean_object* v_res_1974_; 
v_i_boxed_1972_ = lean_unbox_usize(v_i_1969_);
lean_dec(v_i_1969_);
v_stop_boxed_1973_ = lean_unbox_usize(v_stop_1970_);
lean_dec(v_stop_1970_);
v_res_1974_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__6(v_xs_1965_, v_f_1966_, v_x_1967_, v_as_1968_, v_i_boxed_1972_, v_stop_boxed_1973_, v_b_1971_);
lean_dec_ref(v_as_1968_);
lean_dec(v_x_1967_);
lean_dec_ref(v_xs_1965_);
return v_res_1974_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8(lean_object* v_xs_1977_, lean_object* v_f_1978_, size_t v_sz_1979_, size_t v_i_1980_, lean_object* v_bs_1981_){
_start:
{
uint8_t v___x_1982_; 
v___x_1982_ = lean_usize_dec_lt(v_i_1980_, v_sz_1979_);
if (v___x_1982_ == 0)
{
lean_dec_ref(v_f_1978_);
return v_bs_1981_;
}
else
{
lean_object* v_v_1983_; lean_object* v___x_1984_; lean_object* v_bs_x27_1985_; lean_object* v___y_1987_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; uint8_t v___x_1996_; 
v_v_1983_ = lean_array_uget(v_bs_1981_, v_i_1980_);
v___x_1984_ = lean_unsigned_to_nat(0u);
v_bs_x27_1985_ = lean_array_uset(v_bs_1981_, v_i_1980_, v___x_1984_);
v___x_1992_ = lean_array_get_size(v_xs_1977_);
v___x_1993_ = l_Array_range(v___x_1992_);
v___x_1994_ = lean_array_get_size(v___x_1993_);
v___x_1995_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8___closed__0));
v___x_1996_ = lean_nat_dec_lt(v___x_1984_, v___x_1994_);
if (v___x_1996_ == 0)
{
lean_dec_ref(v___x_1993_);
lean_dec(v_v_1983_);
v___y_1987_ = v___x_1995_;
goto v___jp_1986_;
}
else
{
size_t v___x_1997_; size_t v___x_1998_; lean_object* v___x_1999_; 
v___x_1997_ = ((size_t)0ULL);
v___x_1998_ = lean_usize_of_nat(v___x_1994_);
lean_inc_ref(v_f_1978_);
v___x_1999_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__6(v_xs_1977_, v_f_1978_, v_v_1983_, v___x_1993_, v___x_1997_, v___x_1998_, v___x_1995_);
lean_dec_ref(v___x_1993_);
lean_dec(v_v_1983_);
v___y_1987_ = v___x_1999_;
goto v___jp_1986_;
}
v___jp_1986_:
{
size_t v___x_1988_; size_t v___x_1989_; lean_object* v___x_1990_; 
v___x_1988_ = ((size_t)1ULL);
v___x_1989_ = lean_usize_add(v_i_1980_, v___x_1988_);
v___x_1990_ = lean_array_uset(v_bs_x27_1985_, v_i_1980_, v___y_1987_);
v_i_1980_ = v___x_1989_;
v_bs_1981_ = v___x_1990_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8___boxed(lean_object* v_xs_2000_, lean_object* v_f_2001_, lean_object* v_sz_2002_, lean_object* v_i_2003_, lean_object* v_bs_2004_){
_start:
{
size_t v_sz_boxed_2005_; size_t v_i_boxed_2006_; lean_object* v_res_2007_; 
v_sz_boxed_2005_ = lean_unbox_usize(v_sz_2002_);
lean_dec(v_sz_2002_);
v_i_boxed_2006_ = lean_unbox_usize(v_i_2003_);
lean_dec(v_i_2003_);
v_res_2007_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8(v_xs_2000_, v_f_2001_, v_sz_boxed_2005_, v_i_boxed_2006_, v_bs_2004_);
lean_dec_ref(v_xs_2000_);
return v_res_2007_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__11(lean_object* v_as_2008_, size_t v_i_2009_, size_t v_stop_2010_, lean_object* v_b_2011_){
_start:
{
uint8_t v___x_2012_; 
v___x_2012_ = lean_usize_dec_eq(v_i_2009_, v_stop_2010_);
if (v___x_2012_ == 0)
{
lean_object* v___x_2013_; lean_object* v___x_2014_; size_t v___x_2015_; size_t v___x_2016_; 
v___x_2013_ = lean_array_uget_borrowed(v_as_2008_, v_i_2009_);
v___x_2014_ = l_Array_append___redArg(v_b_2011_, v___x_2013_);
v___x_2015_ = ((size_t)1ULL);
v___x_2016_ = lean_usize_add(v_i_2009_, v___x_2015_);
v_i_2009_ = v___x_2016_;
v_b_2011_ = v___x_2014_;
goto _start;
}
else
{
return v_b_2011_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__11___boxed(lean_object* v_as_2018_, lean_object* v_i_2019_, lean_object* v_stop_2020_, lean_object* v_b_2021_){
_start:
{
size_t v_i_boxed_2022_; size_t v_stop_boxed_2023_; lean_object* v_res_2024_; 
v_i_boxed_2022_ = lean_unbox_usize(v_i_2019_);
lean_dec(v_i_2019_);
v_stop_boxed_2023_ = lean_unbox_usize(v_stop_2020_);
lean_dec(v_stop_2020_);
v_res_2024_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__11(v_as_2018_, v_i_boxed_2022_, v_stop_boxed_2023_, v_b_2021_);
lean_dec_ref(v_as_2018_);
return v_res_2024_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__7(lean_object* v_msg_2025_){
_start:
{
lean_object* v___x_2026_; lean_object* v___x_2027_; 
v___x_2026_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0);
v___x_2027_ = lean_panic_fn_borrowed(v___x_2026_, v_msg_2025_);
return v___x_2027_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9___redArg(lean_object* v_xs_2028_, lean_object* v_ys_2029_, lean_object* v_x_2030_){
_start:
{
lean_object* v_zero_2031_; uint8_t v_isZero_2032_; 
v_zero_2031_ = lean_unsigned_to_nat(0u);
v_isZero_2032_ = lean_nat_dec_eq(v_x_2030_, v_zero_2031_);
if (v_isZero_2032_ == 1)
{
lean_dec(v_x_2030_);
return v_isZero_2032_;
}
else
{
lean_object* v_one_2033_; lean_object* v_n_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; uint8_t v___x_2037_; 
v_one_2033_ = lean_unsigned_to_nat(1u);
v_n_2034_ = lean_nat_sub(v_x_2030_, v_one_2033_);
lean_dec(v_x_2030_);
v___x_2035_ = lean_array_fget_borrowed(v_xs_2028_, v_n_2034_);
v___x_2036_ = lean_array_fget_borrowed(v_ys_2029_, v_n_2034_);
v___x_2037_ = lean_nat_dec_eq(v___x_2035_, v___x_2036_);
if (v___x_2037_ == 0)
{
lean_dec(v_n_2034_);
return v___x_2037_;
}
else
{
v_x_2030_ = v_n_2034_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9___redArg___boxed(lean_object* v_xs_2039_, lean_object* v_ys_2040_, lean_object* v_x_2041_){
_start:
{
uint8_t v_res_2042_; lean_object* v_r_2043_; 
v_res_2042_ = l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9___redArg(v_xs_2039_, v_ys_2040_, v_x_2041_);
lean_dec_ref(v_ys_2040_);
lean_dec_ref(v_xs_2039_);
v_r_2043_ = lean_box(v_res_2042_);
return v_r_2043_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__2(void){
_start:
{
lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; 
v___x_2046_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__1));
v___x_2047_ = lean_unsigned_to_nat(2u);
v___x_2048_ = lean_unsigned_to_nat(63u);
v___x_2049_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__0));
v___x_2050_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__0));
v___x_2051_ = l_mkPanicMessageWithDecl(v___x_2050_, v___x_2049_, v___x_2048_, v___x_2047_, v___x_2046_);
return v___x_2051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5(lean_object* v_f_2054_, lean_object* v_xs_2055_, lean_object* v_ys_2056_){
_start:
{
size_t v_sz_2060_; size_t v___x_2061_; lean_object* v_positions_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___y_2066_; lean_object* v___y_2072_; lean_object* v___y_2073_; lean_object* v___y_2074_; lean_object* v___y_2075_; lean_object* v___y_2078_; lean_object* v___y_2079_; lean_object* v___y_2080_; lean_object* v___y_2081_; lean_object* v___y_2084_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; uint8_t v___x_2094_; 
v_sz_2060_ = lean_array_size(v_ys_2056_);
v___x_2061_ = ((size_t)0ULL);
v_positions_2062_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8(v_xs_2055_, v_f_2054_, v_sz_2060_, v___x_2061_, v_ys_2056_);
v___x_2063_ = lean_array_get_size(v_xs_2055_);
v___x_2064_ = l_Array_range(v___x_2063_);
v___x_2091_ = lean_unsigned_to_nat(0u);
v___x_2092_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__3));
v___x_2093_ = lean_array_get_size(v_positions_2062_);
v___x_2094_ = lean_nat_dec_lt(v___x_2091_, v___x_2093_);
if (v___x_2094_ == 0)
{
v___y_2084_ = v___x_2092_;
goto v___jp_2083_;
}
else
{
size_t v___x_2095_; lean_object* v___x_2096_; 
v___x_2095_ = lean_usize_of_nat(v___x_2093_);
v___x_2096_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__11(v_positions_2062_, v___x_2061_, v___x_2095_, v___x_2092_);
v___y_2084_ = v___x_2096_;
goto v___jp_2083_;
}
v___jp_2057_:
{
lean_object* v___x_2058_; lean_object* v___x_2059_; 
v___x_2058_ = lean_obj_once(&l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__2, &l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__2_once, _init_l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__2);
v___x_2059_ = l_panic___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__7(v___x_2058_);
return v___x_2059_;
}
v___jp_2065_:
{
lean_object* v___x_2067_; lean_object* v___x_2068_; uint8_t v___x_2069_; 
v___x_2067_ = lean_array_get_size(v___x_2064_);
v___x_2068_ = lean_array_get_size(v___y_2066_);
v___x_2069_ = lean_nat_dec_eq(v___x_2067_, v___x_2068_);
if (v___x_2069_ == 0)
{
lean_dec_ref(v___y_2066_);
lean_dec_ref(v___x_2064_);
lean_dec_ref(v_positions_2062_);
goto v___jp_2057_;
}
else
{
uint8_t v___x_2070_; 
v___x_2070_ = l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9___redArg(v___x_2064_, v___y_2066_, v___x_2067_);
lean_dec_ref(v___y_2066_);
lean_dec_ref(v___x_2064_);
if (v___x_2070_ == 0)
{
lean_dec_ref(v_positions_2062_);
goto v___jp_2057_;
}
else
{
return v_positions_2062_;
}
}
}
v___jp_2071_:
{
lean_object* v___x_2076_; 
v___x_2076_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg(v___y_2072_, v___y_2074_, v___y_2073_, v___y_2075_);
lean_dec(v___y_2075_);
lean_dec(v___y_2072_);
v___y_2066_ = v___x_2076_;
goto v___jp_2065_;
}
v___jp_2077_:
{
uint8_t v___x_2082_; 
v___x_2082_ = lean_nat_dec_le(v___y_2081_, v___y_2079_);
if (v___x_2082_ == 0)
{
lean_dec(v___y_2079_);
lean_inc(v___y_2081_);
v___y_2072_ = v___y_2078_;
v___y_2073_ = v___y_2081_;
v___y_2074_ = v___y_2080_;
v___y_2075_ = v___y_2081_;
goto v___jp_2071_;
}
else
{
v___y_2072_ = v___y_2078_;
v___y_2073_ = v___y_2081_;
v___y_2074_ = v___y_2080_;
v___y_2075_ = v___y_2079_;
goto v___jp_2071_;
}
}
v___jp_2083_:
{
lean_object* v___x_2085_; lean_object* v___x_2086_; uint8_t v___x_2087_; 
v___x_2085_ = lean_array_get_size(v___y_2084_);
v___x_2086_ = lean_unsigned_to_nat(0u);
v___x_2087_ = lean_nat_dec_eq(v___x_2085_, v___x_2086_);
if (v___x_2087_ == 0)
{
lean_object* v___x_2088_; lean_object* v___x_2089_; uint8_t v___x_2090_; 
v___x_2088_ = lean_unsigned_to_nat(1u);
v___x_2089_ = lean_nat_sub(v___x_2085_, v___x_2088_);
v___x_2090_ = lean_nat_dec_le(v___x_2086_, v___x_2089_);
if (v___x_2090_ == 0)
{
lean_inc(v___x_2089_);
v___y_2078_ = v___x_2085_;
v___y_2079_ = v___x_2089_;
v___y_2080_ = v___y_2084_;
v___y_2081_ = v___x_2089_;
goto v___jp_2077_;
}
else
{
v___y_2078_ = v___x_2085_;
v___y_2079_ = v___x_2089_;
v___y_2080_ = v___y_2084_;
v___y_2081_ = v___x_2086_;
goto v___jp_2077_;
}
}
else
{
v___y_2066_ = v___y_2084_;
goto v___jp_2065_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___boxed(lean_object* v_f_2097_, lean_object* v_xs_2098_, lean_object* v_ys_2099_){
_start:
{
lean_object* v_res_2100_; 
v_res_2100_ = l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5(v_f_2097_, v_xs_2098_, v_ys_2099_);
lean_dec_ref(v_xs_2098_);
return v_res_2100_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__9(void){
_start:
{
lean_object* v___x_2115_; lean_object* v___x_2116_; 
v___x_2115_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__8));
v___x_2116_ = l_Lean_stringToMessageData(v___x_2115_);
return v___x_2116_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__11(void){
_start:
{
lean_object* v___x_2118_; lean_object* v___x_2119_; 
v___x_2118_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__10));
v___x_2119_ = l_Lean_stringToMessageData(v___x_2118_);
return v___x_2119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion(lean_object* v_preDefs_2120_, lean_object* v_fixedParamPerms_2121_, lean_object* v_xs_2122_, lean_object* v_recArgInfos_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_){
_start:
{
lean_object* v___f_2129_; lean_object* v___f_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; size_t v_sz_2134_; size_t v___x_2135_; lean_object* v___x_2136_; 
v___f_2129_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__0));
v___f_2130_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__1));
v___x_2131_ = lean_box(0);
v___x_2132_ = l_Lean_Elab_Structural_instInhabitedRecArgInfo_default;
v___x_2133_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v_sz_2134_ = lean_array_size(v_preDefs_2120_);
v___x_2135_ = ((size_t)0ULL);
lean_inc_ref(v_preDefs_2120_);
lean_inc_ref(v_xs_2122_);
v___x_2136_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___redArg(v_fixedParamPerms_2121_, v_xs_2122_, v_sz_2134_, v___x_2135_, v_preDefs_2120_, v_a_2124_, v_a_2125_, v_a_2126_, v_a_2127_);
if (lean_obj_tag(v___x_2136_) == 0)
{
lean_object* v_a_2137_; lean_object* v___x_2138_; 
v_a_2137_ = lean_ctor_get(v___x_2136_, 0);
lean_inc(v_a_2137_);
lean_dec_ref_known(v___x_2136_, 1);
lean_inc_ref(v_preDefs_2120_);
lean_inc_ref(v_xs_2122_);
v___x_2138_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___redArg(v_fixedParamPerms_2121_, v_xs_2122_, v_sz_2134_, v___x_2135_, v_preDefs_2120_, v_a_2124_, v_a_2125_, v_a_2126_, v_a_2127_);
if (lean_obj_tag(v___x_2138_) == 0)
{
lean_object* v_a_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v_indGroupInst_2142_; lean_object* v_toIndGroupInfo_2143_; lean_object* v_all_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2228_; 
v_a_2139_ = lean_ctor_get(v___x_2138_, 0);
lean_inc(v_a_2139_);
lean_dec_ref_known(v___x_2138_, 1);
v___x_2140_ = lean_unsigned_to_nat(0u);
v___x_2141_ = lean_array_get_borrowed(v___x_2132_, v_recArgInfos_2123_, v___x_2140_);
v_indGroupInst_2142_ = lean_ctor_get(v___x_2141_, 4);
v_toIndGroupInfo_2143_ = lean_ctor_get(v_indGroupInst_2142_, 0);
lean_inc_ref(v_toIndGroupInfo_2143_);
v_all_2144_ = lean_ctor_get(v_toIndGroupInfo_2143_, 0);
v_isSharedCheck_2228_ = !lean_is_exclusive(v_toIndGroupInfo_2143_);
if (v_isSharedCheck_2228_ == 0)
{
lean_object* v_unused_2229_; 
v_unused_2229_ = lean_ctor_get(v_toIndGroupInfo_2143_, 1);
lean_dec(v_unused_2229_);
v___x_2146_ = v_toIndGroupInfo_2143_;
v_isShared_2147_ = v_isSharedCheck_2228_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_all_2144_);
lean_dec(v_toIndGroupInfo_2143_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2228_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
lean_object* v___x_2148_; lean_object* v___x_2149_; 
v___x_2148_ = lean_array_get(v___x_2131_, v_all_2144_, v___x_2140_);
lean_dec_ref(v_all_2144_);
v___x_2149_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4(v___x_2148_, v_a_2124_, v_a_2125_, v_a_2126_, v_a_2127_);
if (lean_obj_tag(v___x_2149_) == 0)
{
lean_object* v_a_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___f_2155_; lean_object* v___y_2157_; lean_object* v___y_2158_; lean_object* v___y_2159_; lean_object* v___y_2160_; lean_object* v___x_2194_; lean_object* v_a_2195_; uint8_t v___x_2196_; 
v_a_2150_ = lean_ctor_get(v___x_2149_, 0);
lean_inc(v_a_2150_);
lean_dec_ref_known(v___x_2149_, 1);
v___x_2151_ = l_Lean_InductiveVal_numTypeFormers(v_a_2150_);
v___x_2152_ = l_Array_range(v___x_2151_);
v___x_2153_ = l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5(v___f_2130_, v_recArgInfos_2123_, v___x_2152_);
v___x_2154_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__5));
v___f_2155_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__6));
v___x_2194_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1(v___x_2154_, v_a_2124_, v_a_2125_, v_a_2126_, v_a_2127_);
v_a_2195_ = lean_ctor_get(v___x_2194_, 0);
lean_inc(v_a_2195_);
lean_dec_ref(v___x_2194_);
v___x_2196_ = lean_unbox(v_a_2195_);
lean_dec(v_a_2195_);
if (v___x_2196_ == 0)
{
lean_del_object(v___x_2146_);
v___y_2157_ = v_a_2124_;
v___y_2158_ = v_a_2125_;
v___y_2159_ = v_a_2126_;
v___y_2160_ = v_a_2127_;
goto v___jp_2156_;
}
else
{
lean_object* v_toConstantVal_2197_; lean_object* v_name_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2202_; 
v_toConstantVal_2197_ = lean_ctor_get(v_a_2150_, 0);
v_name_2198_ = lean_ctor_get(v_toConstantVal_2197_, 0);
v___x_2199_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__9, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__9_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__9);
lean_inc(v_name_2198_);
v___x_2200_ = l_Lean_MessageData_ofName(v_name_2198_);
if (v_isShared_2147_ == 0)
{
lean_ctor_set_tag(v___x_2146_, 7);
lean_ctor_set(v___x_2146_, 1, v___x_2200_);
lean_ctor_set(v___x_2146_, 0, v___x_2199_);
v___x_2202_ = v___x_2146_;
goto v_reusejp_2201_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v___x_2199_);
lean_ctor_set(v_reuseFailAlloc_2219_, 1, v___x_2200_);
v___x_2202_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2201_;
}
v_reusejp_2201_:
{
lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; 
v___x_2203_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__11, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__11_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__11);
v___x_2204_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2204_, 0, v___x_2202_);
lean_ctor_set(v___x_2204_, 1, v___x_2203_);
lean_inc_ref(v___x_2153_);
v___x_2205_ = lean_array_to_list(v___x_2153_);
v___x_2206_ = lean_box(0);
v___x_2207_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__22(v___x_2205_, v___x_2206_);
v___x_2208_ = l_Lean_MessageData_ofList(v___x_2207_);
v___x_2209_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2209_, 0, v___x_2204_);
lean_ctor_set(v___x_2209_, 1, v___x_2208_);
v___x_2210_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_2154_, v___x_2209_, v_a_2124_, v_a_2125_, v_a_2126_, v_a_2127_);
if (lean_obj_tag(v___x_2210_) == 0)
{
lean_dec_ref_known(v___x_2210_, 1);
v___y_2157_ = v_a_2124_;
v___y_2158_ = v_a_2125_;
v___y_2159_ = v_a_2126_;
v___y_2160_ = v_a_2127_;
goto v___jp_2156_;
}
else
{
lean_object* v_a_2211_; lean_object* v___x_2213_; uint8_t v_isShared_2214_; uint8_t v_isSharedCheck_2218_; 
lean_dec_ref(v___x_2153_);
lean_dec(v_a_2150_);
lean_dec(v_a_2139_);
lean_dec(v_a_2137_);
lean_dec_ref(v_recArgInfos_2123_);
lean_dec_ref(v_xs_2122_);
lean_dec_ref(v_fixedParamPerms_2121_);
lean_dec_ref(v_preDefs_2120_);
v_a_2211_ = lean_ctor_get(v___x_2210_, 0);
v_isSharedCheck_2218_ = !lean_is_exclusive(v___x_2210_);
if (v_isSharedCheck_2218_ == 0)
{
v___x_2213_ = v___x_2210_;
v_isShared_2214_ = v_isSharedCheck_2218_;
goto v_resetjp_2212_;
}
else
{
lean_inc(v_a_2211_);
lean_dec(v___x_2210_);
v___x_2213_ = lean_box(0);
v_isShared_2214_ = v_isSharedCheck_2218_;
goto v_resetjp_2212_;
}
v_resetjp_2212_:
{
lean_object* v___x_2216_; 
if (v_isShared_2214_ == 0)
{
v___x_2216_ = v___x_2213_;
goto v_reusejp_2215_;
}
else
{
lean_object* v_reuseFailAlloc_2217_; 
v_reuseFailAlloc_2217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2217_, 0, v_a_2211_);
v___x_2216_ = v_reuseFailAlloc_2217_;
goto v_reusejp_2215_;
}
v_reusejp_2215_:
{
return v___x_2216_;
}
}
}
}
}
v___jp_2156_:
{
lean_object* v_toConstantVal_2161_; lean_object* v_numIndices_2162_; lean_object* v_name_2163_; lean_object* v___x_2164_; 
v_toConstantVal_2161_ = lean_ctor_get(v_a_2150_, 0);
lean_inc_ref(v_toConstantVal_2161_);
v_numIndices_2162_ = lean_ctor_get(v_a_2150_, 2);
lean_inc(v_numIndices_2162_);
lean_dec(v_a_2150_);
v_name_2163_ = lean_ctor_get(v_toConstantVal_2161_, 0);
lean_inc(v_name_2163_);
lean_dec_ref(v_toConstantVal_2161_);
v___x_2164_ = l_Lean_Meta_isInductivePredicate(v_name_2163_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_);
if (lean_obj_tag(v___x_2164_) == 0)
{
lean_object* v_a_2165_; lean_object* v___x_2166_; lean_object* v___f_2167_; uint8_t v___x_2168_; 
v_a_2165_ = lean_ctor_get(v___x_2164_, 0);
lean_inc_n(v_a_2165_, 2);
lean_dec_ref_known(v___x_2164_, 1);
v___x_2166_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___boxed__const__1));
lean_inc(v_numIndices_2162_);
lean_inc_ref(v_preDefs_2120_);
lean_inc_ref(v_xs_2122_);
lean_inc_ref(v_fixedParamPerms_2121_);
lean_inc_ref(v___x_2153_);
lean_inc(v_a_2137_);
lean_inc_ref(v_recArgInfos_2123_);
v___f_2167_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___boxed), 21, 14);
lean_closure_set(v___f_2167_, 0, v_recArgInfos_2123_);
lean_closure_set(v___f_2167_, 1, v_a_2137_);
lean_closure_set(v___f_2167_, 2, v___x_2153_);
lean_closure_set(v___f_2167_, 3, v___x_2166_);
lean_closure_set(v___f_2167_, 4, v_fixedParamPerms_2121_);
lean_closure_set(v___f_2167_, 5, v_xs_2122_);
lean_closure_set(v___f_2167_, 6, v___x_2140_);
lean_closure_set(v___f_2167_, 7, v_preDefs_2120_);
lean_closure_set(v___f_2167_, 8, v_numIndices_2162_);
lean_closure_set(v___f_2167_, 9, v___f_2129_);
lean_closure_set(v___f_2167_, 10, v___x_2154_);
lean_closure_set(v___f_2167_, 11, v_a_2165_);
lean_closure_set(v___f_2167_, 12, v___x_2133_);
lean_closure_set(v___f_2167_, 13, v___f_2155_);
v___x_2168_ = lean_unbox(v_a_2165_);
if (v___x_2168_ == 0)
{
size_t v_sz_2169_; lean_object* v___x_2170_; 
lean_dec_ref(v___f_2167_);
v_sz_2169_ = lean_array_size(v_recArgInfos_2123_);
lean_inc_ref(v_recArgInfos_2123_);
v___x_2170_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__21___redArg(v_a_2137_, v_a_2139_, v_sz_2169_, v___x_2135_, v_recArgInfos_2123_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_);
lean_dec(v_a_2139_);
if (lean_obj_tag(v___x_2170_) == 0)
{
lean_object* v_a_2171_; lean_object* v___x_2172_; uint8_t v___x_2173_; lean_object* v___x_2174_; 
v_a_2171_ = lean_ctor_get(v___x_2170_, 0);
lean_inc(v_a_2171_);
lean_dec_ref_known(v___x_2170_, 1);
v___x_2172_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__7));
v___x_2173_ = lean_unbox(v_a_2165_);
lean_dec(v_a_2165_);
v___x_2174_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2(v_recArgInfos_2123_, v_a_2137_, v___x_2153_, v___x_2135_, v_fixedParamPerms_2121_, v_xs_2122_, v___x_2140_, v_preDefs_2120_, v_numIndices_2162_, v___f_2129_, v___x_2154_, v___x_2173_, v___x_2133_, v___f_2155_, v___x_2172_, v_a_2171_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_);
lean_dec(v_numIndices_2162_);
lean_dec(v_a_2137_);
return v___x_2174_;
}
else
{
lean_object* v_a_2175_; lean_object* v___x_2177_; uint8_t v_isShared_2178_; uint8_t v_isSharedCheck_2182_; 
lean_dec(v_a_2165_);
lean_dec(v_numIndices_2162_);
lean_dec_ref(v___x_2153_);
lean_dec(v_a_2137_);
lean_dec_ref(v_recArgInfos_2123_);
lean_dec_ref(v_xs_2122_);
lean_dec_ref(v_fixedParamPerms_2121_);
lean_dec_ref(v_preDefs_2120_);
v_a_2175_ = lean_ctor_get(v___x_2170_, 0);
v_isSharedCheck_2182_ = !lean_is_exclusive(v___x_2170_);
if (v_isSharedCheck_2182_ == 0)
{
v___x_2177_ = v___x_2170_;
v_isShared_2178_ = v_isSharedCheck_2182_;
goto v_resetjp_2176_;
}
else
{
lean_inc(v_a_2175_);
lean_dec(v___x_2170_);
v___x_2177_ = lean_box(0);
v_isShared_2178_ = v_isSharedCheck_2182_;
goto v_resetjp_2176_;
}
v_resetjp_2176_:
{
lean_object* v___x_2180_; 
if (v_isShared_2178_ == 0)
{
v___x_2180_ = v___x_2177_;
goto v_reusejp_2179_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v_a_2175_);
v___x_2180_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2179_;
}
v_reusejp_2179_:
{
return v___x_2180_;
}
}
}
}
else
{
lean_object* v___x_2183_; lean_object* v___f_2184_; lean_object* v___x_2185_; 
lean_dec(v_a_2165_);
lean_dec(v_numIndices_2162_);
lean_dec_ref(v___x_2153_);
lean_dec(v_a_2139_);
lean_dec_ref(v_xs_2122_);
lean_dec_ref(v_fixedParamPerms_2121_);
lean_dec_ref(v_preDefs_2120_);
v___x_2183_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___boxed__const__1));
lean_inc(v_a_2137_);
v___f_2184_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__3___boxed), 10, 4);
lean_closure_set(v___f_2184_, 0, v_recArgInfos_2123_);
lean_closure_set(v___f_2184_, 1, v_a_2137_);
lean_closure_set(v___f_2184_, 2, v___x_2183_);
lean_closure_set(v___f_2184_, 3, v___f_2167_);
v___x_2185_ = l_Lean_Elab_Structural_withFunTypes___redArg(v_a_2137_, v___f_2184_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_);
return v___x_2185_;
}
}
else
{
lean_object* v_a_2186_; lean_object* v___x_2188_; uint8_t v_isShared_2189_; uint8_t v_isSharedCheck_2193_; 
lean_dec(v_numIndices_2162_);
lean_dec_ref(v___x_2153_);
lean_dec(v_a_2139_);
lean_dec(v_a_2137_);
lean_dec_ref(v_recArgInfos_2123_);
lean_dec_ref(v_xs_2122_);
lean_dec_ref(v_fixedParamPerms_2121_);
lean_dec_ref(v_preDefs_2120_);
v_a_2186_ = lean_ctor_get(v___x_2164_, 0);
v_isSharedCheck_2193_ = !lean_is_exclusive(v___x_2164_);
if (v_isSharedCheck_2193_ == 0)
{
v___x_2188_ = v___x_2164_;
v_isShared_2189_ = v_isSharedCheck_2193_;
goto v_resetjp_2187_;
}
else
{
lean_inc(v_a_2186_);
lean_dec(v___x_2164_);
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
}
else
{
lean_object* v_a_2220_; lean_object* v___x_2222_; uint8_t v_isShared_2223_; uint8_t v_isSharedCheck_2227_; 
lean_del_object(v___x_2146_);
lean_dec(v_a_2139_);
lean_dec(v_a_2137_);
lean_dec_ref(v_recArgInfos_2123_);
lean_dec_ref(v_xs_2122_);
lean_dec_ref(v_fixedParamPerms_2121_);
lean_dec_ref(v_preDefs_2120_);
v_a_2220_ = lean_ctor_get(v___x_2149_, 0);
v_isSharedCheck_2227_ = !lean_is_exclusive(v___x_2149_);
if (v_isSharedCheck_2227_ == 0)
{
v___x_2222_ = v___x_2149_;
v_isShared_2223_ = v_isSharedCheck_2227_;
goto v_resetjp_2221_;
}
else
{
lean_inc(v_a_2220_);
lean_dec(v___x_2149_);
v___x_2222_ = lean_box(0);
v_isShared_2223_ = v_isSharedCheck_2227_;
goto v_resetjp_2221_;
}
v_resetjp_2221_:
{
lean_object* v___x_2225_; 
if (v_isShared_2223_ == 0)
{
v___x_2225_ = v___x_2222_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v_a_2220_);
v___x_2225_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
return v___x_2225_;
}
}
}
}
}
else
{
lean_object* v_a_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2237_; 
lean_dec(v_a_2137_);
lean_dec_ref(v_recArgInfos_2123_);
lean_dec_ref(v_xs_2122_);
lean_dec_ref(v_fixedParamPerms_2121_);
lean_dec_ref(v_preDefs_2120_);
v_a_2230_ = lean_ctor_get(v___x_2138_, 0);
v_isSharedCheck_2237_ = !lean_is_exclusive(v___x_2138_);
if (v_isSharedCheck_2237_ == 0)
{
v___x_2232_ = v___x_2138_;
v_isShared_2233_ = v_isSharedCheck_2237_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_a_2230_);
lean_dec(v___x_2138_);
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
else
{
lean_object* v_a_2238_; lean_object* v___x_2240_; uint8_t v_isShared_2241_; uint8_t v_isSharedCheck_2245_; 
lean_dec_ref(v_recArgInfos_2123_);
lean_dec_ref(v_xs_2122_);
lean_dec_ref(v_fixedParamPerms_2121_);
lean_dec_ref(v_preDefs_2120_);
v_a_2238_ = lean_ctor_get(v___x_2136_, 0);
v_isSharedCheck_2245_ = !lean_is_exclusive(v___x_2136_);
if (v_isSharedCheck_2245_ == 0)
{
v___x_2240_ = v___x_2136_;
v_isShared_2241_ = v_isSharedCheck_2245_;
goto v_resetjp_2239_;
}
else
{
lean_inc(v_a_2238_);
lean_dec(v___x_2136_);
v___x_2240_ = lean_box(0);
v_isShared_2241_ = v_isSharedCheck_2245_;
goto v_resetjp_2239_;
}
v_resetjp_2239_:
{
lean_object* v___x_2243_; 
if (v_isShared_2241_ == 0)
{
v___x_2243_ = v___x_2240_;
goto v_reusejp_2242_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v_a_2238_);
v___x_2243_ = v_reuseFailAlloc_2244_;
goto v_reusejp_2242_;
}
v_reusejp_2242_:
{
return v___x_2243_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___boxed(lean_object* v_preDefs_2246_, lean_object* v_fixedParamPerms_2247_, lean_object* v_xs_2248_, lean_object* v_recArgInfos_2249_, lean_object* v_a_2250_, lean_object* v_a_2251_, lean_object* v_a_2252_, lean_object* v_a_2253_, lean_object* v_a_2254_){
_start:
{
lean_object* v_res_2255_; 
v_res_2255_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion(v_preDefs_2246_, v_fixedParamPerms_2247_, v_xs_2248_, v_recArgInfos_2249_, v_a_2250_, v_a_2251_, v_a_2252_, v_a_2253_);
lean_dec(v_a_2253_);
lean_dec_ref(v_a_2252_);
lean_dec(v_a_2251_);
lean_dec_ref(v_a_2250_);
return v_res_2255_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2(lean_object* v_fixedParamPerms_2256_, lean_object* v_xs_2257_, lean_object* v_as_2258_, size_t v_sz_2259_, size_t v_i_2260_, lean_object* v_bs_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_){
_start:
{
lean_object* v___x_2267_; 
v___x_2267_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___redArg(v_fixedParamPerms_2256_, v_xs_2257_, v_sz_2259_, v_i_2260_, v_bs_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_);
return v___x_2267_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___boxed(lean_object* v_fixedParamPerms_2268_, lean_object* v_xs_2269_, lean_object* v_as_2270_, lean_object* v_sz_2271_, lean_object* v_i_2272_, lean_object* v_bs_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_){
_start:
{
size_t v_sz_boxed_2279_; size_t v_i_boxed_2280_; lean_object* v_res_2281_; 
v_sz_boxed_2279_ = lean_unbox_usize(v_sz_2271_);
lean_dec(v_sz_2271_);
v_i_boxed_2280_ = lean_unbox_usize(v_i_2272_);
lean_dec(v_i_2272_);
v_res_2281_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2(v_fixedParamPerms_2268_, v_xs_2269_, v_as_2270_, v_sz_boxed_2279_, v_i_boxed_2280_, v_bs_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_);
lean_dec(v___y_2277_);
lean_dec_ref(v___y_2276_);
lean_dec(v___y_2275_);
lean_dec_ref(v___y_2274_);
lean_dec_ref(v_as_2270_);
lean_dec_ref(v_fixedParamPerms_2268_);
return v_res_2281_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3(lean_object* v_fixedParamPerms_2282_, lean_object* v_xs_2283_, lean_object* v_as_2284_, size_t v_sz_2285_, size_t v_i_2286_, lean_object* v_bs_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_){
_start:
{
lean_object* v___x_2293_; 
v___x_2293_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___redArg(v_fixedParamPerms_2282_, v_xs_2283_, v_sz_2285_, v_i_2286_, v_bs_2287_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_);
return v___x_2293_;
}
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14(lean_object* v_00_u03b3_2308_, lean_object* v_msg_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_){
_start:
{
lean_object* v___x_2315_; 
v___x_2315_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg(v_msg_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_);
return v___x_2315_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___boxed(lean_object* v_00_u03b3_2316_, lean_object* v_msg_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_){
_start:
{
lean_object* v_res_2323_; 
v_res_2323_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14(v_00_u03b3_2316_, v_msg_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_);
lean_dec(v___y_2321_);
lean_dec_ref(v___y_2320_);
lean_dec(v___y_2319_);
lean_dec_ref(v___y_2318_);
return v_res_2323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6(lean_object* v_00_u03b3_2324_, lean_object* v_00_u03b1_2325_, lean_object* v_f_2326_, lean_object* v_positions_2327_, lean_object* v_ys_2328_, lean_object* v_xs_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_){
_start:
{
lean_object* v___x_2335_; 
v___x_2335_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg(v_f_2326_, v_positions_2327_, v_ys_2328_, v_xs_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_);
return v___x_2335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___boxed(lean_object* v_00_u03b3_2336_, lean_object* v_00_u03b1_2337_, lean_object* v_f_2338_, lean_object* v_positions_2339_, lean_object* v_ys_2340_, lean_object* v_xs_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_){
_start:
{
lean_object* v_res_2347_; 
v_res_2347_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6(v_00_u03b3_2336_, v_00_u03b1_2337_, v_f_2338_, v_positions_2339_, v_ys_2340_, v_xs_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_);
lean_dec(v___y_2345_);
lean_dec_ref(v___y_2344_);
lean_dec(v___y_2343_);
lean_dec_ref(v___y_2342_);
lean_dec_ref(v_xs_2341_);
lean_dec_ref(v_ys_2340_);
lean_dec_ref(v_positions_2339_);
return v_res_2347_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7(lean_object* v___x_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v_funTypes_2351_, lean_object* v_as_2352_, size_t v_sz_2353_, size_t v_i_2354_, lean_object* v_bs_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_){
_start:
{
lean_object* v___x_2361_; 
v___x_2361_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg(v___x_2348_, v_a_2349_, v_a_2350_, v_funTypes_2351_, v_sz_2353_, v_i_2354_, v_bs_2355_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_);
return v___x_2361_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___boxed(lean_object* v___x_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_, lean_object* v_funTypes_2365_, lean_object* v_as_2366_, lean_object* v_sz_2367_, lean_object* v_i_2368_, lean_object* v_bs_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_){
_start:
{
size_t v_sz_boxed_2375_; size_t v_i_boxed_2376_; lean_object* v_res_2377_; 
v_sz_boxed_2375_ = lean_unbox_usize(v_sz_2367_);
lean_dec(v_sz_2367_);
v_i_boxed_2376_ = lean_unbox_usize(v_i_2368_);
lean_dec(v_i_2368_);
v_res_2377_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7(v___x_2362_, v_a_2363_, v_a_2364_, v_funTypes_2365_, v_as_2366_, v_sz_boxed_2375_, v_i_boxed_2376_, v_bs_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_);
lean_dec(v___y_2373_);
lean_dec_ref(v___y_2372_);
lean_dec(v___y_2371_);
lean_dec_ref(v___y_2370_);
lean_dec_ref(v_as_2366_);
return v_res_2377_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8(lean_object* v_fixedParamPerms_2378_, lean_object* v_xs_2379_, lean_object* v_as_2380_, size_t v_sz_2381_, size_t v_i_2382_, lean_object* v_bs_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_){
_start:
{
lean_object* v___x_2389_; 
v___x_2389_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg(v_fixedParamPerms_2378_, v_xs_2379_, v_sz_2381_, v_i_2382_, v_bs_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_);
return v___x_2389_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___boxed(lean_object* v_fixedParamPerms_2390_, lean_object* v_xs_2391_, lean_object* v_as_2392_, lean_object* v_sz_2393_, lean_object* v_i_2394_, lean_object* v_bs_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_){
_start:
{
size_t v_sz_boxed_2401_; size_t v_i_boxed_2402_; lean_object* v_res_2403_; 
v_sz_boxed_2401_ = lean_unbox_usize(v_sz_2393_);
lean_dec(v_sz_2393_);
v_i_boxed_2402_ = lean_unbox_usize(v_i_2394_);
lean_dec(v_i_2394_);
v_res_2403_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8(v_fixedParamPerms_2390_, v_xs_2391_, v_as_2392_, v_sz_boxed_2401_, v_i_boxed_2402_, v_bs_2395_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_);
lean_dec(v___y_2399_);
lean_dec_ref(v___y_2398_);
lean_dec(v___y_2397_);
lean_dec_ref(v___y_2396_);
lean_dec_ref(v_as_2392_);
return v_res_2403_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12(lean_object* v_00_u03b1_2404_, lean_object* v_preDefs_2405_, lean_object* v_k_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_){
_start:
{
lean_object* v___x_2412_; 
v___x_2412_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v_preDefs_2405_, v_k_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_);
return v___x_2412_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___boxed(lean_object* v_00_u03b1_2413_, lean_object* v_preDefs_2414_, lean_object* v_k_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_){
_start:
{
lean_object* v_res_2421_; 
v_res_2421_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12(v_00_u03b1_2413_, v_preDefs_2414_, v_k_2415_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_);
lean_dec(v___y_2419_);
lean_dec_ref(v___y_2418_);
lean_dec(v___y_2417_);
lean_dec_ref(v___y_2416_);
return v_res_2421_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14(uint8_t v_a_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_, lean_object* v_recArgInfos_2425_, lean_object* v___x_2426_, lean_object* v_preDefs_2427_, lean_object* v_a_2428_, lean_object* v_as_2429_, size_t v_sz_2430_, size_t v_i_2431_, lean_object* v_bs_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_){
_start:
{
lean_object* v___x_2438_; 
v___x_2438_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg(v_a_2422_, v_a_2423_, v_a_2424_, v_recArgInfos_2425_, v___x_2426_, v_preDefs_2427_, v_a_2428_, v_sz_2430_, v_i_2431_, v_bs_2432_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_);
return v___x_2438_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___boxed(lean_object* v_a_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_, lean_object* v_recArgInfos_2442_, lean_object* v___x_2443_, lean_object* v_preDefs_2444_, lean_object* v_a_2445_, lean_object* v_as_2446_, lean_object* v_sz_2447_, lean_object* v_i_2448_, lean_object* v_bs_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_){
_start:
{
uint8_t v_a_29306__boxed_2455_; size_t v_sz_boxed_2456_; size_t v_i_boxed_2457_; lean_object* v_res_2458_; 
v_a_29306__boxed_2455_ = lean_unbox(v_a_2439_);
v_sz_boxed_2456_ = lean_unbox_usize(v_sz_2447_);
lean_dec(v_sz_2447_);
v_i_boxed_2457_ = lean_unbox_usize(v_i_2448_);
lean_dec(v_i_2448_);
v_res_2458_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14(v_a_29306__boxed_2455_, v_a_2440_, v_a_2441_, v_recArgInfos_2442_, v___x_2443_, v_preDefs_2444_, v_a_2445_, v_as_2446_, v_sz_boxed_2456_, v_i_boxed_2457_, v_bs_2449_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_);
lean_dec(v___y_2453_);
lean_dec_ref(v___y_2452_);
lean_dec(v___y_2451_);
lean_dec_ref(v___y_2450_);
lean_dec_ref(v_as_2446_);
lean_dec_ref(v_a_2441_);
lean_dec_ref(v_a_2440_);
return v_res_2458_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17_spec__30(lean_object* v_00_u03b2_2459_){
_start:
{
lean_object* v___x_2460_; 
v___x_2460_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__2);
return v___x_2460_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg(){
_start:
{
lean_object* v___x_2462_; 
v___x_2462_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__2);
return v___x_2462_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg___boxed(lean_object* v___dummy_2463_){
_start:
{
lean_object* v_res_2464_; 
v_res_2464_ = l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg();
return v_res_2464_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17(lean_object* v_00_u03b2_2465_){
_start:
{
lean_object* v___x_2466_; 
v___x_2466_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__2);
return v___x_2466_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19(lean_object* v_preDefs_2467_, lean_object* v_xs_2468_, uint8_t v_a_2469_, lean_object* v___x_2470_, lean_object* v_as_2471_, size_t v_sz_2472_, size_t v_i_2473_, lean_object* v_bs_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_){
_start:
{
lean_object* v___x_2480_; 
v___x_2480_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___redArg(v_preDefs_2467_, v_xs_2468_, v_a_2469_, v___x_2470_, v_sz_2472_, v_i_2473_, v_bs_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_);
return v___x_2480_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___boxed(lean_object* v_preDefs_2481_, lean_object* v_xs_2482_, lean_object* v_a_2483_, lean_object* v___x_2484_, lean_object* v_as_2485_, lean_object* v_sz_2486_, lean_object* v_i_2487_, lean_object* v_bs_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_){
_start:
{
uint8_t v_a_29347__boxed_2494_; size_t v_sz_boxed_2495_; size_t v_i_boxed_2496_; lean_object* v_res_2497_; 
v_a_29347__boxed_2494_ = lean_unbox(v_a_2483_);
v_sz_boxed_2495_ = lean_unbox_usize(v_sz_2486_);
lean_dec(v_sz_2486_);
v_i_boxed_2496_ = lean_unbox_usize(v_i_2487_);
lean_dec(v_i_2487_);
v_res_2497_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19(v_preDefs_2481_, v_xs_2482_, v_a_29347__boxed_2494_, v___x_2484_, v_as_2485_, v_sz_boxed_2495_, v_i_boxed_2496_, v_bs_2488_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_);
lean_dec(v___y_2492_);
lean_dec_ref(v___y_2491_);
lean_dec(v___y_2490_);
lean_dec_ref(v___y_2489_);
lean_dec_ref(v_as_2485_);
lean_dec_ref(v_xs_2482_);
return v_res_2497_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__20(lean_object* v_a_2498_, lean_object* v_funTypes_2499_, lean_object* v_as_2500_, size_t v_sz_2501_, size_t v_i_2502_, lean_object* v_bs_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_){
_start:
{
lean_object* v___x_2509_; 
v___x_2509_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__20___redArg(v_a_2498_, v_funTypes_2499_, v_sz_2501_, v_i_2502_, v_bs_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_);
return v___x_2509_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__20___boxed(lean_object* v_a_2510_, lean_object* v_funTypes_2511_, lean_object* v_as_2512_, lean_object* v_sz_2513_, lean_object* v_i_2514_, lean_object* v_bs_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_){
_start:
{
size_t v_sz_boxed_2521_; size_t v_i_boxed_2522_; lean_object* v_res_2523_; 
v_sz_boxed_2521_ = lean_unbox_usize(v_sz_2513_);
lean_dec(v_sz_2513_);
v_i_boxed_2522_ = lean_unbox_usize(v_i_2514_);
lean_dec(v_i_2514_);
v_res_2523_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__20(v_a_2510_, v_funTypes_2511_, v_as_2512_, v_sz_boxed_2521_, v_i_boxed_2522_, v_bs_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_);
lean_dec(v___y_2519_);
lean_dec_ref(v___y_2518_);
lean_dec(v___y_2517_);
lean_dec_ref(v___y_2516_);
lean_dec_ref(v_as_2512_);
lean_dec_ref(v_funTypes_2511_);
lean_dec_ref(v_a_2510_);
return v_res_2523_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__21(lean_object* v_a_2524_, lean_object* v_a_2525_, lean_object* v_as_2526_, size_t v_sz_2527_, size_t v_i_2528_, lean_object* v_bs_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_){
_start:
{
lean_object* v___x_2535_; 
v___x_2535_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__21___redArg(v_a_2524_, v_a_2525_, v_sz_2527_, v_i_2528_, v_bs_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_);
return v___x_2535_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__21___boxed(lean_object* v_a_2536_, lean_object* v_a_2537_, lean_object* v_as_2538_, lean_object* v_sz_2539_, lean_object* v_i_2540_, lean_object* v_bs_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_){
_start:
{
size_t v_sz_boxed_2547_; size_t v_i_boxed_2548_; lean_object* v_res_2549_; 
v_sz_boxed_2547_ = lean_unbox_usize(v_sz_2539_);
lean_dec(v_sz_2539_);
v_i_boxed_2548_ = lean_unbox_usize(v_i_2540_);
lean_dec(v_i_2540_);
v_res_2549_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__21(v_a_2536_, v_a_2537_, v_as_2538_, v_sz_boxed_2547_, v_i_boxed_2548_, v_bs_2541_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_);
lean_dec(v___y_2545_);
lean_dec_ref(v___y_2544_);
lean_dec(v___y_2543_);
lean_dec_ref(v___y_2542_);
lean_dec_ref(v_as_2538_);
lean_dec_ref(v_a_2537_);
lean_dec_ref(v_a_2536_);
return v_res_2549_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4(lean_object* v_00_u03b1_2550_, lean_object* v_msg_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_){
_start:
{
lean_object* v___x_2557_; 
v___x_2557_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg(v_msg_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_);
return v___x_2557_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___boxed(lean_object* v_00_u03b1_2558_, lean_object* v_msg_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_){
_start:
{
lean_object* v_res_2565_; 
v_res_2565_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4(v_00_u03b1_2558_, v_msg_2559_, v___y_2560_, v___y_2561_, v___y_2562_, v___y_2563_);
lean_dec(v___y_2563_);
lean_dec_ref(v___y_2562_);
lean_dec(v___y_2561_);
lean_dec_ref(v___y_2560_);
return v_res_2565_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9(lean_object* v_xs_2566_, lean_object* v_ys_2567_, lean_object* v_hsz_2568_, lean_object* v_x_2569_, lean_object* v_x_2570_){
_start:
{
uint8_t v___x_2571_; 
v___x_2571_ = l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9___redArg(v_xs_2566_, v_ys_2567_, v_x_2569_);
return v___x_2571_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9___boxed(lean_object* v_xs_2572_, lean_object* v_ys_2573_, lean_object* v_hsz_2574_, lean_object* v_x_2575_, lean_object* v_x_2576_){
_start:
{
uint8_t v_res_2577_; lean_object* v_r_2578_; 
v_res_2577_ = l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9(v_xs_2572_, v_ys_2573_, v_hsz_2574_, v_x_2575_, v_x_2576_);
lean_dec_ref(v_ys_2573_);
lean_dec_ref(v_xs_2572_);
v_r_2578_ = lean_box(v_res_2577_);
return v_r_2578_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10(lean_object* v_n_2579_, lean_object* v_as_2580_, lean_object* v_lo_2581_, lean_object* v_hi_2582_, lean_object* v_w_2583_, lean_object* v_hlo_2584_, lean_object* v_hhi_2585_){
_start:
{
lean_object* v___x_2586_; 
v___x_2586_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg(v_n_2579_, v_as_2580_, v_lo_2581_, v_hi_2582_);
return v___x_2586_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___boxed(lean_object* v_n_2587_, lean_object* v_as_2588_, lean_object* v_lo_2589_, lean_object* v_hi_2590_, lean_object* v_w_2591_, lean_object* v_hlo_2592_, lean_object* v_hhi_2593_){
_start:
{
lean_object* v_res_2594_; 
v_res_2594_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10(v_n_2587_, v_as_2588_, v_lo_2589_, v_hi_2590_, v_w_2591_, v_hlo_2592_, v_hhi_2593_);
lean_dec(v_hi_2590_);
lean_dec(v_n_2587_);
return v_res_2594_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15(lean_object* v_00_u03b1_2595_, lean_object* v_00_u03b3_2596_, lean_object* v_xs_2597_, lean_object* v_f_2598_, lean_object* v_as_2599_, lean_object* v_bs_2600_, lean_object* v_i_2601_, lean_object* v_cs_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_){
_start:
{
lean_object* v___x_2608_; 
v___x_2608_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15___redArg(v_xs_2597_, v_f_2598_, v_as_2599_, v_bs_2600_, v_i_2601_, v_cs_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_);
return v___x_2608_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15___boxed(lean_object* v_00_u03b1_2609_, lean_object* v_00_u03b3_2610_, lean_object* v_xs_2611_, lean_object* v_f_2612_, lean_object* v_as_2613_, lean_object* v_bs_2614_, lean_object* v_i_2615_, lean_object* v_cs_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_){
_start:
{
lean_object* v_res_2622_; 
v_res_2622_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15(v_00_u03b1_2609_, v_00_u03b3_2610_, v_xs_2611_, v_f_2612_, v_as_2613_, v_bs_2614_, v_i_2615_, v_cs_2616_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_);
lean_dec(v___y_2620_);
lean_dec_ref(v___y_2619_);
lean_dec(v___y_2618_);
lean_dec_ref(v___y_2617_);
lean_dec_ref(v_bs_2614_);
lean_dec_ref(v_as_2613_);
lean_dec_ref(v_xs_2611_);
return v_res_2622_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23(lean_object* v_00_u03b1_2623_, lean_object* v_env_2624_, lean_object* v_x_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_){
_start:
{
lean_object* v___x_2631_; 
v___x_2631_ = l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23___redArg(v_env_2624_, v_x_2625_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_);
return v___x_2631_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23___boxed(lean_object* v_00_u03b1_2632_, lean_object* v_env_2633_, lean_object* v_x_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_){
_start:
{
lean_object* v_res_2640_; 
v_res_2640_ = l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23(v_00_u03b1_2632_, v_env_2633_, v_x_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_);
lean_dec(v___y_2638_);
lean_dec_ref(v___y_2637_);
lean_dec(v___y_2636_);
lean_dec_ref(v___y_2635_);
return v_res_2640_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32(lean_object* v_declName_2641_, uint8_t v_s_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_){
_start:
{
lean_object* v___x_2648_; 
v___x_2648_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg(v_declName_2641_, v_s_2642_, v___y_2644_, v___y_2646_);
return v___x_2648_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___boxed(lean_object* v_declName_2649_, lean_object* v_s_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_){
_start:
{
uint8_t v_s_boxed_2656_; lean_object* v_res_2657_; 
v_s_boxed_2656_ = lean_unbox(v_s_2650_);
v_res_2657_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32(v_declName_2649_, v_s_boxed_2656_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_);
lean_dec(v___y_2654_);
lean_dec_ref(v___y_2653_);
lean_dec(v___y_2652_);
lean_dec_ref(v___y_2651_);
return v_res_2657_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11(lean_object* v_n_2658_, lean_object* v_lo_2659_, lean_object* v_hi_2660_, lean_object* v_hhi_2661_, lean_object* v_pivot_2662_, lean_object* v_as_2663_, lean_object* v_i_2664_, lean_object* v_k_2665_, lean_object* v_ilo_2666_, lean_object* v_ik_2667_, lean_object* v_w_2668_){
_start:
{
lean_object* v___x_2669_; 
v___x_2669_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11___redArg(v_hi_2660_, v_pivot_2662_, v_as_2663_, v_i_2664_, v_k_2665_);
return v___x_2669_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11___boxed(lean_object* v_n_2670_, lean_object* v_lo_2671_, lean_object* v_hi_2672_, lean_object* v_hhi_2673_, lean_object* v_pivot_2674_, lean_object* v_as_2675_, lean_object* v_i_2676_, lean_object* v_k_2677_, lean_object* v_ilo_2678_, lean_object* v_ik_2679_, lean_object* v_w_2680_){
_start:
{
lean_object* v_res_2681_; 
v_res_2681_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11(v_n_2670_, v_lo_2671_, v_hi_2672_, v_hhi_2673_, v_pivot_2674_, v_as_2675_, v_i_2676_, v_k_2677_, v_ilo_2678_, v_ik_2679_, v_w_2680_);
lean_dec(v_pivot_2674_);
lean_dec(v_hi_2672_);
lean_dec(v_lo_2671_);
lean_dec(v_n_2670_);
return v_res_2681_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25(lean_object* v_env_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_){
_start:
{
lean_object* v___x_2688_; 
v___x_2688_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg(v_env_2682_, v___y_2684_, v___y_2686_);
return v___x_2688_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___boxed(lean_object* v_env_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_){
_start:
{
lean_object* v_res_2695_; 
v_res_2695_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25(v_env_2689_, v___y_2690_, v___y_2691_, v___y_2692_, v___y_2693_);
lean_dec(v___y_2693_);
lean_dec_ref(v___y_2692_);
lean_dec(v___y_2691_);
lean_dec_ref(v___y_2690_);
return v_res_2695_;
}
}
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg___lam__0(lean_object* v_x_2696_){
_start:
{
uint8_t v___x_2697_; 
v___x_2697_ = 0;
return v___x_2697_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg___lam__0___boxed(lean_object* v_x_2698_){
_start:
{
uint8_t v_res_2699_; lean_object* v_r_2700_; 
v_res_2699_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg___lam__0(v_x_2698_);
lean_dec(v_x_2698_);
v_r_2700_ = lean_box(v_res_2699_);
return v_r_2700_;
}
}
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg___lam__1(lean_object* v_fvarId_2701_, lean_object* v_x_2702_){
_start:
{
uint8_t v___x_2703_; 
v___x_2703_ = l_Lean_instBEqFVarId_beq(v_fvarId_2701_, v_x_2702_);
return v___x_2703_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg___lam__1___boxed(lean_object* v_fvarId_2704_, lean_object* v_x_2705_){
_start:
{
uint8_t v_res_2706_; lean_object* v_r_2707_; 
v_res_2706_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg___lam__1(v_fvarId_2704_, v_x_2705_);
lean_dec(v_x_2705_);
lean_dec(v_fvarId_2704_);
v_r_2707_ = lean_box(v_res_2706_);
return v_r_2707_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; 
v___x_2709_ = lean_box(0);
v___x_2710_ = lean_unsigned_to_nat(16u);
v___x_2711_ = lean_mk_array(v___x_2710_, v___x_2709_);
return v___x_2711_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; 
v___x_2712_ = lean_obj_once(&l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg___closed__1, &l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg___closed__1_once, _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg___closed__1);
v___x_2713_ = lean_unsigned_to_nat(0u);
v___x_2714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2714_, 0, v___x_2713_);
lean_ctor_set(v___x_2714_, 1, v___x_2712_);
return v___x_2714_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg(lean_object* v_e_2715_, lean_object* v_fvarId_2716_, lean_object* v___y_2717_){
_start:
{
lean_object* v___f_2719_; lean_object* v___f_2720_; lean_object* v___x_2721_; uint8_t v_fst_2723_; lean_object* v_mctx_2724_; lean_object* v___y_2742_; lean_object* v_mctx_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; uint8_t v___x_2750_; 
v___f_2719_ = ((lean_object*)(l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg___closed__0));
v___f_2720_ = lean_alloc_closure((void*)(l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_2720_, 0, v_fvarId_2716_);
v___x_2721_ = lean_st_ref_get(v___y_2717_);
v_mctx_2747_ = lean_ctor_get(v___x_2721_, 0);
lean_inc_ref_n(v_mctx_2747_, 2);
lean_dec(v___x_2721_);
v___x_2748_ = lean_obj_once(&l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg___closed__2, &l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg___closed__2_once, _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg___closed__2);
v___x_2749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2749_, 0, v___x_2748_);
lean_ctor_set(v___x_2749_, 1, v_mctx_2747_);
v___x_2750_ = l_Lean_Expr_hasFVar(v_e_2715_);
if (v___x_2750_ == 0)
{
uint8_t v___x_2751_; 
v___x_2751_ = l_Lean_Expr_hasMVar(v_e_2715_);
if (v___x_2751_ == 0)
{
lean_dec_ref_known(v___x_2749_, 2);
lean_dec_ref(v___f_2720_);
lean_dec_ref(v_e_2715_);
v_fst_2723_ = v___x_2751_;
v_mctx_2724_ = v_mctx_2747_;
goto v___jp_2722_;
}
else
{
lean_object* v___x_2752_; 
lean_dec_ref(v_mctx_2747_);
v___x_2752_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2720_, v___f_2719_, v_e_2715_, v___x_2749_);
v___y_2742_ = v___x_2752_;
goto v___jp_2741_;
}
}
else
{
lean_object* v___x_2753_; 
lean_dec_ref(v_mctx_2747_);
v___x_2753_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2720_, v___f_2719_, v_e_2715_, v___x_2749_);
v___y_2742_ = v___x_2753_;
goto v___jp_2741_;
}
v___jp_2722_:
{
lean_object* v___x_2725_; lean_object* v_cache_2726_; lean_object* v_zetaDeltaFVarIds_2727_; lean_object* v_postponed_2728_; lean_object* v_diag_2729_; lean_object* v___x_2731_; uint8_t v_isShared_2732_; uint8_t v_isSharedCheck_2739_; 
v___x_2725_ = lean_st_ref_take(v___y_2717_);
v_cache_2726_ = lean_ctor_get(v___x_2725_, 1);
v_zetaDeltaFVarIds_2727_ = lean_ctor_get(v___x_2725_, 2);
v_postponed_2728_ = lean_ctor_get(v___x_2725_, 3);
v_diag_2729_ = lean_ctor_get(v___x_2725_, 4);
v_isSharedCheck_2739_ = !lean_is_exclusive(v___x_2725_);
if (v_isSharedCheck_2739_ == 0)
{
lean_object* v_unused_2740_; 
v_unused_2740_ = lean_ctor_get(v___x_2725_, 0);
lean_dec(v_unused_2740_);
v___x_2731_ = v___x_2725_;
v_isShared_2732_ = v_isSharedCheck_2739_;
goto v_resetjp_2730_;
}
else
{
lean_inc(v_diag_2729_);
lean_inc(v_postponed_2728_);
lean_inc(v_zetaDeltaFVarIds_2727_);
lean_inc(v_cache_2726_);
lean_dec(v___x_2725_);
v___x_2731_ = lean_box(0);
v_isShared_2732_ = v_isSharedCheck_2739_;
goto v_resetjp_2730_;
}
v_resetjp_2730_:
{
lean_object* v___x_2734_; 
if (v_isShared_2732_ == 0)
{
lean_ctor_set(v___x_2731_, 0, v_mctx_2724_);
v___x_2734_ = v___x_2731_;
goto v_reusejp_2733_;
}
else
{
lean_object* v_reuseFailAlloc_2738_; 
v_reuseFailAlloc_2738_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2738_, 0, v_mctx_2724_);
lean_ctor_set(v_reuseFailAlloc_2738_, 1, v_cache_2726_);
lean_ctor_set(v_reuseFailAlloc_2738_, 2, v_zetaDeltaFVarIds_2727_);
lean_ctor_set(v_reuseFailAlloc_2738_, 3, v_postponed_2728_);
lean_ctor_set(v_reuseFailAlloc_2738_, 4, v_diag_2729_);
v___x_2734_ = v_reuseFailAlloc_2738_;
goto v_reusejp_2733_;
}
v_reusejp_2733_:
{
lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; 
v___x_2735_ = lean_st_ref_put(v___y_2717_, v___x_2734_);
v___x_2736_ = lean_box(v_fst_2723_);
v___x_2737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2737_, 0, v___x_2736_);
return v___x_2737_;
}
}
}
v___jp_2741_:
{
lean_object* v_snd_2743_; lean_object* v_fst_2744_; lean_object* v_mctx_2745_; uint8_t v___x_2746_; 
v_snd_2743_ = lean_ctor_get(v___y_2742_, 1);
lean_inc(v_snd_2743_);
v_fst_2744_ = lean_ctor_get(v___y_2742_, 0);
lean_inc(v_fst_2744_);
lean_dec_ref(v___y_2742_);
v_mctx_2745_ = lean_ctor_get(v_snd_2743_, 1);
lean_inc_ref(v_mctx_2745_);
lean_dec(v_snd_2743_);
v___x_2746_ = lean_unbox(v_fst_2744_);
lean_dec(v_fst_2744_);
v_fst_2723_ = v___x_2746_;
v_mctx_2724_ = v_mctx_2745_;
goto v___jp_2722_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg___boxed(lean_object* v_e_2754_, lean_object* v_fvarId_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_){
_start:
{
lean_object* v_res_2758_; 
v_res_2758_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg(v_e_2754_, v_fvarId_2755_, v___y_2756_);
lean_dec(v___y_2756_);
return v_res_2758_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4(lean_object* v_e_2759_, lean_object* v_fvarId_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_){
_start:
{
lean_object* v___x_2766_; 
v___x_2766_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg(v_e_2759_, v_fvarId_2760_, v___y_2762_);
return v___x_2766_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___boxed(lean_object* v_e_2767_, lean_object* v_fvarId_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_){
_start:
{
lean_object* v_res_2774_; 
v_res_2774_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4(v_e_2767_, v_fvarId_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_);
lean_dec(v___y_2772_);
lean_dec_ref(v___y_2771_);
lean_dec(v___y_2770_);
lean_dec_ref(v___y_2769_);
return v_res_2774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg___lam__0(lean_object* v_k_2775_, lean_object* v_b_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_){
_start:
{
lean_object* v___x_2782_; 
lean_inc(v___y_2780_);
lean_inc_ref(v___y_2779_);
lean_inc(v___y_2778_);
lean_inc_ref(v___y_2777_);
v___x_2782_ = lean_apply_6(v_k_2775_, v_b_2776_, v___y_2777_, v___y_2778_, v___y_2779_, v___y_2780_, lean_box(0));
return v___x_2782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg___lam__0___boxed(lean_object* v_k_2783_, lean_object* v_b_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_){
_start:
{
lean_object* v_res_2790_; 
v_res_2790_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg___lam__0(v_k_2783_, v_b_2784_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_);
lean_dec(v___y_2788_);
lean_dec_ref(v___y_2787_);
lean_dec(v___y_2786_);
lean_dec_ref(v___y_2785_);
return v_res_2790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg(lean_object* v_perm_2791_, lean_object* v_type_2792_, lean_object* v_k_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_){
_start:
{
lean_object* v___f_2799_; lean_object* v___x_2800_; 
v___f_2799_ = lean_alloc_closure((void*)(l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2799_, 0, v_k_2793_);
v___x_2800_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl(lean_box(0), v_perm_2791_, v_type_2792_, v___f_2799_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_);
if (lean_obj_tag(v___x_2800_) == 0)
{
lean_object* v_a_2801_; lean_object* v___x_2803_; uint8_t v_isShared_2804_; uint8_t v_isSharedCheck_2808_; 
v_a_2801_ = lean_ctor_get(v___x_2800_, 0);
v_isSharedCheck_2808_ = !lean_is_exclusive(v___x_2800_);
if (v_isSharedCheck_2808_ == 0)
{
v___x_2803_ = v___x_2800_;
v_isShared_2804_ = v_isSharedCheck_2808_;
goto v_resetjp_2802_;
}
else
{
lean_inc(v_a_2801_);
lean_dec(v___x_2800_);
v___x_2803_ = lean_box(0);
v_isShared_2804_ = v_isSharedCheck_2808_;
goto v_resetjp_2802_;
}
v_resetjp_2802_:
{
lean_object* v___x_2806_; 
if (v_isShared_2804_ == 0)
{
v___x_2806_ = v___x_2803_;
goto v_reusejp_2805_;
}
else
{
lean_object* v_reuseFailAlloc_2807_; 
v_reuseFailAlloc_2807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2807_, 0, v_a_2801_);
v___x_2806_ = v_reuseFailAlloc_2807_;
goto v_reusejp_2805_;
}
v_reusejp_2805_:
{
return v___x_2806_;
}
}
}
else
{
lean_object* v_a_2809_; lean_object* v___x_2811_; uint8_t v_isShared_2812_; uint8_t v_isSharedCheck_2816_; 
v_a_2809_ = lean_ctor_get(v___x_2800_, 0);
v_isSharedCheck_2816_ = !lean_is_exclusive(v___x_2800_);
if (v_isSharedCheck_2816_ == 0)
{
v___x_2811_ = v___x_2800_;
v_isShared_2812_ = v_isSharedCheck_2816_;
goto v_resetjp_2810_;
}
else
{
lean_inc(v_a_2809_);
lean_dec(v___x_2800_);
v___x_2811_ = lean_box(0);
v_isShared_2812_ = v_isSharedCheck_2816_;
goto v_resetjp_2810_;
}
v_resetjp_2810_:
{
lean_object* v___x_2814_; 
if (v_isShared_2812_ == 0)
{
v___x_2814_ = v___x_2811_;
goto v_reusejp_2813_;
}
else
{
lean_object* v_reuseFailAlloc_2815_; 
v_reuseFailAlloc_2815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2815_, 0, v_a_2809_);
v___x_2814_ = v_reuseFailAlloc_2815_;
goto v_reusejp_2813_;
}
v_reusejp_2813_:
{
return v___x_2814_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg___boxed(lean_object* v_perm_2817_, lean_object* v_type_2818_, lean_object* v_k_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_){
_start:
{
lean_object* v_res_2825_; 
v_res_2825_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg(v_perm_2817_, v_type_2818_, v_k_2819_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_);
lean_dec(v___y_2823_);
lean_dec_ref(v___y_2822_);
lean_dec(v___y_2821_);
lean_dec_ref(v___y_2820_);
return v_res_2825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12(lean_object* v_00_u03b1_2826_, lean_object* v_perm_2827_, lean_object* v_type_2828_, lean_object* v_k_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_){
_start:
{
lean_object* v___x_2835_; 
v___x_2835_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg(v_perm_2827_, v_type_2828_, v_k_2829_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_);
return v___x_2835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___boxed(lean_object* v_00_u03b1_2836_, lean_object* v_perm_2837_, lean_object* v_type_2838_, lean_object* v_k_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_){
_start:
{
lean_object* v_res_2845_; 
v_res_2845_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12(v_00_u03b1_2836_, v_perm_2837_, v_type_2838_, v_k_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_);
lean_dec(v___y_2843_);
lean_dec_ref(v___y_2842_);
lean_dec(v___y_2841_);
lean_dec_ref(v___y_2840_);
return v_res_2845_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1(lean_object* v_a_2846_, lean_object* v_fst_2847_, lean_object* v_fst_2848_, lean_object* v___x_2849_, lean_object* v___x_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_){
_start:
{
lean_object* v___x_2856_; 
lean_inc_ref(v_fst_2847_);
v___x_2856_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion(v_a_2846_, v_fst_2847_, v_fst_2848_, v___x_2849_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_);
if (lean_obj_tag(v___x_2856_) == 0)
{
lean_object* v_a_2857_; lean_object* v___x_2859_; uint8_t v_isShared_2860_; uint8_t v_isSharedCheck_2866_; 
v_a_2857_ = lean_ctor_get(v___x_2856_, 0);
v_isSharedCheck_2866_ = !lean_is_exclusive(v___x_2856_);
if (v_isSharedCheck_2866_ == 0)
{
v___x_2859_ = v___x_2856_;
v_isShared_2860_ = v_isSharedCheck_2866_;
goto v_resetjp_2858_;
}
else
{
lean_inc(v_a_2857_);
lean_dec(v___x_2856_);
v___x_2859_ = lean_box(0);
v_isShared_2860_ = v_isSharedCheck_2866_;
goto v_resetjp_2858_;
}
v_resetjp_2858_:
{
lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2864_; 
v___x_2861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2861_, 0, v_a_2857_);
lean_ctor_set(v___x_2861_, 1, v_fst_2847_);
v___x_2862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2862_, 0, v___x_2850_);
lean_ctor_set(v___x_2862_, 1, v___x_2861_);
if (v_isShared_2860_ == 0)
{
lean_ctor_set(v___x_2859_, 0, v___x_2862_);
v___x_2864_ = v___x_2859_;
goto v_reusejp_2863_;
}
else
{
lean_object* v_reuseFailAlloc_2865_; 
v_reuseFailAlloc_2865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2865_, 0, v___x_2862_);
v___x_2864_ = v_reuseFailAlloc_2865_;
goto v_reusejp_2863_;
}
v_reusejp_2863_:
{
return v___x_2864_;
}
}
}
else
{
lean_object* v_a_2867_; lean_object* v___x_2869_; uint8_t v_isShared_2870_; uint8_t v_isSharedCheck_2874_; 
lean_dec_ref(v___x_2850_);
lean_dec_ref(v_fst_2847_);
v_a_2867_ = lean_ctor_get(v___x_2856_, 0);
v_isSharedCheck_2874_ = !lean_is_exclusive(v___x_2856_);
if (v_isSharedCheck_2874_ == 0)
{
v___x_2869_ = v___x_2856_;
v_isShared_2870_ = v_isSharedCheck_2874_;
goto v_resetjp_2868_;
}
else
{
lean_inc(v_a_2867_);
lean_dec(v___x_2856_);
v___x_2869_ = lean_box(0);
v_isShared_2870_ = v_isSharedCheck_2874_;
goto v_resetjp_2868_;
}
v_resetjp_2868_:
{
lean_object* v___x_2872_; 
if (v_isShared_2870_ == 0)
{
v___x_2872_ = v___x_2869_;
goto v_reusejp_2871_;
}
else
{
lean_object* v_reuseFailAlloc_2873_; 
v_reuseFailAlloc_2873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2873_, 0, v_a_2867_);
v___x_2872_ = v_reuseFailAlloc_2873_;
goto v_reusejp_2871_;
}
v_reusejp_2871_:
{
return v___x_2872_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___boxed(lean_object* v_a_2875_, lean_object* v_fst_2876_, lean_object* v_fst_2877_, lean_object* v___x_2878_, lean_object* v___x_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_){
_start:
{
lean_object* v_res_2885_; 
v_res_2885_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1(v_a_2875_, v_fst_2876_, v_fst_2877_, v___x_2878_, v___x_2879_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_);
lean_dec(v___y_2883_);
lean_dec_ref(v___y_2882_);
lean_dec(v___y_2881_);
lean_dec_ref(v___y_2880_);
return v_res_2885_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1(size_t v_sz_2886_, size_t v_i_2887_, lean_object* v_bs_2888_){
_start:
{
uint8_t v___x_2889_; 
v___x_2889_ = lean_usize_dec_lt(v_i_2887_, v_sz_2886_);
if (v___x_2889_ == 0)
{
return v_bs_2888_;
}
else
{
lean_object* v_v_2890_; lean_object* v_recArgPos_2891_; lean_object* v___x_2892_; lean_object* v_bs_x27_2893_; size_t v___x_2894_; size_t v___x_2895_; lean_object* v___x_2896_; 
v_v_2890_ = lean_array_uget_borrowed(v_bs_2888_, v_i_2887_);
v_recArgPos_2891_ = lean_ctor_get(v_v_2890_, 2);
lean_inc(v_recArgPos_2891_);
v___x_2892_ = lean_unsigned_to_nat(0u);
v_bs_x27_2893_ = lean_array_uset(v_bs_2888_, v_i_2887_, v___x_2892_);
v___x_2894_ = ((size_t)1ULL);
v___x_2895_ = lean_usize_add(v_i_2887_, v___x_2894_);
v___x_2896_ = lean_array_uset(v_bs_x27_2893_, v_i_2887_, v_recArgPos_2891_);
v_i_2887_ = v___x_2895_;
v_bs_2888_ = v___x_2896_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1___boxed(lean_object* v_sz_2898_, lean_object* v_i_2899_, lean_object* v_bs_2900_){
_start:
{
size_t v_sz_boxed_2901_; size_t v_i_boxed_2902_; lean_object* v_res_2903_; 
v_sz_boxed_2901_ = lean_unbox_usize(v_sz_2898_);
lean_dec(v_sz_2898_);
v_i_boxed_2902_ = lean_unbox_usize(v_i_2899_);
lean_dec(v_i_2899_);
v_res_2903_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1(v_sz_boxed_2901_, v_i_boxed_2902_, v_bs_2900_);
return v_res_2903_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__11(lean_object* v_as_2904_, size_t v_i_2905_, size_t v_stop_2906_, lean_object* v_b_2907_){
_start:
{
uint8_t v___x_2908_; 
v___x_2908_ = lean_usize_dec_eq(v_i_2905_, v_stop_2906_);
if (v___x_2908_ == 0)
{
lean_object* v___x_2909_; lean_object* v___x_2910_; size_t v___x_2911_; size_t v___x_2912_; 
v___x_2909_ = lean_array_uget_borrowed(v_as_2904_, v_i_2905_);
v___x_2910_ = l_Lean_LocalContext_erase(v_b_2907_, v___x_2909_);
v___x_2911_ = ((size_t)1ULL);
v___x_2912_ = lean_usize_add(v_i_2905_, v___x_2911_);
v_i_2905_ = v___x_2912_;
v_b_2907_ = v___x_2910_;
goto _start;
}
else
{
return v_b_2907_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__11___boxed(lean_object* v_as_2914_, lean_object* v_i_2915_, lean_object* v_stop_2916_, lean_object* v_b_2917_){
_start:
{
size_t v_i_boxed_2918_; size_t v_stop_boxed_2919_; lean_object* v_res_2920_; 
v_i_boxed_2918_ = lean_unbox_usize(v_i_2915_);
lean_dec(v_i_2915_);
v_stop_boxed_2919_ = lean_unbox_usize(v_stop_2916_);
lean_dec(v_stop_2916_);
v_res_2920_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__11(v_as_2914_, v_i_boxed_2918_, v_stop_boxed_2919_, v_b_2917_);
lean_dec_ref(v_as_2914_);
return v_res_2920_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__8_spec__10(lean_object* v_a_2921_, lean_object* v_as_2922_, size_t v_i_2923_, size_t v_stop_2924_){
_start:
{
uint8_t v___x_2925_; 
v___x_2925_ = lean_usize_dec_eq(v_i_2923_, v_stop_2924_);
if (v___x_2925_ == 0)
{
lean_object* v___x_2926_; uint8_t v___x_2927_; 
v___x_2926_ = lean_array_uget_borrowed(v_as_2922_, v_i_2923_);
v___x_2927_ = l_Lean_instBEqFVarId_beq(v_a_2921_, v___x_2926_);
if (v___x_2927_ == 0)
{
size_t v___x_2928_; size_t v___x_2929_; 
v___x_2928_ = ((size_t)1ULL);
v___x_2929_ = lean_usize_add(v_i_2923_, v___x_2928_);
v_i_2923_ = v___x_2929_;
goto _start;
}
else
{
return v___x_2927_;
}
}
else
{
uint8_t v___x_2931_; 
v___x_2931_ = 0;
return v___x_2931_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__8_spec__10___boxed(lean_object* v_a_2932_, lean_object* v_as_2933_, lean_object* v_i_2934_, lean_object* v_stop_2935_){
_start:
{
size_t v_i_boxed_2936_; size_t v_stop_boxed_2937_; uint8_t v_res_2938_; lean_object* v_r_2939_; 
v_i_boxed_2936_ = lean_unbox_usize(v_i_2934_);
lean_dec(v_i_2934_);
v_stop_boxed_2937_ = lean_unbox_usize(v_stop_2935_);
lean_dec(v_stop_2935_);
v_res_2938_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__8_spec__10(v_a_2932_, v_as_2933_, v_i_boxed_2936_, v_stop_boxed_2937_);
lean_dec_ref(v_as_2933_);
lean_dec(v_a_2932_);
v_r_2939_ = lean_box(v_res_2938_);
return v_r_2939_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__8(lean_object* v_as_2940_, lean_object* v_a_2941_){
_start:
{
lean_object* v___x_2942_; lean_object* v___x_2943_; uint8_t v___x_2944_; 
v___x_2942_ = lean_unsigned_to_nat(0u);
v___x_2943_ = lean_array_get_size(v_as_2940_);
v___x_2944_ = lean_nat_dec_lt(v___x_2942_, v___x_2943_);
if (v___x_2944_ == 0)
{
return v___x_2944_;
}
else
{
size_t v___x_2945_; size_t v___x_2946_; uint8_t v___x_2947_; 
v___x_2945_ = ((size_t)0ULL);
v___x_2946_ = lean_usize_of_nat(v___x_2943_);
v___x_2947_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__8_spec__10(v_a_2941_, v_as_2940_, v___x_2945_, v___x_2946_);
return v___x_2947_;
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__8___boxed(lean_object* v_as_2948_, lean_object* v_a_2949_){
_start:
{
uint8_t v_res_2950_; lean_object* v_r_2951_; 
v_res_2950_ = l_Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__8(v_as_2948_, v_a_2949_);
lean_dec(v_a_2949_);
lean_dec_ref(v_as_2948_);
v_r_2951_ = lean_box(v_res_2950_);
return v_r_2951_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__10(lean_object* v_fvarIds_2952_, lean_object* v_as_2953_, size_t v_i_2954_, size_t v_stop_2955_, lean_object* v_b_2956_){
_start:
{
lean_object* v___y_2958_; uint8_t v___x_2962_; 
v___x_2962_ = lean_usize_dec_eq(v_i_2954_, v_stop_2955_);
if (v___x_2962_ == 0)
{
lean_object* v___x_2963_; lean_object* v_fvar_2964_; 
v___x_2963_ = lean_array_uget_borrowed(v_as_2953_, v_i_2954_);
v_fvar_2964_ = lean_ctor_get(v___x_2963_, 1);
if (lean_obj_tag(v_fvar_2964_) == 1)
{
lean_object* v_fvarId_2965_; uint8_t v___x_2966_; 
v_fvarId_2965_ = lean_ctor_get(v_fvar_2964_, 0);
v___x_2966_ = l_Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__8(v_fvarIds_2952_, v_fvarId_2965_);
if (v___x_2966_ == 0)
{
lean_object* v___x_2967_; 
lean_inc(v___x_2963_);
v___x_2967_ = lean_array_push(v_b_2956_, v___x_2963_);
v___y_2958_ = v___x_2967_;
goto v___jp_2957_;
}
else
{
v___y_2958_ = v_b_2956_;
goto v___jp_2957_;
}
}
else
{
lean_object* v___x_2968_; 
lean_inc(v___x_2963_);
v___x_2968_ = lean_array_push(v_b_2956_, v___x_2963_);
v___y_2958_ = v___x_2968_;
goto v___jp_2957_;
}
}
else
{
return v_b_2956_;
}
v___jp_2957_:
{
size_t v___x_2959_; size_t v___x_2960_; 
v___x_2959_ = ((size_t)1ULL);
v___x_2960_ = lean_usize_add(v_i_2954_, v___x_2959_);
v_i_2954_ = v___x_2960_;
v_b_2956_ = v___y_2958_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__10___boxed(lean_object* v_fvarIds_2969_, lean_object* v_as_2970_, lean_object* v_i_2971_, lean_object* v_stop_2972_, lean_object* v_b_2973_){
_start:
{
size_t v_i_boxed_2974_; size_t v_stop_boxed_2975_; lean_object* v_res_2976_; 
v_i_boxed_2974_ = lean_unbox_usize(v_i_2971_);
lean_dec(v_i_2971_);
v_stop_boxed_2975_ = lean_unbox_usize(v_stop_2972_);
lean_dec(v_stop_2972_);
v_res_2976_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__10(v_fvarIds_2969_, v_as_2970_, v_i_boxed_2974_, v_stop_boxed_2975_, v_b_2973_);
lean_dec_ref(v_as_2970_);
lean_dec_ref(v_fvarIds_2969_);
return v_res_2976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__9___redArg(lean_object* v_lctx_2977_, lean_object* v_localInsts_2978_, lean_object* v_x_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_){
_start:
{
lean_object* v___x_2985_; 
v___x_2985_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_2977_, v_localInsts_2978_, v_x_2979_, v___y_2980_, v___y_2981_, v___y_2982_, v___y_2983_);
if (lean_obj_tag(v___x_2985_) == 0)
{
lean_object* v_a_2986_; lean_object* v___x_2988_; uint8_t v_isShared_2989_; uint8_t v_isSharedCheck_2993_; 
v_a_2986_ = lean_ctor_get(v___x_2985_, 0);
v_isSharedCheck_2993_ = !lean_is_exclusive(v___x_2985_);
if (v_isSharedCheck_2993_ == 0)
{
v___x_2988_ = v___x_2985_;
v_isShared_2989_ = v_isSharedCheck_2993_;
goto v_resetjp_2987_;
}
else
{
lean_inc(v_a_2986_);
lean_dec(v___x_2985_);
v___x_2988_ = lean_box(0);
v_isShared_2989_ = v_isSharedCheck_2993_;
goto v_resetjp_2987_;
}
v_resetjp_2987_:
{
lean_object* v___x_2991_; 
if (v_isShared_2989_ == 0)
{
v___x_2991_ = v___x_2988_;
goto v_reusejp_2990_;
}
else
{
lean_object* v_reuseFailAlloc_2992_; 
v_reuseFailAlloc_2992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2992_, 0, v_a_2986_);
v___x_2991_ = v_reuseFailAlloc_2992_;
goto v_reusejp_2990_;
}
v_reusejp_2990_:
{
return v___x_2991_;
}
}
}
else
{
lean_object* v_a_2994_; lean_object* v___x_2996_; uint8_t v_isShared_2997_; uint8_t v_isSharedCheck_3001_; 
v_a_2994_ = lean_ctor_get(v___x_2985_, 0);
v_isSharedCheck_3001_ = !lean_is_exclusive(v___x_2985_);
if (v_isSharedCheck_3001_ == 0)
{
v___x_2996_ = v___x_2985_;
v_isShared_2997_ = v_isSharedCheck_3001_;
goto v_resetjp_2995_;
}
else
{
lean_inc(v_a_2994_);
lean_dec(v___x_2985_);
v___x_2996_ = lean_box(0);
v_isShared_2997_ = v_isSharedCheck_3001_;
goto v_resetjp_2995_;
}
v_resetjp_2995_:
{
lean_object* v___x_2999_; 
if (v_isShared_2997_ == 0)
{
v___x_2999_ = v___x_2996_;
goto v_reusejp_2998_;
}
else
{
lean_object* v_reuseFailAlloc_3000_; 
v_reuseFailAlloc_3000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3000_, 0, v_a_2994_);
v___x_2999_ = v_reuseFailAlloc_3000_;
goto v_reusejp_2998_;
}
v_reusejp_2998_:
{
return v___x_2999_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__9___redArg___boxed(lean_object* v_lctx_3002_, lean_object* v_localInsts_3003_, lean_object* v_x_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_){
_start:
{
lean_object* v_res_3010_; 
v_res_3010_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__9___redArg(v_lctx_3002_, v_localInsts_3003_, v_x_3004_, v___y_3005_, v___y_3006_, v___y_3007_, v___y_3008_);
lean_dec(v___y_3008_);
lean_dec_ref(v___y_3007_);
lean_dec(v___y_3006_);
lean_dec_ref(v___y_3005_);
return v_res_3010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8___redArg(lean_object* v_fvarIds_3013_, lean_object* v_k_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_){
_start:
{
lean_object* v_lctx_3020_; lean_object* v_localInstances_3021_; lean_object* v___y_3023_; lean_object* v___x_3033_; lean_object* v___x_3034_; uint8_t v___x_3035_; 
v_lctx_3020_ = lean_ctor_get(v___y_3015_, 2);
v_localInstances_3021_ = lean_ctor_get(v___y_3015_, 3);
v___x_3033_ = lean_unsigned_to_nat(0u);
v___x_3034_ = lean_array_get_size(v_fvarIds_3013_);
v___x_3035_ = lean_nat_dec_lt(v___x_3033_, v___x_3034_);
if (v___x_3035_ == 0)
{
lean_inc_ref(v_lctx_3020_);
v___y_3023_ = v_lctx_3020_;
goto v___jp_3022_;
}
else
{
size_t v___x_3036_; size_t v___x_3037_; lean_object* v___x_3038_; 
v___x_3036_ = ((size_t)0ULL);
v___x_3037_ = lean_usize_of_nat(v___x_3034_);
lean_inc_ref(v_lctx_3020_);
v___x_3038_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__11(v_fvarIds_3013_, v___x_3036_, v___x_3037_, v_lctx_3020_);
v___y_3023_ = v___x_3038_;
goto v___jp_3022_;
}
v___jp_3022_:
{
lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; uint8_t v___x_3027_; 
v___x_3024_ = lean_unsigned_to_nat(0u);
v___x_3025_ = lean_array_get_size(v_localInstances_3021_);
v___x_3026_ = ((lean_object*)(l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8___redArg___closed__0));
v___x_3027_ = lean_nat_dec_lt(v___x_3024_, v___x_3025_);
if (v___x_3027_ == 0)
{
lean_object* v___x_3028_; 
v___x_3028_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__9___redArg(v___y_3023_, v___x_3026_, v_k_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_);
return v___x_3028_;
}
else
{
size_t v___x_3029_; size_t v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; 
v___x_3029_ = ((size_t)0ULL);
v___x_3030_ = lean_usize_of_nat(v___x_3025_);
v___x_3031_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__10(v_fvarIds_3013_, v_localInstances_3021_, v___x_3029_, v___x_3030_, v___x_3026_);
v___x_3032_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__9___redArg(v___y_3023_, v___x_3031_, v_k_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_);
return v___x_3032_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8___redArg___boxed(lean_object* v_fvarIds_3039_, lean_object* v_k_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_){
_start:
{
lean_object* v_res_3046_; 
v_res_3046_ = l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8___redArg(v_fvarIds_3039_, v_k_3040_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_);
lean_dec(v___y_3044_);
lean_dec_ref(v___y_3043_);
lean_dec(v___y_3042_);
lean_dec_ref(v___y_3041_);
lean_dec_ref(v_fvarIds_3039_);
return v_res_3046_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___closed__1(void){
_start:
{
lean_object* v___x_3048_; lean_object* v___x_3049_; 
v___x_3048_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___closed__0));
v___x_3049_ = l_Lean_stringToMessageData(v___x_3048_);
return v___x_3049_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___closed__3(void){
_start:
{
lean_object* v___x_3051_; lean_object* v___x_3052_; 
v___x_3051_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___closed__2));
v___x_3052_ = l_Lean_stringToMessageData(v___x_3051_);
return v___x_3052_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___closed__5(void){
_start:
{
lean_object* v___x_3054_; lean_object* v___x_3055_; 
v___x_3054_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___closed__4));
v___x_3055_ = l_Lean_stringToMessageData(v___x_3054_);
return v___x_3055_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5(lean_object* v_a_3056_, lean_object* v_as_3057_, size_t v_sz_3058_, size_t v_i_3059_, lean_object* v_b_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_){
_start:
{
lean_object* v_a_3067_; uint8_t v___x_3071_; 
v___x_3071_ = lean_usize_dec_lt(v_i_3059_, v_sz_3058_);
if (v___x_3071_ == 0)
{
lean_object* v___x_3072_; 
lean_dec_ref(v_a_3056_);
v___x_3072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3072_, 0, v_b_3060_);
return v___x_3072_;
}
else
{
lean_object* v___x_3073_; lean_object* v_a_3074_; lean_object* v___x_3075_; 
v___x_3073_ = lean_box(0);
v_a_3074_ = lean_array_uget_borrowed(v_as_3057_, v_i_3059_);
lean_inc(v_a_3074_);
lean_inc_ref(v_a_3056_);
v___x_3075_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg(v_a_3056_, v_a_3074_, v___y_3062_);
if (lean_obj_tag(v___x_3075_) == 0)
{
lean_object* v_a_3076_; uint8_t v___x_3077_; 
v_a_3076_ = lean_ctor_get(v___x_3075_, 0);
lean_inc(v_a_3076_);
lean_dec_ref_known(v___x_3075_, 1);
v___x_3077_ = lean_unbox(v_a_3076_);
lean_dec(v_a_3076_);
if (v___x_3077_ == 0)
{
v_a_3067_ = v___x_3073_;
goto v___jp_3066_;
}
else
{
uint8_t v___x_3078_; 
v___x_3078_ = l_Lean_Expr_isFVarOf(v_a_3056_, v_a_3074_);
if (v___x_3078_ == 0)
{
lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; 
v___x_3079_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___closed__1);
lean_inc_ref(v_a_3056_);
v___x_3080_ = l_Lean_indentExpr(v_a_3056_);
v___x_3081_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3081_, 0, v___x_3079_);
lean_ctor_set(v___x_3081_, 1, v___x_3080_);
v___x_3082_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___closed__3);
v___x_3083_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3083_, 0, v___x_3081_);
lean_ctor_set(v___x_3083_, 1, v___x_3082_);
lean_inc(v_a_3074_);
v___x_3084_ = l_Lean_mkFVar(v_a_3074_);
v___x_3085_ = l_Lean_indentExpr(v___x_3084_);
v___x_3086_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3086_, 0, v___x_3083_);
lean_ctor_set(v___x_3086_, 1, v___x_3085_);
v___x_3087_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___closed__5);
v___x_3088_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3088_, 0, v___x_3086_);
lean_ctor_set(v___x_3088_, 1, v___x_3087_);
v___x_3089_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg(v___x_3088_, v___y_3061_, v___y_3062_, v___y_3063_, v___y_3064_);
if (lean_obj_tag(v___x_3089_) == 0)
{
lean_dec_ref_known(v___x_3089_, 1);
v_a_3067_ = v___x_3073_;
goto v___jp_3066_;
}
else
{
lean_dec_ref(v_a_3056_);
return v___x_3089_;
}
}
else
{
lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; 
v___x_3090_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___closed__1);
lean_inc_ref(v_a_3056_);
v___x_3091_ = l_Lean_indentExpr(v_a_3056_);
v___x_3092_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3092_, 0, v___x_3090_);
lean_ctor_set(v___x_3092_, 1, v___x_3091_);
v___x_3093_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___closed__5);
v___x_3094_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3094_, 0, v___x_3092_);
lean_ctor_set(v___x_3094_, 1, v___x_3093_);
v___x_3095_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg(v___x_3094_, v___y_3061_, v___y_3062_, v___y_3063_, v___y_3064_);
if (lean_obj_tag(v___x_3095_) == 0)
{
lean_dec_ref_known(v___x_3095_, 1);
v_a_3067_ = v___x_3073_;
goto v___jp_3066_;
}
else
{
lean_dec_ref(v_a_3056_);
return v___x_3095_;
}
}
}
}
else
{
lean_object* v_a_3096_; lean_object* v___x_3098_; uint8_t v_isShared_3099_; uint8_t v_isSharedCheck_3103_; 
lean_dec_ref(v_a_3056_);
v_a_3096_ = lean_ctor_get(v___x_3075_, 0);
v_isSharedCheck_3103_ = !lean_is_exclusive(v___x_3075_);
if (v_isSharedCheck_3103_ == 0)
{
v___x_3098_ = v___x_3075_;
v_isShared_3099_ = v_isSharedCheck_3103_;
goto v_resetjp_3097_;
}
else
{
lean_inc(v_a_3096_);
lean_dec(v___x_3075_);
v___x_3098_ = lean_box(0);
v_isShared_3099_ = v_isSharedCheck_3103_;
goto v_resetjp_3097_;
}
v_resetjp_3097_:
{
lean_object* v___x_3101_; 
if (v_isShared_3099_ == 0)
{
v___x_3101_ = v___x_3098_;
goto v_reusejp_3100_;
}
else
{
lean_object* v_reuseFailAlloc_3102_; 
v_reuseFailAlloc_3102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3102_, 0, v_a_3096_);
v___x_3101_ = v_reuseFailAlloc_3102_;
goto v_reusejp_3100_;
}
v_reusejp_3100_:
{
return v___x_3101_;
}
}
}
}
v___jp_3066_:
{
size_t v___x_3068_; size_t v___x_3069_; 
v___x_3068_ = ((size_t)1ULL);
v___x_3069_ = lean_usize_add(v_i_3059_, v___x_3068_);
v_i_3059_ = v___x_3069_;
v_b_3060_ = v_a_3067_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___boxed(lean_object* v_a_3104_, lean_object* v_as_3105_, lean_object* v_sz_3106_, lean_object* v_i_3107_, lean_object* v_b_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_){
_start:
{
size_t v_sz_boxed_3114_; size_t v_i_boxed_3115_; lean_object* v_res_3116_; 
v_sz_boxed_3114_ = lean_unbox_usize(v_sz_3106_);
lean_dec(v_sz_3106_);
v_i_boxed_3115_ = lean_unbox_usize(v_i_3107_);
lean_dec(v_i_3107_);
v_res_3116_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5(v_a_3104_, v_as_3105_, v_sz_boxed_3114_, v_i_boxed_3115_, v_b_3108_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_);
lean_dec(v___y_3112_);
lean_dec_ref(v___y_3111_);
lean_dec(v___y_3110_);
lean_dec_ref(v___y_3109_);
lean_dec_ref(v_as_3105_);
return v_res_3116_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6(lean_object* v_snd_3117_, lean_object* v_as_3118_, size_t v_sz_3119_, size_t v_i_3120_, lean_object* v_b_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_){
_start:
{
uint8_t v___x_3127_; 
v___x_3127_ = lean_usize_dec_lt(v_i_3120_, v_sz_3119_);
if (v___x_3127_ == 0)
{
lean_object* v___x_3128_; 
v___x_3128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3128_, 0, v_b_3121_);
return v___x_3128_;
}
else
{
lean_object* v___x_3129_; lean_object* v_a_3130_; size_t v_sz_3131_; size_t v___x_3132_; lean_object* v___x_3133_; 
v___x_3129_ = lean_box(0);
v_a_3130_ = lean_array_uget_borrowed(v_as_3118_, v_i_3120_);
v_sz_3131_ = lean_array_size(v_snd_3117_);
v___x_3132_ = ((size_t)0ULL);
lean_inc(v_a_3130_);
v___x_3133_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5(v_a_3130_, v_snd_3117_, v_sz_3131_, v___x_3132_, v___x_3129_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_);
if (lean_obj_tag(v___x_3133_) == 0)
{
size_t v___x_3134_; size_t v___x_3135_; 
lean_dec_ref_known(v___x_3133_, 1);
v___x_3134_ = ((size_t)1ULL);
v___x_3135_ = lean_usize_add(v_i_3120_, v___x_3134_);
v_i_3120_ = v___x_3135_;
v_b_3121_ = v___x_3129_;
goto _start;
}
else
{
return v___x_3133_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___boxed(lean_object* v_snd_3137_, lean_object* v_as_3138_, lean_object* v_sz_3139_, lean_object* v_i_3140_, lean_object* v_b_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_){
_start:
{
size_t v_sz_boxed_3147_; size_t v_i_boxed_3148_; lean_object* v_res_3149_; 
v_sz_boxed_3147_ = lean_unbox_usize(v_sz_3139_);
lean_dec(v_sz_3139_);
v_i_boxed_3148_ = lean_unbox_usize(v_i_3140_);
lean_dec(v_i_3140_);
v_res_3149_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6(v_snd_3137_, v_as_3138_, v_sz_boxed_3147_, v_i_boxed_3148_, v_b_3141_, v___y_3142_, v___y_3143_, v___y_3144_, v___y_3145_);
lean_dec(v___y_3145_);
lean_dec_ref(v___y_3144_);
lean_dec(v___y_3143_);
lean_dec_ref(v___y_3142_);
lean_dec_ref(v_as_3138_);
lean_dec_ref(v_snd_3137_);
return v_res_3149_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7(lean_object* v_snd_3150_, lean_object* v_as_3151_, size_t v_sz_3152_, size_t v_i_3153_, lean_object* v_b_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_){
_start:
{
uint8_t v___x_3160_; 
v___x_3160_ = lean_usize_dec_lt(v_i_3153_, v_sz_3152_);
if (v___x_3160_ == 0)
{
lean_object* v___x_3161_; 
v___x_3161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3161_, 0, v_b_3154_);
return v___x_3161_;
}
else
{
lean_object* v_a_3162_; lean_object* v_indGroupInst_3163_; lean_object* v_params_3164_; lean_object* v___x_3165_; size_t v_sz_3166_; size_t v___x_3167_; lean_object* v___x_3168_; 
v_a_3162_ = lean_array_uget_borrowed(v_as_3151_, v_i_3153_);
v_indGroupInst_3163_ = lean_ctor_get(v_a_3162_, 4);
v_params_3164_ = lean_ctor_get(v_indGroupInst_3163_, 2);
v___x_3165_ = lean_box(0);
v_sz_3166_ = lean_array_size(v_params_3164_);
v___x_3167_ = ((size_t)0ULL);
v___x_3168_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6(v_snd_3150_, v_params_3164_, v_sz_3166_, v___x_3167_, v___x_3165_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_);
if (lean_obj_tag(v___x_3168_) == 0)
{
size_t v___x_3169_; size_t v___x_3170_; 
lean_dec_ref_known(v___x_3168_, 1);
v___x_3169_ = ((size_t)1ULL);
v___x_3170_ = lean_usize_add(v_i_3153_, v___x_3169_);
v_i_3153_ = v___x_3170_;
v_b_3154_ = v___x_3165_;
goto _start;
}
else
{
return v___x_3168_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7___boxed(lean_object* v_snd_3172_, lean_object* v_as_3173_, lean_object* v_sz_3174_, lean_object* v_i_3175_, lean_object* v_b_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_){
_start:
{
size_t v_sz_boxed_3182_; size_t v_i_boxed_3183_; lean_object* v_res_3184_; 
v_sz_boxed_3182_ = lean_unbox_usize(v_sz_3174_);
lean_dec(v_sz_3174_);
v_i_boxed_3183_ = lean_unbox_usize(v_i_3175_);
lean_dec(v_i_3175_);
v_res_3184_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7(v_snd_3172_, v_as_3173_, v_sz_boxed_3182_, v_i_boxed_3183_, v_b_3176_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_);
lean_dec(v___y_3180_);
lean_dec_ref(v___y_3179_);
lean_dec(v___y_3178_);
lean_dec_ref(v___y_3177_);
lean_dec_ref(v_as_3173_);
lean_dec_ref(v_snd_3172_);
return v_res_3184_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__3___redArg(lean_object* v_fst_3185_, size_t v_sz_3186_, size_t v_i_3187_, lean_object* v_bs_3188_){
_start:
{
uint8_t v___x_3189_; 
v___x_3189_ = lean_usize_dec_lt(v_i_3187_, v_sz_3186_);
if (v___x_3189_ == 0)
{
return v_bs_3188_;
}
else
{
lean_object* v_v_3190_; lean_object* v_fnName_3191_; lean_object* v_recArgPos_3192_; lean_object* v_indicesPos_3193_; lean_object* v_indGroupInst_3194_; lean_object* v_indIdx_3195_; lean_object* v___x_3197_; uint8_t v_isShared_3198_; uint8_t v_isSharedCheck_3212_; 
v_v_3190_ = lean_array_uget(v_bs_3188_, v_i_3187_);
v_fnName_3191_ = lean_ctor_get(v_v_3190_, 0);
v_recArgPos_3192_ = lean_ctor_get(v_v_3190_, 2);
v_indicesPos_3193_ = lean_ctor_get(v_v_3190_, 3);
v_indGroupInst_3194_ = lean_ctor_get(v_v_3190_, 4);
v_indIdx_3195_ = lean_ctor_get(v_v_3190_, 5);
v_isSharedCheck_3212_ = !lean_is_exclusive(v_v_3190_);
if (v_isSharedCheck_3212_ == 0)
{
lean_object* v_unused_3213_; 
v_unused_3213_ = lean_ctor_get(v_v_3190_, 1);
lean_dec(v_unused_3213_);
v___x_3197_ = v_v_3190_;
v_isShared_3198_ = v_isSharedCheck_3212_;
goto v_resetjp_3196_;
}
else
{
lean_inc(v_indIdx_3195_);
lean_inc(v_indGroupInst_3194_);
lean_inc(v_indicesPos_3193_);
lean_inc(v_recArgPos_3192_);
lean_inc(v_fnName_3191_);
lean_dec(v_v_3190_);
v___x_3197_ = lean_box(0);
v_isShared_3198_ = v_isSharedCheck_3212_;
goto v_resetjp_3196_;
}
v_resetjp_3196_:
{
lean_object* v_perms_3199_; lean_object* v___x_3200_; lean_object* v_bs_x27_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3206_; 
v_perms_3199_ = lean_ctor_get(v_fst_3185_, 1);
v___x_3200_ = lean_unsigned_to_nat(0u);
v_bs_x27_3201_ = lean_array_uset(v_bs_3188_, v_i_3187_, v___x_3200_);
v___x_3202_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0);
v___x_3203_ = lean_usize_to_nat(v_i_3187_);
v___x_3204_ = lean_array_get_borrowed(v___x_3202_, v_perms_3199_, v___x_3203_);
lean_dec(v___x_3203_);
lean_inc(v___x_3204_);
if (v_isShared_3198_ == 0)
{
lean_ctor_set(v___x_3197_, 1, v___x_3204_);
v___x_3206_ = v___x_3197_;
goto v_reusejp_3205_;
}
else
{
lean_object* v_reuseFailAlloc_3211_; 
v_reuseFailAlloc_3211_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3211_, 0, v_fnName_3191_);
lean_ctor_set(v_reuseFailAlloc_3211_, 1, v___x_3204_);
lean_ctor_set(v_reuseFailAlloc_3211_, 2, v_recArgPos_3192_);
lean_ctor_set(v_reuseFailAlloc_3211_, 3, v_indicesPos_3193_);
lean_ctor_set(v_reuseFailAlloc_3211_, 4, v_indGroupInst_3194_);
lean_ctor_set(v_reuseFailAlloc_3211_, 5, v_indIdx_3195_);
v___x_3206_ = v_reuseFailAlloc_3211_;
goto v_reusejp_3205_;
}
v_reusejp_3205_:
{
size_t v___x_3207_; size_t v___x_3208_; lean_object* v___x_3209_; 
v___x_3207_ = ((size_t)1ULL);
v___x_3208_ = lean_usize_add(v_i_3187_, v___x_3207_);
v___x_3209_ = lean_array_uset(v_bs_x27_3201_, v_i_3187_, v___x_3206_);
v_i_3187_ = v___x_3208_;
v_bs_3188_ = v___x_3209_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__3___redArg___boxed(lean_object* v_fst_3214_, lean_object* v_sz_3215_, lean_object* v_i_3216_, lean_object* v_bs_3217_){
_start:
{
size_t v_sz_boxed_3218_; size_t v_i_boxed_3219_; lean_object* v_res_3220_; 
v_sz_boxed_3218_ = lean_unbox_usize(v_sz_3215_);
lean_dec(v_sz_3215_);
v_i_boxed_3219_ = lean_unbox_usize(v_i_3216_);
lean_dec(v_i_3216_);
v_res_3220_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__3___redArg(v_fst_3214_, v_sz_boxed_3218_, v_i_boxed_3219_, v_bs_3217_);
lean_dec_ref(v_fst_3214_);
return v_res_3220_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__13_spec__16_spec__20(lean_object* v_x_3221_, lean_object* v_x_3222_, lean_object* v_x_3223_){
_start:
{
if (lean_obj_tag(v_x_3223_) == 0)
{
lean_dec(v_x_3221_);
return v_x_3222_;
}
else
{
lean_object* v_head_3224_; lean_object* v_tail_3225_; lean_object* v___x_3227_; uint8_t v_isShared_3228_; uint8_t v_isSharedCheck_3235_; 
v_head_3224_ = lean_ctor_get(v_x_3223_, 0);
v_tail_3225_ = lean_ctor_get(v_x_3223_, 1);
v_isSharedCheck_3235_ = !lean_is_exclusive(v_x_3223_);
if (v_isSharedCheck_3235_ == 0)
{
v___x_3227_ = v_x_3223_;
v_isShared_3228_ = v_isSharedCheck_3235_;
goto v_resetjp_3226_;
}
else
{
lean_inc(v_tail_3225_);
lean_inc(v_head_3224_);
lean_dec(v_x_3223_);
v___x_3227_ = lean_box(0);
v_isShared_3228_ = v_isSharedCheck_3235_;
goto v_resetjp_3226_;
}
v_resetjp_3226_:
{
lean_object* v___x_3230_; 
lean_inc(v_x_3221_);
if (v_isShared_3228_ == 0)
{
lean_ctor_set_tag(v___x_3227_, 5);
lean_ctor_set(v___x_3227_, 1, v_x_3221_);
lean_ctor_set(v___x_3227_, 0, v_x_3222_);
v___x_3230_ = v___x_3227_;
goto v_reusejp_3229_;
}
else
{
lean_object* v_reuseFailAlloc_3234_; 
v_reuseFailAlloc_3234_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3234_, 0, v_x_3222_);
lean_ctor_set(v_reuseFailAlloc_3234_, 1, v_x_3221_);
v___x_3230_ = v_reuseFailAlloc_3234_;
goto v_reusejp_3229_;
}
v_reusejp_3229_:
{
lean_object* v___x_3231_; lean_object* v___x_3232_; 
v___x_3231_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(v_head_3224_);
v___x_3232_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3232_, 0, v___x_3230_);
lean_ctor_set(v___x_3232_, 1, v___x_3231_);
v_x_3222_ = v___x_3232_;
v_x_3223_ = v_tail_3225_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__13_spec__16(lean_object* v_x_3236_, lean_object* v_x_3237_, lean_object* v_x_3238_){
_start:
{
if (lean_obj_tag(v_x_3238_) == 0)
{
lean_dec(v_x_3236_);
return v_x_3237_;
}
else
{
lean_object* v_head_3239_; lean_object* v_tail_3240_; lean_object* v___x_3242_; uint8_t v_isShared_3243_; uint8_t v_isSharedCheck_3250_; 
v_head_3239_ = lean_ctor_get(v_x_3238_, 0);
v_tail_3240_ = lean_ctor_get(v_x_3238_, 1);
v_isSharedCheck_3250_ = !lean_is_exclusive(v_x_3238_);
if (v_isSharedCheck_3250_ == 0)
{
v___x_3242_ = v_x_3238_;
v_isShared_3243_ = v_isSharedCheck_3250_;
goto v_resetjp_3241_;
}
else
{
lean_inc(v_tail_3240_);
lean_inc(v_head_3239_);
lean_dec(v_x_3238_);
v___x_3242_ = lean_box(0);
v_isShared_3243_ = v_isSharedCheck_3250_;
goto v_resetjp_3241_;
}
v_resetjp_3241_:
{
lean_object* v___x_3245_; 
lean_inc(v_x_3236_);
if (v_isShared_3243_ == 0)
{
lean_ctor_set_tag(v___x_3242_, 5);
lean_ctor_set(v___x_3242_, 1, v_x_3236_);
lean_ctor_set(v___x_3242_, 0, v_x_3237_);
v___x_3245_ = v___x_3242_;
goto v_reusejp_3244_;
}
else
{
lean_object* v_reuseFailAlloc_3249_; 
v_reuseFailAlloc_3249_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3249_, 0, v_x_3237_);
lean_ctor_set(v_reuseFailAlloc_3249_, 1, v_x_3236_);
v___x_3245_ = v_reuseFailAlloc_3249_;
goto v_reusejp_3244_;
}
v_reusejp_3244_:
{
lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; 
v___x_3246_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(v_head_3239_);
v___x_3247_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3247_, 0, v___x_3245_);
lean_ctor_set(v___x_3247_, 1, v___x_3246_);
v___x_3248_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__13_spec__16_spec__20(v_x_3236_, v___x_3247_, v_tail_3240_);
return v___x_3248_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__13(lean_object* v_x_3251_, lean_object* v_x_3252_){
_start:
{
if (lean_obj_tag(v_x_3251_) == 0)
{
lean_object* v___x_3253_; 
lean_dec(v_x_3252_);
v___x_3253_ = lean_box(0);
return v___x_3253_;
}
else
{
lean_object* v_tail_3254_; 
v_tail_3254_ = lean_ctor_get(v_x_3251_, 1);
if (lean_obj_tag(v_tail_3254_) == 0)
{
lean_object* v_head_3255_; lean_object* v___x_3256_; 
lean_dec(v_x_3252_);
v_head_3255_ = lean_ctor_get(v_x_3251_, 0);
lean_inc(v_head_3255_);
lean_dec_ref_known(v_x_3251_, 2);
v___x_3256_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(v_head_3255_);
return v___x_3256_;
}
else
{
lean_object* v_head_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; 
lean_inc(v_tail_3254_);
v_head_3257_ = lean_ctor_get(v_x_3251_, 0);
lean_inc(v_head_3257_);
lean_dec_ref_known(v_x_3251_, 2);
v___x_3258_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(v_head_3257_);
v___x_3259_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__13_spec__16(v_x_3252_, v___x_3258_, v_tail_3254_);
return v___x_3259_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___closed__5(void){
_start:
{
lean_object* v___x_3268_; lean_object* v___x_3269_; 
v___x_3268_ = ((lean_object*)(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___closed__0));
v___x_3269_ = lean_string_length(v___x_3268_);
return v___x_3269_;
}
}
static lean_object* _init_l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___closed__6(void){
_start:
{
lean_object* v___x_3270_; lean_object* v___x_3271_; 
v___x_3270_ = lean_obj_once(&l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___closed__5, &l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___closed__5_once, _init_l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___closed__5);
v___x_3271_ = lean_nat_to_int(v___x_3270_);
return v___x_3271_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9(lean_object* v_xs_3279_){
_start:
{
lean_object* v___x_3280_; lean_object* v___x_3281_; uint8_t v___x_3282_; 
v___x_3280_ = lean_array_get_size(v_xs_3279_);
v___x_3281_ = lean_unsigned_to_nat(0u);
v___x_3282_ = lean_nat_dec_eq(v___x_3280_, v___x_3281_);
if (v___x_3282_ == 0)
{
lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; 
v___x_3283_ = lean_array_to_list(v_xs_3279_);
v___x_3284_ = ((lean_object*)(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___closed__3));
v___x_3285_ = l_Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__13(v___x_3283_, v___x_3284_);
v___x_3286_ = lean_obj_once(&l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___closed__6, &l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___closed__6_once, _init_l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___closed__6);
v___x_3287_ = ((lean_object*)(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___closed__7));
v___x_3288_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3288_, 0, v___x_3287_);
lean_ctor_set(v___x_3288_, 1, v___x_3285_);
v___x_3289_ = ((lean_object*)(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___closed__8));
v___x_3290_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3290_, 0, v___x_3288_);
lean_ctor_set(v___x_3290_, 1, v___x_3289_);
v___x_3291_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3291_, 0, v___x_3286_);
lean_ctor_set(v___x_3291_, 1, v___x_3290_);
v___x_3292_ = l_Std_Format_fill(v___x_3291_);
return v___x_3292_;
}
else
{
lean_object* v___x_3293_; 
lean_dec_ref(v_xs_3279_);
v___x_3293_ = ((lean_object*)(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___closed__10));
return v___x_3293_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10(size_t v_sz_3294_, size_t v_i_3295_, lean_object* v_bs_3296_){
_start:
{
uint8_t v___x_3297_; 
v___x_3297_ = lean_usize_dec_lt(v_i_3295_, v_sz_3294_);
if (v___x_3297_ == 0)
{
return v_bs_3296_;
}
else
{
lean_object* v_v_3298_; lean_object* v___x_3299_; lean_object* v_bs_x27_3300_; lean_object* v___x_3301_; size_t v___x_3302_; size_t v___x_3303_; lean_object* v___x_3304_; 
v_v_3298_ = lean_array_uget(v_bs_3296_, v_i_3295_);
v___x_3299_ = lean_unsigned_to_nat(0u);
v_bs_x27_3300_ = lean_array_uset(v_bs_3296_, v_i_3295_, v___x_3299_);
v___x_3301_ = l_Lean_mkFVar(v_v_3298_);
v___x_3302_ = ((size_t)1ULL);
v___x_3303_ = lean_usize_add(v_i_3295_, v___x_3302_);
v___x_3304_ = lean_array_uset(v_bs_x27_3300_, v_i_3295_, v___x_3301_);
v_i_3295_ = v___x_3303_;
v_bs_3296_ = v___x_3304_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___boxed(lean_object* v_sz_3306_, lean_object* v_i_3307_, lean_object* v_bs_3308_){
_start:
{
size_t v_sz_boxed_3309_; size_t v_i_boxed_3310_; lean_object* v_res_3311_; 
v_sz_boxed_3309_ = lean_unbox_usize(v_sz_3306_);
lean_dec(v_sz_3306_);
v_i_boxed_3310_ = lean_unbox_usize(v_i_3307_);
lean_dec(v_i_3307_);
v_res_3311_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10(v_sz_boxed_3309_, v_i_boxed_3310_, v_bs_3308_);
return v_res_3311_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__2(size_t v_sz_3312_, size_t v_i_3313_, lean_object* v_bs_3314_){
_start:
{
uint8_t v___x_3315_; 
v___x_3315_ = lean_usize_dec_lt(v_i_3313_, v_sz_3312_);
if (v___x_3315_ == 0)
{
return v_bs_3314_;
}
else
{
lean_object* v_v_3316_; lean_object* v___x_3317_; lean_object* v_bs_x27_3318_; lean_object* v___x_3319_; size_t v___x_3320_; size_t v___x_3321_; lean_object* v___x_3322_; 
v_v_3316_ = lean_array_uget(v_bs_3314_, v_i_3313_);
v___x_3317_ = lean_unsigned_to_nat(0u);
v_bs_x27_3318_ = lean_array_uset(v_bs_3314_, v_i_3313_, v___x_3317_);
v___x_3319_ = l_Lean_Elab_Structural_RecArgInfo_indicesAndRecArgPos(v_v_3316_);
v___x_3320_ = ((size_t)1ULL);
v___x_3321_ = lean_usize_add(v_i_3313_, v___x_3320_);
v___x_3322_ = lean_array_uset(v_bs_x27_3318_, v_i_3313_, v___x_3319_);
v_i_3313_ = v___x_3321_;
v_bs_3314_ = v___x_3322_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__2___boxed(lean_object* v_sz_3324_, lean_object* v_i_3325_, lean_object* v_bs_3326_){
_start:
{
size_t v_sz_boxed_3327_; size_t v_i_boxed_3328_; lean_object* v_res_3329_; 
v_sz_boxed_3327_ = lean_unbox_usize(v_sz_3324_);
lean_dec(v_sz_3324_);
v_i_boxed_3328_ = lean_unbox_usize(v_i_3325_);
lean_dec(v_i_3325_);
v_res_3329_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__2(v_sz_boxed_3327_, v_i_boxed_3328_, v_bs_3326_);
return v_res_3329_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__0(void){
_start:
{
lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; 
v___x_3330_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__5));
v___x_3331_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___closed__1));
v___x_3332_ = l_Lean_Name_append(v___x_3331_, v___x_3330_);
return v___x_3332_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3334_; lean_object* v___x_3335_; 
v___x_3334_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__1));
v___x_3335_ = l_Lean_stringToMessageData(v___x_3334_);
return v___x_3335_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__4(void){
_start:
{
lean_object* v___x_3337_; lean_object* v___x_3338_; 
v___x_3337_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__3));
v___x_3338_ = l_Lean_stringToMessageData(v___x_3337_);
return v___x_3338_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__6(void){
_start:
{
lean_object* v___x_3340_; lean_object* v___x_3341_; 
v___x_3340_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__5));
v___x_3341_ = l_Lean_stringToMessageData(v___x_3340_);
return v___x_3341_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__8(void){
_start:
{
lean_object* v___x_3343_; lean_object* v___x_3344_; 
v___x_3343_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__7));
v___x_3344_ = l_Lean_stringToMessageData(v___x_3343_);
return v___x_3344_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__10(void){
_start:
{
lean_object* v___x_3346_; lean_object* v___x_3347_; 
v___x_3346_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__9));
v___x_3347_ = l_Lean_stringToMessageData(v___x_3346_);
return v___x_3347_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0(size_t v___x_3348_, lean_object* v_a_3349_, lean_object* v_xs_3350_, lean_object* v_a_3351_, lean_object* v_recArgInfos_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_){
_start:
{
lean_object* v___y_3359_; lean_object* v___y_3360_; lean_object* v___y_3361_; lean_object* v___y_3362_; lean_object* v___y_3363_; lean_object* v___y_3364_; lean_object* v___y_3365_; size_t v_sz_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___y_3382_; lean_object* v___y_3383_; lean_object* v___y_3384_; lean_object* v___y_3385_; lean_object* v___y_3386_; lean_object* v___y_3387_; lean_object* v___y_3388_; lean_object* v___x_3465_; lean_object* v_a_3466_; uint8_t v___x_3467_; 
v_sz_3378_ = lean_array_size(v_recArgInfos_3352_);
lean_inc_ref(v_recArgInfos_3352_);
v___x_3379_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1(v_sz_3378_, v___x_3348_, v_recArgInfos_3352_);
v___x_3380_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__5));
v___x_3465_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1(v___x_3380_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_);
v_a_3466_ = lean_ctor_get(v___x_3465_, 0);
lean_inc(v_a_3466_);
lean_dec_ref(v___x_3465_);
v___x_3467_ = lean_unbox(v_a_3466_);
lean_dec(v_a_3466_);
if (v___x_3467_ == 0)
{
goto v___jp_3408_;
}
else
{
lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; 
v___x_3468_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__10, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__10);
lean_inc_ref(v___x_3379_);
v___x_3469_ = lean_array_to_list(v___x_3379_);
v___x_3470_ = lean_box(0);
v___x_3471_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__0(v___x_3469_, v___x_3470_);
v___x_3472_ = l_Lean_MessageData_ofList(v___x_3471_);
v___x_3473_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3473_, 0, v___x_3468_);
lean_ctor_set(v___x_3473_, 1, v___x_3472_);
v___x_3474_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_3380_, v___x_3473_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_);
if (lean_obj_tag(v___x_3474_) == 0)
{
lean_dec_ref_known(v___x_3474_, 1);
goto v___jp_3408_;
}
else
{
lean_object* v_a_3475_; lean_object* v___x_3477_; uint8_t v_isShared_3478_; uint8_t v_isSharedCheck_3482_; 
lean_dec_ref(v___x_3379_);
lean_dec_ref(v_recArgInfos_3352_);
lean_dec_ref(v_a_3351_);
lean_dec_ref(v_xs_3350_);
lean_dec_ref(v_a_3349_);
v_a_3475_ = lean_ctor_get(v___x_3474_, 0);
v_isSharedCheck_3482_ = !lean_is_exclusive(v___x_3474_);
if (v_isSharedCheck_3482_ == 0)
{
v___x_3477_ = v___x_3474_;
v_isShared_3478_ = v_isSharedCheck_3482_;
goto v_resetjp_3476_;
}
else
{
lean_inc(v_a_3475_);
lean_dec(v___x_3474_);
v___x_3477_ = lean_box(0);
v_isShared_3478_ = v_isSharedCheck_3482_;
goto v_resetjp_3476_;
}
v_resetjp_3476_:
{
lean_object* v___x_3480_; 
if (v_isShared_3478_ == 0)
{
v___x_3480_ = v___x_3477_;
goto v_reusejp_3479_;
}
else
{
lean_object* v_reuseFailAlloc_3481_; 
v_reuseFailAlloc_3481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3481_, 0, v_a_3475_);
v___x_3480_ = v_reuseFailAlloc_3481_;
goto v_reusejp_3479_;
}
v_reusejp_3479_:
{
return v___x_3480_;
}
}
}
}
v___jp_3358_:
{
lean_object* v___x_3366_; size_t v_sz_3367_; lean_object* v___x_3368_; 
v___x_3366_ = lean_box(0);
v_sz_3367_ = lean_array_size(v___y_3360_);
v___x_3368_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7(v___y_3359_, v___y_3360_, v_sz_3367_, v___x_3348_, v___x_3366_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_);
lean_dec_ref(v___y_3360_);
if (lean_obj_tag(v___x_3368_) == 0)
{
lean_object* v___x_3369_; 
lean_dec_ref_known(v___x_3368_, 1);
v___x_3369_ = l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8___redArg(v___y_3359_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_);
lean_dec_ref(v___y_3359_);
return v___x_3369_;
}
else
{
lean_object* v_a_3370_; lean_object* v___x_3372_; uint8_t v_isShared_3373_; uint8_t v_isSharedCheck_3377_; 
lean_dec_ref(v___y_3361_);
lean_dec_ref(v___y_3359_);
v_a_3370_ = lean_ctor_get(v___x_3368_, 0);
v_isSharedCheck_3377_ = !lean_is_exclusive(v___x_3368_);
if (v_isSharedCheck_3377_ == 0)
{
v___x_3372_ = v___x_3368_;
v_isShared_3373_ = v_isSharedCheck_3377_;
goto v_resetjp_3371_;
}
else
{
lean_inc(v_a_3370_);
lean_dec(v___x_3368_);
v___x_3372_ = lean_box(0);
v_isShared_3373_ = v_isSharedCheck_3377_;
goto v_resetjp_3371_;
}
v_resetjp_3371_:
{
lean_object* v___x_3375_; 
if (v_isShared_3373_ == 0)
{
v___x_3375_ = v___x_3372_;
goto v_reusejp_3374_;
}
else
{
lean_object* v_reuseFailAlloc_3376_; 
v_reuseFailAlloc_3376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3376_, 0, v_a_3370_);
v___x_3375_ = v_reuseFailAlloc_3376_;
goto v_reusejp_3374_;
}
v_reusejp_3374_:
{
return v___x_3375_;
}
}
}
}
v___jp_3381_:
{
lean_object* v_toCold_3389_; lean_object* v_options_3390_; uint8_t v_hasTrace_3391_; 
v_toCold_3389_ = lean_ctor_get(v___y_3387_, 0);
v_options_3390_ = lean_ctor_get(v_toCold_3389_, 2);
v_hasTrace_3391_ = lean_ctor_get_uint8(v_options_3390_, sizeof(void*)*1);
if (v_hasTrace_3391_ == 0)
{
v___y_3359_ = v___y_3383_;
v___y_3360_ = v___y_3382_;
v___y_3361_ = v___y_3384_;
v___y_3362_ = v___y_3385_;
v___y_3363_ = v___y_3386_;
v___y_3364_ = v___y_3387_;
v___y_3365_ = v___y_3388_;
goto v___jp_3358_;
}
else
{
lean_object* v_inheritedTraceOptions_3392_; lean_object* v___x_3393_; uint8_t v___x_3394_; 
v_inheritedTraceOptions_3392_ = lean_ctor_get(v_toCold_3389_, 11);
v___x_3393_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__0);
v___x_3394_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3392_, v_options_3390_, v___x_3393_);
if (v___x_3394_ == 0)
{
v___y_3359_ = v___y_3383_;
v___y_3360_ = v___y_3382_;
v___y_3361_ = v___y_3384_;
v___y_3362_ = v___y_3385_;
v___y_3363_ = v___y_3386_;
v___y_3364_ = v___y_3387_;
v___y_3365_ = v___y_3388_;
goto v___jp_3358_;
}
else
{
lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; 
v___x_3395_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__2);
lean_inc_ref(v___y_3382_);
v___x_3396_ = l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9(v___y_3382_);
v___x_3397_ = l_Lean_MessageData_ofFormat(v___x_3396_);
v___x_3398_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3398_, 0, v___x_3395_);
lean_ctor_set(v___x_3398_, 1, v___x_3397_);
v___x_3399_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_3380_, v___x_3398_, v___y_3385_, v___y_3386_, v___y_3387_, v___y_3388_);
if (lean_obj_tag(v___x_3399_) == 0)
{
lean_dec_ref_known(v___x_3399_, 1);
v___y_3359_ = v___y_3383_;
v___y_3360_ = v___y_3382_;
v___y_3361_ = v___y_3384_;
v___y_3362_ = v___y_3385_;
v___y_3363_ = v___y_3386_;
v___y_3364_ = v___y_3387_;
v___y_3365_ = v___y_3388_;
goto v___jp_3358_;
}
else
{
lean_object* v_a_3400_; lean_object* v___x_3402_; uint8_t v_isShared_3403_; uint8_t v_isSharedCheck_3407_; 
lean_dec_ref(v___y_3384_);
lean_dec_ref(v___y_3383_);
lean_dec_ref(v___y_3382_);
v_a_3400_ = lean_ctor_get(v___x_3399_, 0);
v_isSharedCheck_3407_ = !lean_is_exclusive(v___x_3399_);
if (v_isSharedCheck_3407_ == 0)
{
v___x_3402_ = v___x_3399_;
v_isShared_3403_ = v_isSharedCheck_3407_;
goto v_resetjp_3401_;
}
else
{
lean_inc(v_a_3400_);
lean_dec(v___x_3399_);
v___x_3402_ = lean_box(0);
v_isShared_3403_ = v_isSharedCheck_3407_;
goto v_resetjp_3401_;
}
v_resetjp_3401_:
{
lean_object* v___x_3405_; 
if (v_isShared_3403_ == 0)
{
v___x_3405_ = v___x_3402_;
goto v_reusejp_3404_;
}
else
{
lean_object* v_reuseFailAlloc_3406_; 
v_reuseFailAlloc_3406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3406_, 0, v_a_3400_);
v___x_3405_ = v_reuseFailAlloc_3406_;
goto v_reusejp_3404_;
}
v_reusejp_3404_:
{
return v___x_3405_;
}
}
}
}
}
}
v___jp_3408_:
{
lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v_snd_3411_; lean_object* v_fst_3412_; lean_object* v___x_3414_; uint8_t v_isShared_3415_; uint8_t v_isSharedCheck_3464_; 
lean_inc_ref(v_recArgInfos_3352_);
v___x_3409_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__2(v_sz_3378_, v___x_3348_, v_recArgInfos_3352_);
lean_inc_ref(v_xs_3350_);
v___x_3410_ = l_Lean_Elab_FixedParamPerms_erase(v_a_3349_, v_xs_3350_, v___x_3409_);
v_snd_3411_ = lean_ctor_get(v___x_3410_, 1);
v_fst_3412_ = lean_ctor_get(v___x_3410_, 0);
v_isSharedCheck_3464_ = !lean_is_exclusive(v___x_3410_);
if (v_isSharedCheck_3464_ == 0)
{
v___x_3414_ = v___x_3410_;
v_isShared_3415_ = v_isSharedCheck_3464_;
goto v_resetjp_3413_;
}
else
{
lean_inc(v_snd_3411_);
lean_inc(v_fst_3412_);
lean_dec(v___x_3410_);
v___x_3414_ = lean_box(0);
v_isShared_3415_ = v_isSharedCheck_3464_;
goto v_resetjp_3413_;
}
v_resetjp_3413_:
{
lean_object* v_fst_3416_; lean_object* v_snd_3417_; lean_object* v___x_3419_; uint8_t v_isShared_3420_; uint8_t v_isSharedCheck_3463_; 
v_fst_3416_ = lean_ctor_get(v_snd_3411_, 0);
v_snd_3417_ = lean_ctor_get(v_snd_3411_, 1);
v_isSharedCheck_3463_ = !lean_is_exclusive(v_snd_3411_);
if (v_isSharedCheck_3463_ == 0)
{
v___x_3419_ = v_snd_3411_;
v_isShared_3420_ = v_isSharedCheck_3463_;
goto v_resetjp_3418_;
}
else
{
lean_inc(v_snd_3417_);
lean_inc(v_fst_3416_);
lean_dec(v_snd_3411_);
v___x_3419_ = lean_box(0);
v_isShared_3420_ = v_isSharedCheck_3463_;
goto v_resetjp_3418_;
}
v_resetjp_3418_:
{
lean_object* v___x_3421_; lean_object* v___f_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; uint8_t v___x_3425_; 
v___x_3421_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__3___redArg(v_fst_3412_, v_sz_3378_, v___x_3348_, v_recArgInfos_3352_);
lean_inc_ref(v___x_3421_);
lean_inc(v_fst_3416_);
v___f_3422_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___boxed), 10, 5);
lean_closure_set(v___f_3422_, 0, v_a_3351_);
lean_closure_set(v___f_3422_, 1, v_fst_3412_);
lean_closure_set(v___f_3422_, 2, v_fst_3416_);
lean_closure_set(v___f_3422_, 3, v___x_3421_);
lean_closure_set(v___f_3422_, 4, v___x_3379_);
v___x_3423_ = lean_array_get_size(v_fst_3416_);
v___x_3424_ = lean_array_get_size(v_xs_3350_);
v___x_3425_ = lean_nat_dec_eq(v___x_3423_, v___x_3424_);
if (v___x_3425_ == 0)
{
lean_object* v___x_3426_; lean_object* v_a_3427_; uint8_t v___x_3428_; 
v___x_3426_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1(v___x_3380_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_);
v_a_3427_ = lean_ctor_get(v___x_3426_, 0);
lean_inc(v_a_3427_);
lean_dec_ref(v___x_3426_);
v___x_3428_ = lean_unbox(v_a_3427_);
lean_dec(v_a_3427_);
if (v___x_3428_ == 0)
{
lean_del_object(v___x_3419_);
lean_dec(v_fst_3416_);
lean_del_object(v___x_3414_);
lean_dec_ref(v_xs_3350_);
v___y_3382_ = v___x_3421_;
v___y_3383_ = v_snd_3417_;
v___y_3384_ = v___f_3422_;
v___y_3385_ = v___y_3353_;
v___y_3386_ = v___y_3354_;
v___y_3387_ = v___y_3355_;
v___y_3388_ = v___y_3356_;
goto v___jp_3381_;
}
else
{
lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3435_; 
v___x_3429_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__4);
v___x_3430_ = lean_array_to_list(v_xs_3350_);
v___x_3431_ = lean_box(0);
v___x_3432_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_3430_, v___x_3431_);
v___x_3433_ = l_Lean_MessageData_ofList(v___x_3432_);
if (v_isShared_3420_ == 0)
{
lean_ctor_set_tag(v___x_3419_, 7);
lean_ctor_set(v___x_3419_, 1, v___x_3433_);
lean_ctor_set(v___x_3419_, 0, v___x_3429_);
v___x_3435_ = v___x_3419_;
goto v_reusejp_3434_;
}
else
{
lean_object* v_reuseFailAlloc_3461_; 
v_reuseFailAlloc_3461_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3461_, 0, v___x_3429_);
lean_ctor_set(v_reuseFailAlloc_3461_, 1, v___x_3433_);
v___x_3435_ = v_reuseFailAlloc_3461_;
goto v_reusejp_3434_;
}
v_reusejp_3434_:
{
lean_object* v___x_3436_; lean_object* v___x_3438_; 
v___x_3436_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__6, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__6);
if (v_isShared_3415_ == 0)
{
lean_ctor_set_tag(v___x_3414_, 7);
lean_ctor_set(v___x_3414_, 1, v___x_3436_);
lean_ctor_set(v___x_3414_, 0, v___x_3435_);
v___x_3438_ = v___x_3414_;
goto v_reusejp_3437_;
}
else
{
lean_object* v_reuseFailAlloc_3460_; 
v_reuseFailAlloc_3460_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3460_, 0, v___x_3435_);
lean_ctor_set(v_reuseFailAlloc_3460_, 1, v___x_3436_);
v___x_3438_ = v_reuseFailAlloc_3460_;
goto v_reusejp_3437_;
}
v_reusejp_3437_:
{
lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; size_t v_sz_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; 
v___x_3439_ = lean_array_to_list(v_fst_3416_);
v___x_3440_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_3439_, v___x_3431_);
v___x_3441_ = l_Lean_MessageData_ofList(v___x_3440_);
v___x_3442_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3442_, 0, v___x_3438_);
lean_ctor_set(v___x_3442_, 1, v___x_3441_);
v___x_3443_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__8);
v___x_3444_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3444_, 0, v___x_3442_);
lean_ctor_set(v___x_3444_, 1, v___x_3443_);
v_sz_3445_ = lean_array_size(v_snd_3417_);
lean_inc(v_snd_3417_);
v___x_3446_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10(v_sz_3445_, v___x_3348_, v_snd_3417_);
v___x_3447_ = lean_array_to_list(v___x_3446_);
v___x_3448_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_3447_, v___x_3431_);
v___x_3449_ = l_Lean_MessageData_ofList(v___x_3448_);
v___x_3450_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3450_, 0, v___x_3444_);
lean_ctor_set(v___x_3450_, 1, v___x_3449_);
v___x_3451_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_3380_, v___x_3450_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_);
if (lean_obj_tag(v___x_3451_) == 0)
{
lean_dec_ref_known(v___x_3451_, 1);
v___y_3382_ = v___x_3421_;
v___y_3383_ = v_snd_3417_;
v___y_3384_ = v___f_3422_;
v___y_3385_ = v___y_3353_;
v___y_3386_ = v___y_3354_;
v___y_3387_ = v___y_3355_;
v___y_3388_ = v___y_3356_;
goto v___jp_3381_;
}
else
{
lean_object* v_a_3452_; lean_object* v___x_3454_; uint8_t v_isShared_3455_; uint8_t v_isSharedCheck_3459_; 
lean_dec_ref(v___f_3422_);
lean_dec_ref(v___x_3421_);
lean_dec(v_snd_3417_);
v_a_3452_ = lean_ctor_get(v___x_3451_, 0);
v_isSharedCheck_3459_ = !lean_is_exclusive(v___x_3451_);
if (v_isSharedCheck_3459_ == 0)
{
v___x_3454_ = v___x_3451_;
v_isShared_3455_ = v_isSharedCheck_3459_;
goto v_resetjp_3453_;
}
else
{
lean_inc(v_a_3452_);
lean_dec(v___x_3451_);
v___x_3454_ = lean_box(0);
v_isShared_3455_ = v_isSharedCheck_3459_;
goto v_resetjp_3453_;
}
v_resetjp_3453_:
{
lean_object* v___x_3457_; 
if (v_isShared_3455_ == 0)
{
v___x_3457_ = v___x_3454_;
goto v_reusejp_3456_;
}
else
{
lean_object* v_reuseFailAlloc_3458_; 
v_reuseFailAlloc_3458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3458_, 0, v_a_3452_);
v___x_3457_ = v_reuseFailAlloc_3458_;
goto v_reusejp_3456_;
}
v_reusejp_3456_:
{
return v___x_3457_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3462_; 
lean_dec_ref(v___x_3421_);
lean_del_object(v___x_3419_);
lean_dec(v_fst_3416_);
lean_del_object(v___x_3414_);
lean_dec_ref(v_xs_3350_);
v___x_3462_ = l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8___redArg(v_snd_3417_, v___f_3422_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_);
lean_dec(v_snd_3417_);
return v___x_3462_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___boxed(lean_object* v___x_3483_, lean_object* v_a_3484_, lean_object* v_xs_3485_, lean_object* v_a_3486_, lean_object* v_recArgInfos_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_){
_start:
{
size_t v___x_12976__boxed_3493_; lean_object* v_res_3494_; 
v___x_12976__boxed_3493_ = lean_unbox_usize(v___x_3483_);
lean_dec(v___x_3483_);
v_res_3494_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0(v___x_12976__boxed_3493_, v_a_3484_, v_xs_3485_, v_a_3486_, v_recArgInfos_3487_, v___y_3488_, v___y_3489_, v___y_3490_, v___y_3491_);
lean_dec(v___y_3491_);
lean_dec_ref(v___y_3490_);
lean_dec(v___y_3489_);
lean_dec_ref(v___y_3488_);
return v_res_3494_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__11___redArg(lean_object* v___x_3495_, lean_object* v_xs_3496_, size_t v_sz_3497_, size_t v_i_3498_, lean_object* v_bs_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_){
_start:
{
uint8_t v___x_3505_; 
v___x_3505_ = lean_usize_dec_lt(v_i_3498_, v_sz_3497_);
if (v___x_3505_ == 0)
{
lean_object* v___x_3506_; 
lean_dec_ref(v_xs_3496_);
v___x_3506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3506_, 0, v_bs_3499_);
return v___x_3506_;
}
else
{
lean_object* v_v_3507_; lean_object* v_value_3508_; lean_object* v___x_3509_; lean_object* v_bs_x27_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; 
v_v_3507_ = lean_array_uget_borrowed(v_bs_3499_, v_i_3498_);
v_value_3508_ = lean_ctor_get(v_v_3507_, 7);
lean_inc_ref(v_value_3508_);
v___x_3509_ = lean_unsigned_to_nat(0u);
v_bs_x27_3510_ = lean_array_uset(v_bs_3499_, v_i_3498_, v___x_3509_);
v___x_3511_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0);
v___x_3512_ = lean_usize_to_nat(v_i_3498_);
v___x_3513_ = lean_array_get_borrowed(v___x_3511_, v___x_3495_, v___x_3512_);
lean_dec(v___x_3512_);
lean_inc_ref(v_xs_3496_);
lean_inc(v___x_3513_);
v___x_3514_ = l_Lean_Elab_FixedParamPerm_instantiateLambda(v___x_3513_, v_value_3508_, v_xs_3496_, v___y_3500_, v___y_3501_, v___y_3502_, v___y_3503_);
if (lean_obj_tag(v___x_3514_) == 0)
{
lean_object* v_a_3515_; size_t v___x_3516_; size_t v___x_3517_; lean_object* v___x_3518_; 
v_a_3515_ = lean_ctor_get(v___x_3514_, 0);
lean_inc(v_a_3515_);
lean_dec_ref_known(v___x_3514_, 1);
v___x_3516_ = ((size_t)1ULL);
v___x_3517_ = lean_usize_add(v_i_3498_, v___x_3516_);
v___x_3518_ = lean_array_uset(v_bs_x27_3510_, v_i_3498_, v_a_3515_);
v_i_3498_ = v___x_3517_;
v_bs_3499_ = v___x_3518_;
goto _start;
}
else
{
lean_object* v_a_3520_; lean_object* v___x_3522_; uint8_t v_isShared_3523_; uint8_t v_isSharedCheck_3527_; 
lean_dec_ref(v_bs_x27_3510_);
lean_dec_ref(v_xs_3496_);
v_a_3520_ = lean_ctor_get(v___x_3514_, 0);
v_isSharedCheck_3527_ = !lean_is_exclusive(v___x_3514_);
if (v_isSharedCheck_3527_ == 0)
{
v___x_3522_ = v___x_3514_;
v_isShared_3523_ = v_isSharedCheck_3527_;
goto v_resetjp_3521_;
}
else
{
lean_inc(v_a_3520_);
lean_dec(v___x_3514_);
v___x_3522_ = lean_box(0);
v_isShared_3523_ = v_isSharedCheck_3527_;
goto v_resetjp_3521_;
}
v_resetjp_3521_:
{
lean_object* v___x_3525_; 
if (v_isShared_3523_ == 0)
{
v___x_3525_ = v___x_3522_;
goto v_reusejp_3524_;
}
else
{
lean_object* v_reuseFailAlloc_3526_; 
v_reuseFailAlloc_3526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3526_, 0, v_a_3520_);
v___x_3525_ = v_reuseFailAlloc_3526_;
goto v_reusejp_3524_;
}
v_reusejp_3524_:
{
return v___x_3525_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__11___redArg___boxed(lean_object* v___x_3528_, lean_object* v_xs_3529_, lean_object* v_sz_3530_, lean_object* v_i_3531_, lean_object* v_bs_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_){
_start:
{
size_t v_sz_boxed_3538_; size_t v_i_boxed_3539_; lean_object* v_res_3540_; 
v_sz_boxed_3538_ = lean_unbox_usize(v_sz_3530_);
lean_dec(v_sz_3530_);
v_i_boxed_3539_ = lean_unbox_usize(v_i_3531_);
lean_dec(v_i_3531_);
v_res_3540_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__11___redArg(v___x_3528_, v_xs_3529_, v_sz_boxed_3538_, v_i_boxed_3539_, v_bs_3532_, v___y_3533_, v___y_3534_, v___y_3535_, v___y_3536_);
lean_dec(v___y_3536_);
lean_dec_ref(v___y_3535_);
lean_dec(v___y_3534_);
lean_dec_ref(v___y_3533_);
lean_dec_ref(v___x_3528_);
return v_res_3540_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__2(size_t v___x_3541_, lean_object* v_a_3542_, lean_object* v_a_3543_, lean_object* v_perms_3544_, lean_object* v_fnNames_3545_, lean_object* v_termMeasure_x3fs_3546_, lean_object* v_xs_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_){
_start:
{
lean_object* v___x_3553_; lean_object* v___f_3554_; size_t v_sz_3555_; lean_object* v___x_3556_; 
v___x_3553_ = lean_box_usize(v___x_3541_);
lean_inc_ref_n(v_a_3543_, 2);
lean_inc_ref_n(v_xs_3547_, 2);
lean_inc_ref(v_a_3542_);
v___f_3554_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___boxed), 10, 4);
lean_closure_set(v___f_3554_, 0, v___x_3553_);
lean_closure_set(v___f_3554_, 1, v_a_3542_);
lean_closure_set(v___f_3554_, 2, v_xs_3547_);
lean_closure_set(v___f_3554_, 3, v_a_3543_);
v_sz_3555_ = lean_array_size(v_a_3543_);
v___x_3556_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__11___redArg(v_perms_3544_, v_xs_3547_, v_sz_3555_, v___x_3541_, v_a_3543_, v___y_3548_, v___y_3549_, v___y_3550_, v___y_3551_);
if (lean_obj_tag(v___x_3556_) == 0)
{
lean_object* v_a_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; 
v_a_3557_ = lean_ctor_get(v___x_3556_, 0);
lean_inc_n(v_a_3557_, 2);
lean_dec_ref_known(v___x_3556_, 1);
lean_inc_ref(v_xs_3547_);
lean_inc_ref(v_fnNames_3545_);
v___x_3558_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_findRecArgCandidates___boxed), 10, 5);
lean_closure_set(v___x_3558_, 0, v_fnNames_3545_);
lean_closure_set(v___x_3558_, 1, v_a_3542_);
lean_closure_set(v___x_3558_, 2, v_xs_3547_);
lean_closure_set(v___x_3558_, 3, v_a_3557_);
lean_closure_set(v___x_3558_, 4, v_termMeasure_x3fs_3546_);
v___x_3559_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v_a_3543_, v___x_3558_, v___y_3548_, v___y_3549_, v___y_3550_, v___y_3551_);
if (lean_obj_tag(v___x_3559_) == 0)
{
lean_object* v_a_3560_; lean_object* v___x_3561_; 
v_a_3560_ = lean_ctor_get(v___x_3559_, 0);
lean_inc(v_a_3560_);
lean_dec_ref_known(v___x_3559_, 1);
v___x_3561_ = l_Lean_Elab_Structural_tryCandidates___redArg(v_fnNames_3545_, v_xs_3547_, v_a_3557_, v_a_3560_, v___f_3554_, v___y_3548_, v___y_3549_, v___y_3550_, v___y_3551_);
lean_dec_ref(v_fnNames_3545_);
return v___x_3561_;
}
else
{
lean_object* v_a_3562_; lean_object* v___x_3564_; uint8_t v_isShared_3565_; uint8_t v_isSharedCheck_3569_; 
lean_dec(v_a_3557_);
lean_dec_ref(v___f_3554_);
lean_dec_ref(v_xs_3547_);
lean_dec_ref(v_fnNames_3545_);
v_a_3562_ = lean_ctor_get(v___x_3559_, 0);
v_isSharedCheck_3569_ = !lean_is_exclusive(v___x_3559_);
if (v_isSharedCheck_3569_ == 0)
{
v___x_3564_ = v___x_3559_;
v_isShared_3565_ = v_isSharedCheck_3569_;
goto v_resetjp_3563_;
}
else
{
lean_inc(v_a_3562_);
lean_dec(v___x_3559_);
v___x_3564_ = lean_box(0);
v_isShared_3565_ = v_isSharedCheck_3569_;
goto v_resetjp_3563_;
}
v_resetjp_3563_:
{
lean_object* v___x_3567_; 
if (v_isShared_3565_ == 0)
{
v___x_3567_ = v___x_3564_;
goto v_reusejp_3566_;
}
else
{
lean_object* v_reuseFailAlloc_3568_; 
v_reuseFailAlloc_3568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3568_, 0, v_a_3562_);
v___x_3567_ = v_reuseFailAlloc_3568_;
goto v_reusejp_3566_;
}
v_reusejp_3566_:
{
return v___x_3567_;
}
}
}
}
else
{
lean_object* v_a_3570_; lean_object* v___x_3572_; uint8_t v_isShared_3573_; uint8_t v_isSharedCheck_3577_; 
lean_dec_ref(v___f_3554_);
lean_dec_ref(v_xs_3547_);
lean_dec_ref(v_termMeasure_x3fs_3546_);
lean_dec_ref(v_fnNames_3545_);
lean_dec_ref(v_a_3543_);
lean_dec_ref(v_a_3542_);
v_a_3570_ = lean_ctor_get(v___x_3556_, 0);
v_isSharedCheck_3577_ = !lean_is_exclusive(v___x_3556_);
if (v_isSharedCheck_3577_ == 0)
{
v___x_3572_ = v___x_3556_;
v_isShared_3573_ = v_isSharedCheck_3577_;
goto v_resetjp_3571_;
}
else
{
lean_inc(v_a_3570_);
lean_dec(v___x_3556_);
v___x_3572_ = lean_box(0);
v_isShared_3573_ = v_isSharedCheck_3577_;
goto v_resetjp_3571_;
}
v_resetjp_3571_:
{
lean_object* v___x_3575_; 
if (v_isShared_3573_ == 0)
{
v___x_3575_ = v___x_3572_;
goto v_reusejp_3574_;
}
else
{
lean_object* v_reuseFailAlloc_3576_; 
v_reuseFailAlloc_3576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3576_, 0, v_a_3570_);
v___x_3575_ = v_reuseFailAlloc_3576_;
goto v_reusejp_3574_;
}
v_reusejp_3574_:
{
return v___x_3575_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__2___boxed(lean_object* v___x_3578_, lean_object* v_a_3579_, lean_object* v_a_3580_, lean_object* v_perms_3581_, lean_object* v_fnNames_3582_, lean_object* v_termMeasure_x3fs_3583_, lean_object* v_xs_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_){
_start:
{
size_t v___x_13319__boxed_3590_; lean_object* v_res_3591_; 
v___x_13319__boxed_3590_ = lean_unbox_usize(v___x_3578_);
lean_dec(v___x_3578_);
v_res_3591_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__2(v___x_13319__boxed_3590_, v_a_3579_, v_a_3580_, v_perms_3581_, v_fnNames_3582_, v_termMeasure_x3fs_3583_, v_xs_3584_, v___y_3585_, v___y_3586_, v___y_3587_, v___y_3588_);
lean_dec(v___y_3588_);
lean_dec_ref(v___y_3587_);
lean_dec(v___y_3586_);
lean_dec_ref(v___y_3585_);
lean_dec_ref(v_perms_3581_);
return v_res_3591_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0___redArg(lean_object* v_fnNames_3592_, lean_object* v_numSectionVars_3593_, size_t v_sz_3594_, size_t v_i_3595_, lean_object* v_bs_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_){
_start:
{
uint8_t v___x_3600_; 
v___x_3600_ = lean_usize_dec_lt(v_i_3595_, v_sz_3594_);
if (v___x_3600_ == 0)
{
lean_object* v___x_3601_; 
lean_dec(v_numSectionVars_3593_);
lean_dec_ref(v_fnNames_3592_);
v___x_3601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3601_, 0, v_bs_3596_);
return v___x_3601_;
}
else
{
lean_object* v_v_3602_; lean_object* v_ref_3603_; uint8_t v_kind_3604_; lean_object* v_levelParams_3605_; lean_object* v_modifiers_3606_; lean_object* v_declName_3607_; lean_object* v_binders_3608_; lean_object* v_numSectionVars_3609_; lean_object* v_type_3610_; lean_object* v_value_3611_; lean_object* v_termination_3612_; lean_object* v___x_3614_; uint8_t v_isShared_3615_; uint8_t v_isSharedCheck_3635_; 
v_v_3602_ = lean_array_uget(v_bs_3596_, v_i_3595_);
v_ref_3603_ = lean_ctor_get(v_v_3602_, 0);
v_kind_3604_ = lean_ctor_get_uint8(v_v_3602_, sizeof(void*)*9);
v_levelParams_3605_ = lean_ctor_get(v_v_3602_, 1);
v_modifiers_3606_ = lean_ctor_get(v_v_3602_, 2);
v_declName_3607_ = lean_ctor_get(v_v_3602_, 3);
v_binders_3608_ = lean_ctor_get(v_v_3602_, 4);
v_numSectionVars_3609_ = lean_ctor_get(v_v_3602_, 5);
v_type_3610_ = lean_ctor_get(v_v_3602_, 6);
v_value_3611_ = lean_ctor_get(v_v_3602_, 7);
v_termination_3612_ = lean_ctor_get(v_v_3602_, 8);
v_isSharedCheck_3635_ = !lean_is_exclusive(v_v_3602_);
if (v_isSharedCheck_3635_ == 0)
{
v___x_3614_ = v_v_3602_;
v_isShared_3615_ = v_isSharedCheck_3635_;
goto v_resetjp_3613_;
}
else
{
lean_inc(v_termination_3612_);
lean_inc(v_value_3611_);
lean_inc(v_type_3610_);
lean_inc(v_numSectionVars_3609_);
lean_inc(v_binders_3608_);
lean_inc(v_declName_3607_);
lean_inc(v_modifiers_3606_);
lean_inc(v_levelParams_3605_);
lean_inc(v_ref_3603_);
lean_dec(v_v_3602_);
v___x_3614_ = lean_box(0);
v_isShared_3615_ = v_isSharedCheck_3635_;
goto v_resetjp_3613_;
}
v_resetjp_3613_:
{
lean_object* v___x_3616_; lean_object* v_bs_x27_3617_; lean_object* v___x_3618_; 
v___x_3616_ = lean_unsigned_to_nat(0u);
v_bs_x27_3617_ = lean_array_uset(v_bs_3596_, v_i_3595_, v___x_3616_);
lean_inc(v_numSectionVars_3593_);
lean_inc_ref(v_fnNames_3592_);
v___x_3618_ = l_Lean_Elab_Structural_preprocess(v_value_3611_, v_fnNames_3592_, v_numSectionVars_3593_, v___y_3597_, v___y_3598_);
if (lean_obj_tag(v___x_3618_) == 0)
{
lean_object* v_a_3619_; lean_object* v___x_3621_; 
v_a_3619_ = lean_ctor_get(v___x_3618_, 0);
lean_inc(v_a_3619_);
lean_dec_ref_known(v___x_3618_, 1);
if (v_isShared_3615_ == 0)
{
lean_ctor_set(v___x_3614_, 7, v_a_3619_);
v___x_3621_ = v___x_3614_;
goto v_reusejp_3620_;
}
else
{
lean_object* v_reuseFailAlloc_3626_; 
v_reuseFailAlloc_3626_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_3626_, 0, v_ref_3603_);
lean_ctor_set(v_reuseFailAlloc_3626_, 1, v_levelParams_3605_);
lean_ctor_set(v_reuseFailAlloc_3626_, 2, v_modifiers_3606_);
lean_ctor_set(v_reuseFailAlloc_3626_, 3, v_declName_3607_);
lean_ctor_set(v_reuseFailAlloc_3626_, 4, v_binders_3608_);
lean_ctor_set(v_reuseFailAlloc_3626_, 5, v_numSectionVars_3609_);
lean_ctor_set(v_reuseFailAlloc_3626_, 6, v_type_3610_);
lean_ctor_set(v_reuseFailAlloc_3626_, 7, v_a_3619_);
lean_ctor_set(v_reuseFailAlloc_3626_, 8, v_termination_3612_);
lean_ctor_set_uint8(v_reuseFailAlloc_3626_, sizeof(void*)*9, v_kind_3604_);
v___x_3621_ = v_reuseFailAlloc_3626_;
goto v_reusejp_3620_;
}
v_reusejp_3620_:
{
size_t v___x_3622_; size_t v___x_3623_; lean_object* v___x_3624_; 
v___x_3622_ = ((size_t)1ULL);
v___x_3623_ = lean_usize_add(v_i_3595_, v___x_3622_);
v___x_3624_ = lean_array_uset(v_bs_x27_3617_, v_i_3595_, v___x_3621_);
v_i_3595_ = v___x_3623_;
v_bs_3596_ = v___x_3624_;
goto _start;
}
}
else
{
lean_object* v_a_3627_; lean_object* v___x_3629_; uint8_t v_isShared_3630_; uint8_t v_isSharedCheck_3634_; 
lean_dec_ref(v_bs_x27_3617_);
lean_del_object(v___x_3614_);
lean_dec_ref(v_termination_3612_);
lean_dec_ref(v_type_3610_);
lean_dec(v_numSectionVars_3609_);
lean_dec(v_binders_3608_);
lean_dec(v_declName_3607_);
lean_dec_ref(v_modifiers_3606_);
lean_dec(v_levelParams_3605_);
lean_dec(v_ref_3603_);
lean_dec(v_numSectionVars_3593_);
lean_dec_ref(v_fnNames_3592_);
v_a_3627_ = lean_ctor_get(v___x_3618_, 0);
v_isSharedCheck_3634_ = !lean_is_exclusive(v___x_3618_);
if (v_isSharedCheck_3634_ == 0)
{
v___x_3629_ = v___x_3618_;
v_isShared_3630_ = v_isSharedCheck_3634_;
goto v_resetjp_3628_;
}
else
{
lean_inc(v_a_3627_);
lean_dec(v___x_3618_);
v___x_3629_ = lean_box(0);
v_isShared_3630_ = v_isSharedCheck_3634_;
goto v_resetjp_3628_;
}
v_resetjp_3628_:
{
lean_object* v___x_3632_; 
if (v_isShared_3630_ == 0)
{
v___x_3632_ = v___x_3629_;
goto v_reusejp_3631_;
}
else
{
lean_object* v_reuseFailAlloc_3633_; 
v_reuseFailAlloc_3633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3633_, 0, v_a_3627_);
v___x_3632_ = v_reuseFailAlloc_3633_;
goto v_reusejp_3631_;
}
v_reusejp_3631_:
{
return v___x_3632_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0___redArg___boxed(lean_object* v_fnNames_3636_, lean_object* v_numSectionVars_3637_, lean_object* v_sz_3638_, lean_object* v_i_3639_, lean_object* v_bs_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_){
_start:
{
size_t v_sz_boxed_3644_; size_t v_i_boxed_3645_; lean_object* v_res_3646_; 
v_sz_boxed_3644_ = lean_unbox_usize(v_sz_3638_);
lean_dec(v_sz_3638_);
v_i_boxed_3645_ = lean_unbox_usize(v_i_3639_);
lean_dec(v_i_3639_);
v_res_3646_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0___redArg(v_fnNames_3636_, v_numSectionVars_3637_, v_sz_boxed_3644_, v_i_boxed_3645_, v_bs_3640_, v___y_3641_, v___y_3642_);
lean_dec(v___y_3642_);
lean_dec_ref(v___y_3641_);
return v_res_3646_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0(lean_object* v_fnNames_3647_, lean_object* v_numSectionVars_3648_, size_t v_sz_3649_, size_t v_i_3650_, lean_object* v_bs_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_){
_start:
{
lean_object* v___x_3657_; 
v___x_3657_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0___redArg(v_fnNames_3647_, v_numSectionVars_3648_, v_sz_3649_, v_i_3650_, v_bs_3651_, v___y_3654_, v___y_3655_);
return v___x_3657_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0___boxed(lean_object* v_fnNames_3658_, lean_object* v_numSectionVars_3659_, lean_object* v_sz_3660_, lean_object* v_i_3661_, lean_object* v_bs_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_){
_start:
{
size_t v_sz_boxed_3668_; size_t v_i_boxed_3669_; lean_object* v_res_3670_; 
v_sz_boxed_3668_ = lean_unbox_usize(v_sz_3660_);
lean_dec(v_sz_3660_);
v_i_boxed_3669_ = lean_unbox_usize(v_i_3661_);
lean_dec(v_i_3661_);
v_res_3670_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0(v_fnNames_3658_, v_numSectionVars_3659_, v_sz_boxed_3668_, v_i_boxed_3669_, v_bs_3662_, v___y_3663_, v___y_3664_, v___y_3665_, v___y_3666_);
lean_dec(v___y_3666_);
lean_dec_ref(v___y_3665_);
lean_dec(v___y_3664_);
lean_dec_ref(v___y_3663_);
return v_res_3670_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos(lean_object* v_preDefs_3671_, lean_object* v_termMeasure_x3fs_3672_, lean_object* v_a_3673_, lean_object* v_a_3674_, lean_object* v_a_3675_, lean_object* v_a_3676_){
_start:
{
lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v_numSectionVars_3681_; size_t v_sz_3682_; lean_object* v___x_3683_; size_t v___x_3684_; lean_object* v_fnNames_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; 
v___x_3678_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_3679_ = lean_unsigned_to_nat(0u);
v___x_3680_ = lean_array_get_borrowed(v___x_3678_, v_preDefs_3671_, v___x_3679_);
v_numSectionVars_3681_ = lean_ctor_get(v___x_3680_, 5);
v_sz_3682_ = lean_array_size(v_preDefs_3671_);
v___x_3683_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0);
v___x_3684_ = ((size_t)0ULL);
lean_inc_ref_n(v_preDefs_3671_, 2);
v_fnNames_3685_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16(v_sz_3682_, v___x_3684_, v_preDefs_3671_);
v___x_3686_ = lean_box_usize(v_sz_3682_);
v___x_3687_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___boxed__const__1));
lean_inc(v_numSectionVars_3681_);
lean_inc_ref(v_fnNames_3685_);
v___x_3688_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0___boxed), 10, 5);
lean_closure_set(v___x_3688_, 0, v_fnNames_3685_);
lean_closure_set(v___x_3688_, 1, v_numSectionVars_3681_);
lean_closure_set(v___x_3688_, 2, v___x_3686_);
lean_closure_set(v___x_3688_, 3, v___x_3687_);
lean_closure_set(v___x_3688_, 4, v_preDefs_3671_);
v___x_3689_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v_preDefs_3671_, v___x_3688_, v_a_3673_, v_a_3674_, v_a_3675_, v_a_3676_);
if (lean_obj_tag(v___x_3689_) == 0)
{
lean_object* v_a_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; 
v_a_3690_ = lean_ctor_get(v___x_3689_, 0);
lean_inc_n(v_a_3690_, 3);
lean_dec_ref_known(v___x_3689_, 1);
v___x_3691_ = lean_alloc_closure((void*)(l_Lean_Elab_getFixedParamPerms___boxed), 6, 1);
lean_closure_set(v___x_3691_, 0, v_a_3690_);
v___x_3692_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v_a_3690_, v___x_3691_, v_a_3673_, v_a_3674_, v_a_3675_, v_a_3676_);
if (lean_obj_tag(v___x_3692_) == 0)
{
lean_object* v_a_3693_; lean_object* v_perms_3694_; lean_object* v___x_3695_; lean_object* v_type_3696_; lean_object* v___x_3697_; lean_object* v___f_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; 
v_a_3693_ = lean_ctor_get(v___x_3692_, 0);
lean_inc(v_a_3693_);
lean_dec_ref_known(v___x_3692_, 1);
v_perms_3694_ = lean_ctor_get(v_a_3693_, 1);
lean_inc_ref_n(v_perms_3694_, 2);
v___x_3695_ = lean_array_get_borrowed(v___x_3678_, v_a_3690_, v___x_3679_);
v_type_3696_ = lean_ctor_get(v___x_3695_, 6);
lean_inc_ref(v_type_3696_);
v___x_3697_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___boxed__const__1));
v___f_3698_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__2___boxed), 12, 6);
lean_closure_set(v___f_3698_, 0, v___x_3697_);
lean_closure_set(v___f_3698_, 1, v_a_3693_);
lean_closure_set(v___f_3698_, 2, v_a_3690_);
lean_closure_set(v___f_3698_, 3, v_perms_3694_);
lean_closure_set(v___f_3698_, 4, v_fnNames_3685_);
lean_closure_set(v___f_3698_, 5, v_termMeasure_x3fs_3672_);
v___x_3699_ = lean_array_get(v___x_3683_, v_perms_3694_, v___x_3679_);
lean_dec_ref(v_perms_3694_);
v___x_3700_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg(v___x_3699_, v_type_3696_, v___f_3698_, v_a_3673_, v_a_3674_, v_a_3675_, v_a_3676_);
return v___x_3700_;
}
else
{
lean_object* v_a_3701_; lean_object* v___x_3703_; uint8_t v_isShared_3704_; uint8_t v_isSharedCheck_3708_; 
lean_dec(v_a_3690_);
lean_dec_ref(v_fnNames_3685_);
lean_dec_ref(v_termMeasure_x3fs_3672_);
v_a_3701_ = lean_ctor_get(v___x_3692_, 0);
v_isSharedCheck_3708_ = !lean_is_exclusive(v___x_3692_);
if (v_isSharedCheck_3708_ == 0)
{
v___x_3703_ = v___x_3692_;
v_isShared_3704_ = v_isSharedCheck_3708_;
goto v_resetjp_3702_;
}
else
{
lean_inc(v_a_3701_);
lean_dec(v___x_3692_);
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
else
{
lean_object* v_a_3709_; lean_object* v___x_3711_; uint8_t v_isShared_3712_; uint8_t v_isSharedCheck_3716_; 
lean_dec_ref(v_fnNames_3685_);
lean_dec_ref(v_termMeasure_x3fs_3672_);
v_a_3709_ = lean_ctor_get(v___x_3689_, 0);
v_isSharedCheck_3716_ = !lean_is_exclusive(v___x_3689_);
if (v_isSharedCheck_3716_ == 0)
{
v___x_3711_ = v___x_3689_;
v_isShared_3712_ = v_isSharedCheck_3716_;
goto v_resetjp_3710_;
}
else
{
lean_inc(v_a_3709_);
lean_dec(v___x_3689_);
v___x_3711_ = lean_box(0);
v_isShared_3712_ = v_isSharedCheck_3716_;
goto v_resetjp_3710_;
}
v_resetjp_3710_:
{
lean_object* v___x_3714_; 
if (v_isShared_3712_ == 0)
{
v___x_3714_ = v___x_3711_;
goto v_reusejp_3713_;
}
else
{
lean_object* v_reuseFailAlloc_3715_; 
v_reuseFailAlloc_3715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3715_, 0, v_a_3709_);
v___x_3714_ = v_reuseFailAlloc_3715_;
goto v_reusejp_3713_;
}
v_reusejp_3713_:
{
return v___x_3714_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___boxed(lean_object* v_preDefs_3717_, lean_object* v_termMeasure_x3fs_3718_, lean_object* v_a_3719_, lean_object* v_a_3720_, lean_object* v_a_3721_, lean_object* v_a_3722_, lean_object* v_a_3723_){
_start:
{
lean_object* v_res_3724_; 
v_res_3724_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos(v_preDefs_3717_, v_termMeasure_x3fs_3718_, v_a_3719_, v_a_3720_, v_a_3721_, v_a_3722_);
lean_dec(v_a_3722_);
lean_dec_ref(v_a_3721_);
lean_dec(v_a_3720_);
lean_dec_ref(v_a_3719_);
return v_res_3724_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__3(lean_object* v_fst_3725_, lean_object* v_as_3726_, size_t v_sz_3727_, size_t v_i_3728_, lean_object* v_bs_3729_){
_start:
{
lean_object* v___x_3730_; 
v___x_3730_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__3___redArg(v_fst_3725_, v_sz_3727_, v_i_3728_, v_bs_3729_);
return v___x_3730_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__3___boxed(lean_object* v_fst_3731_, lean_object* v_as_3732_, lean_object* v_sz_3733_, lean_object* v_i_3734_, lean_object* v_bs_3735_){
_start:
{
size_t v_sz_boxed_3736_; size_t v_i_boxed_3737_; lean_object* v_res_3738_; 
v_sz_boxed_3736_ = lean_unbox_usize(v_sz_3733_);
lean_dec(v_sz_3733_);
v_i_boxed_3737_ = lean_unbox_usize(v_i_3734_);
lean_dec(v_i_3734_);
v_res_3738_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__3(v_fst_3731_, v_as_3732_, v_sz_boxed_3736_, v_i_boxed_3737_, v_bs_3735_);
lean_dec_ref(v_as_3732_);
lean_dec_ref(v_fst_3731_);
return v_res_3738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__9(lean_object* v_00_u03b1_3739_, lean_object* v_lctx_3740_, lean_object* v_localInsts_3741_, lean_object* v_x_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_){
_start:
{
lean_object* v___x_3748_; 
v___x_3748_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__9___redArg(v_lctx_3740_, v_localInsts_3741_, v_x_3742_, v___y_3743_, v___y_3744_, v___y_3745_, v___y_3746_);
return v___x_3748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__9___boxed(lean_object* v_00_u03b1_3749_, lean_object* v_lctx_3750_, lean_object* v_localInsts_3751_, lean_object* v_x_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_){
_start:
{
lean_object* v_res_3758_; 
v_res_3758_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__9(v_00_u03b1_3749_, v_lctx_3750_, v_localInsts_3751_, v_x_3752_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_);
lean_dec(v___y_3756_);
lean_dec_ref(v___y_3755_);
lean_dec(v___y_3754_);
lean_dec_ref(v___y_3753_);
return v_res_3758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8(lean_object* v_00_u03b1_3759_, lean_object* v_fvarIds_3760_, lean_object* v_k_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_){
_start:
{
lean_object* v___x_3767_; 
v___x_3767_ = l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8___redArg(v_fvarIds_3760_, v_k_3761_, v___y_3762_, v___y_3763_, v___y_3764_, v___y_3765_);
return v___x_3767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8___boxed(lean_object* v_00_u03b1_3768_, lean_object* v_fvarIds_3769_, lean_object* v_k_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_){
_start:
{
lean_object* v_res_3776_; 
v_res_3776_ = l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8(v_00_u03b1_3768_, v_fvarIds_3769_, v_k_3770_, v___y_3771_, v___y_3772_, v___y_3773_, v___y_3774_);
lean_dec(v___y_3774_);
lean_dec_ref(v___y_3773_);
lean_dec(v___y_3772_);
lean_dec_ref(v___y_3771_);
lean_dec_ref(v_fvarIds_3769_);
return v_res_3776_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__14(lean_object* v_a_3777_){
_start:
{
lean_object* v___x_3778_; 
v___x_3778_ = lean_nat_to_int(v_a_3777_);
return v___x_3778_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__11(lean_object* v___x_3779_, lean_object* v_xs_3780_, lean_object* v_as_3781_, size_t v_sz_3782_, size_t v_i_3783_, lean_object* v_bs_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_){
_start:
{
lean_object* v___x_3790_; 
v___x_3790_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__11___redArg(v___x_3779_, v_xs_3780_, v_sz_3782_, v_i_3783_, v_bs_3784_, v___y_3785_, v___y_3786_, v___y_3787_, v___y_3788_);
return v___x_3790_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__11___boxed(lean_object* v___x_3791_, lean_object* v_xs_3792_, lean_object* v_as_3793_, lean_object* v_sz_3794_, lean_object* v_i_3795_, lean_object* v_bs_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_){
_start:
{
size_t v_sz_boxed_3802_; size_t v_i_boxed_3803_; lean_object* v_res_3804_; 
v_sz_boxed_3802_ = lean_unbox_usize(v_sz_3794_);
lean_dec(v_sz_3794_);
v_i_boxed_3803_ = lean_unbox_usize(v_i_3795_);
lean_dec(v_i_3795_);
v_res_3804_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__11(v___x_3791_, v_xs_3792_, v_as_3793_, v_sz_boxed_3802_, v_i_boxed_3803_, v_bs_3796_, v___y_3797_, v___y_3798_, v___y_3799_, v___y_3800_);
lean_dec(v___y_3800_);
lean_dec_ref(v___y_3799_);
lean_dec(v___y_3798_);
lean_dec_ref(v___y_3797_);
lean_dec_ref(v_as_3793_);
lean_dec_ref(v___x_3791_);
return v_res_3804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure___lam__0(lean_object* v_xs_3805_, lean_object* v_x_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_){
_start:
{
lean_object* v___x_3812_; lean_object* v___x_3813_; 
v___x_3812_ = lean_array_get_size(v_xs_3805_);
v___x_3813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3813_, 0, v___x_3812_);
return v___x_3813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure___lam__0___boxed(lean_object* v_xs_3814_, lean_object* v_x_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_){
_start:
{
lean_object* v_res_3821_; 
v_res_3821_ = l_Lean_Elab_Structural_reportTermMeasure___lam__0(v_xs_3814_, v_x_3815_, v___y_3816_, v___y_3817_, v___y_3818_, v___y_3819_);
lean_dec(v___y_3819_);
lean_dec_ref(v___y_3818_);
lean_dec(v___y_3817_);
lean_dec_ref(v___y_3816_);
lean_dec_ref(v_x_3815_);
lean_dec_ref(v_xs_3814_);
return v_res_3821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure___lam__1(lean_object* v___x_3822_, lean_object* v_recArgPos_3823_, lean_object* v_xs_3824_, lean_object* v_x_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_){
_start:
{
lean_object* v___x_3831_; uint8_t v___x_3832_; uint8_t v___x_3833_; uint8_t v___x_3834_; lean_object* v___x_3835_; 
v___x_3831_ = lean_array_get_borrowed(v___x_3822_, v_xs_3824_, v_recArgPos_3823_);
v___x_3832_ = 0;
v___x_3833_ = 1;
v___x_3834_ = 1;
lean_inc(v___x_3831_);
v___x_3835_ = l_Lean_Meta_mkLambdaFVars(v_xs_3824_, v___x_3831_, v___x_3832_, v___x_3833_, v___x_3832_, v___x_3833_, v___x_3834_, v___y_3826_, v___y_3827_, v___y_3828_, v___y_3829_);
return v___x_3835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure___lam__1___boxed(lean_object* v___x_3836_, lean_object* v_recArgPos_3837_, lean_object* v_xs_3838_, lean_object* v_x_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_){
_start:
{
lean_object* v_res_3845_; 
v_res_3845_ = l_Lean_Elab_Structural_reportTermMeasure___lam__1(v___x_3836_, v_recArgPos_3837_, v_xs_3838_, v_x_3839_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_);
lean_dec(v___y_3843_);
lean_dec_ref(v___y_3842_);
lean_dec(v___y_3841_);
lean_dec_ref(v___y_3840_);
lean_dec_ref(v_x_3839_);
lean_dec_ref(v_xs_3838_);
lean_dec(v_recArgPos_3837_);
lean_dec_ref(v___x_3836_);
return v_res_3845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure(lean_object* v_preDef_3857_, lean_object* v_recArgPos_3858_, lean_object* v_a_3859_, lean_object* v_a_3860_, lean_object* v_a_3861_, lean_object* v_a_3862_){
_start:
{
lean_object* v_termination_3864_; lean_object* v_terminationBy_x3f_x3f_3865_; 
v_termination_3864_ = lean_ctor_get(v_preDef_3857_, 8);
lean_inc_ref(v_termination_3864_);
v_terminationBy_x3f_x3f_3865_ = lean_ctor_get(v_termination_3864_, 1);
lean_inc(v_terminationBy_x3f_x3f_3865_);
if (lean_obj_tag(v_terminationBy_x3f_x3f_3865_) == 1)
{
lean_object* v_value_3866_; lean_object* v_extraParams_3867_; lean_object* v_val_3868_; lean_object* v___f_3869_; lean_object* v___x_3870_; lean_object* v___f_3871_; uint8_t v___x_3872_; lean_object* v___x_3873_; 
v_value_3866_ = lean_ctor_get(v_preDef_3857_, 7);
lean_inc_ref_n(v_value_3866_, 2);
lean_dec_ref(v_preDef_3857_);
v_extraParams_3867_ = lean_ctor_get(v_termination_3864_, 5);
lean_inc(v_extraParams_3867_);
lean_dec_ref(v_termination_3864_);
v_val_3868_ = lean_ctor_get(v_terminationBy_x3f_x3f_3865_, 0);
lean_inc(v_val_3868_);
lean_dec_ref_known(v_terminationBy_x3f_x3f_3865_, 1);
v___f_3869_ = ((lean_object*)(l_Lean_Elab_Structural_reportTermMeasure___closed__0));
v___x_3870_ = l_Lean_instInhabitedExpr;
v___f_3871_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_reportTermMeasure___lam__1___boxed), 9, 2);
lean_closure_set(v___f_3871_, 0, v___x_3870_);
lean_closure_set(v___f_3871_, 1, v_recArgPos_3858_);
v___x_3872_ = 0;
v___x_3873_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg(v_value_3866_, v___f_3871_, v___x_3872_, v_a_3859_, v_a_3860_, v_a_3861_, v_a_3862_);
if (lean_obj_tag(v___x_3873_) == 0)
{
lean_object* v_a_3874_; lean_object* v___x_3875_; uint8_t v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; 
v_a_3874_ = lean_ctor_get(v___x_3873_, 0);
lean_inc(v_a_3874_);
lean_dec_ref_known(v___x_3873_, 1);
v___x_3875_ = lean_box(0);
v___x_3876_ = 1;
v___x_3877_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3877_, 0, v___x_3875_);
lean_ctor_set(v___x_3877_, 1, v_a_3874_);
lean_ctor_set_uint8(v___x_3877_, sizeof(void*)*2, v___x_3876_);
v___x_3878_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg(v_value_3866_, v___f_3869_, v___x_3872_, v_a_3859_, v_a_3860_, v_a_3861_, v_a_3862_);
if (lean_obj_tag(v___x_3878_) == 0)
{
lean_object* v_a_3879_; lean_object* v___x_3880_; 
v_a_3879_ = lean_ctor_get(v___x_3878_, 0);
lean_inc(v_a_3879_);
lean_dec_ref_known(v___x_3878_, 1);
v___x_3880_ = l_Lean_Elab_TerminationMeasure_delab(v_a_3879_, v_extraParams_3867_, v___x_3877_, v_a_3859_, v_a_3860_, v_a_3861_, v_a_3862_);
lean_dec(v_a_3879_);
if (lean_obj_tag(v___x_3880_) == 0)
{
lean_object* v_a_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; uint8_t v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; 
v_a_3881_ = lean_ctor_get(v___x_3880_, 0);
lean_inc(v_a_3881_);
lean_dec_ref_known(v___x_3880_, 1);
v___x_3882_ = ((lean_object*)(l_Lean_Elab_Structural_reportTermMeasure___closed__5));
v___x_3883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3883_, 0, v___x_3882_);
lean_ctor_set(v___x_3883_, 1, v_a_3881_);
v___x_3884_ = lean_box(0);
v___x_3885_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3885_, 0, v___x_3883_);
lean_ctor_set(v___x_3885_, 1, v___x_3884_);
lean_ctor_set(v___x_3885_, 2, v___x_3884_);
lean_ctor_set(v___x_3885_, 3, v___x_3884_);
lean_ctor_set(v___x_3885_, 4, v___x_3884_);
lean_ctor_set(v___x_3885_, 5, v___x_3884_);
v___x_3886_ = ((lean_object*)(l_Lean_Elab_Structural_reportTermMeasure___closed__6));
v___x_3887_ = 4;
v___x_3888_ = l_Lean_MessageData_nil;
v___x_3889_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_val_3868_, v___x_3885_, v___x_3884_, v___x_3886_, v___x_3884_, v___x_3887_, v___x_3888_, v_a_3861_, v_a_3862_);
return v___x_3889_;
}
else
{
lean_object* v_a_3890_; lean_object* v___x_3892_; uint8_t v_isShared_3893_; uint8_t v_isSharedCheck_3897_; 
lean_dec(v_val_3868_);
v_a_3890_ = lean_ctor_get(v___x_3880_, 0);
v_isSharedCheck_3897_ = !lean_is_exclusive(v___x_3880_);
if (v_isSharedCheck_3897_ == 0)
{
v___x_3892_ = v___x_3880_;
v_isShared_3893_ = v_isSharedCheck_3897_;
goto v_resetjp_3891_;
}
else
{
lean_inc(v_a_3890_);
lean_dec(v___x_3880_);
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
lean_object* v_a_3898_; lean_object* v___x_3900_; uint8_t v_isShared_3901_; uint8_t v_isSharedCheck_3905_; 
lean_dec_ref_known(v___x_3877_, 2);
lean_dec(v_val_3868_);
lean_dec(v_extraParams_3867_);
v_a_3898_ = lean_ctor_get(v___x_3878_, 0);
v_isSharedCheck_3905_ = !lean_is_exclusive(v___x_3878_);
if (v_isSharedCheck_3905_ == 0)
{
v___x_3900_ = v___x_3878_;
v_isShared_3901_ = v_isSharedCheck_3905_;
goto v_resetjp_3899_;
}
else
{
lean_inc(v_a_3898_);
lean_dec(v___x_3878_);
v___x_3900_ = lean_box(0);
v_isShared_3901_ = v_isSharedCheck_3905_;
goto v_resetjp_3899_;
}
v_resetjp_3899_:
{
lean_object* v___x_3903_; 
if (v_isShared_3901_ == 0)
{
v___x_3903_ = v___x_3900_;
goto v_reusejp_3902_;
}
else
{
lean_object* v_reuseFailAlloc_3904_; 
v_reuseFailAlloc_3904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3904_, 0, v_a_3898_);
v___x_3903_ = v_reuseFailAlloc_3904_;
goto v_reusejp_3902_;
}
v_reusejp_3902_:
{
return v___x_3903_;
}
}
}
}
else
{
lean_object* v_a_3906_; lean_object* v___x_3908_; uint8_t v_isShared_3909_; uint8_t v_isSharedCheck_3913_; 
lean_dec(v_val_3868_);
lean_dec(v_extraParams_3867_);
lean_dec_ref(v_value_3866_);
v_a_3906_ = lean_ctor_get(v___x_3873_, 0);
v_isSharedCheck_3913_ = !lean_is_exclusive(v___x_3873_);
if (v_isSharedCheck_3913_ == 0)
{
v___x_3908_ = v___x_3873_;
v_isShared_3909_ = v_isSharedCheck_3913_;
goto v_resetjp_3907_;
}
else
{
lean_inc(v_a_3906_);
lean_dec(v___x_3873_);
v___x_3908_ = lean_box(0);
v_isShared_3909_ = v_isSharedCheck_3913_;
goto v_resetjp_3907_;
}
v_resetjp_3907_:
{
lean_object* v___x_3911_; 
if (v_isShared_3909_ == 0)
{
v___x_3911_ = v___x_3908_;
goto v_reusejp_3910_;
}
else
{
lean_object* v_reuseFailAlloc_3912_; 
v_reuseFailAlloc_3912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3912_, 0, v_a_3906_);
v___x_3911_ = v_reuseFailAlloc_3912_;
goto v_reusejp_3910_;
}
v_reusejp_3910_:
{
return v___x_3911_;
}
}
}
}
else
{
lean_object* v___x_3914_; lean_object* v___x_3915_; 
lean_dec(v_terminationBy_x3f_x3f_3865_);
lean_dec_ref(v_termination_3864_);
lean_dec(v_recArgPos_3858_);
lean_dec_ref(v_preDef_3857_);
v___x_3914_ = lean_box(0);
v___x_3915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3915_, 0, v___x_3914_);
return v___x_3915_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure___boxed(lean_object* v_preDef_3916_, lean_object* v_recArgPos_3917_, lean_object* v_a_3918_, lean_object* v_a_3919_, lean_object* v_a_3920_, lean_object* v_a_3921_, lean_object* v_a_3922_){
_start:
{
lean_object* v_res_3923_; 
v_res_3923_ = l_Lean_Elab_Structural_reportTermMeasure(v_preDef_3916_, v_recArgPos_3917_, v_a_3918_, v_a_3919_, v_a_3920_, v_a_3921_);
lean_dec(v_a_3921_);
lean_dec_ref(v_a_3920_);
lean_dec(v_a_3919_);
lean_dec_ref(v_a_3918_);
return v_res_3923_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___redArg(lean_object* v_as_3924_, size_t v_sz_3925_, size_t v_i_3926_, lean_object* v_b_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_){
_start:
{
uint8_t v___x_3933_; 
v___x_3933_ = lean_usize_dec_lt(v_i_3926_, v_sz_3925_);
if (v___x_3933_ == 0)
{
lean_object* v___x_3934_; 
v___x_3934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3934_, 0, v_b_3927_);
return v___x_3934_;
}
else
{
lean_object* v_a_3935_; lean_object* v_declName_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; 
v_a_3935_ = lean_array_uget_borrowed(v_as_3924_, v_i_3926_);
v_declName_3936_ = lean_ctor_get(v_a_3935_, 3);
v___x_3937_ = lean_box(0);
lean_inc(v_declName_3936_);
v___x_3938_ = l_Lean_Meta_saveEqnAffectingOptions(v_declName_3936_, v___y_3928_, v___y_3929_, v___y_3930_, v___y_3931_);
if (lean_obj_tag(v___x_3938_) == 0)
{
size_t v___x_3939_; size_t v___x_3940_; 
lean_dec_ref_known(v___x_3938_, 1);
v___x_3939_ = ((size_t)1ULL);
v___x_3940_ = lean_usize_add(v_i_3926_, v___x_3939_);
v_i_3926_ = v___x_3940_;
v_b_3927_ = v___x_3937_;
goto _start;
}
else
{
return v___x_3938_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___redArg___boxed(lean_object* v_as_3942_, lean_object* v_sz_3943_, lean_object* v_i_3944_, lean_object* v_b_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_){
_start:
{
size_t v_sz_boxed_3951_; size_t v_i_boxed_3952_; lean_object* v_res_3953_; 
v_sz_boxed_3951_ = lean_unbox_usize(v_sz_3943_);
lean_dec(v_sz_3943_);
v_i_boxed_3952_ = lean_unbox_usize(v_i_3944_);
lean_dec(v_i_3944_);
v_res_3953_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___redArg(v_as_3942_, v_sz_boxed_3951_, v_i_boxed_3952_, v_b_3945_, v___y_3946_, v___y_3947_, v___y_3948_, v___y_3949_);
lean_dec(v___y_3949_);
lean_dec_ref(v___y_3948_);
lean_dec(v___y_3947_);
lean_dec_ref(v___y_3946_);
lean_dec_ref(v_as_3942_);
return v_res_3953_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__1(lean_object* v_a_3954_, lean_object* v_fst_3955_, lean_object* v_docCtx_3956_, lean_object* v_snd_3957_, lean_object* v_as_3958_, size_t v_sz_3959_, size_t v_i_3960_, lean_object* v_b_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_){
_start:
{
uint8_t v___x_3969_; 
v___x_3969_ = lean_usize_dec_lt(v_i_3960_, v_sz_3959_);
if (v___x_3969_ == 0)
{
lean_object* v___x_3970_; 
lean_dec_ref(v_snd_3957_);
lean_dec_ref(v_docCtx_3956_);
lean_dec_ref(v_a_3954_);
v___x_3970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3970_, 0, v_b_3961_);
return v___x_3970_;
}
else
{
lean_object* v_array_3971_; lean_object* v_start_3972_; lean_object* v_stop_3973_; uint8_t v___x_3974_; 
v_array_3971_ = lean_ctor_get(v_b_3961_, 0);
v_start_3972_ = lean_ctor_get(v_b_3961_, 1);
v_stop_3973_ = lean_ctor_get(v_b_3961_, 2);
v___x_3974_ = lean_nat_dec_lt(v_start_3972_, v_stop_3973_);
if (v___x_3974_ == 0)
{
lean_object* v___x_3975_; 
lean_dec_ref(v_snd_3957_);
lean_dec_ref(v_docCtx_3956_);
lean_dec_ref(v_a_3954_);
v___x_3975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3975_, 0, v_b_3961_);
return v___x_3975_;
}
else
{
lean_object* v___x_3977_; uint8_t v_isShared_3978_; uint8_t v_isSharedCheck_4046_; 
lean_inc(v_stop_3973_);
lean_inc(v_start_3972_);
lean_inc_ref(v_array_3971_);
v_isSharedCheck_4046_ = !lean_is_exclusive(v_b_3961_);
if (v_isSharedCheck_4046_ == 0)
{
lean_object* v_unused_4047_; lean_object* v_unused_4048_; lean_object* v_unused_4049_; 
v_unused_4047_ = lean_ctor_get(v_b_3961_, 2);
lean_dec(v_unused_4047_);
v_unused_4048_ = lean_ctor_get(v_b_3961_, 1);
lean_dec(v_unused_4048_);
v_unused_4049_ = lean_ctor_get(v_b_3961_, 0);
lean_dec(v_unused_4049_);
v___x_3977_ = v_b_3961_;
v_isShared_3978_ = v_isSharedCheck_4046_;
goto v_resetjp_3976_;
}
else
{
lean_dec(v_b_3961_);
v___x_3977_ = lean_box(0);
v_isShared_3978_ = v_isSharedCheck_4046_;
goto v_resetjp_3976_;
}
v_resetjp_3976_:
{
lean_object* v_a_3979_; uint8_t v_kind_3980_; lean_object* v_type_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3986_; 
v_a_3979_ = lean_array_uget_borrowed(v_as_3958_, v_i_3960_);
v_kind_3980_ = lean_ctor_get_uint8(v_a_3979_, sizeof(void*)*9);
v_type_3981_ = lean_ctor_get(v_a_3979_, 6);
v___x_3982_ = lean_array_fget(v_array_3971_, v_start_3972_);
v___x_3983_ = lean_unsigned_to_nat(1u);
v___x_3984_ = lean_nat_add(v_start_3972_, v___x_3983_);
lean_dec(v_start_3972_);
if (v_isShared_3978_ == 0)
{
lean_ctor_set(v___x_3977_, 1, v___x_3984_);
v___x_3986_ = v___x_3977_;
goto v_reusejp_3985_;
}
else
{
lean_object* v_reuseFailAlloc_4045_; 
v_reuseFailAlloc_4045_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4045_, 0, v_array_3971_);
lean_ctor_set(v_reuseFailAlloc_4045_, 1, v___x_3984_);
lean_ctor_set(v_reuseFailAlloc_4045_, 2, v_stop_3973_);
v___x_3986_ = v_reuseFailAlloc_4045_;
goto v_reusejp_3985_;
}
v_reusejp_3985_:
{
lean_object* v_preDef_3988_; lean_object* v___y_3989_; lean_object* v___y_3990_; lean_object* v___y_3991_; lean_object* v___y_3992_; lean_object* v___y_3993_; lean_object* v___y_3994_; uint8_t v___x_4011_; 
v___x_4011_ = l_Lean_Elab_DefKind_isTheorem(v_kind_3980_);
if (v___x_4011_ == 0)
{
lean_object* v___x_4012_; 
lean_inc_ref(v_type_3981_);
v___x_4012_ = l_Lean_Meta_isProp(v_type_3981_, v___y_3964_, v___y_3965_, v___y_3966_, v___y_3967_);
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
lean_inc(v_a_3979_);
v___x_4015_ = l_Lean_Elab_abstractNestedProofs(v_a_3979_, v___x_3974_, v___y_3964_, v___y_3965_, v___y_3966_, v___y_3967_);
if (lean_obj_tag(v___x_4015_) == 0)
{
lean_object* v_a_4016_; size_t v_sz_4017_; size_t v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; 
v_a_4016_ = lean_ctor_get(v___x_4015_, 0);
lean_inc_n(v_a_4016_, 2);
lean_dec_ref_known(v___x_4015_, 1);
v_sz_4017_ = lean_array_size(v_a_3954_);
v___x_4018_ = ((size_t)0ULL);
lean_inc_ref(v_a_3954_);
v___x_4019_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16(v_sz_4017_, v___x_4018_, v_a_3954_);
lean_inc_ref(v_snd_3957_);
v___x_4020_ = l_Lean_Elab_Structural_registerEqnsInfo(v_a_4016_, v___x_4019_, v___x_3982_, v_snd_3957_, v___y_3966_, v___y_3967_);
if (lean_obj_tag(v___x_4020_) == 0)
{
lean_dec_ref_known(v___x_4020_, 1);
v_preDef_3988_ = v_a_4016_;
v___y_3989_ = v___y_3962_;
v___y_3990_ = v___y_3963_;
v___y_3991_ = v___y_3964_;
v___y_3992_ = v___y_3965_;
v___y_3993_ = v___y_3966_;
v___y_3994_ = v___y_3967_;
goto v___jp_3987_;
}
else
{
lean_object* v_a_4021_; lean_object* v___x_4023_; uint8_t v_isShared_4024_; uint8_t v_isSharedCheck_4028_; 
lean_dec(v_a_4016_);
lean_dec_ref(v___x_3986_);
lean_dec_ref(v_snd_3957_);
lean_dec_ref(v_docCtx_3956_);
lean_dec_ref(v_a_3954_);
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
lean_dec_ref(v___x_3986_);
lean_dec(v___x_3982_);
lean_dec_ref(v_snd_3957_);
lean_dec_ref(v_docCtx_3956_);
lean_dec_ref(v_a_3954_);
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
lean_dec(v___x_3982_);
lean_inc(v_a_3979_);
v_preDef_3988_ = v_a_3979_;
v___y_3989_ = v___y_3962_;
v___y_3990_ = v___y_3963_;
v___y_3991_ = v___y_3964_;
v___y_3992_ = v___y_3965_;
v___y_3993_ = v___y_3966_;
v___y_3994_ = v___y_3967_;
goto v___jp_3987_;
}
}
else
{
lean_object* v_a_4037_; lean_object* v___x_4039_; uint8_t v_isShared_4040_; uint8_t v_isSharedCheck_4044_; 
lean_dec_ref(v___x_3986_);
lean_dec(v___x_3982_);
lean_dec_ref(v_snd_3957_);
lean_dec_ref(v_docCtx_3956_);
lean_dec_ref(v_a_3954_);
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
lean_dec(v___x_3982_);
lean_inc(v_a_3979_);
v_preDef_3988_ = v_a_3979_;
v___y_3989_ = v___y_3962_;
v___y_3990_ = v___y_3963_;
v___y_3991_ = v___y_3964_;
v___y_3992_ = v___y_3965_;
v___y_3993_ = v___y_3966_;
v___y_3994_ = v___y_3967_;
goto v___jp_3987_;
}
v___jp_3987_:
{
size_t v_sz_3995_; size_t v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; 
v_sz_3995_ = lean_array_size(v_a_3954_);
v___x_3996_ = ((size_t)0ULL);
lean_inc_ref(v_a_3954_);
v___x_3997_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16(v_sz_3995_, v___x_3996_, v_a_3954_);
v___x_3998_ = l_Array_zip___redArg(v___x_3997_, v_fst_3955_);
lean_dec_ref(v___x_3997_);
lean_inc_ref(v_docCtx_3956_);
v___x_3999_ = l_Lean_Elab_Structural_addSmartUnfoldingDef(v_docCtx_3956_, v_preDef_3988_, v___x_3998_, v___y_3989_, v___y_3990_, v___y_3991_, v___y_3992_, v___y_3993_, v___y_3994_);
if (lean_obj_tag(v___x_3999_) == 0)
{
size_t v___x_4000_; size_t v___x_4001_; 
lean_dec_ref_known(v___x_3999_, 1);
v___x_4000_ = ((size_t)1ULL);
v___x_4001_ = lean_usize_add(v_i_3960_, v___x_4000_);
v_i_3960_ = v___x_4001_;
v_b_3961_ = v___x_3986_;
goto _start;
}
else
{
lean_object* v_a_4003_; lean_object* v___x_4005_; uint8_t v_isShared_4006_; uint8_t v_isSharedCheck_4010_; 
lean_dec_ref(v___x_3986_);
lean_dec_ref(v_snd_3957_);
lean_dec_ref(v_docCtx_3956_);
lean_dec_ref(v_a_3954_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__1___boxed(lean_object* v_a_4050_, lean_object* v_fst_4051_, lean_object* v_docCtx_4052_, lean_object* v_snd_4053_, lean_object* v_as_4054_, lean_object* v_sz_4055_, lean_object* v_i_4056_, lean_object* v_b_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_){
_start:
{
size_t v_sz_boxed_4065_; size_t v_i_boxed_4066_; lean_object* v_res_4067_; 
v_sz_boxed_4065_ = lean_unbox_usize(v_sz_4055_);
lean_dec(v_sz_4055_);
v_i_boxed_4066_ = lean_unbox_usize(v_i_4056_);
lean_dec(v_i_4056_);
v_res_4067_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__1(v_a_4050_, v_fst_4051_, v_docCtx_4052_, v_snd_4053_, v_as_4054_, v_sz_boxed_4065_, v_i_boxed_4066_, v_b_4057_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_, v___y_4063_);
lean_dec(v___y_4063_);
lean_dec_ref(v___y_4062_);
lean_dec(v___y_4061_);
lean_dec_ref(v___y_4060_);
lean_dec(v___y_4059_);
lean_dec_ref(v___y_4058_);
lean_dec_ref(v_as_4054_);
lean_dec_ref(v_fst_4051_);
return v_res_4067_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___lam__0(lean_object* v___x_4068_, lean_object* v_e_4069_){
_start:
{
lean_object* v___x_4070_; lean_object* v___x_4071_; 
v___x_4070_ = l_Lean_indentD(v_e_4069_);
v___x_4071_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4071_, 0, v___x_4068_);
lean_ctor_set(v___x_4071_, 1, v___x_4070_);
return v___x_4071_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___lam__1(lean_object* v_docCtx_4072_, lean_object* v_a_4073_, uint8_t v___x_4074_, lean_object* v___x_4075_, uint8_t v___x_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_){
_start:
{
lean_object* v___x_4084_; 
v___x_4084_ = l_Lean_Elab_addNonRec(v_docCtx_4072_, v_a_4073_, v___x_4074_, v___x_4075_, v___x_4076_, v___x_4074_, v___x_4076_, v___x_4076_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_, v___y_4081_, v___y_4082_);
return v___x_4084_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___lam__1___boxed(lean_object* v_docCtx_4085_, lean_object* v_a_4086_, lean_object* v___x_4087_, lean_object* v___x_4088_, lean_object* v___x_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_){
_start:
{
uint8_t v___x_9352__boxed_4097_; uint8_t v___x_9354__boxed_4098_; lean_object* v_res_4099_; 
v___x_9352__boxed_4097_ = lean_unbox(v___x_4087_);
v___x_9354__boxed_4098_ = lean_unbox(v___x_4089_);
v_res_4099_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___lam__1(v_docCtx_4085_, v_a_4086_, v___x_9352__boxed_4097_, v___x_4088_, v___x_9354__boxed_4098_, v___y_4090_, v___y_4091_, v___y_4092_, v___y_4093_, v___y_4094_, v___y_4095_);
lean_dec(v___y_4095_);
lean_dec_ref(v___y_4094_);
lean_dec(v___y_4093_);
lean_dec_ref(v___y_4092_);
lean_dec(v___y_4091_);
lean_dec_ref(v___y_4090_);
return v_res_4099_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__1(void){
_start:
{
lean_object* v___x_4101_; lean_object* v___x_4102_; 
v___x_4101_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__0));
v___x_4102_ = l_Lean_stringToMessageData(v___x_4101_);
return v___x_4102_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__2(void){
_start:
{
lean_object* v___x_4103_; lean_object* v___f_4104_; 
v___x_4103_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__1);
v___f_4104_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___lam__0), 2, 1);
lean_closure_set(v___f_4104_, 0, v___x_4103_);
return v___f_4104_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5(lean_object* v_names_4105_, lean_object* v_docCtx_4106_, lean_object* v_as_4107_, size_t v_i_4108_, size_t v_stop_4109_, lean_object* v_b_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_){
_start:
{
uint8_t v___x_4118_; 
v___x_4118_ = lean_usize_dec_eq(v_i_4108_, v_stop_4109_);
if (v___x_4118_ == 0)
{
lean_object* v___x_4119_; lean_object* v___x_4120_; 
v___x_4119_ = lean_array_uget_borrowed(v_as_4107_, v_i_4108_);
lean_inc(v___x_4119_);
v___x_4120_ = l_Lean_Elab_eraseRecAppSyntax(v___x_4119_, v___y_4115_, v___y_4116_);
if (lean_obj_tag(v___x_4120_) == 0)
{
lean_object* v_a_4121_; lean_object* v___f_4122_; lean_object* v___x_4123_; uint8_t v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___f_4127_; lean_object* v___x_4128_; 
v_a_4121_ = lean_ctor_get(v___x_4120_, 0);
lean_inc(v_a_4121_);
lean_dec_ref_known(v___x_4120_, 1);
v___f_4122_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__2);
lean_inc_ref(v_names_4105_);
v___x_4123_ = lean_array_to_list(v_names_4105_);
v___x_4124_ = 1;
v___x_4125_ = lean_box(v___x_4118_);
v___x_4126_ = lean_box(v___x_4124_);
lean_inc(v___y_4112_);
lean_inc_ref(v___y_4111_);
lean_inc_ref(v_docCtx_4106_);
v___f_4127_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___lam__1___boxed), 12, 7);
lean_closure_set(v___f_4127_, 0, v_docCtx_4106_);
lean_closure_set(v___f_4127_, 1, v_a_4121_);
lean_closure_set(v___f_4127_, 2, v___x_4125_);
lean_closure_set(v___f_4127_, 3, v___x_4123_);
lean_closure_set(v___f_4127_, 4, v___x_4126_);
lean_closure_set(v___f_4127_, 5, v___y_4111_);
lean_closure_set(v___f_4127_, 6, v___y_4112_);
v___x_4128_ = l_Lean_Meta_mapErrorImp___redArg(v___f_4127_, v___f_4122_, v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_);
if (lean_obj_tag(v___x_4128_) == 0)
{
lean_object* v_a_4129_; size_t v___x_4130_; size_t v___x_4131_; 
v_a_4129_ = lean_ctor_get(v___x_4128_, 0);
lean_inc(v_a_4129_);
lean_dec_ref_known(v___x_4128_, 1);
v___x_4130_ = ((size_t)1ULL);
v___x_4131_ = lean_usize_add(v_i_4108_, v___x_4130_);
v_i_4108_ = v___x_4131_;
v_b_4110_ = v_a_4129_;
goto _start;
}
else
{
lean_object* v_a_4133_; lean_object* v___x_4135_; uint8_t v_isShared_4136_; uint8_t v_isSharedCheck_4140_; 
lean_dec_ref(v_docCtx_4106_);
lean_dec_ref(v_names_4105_);
v_a_4133_ = lean_ctor_get(v___x_4128_, 0);
v_isSharedCheck_4140_ = !lean_is_exclusive(v___x_4128_);
if (v_isSharedCheck_4140_ == 0)
{
v___x_4135_ = v___x_4128_;
v_isShared_4136_ = v_isSharedCheck_4140_;
goto v_resetjp_4134_;
}
else
{
lean_inc(v_a_4133_);
lean_dec(v___x_4128_);
v___x_4135_ = lean_box(0);
v_isShared_4136_ = v_isSharedCheck_4140_;
goto v_resetjp_4134_;
}
v_resetjp_4134_:
{
lean_object* v___x_4138_; 
if (v_isShared_4136_ == 0)
{
v___x_4138_ = v___x_4135_;
goto v_reusejp_4137_;
}
else
{
lean_object* v_reuseFailAlloc_4139_; 
v_reuseFailAlloc_4139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4139_, 0, v_a_4133_);
v___x_4138_ = v_reuseFailAlloc_4139_;
goto v_reusejp_4137_;
}
v_reusejp_4137_:
{
return v___x_4138_;
}
}
}
}
else
{
lean_object* v_a_4141_; lean_object* v___x_4143_; uint8_t v_isShared_4144_; uint8_t v_isSharedCheck_4148_; 
lean_dec_ref(v_docCtx_4106_);
lean_dec_ref(v_names_4105_);
v_a_4141_ = lean_ctor_get(v___x_4120_, 0);
v_isSharedCheck_4148_ = !lean_is_exclusive(v___x_4120_);
if (v_isSharedCheck_4148_ == 0)
{
v___x_4143_ = v___x_4120_;
v_isShared_4144_ = v_isSharedCheck_4148_;
goto v_resetjp_4142_;
}
else
{
lean_inc(v_a_4141_);
lean_dec(v___x_4120_);
v___x_4143_ = lean_box(0);
v_isShared_4144_ = v_isSharedCheck_4148_;
goto v_resetjp_4142_;
}
v_resetjp_4142_:
{
lean_object* v___x_4146_; 
if (v_isShared_4144_ == 0)
{
v___x_4146_ = v___x_4143_;
goto v_reusejp_4145_;
}
else
{
lean_object* v_reuseFailAlloc_4147_; 
v_reuseFailAlloc_4147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4147_, 0, v_a_4141_);
v___x_4146_ = v_reuseFailAlloc_4147_;
goto v_reusejp_4145_;
}
v_reusejp_4145_:
{
return v___x_4146_;
}
}
}
}
else
{
lean_object* v___x_4149_; 
lean_dec_ref(v_docCtx_4106_);
lean_dec_ref(v_names_4105_);
v___x_4149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4149_, 0, v_b_4110_);
return v___x_4149_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___boxed(lean_object* v_names_4150_, lean_object* v_docCtx_4151_, lean_object* v_as_4152_, lean_object* v_i_4153_, lean_object* v_stop_4154_, lean_object* v_b_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_, lean_object* v___y_4162_){
_start:
{
size_t v_i_boxed_4163_; size_t v_stop_boxed_4164_; lean_object* v_res_4165_; 
v_i_boxed_4163_ = lean_unbox_usize(v_i_4153_);
lean_dec(v_i_4153_);
v_stop_boxed_4164_ = lean_unbox_usize(v_stop_4154_);
lean_dec(v_stop_4154_);
v_res_4165_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5(v_names_4150_, v_docCtx_4151_, v_as_4152_, v_i_boxed_4163_, v_stop_boxed_4164_, v_b_4155_, v___y_4156_, v___y_4157_, v___y_4158_, v___y_4159_, v___y_4160_, v___y_4161_);
lean_dec(v___y_4161_);
lean_dec_ref(v___y_4160_);
lean_dec(v___y_4159_);
lean_dec_ref(v___y_4158_);
lean_dec(v___y_4157_);
lean_dec_ref(v___y_4156_);
lean_dec_ref(v_as_4152_);
return v_res_4165_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4___redArg(lean_object* v_as_4166_, size_t v_sz_4167_, size_t v_i_4168_, lean_object* v_b_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_){
_start:
{
uint8_t v___x_4175_; 
v___x_4175_ = lean_usize_dec_lt(v_i_4168_, v_sz_4167_);
if (v___x_4175_ == 0)
{
lean_object* v___x_4176_; 
v___x_4176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4176_, 0, v_b_4169_);
return v___x_4176_;
}
else
{
lean_object* v_array_4177_; lean_object* v_start_4178_; lean_object* v_stop_4179_; uint8_t v___x_4180_; 
v_array_4177_ = lean_ctor_get(v_b_4169_, 0);
v_start_4178_ = lean_ctor_get(v_b_4169_, 1);
v_stop_4179_ = lean_ctor_get(v_b_4169_, 2);
v___x_4180_ = lean_nat_dec_lt(v_start_4178_, v_stop_4179_);
if (v___x_4180_ == 0)
{
lean_object* v___x_4181_; 
v___x_4181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4181_, 0, v_b_4169_);
return v___x_4181_;
}
else
{
lean_object* v___x_4183_; uint8_t v_isShared_4184_; uint8_t v_isSharedCheck_4204_; 
lean_inc(v_stop_4179_);
lean_inc(v_start_4178_);
lean_inc_ref(v_array_4177_);
v_isSharedCheck_4204_ = !lean_is_exclusive(v_b_4169_);
if (v_isSharedCheck_4204_ == 0)
{
lean_object* v_unused_4205_; lean_object* v_unused_4206_; lean_object* v_unused_4207_; 
v_unused_4205_ = lean_ctor_get(v_b_4169_, 2);
lean_dec(v_unused_4205_);
v_unused_4206_ = lean_ctor_get(v_b_4169_, 1);
lean_dec(v_unused_4206_);
v_unused_4207_ = lean_ctor_get(v_b_4169_, 0);
lean_dec(v_unused_4207_);
v___x_4183_ = v_b_4169_;
v_isShared_4184_ = v_isSharedCheck_4204_;
goto v_resetjp_4182_;
}
else
{
lean_dec(v_b_4169_);
v___x_4183_ = lean_box(0);
v_isShared_4184_ = v_isSharedCheck_4204_;
goto v_resetjp_4182_;
}
v_resetjp_4182_:
{
lean_object* v_a_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4190_; 
v_a_4185_ = lean_array_uget_borrowed(v_as_4166_, v_i_4168_);
v___x_4186_ = lean_array_fget(v_array_4177_, v_start_4178_);
v___x_4187_ = lean_unsigned_to_nat(1u);
v___x_4188_ = lean_nat_add(v_start_4178_, v___x_4187_);
lean_dec(v_start_4178_);
if (v_isShared_4184_ == 0)
{
lean_ctor_set(v___x_4183_, 1, v___x_4188_);
v___x_4190_ = v___x_4183_;
goto v_reusejp_4189_;
}
else
{
lean_object* v_reuseFailAlloc_4203_; 
v_reuseFailAlloc_4203_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4203_, 0, v_array_4177_);
lean_ctor_set(v_reuseFailAlloc_4203_, 1, v___x_4188_);
lean_ctor_set(v_reuseFailAlloc_4203_, 2, v_stop_4179_);
v___x_4190_ = v_reuseFailAlloc_4203_;
goto v_reusejp_4189_;
}
v_reusejp_4189_:
{
lean_object* v___x_4191_; 
lean_inc(v_a_4185_);
v___x_4191_ = l_Lean_Elab_Structural_reportTermMeasure(v___x_4186_, v_a_4185_, v___y_4170_, v___y_4171_, v___y_4172_, v___y_4173_);
if (lean_obj_tag(v___x_4191_) == 0)
{
size_t v___x_4192_; size_t v___x_4193_; 
lean_dec_ref_known(v___x_4191_, 1);
v___x_4192_ = ((size_t)1ULL);
v___x_4193_ = lean_usize_add(v_i_4168_, v___x_4192_);
v_i_4168_ = v___x_4193_;
v_b_4169_ = v___x_4190_;
goto _start;
}
else
{
lean_object* v_a_4195_; lean_object* v___x_4197_; uint8_t v_isShared_4198_; uint8_t v_isSharedCheck_4202_; 
lean_dec_ref(v___x_4190_);
v_a_4195_ = lean_ctor_get(v___x_4191_, 0);
v_isSharedCheck_4202_ = !lean_is_exclusive(v___x_4191_);
if (v_isSharedCheck_4202_ == 0)
{
v___x_4197_ = v___x_4191_;
v_isShared_4198_ = v_isSharedCheck_4202_;
goto v_resetjp_4196_;
}
else
{
lean_inc(v_a_4195_);
lean_dec(v___x_4191_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4___redArg___boxed(lean_object* v_as_4208_, lean_object* v_sz_4209_, lean_object* v_i_4210_, lean_object* v_b_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_){
_start:
{
size_t v_sz_boxed_4217_; size_t v_i_boxed_4218_; lean_object* v_res_4219_; 
v_sz_boxed_4217_ = lean_unbox_usize(v_sz_4209_);
lean_dec(v_sz_4209_);
v_i_boxed_4218_ = lean_unbox_usize(v_i_4210_);
lean_dec(v_i_4210_);
v_res_4219_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4___redArg(v_as_4208_, v_sz_boxed_4217_, v_i_boxed_4218_, v_b_4211_, v___y_4212_, v___y_4213_, v___y_4214_, v___y_4215_);
lean_dec(v___y_4215_);
lean_dec_ref(v___y_4214_);
lean_dec(v___y_4213_);
lean_dec_ref(v___y_4212_);
lean_dec_ref(v_as_4208_);
return v_res_4219_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___redArg(size_t v_sz_4220_, size_t v_i_4221_, lean_object* v_bs_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_){
_start:
{
uint8_t v___x_4226_; 
v___x_4226_ = lean_usize_dec_lt(v_i_4221_, v_sz_4220_);
if (v___x_4226_ == 0)
{
lean_object* v___x_4227_; 
v___x_4227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4227_, 0, v_bs_4222_);
return v___x_4227_;
}
else
{
lean_object* v_v_4228_; lean_object* v___x_4229_; lean_object* v_bs_x27_4230_; lean_object* v___x_4231_; 
v_v_4228_ = lean_array_uget(v_bs_4222_, v_i_4221_);
v___x_4229_ = lean_unsigned_to_nat(0u);
v_bs_x27_4230_ = lean_array_uset(v_bs_4222_, v_i_4221_, v___x_4229_);
v___x_4231_ = l_Lean_Elab_eraseRecAppSyntax(v_v_4228_, v___y_4223_, v___y_4224_);
if (lean_obj_tag(v___x_4231_) == 0)
{
lean_object* v_a_4232_; size_t v___x_4233_; size_t v___x_4234_; lean_object* v___x_4235_; 
v_a_4232_ = lean_ctor_get(v___x_4231_, 0);
lean_inc(v_a_4232_);
lean_dec_ref_known(v___x_4231_, 1);
v___x_4233_ = ((size_t)1ULL);
v___x_4234_ = lean_usize_add(v_i_4221_, v___x_4233_);
v___x_4235_ = lean_array_uset(v_bs_x27_4230_, v_i_4221_, v_a_4232_);
v_i_4221_ = v___x_4234_;
v_bs_4222_ = v___x_4235_;
goto _start;
}
else
{
lean_object* v_a_4237_; lean_object* v___x_4239_; uint8_t v_isShared_4240_; uint8_t v_isSharedCheck_4244_; 
lean_dec_ref(v_bs_x27_4230_);
v_a_4237_ = lean_ctor_get(v___x_4231_, 0);
v_isSharedCheck_4244_ = !lean_is_exclusive(v___x_4231_);
if (v_isSharedCheck_4244_ == 0)
{
v___x_4239_ = v___x_4231_;
v_isShared_4240_ = v_isSharedCheck_4244_;
goto v_resetjp_4238_;
}
else
{
lean_inc(v_a_4237_);
lean_dec(v___x_4231_);
v___x_4239_ = lean_box(0);
v_isShared_4240_ = v_isSharedCheck_4244_;
goto v_resetjp_4238_;
}
v_resetjp_4238_:
{
lean_object* v___x_4242_; 
if (v_isShared_4240_ == 0)
{
v___x_4242_ = v___x_4239_;
goto v_reusejp_4241_;
}
else
{
lean_object* v_reuseFailAlloc_4243_; 
v_reuseFailAlloc_4243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4243_, 0, v_a_4237_);
v___x_4242_ = v_reuseFailAlloc_4243_;
goto v_reusejp_4241_;
}
v_reusejp_4241_:
{
return v___x_4242_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___redArg___boxed(lean_object* v_sz_4245_, lean_object* v_i_4246_, lean_object* v_bs_4247_, lean_object* v___y_4248_, lean_object* v___y_4249_, lean_object* v___y_4250_){
_start:
{
size_t v_sz_boxed_4251_; size_t v_i_boxed_4252_; lean_object* v_res_4253_; 
v_sz_boxed_4251_ = lean_unbox_usize(v_sz_4245_);
lean_dec(v_sz_4245_);
v_i_boxed_4252_ = lean_unbox_usize(v_i_4246_);
lean_dec(v_i_4246_);
v_res_4253_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___redArg(v_sz_boxed_4251_, v_i_boxed_4252_, v_bs_4247_, v___y_4248_, v___y_4249_);
lean_dec(v___y_4249_);
lean_dec_ref(v___y_4248_);
return v_res_4253_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___redArg(lean_object* v_as_4254_, size_t v_sz_4255_, size_t v_i_4256_, lean_object* v_b_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_){
_start:
{
uint8_t v___x_4261_; 
v___x_4261_ = lean_usize_dec_lt(v_i_4256_, v_sz_4255_);
if (v___x_4261_ == 0)
{
lean_object* v___x_4262_; 
v___x_4262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4262_, 0, v_b_4257_);
return v___x_4262_;
}
else
{
lean_object* v_a_4263_; lean_object* v_declName_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; 
v_a_4263_ = lean_array_uget_borrowed(v_as_4254_, v_i_4256_);
v_declName_4264_ = lean_ctor_get(v_a_4263_, 3);
v___x_4265_ = lean_box(0);
lean_inc(v_declName_4264_);
v___x_4266_ = l_Lean_enableRealizationsForConst(v_declName_4264_, v___y_4258_, v___y_4259_);
if (lean_obj_tag(v___x_4266_) == 0)
{
size_t v___x_4267_; size_t v___x_4268_; 
lean_dec_ref_known(v___x_4266_, 1);
v___x_4267_ = ((size_t)1ULL);
v___x_4268_ = lean_usize_add(v_i_4256_, v___x_4267_);
v_i_4256_ = v___x_4268_;
v_b_4257_ = v___x_4265_;
goto _start;
}
else
{
return v___x_4266_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___redArg___boxed(lean_object* v_as_4270_, lean_object* v_sz_4271_, lean_object* v_i_4272_, lean_object* v_b_4273_, lean_object* v___y_4274_, lean_object* v___y_4275_, lean_object* v___y_4276_){
_start:
{
size_t v_sz_boxed_4277_; size_t v_i_boxed_4278_; lean_object* v_res_4279_; 
v_sz_boxed_4277_ = lean_unbox_usize(v_sz_4271_);
lean_dec(v_sz_4271_);
v_i_boxed_4278_ = lean_unbox_usize(v_i_4272_);
lean_dec(v_i_4272_);
v_res_4279_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___redArg(v_as_4270_, v_sz_boxed_4277_, v_i_boxed_4278_, v_b_4273_, v___y_4274_, v___y_4275_);
lean_dec(v___y_4275_);
lean_dec_ref(v___y_4274_);
lean_dec_ref(v_as_4270_);
return v_res_4279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_structuralRecursion(lean_object* v_docCtx_4280_, lean_object* v_preDefs_4281_, lean_object* v_termMeasure_x3fs_4282_, lean_object* v_a_4283_, lean_object* v_a_4284_, lean_object* v_a_4285_, lean_object* v_a_4286_, lean_object* v_a_4287_, lean_object* v_a_4288_){
_start:
{
size_t v_sz_4290_; size_t v___x_4291_; lean_object* v_names_4292_; lean_object* v___x_4293_; 
v_sz_4290_ = lean_array_size(v_preDefs_4281_);
v___x_4291_ = ((size_t)0ULL);
lean_inc_ref_n(v_preDefs_4281_, 2);
v_names_4292_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16(v_sz_4290_, v___x_4291_, v_preDefs_4281_);
v___x_4293_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos(v_preDefs_4281_, v_termMeasure_x3fs_4282_, v_a_4285_, v_a_4286_, v_a_4287_, v_a_4288_);
if (lean_obj_tag(v___x_4293_) == 0)
{
lean_object* v_a_4294_; lean_object* v_snd_4295_; lean_object* v_fst_4296_; lean_object* v_fst_4297_; lean_object* v_snd_4298_; lean_object* v___x_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; size_t v_sz_4332_; lean_object* v___x_4333_; 
v_a_4294_ = lean_ctor_get(v___x_4293_, 0);
lean_inc(v_a_4294_);
lean_dec_ref_known(v___x_4293_, 1);
v_snd_4295_ = lean_ctor_get(v_a_4294_, 1);
lean_inc(v_snd_4295_);
v_fst_4296_ = lean_ctor_get(v_a_4294_, 0);
lean_inc(v_fst_4296_);
lean_dec(v_a_4294_);
v_fst_4297_ = lean_ctor_get(v_snd_4295_, 0);
lean_inc(v_fst_4297_);
v_snd_4298_ = lean_ctor_get(v_snd_4295_, 1);
lean_inc(v_snd_4298_);
lean_dec(v_snd_4295_);
v___x_4329_ = lean_unsigned_to_nat(0u);
v___x_4330_ = lean_array_get_size(v_preDefs_4281_);
lean_inc_ref(v_preDefs_4281_);
v___x_4331_ = l_Array_toSubarray___redArg(v_preDefs_4281_, v___x_4329_, v___x_4330_);
v_sz_4332_ = lean_array_size(v_fst_4296_);
v___x_4333_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4___redArg(v_fst_4296_, v_sz_4332_, v___x_4291_, v___x_4331_, v_a_4285_, v_a_4286_, v_a_4287_, v_a_4288_);
if (lean_obj_tag(v___x_4333_) == 0)
{
lean_object* v___x_4334_; uint8_t v___x_4335_; 
lean_dec_ref_known(v___x_4333_, 1);
v___x_4334_ = lean_array_get_size(v_fst_4297_);
v___x_4335_ = lean_nat_dec_lt(v___x_4329_, v___x_4334_);
if (v___x_4335_ == 0)
{
lean_dec_ref(v_names_4292_);
goto v___jp_4299_;
}
else
{
lean_object* v___x_4336_; size_t v___x_4337_; lean_object* v___x_4338_; 
v___x_4336_ = lean_box(0);
v___x_4337_ = lean_usize_of_nat(v___x_4334_);
lean_inc_ref(v_docCtx_4280_);
v___x_4338_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5(v_names_4292_, v_docCtx_4280_, v_fst_4297_, v___x_4291_, v___x_4337_, v___x_4336_, v_a_4283_, v_a_4284_, v_a_4285_, v_a_4286_, v_a_4287_, v_a_4288_);
if (lean_obj_tag(v___x_4338_) == 0)
{
lean_dec_ref_known(v___x_4338_, 1);
goto v___jp_4299_;
}
else
{
lean_dec(v_snd_4298_);
lean_dec(v_fst_4297_);
lean_dec(v_fst_4296_);
lean_dec_ref(v_preDefs_4281_);
lean_dec_ref(v_docCtx_4280_);
return v___x_4338_;
}
}
}
else
{
lean_object* v_a_4339_; lean_object* v___x_4341_; uint8_t v_isShared_4342_; uint8_t v_isSharedCheck_4346_; 
lean_dec(v_snd_4298_);
lean_dec(v_fst_4297_);
lean_dec(v_fst_4296_);
lean_dec_ref(v_names_4292_);
lean_dec_ref(v_preDefs_4281_);
lean_dec_ref(v_docCtx_4280_);
v_a_4339_ = lean_ctor_get(v___x_4333_, 0);
v_isSharedCheck_4346_ = !lean_is_exclusive(v___x_4333_);
if (v_isSharedCheck_4346_ == 0)
{
v___x_4341_ = v___x_4333_;
v_isShared_4342_ = v_isSharedCheck_4346_;
goto v_resetjp_4340_;
}
else
{
lean_inc(v_a_4339_);
lean_dec(v___x_4333_);
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
v___jp_4299_:
{
lean_object* v___x_4300_; 
v___x_4300_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___redArg(v_sz_4290_, v___x_4291_, v_preDefs_4281_, v_a_4287_, v_a_4288_);
if (lean_obj_tag(v___x_4300_) == 0)
{
lean_object* v_a_4301_; lean_object* v___x_4302_; 
v_a_4301_ = lean_ctor_get(v___x_4300_, 0);
lean_inc_n(v_a_4301_, 2);
lean_dec_ref_known(v___x_4300_, 1);
lean_inc_ref(v_docCtx_4280_);
v___x_4302_ = l_Lean_Elab_addAndCompilePartialRec(v_docCtx_4280_, v_a_4301_, v_a_4283_, v_a_4284_, v_a_4285_, v_a_4286_, v_a_4287_, v_a_4288_);
if (lean_obj_tag(v___x_4302_) == 0)
{
lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; size_t v_sz_4306_; lean_object* v___x_4307_; 
lean_dec_ref_known(v___x_4302_, 1);
v___x_4303_ = lean_unsigned_to_nat(0u);
v___x_4304_ = lean_array_get_size(v_fst_4296_);
lean_inc(v_fst_4296_);
v___x_4305_ = l_Array_toSubarray___redArg(v_fst_4296_, v___x_4303_, v___x_4304_);
v_sz_4306_ = lean_array_size(v_a_4301_);
lean_inc(v_a_4301_);
v___x_4307_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__1(v_a_4301_, v_fst_4296_, v_docCtx_4280_, v_snd_4298_, v_a_4301_, v_sz_4306_, v___x_4291_, v___x_4305_, v_a_4283_, v_a_4284_, v_a_4285_, v_a_4286_, v_a_4287_, v_a_4288_);
lean_dec(v_fst_4296_);
if (lean_obj_tag(v___x_4307_) == 0)
{
lean_object* v___x_4308_; lean_object* v___x_4309_; 
lean_dec_ref_known(v___x_4307_, 1);
v___x_4308_ = lean_box(0);
v___x_4309_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___redArg(v_a_4301_, v_sz_4306_, v___x_4291_, v___x_4308_, v_a_4285_, v_a_4286_, v_a_4287_, v_a_4288_);
if (lean_obj_tag(v___x_4309_) == 0)
{
lean_object* v___x_4310_; 
lean_dec_ref_known(v___x_4309_, 1);
v___x_4310_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___redArg(v_a_4301_, v_sz_4306_, v___x_4291_, v___x_4308_, v_a_4287_, v_a_4288_);
lean_dec(v_a_4301_);
if (lean_obj_tag(v___x_4310_) == 0)
{
uint8_t v___x_4311_; lean_object* v___x_4312_; 
lean_dec_ref_known(v___x_4310_, 1);
v___x_4311_ = 1;
v___x_4312_ = l_Lean_Elab_applyAttributesOf(v_fst_4297_, v___x_4311_, v_a_4283_, v_a_4284_, v_a_4285_, v_a_4286_, v_a_4287_, v_a_4288_);
lean_dec(v_fst_4297_);
return v___x_4312_;
}
else
{
lean_dec(v_fst_4297_);
return v___x_4310_;
}
}
else
{
lean_dec(v_a_4301_);
lean_dec(v_fst_4297_);
return v___x_4309_;
}
}
else
{
lean_object* v_a_4313_; lean_object* v___x_4315_; uint8_t v_isShared_4316_; uint8_t v_isSharedCheck_4320_; 
lean_dec(v_a_4301_);
lean_dec(v_fst_4297_);
v_a_4313_ = lean_ctor_get(v___x_4307_, 0);
v_isSharedCheck_4320_ = !lean_is_exclusive(v___x_4307_);
if (v_isSharedCheck_4320_ == 0)
{
v___x_4315_ = v___x_4307_;
v_isShared_4316_ = v_isSharedCheck_4320_;
goto v_resetjp_4314_;
}
else
{
lean_inc(v_a_4313_);
lean_dec(v___x_4307_);
v___x_4315_ = lean_box(0);
v_isShared_4316_ = v_isSharedCheck_4320_;
goto v_resetjp_4314_;
}
v_resetjp_4314_:
{
lean_object* v___x_4318_; 
if (v_isShared_4316_ == 0)
{
v___x_4318_ = v___x_4315_;
goto v_reusejp_4317_;
}
else
{
lean_object* v_reuseFailAlloc_4319_; 
v_reuseFailAlloc_4319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4319_, 0, v_a_4313_);
v___x_4318_ = v_reuseFailAlloc_4319_;
goto v_reusejp_4317_;
}
v_reusejp_4317_:
{
return v___x_4318_;
}
}
}
}
else
{
lean_dec(v_a_4301_);
lean_dec(v_snd_4298_);
lean_dec(v_fst_4297_);
lean_dec(v_fst_4296_);
lean_dec_ref(v_docCtx_4280_);
return v___x_4302_;
}
}
else
{
lean_object* v_a_4321_; lean_object* v___x_4323_; uint8_t v_isShared_4324_; uint8_t v_isSharedCheck_4328_; 
lean_dec(v_snd_4298_);
lean_dec(v_fst_4297_);
lean_dec(v_fst_4296_);
lean_dec_ref(v_docCtx_4280_);
v_a_4321_ = lean_ctor_get(v___x_4300_, 0);
v_isSharedCheck_4328_ = !lean_is_exclusive(v___x_4300_);
if (v_isSharedCheck_4328_ == 0)
{
v___x_4323_ = v___x_4300_;
v_isShared_4324_ = v_isSharedCheck_4328_;
goto v_resetjp_4322_;
}
else
{
lean_inc(v_a_4321_);
lean_dec(v___x_4300_);
v___x_4323_ = lean_box(0);
v_isShared_4324_ = v_isSharedCheck_4328_;
goto v_resetjp_4322_;
}
v_resetjp_4322_:
{
lean_object* v___x_4326_; 
if (v_isShared_4324_ == 0)
{
v___x_4326_ = v___x_4323_;
goto v_reusejp_4325_;
}
else
{
lean_object* v_reuseFailAlloc_4327_; 
v_reuseFailAlloc_4327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4327_, 0, v_a_4321_);
v___x_4326_ = v_reuseFailAlloc_4327_;
goto v_reusejp_4325_;
}
v_reusejp_4325_:
{
return v___x_4326_;
}
}
}
}
}
else
{
lean_object* v_a_4347_; lean_object* v___x_4349_; uint8_t v_isShared_4350_; uint8_t v_isSharedCheck_4354_; 
lean_dec_ref(v_names_4292_);
lean_dec_ref(v_preDefs_4281_);
lean_dec_ref(v_docCtx_4280_);
v_a_4347_ = lean_ctor_get(v___x_4293_, 0);
v_isSharedCheck_4354_ = !lean_is_exclusive(v___x_4293_);
if (v_isSharedCheck_4354_ == 0)
{
v___x_4349_ = v___x_4293_;
v_isShared_4350_ = v_isSharedCheck_4354_;
goto v_resetjp_4348_;
}
else
{
lean_inc(v_a_4347_);
lean_dec(v___x_4293_);
v___x_4349_ = lean_box(0);
v_isShared_4350_ = v_isSharedCheck_4354_;
goto v_resetjp_4348_;
}
v_resetjp_4348_:
{
lean_object* v___x_4352_; 
if (v_isShared_4350_ == 0)
{
v___x_4352_ = v___x_4349_;
goto v_reusejp_4351_;
}
else
{
lean_object* v_reuseFailAlloc_4353_; 
v_reuseFailAlloc_4353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4353_, 0, v_a_4347_);
v___x_4352_ = v_reuseFailAlloc_4353_;
goto v_reusejp_4351_;
}
v_reusejp_4351_:
{
return v___x_4352_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_structuralRecursion___boxed(lean_object* v_docCtx_4355_, lean_object* v_preDefs_4356_, lean_object* v_termMeasure_x3fs_4357_, lean_object* v_a_4358_, lean_object* v_a_4359_, lean_object* v_a_4360_, lean_object* v_a_4361_, lean_object* v_a_4362_, lean_object* v_a_4363_, lean_object* v_a_4364_){
_start:
{
lean_object* v_res_4365_; 
v_res_4365_ = l_Lean_Elab_Structural_structuralRecursion(v_docCtx_4355_, v_preDefs_4356_, v_termMeasure_x3fs_4357_, v_a_4358_, v_a_4359_, v_a_4360_, v_a_4361_, v_a_4362_, v_a_4363_);
lean_dec(v_a_4363_);
lean_dec_ref(v_a_4362_);
lean_dec(v_a_4361_);
lean_dec_ref(v_a_4360_);
lean_dec(v_a_4359_);
lean_dec_ref(v_a_4358_);
return v_res_4365_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0(size_t v_sz_4366_, size_t v_i_4367_, lean_object* v_bs_4368_, lean_object* v___y_4369_, lean_object* v___y_4370_, lean_object* v___y_4371_, lean_object* v___y_4372_, lean_object* v___y_4373_, lean_object* v___y_4374_){
_start:
{
lean_object* v___x_4376_; 
v___x_4376_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___redArg(v_sz_4366_, v_i_4367_, v_bs_4368_, v___y_4373_, v___y_4374_);
return v___x_4376_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___boxed(lean_object* v_sz_4377_, lean_object* v_i_4378_, lean_object* v_bs_4379_, lean_object* v___y_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_, lean_object* v___y_4383_, lean_object* v___y_4384_, lean_object* v___y_4385_, lean_object* v___y_4386_){
_start:
{
size_t v_sz_boxed_4387_; size_t v_i_boxed_4388_; lean_object* v_res_4389_; 
v_sz_boxed_4387_ = lean_unbox_usize(v_sz_4377_);
lean_dec(v_sz_4377_);
v_i_boxed_4388_ = lean_unbox_usize(v_i_4378_);
lean_dec(v_i_4378_);
v_res_4389_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0(v_sz_boxed_4387_, v_i_boxed_4388_, v_bs_4379_, v___y_4380_, v___y_4381_, v___y_4382_, v___y_4383_, v___y_4384_, v___y_4385_);
lean_dec(v___y_4385_);
lean_dec_ref(v___y_4384_);
lean_dec(v___y_4383_);
lean_dec_ref(v___y_4382_);
lean_dec(v___y_4381_);
lean_dec_ref(v___y_4380_);
return v_res_4389_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2(lean_object* v_as_4390_, size_t v_sz_4391_, size_t v_i_4392_, lean_object* v_b_4393_, lean_object* v___y_4394_, lean_object* v___y_4395_, lean_object* v___y_4396_, lean_object* v___y_4397_, lean_object* v___y_4398_, lean_object* v___y_4399_){
_start:
{
lean_object* v___x_4401_; 
v___x_4401_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___redArg(v_as_4390_, v_sz_4391_, v_i_4392_, v_b_4393_, v___y_4396_, v___y_4397_, v___y_4398_, v___y_4399_);
return v___x_4401_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___boxed(lean_object* v_as_4402_, lean_object* v_sz_4403_, lean_object* v_i_4404_, lean_object* v_b_4405_, lean_object* v___y_4406_, lean_object* v___y_4407_, lean_object* v___y_4408_, lean_object* v___y_4409_, lean_object* v___y_4410_, lean_object* v___y_4411_, lean_object* v___y_4412_){
_start:
{
size_t v_sz_boxed_4413_; size_t v_i_boxed_4414_; lean_object* v_res_4415_; 
v_sz_boxed_4413_ = lean_unbox_usize(v_sz_4403_);
lean_dec(v_sz_4403_);
v_i_boxed_4414_ = lean_unbox_usize(v_i_4404_);
lean_dec(v_i_4404_);
v_res_4415_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2(v_as_4402_, v_sz_boxed_4413_, v_i_boxed_4414_, v_b_4405_, v___y_4406_, v___y_4407_, v___y_4408_, v___y_4409_, v___y_4410_, v___y_4411_);
lean_dec(v___y_4411_);
lean_dec_ref(v___y_4410_);
lean_dec(v___y_4409_);
lean_dec_ref(v___y_4408_);
lean_dec(v___y_4407_);
lean_dec_ref(v___y_4406_);
lean_dec_ref(v_as_4402_);
return v_res_4415_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3(lean_object* v_as_4416_, size_t v_sz_4417_, size_t v_i_4418_, lean_object* v_b_4419_, lean_object* v___y_4420_, lean_object* v___y_4421_, lean_object* v___y_4422_, lean_object* v___y_4423_, lean_object* v___y_4424_, lean_object* v___y_4425_){
_start:
{
lean_object* v___x_4427_; 
v___x_4427_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___redArg(v_as_4416_, v_sz_4417_, v_i_4418_, v_b_4419_, v___y_4424_, v___y_4425_);
return v___x_4427_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___boxed(lean_object* v_as_4428_, lean_object* v_sz_4429_, lean_object* v_i_4430_, lean_object* v_b_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_){
_start:
{
size_t v_sz_boxed_4439_; size_t v_i_boxed_4440_; lean_object* v_res_4441_; 
v_sz_boxed_4439_ = lean_unbox_usize(v_sz_4429_);
lean_dec(v_sz_4429_);
v_i_boxed_4440_ = lean_unbox_usize(v_i_4430_);
lean_dec(v_i_4430_);
v_res_4441_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3(v_as_4428_, v_sz_boxed_4439_, v_i_boxed_4440_, v_b_4431_, v___y_4432_, v___y_4433_, v___y_4434_, v___y_4435_, v___y_4436_, v___y_4437_);
lean_dec(v___y_4437_);
lean_dec_ref(v___y_4436_);
lean_dec(v___y_4435_);
lean_dec_ref(v___y_4434_);
lean_dec(v___y_4433_);
lean_dec_ref(v___y_4432_);
lean_dec_ref(v_as_4428_);
return v_res_4441_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4(lean_object* v_as_4442_, size_t v_sz_4443_, size_t v_i_4444_, lean_object* v_b_4445_, lean_object* v___y_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_){
_start:
{
lean_object* v___x_4453_; 
v___x_4453_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4___redArg(v_as_4442_, v_sz_4443_, v_i_4444_, v_b_4445_, v___y_4448_, v___y_4449_, v___y_4450_, v___y_4451_);
return v___x_4453_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4___boxed(lean_object* v_as_4454_, lean_object* v_sz_4455_, lean_object* v_i_4456_, lean_object* v_b_4457_, lean_object* v___y_4458_, lean_object* v___y_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_, lean_object* v___y_4463_, lean_object* v___y_4464_){
_start:
{
size_t v_sz_boxed_4465_; size_t v_i_boxed_4466_; lean_object* v_res_4467_; 
v_sz_boxed_4465_ = lean_unbox_usize(v_sz_4455_);
lean_dec(v_sz_4455_);
v_i_boxed_4466_ = lean_unbox_usize(v_i_4456_);
lean_dec(v_i_4456_);
v_res_4467_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4(v_as_4454_, v_sz_boxed_4465_, v_i_boxed_4466_, v_b_4457_, v___y_4458_, v___y_4459_, v___y_4460_, v___y_4461_, v___y_4462_, v___y_4463_);
lean_dec(v___y_4463_);
lean_dec_ref(v___y_4462_);
lean_dec(v___y_4461_);
lean_dec_ref(v___y_4460_);
lean_dec(v___y_4459_);
lean_dec_ref(v___y_4458_);
lean_dec_ref(v_as_4454_);
return v_res_4467_;
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
