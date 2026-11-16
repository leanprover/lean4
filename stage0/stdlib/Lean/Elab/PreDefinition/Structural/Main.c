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
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__4;
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__5;
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
lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_173_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__0);
v___x_174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_174_, 0, v___x_173_);
lean_ctor_set(v___x_174_, 1, v___x_173_);
return v___x_174_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__4(void){
_start:
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_175_ = lean_unsigned_to_nat(0u);
v___x_176_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__0);
v___x_177_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_177_, 0, v___x_176_);
lean_ctor_set(v___x_177_, 1, v___x_176_);
lean_ctor_set(v___x_177_, 2, v___x_175_);
return v___x_177_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__5(void){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_178_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__4, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__4_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__4);
v___x_179_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__3);
v___x_180_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__0);
v___x_181_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__2);
v___x_182_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_182_, 0, v___x_181_);
lean_ctor_set(v___x_182_, 1, v___x_180_);
lean_ctor_set(v___x_182_, 2, v___x_179_);
lean_ctor_set(v___x_182_, 3, v___x_180_);
lean_ctor_set(v___x_182_, 4, v___x_180_);
lean_ctor_set(v___x_182_, 5, v___x_180_);
lean_ctor_set(v___x_182_, 6, v___x_180_);
lean_ctor_set(v___x_182_, 7, v___x_178_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg(lean_object* v_declName_183_, uint8_t v_s_184_, lean_object* v___y_185_, lean_object* v___y_186_){
_start:
{
lean_object* v___x_188_; lean_object* v_env_189_; lean_object* v_nextMacroScope_190_; lean_object* v_ngen_191_; lean_object* v_auxDeclNGen_192_; lean_object* v_traceState_193_; lean_object* v_recordedDeps_194_; lean_object* v_messages_195_; lean_object* v_infoState_196_; lean_object* v_snapshotTasks_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_226_; 
v___x_188_ = lean_st_ref_take(v___y_186_);
v_env_189_ = lean_ctor_get(v___x_188_, 0);
v_nextMacroScope_190_ = lean_ctor_get(v___x_188_, 1);
v_ngen_191_ = lean_ctor_get(v___x_188_, 2);
v_auxDeclNGen_192_ = lean_ctor_get(v___x_188_, 3);
v_traceState_193_ = lean_ctor_get(v___x_188_, 4);
v_recordedDeps_194_ = lean_ctor_get(v___x_188_, 6);
v_messages_195_ = lean_ctor_get(v___x_188_, 7);
v_infoState_196_ = lean_ctor_get(v___x_188_, 8);
v_snapshotTasks_197_ = lean_ctor_get(v___x_188_, 9);
v_isSharedCheck_226_ = !lean_is_exclusive(v___x_188_);
if (v_isSharedCheck_226_ == 0)
{
lean_object* v_unused_227_; 
v_unused_227_ = lean_ctor_get(v___x_188_, 5);
lean_dec(v_unused_227_);
v___x_199_ = v___x_188_;
v_isShared_200_ = v_isSharedCheck_226_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_snapshotTasks_197_);
lean_inc(v_infoState_196_);
lean_inc(v_messages_195_);
lean_inc(v_recordedDeps_194_);
lean_inc(v_traceState_193_);
lean_inc(v_auxDeclNGen_192_);
lean_inc(v_ngen_191_);
lean_inc(v_nextMacroScope_190_);
lean_inc(v_env_189_);
lean_dec(v___x_188_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_226_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
uint8_t v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_206_; 
v___x_201_ = 0;
v___x_202_ = lean_box(0);
v___x_203_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_189_, v_declName_183_, v_s_184_, v___x_201_, v___x_202_);
v___x_204_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__1);
if (v_isShared_200_ == 0)
{
lean_ctor_set(v___x_199_, 5, v___x_204_);
lean_ctor_set(v___x_199_, 0, v___x_203_);
v___x_206_ = v___x_199_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v___x_203_);
lean_ctor_set(v_reuseFailAlloc_225_, 1, v_nextMacroScope_190_);
lean_ctor_set(v_reuseFailAlloc_225_, 2, v_ngen_191_);
lean_ctor_set(v_reuseFailAlloc_225_, 3, v_auxDeclNGen_192_);
lean_ctor_set(v_reuseFailAlloc_225_, 4, v_traceState_193_);
lean_ctor_set(v_reuseFailAlloc_225_, 5, v___x_204_);
lean_ctor_set(v_reuseFailAlloc_225_, 6, v_recordedDeps_194_);
lean_ctor_set(v_reuseFailAlloc_225_, 7, v_messages_195_);
lean_ctor_set(v_reuseFailAlloc_225_, 8, v_infoState_196_);
lean_ctor_set(v_reuseFailAlloc_225_, 9, v_snapshotTasks_197_);
v___x_206_ = v_reuseFailAlloc_225_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v_mctx_209_; lean_object* v_zetaDeltaFVarIds_210_; lean_object* v_postponed_211_; lean_object* v_diag_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_223_; 
v___x_207_ = lean_st_ref_put(v___y_186_, v___x_206_);
v___x_208_ = lean_st_ref_take(v___y_185_);
v_mctx_209_ = lean_ctor_get(v___x_208_, 0);
v_zetaDeltaFVarIds_210_ = lean_ctor_get(v___x_208_, 2);
v_postponed_211_ = lean_ctor_get(v___x_208_, 3);
v_diag_212_ = lean_ctor_get(v___x_208_, 4);
v_isSharedCheck_223_ = !lean_is_exclusive(v___x_208_);
if (v_isSharedCheck_223_ == 0)
{
lean_object* v_unused_224_; 
v_unused_224_ = lean_ctor_get(v___x_208_, 1);
lean_dec(v_unused_224_);
v___x_214_ = v___x_208_;
v_isShared_215_ = v_isSharedCheck_223_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_diag_212_);
lean_inc(v_postponed_211_);
lean_inc(v_zetaDeltaFVarIds_210_);
lean_inc(v_mctx_209_);
lean_dec(v___x_208_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_223_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_219_; 
v___x_216_ = lean_box(0);
v___x_217_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__5, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__5_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__5);
if (v_isShared_215_ == 0)
{
lean_ctor_set(v___x_214_, 1, v___x_217_);
v___x_219_ = v___x_214_;
goto v_reusejp_218_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v_mctx_209_);
lean_ctor_set(v_reuseFailAlloc_222_, 1, v___x_217_);
lean_ctor_set(v_reuseFailAlloc_222_, 2, v_zetaDeltaFVarIds_210_);
lean_ctor_set(v_reuseFailAlloc_222_, 3, v_postponed_211_);
lean_ctor_set(v_reuseFailAlloc_222_, 4, v_diag_212_);
v___x_219_ = v_reuseFailAlloc_222_;
goto v_reusejp_218_;
}
v_reusejp_218_:
{
lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_220_ = lean_st_ref_put(v___y_185_, v___x_219_);
v___x_221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_221_, 0, v___x_216_);
return v___x_221_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___boxed(lean_object* v_declName_228_, lean_object* v_s_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_){
_start:
{
uint8_t v_s_boxed_233_; lean_object* v_res_234_; 
v_s_boxed_233_ = lean_unbox(v_s_229_);
v_res_234_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg(v_declName_228_, v_s_boxed_233_, v___y_230_, v___y_231_);
lean_dec(v___y_231_);
lean_dec(v___y_230_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18(lean_object* v_declName_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_){
_start:
{
uint8_t v___x_241_; lean_object* v___x_242_; 
v___x_241_ = 0;
v___x_242_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg(v_declName_235_, v___x_241_, v___y_237_, v___y_239_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___boxed(lean_object* v_declName_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18(v_declName_243_, v___y_244_, v___y_245_, v___y_246_, v___y_247_);
lean_dec(v___y_247_);
lean_dec_ref(v___y_246_);
lean_dec(v___y_245_);
lean_dec_ref(v___y_244_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16(size_t v_sz_250_, size_t v_i_251_, lean_object* v_bs_252_){
_start:
{
uint8_t v___x_253_; 
v___x_253_ = lean_usize_dec_lt(v_i_251_, v_sz_250_);
if (v___x_253_ == 0)
{
return v_bs_252_;
}
else
{
lean_object* v_v_254_; lean_object* v_declName_255_; lean_object* v___x_256_; lean_object* v_bs_x27_257_; size_t v___x_258_; size_t v___x_259_; lean_object* v___x_260_; 
v_v_254_ = lean_array_uget_borrowed(v_bs_252_, v_i_251_);
v_declName_255_ = lean_ctor_get(v_v_254_, 3);
lean_inc(v_declName_255_);
v___x_256_ = lean_unsigned_to_nat(0u);
v_bs_x27_257_ = lean_array_uset(v_bs_252_, v_i_251_, v___x_256_);
v___x_258_ = ((size_t)1ULL);
v___x_259_ = lean_usize_add(v_i_251_, v___x_258_);
v___x_260_ = lean_array_uset(v_bs_x27_257_, v_i_251_, v_declName_255_);
v_i_251_ = v___x_259_;
v_bs_252_ = v___x_260_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16___boxed(lean_object* v_sz_262_, lean_object* v_i_263_, lean_object* v_bs_264_){
_start:
{
size_t v_sz_boxed_265_; size_t v_i_boxed_266_; lean_object* v_res_267_; 
v_sz_boxed_265_ = lean_unbox_usize(v_sz_262_);
lean_dec(v_sz_262_);
v_i_boxed_266_ = lean_unbox_usize(v_i_263_);
lean_dec(v_i_263_);
v_res_267_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16(v_sz_boxed_265_, v_i_boxed_266_, v_bs_264_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___redArg(lean_object* v_preDefs_271_, lean_object* v_xs_272_, uint8_t v_a_273_, lean_object* v___x_274_, size_t v_sz_275_, size_t v_i_276_, lean_object* v_bs_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_){
_start:
{
uint8_t v___x_283_; 
v___x_283_ = lean_usize_dec_lt(v_i_276_, v_sz_275_);
if (v___x_283_ == 0)
{
lean_object* v___x_284_; 
lean_dec(v___x_274_);
lean_dec_ref(v_preDefs_271_);
v___x_284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_284_, 0, v_bs_277_);
return v___x_284_;
}
else
{
lean_object* v___x_285_; lean_object* v_v_286_; lean_object* v___x_287_; lean_object* v_bs_x27_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v_levelParams_291_; lean_object* v_modifiers_292_; lean_object* v_declName_293_; lean_object* v___x_294_; lean_object* v___x_295_; uint8_t v___x_296_; lean_object* v___x_297_; 
v___x_285_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v_v_286_ = lean_array_uget(v_bs_277_, v_i_276_);
v___x_287_ = lean_unsigned_to_nat(0u);
v_bs_x27_288_ = lean_array_uset(v_bs_277_, v_i_276_, v___x_287_);
v___x_289_ = lean_usize_to_nat(v_i_276_);
v___x_290_ = lean_array_get_borrowed(v___x_285_, v_preDefs_271_, v___x_289_);
lean_dec(v___x_289_);
v_levelParams_291_ = lean_ctor_get(v___x_290_, 1);
v_modifiers_292_ = lean_ctor_get(v___x_290_, 2);
v_declName_293_ = lean_ctor_get(v___x_290_, 3);
v___x_294_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___redArg___closed__1));
lean_inc(v_declName_293_);
v___x_295_ = l_Lean_Name_append(v_declName_293_, v___x_294_);
v___x_296_ = 1;
v___x_297_ = l_Lean_Meta_mkLambdaFVars(v_xs_272_, v_v_286_, v_a_273_, v___x_283_, v_a_273_, v___x_283_, v___x_296_, v___y_278_, v___y_279_, v___y_280_, v___y_281_);
if (lean_obj_tag(v___x_297_) == 0)
{
lean_object* v_a_298_; lean_object* v___x_299_; 
v_a_298_ = lean_ctor_get(v___x_297_, 0);
lean_inc(v_a_298_);
lean_dec_ref_known(v___x_297_, 1);
v___x_299_ = l_Lean_Elab_eraseRecAppSyntaxExpr(v_a_298_, v___y_280_, v___y_281_);
if (lean_obj_tag(v___x_299_) == 0)
{
lean_object* v_a_300_; size_t v_sz_301_; size_t v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v_a_300_ = lean_ctor_get(v___x_299_, 0);
lean_inc_n(v_a_300_, 2);
lean_dec_ref_known(v___x_299_, 1);
v_sz_301_ = lean_array_size(v_preDefs_271_);
v___x_302_ = ((size_t)0ULL);
lean_inc_ref(v_preDefs_271_);
v___x_303_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16(v_sz_301_, v___x_302_, v_preDefs_271_);
v___x_304_ = l_Lean_Elab_ensureNoRecFn(v___x_303_, v_a_300_, v___y_278_, v___y_279_, v___y_280_, v___y_281_);
if (lean_obj_tag(v___x_304_) == 0)
{
lean_object* v___x_305_; 
lean_dec_ref_known(v___x_304_, 1);
lean_inc(v___y_281_);
lean_inc_ref(v___y_280_);
lean_inc(v___y_279_);
lean_inc_ref(v___y_278_);
lean_inc(v_a_300_);
v___x_305_ = lean_infer_type(v_a_300_, v___y_278_, v___y_279_, v___y_280_, v___y_281_);
if (lean_obj_tag(v___x_305_) == 0)
{
lean_object* v_a_306_; lean_object* v___x_307_; 
v_a_306_ = lean_ctor_get(v___x_305_, 0);
lean_inc(v_a_306_);
lean_dec_ref_known(v___x_305_, 1);
v___x_307_ = l_Lean_Meta_letToHave(v_a_306_, v___y_278_, v___y_279_, v___y_280_, v___y_281_);
if (lean_obj_tag(v___x_307_) == 0)
{
lean_object* v_a_308_; lean_object* v___x_309_; lean_object* v_env_310_; uint8_t v_isUnsafe_311_; uint32_t v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; uint8_t v___y_316_; 
v_a_308_ = lean_ctor_get(v___x_307_, 0);
lean_inc(v_a_308_);
lean_dec_ref_known(v___x_307_, 1);
v___x_309_ = lean_st_ref_get(v___y_281_);
v_env_310_ = lean_ctor_get(v___x_309_, 0);
lean_inc_ref(v_env_310_);
lean_dec(v___x_309_);
v_isUnsafe_311_ = lean_ctor_get_uint8(v_modifiers_292_, sizeof(void*)*3 + 4);
lean_inc(v_a_300_);
v___x_312_ = l_Lean_getMaxHeight(v_env_310_, v_a_300_);
lean_inc(v_levelParams_291_);
lean_inc(v___x_295_);
v___x_313_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_313_, 0, v___x_295_);
lean_ctor_set(v___x_313_, 1, v_levelParams_291_);
lean_ctor_set(v___x_313_, 2, v_a_308_);
v___x_314_ = lean_box(1);
if (v_isUnsafe_311_ == 0)
{
uint8_t v___x_381_; 
v___x_381_ = 1;
v___y_316_ = v___x_381_;
goto v___jp_315_;
}
else
{
uint8_t v___x_382_; 
v___x_382_ = 0;
v___y_316_ = v___x_382_;
goto v___jp_315_;
}
v___jp_315_:
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_317_ = lean_box(0);
lean_inc(v___x_295_);
v___x_318_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_318_, 0, v___x_295_);
lean_ctor_set(v___x_318_, 1, v___x_317_);
v___x_319_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_319_, 0, v___x_313_);
lean_ctor_set(v___x_319_, 1, v_a_300_);
lean_ctor_set(v___x_319_, 2, v___x_314_);
lean_ctor_set(v___x_319_, 3, v___x_318_);
lean_ctor_set_uint8(v___x_319_, sizeof(void*)*4, v___y_316_);
v___x_320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_320_, 0, v___x_319_);
v___x_321_ = l_Lean_addDecl(v___x_320_, v_a_273_, v___y_280_, v___y_281_);
if (lean_obj_tag(v___x_321_) == 0)
{
lean_object* v___x_322_; lean_object* v_env_323_; lean_object* v_nextMacroScope_324_; lean_object* v_ngen_325_; lean_object* v_auxDeclNGen_326_; lean_object* v_traceState_327_; lean_object* v_recordedDeps_328_; lean_object* v_messages_329_; lean_object* v_infoState_330_; lean_object* v_snapshotTasks_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_371_; 
lean_dec_ref_known(v___x_321_, 1);
v___x_322_ = lean_st_ref_take(v___y_281_);
v_env_323_ = lean_ctor_get(v___x_322_, 0);
v_nextMacroScope_324_ = lean_ctor_get(v___x_322_, 1);
v_ngen_325_ = lean_ctor_get(v___x_322_, 2);
v_auxDeclNGen_326_ = lean_ctor_get(v___x_322_, 3);
v_traceState_327_ = lean_ctor_get(v___x_322_, 4);
v_recordedDeps_328_ = lean_ctor_get(v___x_322_, 6);
v_messages_329_ = lean_ctor_get(v___x_322_, 7);
v_infoState_330_ = lean_ctor_get(v___x_322_, 8);
v_snapshotTasks_331_ = lean_ctor_get(v___x_322_, 9);
v_isSharedCheck_371_ = !lean_is_exclusive(v___x_322_);
if (v_isSharedCheck_371_ == 0)
{
lean_object* v_unused_372_; 
v_unused_372_ = lean_ctor_get(v___x_322_, 5);
lean_dec(v_unused_372_);
v___x_333_ = v___x_322_;
v_isShared_334_ = v_isSharedCheck_371_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_snapshotTasks_331_);
lean_inc(v_infoState_330_);
lean_inc(v_messages_329_);
lean_inc(v_recordedDeps_328_);
lean_inc(v_traceState_327_);
lean_inc(v_auxDeclNGen_326_);
lean_inc(v_ngen_325_);
lean_inc(v_nextMacroScope_324_);
lean_inc(v_env_323_);
lean_dec(v___x_322_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_371_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_338_; 
lean_inc(v___x_295_);
v___x_335_ = l_Lean_setDefHeightOverride(v_env_323_, v___x_295_, v___x_312_);
v___x_336_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__1);
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 5, v___x_336_);
lean_ctor_set(v___x_333_, 0, v___x_335_);
v___x_338_ = v___x_333_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v___x_335_);
lean_ctor_set(v_reuseFailAlloc_370_, 1, v_nextMacroScope_324_);
lean_ctor_set(v_reuseFailAlloc_370_, 2, v_ngen_325_);
lean_ctor_set(v_reuseFailAlloc_370_, 3, v_auxDeclNGen_326_);
lean_ctor_set(v_reuseFailAlloc_370_, 4, v_traceState_327_);
lean_ctor_set(v_reuseFailAlloc_370_, 5, v___x_336_);
lean_ctor_set(v_reuseFailAlloc_370_, 6, v_recordedDeps_328_);
lean_ctor_set(v_reuseFailAlloc_370_, 7, v_messages_329_);
lean_ctor_set(v_reuseFailAlloc_370_, 8, v_infoState_330_);
lean_ctor_set(v_reuseFailAlloc_370_, 9, v_snapshotTasks_331_);
v___x_338_ = v_reuseFailAlloc_370_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v_mctx_341_; lean_object* v_zetaDeltaFVarIds_342_; lean_object* v_postponed_343_; lean_object* v_diag_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_368_; 
v___x_339_ = lean_st_ref_put(v___y_281_, v___x_338_);
v___x_340_ = lean_st_ref_take(v___y_279_);
v_mctx_341_ = lean_ctor_get(v___x_340_, 0);
v_zetaDeltaFVarIds_342_ = lean_ctor_get(v___x_340_, 2);
v_postponed_343_ = lean_ctor_get(v___x_340_, 3);
v_diag_344_ = lean_ctor_get(v___x_340_, 4);
v_isSharedCheck_368_ = !lean_is_exclusive(v___x_340_);
if (v_isSharedCheck_368_ == 0)
{
lean_object* v_unused_369_; 
v_unused_369_ = lean_ctor_get(v___x_340_, 1);
lean_dec(v_unused_369_);
v___x_346_ = v___x_340_;
v_isShared_347_ = v_isSharedCheck_368_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_diag_344_);
lean_inc(v_postponed_343_);
lean_inc(v_zetaDeltaFVarIds_342_);
lean_inc(v_mctx_341_);
lean_dec(v___x_340_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_368_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v___x_348_; lean_object* v___x_350_; 
v___x_348_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__5, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__5_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__5);
if (v_isShared_347_ == 0)
{
lean_ctor_set(v___x_346_, 1, v___x_348_);
v___x_350_ = v___x_346_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v_mctx_341_);
lean_ctor_set(v_reuseFailAlloc_367_, 1, v___x_348_);
lean_ctor_set(v_reuseFailAlloc_367_, 2, v_zetaDeltaFVarIds_342_);
lean_ctor_set(v_reuseFailAlloc_367_, 3, v_postponed_343_);
lean_ctor_set(v_reuseFailAlloc_367_, 4, v_diag_344_);
v___x_350_ = v_reuseFailAlloc_367_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_351_ = lean_st_ref_put(v___y_279_, v___x_350_);
lean_inc(v___x_295_);
v___x_352_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18(v___x_295_, v___y_278_, v___y_279_, v___y_280_, v___y_281_);
if (lean_obj_tag(v___x_352_) == 0)
{
lean_object* v___x_353_; lean_object* v___x_354_; size_t v___x_355_; size_t v___x_356_; lean_object* v___x_357_; 
lean_dec_ref_known(v___x_352_, 1);
lean_inc(v___x_274_);
v___x_353_ = l_Lean_mkConst(v___x_295_, v___x_274_);
v___x_354_ = l_Lean_mkAppN(v___x_353_, v_xs_272_);
v___x_355_ = ((size_t)1ULL);
v___x_356_ = lean_usize_add(v_i_276_, v___x_355_);
v___x_357_ = lean_array_uset(v_bs_x27_288_, v_i_276_, v___x_354_);
v_i_276_ = v___x_356_;
v_bs_277_ = v___x_357_;
goto _start;
}
else
{
lean_object* v_a_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_366_; 
lean_dec(v___x_295_);
lean_dec_ref(v_bs_x27_288_);
lean_dec(v___x_274_);
lean_dec_ref(v_preDefs_271_);
v_a_359_ = lean_ctor_get(v___x_352_, 0);
v_isSharedCheck_366_ = !lean_is_exclusive(v___x_352_);
if (v_isSharedCheck_366_ == 0)
{
v___x_361_ = v___x_352_;
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_a_359_);
lean_dec(v___x_352_);
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
}
}
}
else
{
lean_object* v_a_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_380_; 
lean_dec(v___x_295_);
lean_dec_ref(v_bs_x27_288_);
lean_dec(v___x_274_);
lean_dec_ref(v_preDefs_271_);
v_a_373_ = lean_ctor_get(v___x_321_, 0);
v_isSharedCheck_380_ = !lean_is_exclusive(v___x_321_);
if (v_isSharedCheck_380_ == 0)
{
v___x_375_ = v___x_321_;
v_isShared_376_ = v_isSharedCheck_380_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_a_373_);
lean_dec(v___x_321_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_380_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v___x_378_; 
if (v_isShared_376_ == 0)
{
v___x_378_ = v___x_375_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v_a_373_);
v___x_378_ = v_reuseFailAlloc_379_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
return v___x_378_;
}
}
}
}
}
else
{
lean_object* v_a_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_390_; 
lean_dec(v_a_300_);
lean_dec(v___x_295_);
lean_dec_ref(v_bs_x27_288_);
lean_dec(v___x_274_);
lean_dec_ref(v_preDefs_271_);
v_a_383_ = lean_ctor_get(v___x_307_, 0);
v_isSharedCheck_390_ = !lean_is_exclusive(v___x_307_);
if (v_isSharedCheck_390_ == 0)
{
v___x_385_ = v___x_307_;
v_isShared_386_ = v_isSharedCheck_390_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_a_383_);
lean_dec(v___x_307_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_390_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
lean_object* v___x_388_; 
if (v_isShared_386_ == 0)
{
v___x_388_ = v___x_385_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v_a_383_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
}
}
else
{
lean_object* v_a_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_398_; 
lean_dec(v_a_300_);
lean_dec(v___x_295_);
lean_dec_ref(v_bs_x27_288_);
lean_dec(v___x_274_);
lean_dec_ref(v_preDefs_271_);
v_a_391_ = lean_ctor_get(v___x_305_, 0);
v_isSharedCheck_398_ = !lean_is_exclusive(v___x_305_);
if (v_isSharedCheck_398_ == 0)
{
v___x_393_ = v___x_305_;
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_a_391_);
lean_dec(v___x_305_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
lean_object* v___x_396_; 
if (v_isShared_394_ == 0)
{
v___x_396_ = v___x_393_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v_a_391_);
v___x_396_ = v_reuseFailAlloc_397_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
return v___x_396_;
}
}
}
}
else
{
lean_object* v_a_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_406_; 
lean_dec(v_a_300_);
lean_dec(v___x_295_);
lean_dec_ref(v_bs_x27_288_);
lean_dec(v___x_274_);
lean_dec_ref(v_preDefs_271_);
v_a_399_ = lean_ctor_get(v___x_304_, 0);
v_isSharedCheck_406_ = !lean_is_exclusive(v___x_304_);
if (v_isSharedCheck_406_ == 0)
{
v___x_401_ = v___x_304_;
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_a_399_);
lean_dec(v___x_304_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v___x_404_; 
if (v_isShared_402_ == 0)
{
v___x_404_ = v___x_401_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v_a_399_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
}
}
else
{
lean_object* v_a_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_414_; 
lean_dec(v___x_295_);
lean_dec_ref(v_bs_x27_288_);
lean_dec(v___x_274_);
lean_dec_ref(v_preDefs_271_);
v_a_407_ = lean_ctor_get(v___x_299_, 0);
v_isSharedCheck_414_ = !lean_is_exclusive(v___x_299_);
if (v_isSharedCheck_414_ == 0)
{
v___x_409_ = v___x_299_;
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_a_407_);
lean_dec(v___x_299_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___x_412_; 
if (v_isShared_410_ == 0)
{
v___x_412_ = v___x_409_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_a_407_);
v___x_412_ = v_reuseFailAlloc_413_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
return v___x_412_;
}
}
}
}
else
{
lean_object* v_a_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_422_; 
lean_dec(v___x_295_);
lean_dec_ref(v_bs_x27_288_);
lean_dec(v___x_274_);
lean_dec_ref(v_preDefs_271_);
v_a_415_ = lean_ctor_get(v___x_297_, 0);
v_isSharedCheck_422_ = !lean_is_exclusive(v___x_297_);
if (v_isSharedCheck_422_ == 0)
{
v___x_417_ = v___x_297_;
v_isShared_418_ = v_isSharedCheck_422_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_a_415_);
lean_dec(v___x_297_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_422_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___x_420_; 
if (v_isShared_418_ == 0)
{
v___x_420_ = v___x_417_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v_a_415_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
return v___x_420_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___redArg___boxed(lean_object* v_preDefs_423_, lean_object* v_xs_424_, lean_object* v_a_425_, lean_object* v___x_426_, lean_object* v_sz_427_, lean_object* v_i_428_, lean_object* v_bs_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_){
_start:
{
uint8_t v_a_26748__boxed_435_; size_t v_sz_boxed_436_; size_t v_i_boxed_437_; lean_object* v_res_438_; 
v_a_26748__boxed_435_ = lean_unbox(v_a_425_);
v_sz_boxed_436_ = lean_unbox_usize(v_sz_427_);
lean_dec(v_sz_427_);
v_i_boxed_437_ = lean_unbox_usize(v_i_428_);
lean_dec(v_i_428_);
v_res_438_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___redArg(v_preDefs_423_, v_xs_424_, v_a_26748__boxed_435_, v___x_426_, v_sz_boxed_436_, v_i_boxed_437_, v_bs_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_);
lean_dec(v___y_433_);
lean_dec_ref(v___y_432_);
lean_dec(v___y_431_);
lean_dec_ref(v___y_430_);
lean_dec_ref(v_xs_424_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13(lean_object* v_as_439_, size_t v_i_440_, size_t v_stop_441_, lean_object* v_b_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_){
_start:
{
uint8_t v___x_448_; 
v___x_448_ = lean_usize_dec_eq(v_i_440_, v_stop_441_);
if (v___x_448_ == 0)
{
lean_object* v___x_20632__overap_449_; lean_object* v___x_450_; 
v___x_20632__overap_449_ = lean_array_uget_borrowed(v_as_439_, v_i_440_);
lean_inc(v___x_20632__overap_449_);
lean_inc(v___y_446_);
lean_inc_ref(v___y_445_);
lean_inc(v___y_444_);
lean_inc_ref(v___y_443_);
v___x_450_ = lean_apply_5(v___x_20632__overap_449_, v___y_443_, v___y_444_, v___y_445_, v___y_446_, lean_box(0));
if (lean_obj_tag(v___x_450_) == 0)
{
lean_object* v_a_451_; size_t v___x_452_; size_t v___x_453_; 
v_a_451_ = lean_ctor_get(v___x_450_, 0);
lean_inc(v_a_451_);
lean_dec_ref_known(v___x_450_, 1);
v___x_452_ = ((size_t)1ULL);
v___x_453_ = lean_usize_add(v_i_440_, v___x_452_);
v_i_440_ = v___x_453_;
v_b_442_ = v_a_451_;
goto _start;
}
else
{
return v___x_450_;
}
}
else
{
lean_object* v___x_455_; 
v___x_455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_455_, 0, v_b_442_);
return v___x_455_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13___boxed(lean_object* v_as_456_, lean_object* v_i_457_, lean_object* v_stop_458_, lean_object* v_b_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_){
_start:
{
size_t v_i_boxed_465_; size_t v_stop_boxed_466_; lean_object* v_res_467_; 
v_i_boxed_465_ = lean_unbox_usize(v_i_457_);
lean_dec(v_i_457_);
v_stop_boxed_466_ = lean_unbox_usize(v_stop_458_);
lean_dec(v_stop_458_);
v_res_467_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13(v_as_456_, v_i_boxed_465_, v_stop_boxed_466_, v_b_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_);
lean_dec(v___y_463_);
lean_dec_ref(v___y_462_);
lean_dec(v___y_461_);
lean_dec_ref(v___y_460_);
lean_dec_ref(v_as_456_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__24___redArg(lean_object* v_as_468_, size_t v_i_469_, size_t v_stop_470_, lean_object* v_b_471_, lean_object* v___y_472_, lean_object* v___y_473_){
_start:
{
uint8_t v___x_475_; 
v___x_475_ = lean_usize_dec_eq(v_i_469_, v_stop_470_);
if (v___x_475_ == 0)
{
lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_476_ = lean_array_uget_borrowed(v_as_468_, v_i_469_);
lean_inc(v___x_476_);
v___x_477_ = l_Lean_Elab_addAsAxiom___redArg(v___x_476_, v___y_472_, v___y_473_);
if (lean_obj_tag(v___x_477_) == 0)
{
lean_object* v_a_478_; size_t v___x_479_; size_t v___x_480_; 
v_a_478_ = lean_ctor_get(v___x_477_, 0);
lean_inc(v_a_478_);
lean_dec_ref_known(v___x_477_, 1);
v___x_479_ = ((size_t)1ULL);
v___x_480_ = lean_usize_add(v_i_469_, v___x_479_);
v_i_469_ = v___x_480_;
v_b_471_ = v_a_478_;
goto _start;
}
else
{
return v___x_477_;
}
}
else
{
lean_object* v___x_482_; 
v___x_482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_482_, 0, v_b_471_);
return v___x_482_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__24___redArg___boxed(lean_object* v_as_483_, lean_object* v_i_484_, lean_object* v_stop_485_, lean_object* v_b_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_){
_start:
{
size_t v_i_boxed_490_; size_t v_stop_boxed_491_; lean_object* v_res_492_; 
v_i_boxed_490_ = lean_unbox_usize(v_i_484_);
lean_dec(v_i_484_);
v_stop_boxed_491_ = lean_unbox_usize(v_stop_485_);
lean_dec(v_stop_485_);
v_res_492_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__24___redArg(v_as_483_, v_i_boxed_490_, v_stop_boxed_491_, v_b_486_, v___y_487_, v___y_488_);
lean_dec(v___y_488_);
lean_dec_ref(v___y_487_);
lean_dec_ref(v_as_483_);
return v_res_492_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__24(lean_object* v_as_493_, size_t v_i_494_, size_t v_stop_495_, lean_object* v_b_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_){
_start:
{
lean_object* v___x_502_; 
v___x_502_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__24___redArg(v_as_493_, v_i_494_, v_stop_495_, v_b_496_, v___y_499_, v___y_500_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__24___boxed(lean_object* v_as_503_, lean_object* v_i_504_, lean_object* v_stop_505_, lean_object* v_b_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_){
_start:
{
size_t v_i_boxed_512_; size_t v_stop_boxed_513_; lean_object* v_res_514_; 
v_i_boxed_512_ = lean_unbox_usize(v_i_504_);
lean_dec(v_i_504_);
v_stop_boxed_513_ = lean_unbox_usize(v_stop_505_);
lean_dec(v_stop_505_);
v_res_514_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__24(v_as_503_, v_i_boxed_512_, v_stop_boxed_513_, v_b_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_);
lean_dec(v___y_510_);
lean_dec_ref(v___y_509_);
lean_dec(v___y_508_);
lean_dec_ref(v___y_507_);
lean_dec_ref(v_as_503_);
return v_res_514_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg(lean_object* v_env_515_, lean_object* v___y_516_, lean_object* v___y_517_){
_start:
{
lean_object* v___x_519_; lean_object* v_nextMacroScope_520_; lean_object* v_ngen_521_; lean_object* v_auxDeclNGen_522_; lean_object* v_traceState_523_; lean_object* v_recordedDeps_524_; lean_object* v_messages_525_; lean_object* v_infoState_526_; lean_object* v_snapshotTasks_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_553_; 
v___x_519_ = lean_st_ref_take(v___y_517_);
v_nextMacroScope_520_ = lean_ctor_get(v___x_519_, 1);
v_ngen_521_ = lean_ctor_get(v___x_519_, 2);
v_auxDeclNGen_522_ = lean_ctor_get(v___x_519_, 3);
v_traceState_523_ = lean_ctor_get(v___x_519_, 4);
v_recordedDeps_524_ = lean_ctor_get(v___x_519_, 6);
v_messages_525_ = lean_ctor_get(v___x_519_, 7);
v_infoState_526_ = lean_ctor_get(v___x_519_, 8);
v_snapshotTasks_527_ = lean_ctor_get(v___x_519_, 9);
v_isSharedCheck_553_ = !lean_is_exclusive(v___x_519_);
if (v_isSharedCheck_553_ == 0)
{
lean_object* v_unused_554_; lean_object* v_unused_555_; 
v_unused_554_ = lean_ctor_get(v___x_519_, 5);
lean_dec(v_unused_554_);
v_unused_555_ = lean_ctor_get(v___x_519_, 0);
lean_dec(v_unused_555_);
v___x_529_ = v___x_519_;
v_isShared_530_ = v_isSharedCheck_553_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_snapshotTasks_527_);
lean_inc(v_infoState_526_);
lean_inc(v_messages_525_);
lean_inc(v_recordedDeps_524_);
lean_inc(v_traceState_523_);
lean_inc(v_auxDeclNGen_522_);
lean_inc(v_ngen_521_);
lean_inc(v_nextMacroScope_520_);
lean_dec(v___x_519_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_553_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v___x_531_; lean_object* v___x_533_; 
v___x_531_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__1);
if (v_isShared_530_ == 0)
{
lean_ctor_set(v___x_529_, 5, v___x_531_);
lean_ctor_set(v___x_529_, 0, v_env_515_);
v___x_533_ = v___x_529_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v_env_515_);
lean_ctor_set(v_reuseFailAlloc_552_, 1, v_nextMacroScope_520_);
lean_ctor_set(v_reuseFailAlloc_552_, 2, v_ngen_521_);
lean_ctor_set(v_reuseFailAlloc_552_, 3, v_auxDeclNGen_522_);
lean_ctor_set(v_reuseFailAlloc_552_, 4, v_traceState_523_);
lean_ctor_set(v_reuseFailAlloc_552_, 5, v___x_531_);
lean_ctor_set(v_reuseFailAlloc_552_, 6, v_recordedDeps_524_);
lean_ctor_set(v_reuseFailAlloc_552_, 7, v_messages_525_);
lean_ctor_set(v_reuseFailAlloc_552_, 8, v_infoState_526_);
lean_ctor_set(v_reuseFailAlloc_552_, 9, v_snapshotTasks_527_);
v___x_533_ = v_reuseFailAlloc_552_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v_mctx_536_; lean_object* v_zetaDeltaFVarIds_537_; lean_object* v_postponed_538_; lean_object* v_diag_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_550_; 
v___x_534_ = lean_st_ref_put(v___y_517_, v___x_533_);
v___x_535_ = lean_st_ref_take(v___y_516_);
v_mctx_536_ = lean_ctor_get(v___x_535_, 0);
v_zetaDeltaFVarIds_537_ = lean_ctor_get(v___x_535_, 2);
v_postponed_538_ = lean_ctor_get(v___x_535_, 3);
v_diag_539_ = lean_ctor_get(v___x_535_, 4);
v_isSharedCheck_550_ = !lean_is_exclusive(v___x_535_);
if (v_isSharedCheck_550_ == 0)
{
lean_object* v_unused_551_; 
v_unused_551_ = lean_ctor_get(v___x_535_, 1);
lean_dec(v_unused_551_);
v___x_541_ = v___x_535_;
v_isShared_542_ = v_isSharedCheck_550_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_diag_539_);
lean_inc(v_postponed_538_);
lean_inc(v_zetaDeltaFVarIds_537_);
lean_inc(v_mctx_536_);
lean_dec(v___x_535_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_550_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_546_; 
v___x_543_ = lean_box(0);
v___x_544_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__5, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__5_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__5);
if (v_isShared_542_ == 0)
{
lean_ctor_set(v___x_541_, 1, v___x_544_);
v___x_546_ = v___x_541_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v_mctx_536_);
lean_ctor_set(v_reuseFailAlloc_549_, 1, v___x_544_);
lean_ctor_set(v_reuseFailAlloc_549_, 2, v_zetaDeltaFVarIds_537_);
lean_ctor_set(v_reuseFailAlloc_549_, 3, v_postponed_538_);
lean_ctor_set(v_reuseFailAlloc_549_, 4, v_diag_539_);
v___x_546_ = v_reuseFailAlloc_549_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_547_ = lean_st_ref_put(v___y_516_, v___x_546_);
v___x_548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_548_, 0, v___x_543_);
return v___x_548_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___boxed(lean_object* v_env_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg(v_env_556_, v___y_557_, v___y_558_);
lean_dec(v___y_558_);
lean_dec(v___y_557_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23___redArg(lean_object* v_env_561_, lean_object* v_x_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_){
_start:
{
lean_object* v___x_568_; lean_object* v_env_569_; lean_object* v_a_571_; lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_568_ = lean_st_ref_get(v___y_566_);
v_env_569_ = lean_ctor_get(v___x_568_, 0);
lean_inc_ref(v_env_569_);
lean_dec(v___x_568_);
v___x_581_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg(v_env_561_, v___y_564_, v___y_566_);
lean_dec_ref(v___x_581_);
lean_inc(v___y_566_);
lean_inc_ref(v___y_565_);
lean_inc(v___y_564_);
lean_inc_ref(v___y_563_);
v___x_582_ = lean_apply_5(v_x_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, lean_box(0));
if (lean_obj_tag(v___x_582_) == 0)
{
lean_object* v_a_583_; lean_object* v___x_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_591_; 
v_a_583_ = lean_ctor_get(v___x_582_, 0);
lean_inc(v_a_583_);
lean_dec_ref_known(v___x_582_, 1);
v___x_584_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg(v_env_569_, v___y_564_, v___y_566_);
v_isSharedCheck_591_ = !lean_is_exclusive(v___x_584_);
if (v_isSharedCheck_591_ == 0)
{
lean_object* v_unused_592_; 
v_unused_592_ = lean_ctor_get(v___x_584_, 0);
lean_dec(v_unused_592_);
v___x_586_ = v___x_584_;
v_isShared_587_ = v_isSharedCheck_591_;
goto v_resetjp_585_;
}
else
{
lean_dec(v___x_584_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_591_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_589_; 
if (v_isShared_587_ == 0)
{
lean_ctor_set(v___x_586_, 0, v_a_583_);
v___x_589_ = v___x_586_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v_a_583_);
v___x_589_ = v_reuseFailAlloc_590_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
return v___x_589_;
}
}
}
else
{
lean_object* v_a_593_; 
v_a_593_ = lean_ctor_get(v___x_582_, 0);
lean_inc(v_a_593_);
lean_dec_ref_known(v___x_582_, 1);
v_a_571_ = v_a_593_;
goto v___jp_570_;
}
v___jp_570_:
{
lean_object* v___x_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_579_; 
v___x_572_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg(v_env_569_, v___y_564_, v___y_566_);
v_isSharedCheck_579_ = !lean_is_exclusive(v___x_572_);
if (v_isSharedCheck_579_ == 0)
{
lean_object* v_unused_580_; 
v_unused_580_ = lean_ctor_get(v___x_572_, 0);
lean_dec(v_unused_580_);
v___x_574_ = v___x_572_;
v_isShared_575_ = v_isSharedCheck_579_;
goto v_resetjp_573_;
}
else
{
lean_dec(v___x_572_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_579_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v___x_577_; 
if (v_isShared_575_ == 0)
{
lean_ctor_set_tag(v___x_574_, 1);
lean_ctor_set(v___x_574_, 0, v_a_571_);
v___x_577_ = v___x_574_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v_a_571_);
v___x_577_ = v_reuseFailAlloc_578_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
return v___x_577_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23___redArg___boxed(lean_object* v_env_594_, lean_object* v_x_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23___redArg(v_env_594_, v_x_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_);
lean_dec(v___y_599_);
lean_dec_ref(v___y_598_);
lean_dec(v___y_597_);
lean_dec_ref(v___y_596_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___lam__1(lean_object* v___x_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_){
_start:
{
lean_object* v___x_608_; 
v___x_608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_608_, 0, v___x_602_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___lam__1___boxed(lean_object* v___x_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_){
_start:
{
lean_object* v_res_615_; 
v_res_615_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___lam__1(v___x_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_);
lean_dec(v___y_613_);
lean_dec_ref(v___y_612_);
lean_dec(v___y_611_);
lean_dec_ref(v___y_610_);
return v_res_615_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___lam__0(lean_object* v___y_616_, lean_object* v_k_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_){
_start:
{
lean_object* v___x_623_; 
lean_inc(v___y_621_);
lean_inc_ref(v___y_620_);
lean_inc(v___y_619_);
lean_inc_ref(v___y_618_);
v___x_623_ = lean_apply_5(v___y_616_, v___y_618_, v___y_619_, v___y_620_, v___y_621_, lean_box(0));
if (lean_obj_tag(v___x_623_) == 0)
{
lean_object* v___x_624_; 
lean_dec_ref_known(v___x_623_, 1);
v___x_624_ = lean_apply_5(v_k_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_, lean_box(0));
return v___x_624_;
}
else
{
lean_object* v_a_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_632_; 
lean_dec(v___y_621_);
lean_dec_ref(v___y_620_);
lean_dec(v___y_619_);
lean_dec_ref(v___y_618_);
lean_dec_ref(v_k_617_);
v_a_625_ = lean_ctor_get(v___x_623_, 0);
v_isSharedCheck_632_ = !lean_is_exclusive(v___x_623_);
if (v_isSharedCheck_632_ == 0)
{
v___x_627_ = v___x_623_;
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_a_625_);
lean_dec(v___x_623_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_630_; 
if (v_isShared_628_ == 0)
{
v___x_630_ = v___x_627_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v_a_625_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___lam__0___boxed(lean_object* v___y_633_, lean_object* v_k_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___lam__0(v___y_633_, v_k_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(lean_object* v_preDefs_645_, lean_object* v_k_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_){
_start:
{
lean_object* v___y_653_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; uint8_t v___x_662_; 
v___x_659_ = lean_unsigned_to_nat(0u);
v___x_660_ = lean_array_get_size(v_preDefs_645_);
v___x_661_ = lean_box(0);
v___x_662_ = lean_nat_dec_lt(v___x_659_, v___x_660_);
if (v___x_662_ == 0)
{
lean_object* v___f_663_; 
lean_dec_ref(v_preDefs_645_);
v___f_663_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___closed__0));
v___y_653_ = v___f_663_;
goto v___jp_652_;
}
else
{
size_t v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_664_ = lean_usize_of_nat(v___x_660_);
v___x_665_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___boxed__const__1));
v___x_666_ = lean_box_usize(v___x_664_);
v___x_667_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__24___boxed), 9, 4);
lean_closure_set(v___x_667_, 0, v_preDefs_645_);
lean_closure_set(v___x_667_, 1, v___x_665_);
lean_closure_set(v___x_667_, 2, v___x_666_);
lean_closure_set(v___x_667_, 3, v___x_661_);
v___y_653_ = v___x_667_;
goto v___jp_652_;
}
v___jp_652_:
{
lean_object* v___f_654_; lean_object* v___x_655_; lean_object* v_env_656_; lean_object* v___x_657_; lean_object* v___x_658_; 
v___f_654_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_654_, 0, v___y_653_);
lean_closure_set(v___f_654_, 1, v_k_646_);
v___x_655_ = lean_st_ref_get(v___y_650_);
v_env_656_ = lean_ctor_get(v___x_655_, 0);
lean_inc_ref(v_env_656_);
lean_dec(v___x_655_);
v___x_657_ = l_Lean_Environment_unlockAsync(v_env_656_);
v___x_658_ = l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23___redArg(v___x_657_, v___f_654_, v___y_647_, v___y_648_, v___y_649_, v___y_650_);
return v___x_658_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___boxed(lean_object* v_preDefs_668_, lean_object* v_k_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_){
_start:
{
lean_object* v_res_675_; 
v_res_675_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v_preDefs_668_, v_k_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_);
lean_dec(v___y_673_);
lean_dec_ref(v___y_672_);
lean_dec(v___y_671_);
lean_dec_ref(v___y_670_);
return v_res_675_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg___closed__0(void){
_start:
{
lean_object* v___x_676_; lean_object* v_dummy_677_; 
v___x_676_ = lean_box(0);
v_dummy_677_ = l_Lean_Expr_sort___override(v___x_676_);
return v_dummy_677_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg(uint8_t v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_recArgInfos_681_, lean_object* v___x_682_, lean_object* v_preDefs_683_, lean_object* v_a_684_, size_t v_sz_685_, size_t v_i_686_, lean_object* v_bs_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_){
_start:
{
uint8_t v___x_693_; 
v___x_693_ = lean_usize_dec_lt(v_i_686_, v_sz_685_);
if (v___x_693_ == 0)
{
lean_object* v___x_694_; 
lean_dec_ref(v_a_684_);
lean_dec_ref(v_preDefs_683_);
lean_dec_ref(v___x_682_);
lean_dec_ref(v_recArgInfos_681_);
v___x_694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_694_, 0, v_bs_687_);
return v___x_694_;
}
else
{
lean_object* v___x_695_; lean_object* v_v_696_; lean_object* v___x_697_; lean_object* v_bs_x27_698_; lean_object* v_a_700_; lean_object* v___x_705_; 
v___x_695_ = l_Lean_instInhabitedExpr;
v_v_696_ = lean_array_uget(v_bs_687_, v_i_686_);
v___x_697_ = lean_unsigned_to_nat(0u);
v_bs_x27_698_ = lean_array_uset(v_bs_687_, v_i_686_, v___x_697_);
v___x_705_ = lean_usize_to_nat(v_i_686_);
if (v_a_678_ == 0)
{
lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_706_ = lean_array_get_borrowed(v___x_695_, v_a_679_, v___x_705_);
v___x_707_ = lean_array_get_borrowed(v___x_695_, v_a_680_, v___x_705_);
lean_dec(v___x_705_);
lean_inc(v___x_707_);
lean_inc(v___x_706_);
lean_inc_ref(v___x_682_);
lean_inc_ref(v_recArgInfos_681_);
v___x_708_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnF___boxed), 10, 5);
lean_closure_set(v___x_708_, 0, v_recArgInfos_681_);
lean_closure_set(v___x_708_, 1, v___x_682_);
lean_closure_set(v___x_708_, 2, v_v_696_);
lean_closure_set(v___x_708_, 3, v___x_706_);
lean_closure_set(v___x_708_, 4, v___x_707_);
lean_inc_ref(v_preDefs_683_);
v___x_709_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v_preDefs_683_, v___x_708_, v___y_688_, v___y_689_, v___y_690_, v___y_691_);
if (lean_obj_tag(v___x_709_) == 0)
{
lean_object* v_a_710_; 
v_a_710_ = lean_ctor_get(v___x_709_, 0);
lean_inc(v_a_710_);
lean_dec_ref_known(v___x_709_, 1);
v_a_700_ = v_a_710_;
goto v___jp_699_;
}
else
{
lean_object* v_a_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_718_; 
lean_dec_ref(v_bs_x27_698_);
lean_dec_ref(v_a_684_);
lean_dec_ref(v_preDefs_683_);
lean_dec_ref(v___x_682_);
lean_dec_ref(v_recArgInfos_681_);
v_a_711_ = lean_ctor_get(v___x_709_, 0);
v_isSharedCheck_718_ = !lean_is_exclusive(v___x_709_);
if (v_isSharedCheck_718_ == 0)
{
v___x_713_ = v___x_709_;
v_isShared_714_ = v_isSharedCheck_718_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_a_711_);
lean_dec(v___x_709_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_718_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v___x_716_; 
if (v_isShared_714_ == 0)
{
v___x_716_ = v___x_713_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v_a_711_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
}
}
else
{
lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v_dummy_722_; lean_object* v_nargs_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_719_ = lean_array_get_borrowed(v___x_695_, v_a_679_, v___x_705_);
v___x_720_ = lean_array_get_borrowed(v___x_695_, v_a_680_, v___x_705_);
lean_dec(v___x_705_);
lean_inc_ref(v_a_684_);
v___x_721_ = lean_apply_1(v_a_684_, v___x_697_);
v_dummy_722_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg___closed__0);
v_nargs_723_ = l_Lean_Expr_getAppNumArgs(v___x_721_);
lean_inc(v_nargs_723_);
v___x_724_ = lean_mk_array(v_nargs_723_, v_dummy_722_);
v___x_725_ = lean_unsigned_to_nat(1u);
v___x_726_ = lean_nat_sub(v_nargs_723_, v___x_725_);
lean_dec(v_nargs_723_);
v___x_727_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___x_721_, v___x_724_, v___x_726_);
lean_inc(v___x_720_);
lean_inc(v___x_719_);
lean_inc_ref(v___x_682_);
lean_inc_ref(v_recArgInfos_681_);
v___x_728_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkIndPredBRecOnF___boxed), 11, 6);
lean_closure_set(v___x_728_, 0, v_recArgInfos_681_);
lean_closure_set(v___x_728_, 1, v___x_682_);
lean_closure_set(v___x_728_, 2, v_v_696_);
lean_closure_set(v___x_728_, 3, v___x_719_);
lean_closure_set(v___x_728_, 4, v___x_720_);
lean_closure_set(v___x_728_, 5, v___x_727_);
lean_inc_ref(v_preDefs_683_);
v___x_729_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v_preDefs_683_, v___x_728_, v___y_688_, v___y_689_, v___y_690_, v___y_691_);
if (lean_obj_tag(v___x_729_) == 0)
{
lean_object* v_a_730_; lean_object* v_fst_731_; lean_object* v_snd_732_; lean_object* v___x_733_; uint8_t v___x_734_; 
v_a_730_ = lean_ctor_get(v___x_729_, 0);
lean_inc(v_a_730_);
lean_dec_ref_known(v___x_729_, 1);
v_fst_731_ = lean_ctor_get(v_a_730_, 0);
lean_inc(v_fst_731_);
v_snd_732_ = lean_ctor_get(v_a_730_, 1);
lean_inc(v_snd_732_);
lean_dec(v_a_730_);
v___x_733_ = lean_array_get_size(v_snd_732_);
v___x_734_ = lean_nat_dec_lt(v___x_697_, v___x_733_);
if (v___x_734_ == 0)
{
lean_dec(v_snd_732_);
v_a_700_ = v_fst_731_;
goto v___jp_699_;
}
else
{
lean_object* v___x_735_; size_t v___x_736_; size_t v___x_737_; lean_object* v___x_738_; 
v___x_735_ = lean_box(0);
v___x_736_ = ((size_t)0ULL);
v___x_737_ = lean_usize_of_nat(v___x_733_);
v___x_738_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13(v_snd_732_, v___x_736_, v___x_737_, v___x_735_, v___y_688_, v___y_689_, v___y_690_, v___y_691_);
lean_dec(v_snd_732_);
if (lean_obj_tag(v___x_738_) == 0)
{
lean_dec_ref_known(v___x_738_, 1);
v_a_700_ = v_fst_731_;
goto v___jp_699_;
}
else
{
lean_object* v_a_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_746_; 
lean_dec(v_fst_731_);
lean_dec_ref(v_bs_x27_698_);
lean_dec_ref(v_a_684_);
lean_dec_ref(v_preDefs_683_);
lean_dec_ref(v___x_682_);
lean_dec_ref(v_recArgInfos_681_);
v_a_739_ = lean_ctor_get(v___x_738_, 0);
v_isSharedCheck_746_ = !lean_is_exclusive(v___x_738_);
if (v_isSharedCheck_746_ == 0)
{
v___x_741_ = v___x_738_;
v_isShared_742_ = v_isSharedCheck_746_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_a_739_);
lean_dec(v___x_738_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_746_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v___x_744_; 
if (v_isShared_742_ == 0)
{
v___x_744_ = v___x_741_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_a_739_);
v___x_744_ = v_reuseFailAlloc_745_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
return v___x_744_;
}
}
}
}
}
else
{
lean_object* v_a_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_754_; 
lean_dec_ref(v_bs_x27_698_);
lean_dec_ref(v_a_684_);
lean_dec_ref(v_preDefs_683_);
lean_dec_ref(v___x_682_);
lean_dec_ref(v_recArgInfos_681_);
v_a_747_ = lean_ctor_get(v___x_729_, 0);
v_isSharedCheck_754_ = !lean_is_exclusive(v___x_729_);
if (v_isSharedCheck_754_ == 0)
{
v___x_749_ = v___x_729_;
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_a_747_);
lean_dec(v___x_729_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___x_752_; 
if (v_isShared_750_ == 0)
{
v___x_752_ = v___x_749_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v_a_747_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
return v___x_752_;
}
}
}
}
v___jp_699_:
{
size_t v___x_701_; size_t v___x_702_; lean_object* v___x_703_; 
v___x_701_ = ((size_t)1ULL);
v___x_702_ = lean_usize_add(v_i_686_, v___x_701_);
v___x_703_ = lean_array_uset(v_bs_x27_698_, v_i_686_, v_a_700_);
v_i_686_ = v___x_702_;
v_bs_687_ = v___x_703_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg___boxed(lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_recArgInfos_758_, lean_object* v___x_759_, lean_object* v_preDefs_760_, lean_object* v_a_761_, lean_object* v_sz_762_, lean_object* v_i_763_, lean_object* v_bs_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_){
_start:
{
uint8_t v_a_27362__boxed_770_; size_t v_sz_boxed_771_; size_t v_i_boxed_772_; lean_object* v_res_773_; 
v_a_27362__boxed_770_ = lean_unbox(v_a_755_);
v_sz_boxed_771_ = lean_unbox_usize(v_sz_762_);
lean_dec(v_sz_762_);
v_i_boxed_772_ = lean_unbox_usize(v_i_763_);
lean_dec(v_i_763_);
v_res_773_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg(v_a_27362__boxed_770_, v_a_756_, v_a_757_, v_recArgInfos_758_, v___x_759_, v_preDefs_760_, v_a_761_, v_sz_boxed_771_, v_i_boxed_772_, v_bs_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_);
lean_dec(v___y_768_);
lean_dec_ref(v___y_767_);
lean_dec(v___y_766_);
lean_dec_ref(v___y_765_);
lean_dec_ref(v_a_757_);
lean_dec_ref(v_a_756_);
return v_res_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11_spec__21(lean_object* v_msgData_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_){
_start:
{
lean_object* v___x_780_; lean_object* v_env_781_; uint8_t v___x_782_; lean_object* v_env_783_; lean_object* v___x_784_; lean_object* v_toCold_785_; lean_object* v_mctx_786_; lean_object* v_lctx_787_; lean_object* v_options_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_780_ = lean_st_ref_get(v___y_778_);
v_env_781_ = lean_ctor_get(v___x_780_, 0);
lean_inc_ref(v_env_781_);
lean_dec(v___x_780_);
v___x_782_ = 0;
v_env_783_ = l_Lean_Environment_setRecordingDeps(v_env_781_, v___x_782_);
v___x_784_ = lean_st_ref_get(v___y_776_);
v_toCold_785_ = lean_ctor_get(v___y_777_, 0);
v_mctx_786_ = lean_ctor_get(v___x_784_, 0);
lean_inc_ref(v_mctx_786_);
lean_dec(v___x_784_);
v_lctx_787_ = lean_ctor_get(v___y_775_, 2);
v_options_788_ = lean_ctor_get(v_toCold_785_, 2);
lean_inc_ref(v_options_788_);
lean_inc_ref(v_lctx_787_);
v___x_789_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_789_, 0, v_env_783_);
lean_ctor_set(v___x_789_, 1, v_mctx_786_);
lean_ctor_set(v___x_789_, 2, v_lctx_787_);
lean_ctor_set(v___x_789_, 3, v_options_788_);
v___x_790_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_790_, 0, v___x_789_);
lean_ctor_set(v___x_790_, 1, v_msgData_774_);
v___x_791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_791_, 0, v___x_790_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11_spec__21___boxed(lean_object* v_msgData_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_){
_start:
{
lean_object* v_res_798_; 
v_res_798_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11_spec__21(v_msgData_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_);
lean_dec(v___y_796_);
lean_dec_ref(v___y_795_);
lean_dec(v___y_794_);
lean_dec_ref(v___y_793_);
return v_res_798_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___closed__0(void){
_start:
{
lean_object* v___x_799_; double v___x_800_; 
v___x_799_ = lean_unsigned_to_nat(0u);
v___x_800_ = lean_float_of_nat(v___x_799_);
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(lean_object* v_cls_804_, lean_object* v_msg_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_){
_start:
{
lean_object* v_ref_811_; lean_object* v___x_812_; lean_object* v_a_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_858_; 
v_ref_811_ = lean_ctor_get(v___y_808_, 2);
v___x_812_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11_spec__21(v_msg_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_);
v_a_813_ = lean_ctor_get(v___x_812_, 0);
v_isSharedCheck_858_ = !lean_is_exclusive(v___x_812_);
if (v_isSharedCheck_858_ == 0)
{
v___x_815_ = v___x_812_;
v_isShared_816_ = v_isSharedCheck_858_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_a_813_);
lean_dec(v___x_812_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_858_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v___x_817_; lean_object* v_traceState_818_; lean_object* v_env_819_; lean_object* v_nextMacroScope_820_; lean_object* v_ngen_821_; lean_object* v_auxDeclNGen_822_; lean_object* v_cache_823_; lean_object* v_recordedDeps_824_; lean_object* v_messages_825_; lean_object* v_infoState_826_; lean_object* v_snapshotTasks_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_857_; 
v___x_817_ = lean_st_ref_take(v___y_809_);
v_traceState_818_ = lean_ctor_get(v___x_817_, 4);
v_env_819_ = lean_ctor_get(v___x_817_, 0);
v_nextMacroScope_820_ = lean_ctor_get(v___x_817_, 1);
v_ngen_821_ = lean_ctor_get(v___x_817_, 2);
v_auxDeclNGen_822_ = lean_ctor_get(v___x_817_, 3);
v_cache_823_ = lean_ctor_get(v___x_817_, 5);
v_recordedDeps_824_ = lean_ctor_get(v___x_817_, 6);
v_messages_825_ = lean_ctor_get(v___x_817_, 7);
v_infoState_826_ = lean_ctor_get(v___x_817_, 8);
v_snapshotTasks_827_ = lean_ctor_get(v___x_817_, 9);
v_isSharedCheck_857_ = !lean_is_exclusive(v___x_817_);
if (v_isSharedCheck_857_ == 0)
{
v___x_829_ = v___x_817_;
v_isShared_830_ = v_isSharedCheck_857_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_snapshotTasks_827_);
lean_inc(v_infoState_826_);
lean_inc(v_messages_825_);
lean_inc(v_recordedDeps_824_);
lean_inc(v_cache_823_);
lean_inc(v_traceState_818_);
lean_inc(v_auxDeclNGen_822_);
lean_inc(v_ngen_821_);
lean_inc(v_nextMacroScope_820_);
lean_inc(v_env_819_);
lean_dec(v___x_817_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_857_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
uint64_t v_tid_831_; lean_object* v_traces_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_856_; 
v_tid_831_ = lean_ctor_get_uint64(v_traceState_818_, sizeof(void*)*1);
v_traces_832_ = lean_ctor_get(v_traceState_818_, 0);
v_isSharedCheck_856_ = !lean_is_exclusive(v_traceState_818_);
if (v_isSharedCheck_856_ == 0)
{
v___x_834_ = v_traceState_818_;
v_isShared_835_ = v_isSharedCheck_856_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_traces_832_);
lean_dec(v_traceState_818_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_856_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v___x_836_; lean_object* v___x_837_; double v___x_838_; uint8_t v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_847_; 
v___x_836_ = lean_box(0);
v___x_837_ = lean_box(0);
v___x_838_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___closed__0);
v___x_839_ = 0;
v___x_840_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___closed__1));
v___x_841_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_841_, 0, v_cls_804_);
lean_ctor_set(v___x_841_, 1, v___x_837_);
lean_ctor_set(v___x_841_, 2, v___x_840_);
lean_ctor_set_float(v___x_841_, sizeof(void*)*3, v___x_838_);
lean_ctor_set_float(v___x_841_, sizeof(void*)*3 + 8, v___x_838_);
lean_ctor_set_uint8(v___x_841_, sizeof(void*)*3 + 16, v___x_839_);
v___x_842_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___closed__2));
v___x_843_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_843_, 0, v___x_841_);
lean_ctor_set(v___x_843_, 1, v_a_813_);
lean_ctor_set(v___x_843_, 2, v___x_842_);
lean_inc(v_ref_811_);
v___x_844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_844_, 0, v_ref_811_);
lean_ctor_set(v___x_844_, 1, v___x_843_);
v___x_845_ = l_Lean_PersistentArray_push___redArg(v_traces_832_, v___x_844_);
if (v_isShared_835_ == 0)
{
lean_ctor_set(v___x_834_, 0, v___x_845_);
v___x_847_ = v___x_834_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v___x_845_);
lean_ctor_set_uint64(v_reuseFailAlloc_855_, sizeof(void*)*1, v_tid_831_);
v___x_847_ = v_reuseFailAlloc_855_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
lean_object* v___x_849_; 
if (v_isShared_830_ == 0)
{
lean_ctor_set(v___x_829_, 4, v___x_847_);
v___x_849_ = v___x_829_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v_env_819_);
lean_ctor_set(v_reuseFailAlloc_854_, 1, v_nextMacroScope_820_);
lean_ctor_set(v_reuseFailAlloc_854_, 2, v_ngen_821_);
lean_ctor_set(v_reuseFailAlloc_854_, 3, v_auxDeclNGen_822_);
lean_ctor_set(v_reuseFailAlloc_854_, 4, v___x_847_);
lean_ctor_set(v_reuseFailAlloc_854_, 5, v_cache_823_);
lean_ctor_set(v_reuseFailAlloc_854_, 6, v_recordedDeps_824_);
lean_ctor_set(v_reuseFailAlloc_854_, 7, v_messages_825_);
lean_ctor_set(v_reuseFailAlloc_854_, 8, v_infoState_826_);
lean_ctor_set(v_reuseFailAlloc_854_, 9, v_snapshotTasks_827_);
v___x_849_ = v_reuseFailAlloc_854_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
lean_object* v___x_850_; lean_object* v___x_852_; 
v___x_850_ = lean_st_ref_put(v___y_809_, v___x_849_);
if (v_isShared_816_ == 0)
{
lean_ctor_set(v___x_815_, 0, v___x_836_);
v___x_852_ = v___x_815_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v___x_836_);
v___x_852_ = v_reuseFailAlloc_853_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
return v___x_852_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___boxed(lean_object* v_cls_859_, lean_object* v_msg_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v_cls_859_, v_msg_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_);
lean_dec(v___y_864_);
lean_dec_ref(v___y_863_);
lean_dec(v___y_862_);
lean_dec_ref(v___y_861_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9(lean_object* v_as_867_, lean_object* v_bs_868_, lean_object* v_i_869_, lean_object* v_cs_870_){
_start:
{
lean_object* v___x_871_; uint8_t v___x_872_; 
v___x_871_ = lean_array_get_size(v_as_867_);
v___x_872_ = lean_nat_dec_lt(v_i_869_, v___x_871_);
if (v___x_872_ == 0)
{
lean_dec(v_i_869_);
return v_cs_870_;
}
else
{
lean_object* v___x_873_; uint8_t v___x_874_; 
v___x_873_ = lean_array_get_size(v_bs_868_);
v___x_874_ = lean_nat_dec_lt(v_i_869_, v___x_873_);
if (v___x_874_ == 0)
{
lean_dec(v_i_869_);
return v_cs_870_;
}
else
{
lean_object* v_a_875_; lean_object* v_ref_876_; uint8_t v_kind_877_; lean_object* v_levelParams_878_; lean_object* v_modifiers_879_; lean_object* v_declName_880_; lean_object* v_binders_881_; lean_object* v_numSectionVars_882_; lean_object* v_type_883_; lean_object* v_termination_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_896_; 
v_a_875_ = lean_array_fget(v_as_867_, v_i_869_);
v_ref_876_ = lean_ctor_get(v_a_875_, 0);
v_kind_877_ = lean_ctor_get_uint8(v_a_875_, sizeof(void*)*9);
v_levelParams_878_ = lean_ctor_get(v_a_875_, 1);
v_modifiers_879_ = lean_ctor_get(v_a_875_, 2);
v_declName_880_ = lean_ctor_get(v_a_875_, 3);
v_binders_881_ = lean_ctor_get(v_a_875_, 4);
v_numSectionVars_882_ = lean_ctor_get(v_a_875_, 5);
v_type_883_ = lean_ctor_get(v_a_875_, 6);
v_termination_884_ = lean_ctor_get(v_a_875_, 8);
v_isSharedCheck_896_ = !lean_is_exclusive(v_a_875_);
if (v_isSharedCheck_896_ == 0)
{
lean_object* v_unused_897_; 
v_unused_897_ = lean_ctor_get(v_a_875_, 7);
lean_dec(v_unused_897_);
v___x_886_ = v_a_875_;
v_isShared_887_ = v_isSharedCheck_896_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_termination_884_);
lean_inc(v_type_883_);
lean_inc(v_numSectionVars_882_);
lean_inc(v_binders_881_);
lean_inc(v_declName_880_);
lean_inc(v_modifiers_879_);
lean_inc(v_levelParams_878_);
lean_inc(v_ref_876_);
lean_dec(v_a_875_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_896_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
lean_object* v_b_888_; lean_object* v___x_890_; 
v_b_888_ = lean_array_fget_borrowed(v_bs_868_, v_i_869_);
lean_inc(v_b_888_);
if (v_isShared_887_ == 0)
{
lean_ctor_set(v___x_886_, 7, v_b_888_);
v___x_890_ = v___x_886_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v_ref_876_);
lean_ctor_set(v_reuseFailAlloc_895_, 1, v_levelParams_878_);
lean_ctor_set(v_reuseFailAlloc_895_, 2, v_modifiers_879_);
lean_ctor_set(v_reuseFailAlloc_895_, 3, v_declName_880_);
lean_ctor_set(v_reuseFailAlloc_895_, 4, v_binders_881_);
lean_ctor_set(v_reuseFailAlloc_895_, 5, v_numSectionVars_882_);
lean_ctor_set(v_reuseFailAlloc_895_, 6, v_type_883_);
lean_ctor_set(v_reuseFailAlloc_895_, 7, v_b_888_);
lean_ctor_set(v_reuseFailAlloc_895_, 8, v_termination_884_);
lean_ctor_set_uint8(v_reuseFailAlloc_895_, sizeof(void*)*9, v_kind_877_);
v___x_890_ = v_reuseFailAlloc_895_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; 
v___x_891_ = lean_unsigned_to_nat(1u);
v___x_892_ = lean_nat_add(v_i_869_, v___x_891_);
lean_dec(v_i_869_);
v___x_893_ = lean_array_push(v_cs_870_, v___x_890_);
v_i_869_ = v___x_892_;
v_cs_870_ = v___x_893_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9___boxed(lean_object* v_as_898_, lean_object* v_bs_899_, lean_object* v_i_900_, lean_object* v_cs_901_){
_start:
{
lean_object* v_res_902_; 
v_res_902_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9(v_as_898_, v_bs_899_, v_i_900_, v_cs_901_);
lean_dec_ref(v_bs_899_);
lean_dec_ref(v_as_898_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___lam__0(lean_object* v_fixedParamPerms_903_, lean_object* v___x_904_, lean_object* v___x_905_, lean_object* v_xs_906_, lean_object* v_snd_907_, uint8_t v___x_908_, lean_object* v_ys_909_, lean_object* v_x_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_){
_start:
{
lean_object* v_perms_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; uint8_t v___x_920_; uint8_t v___x_921_; lean_object* v___x_922_; 
v_perms_916_ = lean_ctor_get(v_fixedParamPerms_903_, 1);
v___x_917_ = lean_array_get_borrowed(v___x_904_, v_perms_916_, v___x_905_);
lean_inc_ref(v_ys_909_);
lean_inc(v___x_917_);
v___x_918_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v___x_917_, v_xs_906_, v_ys_909_);
v___x_919_ = l_Lean_Expr_beta(v_snd_907_, v_ys_909_);
v___x_920_ = 0;
v___x_921_ = 1;
v___x_922_ = l_Lean_Meta_mkLambdaFVars(v___x_918_, v___x_919_, v___x_920_, v___x_908_, v___x_920_, v___x_908_, v___x_921_, v___y_911_, v___y_912_, v___y_913_, v___y_914_);
lean_dec_ref(v___x_918_);
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___lam__0___boxed(lean_object* v_fixedParamPerms_923_, lean_object* v___x_924_, lean_object* v___x_925_, lean_object* v_xs_926_, lean_object* v_snd_927_, lean_object* v___x_928_, lean_object* v_ys_929_, lean_object* v_x_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_){
_start:
{
uint8_t v___x_27673__boxed_936_; lean_object* v_res_937_; 
v___x_27673__boxed_936_ = lean_unbox(v___x_928_);
v_res_937_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___lam__0(v_fixedParamPerms_923_, v___x_924_, v___x_925_, v_xs_926_, v_snd_927_, v___x_27673__boxed_936_, v_ys_929_, v_x_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_);
lean_dec(v___y_934_);
lean_dec_ref(v___y_933_);
lean_dec(v___y_932_);
lean_dec_ref(v___y_931_);
lean_dec_ref(v_x_930_);
lean_dec_ref(v_xs_926_);
lean_dec(v___x_925_);
lean_dec_ref(v___x_924_);
lean_dec_ref(v_fixedParamPerms_923_);
return v_res_937_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_938_; 
v___x_938_ = l_Array_instInhabited___redArg();
return v___x_938_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg(lean_object* v_fixedParamPerms_939_, lean_object* v_xs_940_, size_t v_sz_941_, size_t v_i_942_, lean_object* v_bs_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_){
_start:
{
uint8_t v___x_949_; 
v___x_949_ = lean_usize_dec_lt(v_i_942_, v_sz_941_);
if (v___x_949_ == 0)
{
lean_object* v___x_950_; 
lean_dec_ref(v_xs_940_);
lean_dec_ref(v_fixedParamPerms_939_);
v___x_950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_950_, 0, v_bs_943_);
return v___x_950_;
}
else
{
lean_object* v_v_951_; lean_object* v_fst_952_; lean_object* v_snd_953_; lean_object* v___x_954_; lean_object* v_bs_x27_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___f_959_; uint8_t v___x_960_; lean_object* v___x_961_; 
v_v_951_ = lean_array_uget_borrowed(v_bs_943_, v_i_942_);
v_fst_952_ = lean_ctor_get(v_v_951_, 0);
lean_inc(v_fst_952_);
v_snd_953_ = lean_ctor_get(v_v_951_, 1);
lean_inc(v_snd_953_);
v___x_954_ = lean_unsigned_to_nat(0u);
v_bs_x27_955_ = lean_array_uset(v_bs_943_, v_i_942_, v___x_954_);
v___x_956_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0);
v___x_957_ = lean_usize_to_nat(v_i_942_);
v___x_958_ = lean_box(v___x_949_);
lean_inc_ref(v_xs_940_);
lean_inc_ref(v_fixedParamPerms_939_);
v___f_959_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___lam__0___boxed), 13, 6);
lean_closure_set(v___f_959_, 0, v_fixedParamPerms_939_);
lean_closure_set(v___f_959_, 1, v___x_956_);
lean_closure_set(v___f_959_, 2, v___x_957_);
lean_closure_set(v___f_959_, 3, v_xs_940_);
lean_closure_set(v___f_959_, 4, v_snd_953_);
lean_closure_set(v___f_959_, 5, v___x_958_);
v___x_960_ = 0;
v___x_961_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg(v_fst_952_, v___f_959_, v___x_960_, v___y_944_, v___y_945_, v___y_946_, v___y_947_);
if (lean_obj_tag(v___x_961_) == 0)
{
lean_object* v_a_962_; size_t v___x_963_; size_t v___x_964_; lean_object* v___x_965_; 
v_a_962_ = lean_ctor_get(v___x_961_, 0);
lean_inc(v_a_962_);
lean_dec_ref_known(v___x_961_, 1);
v___x_963_ = ((size_t)1ULL);
v___x_964_ = lean_usize_add(v_i_942_, v___x_963_);
v___x_965_ = lean_array_uset(v_bs_x27_955_, v_i_942_, v_a_962_);
v_i_942_ = v___x_964_;
v_bs_943_ = v___x_965_;
goto _start;
}
else
{
lean_object* v_a_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_974_; 
lean_dec_ref(v_bs_x27_955_);
lean_dec_ref(v_xs_940_);
lean_dec_ref(v_fixedParamPerms_939_);
v_a_967_ = lean_ctor_get(v___x_961_, 0);
v_isSharedCheck_974_ = !lean_is_exclusive(v___x_961_);
if (v_isSharedCheck_974_ == 0)
{
v___x_969_ = v___x_961_;
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_a_967_);
lean_dec(v___x_961_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_972_; 
if (v_isShared_970_ == 0)
{
v___x_972_ = v___x_969_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v_a_967_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
return v___x_972_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___boxed(lean_object* v_fixedParamPerms_975_, lean_object* v_xs_976_, lean_object* v_sz_977_, lean_object* v_i_978_, lean_object* v_bs_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_){
_start:
{
size_t v_sz_boxed_985_; size_t v_i_boxed_986_; lean_object* v_res_987_; 
v_sz_boxed_985_ = lean_unbox_usize(v_sz_977_);
lean_dec(v_sz_977_);
v_i_boxed_986_ = lean_unbox_usize(v_i_978_);
lean_dec(v_i_978_);
v_res_987_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg(v_fixedParamPerms_975_, v_xs_976_, v_sz_boxed_985_, v_i_boxed_986_, v_bs_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_);
lean_dec(v___y_983_);
lean_dec_ref(v___y_982_);
lean_dec(v___y_981_);
lean_dec_ref(v___y_980_);
return v_res_987_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(lean_object* v_a_988_, lean_object* v_a_989_){
_start:
{
if (lean_obj_tag(v_a_988_) == 0)
{
lean_object* v___x_990_; 
v___x_990_ = l_List_reverse___redArg(v_a_989_);
return v___x_990_;
}
else
{
lean_object* v_head_991_; lean_object* v_tail_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_1001_; 
v_head_991_ = lean_ctor_get(v_a_988_, 0);
v_tail_992_ = lean_ctor_get(v_a_988_, 1);
v_isSharedCheck_1001_ = !lean_is_exclusive(v_a_988_);
if (v_isSharedCheck_1001_ == 0)
{
v___x_994_ = v_a_988_;
v_isShared_995_ = v_isSharedCheck_1001_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_tail_992_);
lean_inc(v_head_991_);
lean_dec(v_a_988_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_1001_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
lean_object* v___x_996_; lean_object* v___x_998_; 
v___x_996_ = l_Lean_MessageData_ofExpr(v_head_991_);
if (v_isShared_995_ == 0)
{
lean_ctor_set(v___x_994_, 1, v_a_989_);
lean_ctor_set(v___x_994_, 0, v___x_996_);
v___x_998_ = v___x_994_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v___x_996_);
lean_ctor_set(v_reuseFailAlloc_1000_, 1, v_a_989_);
v___x_998_ = v_reuseFailAlloc_1000_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
v_a_988_ = v_tail_992_;
v_a_989_ = v___x_998_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__15(lean_object* v_a_1002_, lean_object* v_a_1003_){
_start:
{
if (lean_obj_tag(v_a_1002_) == 0)
{
lean_object* v___x_1004_; 
v___x_1004_ = l_List_reverse___redArg(v_a_1003_);
return v___x_1004_;
}
else
{
lean_object* v_head_1005_; lean_object* v_tail_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1015_; 
v_head_1005_ = lean_ctor_get(v_a_1002_, 0);
v_tail_1006_ = lean_ctor_get(v_a_1002_, 1);
v_isSharedCheck_1015_ = !lean_is_exclusive(v_a_1002_);
if (v_isSharedCheck_1015_ == 0)
{
v___x_1008_ = v_a_1002_;
v_isShared_1009_ = v_isSharedCheck_1015_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_tail_1006_);
lean_inc(v_head_1005_);
lean_dec(v_a_1002_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1015_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v___x_1010_; lean_object* v___x_1012_; 
v___x_1010_ = l_Lean_mkLevelParam(v_head_1005_);
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 1, v_a_1003_);
lean_ctor_set(v___x_1008_, 0, v___x_1010_);
v___x_1012_ = v___x_1008_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v___x_1010_);
lean_ctor_set(v_reuseFailAlloc_1014_, 1, v_a_1003_);
v___x_1012_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
v_a_1002_ = v_tail_1006_;
v_a_1003_ = v___x_1012_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__0(void){
_start:
{
lean_object* v___x_1016_; 
v___x_1016_ = l_instMonadEIO___redArg();
return v___x_1016_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg(lean_object* v_msg_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_){
_start:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v_toApplicative_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1090_; 
v___x_1027_ = lean_obj_once(&l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__0, &l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__0_once, _init_l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__0);
v___x_1028_ = l_StateRefT_x27_instMonad___redArg(v___x_1027_);
v_toApplicative_1029_ = lean_ctor_get(v___x_1028_, 0);
v_isSharedCheck_1090_ = !lean_is_exclusive(v___x_1028_);
if (v_isSharedCheck_1090_ == 0)
{
lean_object* v_unused_1091_; 
v_unused_1091_ = lean_ctor_get(v___x_1028_, 1);
lean_dec(v_unused_1091_);
v___x_1031_ = v___x_1028_;
v_isShared_1032_ = v_isSharedCheck_1090_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_toApplicative_1029_);
lean_dec(v___x_1028_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1090_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v_toFunctor_1033_; lean_object* v_toSeq_1034_; lean_object* v_toSeqLeft_1035_; lean_object* v_toSeqRight_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1088_; 
v_toFunctor_1033_ = lean_ctor_get(v_toApplicative_1029_, 0);
v_toSeq_1034_ = lean_ctor_get(v_toApplicative_1029_, 2);
v_toSeqLeft_1035_ = lean_ctor_get(v_toApplicative_1029_, 3);
v_toSeqRight_1036_ = lean_ctor_get(v_toApplicative_1029_, 4);
v_isSharedCheck_1088_ = !lean_is_exclusive(v_toApplicative_1029_);
if (v_isSharedCheck_1088_ == 0)
{
lean_object* v_unused_1089_; 
v_unused_1089_ = lean_ctor_get(v_toApplicative_1029_, 1);
lean_dec(v_unused_1089_);
v___x_1038_ = v_toApplicative_1029_;
v_isShared_1039_ = v_isSharedCheck_1088_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_toSeqRight_1036_);
lean_inc(v_toSeqLeft_1035_);
lean_inc(v_toSeq_1034_);
lean_inc(v_toFunctor_1033_);
lean_dec(v_toApplicative_1029_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1088_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v___f_1040_; lean_object* v___f_1041_; lean_object* v___f_1042_; lean_object* v___f_1043_; lean_object* v___x_1044_; lean_object* v___f_1045_; lean_object* v___f_1046_; lean_object* v___f_1047_; lean_object* v___x_1049_; 
v___f_1040_ = ((lean_object*)(l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__1));
v___f_1041_ = ((lean_object*)(l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__2));
lean_inc_ref(v_toFunctor_1033_);
v___f_1042_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1042_, 0, v_toFunctor_1033_);
v___f_1043_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1043_, 0, v_toFunctor_1033_);
v___x_1044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1044_, 0, v___f_1042_);
lean_ctor_set(v___x_1044_, 1, v___f_1043_);
v___f_1045_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1045_, 0, v_toSeqRight_1036_);
v___f_1046_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1046_, 0, v_toSeqLeft_1035_);
v___f_1047_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1047_, 0, v_toSeq_1034_);
if (v_isShared_1039_ == 0)
{
lean_ctor_set(v___x_1038_, 4, v___f_1045_);
lean_ctor_set(v___x_1038_, 3, v___f_1046_);
lean_ctor_set(v___x_1038_, 2, v___f_1047_);
lean_ctor_set(v___x_1038_, 1, v___f_1040_);
lean_ctor_set(v___x_1038_, 0, v___x_1044_);
v___x_1049_ = v___x_1038_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v___x_1044_);
lean_ctor_set(v_reuseFailAlloc_1087_, 1, v___f_1040_);
lean_ctor_set(v_reuseFailAlloc_1087_, 2, v___f_1047_);
lean_ctor_set(v_reuseFailAlloc_1087_, 3, v___f_1046_);
lean_ctor_set(v_reuseFailAlloc_1087_, 4, v___f_1045_);
v___x_1049_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
lean_object* v___x_1051_; 
if (v_isShared_1032_ == 0)
{
lean_ctor_set(v___x_1031_, 1, v___f_1041_);
lean_ctor_set(v___x_1031_, 0, v___x_1049_);
v___x_1051_ = v___x_1031_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v___x_1049_);
lean_ctor_set(v_reuseFailAlloc_1086_, 1, v___f_1041_);
v___x_1051_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
lean_object* v___x_1052_; lean_object* v_toApplicative_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1084_; 
v___x_1052_ = l_StateRefT_x27_instMonad___redArg(v___x_1051_);
v_toApplicative_1053_ = lean_ctor_get(v___x_1052_, 0);
v_isSharedCheck_1084_ = !lean_is_exclusive(v___x_1052_);
if (v_isSharedCheck_1084_ == 0)
{
lean_object* v_unused_1085_; 
v_unused_1085_ = lean_ctor_get(v___x_1052_, 1);
lean_dec(v_unused_1085_);
v___x_1055_ = v___x_1052_;
v_isShared_1056_ = v_isSharedCheck_1084_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_toApplicative_1053_);
lean_dec(v___x_1052_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1084_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v_toFunctor_1057_; lean_object* v_toSeq_1058_; lean_object* v_toSeqLeft_1059_; lean_object* v_toSeqRight_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1082_; 
v_toFunctor_1057_ = lean_ctor_get(v_toApplicative_1053_, 0);
v_toSeq_1058_ = lean_ctor_get(v_toApplicative_1053_, 2);
v_toSeqLeft_1059_ = lean_ctor_get(v_toApplicative_1053_, 3);
v_toSeqRight_1060_ = lean_ctor_get(v_toApplicative_1053_, 4);
v_isSharedCheck_1082_ = !lean_is_exclusive(v_toApplicative_1053_);
if (v_isSharedCheck_1082_ == 0)
{
lean_object* v_unused_1083_; 
v_unused_1083_ = lean_ctor_get(v_toApplicative_1053_, 1);
lean_dec(v_unused_1083_);
v___x_1062_ = v_toApplicative_1053_;
v_isShared_1063_ = v_isSharedCheck_1082_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_toSeqRight_1060_);
lean_inc(v_toSeqLeft_1059_);
lean_inc(v_toSeq_1058_);
lean_inc(v_toFunctor_1057_);
lean_dec(v_toApplicative_1053_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1082_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
lean_object* v___f_1064_; lean_object* v___f_1065_; lean_object* v___f_1066_; lean_object* v___f_1067_; lean_object* v___x_1068_; lean_object* v___f_1069_; lean_object* v___f_1070_; lean_object* v___f_1071_; lean_object* v___x_1073_; 
v___f_1064_ = ((lean_object*)(l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__3));
v___f_1065_ = ((lean_object*)(l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__4));
lean_inc_ref(v_toFunctor_1057_);
v___f_1066_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1066_, 0, v_toFunctor_1057_);
v___f_1067_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1067_, 0, v_toFunctor_1057_);
v___x_1068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1068_, 0, v___f_1066_);
lean_ctor_set(v___x_1068_, 1, v___f_1067_);
v___f_1069_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1069_, 0, v_toSeqRight_1060_);
v___f_1070_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1070_, 0, v_toSeqLeft_1059_);
v___f_1071_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1071_, 0, v_toSeq_1058_);
if (v_isShared_1063_ == 0)
{
lean_ctor_set(v___x_1062_, 4, v___f_1069_);
lean_ctor_set(v___x_1062_, 3, v___f_1070_);
lean_ctor_set(v___x_1062_, 2, v___f_1071_);
lean_ctor_set(v___x_1062_, 1, v___f_1064_);
lean_ctor_set(v___x_1062_, 0, v___x_1068_);
v___x_1073_ = v___x_1062_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v___x_1068_);
lean_ctor_set(v_reuseFailAlloc_1081_, 1, v___f_1064_);
lean_ctor_set(v_reuseFailAlloc_1081_, 2, v___f_1071_);
lean_ctor_set(v_reuseFailAlloc_1081_, 3, v___f_1070_);
lean_ctor_set(v_reuseFailAlloc_1081_, 4, v___f_1069_);
v___x_1073_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
lean_object* v___x_1075_; 
if (v_isShared_1056_ == 0)
{
lean_ctor_set(v___x_1055_, 1, v___f_1065_);
lean_ctor_set(v___x_1055_, 0, v___x_1073_);
v___x_1075_ = v___x_1055_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v___x_1073_);
lean_ctor_set(v_reuseFailAlloc_1080_, 1, v___f_1065_);
v___x_1075_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_22933__overap_1078_; lean_object* v___x_1079_; 
v___x_1076_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0);
v___x_1077_ = l_instInhabitedOfMonad___redArg(v___x_1075_, v___x_1076_);
v___x_22933__overap_1078_ = lean_panic_fn_borrowed(v___x_1077_, v_msg_1021_);
lean_dec(v___x_1077_);
lean_inc(v___y_1025_);
lean_inc_ref(v___y_1024_);
lean_inc(v___y_1023_);
lean_inc_ref(v___y_1022_);
v___x_1079_ = lean_apply_5(v___x_22933__overap_1078_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, lean_box(0));
return v___x_1079_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___boxed(lean_object* v_msg_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_){
_start:
{
lean_object* v_res_1098_; 
v_res_1098_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg(v_msg_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_);
lean_dec(v___y_1096_);
lean_dec_ref(v___y_1095_);
lean_dec(v___y_1094_);
lean_dec_ref(v___y_1093_);
return v_res_1098_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__13(lean_object* v_xs_1099_, size_t v_sz_1100_, size_t v_i_1101_, lean_object* v_bs_1102_){
_start:
{
uint8_t v___x_1103_; 
v___x_1103_ = lean_usize_dec_lt(v_i_1101_, v_sz_1100_);
if (v___x_1103_ == 0)
{
return v_bs_1102_;
}
else
{
lean_object* v___x_1104_; lean_object* v_v_1105_; lean_object* v___x_1106_; lean_object* v_bs_x27_1107_; lean_object* v___x_1108_; size_t v___x_1109_; size_t v___x_1110_; lean_object* v___x_1111_; 
v___x_1104_ = l_Lean_instInhabitedExpr;
v_v_1105_ = lean_array_uget(v_bs_1102_, v_i_1101_);
v___x_1106_ = lean_unsigned_to_nat(0u);
v_bs_x27_1107_ = lean_array_uset(v_bs_1102_, v_i_1101_, v___x_1106_);
v___x_1108_ = lean_array_get_borrowed(v___x_1104_, v_xs_1099_, v_v_1105_);
lean_dec(v_v_1105_);
v___x_1109_ = ((size_t)1ULL);
v___x_1110_ = lean_usize_add(v_i_1101_, v___x_1109_);
lean_inc(v___x_1108_);
v___x_1111_ = lean_array_uset(v_bs_x27_1107_, v_i_1101_, v___x_1108_);
v_i_1101_ = v___x_1110_;
v_bs_1102_ = v___x_1111_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__13___boxed(lean_object* v_xs_1113_, lean_object* v_sz_1114_, lean_object* v_i_1115_, lean_object* v_bs_1116_){
_start:
{
size_t v_sz_boxed_1117_; size_t v_i_boxed_1118_; lean_object* v_res_1119_; 
v_sz_boxed_1117_ = lean_unbox_usize(v_sz_1114_);
lean_dec(v_sz_1114_);
v_i_boxed_1118_ = lean_unbox_usize(v_i_1115_);
lean_dec(v_i_1115_);
v_res_1119_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__13(v_xs_1113_, v_sz_boxed_1117_, v_i_boxed_1118_, v_bs_1116_);
lean_dec_ref(v_xs_1113_);
return v_res_1119_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15___redArg(lean_object* v_xs_1120_, lean_object* v_f_1121_, lean_object* v_as_1122_, lean_object* v_bs_1123_, lean_object* v_i_1124_, lean_object* v_cs_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_){
_start:
{
lean_object* v___x_1131_; uint8_t v___x_1132_; 
v___x_1131_ = lean_array_get_size(v_as_1122_);
v___x_1132_ = lean_nat_dec_lt(v_i_1124_, v___x_1131_);
if (v___x_1132_ == 0)
{
lean_object* v___x_1133_; 
lean_dec(v_i_1124_);
lean_dec_ref(v_f_1121_);
v___x_1133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1133_, 0, v_cs_1125_);
return v___x_1133_;
}
else
{
lean_object* v___x_1134_; uint8_t v___x_1135_; 
v___x_1134_ = lean_array_get_size(v_bs_1123_);
v___x_1135_ = lean_nat_dec_lt(v_i_1124_, v___x_1134_);
if (v___x_1135_ == 0)
{
lean_object* v___x_1136_; 
lean_dec(v_i_1124_);
lean_dec_ref(v_f_1121_);
v___x_1136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1136_, 0, v_cs_1125_);
return v___x_1136_;
}
else
{
lean_object* v_a_1137_; lean_object* v_b_1138_; size_t v_sz_1139_; size_t v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; 
v_a_1137_ = lean_array_fget_borrowed(v_as_1122_, v_i_1124_);
v_b_1138_ = lean_array_fget_borrowed(v_bs_1123_, v_i_1124_);
v_sz_1139_ = lean_array_size(v_b_1138_);
v___x_1140_ = ((size_t)0ULL);
lean_inc(v_b_1138_);
v___x_1141_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__13(v_xs_1120_, v_sz_1139_, v___x_1140_, v_b_1138_);
lean_inc_ref(v_f_1121_);
lean_inc(v___y_1129_);
lean_inc_ref(v___y_1128_);
lean_inc(v___y_1127_);
lean_inc_ref(v___y_1126_);
lean_inc(v_a_1137_);
v___x_1142_ = lean_apply_7(v_f_1121_, v_a_1137_, v___x_1141_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_, lean_box(0));
if (lean_obj_tag(v___x_1142_) == 0)
{
lean_object* v_a_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; 
v_a_1143_ = lean_ctor_get(v___x_1142_, 0);
lean_inc(v_a_1143_);
lean_dec_ref_known(v___x_1142_, 1);
v___x_1144_ = lean_unsigned_to_nat(1u);
v___x_1145_ = lean_nat_add(v_i_1124_, v___x_1144_);
lean_dec(v_i_1124_);
v___x_1146_ = lean_array_push(v_cs_1125_, v_a_1143_);
v_i_1124_ = v___x_1145_;
v_cs_1125_ = v___x_1146_;
goto _start;
}
else
{
lean_object* v_a_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1155_; 
lean_dec_ref(v_cs_1125_);
lean_dec(v_i_1124_);
lean_dec_ref(v_f_1121_);
v_a_1148_ = lean_ctor_get(v___x_1142_, 0);
v_isSharedCheck_1155_ = !lean_is_exclusive(v___x_1142_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1150_ = v___x_1142_;
v_isShared_1151_ = v_isSharedCheck_1155_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_a_1148_);
lean_dec(v___x_1142_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1155_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v___x_1153_; 
if (v_isShared_1151_ == 0)
{
v___x_1153_ = v___x_1150_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v_a_1148_);
v___x_1153_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
return v___x_1153_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15___redArg___boxed(lean_object* v_xs_1156_, lean_object* v_f_1157_, lean_object* v_as_1158_, lean_object* v_bs_1159_, lean_object* v_i_1160_, lean_object* v_cs_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_){
_start:
{
lean_object* v_res_1167_; 
v_res_1167_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15___redArg(v_xs_1156_, v_f_1157_, v_as_1158_, v_bs_1159_, v_i_1160_, v_cs_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_);
lean_dec(v___y_1165_);
lean_dec_ref(v___y_1164_);
lean_dec(v___y_1163_);
lean_dec_ref(v___y_1162_);
lean_dec_ref(v_bs_1159_);
lean_dec_ref(v_as_1158_);
lean_dec_ref(v_xs_1156_);
return v_res_1167_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; 
v___x_1171_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__2));
v___x_1172_ = lean_unsigned_to_nat(2u);
v___x_1173_ = lean_unsigned_to_nat(73u);
v___x_1174_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__1));
v___x_1175_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__0));
v___x_1176_ = l_mkPanicMessageWithDecl(v___x_1175_, v___x_1174_, v___x_1173_, v___x_1172_, v___x_1171_);
return v___x_1176_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; 
v___x_1178_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__4));
v___x_1179_ = lean_unsigned_to_nat(2u);
v___x_1180_ = lean_unsigned_to_nat(74u);
v___x_1181_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__1));
v___x_1182_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__0));
v___x_1183_ = l_mkPanicMessageWithDecl(v___x_1182_, v___x_1181_, v___x_1180_, v___x_1179_, v___x_1178_);
return v___x_1183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg(lean_object* v_f_1186_, lean_object* v_positions_1187_, lean_object* v_ys_1188_, lean_object* v_xs_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_){
_start:
{
lean_object* v___x_1195_; lean_object* v___x_1196_; uint8_t v___x_1197_; 
v___x_1195_ = lean_array_get_size(v_positions_1187_);
v___x_1196_ = lean_array_get_size(v_ys_1188_);
v___x_1197_ = lean_nat_dec_eq(v___x_1195_, v___x_1196_);
if (v___x_1197_ == 0)
{
lean_object* v___x_1198_; lean_object* v___x_1199_; 
lean_dec_ref(v_f_1186_);
v___x_1198_ = lean_obj_once(&l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__3, &l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__3_once, _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__3);
v___x_1199_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg(v___x_1198_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_);
return v___x_1199_;
}
else
{
lean_object* v___x_1200_; lean_object* v___x_1201_; uint8_t v___x_1202_; 
v___x_1200_ = l_Lean_Elab_Structural_Positions_numIndices(v_positions_1187_);
v___x_1201_ = lean_array_get_size(v_xs_1189_);
v___x_1202_ = lean_nat_dec_eq(v___x_1200_, v___x_1201_);
lean_dec(v___x_1200_);
if (v___x_1202_ == 0)
{
lean_object* v___x_1203_; lean_object* v___x_1204_; 
lean_dec_ref(v_f_1186_);
v___x_1203_ = lean_obj_once(&l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__5, &l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__5_once, _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__5);
v___x_1204_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg(v___x_1203_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_);
return v___x_1204_;
}
else
{
lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; 
v___x_1205_ = lean_unsigned_to_nat(0u);
v___x_1206_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__6));
v___x_1207_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15___redArg(v_xs_1189_, v_f_1186_, v_ys_1188_, v_positions_1187_, v___x_1205_, v___x_1206_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_);
return v___x_1207_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___boxed(lean_object* v_f_1208_, lean_object* v_positions_1209_, lean_object* v_ys_1210_, lean_object* v_xs_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_){
_start:
{
lean_object* v_res_1217_; 
v_res_1217_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg(v_f_1208_, v_positions_1209_, v_ys_1210_, v_xs_1211_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_);
lean_dec(v___y_1215_);
lean_dec_ref(v___y_1214_);
lean_dec(v___y_1213_);
lean_dec_ref(v___y_1212_);
lean_dec_ref(v_xs_1211_);
lean_dec_ref(v_ys_1210_);
lean_dec_ref(v_positions_1209_);
return v_res_1217_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg(lean_object* v___x_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_, lean_object* v_funTypes_1221_, size_t v_sz_1222_, size_t v_i_1223_, lean_object* v_bs_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_){
_start:
{
uint8_t v___x_1230_; 
v___x_1230_ = lean_usize_dec_lt(v_i_1223_, v_sz_1222_);
if (v___x_1230_ == 0)
{
lean_object* v___x_1231_; 
lean_dec_ref(v_funTypes_1221_);
lean_dec_ref(v_a_1220_);
lean_dec_ref(v_a_1219_);
lean_dec_ref(v___x_1218_);
v___x_1231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1231_, 0, v_bs_1224_);
return v___x_1231_;
}
else
{
lean_object* v_v_1232_; lean_object* v_fst_1233_; lean_object* v_snd_1234_; lean_object* v___x_1235_; lean_object* v_bs_x27_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; 
v_v_1232_ = lean_array_uget_borrowed(v_bs_1224_, v_i_1223_);
v_fst_1233_ = lean_ctor_get(v_v_1232_, 0);
lean_inc(v_fst_1233_);
v_snd_1234_ = lean_ctor_get(v_v_1232_, 1);
lean_inc(v_snd_1234_);
v___x_1235_ = lean_unsigned_to_nat(0u);
v_bs_x27_1236_ = lean_array_uset(v_bs_1224_, v_i_1223_, v___x_1235_);
v___x_1237_ = lean_usize_to_nat(v_i_1223_);
lean_inc_ref(v_funTypes_1221_);
lean_inc_ref(v_a_1220_);
lean_inc_ref(v_a_1219_);
lean_inc_ref(v___x_1218_);
v___x_1238_ = l_Lean_Elab_Structural_mkBRecOnApp(v___x_1218_, v___x_1237_, v_a_1219_, v_a_1220_, v_funTypes_1221_, v_fst_1233_, v_snd_1234_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_);
if (lean_obj_tag(v___x_1238_) == 0)
{
lean_object* v_a_1239_; size_t v___x_1240_; size_t v___x_1241_; lean_object* v___x_1242_; 
v_a_1239_ = lean_ctor_get(v___x_1238_, 0);
lean_inc(v_a_1239_);
lean_dec_ref_known(v___x_1238_, 1);
v___x_1240_ = ((size_t)1ULL);
v___x_1241_ = lean_usize_add(v_i_1223_, v___x_1240_);
v___x_1242_ = lean_array_uset(v_bs_x27_1236_, v_i_1223_, v_a_1239_);
v_i_1223_ = v___x_1241_;
v_bs_1224_ = v___x_1242_;
goto _start;
}
else
{
lean_object* v_a_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1251_; 
lean_dec_ref(v_bs_x27_1236_);
lean_dec_ref(v_funTypes_1221_);
lean_dec_ref(v_a_1220_);
lean_dec_ref(v_a_1219_);
lean_dec_ref(v___x_1218_);
v_a_1244_ = lean_ctor_get(v___x_1238_, 0);
v_isSharedCheck_1251_ = !lean_is_exclusive(v___x_1238_);
if (v_isSharedCheck_1251_ == 0)
{
v___x_1246_ = v___x_1238_;
v_isShared_1247_ = v_isSharedCheck_1251_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_a_1244_);
lean_dec(v___x_1238_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1251_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
lean_object* v___x_1249_; 
if (v_isShared_1247_ == 0)
{
v___x_1249_ = v___x_1246_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v_a_1244_);
v___x_1249_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
return v___x_1249_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg___boxed(lean_object* v___x_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_, lean_object* v_funTypes_1255_, lean_object* v_sz_1256_, lean_object* v_i_1257_, lean_object* v_bs_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_){
_start:
{
size_t v_sz_boxed_1264_; size_t v_i_boxed_1265_; lean_object* v_res_1266_; 
v_sz_boxed_1264_ = lean_unbox_usize(v_sz_1256_);
lean_dec(v_sz_1256_);
v_i_boxed_1265_ = lean_unbox_usize(v_i_1257_);
lean_dec(v_i_1257_);
v_res_1266_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg(v___x_1252_, v_a_1253_, v_a_1254_, v_funTypes_1255_, v_sz_boxed_1264_, v_i_boxed_1265_, v_bs_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_);
lean_dec(v___y_1262_);
lean_dec_ref(v___y_1261_);
lean_dec(v___y_1260_);
lean_dec_ref(v___y_1259_);
return v_res_1266_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__2(void){
_start:
{
lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; 
v___x_1270_ = lean_box(0);
v___x_1271_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__1));
v___x_1272_ = l_Lean_Expr_const___override(v___x_1271_, v___x_1270_);
return v___x_1272_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__4(void){
_start:
{
lean_object* v___x_1274_; lean_object* v___x_1275_; 
v___x_1274_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__3));
v___x_1275_ = l_Lean_stringToMessageData(v___x_1274_);
return v___x_1275_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__6(void){
_start:
{
lean_object* v___x_1277_; lean_object* v___x_1278_; 
v___x_1277_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__5));
v___x_1278_ = l_Lean_stringToMessageData(v___x_1277_);
return v___x_1278_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__8(void){
_start:
{
lean_object* v___x_1280_; lean_object* v___x_1281_; 
v___x_1280_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__7));
v___x_1281_ = l_Lean_stringToMessageData(v___x_1280_);
return v___x_1281_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__10(void){
_start:
{
lean_object* v___x_1283_; lean_object* v___x_1284_; 
v___x_1283_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__9));
v___x_1284_ = l_Lean_stringToMessageData(v___x_1283_);
return v___x_1284_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__12(void){
_start:
{
lean_object* v___x_1286_; lean_object* v___x_1287_; 
v___x_1286_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__11));
v___x_1287_ = l_Lean_stringToMessageData(v___x_1286_);
return v___x_1287_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2(lean_object* v_recArgInfos_1288_, lean_object* v_a_1289_, lean_object* v___x_1290_, size_t v___x_1291_, lean_object* v_fixedParamPerms_1292_, lean_object* v_xs_1293_, lean_object* v___x_1294_, lean_object* v_preDefs_1295_, lean_object* v_numIndices_1296_, lean_object* v___f_1297_, lean_object* v___x_1298_, uint8_t v_a_1299_, lean_object* v___x_1300_, lean_object* v___f_1301_, lean_object* v_funTypes_1302_, lean_object* v_motives_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_){
_start:
{
lean_object* v___y_1310_; lean_object* v___y_1311_; lean_object* v___y_1312_; lean_object* v___y_1313_; lean_object* v___y_1314_; lean_object* v___y_1315_; lean_object* v___y_1350_; lean_object* v_FArgs_1351_; lean_object* v___y_1352_; lean_object* v___y_1353_; lean_object* v___y_1354_; lean_object* v___y_1355_; lean_object* v___y_1407_; lean_object* v___y_1408_; lean_object* v___y_1409_; lean_object* v___y_1410_; lean_object* v___y_1411_; lean_object* v___y_1412_; lean_object* v___y_1429_; lean_object* v___y_1430_; lean_object* v___y_1431_; lean_object* v___y_1432_; lean_object* v___y_1433_; lean_object* v___y_1434_; lean_object* v___x_1519_; 
lean_inc_ref(v___f_1301_);
lean_inc(v___y_1307_);
lean_inc_ref(v___y_1306_);
lean_inc(v___y_1305_);
lean_inc_ref(v___y_1304_);
v___x_1519_ = lean_apply_5(v___f_1301_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, lean_box(0));
if (lean_obj_tag(v___x_1519_) == 0)
{
lean_object* v_a_1520_; uint8_t v___x_1521_; 
v_a_1520_ = lean_ctor_get(v___x_1519_, 0);
lean_inc(v_a_1520_);
lean_dec_ref_known(v___x_1519_, 1);
v___x_1521_ = lean_unbox(v_a_1520_);
lean_dec(v_a_1520_);
if (v___x_1521_ == 0)
{
goto v___jp_1472_;
}
else
{
lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; 
v___x_1522_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__10, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__10);
lean_inc_ref(v_funTypes_1302_);
v___x_1523_ = lean_array_to_list(v_funTypes_1302_);
v___x_1524_ = lean_box(0);
v___x_1525_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_1523_, v___x_1524_);
v___x_1526_ = l_Lean_MessageData_ofList(v___x_1525_);
v___x_1527_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1527_, 0, v___x_1522_);
lean_ctor_set(v___x_1527_, 1, v___x_1526_);
v___x_1528_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__12, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__12_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__12);
v___x_1529_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1529_, 0, v___x_1527_);
lean_ctor_set(v___x_1529_, 1, v___x_1528_);
lean_inc_ref(v_motives_1303_);
v___x_1530_ = lean_array_to_list(v_motives_1303_);
v___x_1531_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_1530_, v___x_1524_);
v___x_1532_ = l_Lean_MessageData_ofList(v___x_1531_);
v___x_1533_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1533_, 0, v___x_1529_);
lean_ctor_set(v___x_1533_, 1, v___x_1532_);
lean_inc(v___x_1298_);
v___x_1534_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_1298_, v___x_1533_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_);
if (lean_obj_tag(v___x_1534_) == 0)
{
lean_dec_ref_known(v___x_1534_, 1);
goto v___jp_1472_;
}
else
{
lean_object* v_a_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1542_; 
lean_dec_ref(v_motives_1303_);
lean_dec_ref(v_funTypes_1302_);
lean_dec_ref(v___f_1301_);
lean_dec(v___x_1298_);
lean_dec_ref(v___f_1297_);
lean_dec_ref(v_preDefs_1295_);
lean_dec(v___x_1294_);
lean_dec_ref(v_xs_1293_);
lean_dec_ref(v_fixedParamPerms_1292_);
lean_dec_ref(v___x_1290_);
lean_dec_ref(v_recArgInfos_1288_);
v_a_1535_ = lean_ctor_get(v___x_1534_, 0);
v_isSharedCheck_1542_ = !lean_is_exclusive(v___x_1534_);
if (v_isSharedCheck_1542_ == 0)
{
v___x_1537_ = v___x_1534_;
v_isShared_1538_ = v_isSharedCheck_1542_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_a_1535_);
lean_dec(v___x_1534_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1542_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
lean_object* v___x_1540_; 
if (v_isShared_1538_ == 0)
{
v___x_1540_ = v___x_1537_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v_a_1535_);
v___x_1540_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
return v___x_1540_;
}
}
}
}
}
else
{
lean_object* v_a_1543_; lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1550_; 
lean_dec_ref(v_motives_1303_);
lean_dec_ref(v_funTypes_1302_);
lean_dec_ref(v___f_1301_);
lean_dec(v___x_1298_);
lean_dec_ref(v___f_1297_);
lean_dec_ref(v_preDefs_1295_);
lean_dec(v___x_1294_);
lean_dec_ref(v_xs_1293_);
lean_dec_ref(v_fixedParamPerms_1292_);
lean_dec_ref(v___x_1290_);
lean_dec_ref(v_recArgInfos_1288_);
v_a_1543_ = lean_ctor_get(v___x_1519_, 0);
v_isSharedCheck_1550_ = !lean_is_exclusive(v___x_1519_);
if (v_isSharedCheck_1550_ == 0)
{
v___x_1545_ = v___x_1519_;
v_isShared_1546_ = v_isSharedCheck_1550_;
goto v_resetjp_1544_;
}
else
{
lean_inc(v_a_1543_);
lean_dec(v___x_1519_);
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
v___jp_1309_:
{
lean_object* v___x_1316_; size_t v_sz_1317_; lean_object* v___x_1318_; 
v___x_1316_ = l_Array_zip___redArg(v_recArgInfos_1288_, v_a_1289_);
lean_dec_ref(v_recArgInfos_1288_);
v_sz_1317_ = lean_array_size(v___x_1316_);
v___x_1318_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg(v___x_1290_, v___y_1310_, v___y_1311_, v_funTypes_1302_, v_sz_1317_, v___x_1291_, v___x_1316_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
if (lean_obj_tag(v___x_1318_) == 0)
{
lean_object* v_a_1319_; lean_object* v___x_1320_; size_t v_sz_1321_; lean_object* v___x_1322_; 
v_a_1319_ = lean_ctor_get(v___x_1318_, 0);
lean_inc(v_a_1319_);
lean_dec_ref_known(v___x_1318_, 1);
v___x_1320_ = l_Array_zip___redArg(v_a_1289_, v_a_1319_);
lean_dec(v_a_1319_);
v_sz_1321_ = lean_array_size(v___x_1320_);
v___x_1322_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg(v_fixedParamPerms_1292_, v_xs_1293_, v_sz_1321_, v___x_1291_, v___x_1320_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
if (lean_obj_tag(v___x_1322_) == 0)
{
lean_object* v_a_1323_; lean_object* v___x_1325_; uint8_t v_isShared_1326_; uint8_t v_isSharedCheck_1332_; 
v_a_1323_ = lean_ctor_get(v___x_1322_, 0);
v_isSharedCheck_1332_ = !lean_is_exclusive(v___x_1322_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1325_ = v___x_1322_;
v_isShared_1326_ = v_isSharedCheck_1332_;
goto v_resetjp_1324_;
}
else
{
lean_inc(v_a_1323_);
lean_dec(v___x_1322_);
v___x_1325_ = lean_box(0);
v_isShared_1326_ = v_isSharedCheck_1332_;
goto v_resetjp_1324_;
}
v_resetjp_1324_:
{
lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1330_; 
v___x_1327_ = lean_mk_empty_array_with_capacity(v___x_1294_);
v___x_1328_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9(v_preDefs_1295_, v_a_1323_, v___x_1294_, v___x_1327_);
lean_dec(v_a_1323_);
lean_dec_ref(v_preDefs_1295_);
if (v_isShared_1326_ == 0)
{
lean_ctor_set(v___x_1325_, 0, v___x_1328_);
v___x_1330_ = v___x_1325_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v___x_1328_);
v___x_1330_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
return v___x_1330_;
}
}
}
else
{
lean_object* v_a_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1340_; 
lean_dec_ref(v_preDefs_1295_);
lean_dec(v___x_1294_);
v_a_1333_ = lean_ctor_get(v___x_1322_, 0);
v_isSharedCheck_1340_ = !lean_is_exclusive(v___x_1322_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1335_ = v___x_1322_;
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_a_1333_);
lean_dec(v___x_1322_);
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
lean_dec_ref(v_preDefs_1295_);
lean_dec(v___x_1294_);
lean_dec_ref(v_xs_1293_);
lean_dec_ref(v_fixedParamPerms_1292_);
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
v___jp_1349_:
{
lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; 
lean_inc_ref(v___y_1350_);
lean_inc(v___x_1294_);
v___x_1356_ = lean_apply_1(v___y_1350_, v___x_1294_);
v___x_1357_ = lean_unsigned_to_nat(1u);
v___x_1358_ = lean_nat_add(v_numIndices_1296_, v___x_1357_);
v___x_1359_ = lean_box(0);
v___x_1360_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__2);
v___x_1361_ = lean_mk_array(v___x_1358_, v___x_1360_);
v___x_1362_ = l_Lean_mkAppN(v___x_1356_, v___x_1361_);
lean_dec_ref(v___x_1361_);
v___x_1363_ = lean_array_get_size(v___x_1290_);
v___x_1364_ = l_Lean_Meta_inferArgumentTypesN(v___x_1363_, v___x_1362_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
if (lean_obj_tag(v___x_1364_) == 0)
{
lean_object* v_a_1365_; lean_object* v___x_1366_; 
v_a_1365_ = lean_ctor_get(v___x_1364_, 0);
lean_inc(v_a_1365_);
lean_dec_ref_known(v___x_1364_, 1);
v___x_1366_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg(v___f_1297_, v___x_1290_, v_a_1365_, v_FArgs_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
lean_dec_ref(v_FArgs_1351_);
lean_dec(v_a_1365_);
if (lean_obj_tag(v___x_1366_) == 0)
{
lean_object* v_toCold_1367_; lean_object* v_options_1368_; uint8_t v_hasTrace_1369_; 
v_toCold_1367_ = lean_ctor_get(v___y_1354_, 0);
v_options_1368_ = lean_ctor_get(v_toCold_1367_, 2);
v_hasTrace_1369_ = lean_ctor_get_uint8(v_options_1368_, sizeof(void*)*1);
if (v_hasTrace_1369_ == 0)
{
lean_object* v_a_1370_; 
lean_dec(v___x_1298_);
v_a_1370_ = lean_ctor_get(v___x_1366_, 0);
lean_inc(v_a_1370_);
lean_dec_ref_known(v___x_1366_, 1);
v___y_1310_ = v___y_1350_;
v___y_1311_ = v_a_1370_;
v___y_1312_ = v___y_1352_;
v___y_1313_ = v___y_1353_;
v___y_1314_ = v___y_1354_;
v___y_1315_ = v___y_1355_;
goto v___jp_1309_;
}
else
{
lean_object* v_a_1371_; lean_object* v_inheritedTraceOptions_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; uint8_t v___x_1375_; 
v_a_1371_ = lean_ctor_get(v___x_1366_, 0);
lean_inc(v_a_1371_);
lean_dec_ref_known(v___x_1366_, 1);
v_inheritedTraceOptions_1372_ = lean_ctor_get(v_toCold_1367_, 11);
v___x_1373_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___closed__1));
lean_inc(v___x_1298_);
v___x_1374_ = l_Lean_Name_append(v___x_1373_, v___x_1298_);
v___x_1375_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1372_, v_options_1368_, v___x_1374_);
lean_dec(v___x_1374_);
if (v___x_1375_ == 0)
{
lean_dec(v___x_1298_);
v___y_1310_ = v___y_1350_;
v___y_1311_ = v_a_1371_;
v___y_1312_ = v___y_1352_;
v___y_1313_ = v___y_1353_;
v___y_1314_ = v___y_1354_;
v___y_1315_ = v___y_1355_;
goto v___jp_1309_;
}
else
{
lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; 
v___x_1376_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__4);
lean_inc(v_a_1371_);
v___x_1377_ = lean_array_to_list(v_a_1371_);
v___x_1378_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_1377_, v___x_1359_);
v___x_1379_ = l_Lean_MessageData_ofList(v___x_1378_);
v___x_1380_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1380_, 0, v___x_1376_);
lean_ctor_set(v___x_1380_, 1, v___x_1379_);
v___x_1381_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_1298_, v___x_1380_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
if (lean_obj_tag(v___x_1381_) == 0)
{
lean_dec_ref_known(v___x_1381_, 1);
v___y_1310_ = v___y_1350_;
v___y_1311_ = v_a_1371_;
v___y_1312_ = v___y_1352_;
v___y_1313_ = v___y_1353_;
v___y_1314_ = v___y_1354_;
v___y_1315_ = v___y_1355_;
goto v___jp_1309_;
}
else
{
lean_object* v_a_1382_; lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1389_; 
lean_dec(v_a_1371_);
lean_dec_ref(v___y_1350_);
lean_dec_ref(v_funTypes_1302_);
lean_dec_ref(v_preDefs_1295_);
lean_dec(v___x_1294_);
lean_dec_ref(v_xs_1293_);
lean_dec_ref(v_fixedParamPerms_1292_);
lean_dec_ref(v___x_1290_);
lean_dec_ref(v_recArgInfos_1288_);
v_a_1382_ = lean_ctor_get(v___x_1381_, 0);
v_isSharedCheck_1389_ = !lean_is_exclusive(v___x_1381_);
if (v_isSharedCheck_1389_ == 0)
{
v___x_1384_ = v___x_1381_;
v_isShared_1385_ = v_isSharedCheck_1389_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_a_1382_);
lean_dec(v___x_1381_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1389_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
lean_object* v___x_1387_; 
if (v_isShared_1385_ == 0)
{
v___x_1387_ = v___x_1384_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v_a_1382_);
v___x_1387_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
return v___x_1387_;
}
}
}
}
}
}
else
{
lean_object* v_a_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1397_; 
lean_dec_ref(v___y_1350_);
lean_dec_ref(v_funTypes_1302_);
lean_dec(v___x_1298_);
lean_dec_ref(v_preDefs_1295_);
lean_dec(v___x_1294_);
lean_dec_ref(v_xs_1293_);
lean_dec_ref(v_fixedParamPerms_1292_);
lean_dec_ref(v___x_1290_);
lean_dec_ref(v_recArgInfos_1288_);
v_a_1390_ = lean_ctor_get(v___x_1366_, 0);
v_isSharedCheck_1397_ = !lean_is_exclusive(v___x_1366_);
if (v_isSharedCheck_1397_ == 0)
{
v___x_1392_ = v___x_1366_;
v_isShared_1393_ = v_isSharedCheck_1397_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_a_1390_);
lean_dec(v___x_1366_);
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
else
{
lean_object* v_a_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1405_; 
lean_dec_ref(v_FArgs_1351_);
lean_dec_ref(v___y_1350_);
lean_dec_ref(v_funTypes_1302_);
lean_dec(v___x_1298_);
lean_dec_ref(v___f_1297_);
lean_dec_ref(v_preDefs_1295_);
lean_dec(v___x_1294_);
lean_dec_ref(v_xs_1293_);
lean_dec_ref(v_fixedParamPerms_1292_);
lean_dec_ref(v___x_1290_);
lean_dec_ref(v_recArgInfos_1288_);
v_a_1398_ = lean_ctor_get(v___x_1364_, 0);
v_isSharedCheck_1405_ = !lean_is_exclusive(v___x_1364_);
if (v_isSharedCheck_1405_ == 0)
{
v___x_1400_ = v___x_1364_;
v_isShared_1401_ = v_isSharedCheck_1405_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_a_1398_);
lean_dec(v___x_1364_);
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
v___jp_1406_:
{
if (v_a_1299_ == 0)
{
lean_object* v___x_1413_; lean_object* v_levelParams_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; size_t v_sz_1417_; lean_object* v___x_1418_; 
v___x_1413_ = lean_array_get_borrowed(v___x_1300_, v_preDefs_1295_, v___x_1294_);
v_levelParams_1414_ = lean_ctor_get(v___x_1413_, 1);
v___x_1415_ = lean_box(0);
lean_inc(v_levelParams_1414_);
v___x_1416_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__15(v_levelParams_1414_, v___x_1415_);
v_sz_1417_ = lean_array_size(v___y_1408_);
lean_inc_ref(v_preDefs_1295_);
v___x_1418_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___redArg(v_preDefs_1295_, v_xs_1293_, v_a_1299_, v___x_1416_, v_sz_1417_, v___x_1291_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_);
if (lean_obj_tag(v___x_1418_) == 0)
{
lean_object* v_a_1419_; 
v_a_1419_ = lean_ctor_get(v___x_1418_, 0);
lean_inc(v_a_1419_);
lean_dec_ref_known(v___x_1418_, 1);
v___y_1350_ = v___y_1407_;
v_FArgs_1351_ = v_a_1419_;
v___y_1352_ = v___y_1409_;
v___y_1353_ = v___y_1410_;
v___y_1354_ = v___y_1411_;
v___y_1355_ = v___y_1412_;
goto v___jp_1349_;
}
else
{
lean_object* v_a_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1427_; 
lean_dec_ref(v___y_1407_);
lean_dec_ref(v_funTypes_1302_);
lean_dec(v___x_1298_);
lean_dec_ref(v___f_1297_);
lean_dec_ref(v_preDefs_1295_);
lean_dec(v___x_1294_);
lean_dec_ref(v_xs_1293_);
lean_dec_ref(v_fixedParamPerms_1292_);
lean_dec_ref(v___x_1290_);
lean_dec_ref(v_recArgInfos_1288_);
v_a_1420_ = lean_ctor_get(v___x_1418_, 0);
v_isSharedCheck_1427_ = !lean_is_exclusive(v___x_1418_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1422_ = v___x_1418_;
v_isShared_1423_ = v_isSharedCheck_1427_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_a_1420_);
lean_dec(v___x_1418_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1427_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
lean_object* v___x_1425_; 
if (v_isShared_1423_ == 0)
{
v___x_1425_ = v___x_1422_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v_a_1420_);
v___x_1425_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
return v___x_1425_;
}
}
}
}
else
{
v___y_1350_ = v___y_1407_;
v_FArgs_1351_ = v___y_1408_;
v___y_1352_ = v___y_1409_;
v___y_1353_ = v___y_1410_;
v___y_1354_ = v___y_1411_;
v___y_1355_ = v___y_1412_;
goto v___jp_1349_;
}
}
v___jp_1428_:
{
size_t v_sz_1435_; lean_object* v___x_1436_; 
v_sz_1435_ = lean_array_size(v_recArgInfos_1288_);
lean_inc_ref(v___y_1430_);
lean_inc_ref(v_preDefs_1295_);
lean_inc_ref(v___x_1290_);
lean_inc_ref_n(v_recArgInfos_1288_, 2);
v___x_1436_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg(v_a_1299_, v_a_1289_, v___y_1429_, v_recArgInfos_1288_, v___x_1290_, v_preDefs_1295_, v___y_1430_, v_sz_1435_, v___x_1291_, v_recArgInfos_1288_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_);
lean_dec_ref(v___y_1429_);
if (lean_obj_tag(v___x_1436_) == 0)
{
lean_object* v_a_1437_; lean_object* v___x_1438_; 
v_a_1437_ = lean_ctor_get(v___x_1436_, 0);
lean_inc(v_a_1437_);
lean_dec_ref_known(v___x_1436_, 1);
lean_inc(v___y_1434_);
lean_inc_ref(v___y_1433_);
lean_inc(v___y_1432_);
lean_inc_ref(v___y_1431_);
v___x_1438_ = lean_apply_5(v___f_1301_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_, lean_box(0));
if (lean_obj_tag(v___x_1438_) == 0)
{
lean_object* v_a_1439_; uint8_t v___x_1440_; 
v_a_1439_ = lean_ctor_get(v___x_1438_, 0);
lean_inc(v_a_1439_);
lean_dec_ref_known(v___x_1438_, 1);
v___x_1440_ = lean_unbox(v_a_1439_);
lean_dec(v_a_1439_);
if (v___x_1440_ == 0)
{
v___y_1407_ = v___y_1430_;
v___y_1408_ = v_a_1437_;
v___y_1409_ = v___y_1431_;
v___y_1410_ = v___y_1432_;
v___y_1411_ = v___y_1433_;
v___y_1412_ = v___y_1434_;
goto v___jp_1406_;
}
else
{
lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; 
v___x_1441_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__6, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__6);
lean_inc(v_a_1437_);
v___x_1442_ = lean_array_to_list(v_a_1437_);
v___x_1443_ = lean_box(0);
v___x_1444_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_1442_, v___x_1443_);
v___x_1445_ = l_Lean_MessageData_ofList(v___x_1444_);
v___x_1446_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1446_, 0, v___x_1441_);
lean_ctor_set(v___x_1446_, 1, v___x_1445_);
lean_inc(v___x_1298_);
v___x_1447_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_1298_, v___x_1446_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_);
if (lean_obj_tag(v___x_1447_) == 0)
{
lean_dec_ref_known(v___x_1447_, 1);
v___y_1407_ = v___y_1430_;
v___y_1408_ = v_a_1437_;
v___y_1409_ = v___y_1431_;
v___y_1410_ = v___y_1432_;
v___y_1411_ = v___y_1433_;
v___y_1412_ = v___y_1434_;
goto v___jp_1406_;
}
else
{
lean_object* v_a_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1455_; 
lean_dec(v_a_1437_);
lean_dec_ref(v___y_1430_);
lean_dec_ref(v_funTypes_1302_);
lean_dec(v___x_1298_);
lean_dec_ref(v___f_1297_);
lean_dec_ref(v_preDefs_1295_);
lean_dec(v___x_1294_);
lean_dec_ref(v_xs_1293_);
lean_dec_ref(v_fixedParamPerms_1292_);
lean_dec_ref(v___x_1290_);
lean_dec_ref(v_recArgInfos_1288_);
v_a_1448_ = lean_ctor_get(v___x_1447_, 0);
v_isSharedCheck_1455_ = !lean_is_exclusive(v___x_1447_);
if (v_isSharedCheck_1455_ == 0)
{
v___x_1450_ = v___x_1447_;
v_isShared_1451_ = v_isSharedCheck_1455_;
goto v_resetjp_1449_;
}
else
{
lean_inc(v_a_1448_);
lean_dec(v___x_1447_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1455_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
lean_object* v___x_1453_; 
if (v_isShared_1451_ == 0)
{
v___x_1453_ = v___x_1450_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v_a_1448_);
v___x_1453_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
return v___x_1453_;
}
}
}
}
}
else
{
lean_object* v_a_1456_; lean_object* v___x_1458_; uint8_t v_isShared_1459_; uint8_t v_isSharedCheck_1463_; 
lean_dec(v_a_1437_);
lean_dec_ref(v___y_1430_);
lean_dec_ref(v_funTypes_1302_);
lean_dec(v___x_1298_);
lean_dec_ref(v___f_1297_);
lean_dec_ref(v_preDefs_1295_);
lean_dec(v___x_1294_);
lean_dec_ref(v_xs_1293_);
lean_dec_ref(v_fixedParamPerms_1292_);
lean_dec_ref(v___x_1290_);
lean_dec_ref(v_recArgInfos_1288_);
v_a_1456_ = lean_ctor_get(v___x_1438_, 0);
v_isSharedCheck_1463_ = !lean_is_exclusive(v___x_1438_);
if (v_isSharedCheck_1463_ == 0)
{
v___x_1458_ = v___x_1438_;
v_isShared_1459_ = v_isSharedCheck_1463_;
goto v_resetjp_1457_;
}
else
{
lean_inc(v_a_1456_);
lean_dec(v___x_1438_);
v___x_1458_ = lean_box(0);
v_isShared_1459_ = v_isSharedCheck_1463_;
goto v_resetjp_1457_;
}
v_resetjp_1457_:
{
lean_object* v___x_1461_; 
if (v_isShared_1459_ == 0)
{
v___x_1461_ = v___x_1458_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v_a_1456_);
v___x_1461_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
return v___x_1461_;
}
}
}
}
else
{
lean_object* v_a_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1471_; 
lean_dec_ref(v___y_1430_);
lean_dec_ref(v_funTypes_1302_);
lean_dec_ref(v___f_1301_);
lean_dec(v___x_1298_);
lean_dec_ref(v___f_1297_);
lean_dec_ref(v_preDefs_1295_);
lean_dec(v___x_1294_);
lean_dec_ref(v_xs_1293_);
lean_dec_ref(v_fixedParamPerms_1292_);
lean_dec_ref(v___x_1290_);
lean_dec_ref(v_recArgInfos_1288_);
v_a_1464_ = lean_ctor_get(v___x_1436_, 0);
v_isSharedCheck_1471_ = !lean_is_exclusive(v___x_1436_);
if (v_isSharedCheck_1471_ == 0)
{
v___x_1466_ = v___x_1436_;
v_isShared_1467_ = v_isSharedCheck_1471_;
goto v_resetjp_1465_;
}
else
{
lean_inc(v_a_1464_);
lean_dec(v___x_1436_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1471_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v___x_1469_; 
if (v_isShared_1467_ == 0)
{
v___x_1469_ = v___x_1466_;
goto v_reusejp_1468_;
}
else
{
lean_object* v_reuseFailAlloc_1470_; 
v_reuseFailAlloc_1470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1470_, 0, v_a_1464_);
v___x_1469_ = v_reuseFailAlloc_1470_;
goto v_reusejp_1468_;
}
v_reusejp_1468_:
{
return v___x_1469_;
}
}
}
}
v___jp_1472_:
{
lean_object* v___x_1473_; 
v___x_1473_ = l_Lean_Elab_Structural_mkBRecOnConst(v_recArgInfos_1288_, v___x_1290_, v_motives_1303_, v_a_1299_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_);
lean_dec_ref(v_motives_1303_);
if (lean_obj_tag(v___x_1473_) == 0)
{
lean_object* v_a_1474_; lean_object* v___x_1475_; 
v_a_1474_ = lean_ctor_get(v___x_1473_, 0);
lean_inc_n(v_a_1474_, 2);
lean_dec_ref_known(v___x_1473_, 1);
lean_inc_ref(v___x_1290_);
v___x_1475_ = l_Lean_Elab_Structural_inferBRecOnFTypes(v_recArgInfos_1288_, v___x_1290_, v_a_1474_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_);
if (lean_obj_tag(v___x_1475_) == 0)
{
lean_object* v_a_1476_; lean_object* v___x_1477_; 
v_a_1476_ = lean_ctor_get(v___x_1475_, 0);
lean_inc(v_a_1476_);
lean_dec_ref_known(v___x_1475_, 1);
lean_inc_ref(v___f_1301_);
lean_inc(v___y_1307_);
lean_inc_ref(v___y_1306_);
lean_inc(v___y_1305_);
lean_inc_ref(v___y_1304_);
v___x_1477_ = lean_apply_5(v___f_1301_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, lean_box(0));
if (lean_obj_tag(v___x_1477_) == 0)
{
lean_object* v_a_1478_; uint8_t v___x_1479_; 
v_a_1478_ = lean_ctor_get(v___x_1477_, 0);
lean_inc(v_a_1478_);
lean_dec_ref_known(v___x_1477_, 1);
v___x_1479_ = lean_unbox(v_a_1478_);
lean_dec(v_a_1478_);
if (v___x_1479_ == 0)
{
v___y_1429_ = v_a_1476_;
v___y_1430_ = v_a_1474_;
v___y_1431_ = v___y_1304_;
v___y_1432_ = v___y_1305_;
v___y_1433_ = v___y_1306_;
v___y_1434_ = v___y_1307_;
goto v___jp_1428_;
}
else
{
lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; 
v___x_1480_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__8);
lean_inc(v_a_1476_);
v___x_1481_ = lean_array_to_list(v_a_1476_);
v___x_1482_ = lean_box(0);
v___x_1483_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_1481_, v___x_1482_);
v___x_1484_ = l_Lean_MessageData_ofList(v___x_1483_);
v___x_1485_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1485_, 0, v___x_1480_);
lean_ctor_set(v___x_1485_, 1, v___x_1484_);
lean_inc(v___x_1298_);
v___x_1486_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_1298_, v___x_1485_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_);
if (lean_obj_tag(v___x_1486_) == 0)
{
lean_dec_ref_known(v___x_1486_, 1);
v___y_1429_ = v_a_1476_;
v___y_1430_ = v_a_1474_;
v___y_1431_ = v___y_1304_;
v___y_1432_ = v___y_1305_;
v___y_1433_ = v___y_1306_;
v___y_1434_ = v___y_1307_;
goto v___jp_1428_;
}
else
{
lean_object* v_a_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1494_; 
lean_dec(v_a_1476_);
lean_dec(v_a_1474_);
lean_dec_ref(v_funTypes_1302_);
lean_dec_ref(v___f_1301_);
lean_dec(v___x_1298_);
lean_dec_ref(v___f_1297_);
lean_dec_ref(v_preDefs_1295_);
lean_dec(v___x_1294_);
lean_dec_ref(v_xs_1293_);
lean_dec_ref(v_fixedParamPerms_1292_);
lean_dec_ref(v___x_1290_);
lean_dec_ref(v_recArgInfos_1288_);
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
lean_dec(v_a_1476_);
lean_dec(v_a_1474_);
lean_dec_ref(v_funTypes_1302_);
lean_dec_ref(v___f_1301_);
lean_dec(v___x_1298_);
lean_dec_ref(v___f_1297_);
lean_dec_ref(v_preDefs_1295_);
lean_dec(v___x_1294_);
lean_dec_ref(v_xs_1293_);
lean_dec_ref(v_fixedParamPerms_1292_);
lean_dec_ref(v___x_1290_);
lean_dec_ref(v_recArgInfos_1288_);
v_a_1495_ = lean_ctor_get(v___x_1477_, 0);
v_isSharedCheck_1502_ = !lean_is_exclusive(v___x_1477_);
if (v_isSharedCheck_1502_ == 0)
{
v___x_1497_ = v___x_1477_;
v_isShared_1498_ = v_isSharedCheck_1502_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_a_1495_);
lean_dec(v___x_1477_);
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
}
else
{
lean_object* v_a_1503_; lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1510_; 
lean_dec(v_a_1474_);
lean_dec_ref(v_funTypes_1302_);
lean_dec_ref(v___f_1301_);
lean_dec(v___x_1298_);
lean_dec_ref(v___f_1297_);
lean_dec_ref(v_preDefs_1295_);
lean_dec(v___x_1294_);
lean_dec_ref(v_xs_1293_);
lean_dec_ref(v_fixedParamPerms_1292_);
lean_dec_ref(v___x_1290_);
lean_dec_ref(v_recArgInfos_1288_);
v_a_1503_ = lean_ctor_get(v___x_1475_, 0);
v_isSharedCheck_1510_ = !lean_is_exclusive(v___x_1475_);
if (v_isSharedCheck_1510_ == 0)
{
v___x_1505_ = v___x_1475_;
v_isShared_1506_ = v_isSharedCheck_1510_;
goto v_resetjp_1504_;
}
else
{
lean_inc(v_a_1503_);
lean_dec(v___x_1475_);
v___x_1505_ = lean_box(0);
v_isShared_1506_ = v_isSharedCheck_1510_;
goto v_resetjp_1504_;
}
v_resetjp_1504_:
{
lean_object* v___x_1508_; 
if (v_isShared_1506_ == 0)
{
v___x_1508_ = v___x_1505_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v_a_1503_);
v___x_1508_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
return v___x_1508_;
}
}
}
}
else
{
lean_object* v_a_1511_; lean_object* v___x_1513_; uint8_t v_isShared_1514_; uint8_t v_isSharedCheck_1518_; 
lean_dec_ref(v_funTypes_1302_);
lean_dec_ref(v___f_1301_);
lean_dec(v___x_1298_);
lean_dec_ref(v___f_1297_);
lean_dec_ref(v_preDefs_1295_);
lean_dec(v___x_1294_);
lean_dec_ref(v_xs_1293_);
lean_dec_ref(v_fixedParamPerms_1292_);
lean_dec_ref(v___x_1290_);
lean_dec_ref(v_recArgInfos_1288_);
v_a_1511_ = lean_ctor_get(v___x_1473_, 0);
v_isSharedCheck_1518_ = !lean_is_exclusive(v___x_1473_);
if (v_isSharedCheck_1518_ == 0)
{
v___x_1513_ = v___x_1473_;
v_isShared_1514_ = v_isSharedCheck_1518_;
goto v_resetjp_1512_;
}
else
{
lean_inc(v_a_1511_);
lean_dec(v___x_1473_);
v___x_1513_ = lean_box(0);
v_isShared_1514_ = v_isSharedCheck_1518_;
goto v_resetjp_1512_;
}
v_resetjp_1512_:
{
lean_object* v___x_1516_; 
if (v_isShared_1514_ == 0)
{
v___x_1516_ = v___x_1513_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v_a_1511_);
v___x_1516_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
return v___x_1516_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___boxed(lean_object** _args){
lean_object* v_recArgInfos_1551_ = _args[0];
lean_object* v_a_1552_ = _args[1];
lean_object* v___x_1553_ = _args[2];
lean_object* v___x_1554_ = _args[3];
lean_object* v_fixedParamPerms_1555_ = _args[4];
lean_object* v_xs_1556_ = _args[5];
lean_object* v___x_1557_ = _args[6];
lean_object* v_preDefs_1558_ = _args[7];
lean_object* v_numIndices_1559_ = _args[8];
lean_object* v___f_1560_ = _args[9];
lean_object* v___x_1561_ = _args[10];
lean_object* v_a_1562_ = _args[11];
lean_object* v___x_1563_ = _args[12];
lean_object* v___f_1564_ = _args[13];
lean_object* v_funTypes_1565_ = _args[14];
lean_object* v_motives_1566_ = _args[15];
lean_object* v___y_1567_ = _args[16];
lean_object* v___y_1568_ = _args[17];
lean_object* v___y_1569_ = _args[18];
lean_object* v___y_1570_ = _args[19];
lean_object* v___y_1571_ = _args[20];
_start:
{
size_t v___x_28256__boxed_1572_; uint8_t v_a_28260__boxed_1573_; lean_object* v_res_1574_; 
v___x_28256__boxed_1572_ = lean_unbox_usize(v___x_1554_);
lean_dec(v___x_1554_);
v_a_28260__boxed_1573_ = lean_unbox(v_a_1562_);
v_res_1574_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2(v_recArgInfos_1551_, v_a_1552_, v___x_1553_, v___x_28256__boxed_1572_, v_fixedParamPerms_1555_, v_xs_1556_, v___x_1557_, v_preDefs_1558_, v_numIndices_1559_, v___f_1560_, v___x_1561_, v_a_28260__boxed_1573_, v___x_1563_, v___f_1564_, v_funTypes_1565_, v_motives_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_);
lean_dec(v___y_1570_);
lean_dec_ref(v___y_1569_);
lean_dec(v___y_1568_);
lean_dec_ref(v___y_1567_);
lean_dec_ref(v___x_1563_);
lean_dec(v_numIndices_1559_);
lean_dec_ref(v_a_1552_);
return v_res_1574_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__20___redArg(lean_object* v_a_1575_, lean_object* v_funTypes_1576_, size_t v_sz_1577_, size_t v_i_1578_, lean_object* v_bs_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_){
_start:
{
uint8_t v___x_1585_; 
v___x_1585_ = lean_usize_dec_lt(v_i_1578_, v_sz_1577_);
if (v___x_1585_ == 0)
{
lean_object* v___x_1586_; 
v___x_1586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1586_, 0, v_bs_1579_);
return v___x_1586_;
}
else
{
lean_object* v___x_1587_; lean_object* v_v_1588_; lean_object* v___x_1589_; lean_object* v_bs_x27_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; 
v___x_1587_ = l_Lean_instInhabitedExpr;
v_v_1588_ = lean_array_uget(v_bs_1579_, v_i_1578_);
v___x_1589_ = lean_unsigned_to_nat(0u);
v_bs_x27_1590_ = lean_array_uset(v_bs_1579_, v_i_1578_, v___x_1589_);
v___x_1591_ = lean_usize_to_nat(v_i_1578_);
v___x_1592_ = lean_array_get_borrowed(v___x_1587_, v_a_1575_, v___x_1591_);
v___x_1593_ = lean_array_get_borrowed(v___x_1587_, v_funTypes_1576_, v___x_1591_);
lean_dec(v___x_1591_);
lean_inc(v___x_1593_);
lean_inc(v___x_1592_);
v___x_1594_ = l_Lean_Elab_Structural_mkIndPredBRecOnMotive(v_v_1588_, v___x_1592_, v___x_1593_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_);
if (lean_obj_tag(v___x_1594_) == 0)
{
lean_object* v_a_1595_; size_t v___x_1596_; size_t v___x_1597_; lean_object* v___x_1598_; 
v_a_1595_ = lean_ctor_get(v___x_1594_, 0);
lean_inc(v_a_1595_);
lean_dec_ref_known(v___x_1594_, 1);
v___x_1596_ = ((size_t)1ULL);
v___x_1597_ = lean_usize_add(v_i_1578_, v___x_1596_);
v___x_1598_ = lean_array_uset(v_bs_x27_1590_, v_i_1578_, v_a_1595_);
v_i_1578_ = v___x_1597_;
v_bs_1579_ = v___x_1598_;
goto _start;
}
else
{
lean_object* v_a_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1607_; 
lean_dec_ref(v_bs_x27_1590_);
v_a_1600_ = lean_ctor_get(v___x_1594_, 0);
v_isSharedCheck_1607_ = !lean_is_exclusive(v___x_1594_);
if (v_isSharedCheck_1607_ == 0)
{
v___x_1602_ = v___x_1594_;
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_a_1600_);
lean_dec(v___x_1594_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1605_; 
if (v_isShared_1603_ == 0)
{
v___x_1605_ = v___x_1602_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v_a_1600_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
return v___x_1605_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__20___redArg___boxed(lean_object* v_a_1608_, lean_object* v_funTypes_1609_, lean_object* v_sz_1610_, lean_object* v_i_1611_, lean_object* v_bs_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_){
_start:
{
size_t v_sz_boxed_1618_; size_t v_i_boxed_1619_; lean_object* v_res_1620_; 
v_sz_boxed_1618_ = lean_unbox_usize(v_sz_1610_);
lean_dec(v_sz_1610_);
v_i_boxed_1619_ = lean_unbox_usize(v_i_1611_);
lean_dec(v_i_1611_);
v_res_1620_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__20___redArg(v_a_1608_, v_funTypes_1609_, v_sz_boxed_1618_, v_i_boxed_1619_, v_bs_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_);
lean_dec(v___y_1616_);
lean_dec_ref(v___y_1615_);
lean_dec(v___y_1614_);
lean_dec_ref(v___y_1613_);
lean_dec_ref(v_funTypes_1609_);
lean_dec_ref(v_a_1608_);
return v_res_1620_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__3(lean_object* v_recArgInfos_1621_, lean_object* v_a_1622_, size_t v___x_1623_, lean_object* v___f_1624_, lean_object* v_funTypes_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_){
_start:
{
size_t v_sz_1631_; lean_object* v___x_1632_; 
v_sz_1631_ = lean_array_size(v_recArgInfos_1621_);
v___x_1632_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__20___redArg(v_a_1622_, v_funTypes_1625_, v_sz_1631_, v___x_1623_, v_recArgInfos_1621_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
if (lean_obj_tag(v___x_1632_) == 0)
{
lean_object* v_a_1633_; lean_object* v___x_1634_; 
v_a_1633_ = lean_ctor_get(v___x_1632_, 0);
lean_inc(v_a_1633_);
lean_dec_ref_known(v___x_1632_, 1);
lean_inc(v___y_1629_);
lean_inc_ref(v___y_1628_);
lean_inc(v___y_1627_);
lean_inc_ref(v___y_1626_);
v___x_1634_ = lean_apply_7(v___f_1624_, v_funTypes_1625_, v_a_1633_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, lean_box(0));
return v___x_1634_;
}
else
{
lean_object* v_a_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1642_; 
lean_dec_ref(v_funTypes_1625_);
lean_dec_ref(v___f_1624_);
v_a_1635_ = lean_ctor_get(v___x_1632_, 0);
v_isSharedCheck_1642_ = !lean_is_exclusive(v___x_1632_);
if (v_isSharedCheck_1642_ == 0)
{
v___x_1637_ = v___x_1632_;
v_isShared_1638_ = v_isSharedCheck_1642_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_a_1635_);
lean_dec(v___x_1632_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__3___boxed(lean_object* v_recArgInfos_1643_, lean_object* v_a_1644_, lean_object* v___x_1645_, lean_object* v___f_1646_, lean_object* v_funTypes_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_){
_start:
{
size_t v___x_28846__boxed_1653_; lean_object* v_res_1654_; 
v___x_28846__boxed_1653_ = lean_unbox_usize(v___x_1645_);
lean_dec(v___x_1645_);
v_res_1654_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__3(v_recArgInfos_1643_, v_a_1644_, v___x_28846__boxed_1653_, v___f_1646_, v_funTypes_1647_, v___y_1648_, v___y_1649_, v___y_1650_, v___y_1651_);
lean_dec(v___y_1651_);
lean_dec_ref(v___y_1650_);
lean_dec(v___y_1649_);
lean_dec_ref(v___y_1648_);
lean_dec_ref(v_a_1644_);
return v_res_1654_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg(lean_object* v_msg_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_){
_start:
{
lean_object* v_ref_1661_; lean_object* v___x_1662_; lean_object* v_a_1663_; lean_object* v___x_1665_; uint8_t v_isShared_1666_; uint8_t v_isSharedCheck_1671_; 
v_ref_1661_ = lean_ctor_get(v___y_1658_, 2);
v___x_1662_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11_spec__21(v_msg_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_);
v_a_1663_ = lean_ctor_get(v___x_1662_, 0);
v_isSharedCheck_1671_ = !lean_is_exclusive(v___x_1662_);
if (v_isSharedCheck_1671_ == 0)
{
v___x_1665_ = v___x_1662_;
v_isShared_1666_ = v_isSharedCheck_1671_;
goto v_resetjp_1664_;
}
else
{
lean_inc(v_a_1663_);
lean_dec(v___x_1662_);
v___x_1665_ = lean_box(0);
v_isShared_1666_ = v_isSharedCheck_1671_;
goto v_resetjp_1664_;
}
v_resetjp_1664_:
{
lean_object* v___x_1667_; lean_object* v___x_1669_; 
lean_inc(v_ref_1661_);
v___x_1667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1667_, 0, v_ref_1661_);
lean_ctor_set(v___x_1667_, 1, v_a_1663_);
if (v_isShared_1666_ == 0)
{
lean_ctor_set_tag(v___x_1665_, 1);
lean_ctor_set(v___x_1665_, 0, v___x_1667_);
v___x_1669_ = v___x_1665_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v___x_1667_);
v___x_1669_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
return v___x_1669_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg___boxed(lean_object* v_msg_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_){
_start:
{
lean_object* v_res_1678_; 
v_res_1678_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg(v_msg_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_);
lean_dec(v___y_1676_);
lean_dec_ref(v___y_1675_);
lean_dec(v___y_1674_);
lean_dec_ref(v___y_1673_);
return v_res_1678_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1680_; lean_object* v___x_1681_; 
v___x_1680_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__0));
v___x_1681_ = l_Lean_stringToMessageData(v___x_1680_);
return v___x_1681_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__3(void){
_start:
{
lean_object* v___x_1683_; lean_object* v___x_1684_; 
v___x_1683_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__2));
v___x_1684_ = l_Lean_stringToMessageData(v___x_1683_);
return v___x_1684_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4(lean_object* v_constName_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_){
_start:
{
lean_object* v___x_1691_; lean_object* v_env_1692_; lean_object* v___x_1693_; 
v___x_1691_ = lean_st_ref_get(v___y_1689_);
v_env_1692_ = lean_ctor_get(v___x_1691_, 0);
lean_inc_ref(v_env_1692_);
lean_dec(v___x_1691_);
lean_inc(v_constName_1685_);
v___x_1693_ = l_Lean_isInductiveCore_x3f(v_env_1692_, v_constName_1685_);
if (lean_obj_tag(v___x_1693_) == 0)
{
lean_object* v___x_1694_; uint8_t v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; 
v___x_1694_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__1, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__1);
v___x_1695_ = 0;
v___x_1696_ = l_Lean_MessageData_ofConstName(v_constName_1685_, v___x_1695_);
v___x_1697_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1697_, 0, v___x_1694_);
lean_ctor_set(v___x_1697_, 1, v___x_1696_);
v___x_1698_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__3, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__3_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__3);
v___x_1699_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1699_, 0, v___x_1697_);
lean_ctor_set(v___x_1699_, 1, v___x_1698_);
v___x_1700_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg(v___x_1699_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_);
return v___x_1700_;
}
else
{
lean_object* v_val_1701_; lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1708_; 
lean_dec(v_constName_1685_);
v_val_1701_ = lean_ctor_get(v___x_1693_, 0);
v_isSharedCheck_1708_ = !lean_is_exclusive(v___x_1693_);
if (v_isSharedCheck_1708_ == 0)
{
v___x_1703_ = v___x_1693_;
v_isShared_1704_ = v_isSharedCheck_1708_;
goto v_resetjp_1702_;
}
else
{
lean_inc(v_val_1701_);
lean_dec(v___x_1693_);
v___x_1703_ = lean_box(0);
v_isShared_1704_ = v_isSharedCheck_1708_;
goto v_resetjp_1702_;
}
v_resetjp_1702_:
{
lean_object* v___x_1706_; 
if (v_isShared_1704_ == 0)
{
lean_ctor_set_tag(v___x_1703_, 0);
v___x_1706_ = v___x_1703_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v_val_1701_);
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
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___boxed(lean_object* v_constName_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_){
_start:
{
lean_object* v_res_1715_; 
v_res_1715_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4(v_constName_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_);
lean_dec(v___y_1713_);
lean_dec_ref(v___y_1712_);
lean_dec(v___y_1711_);
lean_dec_ref(v___y_1710_);
return v_res_1715_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___redArg(lean_object* v_fixedParamPerms_1716_, lean_object* v_xs_1717_, size_t v_sz_1718_, size_t v_i_1719_, lean_object* v_bs_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_){
_start:
{
uint8_t v___x_1726_; 
v___x_1726_ = lean_usize_dec_lt(v_i_1719_, v_sz_1718_);
if (v___x_1726_ == 0)
{
lean_object* v___x_1727_; 
lean_dec_ref(v_xs_1717_);
v___x_1727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1727_, 0, v_bs_1720_);
return v___x_1727_;
}
else
{
lean_object* v_v_1728_; lean_object* v_perms_1729_; lean_object* v_type_1730_; lean_object* v___x_1731_; lean_object* v_bs_x27_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; 
v_v_1728_ = lean_array_uget_borrowed(v_bs_1720_, v_i_1719_);
v_perms_1729_ = lean_ctor_get(v_fixedParamPerms_1716_, 1);
v_type_1730_ = lean_ctor_get(v_v_1728_, 6);
lean_inc_ref(v_type_1730_);
v___x_1731_ = lean_unsigned_to_nat(0u);
v_bs_x27_1732_ = lean_array_uset(v_bs_1720_, v_i_1719_, v___x_1731_);
v___x_1733_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0);
v___x_1734_ = lean_usize_to_nat(v_i_1719_);
v___x_1735_ = lean_array_get_borrowed(v___x_1733_, v_perms_1729_, v___x_1734_);
lean_dec(v___x_1734_);
lean_inc_ref(v_xs_1717_);
lean_inc(v___x_1735_);
v___x_1736_ = l_Lean_Elab_FixedParamPerm_instantiateForall(v___x_1735_, v_type_1730_, v_xs_1717_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_);
if (lean_obj_tag(v___x_1736_) == 0)
{
lean_object* v_a_1737_; size_t v___x_1738_; size_t v___x_1739_; lean_object* v___x_1740_; 
v_a_1737_ = lean_ctor_get(v___x_1736_, 0);
lean_inc(v_a_1737_);
lean_dec_ref_known(v___x_1736_, 1);
v___x_1738_ = ((size_t)1ULL);
v___x_1739_ = lean_usize_add(v_i_1719_, v___x_1738_);
v___x_1740_ = lean_array_uset(v_bs_x27_1732_, v_i_1719_, v_a_1737_);
v_i_1719_ = v___x_1739_;
v_bs_1720_ = v___x_1740_;
goto _start;
}
else
{
lean_object* v_a_1742_; lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1749_; 
lean_dec_ref(v_bs_x27_1732_);
lean_dec_ref(v_xs_1717_);
v_a_1742_ = lean_ctor_get(v___x_1736_, 0);
v_isSharedCheck_1749_ = !lean_is_exclusive(v___x_1736_);
if (v_isSharedCheck_1749_ == 0)
{
v___x_1744_ = v___x_1736_;
v_isShared_1745_ = v_isSharedCheck_1749_;
goto v_resetjp_1743_;
}
else
{
lean_inc(v_a_1742_);
lean_dec(v___x_1736_);
v___x_1744_ = lean_box(0);
v_isShared_1745_ = v_isSharedCheck_1749_;
goto v_resetjp_1743_;
}
v_resetjp_1743_:
{
lean_object* v___x_1747_; 
if (v_isShared_1745_ == 0)
{
v___x_1747_ = v___x_1744_;
goto v_reusejp_1746_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v_a_1742_);
v___x_1747_ = v_reuseFailAlloc_1748_;
goto v_reusejp_1746_;
}
v_reusejp_1746_:
{
return v___x_1747_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___redArg___boxed(lean_object* v_fixedParamPerms_1750_, lean_object* v_xs_1751_, lean_object* v_sz_1752_, lean_object* v_i_1753_, lean_object* v_bs_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_){
_start:
{
size_t v_sz_boxed_1760_; size_t v_i_boxed_1761_; lean_object* v_res_1762_; 
v_sz_boxed_1760_ = lean_unbox_usize(v_sz_1752_);
lean_dec(v_sz_1752_);
v_i_boxed_1761_ = lean_unbox_usize(v_i_1753_);
lean_dec(v_i_1753_);
v_res_1762_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___redArg(v_fixedParamPerms_1750_, v_xs_1751_, v_sz_boxed_1760_, v_i_boxed_1761_, v_bs_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_);
lean_dec(v___y_1758_);
lean_dec_ref(v___y_1757_);
lean_dec(v___y_1756_);
lean_dec_ref(v___y_1755_);
lean_dec_ref(v_fixedParamPerms_1750_);
return v_res_1762_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___redArg(lean_object* v_fixedParamPerms_1763_, lean_object* v_xs_1764_, size_t v_sz_1765_, size_t v_i_1766_, lean_object* v_bs_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_){
_start:
{
uint8_t v___x_1773_; 
v___x_1773_ = lean_usize_dec_lt(v_i_1766_, v_sz_1765_);
if (v___x_1773_ == 0)
{
lean_object* v___x_1774_; 
lean_dec_ref(v_xs_1764_);
v___x_1774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1774_, 0, v_bs_1767_);
return v___x_1774_;
}
else
{
lean_object* v_v_1775_; lean_object* v_perms_1776_; lean_object* v_value_1777_; lean_object* v___x_1778_; lean_object* v_bs_x27_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; 
v_v_1775_ = lean_array_uget_borrowed(v_bs_1767_, v_i_1766_);
v_perms_1776_ = lean_ctor_get(v_fixedParamPerms_1763_, 1);
v_value_1777_ = lean_ctor_get(v_v_1775_, 7);
lean_inc_ref(v_value_1777_);
v___x_1778_ = lean_unsigned_to_nat(0u);
v_bs_x27_1779_ = lean_array_uset(v_bs_1767_, v_i_1766_, v___x_1778_);
v___x_1780_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0);
v___x_1781_ = lean_usize_to_nat(v_i_1766_);
v___x_1782_ = lean_array_get_borrowed(v___x_1780_, v_perms_1776_, v___x_1781_);
lean_dec(v___x_1781_);
lean_inc_ref(v_xs_1764_);
lean_inc(v___x_1782_);
v___x_1783_ = l_Lean_Elab_FixedParamPerm_instantiateLambda(v___x_1782_, v_value_1777_, v_xs_1764_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_);
if (lean_obj_tag(v___x_1783_) == 0)
{
lean_object* v_a_1784_; size_t v___x_1785_; size_t v___x_1786_; lean_object* v___x_1787_; 
v_a_1784_ = lean_ctor_get(v___x_1783_, 0);
lean_inc(v_a_1784_);
lean_dec_ref_known(v___x_1783_, 1);
v___x_1785_ = ((size_t)1ULL);
v___x_1786_ = lean_usize_add(v_i_1766_, v___x_1785_);
v___x_1787_ = lean_array_uset(v_bs_x27_1779_, v_i_1766_, v_a_1784_);
v_i_1766_ = v___x_1786_;
v_bs_1767_ = v___x_1787_;
goto _start;
}
else
{
lean_object* v_a_1789_; lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1796_; 
lean_dec_ref(v_bs_x27_1779_);
lean_dec_ref(v_xs_1764_);
v_a_1789_ = lean_ctor_get(v___x_1783_, 0);
v_isSharedCheck_1796_ = !lean_is_exclusive(v___x_1783_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1791_ = v___x_1783_;
v_isShared_1792_ = v_isSharedCheck_1796_;
goto v_resetjp_1790_;
}
else
{
lean_inc(v_a_1789_);
lean_dec(v___x_1783_);
v___x_1791_ = lean_box(0);
v_isShared_1792_ = v_isSharedCheck_1796_;
goto v_resetjp_1790_;
}
v_resetjp_1790_:
{
lean_object* v___x_1794_; 
if (v_isShared_1792_ == 0)
{
v___x_1794_ = v___x_1791_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v_a_1789_);
v___x_1794_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
return v___x_1794_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___redArg___boxed(lean_object* v_fixedParamPerms_1797_, lean_object* v_xs_1798_, lean_object* v_sz_1799_, lean_object* v_i_1800_, lean_object* v_bs_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_){
_start:
{
size_t v_sz_boxed_1807_; size_t v_i_boxed_1808_; lean_object* v_res_1809_; 
v_sz_boxed_1807_ = lean_unbox_usize(v_sz_1799_);
lean_dec(v_sz_1799_);
v_i_boxed_1808_ = lean_unbox_usize(v_i_1800_);
lean_dec(v_i_1800_);
v_res_1809_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___redArg(v_fixedParamPerms_1797_, v_xs_1798_, v_sz_boxed_1807_, v_i_boxed_1808_, v_bs_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_);
lean_dec(v___y_1805_);
lean_dec_ref(v___y_1804_);
lean_dec(v___y_1803_);
lean_dec_ref(v___y_1802_);
lean_dec_ref(v_fixedParamPerms_1797_);
return v_res_1809_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__0(lean_object* v_a_1810_, lean_object* v_a_1811_){
_start:
{
if (lean_obj_tag(v_a_1810_) == 0)
{
lean_object* v___x_1812_; 
v___x_1812_ = l_List_reverse___redArg(v_a_1811_);
return v___x_1812_;
}
else
{
lean_object* v_head_1813_; lean_object* v_tail_1814_; lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1825_; 
v_head_1813_ = lean_ctor_get(v_a_1810_, 0);
v_tail_1814_ = lean_ctor_get(v_a_1810_, 1);
v_isSharedCheck_1825_ = !lean_is_exclusive(v_a_1810_);
if (v_isSharedCheck_1825_ == 0)
{
v___x_1816_ = v_a_1810_;
v_isShared_1817_ = v_isSharedCheck_1825_;
goto v_resetjp_1815_;
}
else
{
lean_inc(v_tail_1814_);
lean_inc(v_head_1813_);
lean_dec(v_a_1810_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1825_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1822_; 
v___x_1818_ = l_Nat_reprFast(v_head_1813_);
v___x_1819_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1819_, 0, v___x_1818_);
v___x_1820_ = l_Lean_MessageData_ofFormat(v___x_1819_);
if (v_isShared_1817_ == 0)
{
lean_ctor_set(v___x_1816_, 1, v_a_1811_);
lean_ctor_set(v___x_1816_, 0, v___x_1820_);
v___x_1822_ = v___x_1816_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1824_; 
v_reuseFailAlloc_1824_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1824_, 0, v___x_1820_);
lean_ctor_set(v_reuseFailAlloc_1824_, 1, v_a_1811_);
v___x_1822_ = v_reuseFailAlloc_1824_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
v_a_1810_ = v_tail_1814_;
v_a_1811_ = v___x_1822_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__22(lean_object* v_a_1826_, lean_object* v_a_1827_){
_start:
{
if (lean_obj_tag(v_a_1826_) == 0)
{
lean_object* v___x_1828_; 
v___x_1828_ = l_List_reverse___redArg(v_a_1827_);
return v___x_1828_;
}
else
{
lean_object* v_head_1829_; lean_object* v_tail_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1842_; 
v_head_1829_ = lean_ctor_get(v_a_1826_, 0);
v_tail_1830_ = lean_ctor_get(v_a_1826_, 1);
v_isSharedCheck_1842_ = !lean_is_exclusive(v_a_1826_);
if (v_isSharedCheck_1842_ == 0)
{
v___x_1832_ = v_a_1826_;
v_isShared_1833_ = v_isSharedCheck_1842_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_tail_1830_);
lean_inc(v_head_1829_);
lean_dec(v_a_1826_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1842_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1839_; 
v___x_1834_ = lean_array_to_list(v_head_1829_);
v___x_1835_ = lean_box(0);
v___x_1836_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__0(v___x_1834_, v___x_1835_);
v___x_1837_ = l_Lean_MessageData_ofList(v___x_1836_);
if (v_isShared_1833_ == 0)
{
lean_ctor_set(v___x_1832_, 1, v_a_1827_);
lean_ctor_set(v___x_1832_, 0, v___x_1837_);
v___x_1839_ = v___x_1832_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v___x_1837_);
lean_ctor_set(v_reuseFailAlloc_1841_, 1, v_a_1827_);
v___x_1839_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
v_a_1826_ = v_tail_1830_;
v_a_1827_ = v___x_1839_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__21___redArg(lean_object* v_a_1843_, lean_object* v_a_1844_, size_t v_sz_1845_, size_t v_i_1846_, lean_object* v_bs_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_){
_start:
{
uint8_t v___x_1853_; 
v___x_1853_ = lean_usize_dec_lt(v_i_1846_, v_sz_1845_);
if (v___x_1853_ == 0)
{
lean_object* v___x_1854_; 
v___x_1854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1854_, 0, v_bs_1847_);
return v___x_1854_;
}
else
{
lean_object* v___x_1855_; lean_object* v_v_1856_; lean_object* v___x_1857_; lean_object* v_bs_x27_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; 
v___x_1855_ = l_Lean_instInhabitedExpr;
v_v_1856_ = lean_array_uget(v_bs_1847_, v_i_1846_);
v___x_1857_ = lean_unsigned_to_nat(0u);
v_bs_x27_1858_ = lean_array_uset(v_bs_1847_, v_i_1846_, v___x_1857_);
v___x_1859_ = lean_usize_to_nat(v_i_1846_);
v___x_1860_ = lean_array_get_borrowed(v___x_1855_, v_a_1843_, v___x_1859_);
v___x_1861_ = lean_array_get_borrowed(v___x_1855_, v_a_1844_, v___x_1859_);
lean_dec(v___x_1859_);
lean_inc(v___x_1861_);
lean_inc(v___x_1860_);
v___x_1862_ = l_Lean_Elab_Structural_mkBRecOnMotive(v_v_1856_, v___x_1860_, v___x_1861_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_);
if (lean_obj_tag(v___x_1862_) == 0)
{
lean_object* v_a_1863_; size_t v___x_1864_; size_t v___x_1865_; lean_object* v___x_1866_; 
v_a_1863_ = lean_ctor_get(v___x_1862_, 0);
lean_inc(v_a_1863_);
lean_dec_ref_known(v___x_1862_, 1);
v___x_1864_ = ((size_t)1ULL);
v___x_1865_ = lean_usize_add(v_i_1846_, v___x_1864_);
v___x_1866_ = lean_array_uset(v_bs_x27_1858_, v_i_1846_, v_a_1863_);
v_i_1846_ = v___x_1865_;
v_bs_1847_ = v___x_1866_;
goto _start;
}
else
{
lean_object* v_a_1868_; lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_1875_; 
lean_dec_ref(v_bs_x27_1858_);
v_a_1868_ = lean_ctor_get(v___x_1862_, 0);
v_isSharedCheck_1875_ = !lean_is_exclusive(v___x_1862_);
if (v_isSharedCheck_1875_ == 0)
{
v___x_1870_ = v___x_1862_;
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
else
{
lean_inc(v_a_1868_);
lean_dec(v___x_1862_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
v_resetjp_1869_:
{
lean_object* v___x_1873_; 
if (v_isShared_1871_ == 0)
{
v___x_1873_ = v___x_1870_;
goto v_reusejp_1872_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v_a_1868_);
v___x_1873_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1872_;
}
v_reusejp_1872_:
{
return v___x_1873_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__21___redArg___boxed(lean_object* v_a_1876_, lean_object* v_a_1877_, lean_object* v_sz_1878_, lean_object* v_i_1879_, lean_object* v_bs_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_){
_start:
{
size_t v_sz_boxed_1886_; size_t v_i_boxed_1887_; lean_object* v_res_1888_; 
v_sz_boxed_1886_ = lean_unbox_usize(v_sz_1878_);
lean_dec(v_sz_1878_);
v_i_boxed_1887_ = lean_unbox_usize(v_i_1879_);
lean_dec(v_i_1879_);
v_res_1888_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__21___redArg(v_a_1876_, v_a_1877_, v_sz_boxed_1886_, v_i_boxed_1887_, v_bs_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_);
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1883_);
lean_dec(v___y_1882_);
lean_dec_ref(v___y_1881_);
lean_dec_ref(v_a_1877_);
lean_dec_ref(v_a_1876_);
return v_res_1888_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11___redArg(lean_object* v_hi_1889_, lean_object* v_pivot_1890_, lean_object* v_as_1891_, lean_object* v_i_1892_, lean_object* v_k_1893_){
_start:
{
uint8_t v___x_1894_; 
v___x_1894_ = lean_nat_dec_lt(v_k_1893_, v_hi_1889_);
if (v___x_1894_ == 0)
{
lean_object* v___x_1895_; lean_object* v___x_1896_; 
lean_dec(v_k_1893_);
v___x_1895_ = lean_array_fswap(v_as_1891_, v_i_1892_, v_hi_1889_);
v___x_1896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1896_, 0, v_i_1892_);
lean_ctor_set(v___x_1896_, 1, v___x_1895_);
return v___x_1896_;
}
else
{
lean_object* v___x_1897_; uint8_t v___x_1898_; 
v___x_1897_ = lean_array_fget_borrowed(v_as_1891_, v_k_1893_);
v___x_1898_ = l_Nat_blt(v___x_1897_, v_pivot_1890_);
if (v___x_1898_ == 0)
{
lean_object* v___x_1899_; lean_object* v___x_1900_; 
v___x_1899_ = lean_unsigned_to_nat(1u);
v___x_1900_ = lean_nat_add(v_k_1893_, v___x_1899_);
lean_dec(v_k_1893_);
v_k_1893_ = v___x_1900_;
goto _start;
}
else
{
lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; 
v___x_1902_ = lean_array_fswap(v_as_1891_, v_i_1892_, v_k_1893_);
v___x_1903_ = lean_unsigned_to_nat(1u);
v___x_1904_ = lean_nat_add(v_i_1892_, v___x_1903_);
lean_dec(v_i_1892_);
v___x_1905_ = lean_nat_add(v_k_1893_, v___x_1903_);
lean_dec(v_k_1893_);
v_as_1891_ = v___x_1902_;
v_i_1892_ = v___x_1904_;
v_k_1893_ = v___x_1905_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11___redArg___boxed(lean_object* v_hi_1907_, lean_object* v_pivot_1908_, lean_object* v_as_1909_, lean_object* v_i_1910_, lean_object* v_k_1911_){
_start:
{
lean_object* v_res_1912_; 
v_res_1912_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11___redArg(v_hi_1907_, v_pivot_1908_, v_as_1909_, v_i_1910_, v_k_1911_);
lean_dec(v_pivot_1908_);
lean_dec(v_hi_1907_);
return v_res_1912_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg(lean_object* v_n_1913_, lean_object* v_as_1914_, lean_object* v_lo_1915_, lean_object* v_hi_1916_){
_start:
{
lean_object* v___y_1918_; uint8_t v___x_1928_; 
v___x_1928_ = lean_nat_dec_lt(v_lo_1915_, v_hi_1916_);
if (v___x_1928_ == 0)
{
lean_dec(v_lo_1915_);
return v_as_1914_;
}
else
{
lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v_mid_1931_; lean_object* v___y_1933_; lean_object* v___y_1939_; lean_object* v___x_1944_; lean_object* v___x_1945_; uint8_t v___x_1946_; 
v___x_1929_ = lean_nat_add(v_lo_1915_, v_hi_1916_);
v___x_1930_ = lean_unsigned_to_nat(1u);
v_mid_1931_ = lean_nat_shiftr(v___x_1929_, v___x_1930_);
lean_dec(v___x_1929_);
v___x_1944_ = lean_array_fget_borrowed(v_as_1914_, v_mid_1931_);
v___x_1945_ = lean_array_fget_borrowed(v_as_1914_, v_lo_1915_);
v___x_1946_ = l_Nat_blt(v___x_1944_, v___x_1945_);
if (v___x_1946_ == 0)
{
v___y_1939_ = v_as_1914_;
goto v___jp_1938_;
}
else
{
lean_object* v___x_1947_; 
v___x_1947_ = lean_array_fswap(v_as_1914_, v_lo_1915_, v_mid_1931_);
v___y_1939_ = v___x_1947_;
goto v___jp_1938_;
}
v___jp_1932_:
{
lean_object* v___x_1934_; lean_object* v___x_1935_; uint8_t v___x_1936_; 
v___x_1934_ = lean_array_fget_borrowed(v___y_1933_, v_mid_1931_);
v___x_1935_ = lean_array_fget_borrowed(v___y_1933_, v_hi_1916_);
v___x_1936_ = l_Nat_blt(v___x_1934_, v___x_1935_);
if (v___x_1936_ == 0)
{
lean_dec(v_mid_1931_);
v___y_1918_ = v___y_1933_;
goto v___jp_1917_;
}
else
{
lean_object* v___x_1937_; 
v___x_1937_ = lean_array_fswap(v___y_1933_, v_mid_1931_, v_hi_1916_);
lean_dec(v_mid_1931_);
v___y_1918_ = v___x_1937_;
goto v___jp_1917_;
}
}
v___jp_1938_:
{
lean_object* v___x_1940_; lean_object* v___x_1941_; uint8_t v___x_1942_; 
v___x_1940_ = lean_array_fget_borrowed(v___y_1939_, v_hi_1916_);
v___x_1941_ = lean_array_fget_borrowed(v___y_1939_, v_lo_1915_);
v___x_1942_ = l_Nat_blt(v___x_1940_, v___x_1941_);
if (v___x_1942_ == 0)
{
v___y_1933_ = v___y_1939_;
goto v___jp_1932_;
}
else
{
lean_object* v___x_1943_; 
v___x_1943_ = lean_array_fswap(v___y_1939_, v_lo_1915_, v_hi_1916_);
v___y_1933_ = v___x_1943_;
goto v___jp_1932_;
}
}
}
v___jp_1917_:
{
lean_object* v_pivot_1919_; lean_object* v___x_1920_; lean_object* v_fst_1921_; lean_object* v_snd_1922_; uint8_t v___x_1923_; 
v_pivot_1919_ = lean_array_fget(v___y_1918_, v_hi_1916_);
lean_inc_n(v_lo_1915_, 2);
v___x_1920_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11___redArg(v_hi_1916_, v_pivot_1919_, v___y_1918_, v_lo_1915_, v_lo_1915_);
lean_dec(v_pivot_1919_);
v_fst_1921_ = lean_ctor_get(v___x_1920_, 0);
lean_inc(v_fst_1921_);
v_snd_1922_ = lean_ctor_get(v___x_1920_, 1);
lean_inc(v_snd_1922_);
lean_dec_ref(v___x_1920_);
v___x_1923_ = lean_nat_dec_le(v_hi_1916_, v_fst_1921_);
if (v___x_1923_ == 0)
{
lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; 
v___x_1924_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg(v_n_1913_, v_snd_1922_, v_lo_1915_, v_fst_1921_);
v___x_1925_ = lean_unsigned_to_nat(1u);
v___x_1926_ = lean_nat_add(v_fst_1921_, v___x_1925_);
lean_dec(v_fst_1921_);
v_as_1914_ = v___x_1924_;
v_lo_1915_ = v___x_1926_;
goto _start;
}
else
{
lean_dec(v_fst_1921_);
lean_dec(v_lo_1915_);
return v_snd_1922_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg___boxed(lean_object* v_n_1948_, lean_object* v_as_1949_, lean_object* v_lo_1950_, lean_object* v_hi_1951_){
_start:
{
lean_object* v_res_1952_; 
v_res_1952_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg(v_n_1948_, v_as_1949_, v_lo_1950_, v_hi_1951_);
lean_dec(v_hi_1951_);
lean_dec(v_n_1948_);
return v_res_1952_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__6(lean_object* v_xs_1953_, lean_object* v_f_1954_, lean_object* v_x_1955_, lean_object* v_as_1956_, size_t v_i_1957_, size_t v_stop_1958_, lean_object* v_b_1959_){
_start:
{
lean_object* v___y_1961_; uint8_t v___x_1965_; 
v___x_1965_ = lean_usize_dec_eq(v_i_1957_, v_stop_1958_);
if (v___x_1965_ == 0)
{
lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; uint8_t v___x_1970_; 
v___x_1966_ = l_Lean_Elab_Structural_instInhabitedRecArgInfo_default;
v___x_1967_ = lean_array_uget_borrowed(v_as_1956_, v_i_1957_);
v___x_1968_ = lean_array_get_borrowed(v___x_1966_, v_xs_1953_, v___x_1967_);
lean_inc_ref(v_f_1954_);
lean_inc(v___x_1968_);
v___x_1969_ = lean_apply_1(v_f_1954_, v___x_1968_);
v___x_1970_ = lean_nat_dec_eq(v___x_1969_, v_x_1955_);
lean_dec(v___x_1969_);
if (v___x_1970_ == 0)
{
v___y_1961_ = v_b_1959_;
goto v___jp_1960_;
}
else
{
lean_object* v___x_1971_; 
lean_inc(v___x_1967_);
v___x_1971_ = lean_array_push(v_b_1959_, v___x_1967_);
v___y_1961_ = v___x_1971_;
goto v___jp_1960_;
}
}
else
{
lean_dec_ref(v_f_1954_);
return v_b_1959_;
}
v___jp_1960_:
{
size_t v___x_1962_; size_t v___x_1963_; 
v___x_1962_ = ((size_t)1ULL);
v___x_1963_ = lean_usize_add(v_i_1957_, v___x_1962_);
v_i_1957_ = v___x_1963_;
v_b_1959_ = v___y_1961_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__6___boxed(lean_object* v_xs_1972_, lean_object* v_f_1973_, lean_object* v_x_1974_, lean_object* v_as_1975_, lean_object* v_i_1976_, lean_object* v_stop_1977_, lean_object* v_b_1978_){
_start:
{
size_t v_i_boxed_1979_; size_t v_stop_boxed_1980_; lean_object* v_res_1981_; 
v_i_boxed_1979_ = lean_unbox_usize(v_i_1976_);
lean_dec(v_i_1976_);
v_stop_boxed_1980_ = lean_unbox_usize(v_stop_1977_);
lean_dec(v_stop_1977_);
v_res_1981_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__6(v_xs_1972_, v_f_1973_, v_x_1974_, v_as_1975_, v_i_boxed_1979_, v_stop_boxed_1980_, v_b_1978_);
lean_dec_ref(v_as_1975_);
lean_dec(v_x_1974_);
lean_dec_ref(v_xs_1972_);
return v_res_1981_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8(lean_object* v_xs_1984_, lean_object* v_f_1985_, size_t v_sz_1986_, size_t v_i_1987_, lean_object* v_bs_1988_){
_start:
{
uint8_t v___x_1989_; 
v___x_1989_ = lean_usize_dec_lt(v_i_1987_, v_sz_1986_);
if (v___x_1989_ == 0)
{
lean_dec_ref(v_f_1985_);
return v_bs_1988_;
}
else
{
lean_object* v_v_1990_; lean_object* v___x_1991_; lean_object* v_bs_x27_1992_; lean_object* v___y_1994_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; uint8_t v___x_2003_; 
v_v_1990_ = lean_array_uget(v_bs_1988_, v_i_1987_);
v___x_1991_ = lean_unsigned_to_nat(0u);
v_bs_x27_1992_ = lean_array_uset(v_bs_1988_, v_i_1987_, v___x_1991_);
v___x_1999_ = lean_array_get_size(v_xs_1984_);
v___x_2000_ = l_Array_range(v___x_1999_);
v___x_2001_ = lean_array_get_size(v___x_2000_);
v___x_2002_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8___closed__0));
v___x_2003_ = lean_nat_dec_lt(v___x_1991_, v___x_2001_);
if (v___x_2003_ == 0)
{
lean_dec_ref(v___x_2000_);
lean_dec(v_v_1990_);
v___y_1994_ = v___x_2002_;
goto v___jp_1993_;
}
else
{
size_t v___x_2004_; size_t v___x_2005_; lean_object* v___x_2006_; 
v___x_2004_ = ((size_t)0ULL);
v___x_2005_ = lean_usize_of_nat(v___x_2001_);
lean_inc_ref(v_f_1985_);
v___x_2006_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__6(v_xs_1984_, v_f_1985_, v_v_1990_, v___x_2000_, v___x_2004_, v___x_2005_, v___x_2002_);
lean_dec_ref(v___x_2000_);
lean_dec(v_v_1990_);
v___y_1994_ = v___x_2006_;
goto v___jp_1993_;
}
v___jp_1993_:
{
size_t v___x_1995_; size_t v___x_1996_; lean_object* v___x_1997_; 
v___x_1995_ = ((size_t)1ULL);
v___x_1996_ = lean_usize_add(v_i_1987_, v___x_1995_);
v___x_1997_ = lean_array_uset(v_bs_x27_1992_, v_i_1987_, v___y_1994_);
v_i_1987_ = v___x_1996_;
v_bs_1988_ = v___x_1997_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8___boxed(lean_object* v_xs_2007_, lean_object* v_f_2008_, lean_object* v_sz_2009_, lean_object* v_i_2010_, lean_object* v_bs_2011_){
_start:
{
size_t v_sz_boxed_2012_; size_t v_i_boxed_2013_; lean_object* v_res_2014_; 
v_sz_boxed_2012_ = lean_unbox_usize(v_sz_2009_);
lean_dec(v_sz_2009_);
v_i_boxed_2013_ = lean_unbox_usize(v_i_2010_);
lean_dec(v_i_2010_);
v_res_2014_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8(v_xs_2007_, v_f_2008_, v_sz_boxed_2012_, v_i_boxed_2013_, v_bs_2011_);
lean_dec_ref(v_xs_2007_);
return v_res_2014_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__11(lean_object* v_as_2015_, size_t v_i_2016_, size_t v_stop_2017_, lean_object* v_b_2018_){
_start:
{
uint8_t v___x_2019_; 
v___x_2019_ = lean_usize_dec_eq(v_i_2016_, v_stop_2017_);
if (v___x_2019_ == 0)
{
lean_object* v___x_2020_; lean_object* v___x_2021_; size_t v___x_2022_; size_t v___x_2023_; 
v___x_2020_ = lean_array_uget_borrowed(v_as_2015_, v_i_2016_);
v___x_2021_ = l_Array_append___redArg(v_b_2018_, v___x_2020_);
v___x_2022_ = ((size_t)1ULL);
v___x_2023_ = lean_usize_add(v_i_2016_, v___x_2022_);
v_i_2016_ = v___x_2023_;
v_b_2018_ = v___x_2021_;
goto _start;
}
else
{
return v_b_2018_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__11___boxed(lean_object* v_as_2025_, lean_object* v_i_2026_, lean_object* v_stop_2027_, lean_object* v_b_2028_){
_start:
{
size_t v_i_boxed_2029_; size_t v_stop_boxed_2030_; lean_object* v_res_2031_; 
v_i_boxed_2029_ = lean_unbox_usize(v_i_2026_);
lean_dec(v_i_2026_);
v_stop_boxed_2030_ = lean_unbox_usize(v_stop_2027_);
lean_dec(v_stop_2027_);
v_res_2031_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__11(v_as_2025_, v_i_boxed_2029_, v_stop_boxed_2030_, v_b_2028_);
lean_dec_ref(v_as_2025_);
return v_res_2031_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__7(lean_object* v_msg_2032_){
_start:
{
lean_object* v___x_2033_; lean_object* v___x_2034_; 
v___x_2033_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0);
v___x_2034_ = lean_panic_fn_borrowed(v___x_2033_, v_msg_2032_);
return v___x_2034_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9___redArg(lean_object* v_xs_2035_, lean_object* v_ys_2036_, lean_object* v_x_2037_){
_start:
{
lean_object* v_zero_2038_; uint8_t v_isZero_2039_; 
v_zero_2038_ = lean_unsigned_to_nat(0u);
v_isZero_2039_ = lean_nat_dec_eq(v_x_2037_, v_zero_2038_);
if (v_isZero_2039_ == 1)
{
lean_dec(v_x_2037_);
return v_isZero_2039_;
}
else
{
lean_object* v_one_2040_; lean_object* v_n_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; uint8_t v___x_2044_; 
v_one_2040_ = lean_unsigned_to_nat(1u);
v_n_2041_ = lean_nat_sub(v_x_2037_, v_one_2040_);
lean_dec(v_x_2037_);
v___x_2042_ = lean_array_fget_borrowed(v_xs_2035_, v_n_2041_);
v___x_2043_ = lean_array_fget_borrowed(v_ys_2036_, v_n_2041_);
v___x_2044_ = lean_nat_dec_eq(v___x_2042_, v___x_2043_);
if (v___x_2044_ == 0)
{
lean_dec(v_n_2041_);
return v___x_2044_;
}
else
{
v_x_2037_ = v_n_2041_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9___redArg___boxed(lean_object* v_xs_2046_, lean_object* v_ys_2047_, lean_object* v_x_2048_){
_start:
{
uint8_t v_res_2049_; lean_object* v_r_2050_; 
v_res_2049_ = l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9___redArg(v_xs_2046_, v_ys_2047_, v_x_2048_);
lean_dec_ref(v_ys_2047_);
lean_dec_ref(v_xs_2046_);
v_r_2050_ = lean_box(v_res_2049_);
return v_r_2050_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__2(void){
_start:
{
lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; 
v___x_2053_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__1));
v___x_2054_ = lean_unsigned_to_nat(2u);
v___x_2055_ = lean_unsigned_to_nat(63u);
v___x_2056_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__0));
v___x_2057_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__0));
v___x_2058_ = l_mkPanicMessageWithDecl(v___x_2057_, v___x_2056_, v___x_2055_, v___x_2054_, v___x_2053_);
return v___x_2058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5(lean_object* v_f_2061_, lean_object* v_xs_2062_, lean_object* v_ys_2063_){
_start:
{
size_t v_sz_2067_; size_t v___x_2068_; lean_object* v_positions_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___y_2073_; lean_object* v___y_2079_; lean_object* v___y_2080_; lean_object* v___y_2081_; lean_object* v___y_2082_; lean_object* v___y_2085_; lean_object* v___y_2086_; lean_object* v___y_2087_; lean_object* v___y_2088_; lean_object* v___y_2091_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; uint8_t v___x_2101_; 
v_sz_2067_ = lean_array_size(v_ys_2063_);
v___x_2068_ = ((size_t)0ULL);
v_positions_2069_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8(v_xs_2062_, v_f_2061_, v_sz_2067_, v___x_2068_, v_ys_2063_);
v___x_2070_ = lean_array_get_size(v_xs_2062_);
v___x_2071_ = l_Array_range(v___x_2070_);
v___x_2098_ = lean_unsigned_to_nat(0u);
v___x_2099_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__3));
v___x_2100_ = lean_array_get_size(v_positions_2069_);
v___x_2101_ = lean_nat_dec_lt(v___x_2098_, v___x_2100_);
if (v___x_2101_ == 0)
{
v___y_2091_ = v___x_2099_;
goto v___jp_2090_;
}
else
{
size_t v___x_2102_; lean_object* v___x_2103_; 
v___x_2102_ = lean_usize_of_nat(v___x_2100_);
v___x_2103_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__11(v_positions_2069_, v___x_2068_, v___x_2102_, v___x_2099_);
v___y_2091_ = v___x_2103_;
goto v___jp_2090_;
}
v___jp_2064_:
{
lean_object* v___x_2065_; lean_object* v___x_2066_; 
v___x_2065_ = lean_obj_once(&l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__2, &l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__2_once, _init_l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__2);
v___x_2066_ = l_panic___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__7(v___x_2065_);
return v___x_2066_;
}
v___jp_2072_:
{
lean_object* v___x_2074_; lean_object* v___x_2075_; uint8_t v___x_2076_; 
v___x_2074_ = lean_array_get_size(v___x_2071_);
v___x_2075_ = lean_array_get_size(v___y_2073_);
v___x_2076_ = lean_nat_dec_eq(v___x_2074_, v___x_2075_);
if (v___x_2076_ == 0)
{
lean_dec_ref(v___y_2073_);
lean_dec_ref(v___x_2071_);
lean_dec_ref(v_positions_2069_);
goto v___jp_2064_;
}
else
{
uint8_t v___x_2077_; 
v___x_2077_ = l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9___redArg(v___x_2071_, v___y_2073_, v___x_2074_);
lean_dec_ref(v___y_2073_);
lean_dec_ref(v___x_2071_);
if (v___x_2077_ == 0)
{
lean_dec_ref(v_positions_2069_);
goto v___jp_2064_;
}
else
{
return v_positions_2069_;
}
}
}
v___jp_2078_:
{
lean_object* v___x_2083_; 
v___x_2083_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg(v___y_2080_, v___y_2081_, v___y_2079_, v___y_2082_);
lean_dec(v___y_2082_);
lean_dec(v___y_2080_);
v___y_2073_ = v___x_2083_;
goto v___jp_2072_;
}
v___jp_2084_:
{
uint8_t v___x_2089_; 
v___x_2089_ = lean_nat_dec_le(v___y_2088_, v___y_2085_);
if (v___x_2089_ == 0)
{
lean_dec(v___y_2085_);
lean_inc(v___y_2088_);
v___y_2079_ = v___y_2088_;
v___y_2080_ = v___y_2086_;
v___y_2081_ = v___y_2087_;
v___y_2082_ = v___y_2088_;
goto v___jp_2078_;
}
else
{
v___y_2079_ = v___y_2088_;
v___y_2080_ = v___y_2086_;
v___y_2081_ = v___y_2087_;
v___y_2082_ = v___y_2085_;
goto v___jp_2078_;
}
}
v___jp_2090_:
{
lean_object* v___x_2092_; lean_object* v___x_2093_; uint8_t v___x_2094_; 
v___x_2092_ = lean_array_get_size(v___y_2091_);
v___x_2093_ = lean_unsigned_to_nat(0u);
v___x_2094_ = lean_nat_dec_eq(v___x_2092_, v___x_2093_);
if (v___x_2094_ == 0)
{
lean_object* v___x_2095_; lean_object* v___x_2096_; uint8_t v___x_2097_; 
v___x_2095_ = lean_unsigned_to_nat(1u);
v___x_2096_ = lean_nat_sub(v___x_2092_, v___x_2095_);
v___x_2097_ = lean_nat_dec_le(v___x_2093_, v___x_2096_);
if (v___x_2097_ == 0)
{
lean_inc(v___x_2096_);
v___y_2085_ = v___x_2096_;
v___y_2086_ = v___x_2092_;
v___y_2087_ = v___y_2091_;
v___y_2088_ = v___x_2096_;
goto v___jp_2084_;
}
else
{
v___y_2085_ = v___x_2096_;
v___y_2086_ = v___x_2092_;
v___y_2087_ = v___y_2091_;
v___y_2088_ = v___x_2093_;
goto v___jp_2084_;
}
}
else
{
v___y_2073_ = v___y_2091_;
goto v___jp_2072_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___boxed(lean_object* v_f_2104_, lean_object* v_xs_2105_, lean_object* v_ys_2106_){
_start:
{
lean_object* v_res_2107_; 
v_res_2107_ = l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5(v_f_2104_, v_xs_2105_, v_ys_2106_);
lean_dec_ref(v_xs_2105_);
return v_res_2107_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__9(void){
_start:
{
lean_object* v___x_2122_; lean_object* v___x_2123_; 
v___x_2122_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__8));
v___x_2123_ = l_Lean_stringToMessageData(v___x_2122_);
return v___x_2123_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__11(void){
_start:
{
lean_object* v___x_2125_; lean_object* v___x_2126_; 
v___x_2125_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__10));
v___x_2126_ = l_Lean_stringToMessageData(v___x_2125_);
return v___x_2126_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion(lean_object* v_preDefs_2127_, lean_object* v_fixedParamPerms_2128_, lean_object* v_xs_2129_, lean_object* v_recArgInfos_2130_, lean_object* v_a_2131_, lean_object* v_a_2132_, lean_object* v_a_2133_, lean_object* v_a_2134_){
_start:
{
lean_object* v___f_2136_; lean_object* v___f_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; size_t v_sz_2141_; size_t v___x_2142_; lean_object* v___x_2143_; 
v___f_2136_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__0));
v___f_2137_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__1));
v___x_2138_ = lean_box(0);
v___x_2139_ = l_Lean_Elab_Structural_instInhabitedRecArgInfo_default;
v___x_2140_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v_sz_2141_ = lean_array_size(v_preDefs_2127_);
v___x_2142_ = ((size_t)0ULL);
lean_inc_ref(v_preDefs_2127_);
lean_inc_ref(v_xs_2129_);
v___x_2143_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___redArg(v_fixedParamPerms_2128_, v_xs_2129_, v_sz_2141_, v___x_2142_, v_preDefs_2127_, v_a_2131_, v_a_2132_, v_a_2133_, v_a_2134_);
if (lean_obj_tag(v___x_2143_) == 0)
{
lean_object* v_a_2144_; lean_object* v___x_2145_; 
v_a_2144_ = lean_ctor_get(v___x_2143_, 0);
lean_inc(v_a_2144_);
lean_dec_ref_known(v___x_2143_, 1);
lean_inc_ref(v_preDefs_2127_);
lean_inc_ref(v_xs_2129_);
v___x_2145_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___redArg(v_fixedParamPerms_2128_, v_xs_2129_, v_sz_2141_, v___x_2142_, v_preDefs_2127_, v_a_2131_, v_a_2132_, v_a_2133_, v_a_2134_);
if (lean_obj_tag(v___x_2145_) == 0)
{
lean_object* v_a_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v_indGroupInst_2149_; lean_object* v_toIndGroupInfo_2150_; lean_object* v_all_2151_; lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2235_; 
v_a_2146_ = lean_ctor_get(v___x_2145_, 0);
lean_inc(v_a_2146_);
lean_dec_ref_known(v___x_2145_, 1);
v___x_2147_ = lean_unsigned_to_nat(0u);
v___x_2148_ = lean_array_get_borrowed(v___x_2139_, v_recArgInfos_2130_, v___x_2147_);
v_indGroupInst_2149_ = lean_ctor_get(v___x_2148_, 4);
v_toIndGroupInfo_2150_ = lean_ctor_get(v_indGroupInst_2149_, 0);
lean_inc_ref(v_toIndGroupInfo_2150_);
v_all_2151_ = lean_ctor_get(v_toIndGroupInfo_2150_, 0);
v_isSharedCheck_2235_ = !lean_is_exclusive(v_toIndGroupInfo_2150_);
if (v_isSharedCheck_2235_ == 0)
{
lean_object* v_unused_2236_; 
v_unused_2236_ = lean_ctor_get(v_toIndGroupInfo_2150_, 1);
lean_dec(v_unused_2236_);
v___x_2153_ = v_toIndGroupInfo_2150_;
v_isShared_2154_ = v_isSharedCheck_2235_;
goto v_resetjp_2152_;
}
else
{
lean_inc(v_all_2151_);
lean_dec(v_toIndGroupInfo_2150_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2235_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
lean_object* v___x_2155_; lean_object* v___x_2156_; 
v___x_2155_ = lean_array_get(v___x_2138_, v_all_2151_, v___x_2147_);
lean_dec_ref(v_all_2151_);
v___x_2156_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4(v___x_2155_, v_a_2131_, v_a_2132_, v_a_2133_, v_a_2134_);
if (lean_obj_tag(v___x_2156_) == 0)
{
lean_object* v_a_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___f_2162_; lean_object* v___y_2164_; lean_object* v___y_2165_; lean_object* v___y_2166_; lean_object* v___y_2167_; lean_object* v___x_2201_; lean_object* v_a_2202_; uint8_t v___x_2203_; 
v_a_2157_ = lean_ctor_get(v___x_2156_, 0);
lean_inc(v_a_2157_);
lean_dec_ref_known(v___x_2156_, 1);
v___x_2158_ = l_Lean_InductiveVal_numTypeFormers(v_a_2157_);
v___x_2159_ = l_Array_range(v___x_2158_);
v___x_2160_ = l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5(v___f_2137_, v_recArgInfos_2130_, v___x_2159_);
v___x_2161_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__5));
v___f_2162_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__6));
v___x_2201_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1(v___x_2161_, v_a_2131_, v_a_2132_, v_a_2133_, v_a_2134_);
v_a_2202_ = lean_ctor_get(v___x_2201_, 0);
lean_inc(v_a_2202_);
lean_dec_ref(v___x_2201_);
v___x_2203_ = lean_unbox(v_a_2202_);
lean_dec(v_a_2202_);
if (v___x_2203_ == 0)
{
lean_del_object(v___x_2153_);
v___y_2164_ = v_a_2131_;
v___y_2165_ = v_a_2132_;
v___y_2166_ = v_a_2133_;
v___y_2167_ = v_a_2134_;
goto v___jp_2163_;
}
else
{
lean_object* v_toConstantVal_2204_; lean_object* v_name_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2209_; 
v_toConstantVal_2204_ = lean_ctor_get(v_a_2157_, 0);
v_name_2205_ = lean_ctor_get(v_toConstantVal_2204_, 0);
v___x_2206_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__9, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__9_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__9);
lean_inc(v_name_2205_);
v___x_2207_ = l_Lean_MessageData_ofName(v_name_2205_);
if (v_isShared_2154_ == 0)
{
lean_ctor_set_tag(v___x_2153_, 7);
lean_ctor_set(v___x_2153_, 1, v___x_2207_);
lean_ctor_set(v___x_2153_, 0, v___x_2206_);
v___x_2209_ = v___x_2153_;
goto v_reusejp_2208_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v___x_2206_);
lean_ctor_set(v_reuseFailAlloc_2226_, 1, v___x_2207_);
v___x_2209_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2208_;
}
v_reusejp_2208_:
{
lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; 
v___x_2210_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__11, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__11_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__11);
v___x_2211_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2211_, 0, v___x_2209_);
lean_ctor_set(v___x_2211_, 1, v___x_2210_);
lean_inc_ref(v___x_2160_);
v___x_2212_ = lean_array_to_list(v___x_2160_);
v___x_2213_ = lean_box(0);
v___x_2214_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__22(v___x_2212_, v___x_2213_);
v___x_2215_ = l_Lean_MessageData_ofList(v___x_2214_);
v___x_2216_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2216_, 0, v___x_2211_);
lean_ctor_set(v___x_2216_, 1, v___x_2215_);
v___x_2217_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_2161_, v___x_2216_, v_a_2131_, v_a_2132_, v_a_2133_, v_a_2134_);
if (lean_obj_tag(v___x_2217_) == 0)
{
lean_dec_ref_known(v___x_2217_, 1);
v___y_2164_ = v_a_2131_;
v___y_2165_ = v_a_2132_;
v___y_2166_ = v_a_2133_;
v___y_2167_ = v_a_2134_;
goto v___jp_2163_;
}
else
{
lean_object* v_a_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2225_; 
lean_dec_ref(v___x_2160_);
lean_dec(v_a_2157_);
lean_dec(v_a_2146_);
lean_dec(v_a_2144_);
lean_dec_ref(v_recArgInfos_2130_);
lean_dec_ref(v_xs_2129_);
lean_dec_ref(v_fixedParamPerms_2128_);
lean_dec_ref(v_preDefs_2127_);
v_a_2218_ = lean_ctor_get(v___x_2217_, 0);
v_isSharedCheck_2225_ = !lean_is_exclusive(v___x_2217_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_2220_ = v___x_2217_;
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_a_2218_);
lean_dec(v___x_2217_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
lean_object* v___x_2223_; 
if (v_isShared_2221_ == 0)
{
v___x_2223_ = v___x_2220_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v_a_2218_);
v___x_2223_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
return v___x_2223_;
}
}
}
}
}
v___jp_2163_:
{
lean_object* v_toConstantVal_2168_; lean_object* v_numIndices_2169_; lean_object* v_name_2170_; lean_object* v___x_2171_; 
v_toConstantVal_2168_ = lean_ctor_get(v_a_2157_, 0);
lean_inc_ref(v_toConstantVal_2168_);
v_numIndices_2169_ = lean_ctor_get(v_a_2157_, 2);
lean_inc(v_numIndices_2169_);
lean_dec(v_a_2157_);
v_name_2170_ = lean_ctor_get(v_toConstantVal_2168_, 0);
lean_inc(v_name_2170_);
lean_dec_ref(v_toConstantVal_2168_);
v___x_2171_ = l_Lean_Meta_isInductivePredicate(v_name_2170_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_);
if (lean_obj_tag(v___x_2171_) == 0)
{
lean_object* v_a_2172_; lean_object* v___x_2173_; lean_object* v___f_2174_; uint8_t v___x_2175_; 
v_a_2172_ = lean_ctor_get(v___x_2171_, 0);
lean_inc_n(v_a_2172_, 2);
lean_dec_ref_known(v___x_2171_, 1);
v___x_2173_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___boxed__const__1));
lean_inc(v_numIndices_2169_);
lean_inc_ref(v_preDefs_2127_);
lean_inc_ref(v_xs_2129_);
lean_inc_ref(v_fixedParamPerms_2128_);
lean_inc_ref(v___x_2160_);
lean_inc(v_a_2144_);
lean_inc_ref(v_recArgInfos_2130_);
v___f_2174_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___boxed), 21, 14);
lean_closure_set(v___f_2174_, 0, v_recArgInfos_2130_);
lean_closure_set(v___f_2174_, 1, v_a_2144_);
lean_closure_set(v___f_2174_, 2, v___x_2160_);
lean_closure_set(v___f_2174_, 3, v___x_2173_);
lean_closure_set(v___f_2174_, 4, v_fixedParamPerms_2128_);
lean_closure_set(v___f_2174_, 5, v_xs_2129_);
lean_closure_set(v___f_2174_, 6, v___x_2147_);
lean_closure_set(v___f_2174_, 7, v_preDefs_2127_);
lean_closure_set(v___f_2174_, 8, v_numIndices_2169_);
lean_closure_set(v___f_2174_, 9, v___f_2136_);
lean_closure_set(v___f_2174_, 10, v___x_2161_);
lean_closure_set(v___f_2174_, 11, v_a_2172_);
lean_closure_set(v___f_2174_, 12, v___x_2140_);
lean_closure_set(v___f_2174_, 13, v___f_2162_);
v___x_2175_ = lean_unbox(v_a_2172_);
if (v___x_2175_ == 0)
{
size_t v_sz_2176_; lean_object* v___x_2177_; 
lean_dec_ref(v___f_2174_);
v_sz_2176_ = lean_array_size(v_recArgInfos_2130_);
lean_inc_ref(v_recArgInfos_2130_);
v___x_2177_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__21___redArg(v_a_2144_, v_a_2146_, v_sz_2176_, v___x_2142_, v_recArgInfos_2130_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_);
lean_dec(v_a_2146_);
if (lean_obj_tag(v___x_2177_) == 0)
{
lean_object* v_a_2178_; lean_object* v___x_2179_; uint8_t v___x_2180_; lean_object* v___x_2181_; 
v_a_2178_ = lean_ctor_get(v___x_2177_, 0);
lean_inc(v_a_2178_);
lean_dec_ref_known(v___x_2177_, 1);
v___x_2179_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__7));
v___x_2180_ = lean_unbox(v_a_2172_);
lean_dec(v_a_2172_);
v___x_2181_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2(v_recArgInfos_2130_, v_a_2144_, v___x_2160_, v___x_2142_, v_fixedParamPerms_2128_, v_xs_2129_, v___x_2147_, v_preDefs_2127_, v_numIndices_2169_, v___f_2136_, v___x_2161_, v___x_2180_, v___x_2140_, v___f_2162_, v___x_2179_, v_a_2178_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_);
lean_dec(v_numIndices_2169_);
lean_dec(v_a_2144_);
return v___x_2181_;
}
else
{
lean_object* v_a_2182_; lean_object* v___x_2184_; uint8_t v_isShared_2185_; uint8_t v_isSharedCheck_2189_; 
lean_dec(v_a_2172_);
lean_dec(v_numIndices_2169_);
lean_dec_ref(v___x_2160_);
lean_dec(v_a_2144_);
lean_dec_ref(v_recArgInfos_2130_);
lean_dec_ref(v_xs_2129_);
lean_dec_ref(v_fixedParamPerms_2128_);
lean_dec_ref(v_preDefs_2127_);
v_a_2182_ = lean_ctor_get(v___x_2177_, 0);
v_isSharedCheck_2189_ = !lean_is_exclusive(v___x_2177_);
if (v_isSharedCheck_2189_ == 0)
{
v___x_2184_ = v___x_2177_;
v_isShared_2185_ = v_isSharedCheck_2189_;
goto v_resetjp_2183_;
}
else
{
lean_inc(v_a_2182_);
lean_dec(v___x_2177_);
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
lean_object* v___x_2190_; lean_object* v___f_2191_; lean_object* v___x_2192_; 
lean_dec(v_a_2172_);
lean_dec(v_numIndices_2169_);
lean_dec_ref(v___x_2160_);
lean_dec(v_a_2146_);
lean_dec_ref(v_xs_2129_);
lean_dec_ref(v_fixedParamPerms_2128_);
lean_dec_ref(v_preDefs_2127_);
v___x_2190_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___boxed__const__1));
lean_inc(v_a_2144_);
v___f_2191_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__3___boxed), 10, 4);
lean_closure_set(v___f_2191_, 0, v_recArgInfos_2130_);
lean_closure_set(v___f_2191_, 1, v_a_2144_);
lean_closure_set(v___f_2191_, 2, v___x_2190_);
lean_closure_set(v___f_2191_, 3, v___f_2174_);
v___x_2192_ = l_Lean_Elab_Structural_withFunTypes___redArg(v_a_2144_, v___f_2191_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_);
return v___x_2192_;
}
}
else
{
lean_object* v_a_2193_; lean_object* v___x_2195_; uint8_t v_isShared_2196_; uint8_t v_isSharedCheck_2200_; 
lean_dec(v_numIndices_2169_);
lean_dec_ref(v___x_2160_);
lean_dec(v_a_2146_);
lean_dec(v_a_2144_);
lean_dec_ref(v_recArgInfos_2130_);
lean_dec_ref(v_xs_2129_);
lean_dec_ref(v_fixedParamPerms_2128_);
lean_dec_ref(v_preDefs_2127_);
v_a_2193_ = lean_ctor_get(v___x_2171_, 0);
v_isSharedCheck_2200_ = !lean_is_exclusive(v___x_2171_);
if (v_isSharedCheck_2200_ == 0)
{
v___x_2195_ = v___x_2171_;
v_isShared_2196_ = v_isSharedCheck_2200_;
goto v_resetjp_2194_;
}
else
{
lean_inc(v_a_2193_);
lean_dec(v___x_2171_);
v___x_2195_ = lean_box(0);
v_isShared_2196_ = v_isSharedCheck_2200_;
goto v_resetjp_2194_;
}
v_resetjp_2194_:
{
lean_object* v___x_2198_; 
if (v_isShared_2196_ == 0)
{
v___x_2198_ = v___x_2195_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v_a_2193_);
v___x_2198_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
return v___x_2198_;
}
}
}
}
}
else
{
lean_object* v_a_2227_; lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2234_; 
lean_del_object(v___x_2153_);
lean_dec(v_a_2146_);
lean_dec(v_a_2144_);
lean_dec_ref(v_recArgInfos_2130_);
lean_dec_ref(v_xs_2129_);
lean_dec_ref(v_fixedParamPerms_2128_);
lean_dec_ref(v_preDefs_2127_);
v_a_2227_ = lean_ctor_get(v___x_2156_, 0);
v_isSharedCheck_2234_ = !lean_is_exclusive(v___x_2156_);
if (v_isSharedCheck_2234_ == 0)
{
v___x_2229_ = v___x_2156_;
v_isShared_2230_ = v_isSharedCheck_2234_;
goto v_resetjp_2228_;
}
else
{
lean_inc(v_a_2227_);
lean_dec(v___x_2156_);
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
}
else
{
lean_object* v_a_2237_; lean_object* v___x_2239_; uint8_t v_isShared_2240_; uint8_t v_isSharedCheck_2244_; 
lean_dec(v_a_2144_);
lean_dec_ref(v_recArgInfos_2130_);
lean_dec_ref(v_xs_2129_);
lean_dec_ref(v_fixedParamPerms_2128_);
lean_dec_ref(v_preDefs_2127_);
v_a_2237_ = lean_ctor_get(v___x_2145_, 0);
v_isSharedCheck_2244_ = !lean_is_exclusive(v___x_2145_);
if (v_isSharedCheck_2244_ == 0)
{
v___x_2239_ = v___x_2145_;
v_isShared_2240_ = v_isSharedCheck_2244_;
goto v_resetjp_2238_;
}
else
{
lean_inc(v_a_2237_);
lean_dec(v___x_2145_);
v___x_2239_ = lean_box(0);
v_isShared_2240_ = v_isSharedCheck_2244_;
goto v_resetjp_2238_;
}
v_resetjp_2238_:
{
lean_object* v___x_2242_; 
if (v_isShared_2240_ == 0)
{
v___x_2242_ = v___x_2239_;
goto v_reusejp_2241_;
}
else
{
lean_object* v_reuseFailAlloc_2243_; 
v_reuseFailAlloc_2243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2243_, 0, v_a_2237_);
v___x_2242_ = v_reuseFailAlloc_2243_;
goto v_reusejp_2241_;
}
v_reusejp_2241_:
{
return v___x_2242_;
}
}
}
}
else
{
lean_object* v_a_2245_; lean_object* v___x_2247_; uint8_t v_isShared_2248_; uint8_t v_isSharedCheck_2252_; 
lean_dec_ref(v_recArgInfos_2130_);
lean_dec_ref(v_xs_2129_);
lean_dec_ref(v_fixedParamPerms_2128_);
lean_dec_ref(v_preDefs_2127_);
v_a_2245_ = lean_ctor_get(v___x_2143_, 0);
v_isSharedCheck_2252_ = !lean_is_exclusive(v___x_2143_);
if (v_isSharedCheck_2252_ == 0)
{
v___x_2247_ = v___x_2143_;
v_isShared_2248_ = v_isSharedCheck_2252_;
goto v_resetjp_2246_;
}
else
{
lean_inc(v_a_2245_);
lean_dec(v___x_2143_);
v___x_2247_ = lean_box(0);
v_isShared_2248_ = v_isSharedCheck_2252_;
goto v_resetjp_2246_;
}
v_resetjp_2246_:
{
lean_object* v___x_2250_; 
if (v_isShared_2248_ == 0)
{
v___x_2250_ = v___x_2247_;
goto v_reusejp_2249_;
}
else
{
lean_object* v_reuseFailAlloc_2251_; 
v_reuseFailAlloc_2251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2251_, 0, v_a_2245_);
v___x_2250_ = v_reuseFailAlloc_2251_;
goto v_reusejp_2249_;
}
v_reusejp_2249_:
{
return v___x_2250_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___boxed(lean_object* v_preDefs_2253_, lean_object* v_fixedParamPerms_2254_, lean_object* v_xs_2255_, lean_object* v_recArgInfos_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_, lean_object* v_a_2259_, lean_object* v_a_2260_, lean_object* v_a_2261_){
_start:
{
lean_object* v_res_2262_; 
v_res_2262_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion(v_preDefs_2253_, v_fixedParamPerms_2254_, v_xs_2255_, v_recArgInfos_2256_, v_a_2257_, v_a_2258_, v_a_2259_, v_a_2260_);
lean_dec(v_a_2260_);
lean_dec_ref(v_a_2259_);
lean_dec(v_a_2258_);
lean_dec_ref(v_a_2257_);
return v_res_2262_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2(lean_object* v_fixedParamPerms_2263_, lean_object* v_xs_2264_, lean_object* v_as_2265_, size_t v_sz_2266_, size_t v_i_2267_, lean_object* v_bs_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_){
_start:
{
lean_object* v___x_2274_; 
v___x_2274_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___redArg(v_fixedParamPerms_2263_, v_xs_2264_, v_sz_2266_, v_i_2267_, v_bs_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_);
return v___x_2274_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___boxed(lean_object* v_fixedParamPerms_2275_, lean_object* v_xs_2276_, lean_object* v_as_2277_, lean_object* v_sz_2278_, lean_object* v_i_2279_, lean_object* v_bs_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_){
_start:
{
size_t v_sz_boxed_2286_; size_t v_i_boxed_2287_; lean_object* v_res_2288_; 
v_sz_boxed_2286_ = lean_unbox_usize(v_sz_2278_);
lean_dec(v_sz_2278_);
v_i_boxed_2287_ = lean_unbox_usize(v_i_2279_);
lean_dec(v_i_2279_);
v_res_2288_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2(v_fixedParamPerms_2275_, v_xs_2276_, v_as_2277_, v_sz_boxed_2286_, v_i_boxed_2287_, v_bs_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_);
lean_dec(v___y_2284_);
lean_dec_ref(v___y_2283_);
lean_dec(v___y_2282_);
lean_dec_ref(v___y_2281_);
lean_dec_ref(v_as_2277_);
lean_dec_ref(v_fixedParamPerms_2275_);
return v_res_2288_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3(lean_object* v_fixedParamPerms_2289_, lean_object* v_xs_2290_, lean_object* v_as_2291_, size_t v_sz_2292_, size_t v_i_2293_, lean_object* v_bs_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_){
_start:
{
lean_object* v___x_2300_; 
v___x_2300_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___redArg(v_fixedParamPerms_2289_, v_xs_2290_, v_sz_2292_, v_i_2293_, v_bs_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_);
return v___x_2300_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___boxed(lean_object* v_fixedParamPerms_2301_, lean_object* v_xs_2302_, lean_object* v_as_2303_, lean_object* v_sz_2304_, lean_object* v_i_2305_, lean_object* v_bs_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_){
_start:
{
size_t v_sz_boxed_2312_; size_t v_i_boxed_2313_; lean_object* v_res_2314_; 
v_sz_boxed_2312_ = lean_unbox_usize(v_sz_2304_);
lean_dec(v_sz_2304_);
v_i_boxed_2313_ = lean_unbox_usize(v_i_2305_);
lean_dec(v_i_2305_);
v_res_2314_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3(v_fixedParamPerms_2301_, v_xs_2302_, v_as_2303_, v_sz_boxed_2312_, v_i_boxed_2313_, v_bs_2306_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_);
lean_dec(v___y_2310_);
lean_dec_ref(v___y_2309_);
lean_dec(v___y_2308_);
lean_dec_ref(v___y_2307_);
lean_dec_ref(v_as_2303_);
lean_dec_ref(v_fixedParamPerms_2301_);
return v_res_2314_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14(lean_object* v_00_u03b3_2315_, lean_object* v_msg_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_){
_start:
{
lean_object* v___x_2322_; 
v___x_2322_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg(v_msg_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_);
return v___x_2322_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___boxed(lean_object* v_00_u03b3_2323_, lean_object* v_msg_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_){
_start:
{
lean_object* v_res_2330_; 
v_res_2330_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14(v_00_u03b3_2323_, v_msg_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_);
lean_dec(v___y_2328_);
lean_dec_ref(v___y_2327_);
lean_dec(v___y_2326_);
lean_dec_ref(v___y_2325_);
return v_res_2330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6(lean_object* v_00_u03b3_2331_, lean_object* v_00_u03b1_2332_, lean_object* v_f_2333_, lean_object* v_positions_2334_, lean_object* v_ys_2335_, lean_object* v_xs_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_){
_start:
{
lean_object* v___x_2342_; 
v___x_2342_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg(v_f_2333_, v_positions_2334_, v_ys_2335_, v_xs_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_);
return v___x_2342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___boxed(lean_object* v_00_u03b3_2343_, lean_object* v_00_u03b1_2344_, lean_object* v_f_2345_, lean_object* v_positions_2346_, lean_object* v_ys_2347_, lean_object* v_xs_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_){
_start:
{
lean_object* v_res_2354_; 
v_res_2354_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6(v_00_u03b3_2343_, v_00_u03b1_2344_, v_f_2345_, v_positions_2346_, v_ys_2347_, v_xs_2348_, v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_);
lean_dec(v___y_2352_);
lean_dec_ref(v___y_2351_);
lean_dec(v___y_2350_);
lean_dec_ref(v___y_2349_);
lean_dec_ref(v_xs_2348_);
lean_dec_ref(v_ys_2347_);
lean_dec_ref(v_positions_2346_);
return v_res_2354_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7(lean_object* v___x_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_, lean_object* v_funTypes_2358_, lean_object* v_as_2359_, size_t v_sz_2360_, size_t v_i_2361_, lean_object* v_bs_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_){
_start:
{
lean_object* v___x_2368_; 
v___x_2368_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg(v___x_2355_, v_a_2356_, v_a_2357_, v_funTypes_2358_, v_sz_2360_, v_i_2361_, v_bs_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_);
return v___x_2368_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___boxed(lean_object* v___x_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_, lean_object* v_funTypes_2372_, lean_object* v_as_2373_, lean_object* v_sz_2374_, lean_object* v_i_2375_, lean_object* v_bs_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_){
_start:
{
size_t v_sz_boxed_2382_; size_t v_i_boxed_2383_; lean_object* v_res_2384_; 
v_sz_boxed_2382_ = lean_unbox_usize(v_sz_2374_);
lean_dec(v_sz_2374_);
v_i_boxed_2383_ = lean_unbox_usize(v_i_2375_);
lean_dec(v_i_2375_);
v_res_2384_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7(v___x_2369_, v_a_2370_, v_a_2371_, v_funTypes_2372_, v_as_2373_, v_sz_boxed_2382_, v_i_boxed_2383_, v_bs_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_);
lean_dec(v___y_2380_);
lean_dec_ref(v___y_2379_);
lean_dec(v___y_2378_);
lean_dec_ref(v___y_2377_);
lean_dec_ref(v_as_2373_);
return v_res_2384_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8(lean_object* v_fixedParamPerms_2385_, lean_object* v_xs_2386_, lean_object* v_as_2387_, size_t v_sz_2388_, size_t v_i_2389_, lean_object* v_bs_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_){
_start:
{
lean_object* v___x_2396_; 
v___x_2396_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg(v_fixedParamPerms_2385_, v_xs_2386_, v_sz_2388_, v_i_2389_, v_bs_2390_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_);
return v___x_2396_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___boxed(lean_object* v_fixedParamPerms_2397_, lean_object* v_xs_2398_, lean_object* v_as_2399_, lean_object* v_sz_2400_, lean_object* v_i_2401_, lean_object* v_bs_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_){
_start:
{
size_t v_sz_boxed_2408_; size_t v_i_boxed_2409_; lean_object* v_res_2410_; 
v_sz_boxed_2408_ = lean_unbox_usize(v_sz_2400_);
lean_dec(v_sz_2400_);
v_i_boxed_2409_ = lean_unbox_usize(v_i_2401_);
lean_dec(v_i_2401_);
v_res_2410_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8(v_fixedParamPerms_2397_, v_xs_2398_, v_as_2399_, v_sz_boxed_2408_, v_i_boxed_2409_, v_bs_2402_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_);
lean_dec(v___y_2406_);
lean_dec_ref(v___y_2405_);
lean_dec(v___y_2404_);
lean_dec_ref(v___y_2403_);
lean_dec_ref(v_as_2399_);
return v_res_2410_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12(lean_object* v_00_u03b1_2411_, lean_object* v_preDefs_2412_, lean_object* v_k_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_){
_start:
{
lean_object* v___x_2419_; 
v___x_2419_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v_preDefs_2412_, v_k_2413_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_);
return v___x_2419_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___boxed(lean_object* v_00_u03b1_2420_, lean_object* v_preDefs_2421_, lean_object* v_k_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_){
_start:
{
lean_object* v_res_2428_; 
v_res_2428_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12(v_00_u03b1_2420_, v_preDefs_2421_, v_k_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_);
lean_dec(v___y_2426_);
lean_dec_ref(v___y_2425_);
lean_dec(v___y_2424_);
lean_dec_ref(v___y_2423_);
return v_res_2428_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14(uint8_t v_a_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_recArgInfos_2432_, lean_object* v___x_2433_, lean_object* v_preDefs_2434_, lean_object* v_a_2435_, lean_object* v_as_2436_, size_t v_sz_2437_, size_t v_i_2438_, lean_object* v_bs_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_){
_start:
{
lean_object* v___x_2445_; 
v___x_2445_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg(v_a_2429_, v_a_2430_, v_a_2431_, v_recArgInfos_2432_, v___x_2433_, v_preDefs_2434_, v_a_2435_, v_sz_2437_, v_i_2438_, v_bs_2439_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_);
return v___x_2445_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___boxed(lean_object* v_a_2446_, lean_object* v_a_2447_, lean_object* v_a_2448_, lean_object* v_recArgInfos_2449_, lean_object* v___x_2450_, lean_object* v_preDefs_2451_, lean_object* v_a_2452_, lean_object* v_as_2453_, lean_object* v_sz_2454_, lean_object* v_i_2455_, lean_object* v_bs_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_){
_start:
{
uint8_t v_a_29929__boxed_2462_; size_t v_sz_boxed_2463_; size_t v_i_boxed_2464_; lean_object* v_res_2465_; 
v_a_29929__boxed_2462_ = lean_unbox(v_a_2446_);
v_sz_boxed_2463_ = lean_unbox_usize(v_sz_2454_);
lean_dec(v_sz_2454_);
v_i_boxed_2464_ = lean_unbox_usize(v_i_2455_);
lean_dec(v_i_2455_);
v_res_2465_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14(v_a_29929__boxed_2462_, v_a_2447_, v_a_2448_, v_recArgInfos_2449_, v___x_2450_, v_preDefs_2451_, v_a_2452_, v_as_2453_, v_sz_boxed_2463_, v_i_boxed_2464_, v_bs_2456_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_);
lean_dec(v___y_2460_);
lean_dec_ref(v___y_2459_);
lean_dec(v___y_2458_);
lean_dec_ref(v___y_2457_);
lean_dec_ref(v_as_2453_);
lean_dec_ref(v_a_2448_);
lean_dec_ref(v_a_2447_);
return v_res_2465_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17_spec__30(lean_object* v_00_u03b2_2466_){
_start:
{
lean_object* v___x_2467_; 
v___x_2467_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__2);
return v___x_2467_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg(){
_start:
{
lean_object* v___x_2469_; 
v___x_2469_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__2);
return v___x_2469_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg___boxed(lean_object* v___dummy_2470_){
_start:
{
lean_object* v_res_2471_; 
v_res_2471_ = l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg();
return v_res_2471_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17(lean_object* v_00_u03b2_2472_){
_start:
{
lean_object* v___x_2473_; 
v___x_2473_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg___closed__2);
return v___x_2473_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19(lean_object* v_preDefs_2474_, lean_object* v_xs_2475_, uint8_t v_a_2476_, lean_object* v___x_2477_, lean_object* v_as_2478_, size_t v_sz_2479_, size_t v_i_2480_, lean_object* v_bs_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_){
_start:
{
lean_object* v___x_2487_; 
v___x_2487_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___redArg(v_preDefs_2474_, v_xs_2475_, v_a_2476_, v___x_2477_, v_sz_2479_, v_i_2480_, v_bs_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_);
return v___x_2487_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___boxed(lean_object* v_preDefs_2488_, lean_object* v_xs_2489_, lean_object* v_a_2490_, lean_object* v___x_2491_, lean_object* v_as_2492_, lean_object* v_sz_2493_, lean_object* v_i_2494_, lean_object* v_bs_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_){
_start:
{
uint8_t v_a_29970__boxed_2501_; size_t v_sz_boxed_2502_; size_t v_i_boxed_2503_; lean_object* v_res_2504_; 
v_a_29970__boxed_2501_ = lean_unbox(v_a_2490_);
v_sz_boxed_2502_ = lean_unbox_usize(v_sz_2493_);
lean_dec(v_sz_2493_);
v_i_boxed_2503_ = lean_unbox_usize(v_i_2494_);
lean_dec(v_i_2494_);
v_res_2504_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19(v_preDefs_2488_, v_xs_2489_, v_a_29970__boxed_2501_, v___x_2491_, v_as_2492_, v_sz_boxed_2502_, v_i_boxed_2503_, v_bs_2495_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_);
lean_dec(v___y_2499_);
lean_dec_ref(v___y_2498_);
lean_dec(v___y_2497_);
lean_dec_ref(v___y_2496_);
lean_dec_ref(v_as_2492_);
lean_dec_ref(v_xs_2489_);
return v_res_2504_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__20(lean_object* v_a_2505_, lean_object* v_funTypes_2506_, lean_object* v_as_2507_, size_t v_sz_2508_, size_t v_i_2509_, lean_object* v_bs_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_){
_start:
{
lean_object* v___x_2516_; 
v___x_2516_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__20___redArg(v_a_2505_, v_funTypes_2506_, v_sz_2508_, v_i_2509_, v_bs_2510_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_);
return v___x_2516_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__20___boxed(lean_object* v_a_2517_, lean_object* v_funTypes_2518_, lean_object* v_as_2519_, lean_object* v_sz_2520_, lean_object* v_i_2521_, lean_object* v_bs_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_){
_start:
{
size_t v_sz_boxed_2528_; size_t v_i_boxed_2529_; lean_object* v_res_2530_; 
v_sz_boxed_2528_ = lean_unbox_usize(v_sz_2520_);
lean_dec(v_sz_2520_);
v_i_boxed_2529_ = lean_unbox_usize(v_i_2521_);
lean_dec(v_i_2521_);
v_res_2530_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__20(v_a_2517_, v_funTypes_2518_, v_as_2519_, v_sz_boxed_2528_, v_i_boxed_2529_, v_bs_2522_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_);
lean_dec(v___y_2526_);
lean_dec_ref(v___y_2525_);
lean_dec(v___y_2524_);
lean_dec_ref(v___y_2523_);
lean_dec_ref(v_as_2519_);
lean_dec_ref(v_funTypes_2518_);
lean_dec_ref(v_a_2517_);
return v_res_2530_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__21(lean_object* v_a_2531_, lean_object* v_a_2532_, lean_object* v_as_2533_, size_t v_sz_2534_, size_t v_i_2535_, lean_object* v_bs_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_){
_start:
{
lean_object* v___x_2542_; 
v___x_2542_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__21___redArg(v_a_2531_, v_a_2532_, v_sz_2534_, v_i_2535_, v_bs_2536_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_);
return v___x_2542_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__21___boxed(lean_object* v_a_2543_, lean_object* v_a_2544_, lean_object* v_as_2545_, lean_object* v_sz_2546_, lean_object* v_i_2547_, lean_object* v_bs_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_){
_start:
{
size_t v_sz_boxed_2554_; size_t v_i_boxed_2555_; lean_object* v_res_2556_; 
v_sz_boxed_2554_ = lean_unbox_usize(v_sz_2546_);
lean_dec(v_sz_2546_);
v_i_boxed_2555_ = lean_unbox_usize(v_i_2547_);
lean_dec(v_i_2547_);
v_res_2556_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__21(v_a_2543_, v_a_2544_, v_as_2545_, v_sz_boxed_2554_, v_i_boxed_2555_, v_bs_2548_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_);
lean_dec(v___y_2552_);
lean_dec_ref(v___y_2551_);
lean_dec(v___y_2550_);
lean_dec_ref(v___y_2549_);
lean_dec_ref(v_as_2545_);
lean_dec_ref(v_a_2544_);
lean_dec_ref(v_a_2543_);
return v_res_2556_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4(lean_object* v_00_u03b1_2557_, lean_object* v_msg_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_){
_start:
{
lean_object* v___x_2564_; 
v___x_2564_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg(v_msg_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_);
return v___x_2564_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___boxed(lean_object* v_00_u03b1_2565_, lean_object* v_msg_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_){
_start:
{
lean_object* v_res_2572_; 
v_res_2572_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4(v_00_u03b1_2565_, v_msg_2566_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_);
lean_dec(v___y_2570_);
lean_dec_ref(v___y_2569_);
lean_dec(v___y_2568_);
lean_dec_ref(v___y_2567_);
return v_res_2572_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9(lean_object* v_xs_2573_, lean_object* v_ys_2574_, lean_object* v_hsz_2575_, lean_object* v_x_2576_, lean_object* v_x_2577_){
_start:
{
uint8_t v___x_2578_; 
v___x_2578_ = l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9___redArg(v_xs_2573_, v_ys_2574_, v_x_2576_);
return v___x_2578_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9___boxed(lean_object* v_xs_2579_, lean_object* v_ys_2580_, lean_object* v_hsz_2581_, lean_object* v_x_2582_, lean_object* v_x_2583_){
_start:
{
uint8_t v_res_2584_; lean_object* v_r_2585_; 
v_res_2584_ = l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9(v_xs_2579_, v_ys_2580_, v_hsz_2581_, v_x_2582_, v_x_2583_);
lean_dec_ref(v_ys_2580_);
lean_dec_ref(v_xs_2579_);
v_r_2585_ = lean_box(v_res_2584_);
return v_r_2585_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10(lean_object* v_n_2586_, lean_object* v_as_2587_, lean_object* v_lo_2588_, lean_object* v_hi_2589_, lean_object* v_w_2590_, lean_object* v_hlo_2591_, lean_object* v_hhi_2592_){
_start:
{
lean_object* v___x_2593_; 
v___x_2593_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg(v_n_2586_, v_as_2587_, v_lo_2588_, v_hi_2589_);
return v___x_2593_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___boxed(lean_object* v_n_2594_, lean_object* v_as_2595_, lean_object* v_lo_2596_, lean_object* v_hi_2597_, lean_object* v_w_2598_, lean_object* v_hlo_2599_, lean_object* v_hhi_2600_){
_start:
{
lean_object* v_res_2601_; 
v_res_2601_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10(v_n_2594_, v_as_2595_, v_lo_2596_, v_hi_2597_, v_w_2598_, v_hlo_2599_, v_hhi_2600_);
lean_dec(v_hi_2597_);
lean_dec(v_n_2594_);
return v_res_2601_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15(lean_object* v_00_u03b1_2602_, lean_object* v_00_u03b3_2603_, lean_object* v_xs_2604_, lean_object* v_f_2605_, lean_object* v_as_2606_, lean_object* v_bs_2607_, lean_object* v_i_2608_, lean_object* v_cs_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_){
_start:
{
lean_object* v___x_2615_; 
v___x_2615_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15___redArg(v_xs_2604_, v_f_2605_, v_as_2606_, v_bs_2607_, v_i_2608_, v_cs_2609_, v___y_2610_, v___y_2611_, v___y_2612_, v___y_2613_);
return v___x_2615_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15___boxed(lean_object* v_00_u03b1_2616_, lean_object* v_00_u03b3_2617_, lean_object* v_xs_2618_, lean_object* v_f_2619_, lean_object* v_as_2620_, lean_object* v_bs_2621_, lean_object* v_i_2622_, lean_object* v_cs_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_){
_start:
{
lean_object* v_res_2629_; 
v_res_2629_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15(v_00_u03b1_2616_, v_00_u03b3_2617_, v_xs_2618_, v_f_2619_, v_as_2620_, v_bs_2621_, v_i_2622_, v_cs_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_);
lean_dec(v___y_2627_);
lean_dec_ref(v___y_2626_);
lean_dec(v___y_2625_);
lean_dec_ref(v___y_2624_);
lean_dec_ref(v_bs_2621_);
lean_dec_ref(v_as_2620_);
lean_dec_ref(v_xs_2618_);
return v_res_2629_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23(lean_object* v_00_u03b1_2630_, lean_object* v_env_2631_, lean_object* v_x_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_){
_start:
{
lean_object* v___x_2638_; 
v___x_2638_ = l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23___redArg(v_env_2631_, v_x_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_);
return v___x_2638_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23___boxed(lean_object* v_00_u03b1_2639_, lean_object* v_env_2640_, lean_object* v_x_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_){
_start:
{
lean_object* v_res_2647_; 
v_res_2647_ = l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23(v_00_u03b1_2639_, v_env_2640_, v_x_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_);
lean_dec(v___y_2645_);
lean_dec_ref(v___y_2644_);
lean_dec(v___y_2643_);
lean_dec_ref(v___y_2642_);
return v_res_2647_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32(lean_object* v_declName_2648_, uint8_t v_s_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_){
_start:
{
lean_object* v___x_2655_; 
v___x_2655_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___redArg(v_declName_2648_, v_s_2649_, v___y_2651_, v___y_2653_);
return v___x_2655_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32___boxed(lean_object* v_declName_2656_, lean_object* v_s_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_){
_start:
{
uint8_t v_s_boxed_2663_; lean_object* v_res_2664_; 
v_s_boxed_2663_ = lean_unbox(v_s_2657_);
v_res_2664_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18_spec__32(v_declName_2656_, v_s_boxed_2663_, v___y_2658_, v___y_2659_, v___y_2660_, v___y_2661_);
lean_dec(v___y_2661_);
lean_dec_ref(v___y_2660_);
lean_dec(v___y_2659_);
lean_dec_ref(v___y_2658_);
return v_res_2664_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11(lean_object* v_n_2665_, lean_object* v_lo_2666_, lean_object* v_hi_2667_, lean_object* v_hhi_2668_, lean_object* v_pivot_2669_, lean_object* v_as_2670_, lean_object* v_i_2671_, lean_object* v_k_2672_, lean_object* v_ilo_2673_, lean_object* v_ik_2674_, lean_object* v_w_2675_){
_start:
{
lean_object* v___x_2676_; 
v___x_2676_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11___redArg(v_hi_2667_, v_pivot_2669_, v_as_2670_, v_i_2671_, v_k_2672_);
return v___x_2676_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11___boxed(lean_object* v_n_2677_, lean_object* v_lo_2678_, lean_object* v_hi_2679_, lean_object* v_hhi_2680_, lean_object* v_pivot_2681_, lean_object* v_as_2682_, lean_object* v_i_2683_, lean_object* v_k_2684_, lean_object* v_ilo_2685_, lean_object* v_ik_2686_, lean_object* v_w_2687_){
_start:
{
lean_object* v_res_2688_; 
v_res_2688_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11(v_n_2677_, v_lo_2678_, v_hi_2679_, v_hhi_2680_, v_pivot_2681_, v_as_2682_, v_i_2683_, v_k_2684_, v_ilo_2685_, v_ik_2686_, v_w_2687_);
lean_dec(v_pivot_2681_);
lean_dec(v_hi_2679_);
lean_dec(v_lo_2678_);
lean_dec(v_n_2677_);
return v_res_2688_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25(lean_object* v_env_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_){
_start:
{
lean_object* v___x_2695_; 
v___x_2695_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg(v_env_2689_, v___y_2691_, v___y_2693_);
return v___x_2695_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___boxed(lean_object* v_env_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_){
_start:
{
lean_object* v_res_2702_; 
v_res_2702_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25(v_env_2696_, v___y_2697_, v___y_2698_, v___y_2699_, v___y_2700_);
lean_dec(v___y_2700_);
lean_dec_ref(v___y_2699_);
lean_dec(v___y_2698_);
lean_dec_ref(v___y_2697_);
return v_res_2702_;
}
}
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg___lam__0(lean_object* v_x_2703_){
_start:
{
uint8_t v___x_2704_; 
v___x_2704_ = 0;
return v___x_2704_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg___lam__0___boxed(lean_object* v_x_2705_){
_start:
{
uint8_t v_res_2706_; lean_object* v_r_2707_; 
v_res_2706_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg___lam__0(v_x_2705_);
lean_dec(v_x_2705_);
v_r_2707_ = lean_box(v_res_2706_);
return v_r_2707_;
}
}
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg___lam__1(lean_object* v_fvarId_2708_, lean_object* v_x_2709_){
_start:
{
uint8_t v___x_2710_; 
v___x_2710_ = l_Lean_instBEqFVarId_beq(v_fvarId_2708_, v_x_2709_);
return v___x_2710_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg___lam__1___boxed(lean_object* v_fvarId_2711_, lean_object* v_x_2712_){
_start:
{
uint8_t v_res_2713_; lean_object* v_r_2714_; 
v_res_2713_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg___lam__1(v_fvarId_2711_, v_x_2712_);
lean_dec(v_x_2712_);
lean_dec(v_fvarId_2711_);
v_r_2714_ = lean_box(v_res_2713_);
return v_r_2714_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; 
v___x_2716_ = lean_box(0);
v___x_2717_ = lean_unsigned_to_nat(16u);
v___x_2718_ = lean_mk_array(v___x_2717_, v___x_2716_);
return v___x_2718_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; 
v___x_2719_ = lean_obj_once(&l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg___closed__1, &l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg___closed__1_once, _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg___closed__1);
v___x_2720_ = lean_unsigned_to_nat(0u);
v___x_2721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2721_, 0, v___x_2720_);
lean_ctor_set(v___x_2721_, 1, v___x_2719_);
return v___x_2721_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg(lean_object* v_e_2722_, lean_object* v_fvarId_2723_, lean_object* v___y_2724_){
_start:
{
lean_object* v___f_2726_; lean_object* v___f_2727_; lean_object* v___x_2728_; uint8_t v_fst_2730_; lean_object* v_mctx_2731_; lean_object* v___y_2749_; lean_object* v_mctx_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; uint8_t v___x_2757_; 
v___f_2726_ = ((lean_object*)(l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg___closed__0));
v___f_2727_ = lean_alloc_closure((void*)(l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_2727_, 0, v_fvarId_2723_);
v___x_2728_ = lean_st_ref_get(v___y_2724_);
v_mctx_2754_ = lean_ctor_get(v___x_2728_, 0);
lean_inc_ref_n(v_mctx_2754_, 2);
lean_dec(v___x_2728_);
v___x_2755_ = lean_obj_once(&l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg___closed__2, &l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg___closed__2_once, _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg___closed__2);
v___x_2756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2756_, 0, v___x_2755_);
lean_ctor_set(v___x_2756_, 1, v_mctx_2754_);
v___x_2757_ = l_Lean_Expr_hasFVar(v_e_2722_);
if (v___x_2757_ == 0)
{
uint8_t v___x_2758_; 
v___x_2758_ = l_Lean_Expr_hasMVar(v_e_2722_);
if (v___x_2758_ == 0)
{
lean_dec_ref_known(v___x_2756_, 2);
lean_dec_ref(v___f_2727_);
lean_dec_ref(v_e_2722_);
v_fst_2730_ = v___x_2758_;
v_mctx_2731_ = v_mctx_2754_;
goto v___jp_2729_;
}
else
{
lean_object* v___x_2759_; 
lean_dec_ref(v_mctx_2754_);
v___x_2759_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2727_, v___f_2726_, v_e_2722_, v___x_2756_);
v___y_2749_ = v___x_2759_;
goto v___jp_2748_;
}
}
else
{
lean_object* v___x_2760_; 
lean_dec_ref(v_mctx_2754_);
v___x_2760_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2727_, v___f_2726_, v_e_2722_, v___x_2756_);
v___y_2749_ = v___x_2760_;
goto v___jp_2748_;
}
v___jp_2729_:
{
lean_object* v___x_2732_; lean_object* v_cache_2733_; lean_object* v_zetaDeltaFVarIds_2734_; lean_object* v_postponed_2735_; lean_object* v_diag_2736_; lean_object* v___x_2738_; uint8_t v_isShared_2739_; uint8_t v_isSharedCheck_2746_; 
v___x_2732_ = lean_st_ref_take(v___y_2724_);
v_cache_2733_ = lean_ctor_get(v___x_2732_, 1);
v_zetaDeltaFVarIds_2734_ = lean_ctor_get(v___x_2732_, 2);
v_postponed_2735_ = lean_ctor_get(v___x_2732_, 3);
v_diag_2736_ = lean_ctor_get(v___x_2732_, 4);
v_isSharedCheck_2746_ = !lean_is_exclusive(v___x_2732_);
if (v_isSharedCheck_2746_ == 0)
{
lean_object* v_unused_2747_; 
v_unused_2747_ = lean_ctor_get(v___x_2732_, 0);
lean_dec(v_unused_2747_);
v___x_2738_ = v___x_2732_;
v_isShared_2739_ = v_isSharedCheck_2746_;
goto v_resetjp_2737_;
}
else
{
lean_inc(v_diag_2736_);
lean_inc(v_postponed_2735_);
lean_inc(v_zetaDeltaFVarIds_2734_);
lean_inc(v_cache_2733_);
lean_dec(v___x_2732_);
v___x_2738_ = lean_box(0);
v_isShared_2739_ = v_isSharedCheck_2746_;
goto v_resetjp_2737_;
}
v_resetjp_2737_:
{
lean_object* v___x_2741_; 
if (v_isShared_2739_ == 0)
{
lean_ctor_set(v___x_2738_, 0, v_mctx_2731_);
v___x_2741_ = v___x_2738_;
goto v_reusejp_2740_;
}
else
{
lean_object* v_reuseFailAlloc_2745_; 
v_reuseFailAlloc_2745_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2745_, 0, v_mctx_2731_);
lean_ctor_set(v_reuseFailAlloc_2745_, 1, v_cache_2733_);
lean_ctor_set(v_reuseFailAlloc_2745_, 2, v_zetaDeltaFVarIds_2734_);
lean_ctor_set(v_reuseFailAlloc_2745_, 3, v_postponed_2735_);
lean_ctor_set(v_reuseFailAlloc_2745_, 4, v_diag_2736_);
v___x_2741_ = v_reuseFailAlloc_2745_;
goto v_reusejp_2740_;
}
v_reusejp_2740_:
{
lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; 
v___x_2742_ = lean_st_ref_put(v___y_2724_, v___x_2741_);
v___x_2743_ = lean_box(v_fst_2730_);
v___x_2744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2744_, 0, v___x_2743_);
return v___x_2744_;
}
}
}
v___jp_2748_:
{
lean_object* v_snd_2750_; lean_object* v_fst_2751_; lean_object* v_mctx_2752_; uint8_t v___x_2753_; 
v_snd_2750_ = lean_ctor_get(v___y_2749_, 1);
lean_inc(v_snd_2750_);
v_fst_2751_ = lean_ctor_get(v___y_2749_, 0);
lean_inc(v_fst_2751_);
lean_dec_ref(v___y_2749_);
v_mctx_2752_ = lean_ctor_get(v_snd_2750_, 1);
lean_inc_ref(v_mctx_2752_);
lean_dec(v_snd_2750_);
v___x_2753_ = lean_unbox(v_fst_2751_);
lean_dec(v_fst_2751_);
v_fst_2730_ = v___x_2753_;
v_mctx_2731_ = v_mctx_2752_;
goto v___jp_2729_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg___boxed(lean_object* v_e_2761_, lean_object* v_fvarId_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_){
_start:
{
lean_object* v_res_2765_; 
v_res_2765_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg(v_e_2761_, v_fvarId_2762_, v___y_2763_);
lean_dec(v___y_2763_);
return v_res_2765_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4(lean_object* v_e_2766_, lean_object* v_fvarId_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_){
_start:
{
lean_object* v___x_2773_; 
v___x_2773_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg(v_e_2766_, v_fvarId_2767_, v___y_2769_);
return v___x_2773_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___boxed(lean_object* v_e_2774_, lean_object* v_fvarId_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_){
_start:
{
lean_object* v_res_2781_; 
v_res_2781_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4(v_e_2774_, v_fvarId_2775_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2779_);
lean_dec(v___y_2779_);
lean_dec_ref(v___y_2778_);
lean_dec(v___y_2777_);
lean_dec_ref(v___y_2776_);
return v_res_2781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg___lam__0(lean_object* v_k_2782_, lean_object* v_b_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_){
_start:
{
lean_object* v___x_2789_; 
lean_inc(v___y_2787_);
lean_inc_ref(v___y_2786_);
lean_inc(v___y_2785_);
lean_inc_ref(v___y_2784_);
v___x_2789_ = lean_apply_6(v_k_2782_, v_b_2783_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_, lean_box(0));
return v___x_2789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg___lam__0___boxed(lean_object* v_k_2790_, lean_object* v_b_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_){
_start:
{
lean_object* v_res_2797_; 
v_res_2797_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg___lam__0(v_k_2790_, v_b_2791_, v___y_2792_, v___y_2793_, v___y_2794_, v___y_2795_);
lean_dec(v___y_2795_);
lean_dec_ref(v___y_2794_);
lean_dec(v___y_2793_);
lean_dec_ref(v___y_2792_);
return v_res_2797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg(lean_object* v_perm_2798_, lean_object* v_type_2799_, lean_object* v_k_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_){
_start:
{
lean_object* v___f_2806_; lean_object* v___x_2807_; 
v___f_2806_ = lean_alloc_closure((void*)(l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2806_, 0, v_k_2800_);
v___x_2807_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl(lean_box(0), v_perm_2798_, v_type_2799_, v___f_2806_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_);
if (lean_obj_tag(v___x_2807_) == 0)
{
lean_object* v_a_2808_; lean_object* v___x_2810_; uint8_t v_isShared_2811_; uint8_t v_isSharedCheck_2815_; 
v_a_2808_ = lean_ctor_get(v___x_2807_, 0);
v_isSharedCheck_2815_ = !lean_is_exclusive(v___x_2807_);
if (v_isSharedCheck_2815_ == 0)
{
v___x_2810_ = v___x_2807_;
v_isShared_2811_ = v_isSharedCheck_2815_;
goto v_resetjp_2809_;
}
else
{
lean_inc(v_a_2808_);
lean_dec(v___x_2807_);
v___x_2810_ = lean_box(0);
v_isShared_2811_ = v_isSharedCheck_2815_;
goto v_resetjp_2809_;
}
v_resetjp_2809_:
{
lean_object* v___x_2813_; 
if (v_isShared_2811_ == 0)
{
v___x_2813_ = v___x_2810_;
goto v_reusejp_2812_;
}
else
{
lean_object* v_reuseFailAlloc_2814_; 
v_reuseFailAlloc_2814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2814_, 0, v_a_2808_);
v___x_2813_ = v_reuseFailAlloc_2814_;
goto v_reusejp_2812_;
}
v_reusejp_2812_:
{
return v___x_2813_;
}
}
}
else
{
lean_object* v_a_2816_; lean_object* v___x_2818_; uint8_t v_isShared_2819_; uint8_t v_isSharedCheck_2823_; 
v_a_2816_ = lean_ctor_get(v___x_2807_, 0);
v_isSharedCheck_2823_ = !lean_is_exclusive(v___x_2807_);
if (v_isSharedCheck_2823_ == 0)
{
v___x_2818_ = v___x_2807_;
v_isShared_2819_ = v_isSharedCheck_2823_;
goto v_resetjp_2817_;
}
else
{
lean_inc(v_a_2816_);
lean_dec(v___x_2807_);
v___x_2818_ = lean_box(0);
v_isShared_2819_ = v_isSharedCheck_2823_;
goto v_resetjp_2817_;
}
v_resetjp_2817_:
{
lean_object* v___x_2821_; 
if (v_isShared_2819_ == 0)
{
v___x_2821_ = v___x_2818_;
goto v_reusejp_2820_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2822_, 0, v_a_2816_);
v___x_2821_ = v_reuseFailAlloc_2822_;
goto v_reusejp_2820_;
}
v_reusejp_2820_:
{
return v___x_2821_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg___boxed(lean_object* v_perm_2824_, lean_object* v_type_2825_, lean_object* v_k_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_){
_start:
{
lean_object* v_res_2832_; 
v_res_2832_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg(v_perm_2824_, v_type_2825_, v_k_2826_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_);
lean_dec(v___y_2830_);
lean_dec_ref(v___y_2829_);
lean_dec(v___y_2828_);
lean_dec_ref(v___y_2827_);
return v_res_2832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12(lean_object* v_00_u03b1_2833_, lean_object* v_perm_2834_, lean_object* v_type_2835_, lean_object* v_k_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_){
_start:
{
lean_object* v___x_2842_; 
v___x_2842_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg(v_perm_2834_, v_type_2835_, v_k_2836_, v___y_2837_, v___y_2838_, v___y_2839_, v___y_2840_);
return v___x_2842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___boxed(lean_object* v_00_u03b1_2843_, lean_object* v_perm_2844_, lean_object* v_type_2845_, lean_object* v_k_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_){
_start:
{
lean_object* v_res_2852_; 
v_res_2852_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12(v_00_u03b1_2843_, v_perm_2844_, v_type_2845_, v_k_2846_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_);
lean_dec(v___y_2850_);
lean_dec_ref(v___y_2849_);
lean_dec(v___y_2848_);
lean_dec_ref(v___y_2847_);
return v_res_2852_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1(lean_object* v_a_2853_, lean_object* v_fst_2854_, lean_object* v_fst_2855_, lean_object* v___x_2856_, lean_object* v___x_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_){
_start:
{
lean_object* v___x_2863_; 
lean_inc_ref(v_fst_2854_);
v___x_2863_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion(v_a_2853_, v_fst_2854_, v_fst_2855_, v___x_2856_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_);
if (lean_obj_tag(v___x_2863_) == 0)
{
lean_object* v_a_2864_; lean_object* v___x_2866_; uint8_t v_isShared_2867_; uint8_t v_isSharedCheck_2873_; 
v_a_2864_ = lean_ctor_get(v___x_2863_, 0);
v_isSharedCheck_2873_ = !lean_is_exclusive(v___x_2863_);
if (v_isSharedCheck_2873_ == 0)
{
v___x_2866_ = v___x_2863_;
v_isShared_2867_ = v_isSharedCheck_2873_;
goto v_resetjp_2865_;
}
else
{
lean_inc(v_a_2864_);
lean_dec(v___x_2863_);
v___x_2866_ = lean_box(0);
v_isShared_2867_ = v_isSharedCheck_2873_;
goto v_resetjp_2865_;
}
v_resetjp_2865_:
{
lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2871_; 
v___x_2868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2868_, 0, v_a_2864_);
lean_ctor_set(v___x_2868_, 1, v_fst_2854_);
v___x_2869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2869_, 0, v___x_2857_);
lean_ctor_set(v___x_2869_, 1, v___x_2868_);
if (v_isShared_2867_ == 0)
{
lean_ctor_set(v___x_2866_, 0, v___x_2869_);
v___x_2871_ = v___x_2866_;
goto v_reusejp_2870_;
}
else
{
lean_object* v_reuseFailAlloc_2872_; 
v_reuseFailAlloc_2872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2872_, 0, v___x_2869_);
v___x_2871_ = v_reuseFailAlloc_2872_;
goto v_reusejp_2870_;
}
v_reusejp_2870_:
{
return v___x_2871_;
}
}
}
else
{
lean_object* v_a_2874_; lean_object* v___x_2876_; uint8_t v_isShared_2877_; uint8_t v_isSharedCheck_2881_; 
lean_dec_ref(v___x_2857_);
lean_dec_ref(v_fst_2854_);
v_a_2874_ = lean_ctor_get(v___x_2863_, 0);
v_isSharedCheck_2881_ = !lean_is_exclusive(v___x_2863_);
if (v_isSharedCheck_2881_ == 0)
{
v___x_2876_ = v___x_2863_;
v_isShared_2877_ = v_isSharedCheck_2881_;
goto v_resetjp_2875_;
}
else
{
lean_inc(v_a_2874_);
lean_dec(v___x_2863_);
v___x_2876_ = lean_box(0);
v_isShared_2877_ = v_isSharedCheck_2881_;
goto v_resetjp_2875_;
}
v_resetjp_2875_:
{
lean_object* v___x_2879_; 
if (v_isShared_2877_ == 0)
{
v___x_2879_ = v___x_2876_;
goto v_reusejp_2878_;
}
else
{
lean_object* v_reuseFailAlloc_2880_; 
v_reuseFailAlloc_2880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2880_, 0, v_a_2874_);
v___x_2879_ = v_reuseFailAlloc_2880_;
goto v_reusejp_2878_;
}
v_reusejp_2878_:
{
return v___x_2879_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___boxed(lean_object* v_a_2882_, lean_object* v_fst_2883_, lean_object* v_fst_2884_, lean_object* v___x_2885_, lean_object* v___x_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_){
_start:
{
lean_object* v_res_2892_; 
v_res_2892_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1(v_a_2882_, v_fst_2883_, v_fst_2884_, v___x_2885_, v___x_2886_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_);
lean_dec(v___y_2890_);
lean_dec_ref(v___y_2889_);
lean_dec(v___y_2888_);
lean_dec_ref(v___y_2887_);
return v_res_2892_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1(size_t v_sz_2893_, size_t v_i_2894_, lean_object* v_bs_2895_){
_start:
{
uint8_t v___x_2896_; 
v___x_2896_ = lean_usize_dec_lt(v_i_2894_, v_sz_2893_);
if (v___x_2896_ == 0)
{
return v_bs_2895_;
}
else
{
lean_object* v_v_2897_; lean_object* v_recArgPos_2898_; lean_object* v___x_2899_; lean_object* v_bs_x27_2900_; size_t v___x_2901_; size_t v___x_2902_; lean_object* v___x_2903_; 
v_v_2897_ = lean_array_uget_borrowed(v_bs_2895_, v_i_2894_);
v_recArgPos_2898_ = lean_ctor_get(v_v_2897_, 2);
lean_inc(v_recArgPos_2898_);
v___x_2899_ = lean_unsigned_to_nat(0u);
v_bs_x27_2900_ = lean_array_uset(v_bs_2895_, v_i_2894_, v___x_2899_);
v___x_2901_ = ((size_t)1ULL);
v___x_2902_ = lean_usize_add(v_i_2894_, v___x_2901_);
v___x_2903_ = lean_array_uset(v_bs_x27_2900_, v_i_2894_, v_recArgPos_2898_);
v_i_2894_ = v___x_2902_;
v_bs_2895_ = v___x_2903_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1___boxed(lean_object* v_sz_2905_, lean_object* v_i_2906_, lean_object* v_bs_2907_){
_start:
{
size_t v_sz_boxed_2908_; size_t v_i_boxed_2909_; lean_object* v_res_2910_; 
v_sz_boxed_2908_ = lean_unbox_usize(v_sz_2905_);
lean_dec(v_sz_2905_);
v_i_boxed_2909_ = lean_unbox_usize(v_i_2906_);
lean_dec(v_i_2906_);
v_res_2910_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1(v_sz_boxed_2908_, v_i_boxed_2909_, v_bs_2907_);
return v_res_2910_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__11(lean_object* v_as_2911_, size_t v_i_2912_, size_t v_stop_2913_, lean_object* v_b_2914_){
_start:
{
uint8_t v___x_2915_; 
v___x_2915_ = lean_usize_dec_eq(v_i_2912_, v_stop_2913_);
if (v___x_2915_ == 0)
{
lean_object* v___x_2916_; lean_object* v___x_2917_; size_t v___x_2918_; size_t v___x_2919_; 
v___x_2916_ = lean_array_uget_borrowed(v_as_2911_, v_i_2912_);
v___x_2917_ = l_Lean_LocalContext_erase(v_b_2914_, v___x_2916_);
v___x_2918_ = ((size_t)1ULL);
v___x_2919_ = lean_usize_add(v_i_2912_, v___x_2918_);
v_i_2912_ = v___x_2919_;
v_b_2914_ = v___x_2917_;
goto _start;
}
else
{
return v_b_2914_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__11___boxed(lean_object* v_as_2921_, lean_object* v_i_2922_, lean_object* v_stop_2923_, lean_object* v_b_2924_){
_start:
{
size_t v_i_boxed_2925_; size_t v_stop_boxed_2926_; lean_object* v_res_2927_; 
v_i_boxed_2925_ = lean_unbox_usize(v_i_2922_);
lean_dec(v_i_2922_);
v_stop_boxed_2926_ = lean_unbox_usize(v_stop_2923_);
lean_dec(v_stop_2923_);
v_res_2927_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__11(v_as_2921_, v_i_boxed_2925_, v_stop_boxed_2926_, v_b_2924_);
lean_dec_ref(v_as_2921_);
return v_res_2927_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__8_spec__10(lean_object* v_a_2928_, lean_object* v_as_2929_, size_t v_i_2930_, size_t v_stop_2931_){
_start:
{
uint8_t v___x_2932_; 
v___x_2932_ = lean_usize_dec_eq(v_i_2930_, v_stop_2931_);
if (v___x_2932_ == 0)
{
lean_object* v___x_2933_; uint8_t v___x_2934_; 
v___x_2933_ = lean_array_uget_borrowed(v_as_2929_, v_i_2930_);
v___x_2934_ = l_Lean_instBEqFVarId_beq(v_a_2928_, v___x_2933_);
if (v___x_2934_ == 0)
{
size_t v___x_2935_; size_t v___x_2936_; 
v___x_2935_ = ((size_t)1ULL);
v___x_2936_ = lean_usize_add(v_i_2930_, v___x_2935_);
v_i_2930_ = v___x_2936_;
goto _start;
}
else
{
return v___x_2934_;
}
}
else
{
uint8_t v___x_2938_; 
v___x_2938_ = 0;
return v___x_2938_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__8_spec__10___boxed(lean_object* v_a_2939_, lean_object* v_as_2940_, lean_object* v_i_2941_, lean_object* v_stop_2942_){
_start:
{
size_t v_i_boxed_2943_; size_t v_stop_boxed_2944_; uint8_t v_res_2945_; lean_object* v_r_2946_; 
v_i_boxed_2943_ = lean_unbox_usize(v_i_2941_);
lean_dec(v_i_2941_);
v_stop_boxed_2944_ = lean_unbox_usize(v_stop_2942_);
lean_dec(v_stop_2942_);
v_res_2945_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__8_spec__10(v_a_2939_, v_as_2940_, v_i_boxed_2943_, v_stop_boxed_2944_);
lean_dec_ref(v_as_2940_);
lean_dec(v_a_2939_);
v_r_2946_ = lean_box(v_res_2945_);
return v_r_2946_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__8(lean_object* v_as_2947_, lean_object* v_a_2948_){
_start:
{
lean_object* v___x_2949_; lean_object* v___x_2950_; uint8_t v___x_2951_; 
v___x_2949_ = lean_unsigned_to_nat(0u);
v___x_2950_ = lean_array_get_size(v_as_2947_);
v___x_2951_ = lean_nat_dec_lt(v___x_2949_, v___x_2950_);
if (v___x_2951_ == 0)
{
return v___x_2951_;
}
else
{
size_t v___x_2952_; size_t v___x_2953_; uint8_t v___x_2954_; 
v___x_2952_ = ((size_t)0ULL);
v___x_2953_ = lean_usize_of_nat(v___x_2950_);
v___x_2954_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__8_spec__10(v_a_2948_, v_as_2947_, v___x_2952_, v___x_2953_);
return v___x_2954_;
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__8___boxed(lean_object* v_as_2955_, lean_object* v_a_2956_){
_start:
{
uint8_t v_res_2957_; lean_object* v_r_2958_; 
v_res_2957_ = l_Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__8(v_as_2955_, v_a_2956_);
lean_dec(v_a_2956_);
lean_dec_ref(v_as_2955_);
v_r_2958_ = lean_box(v_res_2957_);
return v_r_2958_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__10(lean_object* v_fvarIds_2959_, lean_object* v_as_2960_, size_t v_i_2961_, size_t v_stop_2962_, lean_object* v_b_2963_){
_start:
{
lean_object* v___y_2965_; uint8_t v___x_2969_; 
v___x_2969_ = lean_usize_dec_eq(v_i_2961_, v_stop_2962_);
if (v___x_2969_ == 0)
{
lean_object* v___x_2970_; lean_object* v_fvar_2971_; 
v___x_2970_ = lean_array_uget_borrowed(v_as_2960_, v_i_2961_);
v_fvar_2971_ = lean_ctor_get(v___x_2970_, 1);
if (lean_obj_tag(v_fvar_2971_) == 1)
{
lean_object* v_fvarId_2972_; uint8_t v___x_2973_; 
v_fvarId_2972_ = lean_ctor_get(v_fvar_2971_, 0);
v___x_2973_ = l_Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__8(v_fvarIds_2959_, v_fvarId_2972_);
if (v___x_2973_ == 0)
{
lean_object* v___x_2974_; 
lean_inc(v___x_2970_);
v___x_2974_ = lean_array_push(v_b_2963_, v___x_2970_);
v___y_2965_ = v___x_2974_;
goto v___jp_2964_;
}
else
{
v___y_2965_ = v_b_2963_;
goto v___jp_2964_;
}
}
else
{
lean_object* v___x_2975_; 
lean_inc(v___x_2970_);
v___x_2975_ = lean_array_push(v_b_2963_, v___x_2970_);
v___y_2965_ = v___x_2975_;
goto v___jp_2964_;
}
}
else
{
return v_b_2963_;
}
v___jp_2964_:
{
size_t v___x_2966_; size_t v___x_2967_; 
v___x_2966_ = ((size_t)1ULL);
v___x_2967_ = lean_usize_add(v_i_2961_, v___x_2966_);
v_i_2961_ = v___x_2967_;
v_b_2963_ = v___y_2965_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__10___boxed(lean_object* v_fvarIds_2976_, lean_object* v_as_2977_, lean_object* v_i_2978_, lean_object* v_stop_2979_, lean_object* v_b_2980_){
_start:
{
size_t v_i_boxed_2981_; size_t v_stop_boxed_2982_; lean_object* v_res_2983_; 
v_i_boxed_2981_ = lean_unbox_usize(v_i_2978_);
lean_dec(v_i_2978_);
v_stop_boxed_2982_ = lean_unbox_usize(v_stop_2979_);
lean_dec(v_stop_2979_);
v_res_2983_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__10(v_fvarIds_2976_, v_as_2977_, v_i_boxed_2981_, v_stop_boxed_2982_, v_b_2980_);
lean_dec_ref(v_as_2977_);
lean_dec_ref(v_fvarIds_2976_);
return v_res_2983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__9___redArg(lean_object* v_lctx_2984_, lean_object* v_localInsts_2985_, lean_object* v_x_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_){
_start:
{
lean_object* v___x_2992_; 
v___x_2992_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_2984_, v_localInsts_2985_, v_x_2986_, v___y_2987_, v___y_2988_, v___y_2989_, v___y_2990_);
if (lean_obj_tag(v___x_2992_) == 0)
{
lean_object* v_a_2993_; lean_object* v___x_2995_; uint8_t v_isShared_2996_; uint8_t v_isSharedCheck_3000_; 
v_a_2993_ = lean_ctor_get(v___x_2992_, 0);
v_isSharedCheck_3000_ = !lean_is_exclusive(v___x_2992_);
if (v_isSharedCheck_3000_ == 0)
{
v___x_2995_ = v___x_2992_;
v_isShared_2996_ = v_isSharedCheck_3000_;
goto v_resetjp_2994_;
}
else
{
lean_inc(v_a_2993_);
lean_dec(v___x_2992_);
v___x_2995_ = lean_box(0);
v_isShared_2996_ = v_isSharedCheck_3000_;
goto v_resetjp_2994_;
}
v_resetjp_2994_:
{
lean_object* v___x_2998_; 
if (v_isShared_2996_ == 0)
{
v___x_2998_ = v___x_2995_;
goto v_reusejp_2997_;
}
else
{
lean_object* v_reuseFailAlloc_2999_; 
v_reuseFailAlloc_2999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2999_, 0, v_a_2993_);
v___x_2998_ = v_reuseFailAlloc_2999_;
goto v_reusejp_2997_;
}
v_reusejp_2997_:
{
return v___x_2998_;
}
}
}
else
{
lean_object* v_a_3001_; lean_object* v___x_3003_; uint8_t v_isShared_3004_; uint8_t v_isSharedCheck_3008_; 
v_a_3001_ = lean_ctor_get(v___x_2992_, 0);
v_isSharedCheck_3008_ = !lean_is_exclusive(v___x_2992_);
if (v_isSharedCheck_3008_ == 0)
{
v___x_3003_ = v___x_2992_;
v_isShared_3004_ = v_isSharedCheck_3008_;
goto v_resetjp_3002_;
}
else
{
lean_inc(v_a_3001_);
lean_dec(v___x_2992_);
v___x_3003_ = lean_box(0);
v_isShared_3004_ = v_isSharedCheck_3008_;
goto v_resetjp_3002_;
}
v_resetjp_3002_:
{
lean_object* v___x_3006_; 
if (v_isShared_3004_ == 0)
{
v___x_3006_ = v___x_3003_;
goto v_reusejp_3005_;
}
else
{
lean_object* v_reuseFailAlloc_3007_; 
v_reuseFailAlloc_3007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3007_, 0, v_a_3001_);
v___x_3006_ = v_reuseFailAlloc_3007_;
goto v_reusejp_3005_;
}
v_reusejp_3005_:
{
return v___x_3006_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__9___redArg___boxed(lean_object* v_lctx_3009_, lean_object* v_localInsts_3010_, lean_object* v_x_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_){
_start:
{
lean_object* v_res_3017_; 
v_res_3017_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__9___redArg(v_lctx_3009_, v_localInsts_3010_, v_x_3011_, v___y_3012_, v___y_3013_, v___y_3014_, v___y_3015_);
lean_dec(v___y_3015_);
lean_dec_ref(v___y_3014_);
lean_dec(v___y_3013_);
lean_dec_ref(v___y_3012_);
return v_res_3017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8___redArg(lean_object* v_fvarIds_3020_, lean_object* v_k_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_){
_start:
{
lean_object* v_lctx_3027_; lean_object* v_localInstances_3028_; lean_object* v___y_3030_; lean_object* v___x_3040_; lean_object* v___x_3041_; uint8_t v___x_3042_; 
v_lctx_3027_ = lean_ctor_get(v___y_3022_, 2);
v_localInstances_3028_ = lean_ctor_get(v___y_3022_, 3);
v___x_3040_ = lean_unsigned_to_nat(0u);
v___x_3041_ = lean_array_get_size(v_fvarIds_3020_);
v___x_3042_ = lean_nat_dec_lt(v___x_3040_, v___x_3041_);
if (v___x_3042_ == 0)
{
lean_inc_ref(v_lctx_3027_);
v___y_3030_ = v_lctx_3027_;
goto v___jp_3029_;
}
else
{
size_t v___x_3043_; size_t v___x_3044_; lean_object* v___x_3045_; 
v___x_3043_ = ((size_t)0ULL);
v___x_3044_ = lean_usize_of_nat(v___x_3041_);
lean_inc_ref(v_lctx_3027_);
v___x_3045_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__11(v_fvarIds_3020_, v___x_3043_, v___x_3044_, v_lctx_3027_);
v___y_3030_ = v___x_3045_;
goto v___jp_3029_;
}
v___jp_3029_:
{
lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; uint8_t v___x_3034_; 
v___x_3031_ = lean_unsigned_to_nat(0u);
v___x_3032_ = lean_array_get_size(v_localInstances_3028_);
v___x_3033_ = ((lean_object*)(l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8___redArg___closed__0));
v___x_3034_ = lean_nat_dec_lt(v___x_3031_, v___x_3032_);
if (v___x_3034_ == 0)
{
lean_object* v___x_3035_; 
v___x_3035_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__9___redArg(v___y_3030_, v___x_3033_, v_k_3021_, v___y_3022_, v___y_3023_, v___y_3024_, v___y_3025_);
return v___x_3035_;
}
else
{
size_t v___x_3036_; size_t v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; 
v___x_3036_ = ((size_t)0ULL);
v___x_3037_ = lean_usize_of_nat(v___x_3032_);
v___x_3038_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__10(v_fvarIds_3020_, v_localInstances_3028_, v___x_3036_, v___x_3037_, v___x_3033_);
v___x_3039_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__9___redArg(v___y_3030_, v___x_3038_, v_k_3021_, v___y_3022_, v___y_3023_, v___y_3024_, v___y_3025_);
return v___x_3039_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8___redArg___boxed(lean_object* v_fvarIds_3046_, lean_object* v_k_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_){
_start:
{
lean_object* v_res_3053_; 
v_res_3053_ = l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8___redArg(v_fvarIds_3046_, v_k_3047_, v___y_3048_, v___y_3049_, v___y_3050_, v___y_3051_);
lean_dec(v___y_3051_);
lean_dec_ref(v___y_3050_);
lean_dec(v___y_3049_);
lean_dec_ref(v___y_3048_);
lean_dec_ref(v_fvarIds_3046_);
return v_res_3053_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___closed__1(void){
_start:
{
lean_object* v___x_3055_; lean_object* v___x_3056_; 
v___x_3055_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___closed__0));
v___x_3056_ = l_Lean_stringToMessageData(v___x_3055_);
return v___x_3056_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___closed__3(void){
_start:
{
lean_object* v___x_3058_; lean_object* v___x_3059_; 
v___x_3058_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___closed__2));
v___x_3059_ = l_Lean_stringToMessageData(v___x_3058_);
return v___x_3059_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___closed__5(void){
_start:
{
lean_object* v___x_3061_; lean_object* v___x_3062_; 
v___x_3061_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___closed__4));
v___x_3062_ = l_Lean_stringToMessageData(v___x_3061_);
return v___x_3062_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5(lean_object* v_a_3063_, lean_object* v_as_3064_, size_t v_sz_3065_, size_t v_i_3066_, lean_object* v_b_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_){
_start:
{
lean_object* v_a_3074_; uint8_t v___x_3078_; 
v___x_3078_ = lean_usize_dec_lt(v_i_3066_, v_sz_3065_);
if (v___x_3078_ == 0)
{
lean_object* v___x_3079_; 
lean_dec_ref(v_a_3063_);
v___x_3079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3079_, 0, v_b_3067_);
return v___x_3079_;
}
else
{
lean_object* v___x_3080_; lean_object* v_a_3081_; lean_object* v___x_3082_; 
v___x_3080_ = lean_box(0);
v_a_3081_ = lean_array_uget_borrowed(v_as_3064_, v_i_3066_);
lean_inc(v_a_3081_);
lean_inc_ref(v_a_3063_);
v___x_3082_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg(v_a_3063_, v_a_3081_, v___y_3069_);
if (lean_obj_tag(v___x_3082_) == 0)
{
lean_object* v_a_3083_; uint8_t v___x_3084_; 
v_a_3083_ = lean_ctor_get(v___x_3082_, 0);
lean_inc(v_a_3083_);
lean_dec_ref_known(v___x_3082_, 1);
v___x_3084_ = lean_unbox(v_a_3083_);
lean_dec(v_a_3083_);
if (v___x_3084_ == 0)
{
v_a_3074_ = v___x_3080_;
goto v___jp_3073_;
}
else
{
uint8_t v___x_3085_; 
v___x_3085_ = l_Lean_Expr_isFVarOf(v_a_3063_, v_a_3081_);
if (v___x_3085_ == 0)
{
lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; 
v___x_3086_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___closed__1);
lean_inc_ref(v_a_3063_);
v___x_3087_ = l_Lean_indentExpr(v_a_3063_);
v___x_3088_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3088_, 0, v___x_3086_);
lean_ctor_set(v___x_3088_, 1, v___x_3087_);
v___x_3089_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___closed__3);
v___x_3090_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3090_, 0, v___x_3088_);
lean_ctor_set(v___x_3090_, 1, v___x_3089_);
lean_inc(v_a_3081_);
v___x_3091_ = l_Lean_mkFVar(v_a_3081_);
v___x_3092_ = l_Lean_indentExpr(v___x_3091_);
v___x_3093_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3093_, 0, v___x_3090_);
lean_ctor_set(v___x_3093_, 1, v___x_3092_);
v___x_3094_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___closed__5);
v___x_3095_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3095_, 0, v___x_3093_);
lean_ctor_set(v___x_3095_, 1, v___x_3094_);
v___x_3096_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg(v___x_3095_, v___y_3068_, v___y_3069_, v___y_3070_, v___y_3071_);
if (lean_obj_tag(v___x_3096_) == 0)
{
lean_dec_ref_known(v___x_3096_, 1);
v_a_3074_ = v___x_3080_;
goto v___jp_3073_;
}
else
{
lean_dec_ref(v_a_3063_);
return v___x_3096_;
}
}
else
{
lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; 
v___x_3097_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___closed__1);
lean_inc_ref(v_a_3063_);
v___x_3098_ = l_Lean_indentExpr(v_a_3063_);
v___x_3099_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3099_, 0, v___x_3097_);
lean_ctor_set(v___x_3099_, 1, v___x_3098_);
v___x_3100_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___closed__5);
v___x_3101_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3101_, 0, v___x_3099_);
lean_ctor_set(v___x_3101_, 1, v___x_3100_);
v___x_3102_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg(v___x_3101_, v___y_3068_, v___y_3069_, v___y_3070_, v___y_3071_);
if (lean_obj_tag(v___x_3102_) == 0)
{
lean_dec_ref_known(v___x_3102_, 1);
v_a_3074_ = v___x_3080_;
goto v___jp_3073_;
}
else
{
lean_dec_ref(v_a_3063_);
return v___x_3102_;
}
}
}
}
else
{
lean_object* v_a_3103_; lean_object* v___x_3105_; uint8_t v_isShared_3106_; uint8_t v_isSharedCheck_3110_; 
lean_dec_ref(v_a_3063_);
v_a_3103_ = lean_ctor_get(v___x_3082_, 0);
v_isSharedCheck_3110_ = !lean_is_exclusive(v___x_3082_);
if (v_isSharedCheck_3110_ == 0)
{
v___x_3105_ = v___x_3082_;
v_isShared_3106_ = v_isSharedCheck_3110_;
goto v_resetjp_3104_;
}
else
{
lean_inc(v_a_3103_);
lean_dec(v___x_3082_);
v___x_3105_ = lean_box(0);
v_isShared_3106_ = v_isSharedCheck_3110_;
goto v_resetjp_3104_;
}
v_resetjp_3104_:
{
lean_object* v___x_3108_; 
if (v_isShared_3106_ == 0)
{
v___x_3108_ = v___x_3105_;
goto v_reusejp_3107_;
}
else
{
lean_object* v_reuseFailAlloc_3109_; 
v_reuseFailAlloc_3109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3109_, 0, v_a_3103_);
v___x_3108_ = v_reuseFailAlloc_3109_;
goto v_reusejp_3107_;
}
v_reusejp_3107_:
{
return v___x_3108_;
}
}
}
}
v___jp_3073_:
{
size_t v___x_3075_; size_t v___x_3076_; 
v___x_3075_ = ((size_t)1ULL);
v___x_3076_ = lean_usize_add(v_i_3066_, v___x_3075_);
v_i_3066_ = v___x_3076_;
v_b_3067_ = v_a_3074_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___boxed(lean_object* v_a_3111_, lean_object* v_as_3112_, lean_object* v_sz_3113_, lean_object* v_i_3114_, lean_object* v_b_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_){
_start:
{
size_t v_sz_boxed_3121_; size_t v_i_boxed_3122_; lean_object* v_res_3123_; 
v_sz_boxed_3121_ = lean_unbox_usize(v_sz_3113_);
lean_dec(v_sz_3113_);
v_i_boxed_3122_ = lean_unbox_usize(v_i_3114_);
lean_dec(v_i_3114_);
v_res_3123_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5(v_a_3111_, v_as_3112_, v_sz_boxed_3121_, v_i_boxed_3122_, v_b_3115_, v___y_3116_, v___y_3117_, v___y_3118_, v___y_3119_);
lean_dec(v___y_3119_);
lean_dec_ref(v___y_3118_);
lean_dec(v___y_3117_);
lean_dec_ref(v___y_3116_);
lean_dec_ref(v_as_3112_);
return v_res_3123_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6(lean_object* v_snd_3124_, lean_object* v_as_3125_, size_t v_sz_3126_, size_t v_i_3127_, lean_object* v_b_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_){
_start:
{
uint8_t v___x_3134_; 
v___x_3134_ = lean_usize_dec_lt(v_i_3127_, v_sz_3126_);
if (v___x_3134_ == 0)
{
lean_object* v___x_3135_; 
v___x_3135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3135_, 0, v_b_3128_);
return v___x_3135_;
}
else
{
lean_object* v___x_3136_; lean_object* v_a_3137_; size_t v_sz_3138_; size_t v___x_3139_; lean_object* v___x_3140_; 
v___x_3136_ = lean_box(0);
v_a_3137_ = lean_array_uget_borrowed(v_as_3125_, v_i_3127_);
v_sz_3138_ = lean_array_size(v_snd_3124_);
v___x_3139_ = ((size_t)0ULL);
lean_inc(v_a_3137_);
v___x_3140_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5(v_a_3137_, v_snd_3124_, v_sz_3138_, v___x_3139_, v___x_3136_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_);
if (lean_obj_tag(v___x_3140_) == 0)
{
size_t v___x_3141_; size_t v___x_3142_; 
lean_dec_ref_known(v___x_3140_, 1);
v___x_3141_ = ((size_t)1ULL);
v___x_3142_ = lean_usize_add(v_i_3127_, v___x_3141_);
v_i_3127_ = v___x_3142_;
v_b_3128_ = v___x_3136_;
goto _start;
}
else
{
return v___x_3140_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___boxed(lean_object* v_snd_3144_, lean_object* v_as_3145_, lean_object* v_sz_3146_, lean_object* v_i_3147_, lean_object* v_b_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_){
_start:
{
size_t v_sz_boxed_3154_; size_t v_i_boxed_3155_; lean_object* v_res_3156_; 
v_sz_boxed_3154_ = lean_unbox_usize(v_sz_3146_);
lean_dec(v_sz_3146_);
v_i_boxed_3155_ = lean_unbox_usize(v_i_3147_);
lean_dec(v_i_3147_);
v_res_3156_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6(v_snd_3144_, v_as_3145_, v_sz_boxed_3154_, v_i_boxed_3155_, v_b_3148_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_);
lean_dec(v___y_3152_);
lean_dec_ref(v___y_3151_);
lean_dec(v___y_3150_);
lean_dec_ref(v___y_3149_);
lean_dec_ref(v_as_3145_);
lean_dec_ref(v_snd_3144_);
return v_res_3156_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7(lean_object* v_snd_3157_, lean_object* v_as_3158_, size_t v_sz_3159_, size_t v_i_3160_, lean_object* v_b_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_){
_start:
{
uint8_t v___x_3167_; 
v___x_3167_ = lean_usize_dec_lt(v_i_3160_, v_sz_3159_);
if (v___x_3167_ == 0)
{
lean_object* v___x_3168_; 
v___x_3168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3168_, 0, v_b_3161_);
return v___x_3168_;
}
else
{
lean_object* v_a_3169_; lean_object* v_indGroupInst_3170_; lean_object* v_params_3171_; lean_object* v___x_3172_; size_t v_sz_3173_; size_t v___x_3174_; lean_object* v___x_3175_; 
v_a_3169_ = lean_array_uget_borrowed(v_as_3158_, v_i_3160_);
v_indGroupInst_3170_ = lean_ctor_get(v_a_3169_, 4);
v_params_3171_ = lean_ctor_get(v_indGroupInst_3170_, 2);
v___x_3172_ = lean_box(0);
v_sz_3173_ = lean_array_size(v_params_3171_);
v___x_3174_ = ((size_t)0ULL);
v___x_3175_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6(v_snd_3157_, v_params_3171_, v_sz_3173_, v___x_3174_, v___x_3172_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_);
if (lean_obj_tag(v___x_3175_) == 0)
{
size_t v___x_3176_; size_t v___x_3177_; 
lean_dec_ref_known(v___x_3175_, 1);
v___x_3176_ = ((size_t)1ULL);
v___x_3177_ = lean_usize_add(v_i_3160_, v___x_3176_);
v_i_3160_ = v___x_3177_;
v_b_3161_ = v___x_3172_;
goto _start;
}
else
{
return v___x_3175_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7___boxed(lean_object* v_snd_3179_, lean_object* v_as_3180_, lean_object* v_sz_3181_, lean_object* v_i_3182_, lean_object* v_b_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_){
_start:
{
size_t v_sz_boxed_3189_; size_t v_i_boxed_3190_; lean_object* v_res_3191_; 
v_sz_boxed_3189_ = lean_unbox_usize(v_sz_3181_);
lean_dec(v_sz_3181_);
v_i_boxed_3190_ = lean_unbox_usize(v_i_3182_);
lean_dec(v_i_3182_);
v_res_3191_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7(v_snd_3179_, v_as_3180_, v_sz_boxed_3189_, v_i_boxed_3190_, v_b_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_);
lean_dec(v___y_3187_);
lean_dec_ref(v___y_3186_);
lean_dec(v___y_3185_);
lean_dec_ref(v___y_3184_);
lean_dec_ref(v_as_3180_);
lean_dec_ref(v_snd_3179_);
return v_res_3191_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__3___redArg(lean_object* v_fst_3192_, size_t v_sz_3193_, size_t v_i_3194_, lean_object* v_bs_3195_){
_start:
{
uint8_t v___x_3196_; 
v___x_3196_ = lean_usize_dec_lt(v_i_3194_, v_sz_3193_);
if (v___x_3196_ == 0)
{
return v_bs_3195_;
}
else
{
lean_object* v_v_3197_; lean_object* v_fnName_3198_; lean_object* v_recArgPos_3199_; lean_object* v_indicesPos_3200_; lean_object* v_indGroupInst_3201_; lean_object* v_indIdx_3202_; lean_object* v___x_3204_; uint8_t v_isShared_3205_; uint8_t v_isSharedCheck_3219_; 
v_v_3197_ = lean_array_uget(v_bs_3195_, v_i_3194_);
v_fnName_3198_ = lean_ctor_get(v_v_3197_, 0);
v_recArgPos_3199_ = lean_ctor_get(v_v_3197_, 2);
v_indicesPos_3200_ = lean_ctor_get(v_v_3197_, 3);
v_indGroupInst_3201_ = lean_ctor_get(v_v_3197_, 4);
v_indIdx_3202_ = lean_ctor_get(v_v_3197_, 5);
v_isSharedCheck_3219_ = !lean_is_exclusive(v_v_3197_);
if (v_isSharedCheck_3219_ == 0)
{
lean_object* v_unused_3220_; 
v_unused_3220_ = lean_ctor_get(v_v_3197_, 1);
lean_dec(v_unused_3220_);
v___x_3204_ = v_v_3197_;
v_isShared_3205_ = v_isSharedCheck_3219_;
goto v_resetjp_3203_;
}
else
{
lean_inc(v_indIdx_3202_);
lean_inc(v_indGroupInst_3201_);
lean_inc(v_indicesPos_3200_);
lean_inc(v_recArgPos_3199_);
lean_inc(v_fnName_3198_);
lean_dec(v_v_3197_);
v___x_3204_ = lean_box(0);
v_isShared_3205_ = v_isSharedCheck_3219_;
goto v_resetjp_3203_;
}
v_resetjp_3203_:
{
lean_object* v_perms_3206_; lean_object* v___x_3207_; lean_object* v_bs_x27_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3213_; 
v_perms_3206_ = lean_ctor_get(v_fst_3192_, 1);
v___x_3207_ = lean_unsigned_to_nat(0u);
v_bs_x27_3208_ = lean_array_uset(v_bs_3195_, v_i_3194_, v___x_3207_);
v___x_3209_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0);
v___x_3210_ = lean_usize_to_nat(v_i_3194_);
v___x_3211_ = lean_array_get_borrowed(v___x_3209_, v_perms_3206_, v___x_3210_);
lean_dec(v___x_3210_);
lean_inc(v___x_3211_);
if (v_isShared_3205_ == 0)
{
lean_ctor_set(v___x_3204_, 1, v___x_3211_);
v___x_3213_ = v___x_3204_;
goto v_reusejp_3212_;
}
else
{
lean_object* v_reuseFailAlloc_3218_; 
v_reuseFailAlloc_3218_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3218_, 0, v_fnName_3198_);
lean_ctor_set(v_reuseFailAlloc_3218_, 1, v___x_3211_);
lean_ctor_set(v_reuseFailAlloc_3218_, 2, v_recArgPos_3199_);
lean_ctor_set(v_reuseFailAlloc_3218_, 3, v_indicesPos_3200_);
lean_ctor_set(v_reuseFailAlloc_3218_, 4, v_indGroupInst_3201_);
lean_ctor_set(v_reuseFailAlloc_3218_, 5, v_indIdx_3202_);
v___x_3213_ = v_reuseFailAlloc_3218_;
goto v_reusejp_3212_;
}
v_reusejp_3212_:
{
size_t v___x_3214_; size_t v___x_3215_; lean_object* v___x_3216_; 
v___x_3214_ = ((size_t)1ULL);
v___x_3215_ = lean_usize_add(v_i_3194_, v___x_3214_);
v___x_3216_ = lean_array_uset(v_bs_x27_3208_, v_i_3194_, v___x_3213_);
v_i_3194_ = v___x_3215_;
v_bs_3195_ = v___x_3216_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__3___redArg___boxed(lean_object* v_fst_3221_, lean_object* v_sz_3222_, lean_object* v_i_3223_, lean_object* v_bs_3224_){
_start:
{
size_t v_sz_boxed_3225_; size_t v_i_boxed_3226_; lean_object* v_res_3227_; 
v_sz_boxed_3225_ = lean_unbox_usize(v_sz_3222_);
lean_dec(v_sz_3222_);
v_i_boxed_3226_ = lean_unbox_usize(v_i_3223_);
lean_dec(v_i_3223_);
v_res_3227_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__3___redArg(v_fst_3221_, v_sz_boxed_3225_, v_i_boxed_3226_, v_bs_3224_);
lean_dec_ref(v_fst_3221_);
return v_res_3227_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__13_spec__16_spec__20(lean_object* v_x_3228_, lean_object* v_x_3229_, lean_object* v_x_3230_){
_start:
{
if (lean_obj_tag(v_x_3230_) == 0)
{
lean_dec(v_x_3228_);
return v_x_3229_;
}
else
{
lean_object* v_head_3231_; lean_object* v_tail_3232_; lean_object* v___x_3234_; uint8_t v_isShared_3235_; uint8_t v_isSharedCheck_3242_; 
v_head_3231_ = lean_ctor_get(v_x_3230_, 0);
v_tail_3232_ = lean_ctor_get(v_x_3230_, 1);
v_isSharedCheck_3242_ = !lean_is_exclusive(v_x_3230_);
if (v_isSharedCheck_3242_ == 0)
{
v___x_3234_ = v_x_3230_;
v_isShared_3235_ = v_isSharedCheck_3242_;
goto v_resetjp_3233_;
}
else
{
lean_inc(v_tail_3232_);
lean_inc(v_head_3231_);
lean_dec(v_x_3230_);
v___x_3234_ = lean_box(0);
v_isShared_3235_ = v_isSharedCheck_3242_;
goto v_resetjp_3233_;
}
v_resetjp_3233_:
{
lean_object* v___x_3237_; 
lean_inc(v_x_3228_);
if (v_isShared_3235_ == 0)
{
lean_ctor_set_tag(v___x_3234_, 5);
lean_ctor_set(v___x_3234_, 1, v_x_3228_);
lean_ctor_set(v___x_3234_, 0, v_x_3229_);
v___x_3237_ = v___x_3234_;
goto v_reusejp_3236_;
}
else
{
lean_object* v_reuseFailAlloc_3241_; 
v_reuseFailAlloc_3241_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3241_, 0, v_x_3229_);
lean_ctor_set(v_reuseFailAlloc_3241_, 1, v_x_3228_);
v___x_3237_ = v_reuseFailAlloc_3241_;
goto v_reusejp_3236_;
}
v_reusejp_3236_:
{
lean_object* v___x_3238_; lean_object* v___x_3239_; 
v___x_3238_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(v_head_3231_);
v___x_3239_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3239_, 0, v___x_3237_);
lean_ctor_set(v___x_3239_, 1, v___x_3238_);
v_x_3229_ = v___x_3239_;
v_x_3230_ = v_tail_3232_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__13_spec__16(lean_object* v_x_3243_, lean_object* v_x_3244_, lean_object* v_x_3245_){
_start:
{
if (lean_obj_tag(v_x_3245_) == 0)
{
lean_dec(v_x_3243_);
return v_x_3244_;
}
else
{
lean_object* v_head_3246_; lean_object* v_tail_3247_; lean_object* v___x_3249_; uint8_t v_isShared_3250_; uint8_t v_isSharedCheck_3257_; 
v_head_3246_ = lean_ctor_get(v_x_3245_, 0);
v_tail_3247_ = lean_ctor_get(v_x_3245_, 1);
v_isSharedCheck_3257_ = !lean_is_exclusive(v_x_3245_);
if (v_isSharedCheck_3257_ == 0)
{
v___x_3249_ = v_x_3245_;
v_isShared_3250_ = v_isSharedCheck_3257_;
goto v_resetjp_3248_;
}
else
{
lean_inc(v_tail_3247_);
lean_inc(v_head_3246_);
lean_dec(v_x_3245_);
v___x_3249_ = lean_box(0);
v_isShared_3250_ = v_isSharedCheck_3257_;
goto v_resetjp_3248_;
}
v_resetjp_3248_:
{
lean_object* v___x_3252_; 
lean_inc(v_x_3243_);
if (v_isShared_3250_ == 0)
{
lean_ctor_set_tag(v___x_3249_, 5);
lean_ctor_set(v___x_3249_, 1, v_x_3243_);
lean_ctor_set(v___x_3249_, 0, v_x_3244_);
v___x_3252_ = v___x_3249_;
goto v_reusejp_3251_;
}
else
{
lean_object* v_reuseFailAlloc_3256_; 
v_reuseFailAlloc_3256_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3256_, 0, v_x_3244_);
lean_ctor_set(v_reuseFailAlloc_3256_, 1, v_x_3243_);
v___x_3252_ = v_reuseFailAlloc_3256_;
goto v_reusejp_3251_;
}
v_reusejp_3251_:
{
lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; 
v___x_3253_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(v_head_3246_);
v___x_3254_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3254_, 0, v___x_3252_);
lean_ctor_set(v___x_3254_, 1, v___x_3253_);
v___x_3255_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__13_spec__16_spec__20(v_x_3243_, v___x_3254_, v_tail_3247_);
return v___x_3255_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__13(lean_object* v_x_3258_, lean_object* v_x_3259_){
_start:
{
if (lean_obj_tag(v_x_3258_) == 0)
{
lean_object* v___x_3260_; 
lean_dec(v_x_3259_);
v___x_3260_ = lean_box(0);
return v___x_3260_;
}
else
{
lean_object* v_tail_3261_; 
v_tail_3261_ = lean_ctor_get(v_x_3258_, 1);
if (lean_obj_tag(v_tail_3261_) == 0)
{
lean_object* v_head_3262_; lean_object* v___x_3263_; 
lean_dec(v_x_3259_);
v_head_3262_ = lean_ctor_get(v_x_3258_, 0);
lean_inc(v_head_3262_);
lean_dec_ref_known(v_x_3258_, 2);
v___x_3263_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(v_head_3262_);
return v___x_3263_;
}
else
{
lean_object* v_head_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; 
lean_inc(v_tail_3261_);
v_head_3264_ = lean_ctor_get(v_x_3258_, 0);
lean_inc(v_head_3264_);
lean_dec_ref_known(v_x_3258_, 2);
v___x_3265_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(v_head_3264_);
v___x_3266_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__13_spec__16(v_x_3259_, v___x_3265_, v_tail_3261_);
return v___x_3266_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___closed__5(void){
_start:
{
lean_object* v___x_3275_; lean_object* v___x_3276_; 
v___x_3275_ = ((lean_object*)(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___closed__0));
v___x_3276_ = lean_string_length(v___x_3275_);
return v___x_3276_;
}
}
static lean_object* _init_l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___closed__6(void){
_start:
{
lean_object* v___x_3277_; lean_object* v___x_3278_; 
v___x_3277_ = lean_obj_once(&l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___closed__5, &l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___closed__5_once, _init_l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___closed__5);
v___x_3278_ = lean_nat_to_int(v___x_3277_);
return v___x_3278_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9(lean_object* v_xs_3286_){
_start:
{
lean_object* v___x_3287_; lean_object* v___x_3288_; uint8_t v___x_3289_; 
v___x_3287_ = lean_array_get_size(v_xs_3286_);
v___x_3288_ = lean_unsigned_to_nat(0u);
v___x_3289_ = lean_nat_dec_eq(v___x_3287_, v___x_3288_);
if (v___x_3289_ == 0)
{
lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; 
v___x_3290_ = lean_array_to_list(v_xs_3286_);
v___x_3291_ = ((lean_object*)(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___closed__3));
v___x_3292_ = l_Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__13(v___x_3290_, v___x_3291_);
v___x_3293_ = lean_obj_once(&l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___closed__6, &l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___closed__6_once, _init_l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___closed__6);
v___x_3294_ = ((lean_object*)(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___closed__7));
v___x_3295_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3295_, 0, v___x_3294_);
lean_ctor_set(v___x_3295_, 1, v___x_3292_);
v___x_3296_ = ((lean_object*)(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___closed__8));
v___x_3297_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3297_, 0, v___x_3295_);
lean_ctor_set(v___x_3297_, 1, v___x_3296_);
v___x_3298_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3298_, 0, v___x_3293_);
lean_ctor_set(v___x_3298_, 1, v___x_3297_);
v___x_3299_ = l_Std_Format_fill(v___x_3298_);
return v___x_3299_;
}
else
{
lean_object* v___x_3300_; 
lean_dec_ref(v_xs_3286_);
v___x_3300_ = ((lean_object*)(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___closed__10));
return v___x_3300_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10(size_t v_sz_3301_, size_t v_i_3302_, lean_object* v_bs_3303_){
_start:
{
uint8_t v___x_3304_; 
v___x_3304_ = lean_usize_dec_lt(v_i_3302_, v_sz_3301_);
if (v___x_3304_ == 0)
{
return v_bs_3303_;
}
else
{
lean_object* v_v_3305_; lean_object* v___x_3306_; lean_object* v_bs_x27_3307_; lean_object* v___x_3308_; size_t v___x_3309_; size_t v___x_3310_; lean_object* v___x_3311_; 
v_v_3305_ = lean_array_uget(v_bs_3303_, v_i_3302_);
v___x_3306_ = lean_unsigned_to_nat(0u);
v_bs_x27_3307_ = lean_array_uset(v_bs_3303_, v_i_3302_, v___x_3306_);
v___x_3308_ = l_Lean_mkFVar(v_v_3305_);
v___x_3309_ = ((size_t)1ULL);
v___x_3310_ = lean_usize_add(v_i_3302_, v___x_3309_);
v___x_3311_ = lean_array_uset(v_bs_x27_3307_, v_i_3302_, v___x_3308_);
v_i_3302_ = v___x_3310_;
v_bs_3303_ = v___x_3311_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___boxed(lean_object* v_sz_3313_, lean_object* v_i_3314_, lean_object* v_bs_3315_){
_start:
{
size_t v_sz_boxed_3316_; size_t v_i_boxed_3317_; lean_object* v_res_3318_; 
v_sz_boxed_3316_ = lean_unbox_usize(v_sz_3313_);
lean_dec(v_sz_3313_);
v_i_boxed_3317_ = lean_unbox_usize(v_i_3314_);
lean_dec(v_i_3314_);
v_res_3318_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10(v_sz_boxed_3316_, v_i_boxed_3317_, v_bs_3315_);
return v_res_3318_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__2(size_t v_sz_3319_, size_t v_i_3320_, lean_object* v_bs_3321_){
_start:
{
uint8_t v___x_3322_; 
v___x_3322_ = lean_usize_dec_lt(v_i_3320_, v_sz_3319_);
if (v___x_3322_ == 0)
{
return v_bs_3321_;
}
else
{
lean_object* v_v_3323_; lean_object* v___x_3324_; lean_object* v_bs_x27_3325_; lean_object* v___x_3326_; size_t v___x_3327_; size_t v___x_3328_; lean_object* v___x_3329_; 
v_v_3323_ = lean_array_uget(v_bs_3321_, v_i_3320_);
v___x_3324_ = lean_unsigned_to_nat(0u);
v_bs_x27_3325_ = lean_array_uset(v_bs_3321_, v_i_3320_, v___x_3324_);
v___x_3326_ = l_Lean_Elab_Structural_RecArgInfo_indicesAndRecArgPos(v_v_3323_);
v___x_3327_ = ((size_t)1ULL);
v___x_3328_ = lean_usize_add(v_i_3320_, v___x_3327_);
v___x_3329_ = lean_array_uset(v_bs_x27_3325_, v_i_3320_, v___x_3326_);
v_i_3320_ = v___x_3328_;
v_bs_3321_ = v___x_3329_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__2___boxed(lean_object* v_sz_3331_, lean_object* v_i_3332_, lean_object* v_bs_3333_){
_start:
{
size_t v_sz_boxed_3334_; size_t v_i_boxed_3335_; lean_object* v_res_3336_; 
v_sz_boxed_3334_ = lean_unbox_usize(v_sz_3331_);
lean_dec(v_sz_3331_);
v_i_boxed_3335_ = lean_unbox_usize(v_i_3332_);
lean_dec(v_i_3332_);
v_res_3336_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__2(v_sz_boxed_3334_, v_i_boxed_3335_, v_bs_3333_);
return v_res_3336_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__0(void){
_start:
{
lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; 
v___x_3337_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__5));
v___x_3338_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___closed__1));
v___x_3339_ = l_Lean_Name_append(v___x_3338_, v___x_3337_);
return v___x_3339_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3341_; lean_object* v___x_3342_; 
v___x_3341_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__1));
v___x_3342_ = l_Lean_stringToMessageData(v___x_3341_);
return v___x_3342_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__4(void){
_start:
{
lean_object* v___x_3344_; lean_object* v___x_3345_; 
v___x_3344_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__3));
v___x_3345_ = l_Lean_stringToMessageData(v___x_3344_);
return v___x_3345_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__6(void){
_start:
{
lean_object* v___x_3347_; lean_object* v___x_3348_; 
v___x_3347_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__5));
v___x_3348_ = l_Lean_stringToMessageData(v___x_3347_);
return v___x_3348_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__8(void){
_start:
{
lean_object* v___x_3350_; lean_object* v___x_3351_; 
v___x_3350_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__7));
v___x_3351_ = l_Lean_stringToMessageData(v___x_3350_);
return v___x_3351_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__10(void){
_start:
{
lean_object* v___x_3353_; lean_object* v___x_3354_; 
v___x_3353_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__9));
v___x_3354_ = l_Lean_stringToMessageData(v___x_3353_);
return v___x_3354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0(size_t v___x_3355_, lean_object* v_a_3356_, lean_object* v_xs_3357_, lean_object* v_a_3358_, lean_object* v_recArgInfos_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_){
_start:
{
lean_object* v___y_3366_; lean_object* v___y_3367_; lean_object* v___y_3368_; lean_object* v___y_3369_; lean_object* v___y_3370_; lean_object* v___y_3371_; lean_object* v___y_3372_; size_t v_sz_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___y_3389_; lean_object* v___y_3390_; lean_object* v___y_3391_; lean_object* v___y_3392_; lean_object* v___y_3393_; lean_object* v___y_3394_; lean_object* v___y_3395_; lean_object* v___x_3472_; lean_object* v_a_3473_; uint8_t v___x_3474_; 
v_sz_3385_ = lean_array_size(v_recArgInfos_3359_);
lean_inc_ref(v_recArgInfos_3359_);
v___x_3386_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1(v_sz_3385_, v___x_3355_, v_recArgInfos_3359_);
v___x_3387_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__5));
v___x_3472_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1(v___x_3387_, v___y_3360_, v___y_3361_, v___y_3362_, v___y_3363_);
v_a_3473_ = lean_ctor_get(v___x_3472_, 0);
lean_inc(v_a_3473_);
lean_dec_ref(v___x_3472_);
v___x_3474_ = lean_unbox(v_a_3473_);
lean_dec(v_a_3473_);
if (v___x_3474_ == 0)
{
goto v___jp_3415_;
}
else
{
lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; 
v___x_3475_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__10, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__10);
lean_inc_ref(v___x_3386_);
v___x_3476_ = lean_array_to_list(v___x_3386_);
v___x_3477_ = lean_box(0);
v___x_3478_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__0(v___x_3476_, v___x_3477_);
v___x_3479_ = l_Lean_MessageData_ofList(v___x_3478_);
v___x_3480_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3480_, 0, v___x_3475_);
lean_ctor_set(v___x_3480_, 1, v___x_3479_);
v___x_3481_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_3387_, v___x_3480_, v___y_3360_, v___y_3361_, v___y_3362_, v___y_3363_);
if (lean_obj_tag(v___x_3481_) == 0)
{
lean_dec_ref_known(v___x_3481_, 1);
goto v___jp_3415_;
}
else
{
lean_object* v_a_3482_; lean_object* v___x_3484_; uint8_t v_isShared_3485_; uint8_t v_isSharedCheck_3489_; 
lean_dec_ref(v___x_3386_);
lean_dec_ref(v_recArgInfos_3359_);
lean_dec_ref(v_a_3358_);
lean_dec_ref(v_xs_3357_);
lean_dec_ref(v_a_3356_);
v_a_3482_ = lean_ctor_get(v___x_3481_, 0);
v_isSharedCheck_3489_ = !lean_is_exclusive(v___x_3481_);
if (v_isSharedCheck_3489_ == 0)
{
v___x_3484_ = v___x_3481_;
v_isShared_3485_ = v_isSharedCheck_3489_;
goto v_resetjp_3483_;
}
else
{
lean_inc(v_a_3482_);
lean_dec(v___x_3481_);
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
v___jp_3365_:
{
lean_object* v___x_3373_; size_t v_sz_3374_; lean_object* v___x_3375_; 
v___x_3373_ = lean_box(0);
v_sz_3374_ = lean_array_size(v___y_3368_);
v___x_3375_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7(v___y_3367_, v___y_3368_, v_sz_3374_, v___x_3355_, v___x_3373_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_);
lean_dec_ref(v___y_3368_);
if (lean_obj_tag(v___x_3375_) == 0)
{
lean_object* v___x_3376_; 
lean_dec_ref_known(v___x_3375_, 1);
v___x_3376_ = l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8___redArg(v___y_3367_, v___y_3366_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_);
lean_dec_ref(v___y_3367_);
return v___x_3376_;
}
else
{
lean_object* v_a_3377_; lean_object* v___x_3379_; uint8_t v_isShared_3380_; uint8_t v_isSharedCheck_3384_; 
lean_dec_ref(v___y_3367_);
lean_dec_ref(v___y_3366_);
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
v___jp_3388_:
{
lean_object* v_toCold_3396_; lean_object* v_options_3397_; uint8_t v_hasTrace_3398_; 
v_toCold_3396_ = lean_ctor_get(v___y_3394_, 0);
v_options_3397_ = lean_ctor_get(v_toCold_3396_, 2);
v_hasTrace_3398_ = lean_ctor_get_uint8(v_options_3397_, sizeof(void*)*1);
if (v_hasTrace_3398_ == 0)
{
v___y_3366_ = v___y_3389_;
v___y_3367_ = v___y_3390_;
v___y_3368_ = v___y_3391_;
v___y_3369_ = v___y_3392_;
v___y_3370_ = v___y_3393_;
v___y_3371_ = v___y_3394_;
v___y_3372_ = v___y_3395_;
goto v___jp_3365_;
}
else
{
lean_object* v_inheritedTraceOptions_3399_; lean_object* v___x_3400_; uint8_t v___x_3401_; 
v_inheritedTraceOptions_3399_ = lean_ctor_get(v_toCold_3396_, 11);
v___x_3400_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__0);
v___x_3401_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3399_, v_options_3397_, v___x_3400_);
if (v___x_3401_ == 0)
{
v___y_3366_ = v___y_3389_;
v___y_3367_ = v___y_3390_;
v___y_3368_ = v___y_3391_;
v___y_3369_ = v___y_3392_;
v___y_3370_ = v___y_3393_;
v___y_3371_ = v___y_3394_;
v___y_3372_ = v___y_3395_;
goto v___jp_3365_;
}
else
{
lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; 
v___x_3402_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__2);
lean_inc_ref(v___y_3391_);
v___x_3403_ = l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9(v___y_3391_);
v___x_3404_ = l_Lean_MessageData_ofFormat(v___x_3403_);
v___x_3405_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3405_, 0, v___x_3402_);
lean_ctor_set(v___x_3405_, 1, v___x_3404_);
v___x_3406_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_3387_, v___x_3405_, v___y_3392_, v___y_3393_, v___y_3394_, v___y_3395_);
if (lean_obj_tag(v___x_3406_) == 0)
{
lean_dec_ref_known(v___x_3406_, 1);
v___y_3366_ = v___y_3389_;
v___y_3367_ = v___y_3390_;
v___y_3368_ = v___y_3391_;
v___y_3369_ = v___y_3392_;
v___y_3370_ = v___y_3393_;
v___y_3371_ = v___y_3394_;
v___y_3372_ = v___y_3395_;
goto v___jp_3365_;
}
else
{
lean_object* v_a_3407_; lean_object* v___x_3409_; uint8_t v_isShared_3410_; uint8_t v_isSharedCheck_3414_; 
lean_dec_ref(v___y_3391_);
lean_dec_ref(v___y_3390_);
lean_dec_ref(v___y_3389_);
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
v___jp_3415_:
{
lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v_snd_3418_; lean_object* v_fst_3419_; lean_object* v___x_3421_; uint8_t v_isShared_3422_; uint8_t v_isSharedCheck_3471_; 
lean_inc_ref(v_recArgInfos_3359_);
v___x_3416_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__2(v_sz_3385_, v___x_3355_, v_recArgInfos_3359_);
lean_inc_ref(v_xs_3357_);
v___x_3417_ = l_Lean_Elab_FixedParamPerms_erase(v_a_3356_, v_xs_3357_, v___x_3416_);
v_snd_3418_ = lean_ctor_get(v___x_3417_, 1);
v_fst_3419_ = lean_ctor_get(v___x_3417_, 0);
v_isSharedCheck_3471_ = !lean_is_exclusive(v___x_3417_);
if (v_isSharedCheck_3471_ == 0)
{
v___x_3421_ = v___x_3417_;
v_isShared_3422_ = v_isSharedCheck_3471_;
goto v_resetjp_3420_;
}
else
{
lean_inc(v_snd_3418_);
lean_inc(v_fst_3419_);
lean_dec(v___x_3417_);
v___x_3421_ = lean_box(0);
v_isShared_3422_ = v_isSharedCheck_3471_;
goto v_resetjp_3420_;
}
v_resetjp_3420_:
{
lean_object* v_fst_3423_; lean_object* v_snd_3424_; lean_object* v___x_3426_; uint8_t v_isShared_3427_; uint8_t v_isSharedCheck_3470_; 
v_fst_3423_ = lean_ctor_get(v_snd_3418_, 0);
v_snd_3424_ = lean_ctor_get(v_snd_3418_, 1);
v_isSharedCheck_3470_ = !lean_is_exclusive(v_snd_3418_);
if (v_isSharedCheck_3470_ == 0)
{
v___x_3426_ = v_snd_3418_;
v_isShared_3427_ = v_isSharedCheck_3470_;
goto v_resetjp_3425_;
}
else
{
lean_inc(v_snd_3424_);
lean_inc(v_fst_3423_);
lean_dec(v_snd_3418_);
v___x_3426_ = lean_box(0);
v_isShared_3427_ = v_isSharedCheck_3470_;
goto v_resetjp_3425_;
}
v_resetjp_3425_:
{
lean_object* v___x_3428_; lean_object* v___f_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; uint8_t v___x_3432_; 
v___x_3428_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__3___redArg(v_fst_3419_, v_sz_3385_, v___x_3355_, v_recArgInfos_3359_);
lean_inc_ref(v___x_3428_);
lean_inc(v_fst_3423_);
v___f_3429_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___boxed), 10, 5);
lean_closure_set(v___f_3429_, 0, v_a_3358_);
lean_closure_set(v___f_3429_, 1, v_fst_3419_);
lean_closure_set(v___f_3429_, 2, v_fst_3423_);
lean_closure_set(v___f_3429_, 3, v___x_3428_);
lean_closure_set(v___f_3429_, 4, v___x_3386_);
v___x_3430_ = lean_array_get_size(v_fst_3423_);
v___x_3431_ = lean_array_get_size(v_xs_3357_);
v___x_3432_ = lean_nat_dec_eq(v___x_3430_, v___x_3431_);
if (v___x_3432_ == 0)
{
lean_object* v___x_3433_; lean_object* v_a_3434_; uint8_t v___x_3435_; 
v___x_3433_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1(v___x_3387_, v___y_3360_, v___y_3361_, v___y_3362_, v___y_3363_);
v_a_3434_ = lean_ctor_get(v___x_3433_, 0);
lean_inc(v_a_3434_);
lean_dec_ref(v___x_3433_);
v___x_3435_ = lean_unbox(v_a_3434_);
lean_dec(v_a_3434_);
if (v___x_3435_ == 0)
{
lean_del_object(v___x_3426_);
lean_dec(v_fst_3423_);
lean_del_object(v___x_3421_);
lean_dec_ref(v_xs_3357_);
v___y_3389_ = v___f_3429_;
v___y_3390_ = v_snd_3424_;
v___y_3391_ = v___x_3428_;
v___y_3392_ = v___y_3360_;
v___y_3393_ = v___y_3361_;
v___y_3394_ = v___y_3362_;
v___y_3395_ = v___y_3363_;
goto v___jp_3388_;
}
else
{
lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3442_; 
v___x_3436_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__4);
v___x_3437_ = lean_array_to_list(v_xs_3357_);
v___x_3438_ = lean_box(0);
v___x_3439_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_3437_, v___x_3438_);
v___x_3440_ = l_Lean_MessageData_ofList(v___x_3439_);
if (v_isShared_3427_ == 0)
{
lean_ctor_set_tag(v___x_3426_, 7);
lean_ctor_set(v___x_3426_, 1, v___x_3440_);
lean_ctor_set(v___x_3426_, 0, v___x_3436_);
v___x_3442_ = v___x_3426_;
goto v_reusejp_3441_;
}
else
{
lean_object* v_reuseFailAlloc_3468_; 
v_reuseFailAlloc_3468_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3468_, 0, v___x_3436_);
lean_ctor_set(v_reuseFailAlloc_3468_, 1, v___x_3440_);
v___x_3442_ = v_reuseFailAlloc_3468_;
goto v_reusejp_3441_;
}
v_reusejp_3441_:
{
lean_object* v___x_3443_; lean_object* v___x_3445_; 
v___x_3443_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__6, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__6);
if (v_isShared_3422_ == 0)
{
lean_ctor_set_tag(v___x_3421_, 7);
lean_ctor_set(v___x_3421_, 1, v___x_3443_);
lean_ctor_set(v___x_3421_, 0, v___x_3442_);
v___x_3445_ = v___x_3421_;
goto v_reusejp_3444_;
}
else
{
lean_object* v_reuseFailAlloc_3467_; 
v_reuseFailAlloc_3467_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3467_, 0, v___x_3442_);
lean_ctor_set(v_reuseFailAlloc_3467_, 1, v___x_3443_);
v___x_3445_ = v_reuseFailAlloc_3467_;
goto v_reusejp_3444_;
}
v_reusejp_3444_:
{
lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; size_t v_sz_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; 
v___x_3446_ = lean_array_to_list(v_fst_3423_);
v___x_3447_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_3446_, v___x_3438_);
v___x_3448_ = l_Lean_MessageData_ofList(v___x_3447_);
v___x_3449_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3449_, 0, v___x_3445_);
lean_ctor_set(v___x_3449_, 1, v___x_3448_);
v___x_3450_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__8);
v___x_3451_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3451_, 0, v___x_3449_);
lean_ctor_set(v___x_3451_, 1, v___x_3450_);
v_sz_3452_ = lean_array_size(v_snd_3424_);
lean_inc(v_snd_3424_);
v___x_3453_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10(v_sz_3452_, v___x_3355_, v_snd_3424_);
v___x_3454_ = lean_array_to_list(v___x_3453_);
v___x_3455_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_3454_, v___x_3438_);
v___x_3456_ = l_Lean_MessageData_ofList(v___x_3455_);
v___x_3457_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3457_, 0, v___x_3451_);
lean_ctor_set(v___x_3457_, 1, v___x_3456_);
v___x_3458_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_3387_, v___x_3457_, v___y_3360_, v___y_3361_, v___y_3362_, v___y_3363_);
if (lean_obj_tag(v___x_3458_) == 0)
{
lean_dec_ref_known(v___x_3458_, 1);
v___y_3389_ = v___f_3429_;
v___y_3390_ = v_snd_3424_;
v___y_3391_ = v___x_3428_;
v___y_3392_ = v___y_3360_;
v___y_3393_ = v___y_3361_;
v___y_3394_ = v___y_3362_;
v___y_3395_ = v___y_3363_;
goto v___jp_3388_;
}
else
{
lean_object* v_a_3459_; lean_object* v___x_3461_; uint8_t v_isShared_3462_; uint8_t v_isSharedCheck_3466_; 
lean_dec_ref(v___f_3429_);
lean_dec_ref(v___x_3428_);
lean_dec(v_snd_3424_);
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
}
}
}
else
{
lean_object* v___x_3469_; 
lean_dec_ref(v___x_3428_);
lean_del_object(v___x_3426_);
lean_dec(v_fst_3423_);
lean_del_object(v___x_3421_);
lean_dec_ref(v_xs_3357_);
v___x_3469_ = l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8___redArg(v_snd_3424_, v___f_3429_, v___y_3360_, v___y_3361_, v___y_3362_, v___y_3363_);
lean_dec(v_snd_3424_);
return v___x_3469_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___boxed(lean_object* v___x_3490_, lean_object* v_a_3491_, lean_object* v_xs_3492_, lean_object* v_a_3493_, lean_object* v_recArgInfos_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_){
_start:
{
size_t v___x_12976__boxed_3500_; lean_object* v_res_3501_; 
v___x_12976__boxed_3500_ = lean_unbox_usize(v___x_3490_);
lean_dec(v___x_3490_);
v_res_3501_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0(v___x_12976__boxed_3500_, v_a_3491_, v_xs_3492_, v_a_3493_, v_recArgInfos_3494_, v___y_3495_, v___y_3496_, v___y_3497_, v___y_3498_);
lean_dec(v___y_3498_);
lean_dec_ref(v___y_3497_);
lean_dec(v___y_3496_);
lean_dec_ref(v___y_3495_);
return v_res_3501_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__11___redArg(lean_object* v___x_3502_, lean_object* v_xs_3503_, size_t v_sz_3504_, size_t v_i_3505_, lean_object* v_bs_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_){
_start:
{
uint8_t v___x_3512_; 
v___x_3512_ = lean_usize_dec_lt(v_i_3505_, v_sz_3504_);
if (v___x_3512_ == 0)
{
lean_object* v___x_3513_; 
lean_dec_ref(v_xs_3503_);
v___x_3513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3513_, 0, v_bs_3506_);
return v___x_3513_;
}
else
{
lean_object* v_v_3514_; lean_object* v_value_3515_; lean_object* v___x_3516_; lean_object* v_bs_x27_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; 
v_v_3514_ = lean_array_uget_borrowed(v_bs_3506_, v_i_3505_);
v_value_3515_ = lean_ctor_get(v_v_3514_, 7);
lean_inc_ref(v_value_3515_);
v___x_3516_ = lean_unsigned_to_nat(0u);
v_bs_x27_3517_ = lean_array_uset(v_bs_3506_, v_i_3505_, v___x_3516_);
v___x_3518_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0);
v___x_3519_ = lean_usize_to_nat(v_i_3505_);
v___x_3520_ = lean_array_get_borrowed(v___x_3518_, v___x_3502_, v___x_3519_);
lean_dec(v___x_3519_);
lean_inc_ref(v_xs_3503_);
lean_inc(v___x_3520_);
v___x_3521_ = l_Lean_Elab_FixedParamPerm_instantiateLambda(v___x_3520_, v_value_3515_, v_xs_3503_, v___y_3507_, v___y_3508_, v___y_3509_, v___y_3510_);
if (lean_obj_tag(v___x_3521_) == 0)
{
lean_object* v_a_3522_; size_t v___x_3523_; size_t v___x_3524_; lean_object* v___x_3525_; 
v_a_3522_ = lean_ctor_get(v___x_3521_, 0);
lean_inc(v_a_3522_);
lean_dec_ref_known(v___x_3521_, 1);
v___x_3523_ = ((size_t)1ULL);
v___x_3524_ = lean_usize_add(v_i_3505_, v___x_3523_);
v___x_3525_ = lean_array_uset(v_bs_x27_3517_, v_i_3505_, v_a_3522_);
v_i_3505_ = v___x_3524_;
v_bs_3506_ = v___x_3525_;
goto _start;
}
else
{
lean_object* v_a_3527_; lean_object* v___x_3529_; uint8_t v_isShared_3530_; uint8_t v_isSharedCheck_3534_; 
lean_dec_ref(v_bs_x27_3517_);
lean_dec_ref(v_xs_3503_);
v_a_3527_ = lean_ctor_get(v___x_3521_, 0);
v_isSharedCheck_3534_ = !lean_is_exclusive(v___x_3521_);
if (v_isSharedCheck_3534_ == 0)
{
v___x_3529_ = v___x_3521_;
v_isShared_3530_ = v_isSharedCheck_3534_;
goto v_resetjp_3528_;
}
else
{
lean_inc(v_a_3527_);
lean_dec(v___x_3521_);
v___x_3529_ = lean_box(0);
v_isShared_3530_ = v_isSharedCheck_3534_;
goto v_resetjp_3528_;
}
v_resetjp_3528_:
{
lean_object* v___x_3532_; 
if (v_isShared_3530_ == 0)
{
v___x_3532_ = v___x_3529_;
goto v_reusejp_3531_;
}
else
{
lean_object* v_reuseFailAlloc_3533_; 
v_reuseFailAlloc_3533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3533_, 0, v_a_3527_);
v___x_3532_ = v_reuseFailAlloc_3533_;
goto v_reusejp_3531_;
}
v_reusejp_3531_:
{
return v___x_3532_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__11___redArg___boxed(lean_object* v___x_3535_, lean_object* v_xs_3536_, lean_object* v_sz_3537_, lean_object* v_i_3538_, lean_object* v_bs_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_){
_start:
{
size_t v_sz_boxed_3545_; size_t v_i_boxed_3546_; lean_object* v_res_3547_; 
v_sz_boxed_3545_ = lean_unbox_usize(v_sz_3537_);
lean_dec(v_sz_3537_);
v_i_boxed_3546_ = lean_unbox_usize(v_i_3538_);
lean_dec(v_i_3538_);
v_res_3547_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__11___redArg(v___x_3535_, v_xs_3536_, v_sz_boxed_3545_, v_i_boxed_3546_, v_bs_3539_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_);
lean_dec(v___y_3543_);
lean_dec_ref(v___y_3542_);
lean_dec(v___y_3541_);
lean_dec_ref(v___y_3540_);
lean_dec_ref(v___x_3535_);
return v_res_3547_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__2(size_t v___x_3548_, lean_object* v_a_3549_, lean_object* v_a_3550_, lean_object* v_perms_3551_, lean_object* v_fnNames_3552_, lean_object* v_termMeasure_x3fs_3553_, lean_object* v_xs_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_){
_start:
{
lean_object* v___x_3560_; lean_object* v___f_3561_; size_t v_sz_3562_; lean_object* v___x_3563_; 
v___x_3560_ = lean_box_usize(v___x_3548_);
lean_inc_ref_n(v_a_3550_, 2);
lean_inc_ref_n(v_xs_3554_, 2);
lean_inc_ref(v_a_3549_);
v___f_3561_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___boxed), 10, 4);
lean_closure_set(v___f_3561_, 0, v___x_3560_);
lean_closure_set(v___f_3561_, 1, v_a_3549_);
lean_closure_set(v___f_3561_, 2, v_xs_3554_);
lean_closure_set(v___f_3561_, 3, v_a_3550_);
v_sz_3562_ = lean_array_size(v_a_3550_);
v___x_3563_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__11___redArg(v_perms_3551_, v_xs_3554_, v_sz_3562_, v___x_3548_, v_a_3550_, v___y_3555_, v___y_3556_, v___y_3557_, v___y_3558_);
if (lean_obj_tag(v___x_3563_) == 0)
{
lean_object* v_a_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; 
v_a_3564_ = lean_ctor_get(v___x_3563_, 0);
lean_inc_n(v_a_3564_, 2);
lean_dec_ref_known(v___x_3563_, 1);
lean_inc_ref(v_xs_3554_);
lean_inc_ref(v_fnNames_3552_);
v___x_3565_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_findRecArgCandidates___boxed), 10, 5);
lean_closure_set(v___x_3565_, 0, v_fnNames_3552_);
lean_closure_set(v___x_3565_, 1, v_a_3549_);
lean_closure_set(v___x_3565_, 2, v_xs_3554_);
lean_closure_set(v___x_3565_, 3, v_a_3564_);
lean_closure_set(v___x_3565_, 4, v_termMeasure_x3fs_3553_);
v___x_3566_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v_a_3550_, v___x_3565_, v___y_3555_, v___y_3556_, v___y_3557_, v___y_3558_);
if (lean_obj_tag(v___x_3566_) == 0)
{
lean_object* v_a_3567_; lean_object* v___x_3568_; 
v_a_3567_ = lean_ctor_get(v___x_3566_, 0);
lean_inc(v_a_3567_);
lean_dec_ref_known(v___x_3566_, 1);
v___x_3568_ = l_Lean_Elab_Structural_tryCandidates___redArg(v_fnNames_3552_, v_xs_3554_, v_a_3564_, v_a_3567_, v___f_3561_, v___y_3555_, v___y_3556_, v___y_3557_, v___y_3558_);
lean_dec_ref(v_fnNames_3552_);
return v___x_3568_;
}
else
{
lean_object* v_a_3569_; lean_object* v___x_3571_; uint8_t v_isShared_3572_; uint8_t v_isSharedCheck_3576_; 
lean_dec(v_a_3564_);
lean_dec_ref(v___f_3561_);
lean_dec_ref(v_xs_3554_);
lean_dec_ref(v_fnNames_3552_);
v_a_3569_ = lean_ctor_get(v___x_3566_, 0);
v_isSharedCheck_3576_ = !lean_is_exclusive(v___x_3566_);
if (v_isSharedCheck_3576_ == 0)
{
v___x_3571_ = v___x_3566_;
v_isShared_3572_ = v_isSharedCheck_3576_;
goto v_resetjp_3570_;
}
else
{
lean_inc(v_a_3569_);
lean_dec(v___x_3566_);
v___x_3571_ = lean_box(0);
v_isShared_3572_ = v_isSharedCheck_3576_;
goto v_resetjp_3570_;
}
v_resetjp_3570_:
{
lean_object* v___x_3574_; 
if (v_isShared_3572_ == 0)
{
v___x_3574_ = v___x_3571_;
goto v_reusejp_3573_;
}
else
{
lean_object* v_reuseFailAlloc_3575_; 
v_reuseFailAlloc_3575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3575_, 0, v_a_3569_);
v___x_3574_ = v_reuseFailAlloc_3575_;
goto v_reusejp_3573_;
}
v_reusejp_3573_:
{
return v___x_3574_;
}
}
}
}
else
{
lean_object* v_a_3577_; lean_object* v___x_3579_; uint8_t v_isShared_3580_; uint8_t v_isSharedCheck_3584_; 
lean_dec_ref(v___f_3561_);
lean_dec_ref(v_xs_3554_);
lean_dec_ref(v_termMeasure_x3fs_3553_);
lean_dec_ref(v_fnNames_3552_);
lean_dec_ref(v_a_3550_);
lean_dec_ref(v_a_3549_);
v_a_3577_ = lean_ctor_get(v___x_3563_, 0);
v_isSharedCheck_3584_ = !lean_is_exclusive(v___x_3563_);
if (v_isSharedCheck_3584_ == 0)
{
v___x_3579_ = v___x_3563_;
v_isShared_3580_ = v_isSharedCheck_3584_;
goto v_resetjp_3578_;
}
else
{
lean_inc(v_a_3577_);
lean_dec(v___x_3563_);
v___x_3579_ = lean_box(0);
v_isShared_3580_ = v_isSharedCheck_3584_;
goto v_resetjp_3578_;
}
v_resetjp_3578_:
{
lean_object* v___x_3582_; 
if (v_isShared_3580_ == 0)
{
v___x_3582_ = v___x_3579_;
goto v_reusejp_3581_;
}
else
{
lean_object* v_reuseFailAlloc_3583_; 
v_reuseFailAlloc_3583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3583_, 0, v_a_3577_);
v___x_3582_ = v_reuseFailAlloc_3583_;
goto v_reusejp_3581_;
}
v_reusejp_3581_:
{
return v___x_3582_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__2___boxed(lean_object* v___x_3585_, lean_object* v_a_3586_, lean_object* v_a_3587_, lean_object* v_perms_3588_, lean_object* v_fnNames_3589_, lean_object* v_termMeasure_x3fs_3590_, lean_object* v_xs_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_){
_start:
{
size_t v___x_13319__boxed_3597_; lean_object* v_res_3598_; 
v___x_13319__boxed_3597_ = lean_unbox_usize(v___x_3585_);
lean_dec(v___x_3585_);
v_res_3598_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__2(v___x_13319__boxed_3597_, v_a_3586_, v_a_3587_, v_perms_3588_, v_fnNames_3589_, v_termMeasure_x3fs_3590_, v_xs_3591_, v___y_3592_, v___y_3593_, v___y_3594_, v___y_3595_);
lean_dec(v___y_3595_);
lean_dec_ref(v___y_3594_);
lean_dec(v___y_3593_);
lean_dec_ref(v___y_3592_);
lean_dec_ref(v_perms_3588_);
return v_res_3598_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0___redArg(lean_object* v_fnNames_3599_, lean_object* v_numSectionVars_3600_, size_t v_sz_3601_, size_t v_i_3602_, lean_object* v_bs_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_){
_start:
{
uint8_t v___x_3607_; 
v___x_3607_ = lean_usize_dec_lt(v_i_3602_, v_sz_3601_);
if (v___x_3607_ == 0)
{
lean_object* v___x_3608_; 
lean_dec(v_numSectionVars_3600_);
lean_dec_ref(v_fnNames_3599_);
v___x_3608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3608_, 0, v_bs_3603_);
return v___x_3608_;
}
else
{
lean_object* v_v_3609_; lean_object* v_ref_3610_; uint8_t v_kind_3611_; lean_object* v_levelParams_3612_; lean_object* v_modifiers_3613_; lean_object* v_declName_3614_; lean_object* v_binders_3615_; lean_object* v_numSectionVars_3616_; lean_object* v_type_3617_; lean_object* v_value_3618_; lean_object* v_termination_3619_; lean_object* v___x_3621_; uint8_t v_isShared_3622_; uint8_t v_isSharedCheck_3642_; 
v_v_3609_ = lean_array_uget(v_bs_3603_, v_i_3602_);
v_ref_3610_ = lean_ctor_get(v_v_3609_, 0);
v_kind_3611_ = lean_ctor_get_uint8(v_v_3609_, sizeof(void*)*9);
v_levelParams_3612_ = lean_ctor_get(v_v_3609_, 1);
v_modifiers_3613_ = lean_ctor_get(v_v_3609_, 2);
v_declName_3614_ = lean_ctor_get(v_v_3609_, 3);
v_binders_3615_ = lean_ctor_get(v_v_3609_, 4);
v_numSectionVars_3616_ = lean_ctor_get(v_v_3609_, 5);
v_type_3617_ = lean_ctor_get(v_v_3609_, 6);
v_value_3618_ = lean_ctor_get(v_v_3609_, 7);
v_termination_3619_ = lean_ctor_get(v_v_3609_, 8);
v_isSharedCheck_3642_ = !lean_is_exclusive(v_v_3609_);
if (v_isSharedCheck_3642_ == 0)
{
v___x_3621_ = v_v_3609_;
v_isShared_3622_ = v_isSharedCheck_3642_;
goto v_resetjp_3620_;
}
else
{
lean_inc(v_termination_3619_);
lean_inc(v_value_3618_);
lean_inc(v_type_3617_);
lean_inc(v_numSectionVars_3616_);
lean_inc(v_binders_3615_);
lean_inc(v_declName_3614_);
lean_inc(v_modifiers_3613_);
lean_inc(v_levelParams_3612_);
lean_inc(v_ref_3610_);
lean_dec(v_v_3609_);
v___x_3621_ = lean_box(0);
v_isShared_3622_ = v_isSharedCheck_3642_;
goto v_resetjp_3620_;
}
v_resetjp_3620_:
{
lean_object* v___x_3623_; lean_object* v_bs_x27_3624_; lean_object* v___x_3625_; 
v___x_3623_ = lean_unsigned_to_nat(0u);
v_bs_x27_3624_ = lean_array_uset(v_bs_3603_, v_i_3602_, v___x_3623_);
lean_inc(v_numSectionVars_3600_);
lean_inc_ref(v_fnNames_3599_);
v___x_3625_ = l_Lean_Elab_Structural_preprocess(v_value_3618_, v_fnNames_3599_, v_numSectionVars_3600_, v___y_3604_, v___y_3605_);
if (lean_obj_tag(v___x_3625_) == 0)
{
lean_object* v_a_3626_; lean_object* v___x_3628_; 
v_a_3626_ = lean_ctor_get(v___x_3625_, 0);
lean_inc(v_a_3626_);
lean_dec_ref_known(v___x_3625_, 1);
if (v_isShared_3622_ == 0)
{
lean_ctor_set(v___x_3621_, 7, v_a_3626_);
v___x_3628_ = v___x_3621_;
goto v_reusejp_3627_;
}
else
{
lean_object* v_reuseFailAlloc_3633_; 
v_reuseFailAlloc_3633_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_3633_, 0, v_ref_3610_);
lean_ctor_set(v_reuseFailAlloc_3633_, 1, v_levelParams_3612_);
lean_ctor_set(v_reuseFailAlloc_3633_, 2, v_modifiers_3613_);
lean_ctor_set(v_reuseFailAlloc_3633_, 3, v_declName_3614_);
lean_ctor_set(v_reuseFailAlloc_3633_, 4, v_binders_3615_);
lean_ctor_set(v_reuseFailAlloc_3633_, 5, v_numSectionVars_3616_);
lean_ctor_set(v_reuseFailAlloc_3633_, 6, v_type_3617_);
lean_ctor_set(v_reuseFailAlloc_3633_, 7, v_a_3626_);
lean_ctor_set(v_reuseFailAlloc_3633_, 8, v_termination_3619_);
lean_ctor_set_uint8(v_reuseFailAlloc_3633_, sizeof(void*)*9, v_kind_3611_);
v___x_3628_ = v_reuseFailAlloc_3633_;
goto v_reusejp_3627_;
}
v_reusejp_3627_:
{
size_t v___x_3629_; size_t v___x_3630_; lean_object* v___x_3631_; 
v___x_3629_ = ((size_t)1ULL);
v___x_3630_ = lean_usize_add(v_i_3602_, v___x_3629_);
v___x_3631_ = lean_array_uset(v_bs_x27_3624_, v_i_3602_, v___x_3628_);
v_i_3602_ = v___x_3630_;
v_bs_3603_ = v___x_3631_;
goto _start;
}
}
else
{
lean_object* v_a_3634_; lean_object* v___x_3636_; uint8_t v_isShared_3637_; uint8_t v_isSharedCheck_3641_; 
lean_dec_ref(v_bs_x27_3624_);
lean_del_object(v___x_3621_);
lean_dec_ref(v_termination_3619_);
lean_dec_ref(v_type_3617_);
lean_dec(v_numSectionVars_3616_);
lean_dec(v_binders_3615_);
lean_dec(v_declName_3614_);
lean_dec_ref(v_modifiers_3613_);
lean_dec(v_levelParams_3612_);
lean_dec(v_ref_3610_);
lean_dec(v_numSectionVars_3600_);
lean_dec_ref(v_fnNames_3599_);
v_a_3634_ = lean_ctor_get(v___x_3625_, 0);
v_isSharedCheck_3641_ = !lean_is_exclusive(v___x_3625_);
if (v_isSharedCheck_3641_ == 0)
{
v___x_3636_ = v___x_3625_;
v_isShared_3637_ = v_isSharedCheck_3641_;
goto v_resetjp_3635_;
}
else
{
lean_inc(v_a_3634_);
lean_dec(v___x_3625_);
v___x_3636_ = lean_box(0);
v_isShared_3637_ = v_isSharedCheck_3641_;
goto v_resetjp_3635_;
}
v_resetjp_3635_:
{
lean_object* v___x_3639_; 
if (v_isShared_3637_ == 0)
{
v___x_3639_ = v___x_3636_;
goto v_reusejp_3638_;
}
else
{
lean_object* v_reuseFailAlloc_3640_; 
v_reuseFailAlloc_3640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3640_, 0, v_a_3634_);
v___x_3639_ = v_reuseFailAlloc_3640_;
goto v_reusejp_3638_;
}
v_reusejp_3638_:
{
return v___x_3639_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0___redArg___boxed(lean_object* v_fnNames_3643_, lean_object* v_numSectionVars_3644_, lean_object* v_sz_3645_, lean_object* v_i_3646_, lean_object* v_bs_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_){
_start:
{
size_t v_sz_boxed_3651_; size_t v_i_boxed_3652_; lean_object* v_res_3653_; 
v_sz_boxed_3651_ = lean_unbox_usize(v_sz_3645_);
lean_dec(v_sz_3645_);
v_i_boxed_3652_ = lean_unbox_usize(v_i_3646_);
lean_dec(v_i_3646_);
v_res_3653_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0___redArg(v_fnNames_3643_, v_numSectionVars_3644_, v_sz_boxed_3651_, v_i_boxed_3652_, v_bs_3647_, v___y_3648_, v___y_3649_);
lean_dec(v___y_3649_);
lean_dec_ref(v___y_3648_);
return v_res_3653_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0(lean_object* v_fnNames_3654_, lean_object* v_numSectionVars_3655_, size_t v_sz_3656_, size_t v_i_3657_, lean_object* v_bs_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_, lean_object* v___y_3662_){
_start:
{
lean_object* v___x_3664_; 
v___x_3664_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0___redArg(v_fnNames_3654_, v_numSectionVars_3655_, v_sz_3656_, v_i_3657_, v_bs_3658_, v___y_3661_, v___y_3662_);
return v___x_3664_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0___boxed(lean_object* v_fnNames_3665_, lean_object* v_numSectionVars_3666_, lean_object* v_sz_3667_, lean_object* v_i_3668_, lean_object* v_bs_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_){
_start:
{
size_t v_sz_boxed_3675_; size_t v_i_boxed_3676_; lean_object* v_res_3677_; 
v_sz_boxed_3675_ = lean_unbox_usize(v_sz_3667_);
lean_dec(v_sz_3667_);
v_i_boxed_3676_ = lean_unbox_usize(v_i_3668_);
lean_dec(v_i_3668_);
v_res_3677_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0(v_fnNames_3665_, v_numSectionVars_3666_, v_sz_boxed_3675_, v_i_boxed_3676_, v_bs_3669_, v___y_3670_, v___y_3671_, v___y_3672_, v___y_3673_);
lean_dec(v___y_3673_);
lean_dec_ref(v___y_3672_);
lean_dec(v___y_3671_);
lean_dec_ref(v___y_3670_);
return v_res_3677_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos(lean_object* v_preDefs_3678_, lean_object* v_termMeasure_x3fs_3679_, lean_object* v_a_3680_, lean_object* v_a_3681_, lean_object* v_a_3682_, lean_object* v_a_3683_){
_start:
{
lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v_numSectionVars_3688_; size_t v_sz_3689_; lean_object* v___x_3690_; size_t v___x_3691_; lean_object* v_fnNames_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; 
v___x_3685_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_3686_ = lean_unsigned_to_nat(0u);
v___x_3687_ = lean_array_get_borrowed(v___x_3685_, v_preDefs_3678_, v___x_3686_);
v_numSectionVars_3688_ = lean_ctor_get(v___x_3687_, 5);
v_sz_3689_ = lean_array_size(v_preDefs_3678_);
v___x_3690_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0);
v___x_3691_ = ((size_t)0ULL);
lean_inc_ref_n(v_preDefs_3678_, 2);
v_fnNames_3692_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16(v_sz_3689_, v___x_3691_, v_preDefs_3678_);
v___x_3693_ = lean_box_usize(v_sz_3689_);
v___x_3694_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___boxed__const__1));
lean_inc(v_numSectionVars_3688_);
lean_inc_ref(v_fnNames_3692_);
v___x_3695_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0___boxed), 10, 5);
lean_closure_set(v___x_3695_, 0, v_fnNames_3692_);
lean_closure_set(v___x_3695_, 1, v_numSectionVars_3688_);
lean_closure_set(v___x_3695_, 2, v___x_3693_);
lean_closure_set(v___x_3695_, 3, v___x_3694_);
lean_closure_set(v___x_3695_, 4, v_preDefs_3678_);
v___x_3696_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v_preDefs_3678_, v___x_3695_, v_a_3680_, v_a_3681_, v_a_3682_, v_a_3683_);
if (lean_obj_tag(v___x_3696_) == 0)
{
lean_object* v_a_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; 
v_a_3697_ = lean_ctor_get(v___x_3696_, 0);
lean_inc_n(v_a_3697_, 3);
lean_dec_ref_known(v___x_3696_, 1);
v___x_3698_ = lean_alloc_closure((void*)(l_Lean_Elab_getFixedParamPerms___boxed), 6, 1);
lean_closure_set(v___x_3698_, 0, v_a_3697_);
v___x_3699_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v_a_3697_, v___x_3698_, v_a_3680_, v_a_3681_, v_a_3682_, v_a_3683_);
if (lean_obj_tag(v___x_3699_) == 0)
{
lean_object* v_a_3700_; lean_object* v_perms_3701_; lean_object* v___x_3702_; lean_object* v_type_3703_; lean_object* v___x_3704_; lean_object* v___f_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; 
v_a_3700_ = lean_ctor_get(v___x_3699_, 0);
lean_inc(v_a_3700_);
lean_dec_ref_known(v___x_3699_, 1);
v_perms_3701_ = lean_ctor_get(v_a_3700_, 1);
lean_inc_ref_n(v_perms_3701_, 2);
v___x_3702_ = lean_array_get_borrowed(v___x_3685_, v_a_3697_, v___x_3686_);
v_type_3703_ = lean_ctor_get(v___x_3702_, 6);
lean_inc_ref(v_type_3703_);
v___x_3704_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___boxed__const__1));
v___f_3705_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__2___boxed), 12, 6);
lean_closure_set(v___f_3705_, 0, v___x_3704_);
lean_closure_set(v___f_3705_, 1, v_a_3700_);
lean_closure_set(v___f_3705_, 2, v_a_3697_);
lean_closure_set(v___f_3705_, 3, v_perms_3701_);
lean_closure_set(v___f_3705_, 4, v_fnNames_3692_);
lean_closure_set(v___f_3705_, 5, v_termMeasure_x3fs_3679_);
v___x_3706_ = lean_array_get(v___x_3690_, v_perms_3701_, v___x_3686_);
lean_dec_ref(v_perms_3701_);
v___x_3707_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg(v___x_3706_, v_type_3703_, v___f_3705_, v_a_3680_, v_a_3681_, v_a_3682_, v_a_3683_);
return v___x_3707_;
}
else
{
lean_object* v_a_3708_; lean_object* v___x_3710_; uint8_t v_isShared_3711_; uint8_t v_isSharedCheck_3715_; 
lean_dec(v_a_3697_);
lean_dec_ref(v_fnNames_3692_);
lean_dec_ref(v_termMeasure_x3fs_3679_);
v_a_3708_ = lean_ctor_get(v___x_3699_, 0);
v_isSharedCheck_3715_ = !lean_is_exclusive(v___x_3699_);
if (v_isSharedCheck_3715_ == 0)
{
v___x_3710_ = v___x_3699_;
v_isShared_3711_ = v_isSharedCheck_3715_;
goto v_resetjp_3709_;
}
else
{
lean_inc(v_a_3708_);
lean_dec(v___x_3699_);
v___x_3710_ = lean_box(0);
v_isShared_3711_ = v_isSharedCheck_3715_;
goto v_resetjp_3709_;
}
v_resetjp_3709_:
{
lean_object* v___x_3713_; 
if (v_isShared_3711_ == 0)
{
v___x_3713_ = v___x_3710_;
goto v_reusejp_3712_;
}
else
{
lean_object* v_reuseFailAlloc_3714_; 
v_reuseFailAlloc_3714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3714_, 0, v_a_3708_);
v___x_3713_ = v_reuseFailAlloc_3714_;
goto v_reusejp_3712_;
}
v_reusejp_3712_:
{
return v___x_3713_;
}
}
}
}
else
{
lean_object* v_a_3716_; lean_object* v___x_3718_; uint8_t v_isShared_3719_; uint8_t v_isSharedCheck_3723_; 
lean_dec_ref(v_fnNames_3692_);
lean_dec_ref(v_termMeasure_x3fs_3679_);
v_a_3716_ = lean_ctor_get(v___x_3696_, 0);
v_isSharedCheck_3723_ = !lean_is_exclusive(v___x_3696_);
if (v_isSharedCheck_3723_ == 0)
{
v___x_3718_ = v___x_3696_;
v_isShared_3719_ = v_isSharedCheck_3723_;
goto v_resetjp_3717_;
}
else
{
lean_inc(v_a_3716_);
lean_dec(v___x_3696_);
v___x_3718_ = lean_box(0);
v_isShared_3719_ = v_isSharedCheck_3723_;
goto v_resetjp_3717_;
}
v_resetjp_3717_:
{
lean_object* v___x_3721_; 
if (v_isShared_3719_ == 0)
{
v___x_3721_ = v___x_3718_;
goto v_reusejp_3720_;
}
else
{
lean_object* v_reuseFailAlloc_3722_; 
v_reuseFailAlloc_3722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3722_, 0, v_a_3716_);
v___x_3721_ = v_reuseFailAlloc_3722_;
goto v_reusejp_3720_;
}
v_reusejp_3720_:
{
return v___x_3721_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___boxed(lean_object* v_preDefs_3724_, lean_object* v_termMeasure_x3fs_3725_, lean_object* v_a_3726_, lean_object* v_a_3727_, lean_object* v_a_3728_, lean_object* v_a_3729_, lean_object* v_a_3730_){
_start:
{
lean_object* v_res_3731_; 
v_res_3731_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos(v_preDefs_3724_, v_termMeasure_x3fs_3725_, v_a_3726_, v_a_3727_, v_a_3728_, v_a_3729_);
lean_dec(v_a_3729_);
lean_dec_ref(v_a_3728_);
lean_dec(v_a_3727_);
lean_dec_ref(v_a_3726_);
return v_res_3731_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__3(lean_object* v_fst_3732_, lean_object* v_as_3733_, size_t v_sz_3734_, size_t v_i_3735_, lean_object* v_bs_3736_){
_start:
{
lean_object* v___x_3737_; 
v___x_3737_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__3___redArg(v_fst_3732_, v_sz_3734_, v_i_3735_, v_bs_3736_);
return v___x_3737_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__3___boxed(lean_object* v_fst_3738_, lean_object* v_as_3739_, lean_object* v_sz_3740_, lean_object* v_i_3741_, lean_object* v_bs_3742_){
_start:
{
size_t v_sz_boxed_3743_; size_t v_i_boxed_3744_; lean_object* v_res_3745_; 
v_sz_boxed_3743_ = lean_unbox_usize(v_sz_3740_);
lean_dec(v_sz_3740_);
v_i_boxed_3744_ = lean_unbox_usize(v_i_3741_);
lean_dec(v_i_3741_);
v_res_3745_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__3(v_fst_3738_, v_as_3739_, v_sz_boxed_3743_, v_i_boxed_3744_, v_bs_3742_);
lean_dec_ref(v_as_3739_);
lean_dec_ref(v_fst_3738_);
return v_res_3745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__9(lean_object* v_00_u03b1_3746_, lean_object* v_lctx_3747_, lean_object* v_localInsts_3748_, lean_object* v_x_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_){
_start:
{
lean_object* v___x_3755_; 
v___x_3755_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__9___redArg(v_lctx_3747_, v_localInsts_3748_, v_x_3749_, v___y_3750_, v___y_3751_, v___y_3752_, v___y_3753_);
return v___x_3755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__9___boxed(lean_object* v_00_u03b1_3756_, lean_object* v_lctx_3757_, lean_object* v_localInsts_3758_, lean_object* v_x_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_){
_start:
{
lean_object* v_res_3765_; 
v_res_3765_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8_spec__9(v_00_u03b1_3756_, v_lctx_3757_, v_localInsts_3758_, v_x_3759_, v___y_3760_, v___y_3761_, v___y_3762_, v___y_3763_);
lean_dec(v___y_3763_);
lean_dec_ref(v___y_3762_);
lean_dec(v___y_3761_);
lean_dec_ref(v___y_3760_);
return v_res_3765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8(lean_object* v_00_u03b1_3766_, lean_object* v_fvarIds_3767_, lean_object* v_k_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_){
_start:
{
lean_object* v___x_3774_; 
v___x_3774_ = l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8___redArg(v_fvarIds_3767_, v_k_3768_, v___y_3769_, v___y_3770_, v___y_3771_, v___y_3772_);
return v___x_3774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8___boxed(lean_object* v_00_u03b1_3775_, lean_object* v_fvarIds_3776_, lean_object* v_k_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_){
_start:
{
lean_object* v_res_3783_; 
v_res_3783_ = l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8(v_00_u03b1_3775_, v_fvarIds_3776_, v_k_3777_, v___y_3778_, v___y_3779_, v___y_3780_, v___y_3781_);
lean_dec(v___y_3781_);
lean_dec_ref(v___y_3780_);
lean_dec(v___y_3779_);
lean_dec_ref(v___y_3778_);
lean_dec_ref(v_fvarIds_3776_);
return v_res_3783_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__14(lean_object* v_a_3784_){
_start:
{
lean_object* v___x_3785_; 
v___x_3785_ = lean_nat_to_int(v_a_3784_);
return v___x_3785_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__11(lean_object* v___x_3786_, lean_object* v_xs_3787_, lean_object* v_as_3788_, size_t v_sz_3789_, size_t v_i_3790_, lean_object* v_bs_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_){
_start:
{
lean_object* v___x_3797_; 
v___x_3797_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__11___redArg(v___x_3786_, v_xs_3787_, v_sz_3789_, v_i_3790_, v_bs_3791_, v___y_3792_, v___y_3793_, v___y_3794_, v___y_3795_);
return v___x_3797_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__11___boxed(lean_object* v___x_3798_, lean_object* v_xs_3799_, lean_object* v_as_3800_, lean_object* v_sz_3801_, lean_object* v_i_3802_, lean_object* v_bs_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_){
_start:
{
size_t v_sz_boxed_3809_; size_t v_i_boxed_3810_; lean_object* v_res_3811_; 
v_sz_boxed_3809_ = lean_unbox_usize(v_sz_3801_);
lean_dec(v_sz_3801_);
v_i_boxed_3810_ = lean_unbox_usize(v_i_3802_);
lean_dec(v_i_3802_);
v_res_3811_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__11(v___x_3798_, v_xs_3799_, v_as_3800_, v_sz_boxed_3809_, v_i_boxed_3810_, v_bs_3803_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_);
lean_dec(v___y_3807_);
lean_dec_ref(v___y_3806_);
lean_dec(v___y_3805_);
lean_dec_ref(v___y_3804_);
lean_dec_ref(v_as_3800_);
lean_dec_ref(v___x_3798_);
return v_res_3811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure___lam__0(lean_object* v_xs_3812_, lean_object* v_x_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_){
_start:
{
lean_object* v___x_3819_; lean_object* v___x_3820_; 
v___x_3819_ = lean_array_get_size(v_xs_3812_);
v___x_3820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3820_, 0, v___x_3819_);
return v___x_3820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure___lam__0___boxed(lean_object* v_xs_3821_, lean_object* v_x_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_){
_start:
{
lean_object* v_res_3828_; 
v_res_3828_ = l_Lean_Elab_Structural_reportTermMeasure___lam__0(v_xs_3821_, v_x_3822_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_);
lean_dec(v___y_3826_);
lean_dec_ref(v___y_3825_);
lean_dec(v___y_3824_);
lean_dec_ref(v___y_3823_);
lean_dec_ref(v_x_3822_);
lean_dec_ref(v_xs_3821_);
return v_res_3828_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure___lam__1(lean_object* v___x_3829_, lean_object* v_recArgPos_3830_, lean_object* v_xs_3831_, lean_object* v_x_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_){
_start:
{
lean_object* v___x_3838_; uint8_t v___x_3839_; uint8_t v___x_3840_; uint8_t v___x_3841_; lean_object* v___x_3842_; 
v___x_3838_ = lean_array_get_borrowed(v___x_3829_, v_xs_3831_, v_recArgPos_3830_);
v___x_3839_ = 0;
v___x_3840_ = 1;
v___x_3841_ = 1;
lean_inc(v___x_3838_);
v___x_3842_ = l_Lean_Meta_mkLambdaFVars(v_xs_3831_, v___x_3838_, v___x_3839_, v___x_3840_, v___x_3839_, v___x_3840_, v___x_3841_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_);
return v___x_3842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure___lam__1___boxed(lean_object* v___x_3843_, lean_object* v_recArgPos_3844_, lean_object* v_xs_3845_, lean_object* v_x_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_){
_start:
{
lean_object* v_res_3852_; 
v_res_3852_ = l_Lean_Elab_Structural_reportTermMeasure___lam__1(v___x_3843_, v_recArgPos_3844_, v_xs_3845_, v_x_3846_, v___y_3847_, v___y_3848_, v___y_3849_, v___y_3850_);
lean_dec(v___y_3850_);
lean_dec_ref(v___y_3849_);
lean_dec(v___y_3848_);
lean_dec_ref(v___y_3847_);
lean_dec_ref(v_x_3846_);
lean_dec_ref(v_xs_3845_);
lean_dec(v_recArgPos_3844_);
lean_dec_ref(v___x_3843_);
return v_res_3852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure(lean_object* v_preDef_3864_, lean_object* v_recArgPos_3865_, lean_object* v_a_3866_, lean_object* v_a_3867_, lean_object* v_a_3868_, lean_object* v_a_3869_){
_start:
{
lean_object* v_termination_3871_; lean_object* v_terminationBy_x3f_x3f_3872_; 
v_termination_3871_ = lean_ctor_get(v_preDef_3864_, 8);
lean_inc_ref(v_termination_3871_);
v_terminationBy_x3f_x3f_3872_ = lean_ctor_get(v_termination_3871_, 1);
lean_inc(v_terminationBy_x3f_x3f_3872_);
if (lean_obj_tag(v_terminationBy_x3f_x3f_3872_) == 1)
{
lean_object* v_value_3873_; lean_object* v_extraParams_3874_; lean_object* v_val_3875_; lean_object* v___f_3876_; lean_object* v___x_3877_; lean_object* v___f_3878_; uint8_t v___x_3879_; lean_object* v___x_3880_; 
v_value_3873_ = lean_ctor_get(v_preDef_3864_, 7);
lean_inc_ref_n(v_value_3873_, 2);
lean_dec_ref(v_preDef_3864_);
v_extraParams_3874_ = lean_ctor_get(v_termination_3871_, 5);
lean_inc(v_extraParams_3874_);
lean_dec_ref(v_termination_3871_);
v_val_3875_ = lean_ctor_get(v_terminationBy_x3f_x3f_3872_, 0);
lean_inc(v_val_3875_);
lean_dec_ref_known(v_terminationBy_x3f_x3f_3872_, 1);
v___f_3876_ = ((lean_object*)(l_Lean_Elab_Structural_reportTermMeasure___closed__0));
v___x_3877_ = l_Lean_instInhabitedExpr;
v___f_3878_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_reportTermMeasure___lam__1___boxed), 9, 2);
lean_closure_set(v___f_3878_, 0, v___x_3877_);
lean_closure_set(v___f_3878_, 1, v_recArgPos_3865_);
v___x_3879_ = 0;
v___x_3880_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg(v_value_3873_, v___f_3878_, v___x_3879_, v_a_3866_, v_a_3867_, v_a_3868_, v_a_3869_);
if (lean_obj_tag(v___x_3880_) == 0)
{
lean_object* v_a_3881_; lean_object* v___x_3882_; uint8_t v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; 
v_a_3881_ = lean_ctor_get(v___x_3880_, 0);
lean_inc(v_a_3881_);
lean_dec_ref_known(v___x_3880_, 1);
v___x_3882_ = lean_box(0);
v___x_3883_ = 1;
v___x_3884_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3884_, 0, v___x_3882_);
lean_ctor_set(v___x_3884_, 1, v_a_3881_);
lean_ctor_set_uint8(v___x_3884_, sizeof(void*)*2, v___x_3883_);
v___x_3885_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg(v_value_3873_, v___f_3876_, v___x_3879_, v_a_3866_, v_a_3867_, v_a_3868_, v_a_3869_);
if (lean_obj_tag(v___x_3885_) == 0)
{
lean_object* v_a_3886_; lean_object* v___x_3887_; 
v_a_3886_ = lean_ctor_get(v___x_3885_, 0);
lean_inc(v_a_3886_);
lean_dec_ref_known(v___x_3885_, 1);
v___x_3887_ = l_Lean_Elab_TerminationMeasure_delab(v_a_3886_, v_extraParams_3874_, v___x_3884_, v_a_3866_, v_a_3867_, v_a_3868_, v_a_3869_);
lean_dec(v_a_3886_);
if (lean_obj_tag(v___x_3887_) == 0)
{
lean_object* v_a_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; uint8_t v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; 
v_a_3888_ = lean_ctor_get(v___x_3887_, 0);
lean_inc(v_a_3888_);
lean_dec_ref_known(v___x_3887_, 1);
v___x_3889_ = ((lean_object*)(l_Lean_Elab_Structural_reportTermMeasure___closed__5));
v___x_3890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3890_, 0, v___x_3889_);
lean_ctor_set(v___x_3890_, 1, v_a_3888_);
v___x_3891_ = lean_box(0);
v___x_3892_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3892_, 0, v___x_3890_);
lean_ctor_set(v___x_3892_, 1, v___x_3891_);
lean_ctor_set(v___x_3892_, 2, v___x_3891_);
lean_ctor_set(v___x_3892_, 3, v___x_3891_);
lean_ctor_set(v___x_3892_, 4, v___x_3891_);
lean_ctor_set(v___x_3892_, 5, v___x_3891_);
v___x_3893_ = ((lean_object*)(l_Lean_Elab_Structural_reportTermMeasure___closed__6));
v___x_3894_ = 4;
v___x_3895_ = l_Lean_MessageData_nil;
v___x_3896_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_val_3875_, v___x_3892_, v___x_3891_, v___x_3893_, v___x_3891_, v___x_3894_, v___x_3895_, v_a_3868_, v_a_3869_);
return v___x_3896_;
}
else
{
lean_object* v_a_3897_; lean_object* v___x_3899_; uint8_t v_isShared_3900_; uint8_t v_isSharedCheck_3904_; 
lean_dec(v_val_3875_);
v_a_3897_ = lean_ctor_get(v___x_3887_, 0);
v_isSharedCheck_3904_ = !lean_is_exclusive(v___x_3887_);
if (v_isSharedCheck_3904_ == 0)
{
v___x_3899_ = v___x_3887_;
v_isShared_3900_ = v_isSharedCheck_3904_;
goto v_resetjp_3898_;
}
else
{
lean_inc(v_a_3897_);
lean_dec(v___x_3887_);
v___x_3899_ = lean_box(0);
v_isShared_3900_ = v_isSharedCheck_3904_;
goto v_resetjp_3898_;
}
v_resetjp_3898_:
{
lean_object* v___x_3902_; 
if (v_isShared_3900_ == 0)
{
v___x_3902_ = v___x_3899_;
goto v_reusejp_3901_;
}
else
{
lean_object* v_reuseFailAlloc_3903_; 
v_reuseFailAlloc_3903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3903_, 0, v_a_3897_);
v___x_3902_ = v_reuseFailAlloc_3903_;
goto v_reusejp_3901_;
}
v_reusejp_3901_:
{
return v___x_3902_;
}
}
}
}
else
{
lean_object* v_a_3905_; lean_object* v___x_3907_; uint8_t v_isShared_3908_; uint8_t v_isSharedCheck_3912_; 
lean_dec_ref_known(v___x_3884_, 2);
lean_dec(v_val_3875_);
lean_dec(v_extraParams_3874_);
v_a_3905_ = lean_ctor_get(v___x_3885_, 0);
v_isSharedCheck_3912_ = !lean_is_exclusive(v___x_3885_);
if (v_isSharedCheck_3912_ == 0)
{
v___x_3907_ = v___x_3885_;
v_isShared_3908_ = v_isSharedCheck_3912_;
goto v_resetjp_3906_;
}
else
{
lean_inc(v_a_3905_);
lean_dec(v___x_3885_);
v___x_3907_ = lean_box(0);
v_isShared_3908_ = v_isSharedCheck_3912_;
goto v_resetjp_3906_;
}
v_resetjp_3906_:
{
lean_object* v___x_3910_; 
if (v_isShared_3908_ == 0)
{
v___x_3910_ = v___x_3907_;
goto v_reusejp_3909_;
}
else
{
lean_object* v_reuseFailAlloc_3911_; 
v_reuseFailAlloc_3911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3911_, 0, v_a_3905_);
v___x_3910_ = v_reuseFailAlloc_3911_;
goto v_reusejp_3909_;
}
v_reusejp_3909_:
{
return v___x_3910_;
}
}
}
}
else
{
lean_object* v_a_3913_; lean_object* v___x_3915_; uint8_t v_isShared_3916_; uint8_t v_isSharedCheck_3920_; 
lean_dec(v_val_3875_);
lean_dec(v_extraParams_3874_);
lean_dec_ref(v_value_3873_);
v_a_3913_ = lean_ctor_get(v___x_3880_, 0);
v_isSharedCheck_3920_ = !lean_is_exclusive(v___x_3880_);
if (v_isSharedCheck_3920_ == 0)
{
v___x_3915_ = v___x_3880_;
v_isShared_3916_ = v_isSharedCheck_3920_;
goto v_resetjp_3914_;
}
else
{
lean_inc(v_a_3913_);
lean_dec(v___x_3880_);
v___x_3915_ = lean_box(0);
v_isShared_3916_ = v_isSharedCheck_3920_;
goto v_resetjp_3914_;
}
v_resetjp_3914_:
{
lean_object* v___x_3918_; 
if (v_isShared_3916_ == 0)
{
v___x_3918_ = v___x_3915_;
goto v_reusejp_3917_;
}
else
{
lean_object* v_reuseFailAlloc_3919_; 
v_reuseFailAlloc_3919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3919_, 0, v_a_3913_);
v___x_3918_ = v_reuseFailAlloc_3919_;
goto v_reusejp_3917_;
}
v_reusejp_3917_:
{
return v___x_3918_;
}
}
}
}
else
{
lean_object* v___x_3921_; lean_object* v___x_3922_; 
lean_dec(v_terminationBy_x3f_x3f_3872_);
lean_dec_ref(v_termination_3871_);
lean_dec(v_recArgPos_3865_);
lean_dec_ref(v_preDef_3864_);
v___x_3921_ = lean_box(0);
v___x_3922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3922_, 0, v___x_3921_);
return v___x_3922_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure___boxed(lean_object* v_preDef_3923_, lean_object* v_recArgPos_3924_, lean_object* v_a_3925_, lean_object* v_a_3926_, lean_object* v_a_3927_, lean_object* v_a_3928_, lean_object* v_a_3929_){
_start:
{
lean_object* v_res_3930_; 
v_res_3930_ = l_Lean_Elab_Structural_reportTermMeasure(v_preDef_3923_, v_recArgPos_3924_, v_a_3925_, v_a_3926_, v_a_3927_, v_a_3928_);
lean_dec(v_a_3928_);
lean_dec_ref(v_a_3927_);
lean_dec(v_a_3926_);
lean_dec_ref(v_a_3925_);
return v_res_3930_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___redArg(lean_object* v_as_3931_, size_t v_sz_3932_, size_t v_i_3933_, lean_object* v_b_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_){
_start:
{
uint8_t v___x_3940_; 
v___x_3940_ = lean_usize_dec_lt(v_i_3933_, v_sz_3932_);
if (v___x_3940_ == 0)
{
lean_object* v___x_3941_; 
v___x_3941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3941_, 0, v_b_3934_);
return v___x_3941_;
}
else
{
lean_object* v_a_3942_; lean_object* v_declName_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; 
v_a_3942_ = lean_array_uget_borrowed(v_as_3931_, v_i_3933_);
v_declName_3943_ = lean_ctor_get(v_a_3942_, 3);
v___x_3944_ = lean_box(0);
lean_inc(v_declName_3943_);
v___x_3945_ = l_Lean_Meta_saveEqnAffectingOptions(v_declName_3943_, v___y_3935_, v___y_3936_, v___y_3937_, v___y_3938_);
if (lean_obj_tag(v___x_3945_) == 0)
{
size_t v___x_3946_; size_t v___x_3947_; 
lean_dec_ref_known(v___x_3945_, 1);
v___x_3946_ = ((size_t)1ULL);
v___x_3947_ = lean_usize_add(v_i_3933_, v___x_3946_);
v_i_3933_ = v___x_3947_;
v_b_3934_ = v___x_3944_;
goto _start;
}
else
{
return v___x_3945_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___redArg___boxed(lean_object* v_as_3949_, lean_object* v_sz_3950_, lean_object* v_i_3951_, lean_object* v_b_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_){
_start:
{
size_t v_sz_boxed_3958_; size_t v_i_boxed_3959_; lean_object* v_res_3960_; 
v_sz_boxed_3958_ = lean_unbox_usize(v_sz_3950_);
lean_dec(v_sz_3950_);
v_i_boxed_3959_ = lean_unbox_usize(v_i_3951_);
lean_dec(v_i_3951_);
v_res_3960_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___redArg(v_as_3949_, v_sz_boxed_3958_, v_i_boxed_3959_, v_b_3952_, v___y_3953_, v___y_3954_, v___y_3955_, v___y_3956_);
lean_dec(v___y_3956_);
lean_dec_ref(v___y_3955_);
lean_dec(v___y_3954_);
lean_dec_ref(v___y_3953_);
lean_dec_ref(v_as_3949_);
return v_res_3960_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__1(lean_object* v_a_3961_, lean_object* v_fst_3962_, lean_object* v_docCtx_3963_, lean_object* v_snd_3964_, lean_object* v_as_3965_, size_t v_sz_3966_, size_t v_i_3967_, lean_object* v_b_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_){
_start:
{
uint8_t v___x_3976_; 
v___x_3976_ = lean_usize_dec_lt(v_i_3967_, v_sz_3966_);
if (v___x_3976_ == 0)
{
lean_object* v___x_3977_; 
lean_dec_ref(v_snd_3964_);
lean_dec_ref(v_docCtx_3963_);
lean_dec_ref(v_a_3961_);
v___x_3977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3977_, 0, v_b_3968_);
return v___x_3977_;
}
else
{
lean_object* v_array_3978_; lean_object* v_start_3979_; lean_object* v_stop_3980_; uint8_t v___x_3981_; 
v_array_3978_ = lean_ctor_get(v_b_3968_, 0);
v_start_3979_ = lean_ctor_get(v_b_3968_, 1);
v_stop_3980_ = lean_ctor_get(v_b_3968_, 2);
v___x_3981_ = lean_nat_dec_lt(v_start_3979_, v_stop_3980_);
if (v___x_3981_ == 0)
{
lean_object* v___x_3982_; 
lean_dec_ref(v_snd_3964_);
lean_dec_ref(v_docCtx_3963_);
lean_dec_ref(v_a_3961_);
v___x_3982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3982_, 0, v_b_3968_);
return v___x_3982_;
}
else
{
lean_object* v___x_3984_; uint8_t v_isShared_3985_; uint8_t v_isSharedCheck_4053_; 
lean_inc(v_stop_3980_);
lean_inc(v_start_3979_);
lean_inc_ref(v_array_3978_);
v_isSharedCheck_4053_ = !lean_is_exclusive(v_b_3968_);
if (v_isSharedCheck_4053_ == 0)
{
lean_object* v_unused_4054_; lean_object* v_unused_4055_; lean_object* v_unused_4056_; 
v_unused_4054_ = lean_ctor_get(v_b_3968_, 2);
lean_dec(v_unused_4054_);
v_unused_4055_ = lean_ctor_get(v_b_3968_, 1);
lean_dec(v_unused_4055_);
v_unused_4056_ = lean_ctor_get(v_b_3968_, 0);
lean_dec(v_unused_4056_);
v___x_3984_ = v_b_3968_;
v_isShared_3985_ = v_isSharedCheck_4053_;
goto v_resetjp_3983_;
}
else
{
lean_dec(v_b_3968_);
v___x_3984_ = lean_box(0);
v_isShared_3985_ = v_isSharedCheck_4053_;
goto v_resetjp_3983_;
}
v_resetjp_3983_:
{
lean_object* v_a_3986_; uint8_t v_kind_3987_; lean_object* v_type_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3993_; 
v_a_3986_ = lean_array_uget_borrowed(v_as_3965_, v_i_3967_);
v_kind_3987_ = lean_ctor_get_uint8(v_a_3986_, sizeof(void*)*9);
v_type_3988_ = lean_ctor_get(v_a_3986_, 6);
v___x_3989_ = lean_array_fget(v_array_3978_, v_start_3979_);
v___x_3990_ = lean_unsigned_to_nat(1u);
v___x_3991_ = lean_nat_add(v_start_3979_, v___x_3990_);
lean_dec(v_start_3979_);
if (v_isShared_3985_ == 0)
{
lean_ctor_set(v___x_3984_, 1, v___x_3991_);
v___x_3993_ = v___x_3984_;
goto v_reusejp_3992_;
}
else
{
lean_object* v_reuseFailAlloc_4052_; 
v_reuseFailAlloc_4052_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4052_, 0, v_array_3978_);
lean_ctor_set(v_reuseFailAlloc_4052_, 1, v___x_3991_);
lean_ctor_set(v_reuseFailAlloc_4052_, 2, v_stop_3980_);
v___x_3993_ = v_reuseFailAlloc_4052_;
goto v_reusejp_3992_;
}
v_reusejp_3992_:
{
lean_object* v_preDef_3995_; lean_object* v___y_3996_; lean_object* v___y_3997_; lean_object* v___y_3998_; lean_object* v___y_3999_; lean_object* v___y_4000_; lean_object* v___y_4001_; uint8_t v___x_4018_; 
v___x_4018_ = l_Lean_Elab_DefKind_isTheorem(v_kind_3987_);
if (v___x_4018_ == 0)
{
lean_object* v___x_4019_; 
lean_inc_ref(v_type_3988_);
v___x_4019_ = l_Lean_Meta_isProp(v_type_3988_, v___y_3971_, v___y_3972_, v___y_3973_, v___y_3974_);
if (lean_obj_tag(v___x_4019_) == 0)
{
lean_object* v_a_4020_; uint8_t v___x_4021_; 
v_a_4020_ = lean_ctor_get(v___x_4019_, 0);
lean_inc(v_a_4020_);
lean_dec_ref_known(v___x_4019_, 1);
v___x_4021_ = lean_unbox(v_a_4020_);
lean_dec(v_a_4020_);
if (v___x_4021_ == 0)
{
lean_object* v___x_4022_; 
lean_inc(v_a_3986_);
v___x_4022_ = l_Lean_Elab_abstractNestedProofs(v_a_3986_, v___x_3981_, v___y_3971_, v___y_3972_, v___y_3973_, v___y_3974_);
if (lean_obj_tag(v___x_4022_) == 0)
{
lean_object* v_a_4023_; size_t v_sz_4024_; size_t v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; 
v_a_4023_ = lean_ctor_get(v___x_4022_, 0);
lean_inc_n(v_a_4023_, 2);
lean_dec_ref_known(v___x_4022_, 1);
v_sz_4024_ = lean_array_size(v_a_3961_);
v___x_4025_ = ((size_t)0ULL);
lean_inc_ref(v_a_3961_);
v___x_4026_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16(v_sz_4024_, v___x_4025_, v_a_3961_);
lean_inc_ref(v_snd_3964_);
v___x_4027_ = l_Lean_Elab_Structural_registerEqnsInfo(v_a_4023_, v___x_4026_, v___x_3989_, v_snd_3964_, v___y_3973_, v___y_3974_);
if (lean_obj_tag(v___x_4027_) == 0)
{
lean_dec_ref_known(v___x_4027_, 1);
v_preDef_3995_ = v_a_4023_;
v___y_3996_ = v___y_3969_;
v___y_3997_ = v___y_3970_;
v___y_3998_ = v___y_3971_;
v___y_3999_ = v___y_3972_;
v___y_4000_ = v___y_3973_;
v___y_4001_ = v___y_3974_;
goto v___jp_3994_;
}
else
{
lean_object* v_a_4028_; lean_object* v___x_4030_; uint8_t v_isShared_4031_; uint8_t v_isSharedCheck_4035_; 
lean_dec(v_a_4023_);
lean_dec_ref(v___x_3993_);
lean_dec_ref(v_snd_3964_);
lean_dec_ref(v_docCtx_3963_);
lean_dec_ref(v_a_3961_);
v_a_4028_ = lean_ctor_get(v___x_4027_, 0);
v_isSharedCheck_4035_ = !lean_is_exclusive(v___x_4027_);
if (v_isSharedCheck_4035_ == 0)
{
v___x_4030_ = v___x_4027_;
v_isShared_4031_ = v_isSharedCheck_4035_;
goto v_resetjp_4029_;
}
else
{
lean_inc(v_a_4028_);
lean_dec(v___x_4027_);
v___x_4030_ = lean_box(0);
v_isShared_4031_ = v_isSharedCheck_4035_;
goto v_resetjp_4029_;
}
v_resetjp_4029_:
{
lean_object* v___x_4033_; 
if (v_isShared_4031_ == 0)
{
v___x_4033_ = v___x_4030_;
goto v_reusejp_4032_;
}
else
{
lean_object* v_reuseFailAlloc_4034_; 
v_reuseFailAlloc_4034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4034_, 0, v_a_4028_);
v___x_4033_ = v_reuseFailAlloc_4034_;
goto v_reusejp_4032_;
}
v_reusejp_4032_:
{
return v___x_4033_;
}
}
}
}
else
{
lean_object* v_a_4036_; lean_object* v___x_4038_; uint8_t v_isShared_4039_; uint8_t v_isSharedCheck_4043_; 
lean_dec_ref(v___x_3993_);
lean_dec(v___x_3989_);
lean_dec_ref(v_snd_3964_);
lean_dec_ref(v_docCtx_3963_);
lean_dec_ref(v_a_3961_);
v_a_4036_ = lean_ctor_get(v___x_4022_, 0);
v_isSharedCheck_4043_ = !lean_is_exclusive(v___x_4022_);
if (v_isSharedCheck_4043_ == 0)
{
v___x_4038_ = v___x_4022_;
v_isShared_4039_ = v_isSharedCheck_4043_;
goto v_resetjp_4037_;
}
else
{
lean_inc(v_a_4036_);
lean_dec(v___x_4022_);
v___x_4038_ = lean_box(0);
v_isShared_4039_ = v_isSharedCheck_4043_;
goto v_resetjp_4037_;
}
v_resetjp_4037_:
{
lean_object* v___x_4041_; 
if (v_isShared_4039_ == 0)
{
v___x_4041_ = v___x_4038_;
goto v_reusejp_4040_;
}
else
{
lean_object* v_reuseFailAlloc_4042_; 
v_reuseFailAlloc_4042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4042_, 0, v_a_4036_);
v___x_4041_ = v_reuseFailAlloc_4042_;
goto v_reusejp_4040_;
}
v_reusejp_4040_:
{
return v___x_4041_;
}
}
}
}
else
{
lean_dec(v___x_3989_);
lean_inc(v_a_3986_);
v_preDef_3995_ = v_a_3986_;
v___y_3996_ = v___y_3969_;
v___y_3997_ = v___y_3970_;
v___y_3998_ = v___y_3971_;
v___y_3999_ = v___y_3972_;
v___y_4000_ = v___y_3973_;
v___y_4001_ = v___y_3974_;
goto v___jp_3994_;
}
}
else
{
lean_object* v_a_4044_; lean_object* v___x_4046_; uint8_t v_isShared_4047_; uint8_t v_isSharedCheck_4051_; 
lean_dec_ref(v___x_3993_);
lean_dec(v___x_3989_);
lean_dec_ref(v_snd_3964_);
lean_dec_ref(v_docCtx_3963_);
lean_dec_ref(v_a_3961_);
v_a_4044_ = lean_ctor_get(v___x_4019_, 0);
v_isSharedCheck_4051_ = !lean_is_exclusive(v___x_4019_);
if (v_isSharedCheck_4051_ == 0)
{
v___x_4046_ = v___x_4019_;
v_isShared_4047_ = v_isSharedCheck_4051_;
goto v_resetjp_4045_;
}
else
{
lean_inc(v_a_4044_);
lean_dec(v___x_4019_);
v___x_4046_ = lean_box(0);
v_isShared_4047_ = v_isSharedCheck_4051_;
goto v_resetjp_4045_;
}
v_resetjp_4045_:
{
lean_object* v___x_4049_; 
if (v_isShared_4047_ == 0)
{
v___x_4049_ = v___x_4046_;
goto v_reusejp_4048_;
}
else
{
lean_object* v_reuseFailAlloc_4050_; 
v_reuseFailAlloc_4050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4050_, 0, v_a_4044_);
v___x_4049_ = v_reuseFailAlloc_4050_;
goto v_reusejp_4048_;
}
v_reusejp_4048_:
{
return v___x_4049_;
}
}
}
}
else
{
lean_dec(v___x_3989_);
lean_inc(v_a_3986_);
v_preDef_3995_ = v_a_3986_;
v___y_3996_ = v___y_3969_;
v___y_3997_ = v___y_3970_;
v___y_3998_ = v___y_3971_;
v___y_3999_ = v___y_3972_;
v___y_4000_ = v___y_3973_;
v___y_4001_ = v___y_3974_;
goto v___jp_3994_;
}
v___jp_3994_:
{
size_t v_sz_4002_; size_t v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; 
v_sz_4002_ = lean_array_size(v_a_3961_);
v___x_4003_ = ((size_t)0ULL);
lean_inc_ref(v_a_3961_);
v___x_4004_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16(v_sz_4002_, v___x_4003_, v_a_3961_);
v___x_4005_ = l_Array_zip___redArg(v___x_4004_, v_fst_3962_);
lean_dec_ref(v___x_4004_);
lean_inc_ref(v_docCtx_3963_);
v___x_4006_ = l_Lean_Elab_Structural_addSmartUnfoldingDef(v_docCtx_3963_, v_preDef_3995_, v___x_4005_, v___y_3996_, v___y_3997_, v___y_3998_, v___y_3999_, v___y_4000_, v___y_4001_);
if (lean_obj_tag(v___x_4006_) == 0)
{
size_t v___x_4007_; size_t v___x_4008_; 
lean_dec_ref_known(v___x_4006_, 1);
v___x_4007_ = ((size_t)1ULL);
v___x_4008_ = lean_usize_add(v_i_3967_, v___x_4007_);
v_i_3967_ = v___x_4008_;
v_b_3968_ = v___x_3993_;
goto _start;
}
else
{
lean_object* v_a_4010_; lean_object* v___x_4012_; uint8_t v_isShared_4013_; uint8_t v_isSharedCheck_4017_; 
lean_dec_ref(v___x_3993_);
lean_dec_ref(v_snd_3964_);
lean_dec_ref(v_docCtx_3963_);
lean_dec_ref(v_a_3961_);
v_a_4010_ = lean_ctor_get(v___x_4006_, 0);
v_isSharedCheck_4017_ = !lean_is_exclusive(v___x_4006_);
if (v_isSharedCheck_4017_ == 0)
{
v___x_4012_ = v___x_4006_;
v_isShared_4013_ = v_isSharedCheck_4017_;
goto v_resetjp_4011_;
}
else
{
lean_inc(v_a_4010_);
lean_dec(v___x_4006_);
v___x_4012_ = lean_box(0);
v_isShared_4013_ = v_isSharedCheck_4017_;
goto v_resetjp_4011_;
}
v_resetjp_4011_:
{
lean_object* v___x_4015_; 
if (v_isShared_4013_ == 0)
{
v___x_4015_ = v___x_4012_;
goto v_reusejp_4014_;
}
else
{
lean_object* v_reuseFailAlloc_4016_; 
v_reuseFailAlloc_4016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4016_, 0, v_a_4010_);
v___x_4015_ = v_reuseFailAlloc_4016_;
goto v_reusejp_4014_;
}
v_reusejp_4014_:
{
return v___x_4015_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__1___boxed(lean_object* v_a_4057_, lean_object* v_fst_4058_, lean_object* v_docCtx_4059_, lean_object* v_snd_4060_, lean_object* v_as_4061_, lean_object* v_sz_4062_, lean_object* v_i_4063_, lean_object* v_b_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_, lean_object* v___y_4070_, lean_object* v___y_4071_){
_start:
{
size_t v_sz_boxed_4072_; size_t v_i_boxed_4073_; lean_object* v_res_4074_; 
v_sz_boxed_4072_ = lean_unbox_usize(v_sz_4062_);
lean_dec(v_sz_4062_);
v_i_boxed_4073_ = lean_unbox_usize(v_i_4063_);
lean_dec(v_i_4063_);
v_res_4074_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__1(v_a_4057_, v_fst_4058_, v_docCtx_4059_, v_snd_4060_, v_as_4061_, v_sz_boxed_4072_, v_i_boxed_4073_, v_b_4064_, v___y_4065_, v___y_4066_, v___y_4067_, v___y_4068_, v___y_4069_, v___y_4070_);
lean_dec(v___y_4070_);
lean_dec_ref(v___y_4069_);
lean_dec(v___y_4068_);
lean_dec_ref(v___y_4067_);
lean_dec(v___y_4066_);
lean_dec_ref(v___y_4065_);
lean_dec_ref(v_as_4061_);
lean_dec_ref(v_fst_4058_);
return v_res_4074_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___lam__0(lean_object* v___x_4075_, lean_object* v_e_4076_){
_start:
{
lean_object* v___x_4077_; lean_object* v___x_4078_; 
v___x_4077_ = l_Lean_indentD(v_e_4076_);
v___x_4078_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4078_, 0, v___x_4075_);
lean_ctor_set(v___x_4078_, 1, v___x_4077_);
return v___x_4078_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___lam__1(lean_object* v_docCtx_4079_, lean_object* v_a_4080_, uint8_t v___x_4081_, lean_object* v___x_4082_, uint8_t v___x_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_){
_start:
{
lean_object* v___x_4091_; 
v___x_4091_ = l_Lean_Elab_addNonRec(v_docCtx_4079_, v_a_4080_, v___x_4081_, v___x_4082_, v___x_4083_, v___x_4081_, v___x_4083_, v___x_4083_, v___y_4084_, v___y_4085_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_);
return v___x_4091_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___lam__1___boxed(lean_object* v_docCtx_4092_, lean_object* v_a_4093_, lean_object* v___x_4094_, lean_object* v___x_4095_, lean_object* v___x_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_){
_start:
{
uint8_t v___x_9352__boxed_4104_; uint8_t v___x_9354__boxed_4105_; lean_object* v_res_4106_; 
v___x_9352__boxed_4104_ = lean_unbox(v___x_4094_);
v___x_9354__boxed_4105_ = lean_unbox(v___x_4096_);
v_res_4106_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___lam__1(v_docCtx_4092_, v_a_4093_, v___x_9352__boxed_4104_, v___x_4095_, v___x_9354__boxed_4105_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_, v___y_4101_, v___y_4102_);
lean_dec(v___y_4102_);
lean_dec_ref(v___y_4101_);
lean_dec(v___y_4100_);
lean_dec_ref(v___y_4099_);
lean_dec(v___y_4098_);
lean_dec_ref(v___y_4097_);
return v_res_4106_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__1(void){
_start:
{
lean_object* v___x_4108_; lean_object* v___x_4109_; 
v___x_4108_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__0));
v___x_4109_ = l_Lean_stringToMessageData(v___x_4108_);
return v___x_4109_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__2(void){
_start:
{
lean_object* v___x_4110_; lean_object* v___f_4111_; 
v___x_4110_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__1);
v___f_4111_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___lam__0), 2, 1);
lean_closure_set(v___f_4111_, 0, v___x_4110_);
return v___f_4111_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5(lean_object* v_names_4112_, lean_object* v_docCtx_4113_, lean_object* v_as_4114_, size_t v_i_4115_, size_t v_stop_4116_, lean_object* v_b_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_){
_start:
{
uint8_t v___x_4125_; 
v___x_4125_ = lean_usize_dec_eq(v_i_4115_, v_stop_4116_);
if (v___x_4125_ == 0)
{
lean_object* v___x_4126_; lean_object* v___x_4127_; 
v___x_4126_ = lean_array_uget_borrowed(v_as_4114_, v_i_4115_);
lean_inc(v___x_4126_);
v___x_4127_ = l_Lean_Elab_eraseRecAppSyntax(v___x_4126_, v___y_4122_, v___y_4123_);
if (lean_obj_tag(v___x_4127_) == 0)
{
lean_object* v_a_4128_; lean_object* v___f_4129_; lean_object* v___x_4130_; uint8_t v___x_4131_; lean_object* v___x_4132_; lean_object* v___x_4133_; lean_object* v___f_4134_; lean_object* v___x_4135_; 
v_a_4128_ = lean_ctor_get(v___x_4127_, 0);
lean_inc(v_a_4128_);
lean_dec_ref_known(v___x_4127_, 1);
v___f_4129_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__2);
lean_inc_ref(v_names_4112_);
v___x_4130_ = lean_array_to_list(v_names_4112_);
v___x_4131_ = 1;
v___x_4132_ = lean_box(v___x_4125_);
v___x_4133_ = lean_box(v___x_4131_);
lean_inc(v___y_4119_);
lean_inc_ref(v___y_4118_);
lean_inc_ref(v_docCtx_4113_);
v___f_4134_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___lam__1___boxed), 12, 7);
lean_closure_set(v___f_4134_, 0, v_docCtx_4113_);
lean_closure_set(v___f_4134_, 1, v_a_4128_);
lean_closure_set(v___f_4134_, 2, v___x_4132_);
lean_closure_set(v___f_4134_, 3, v___x_4130_);
lean_closure_set(v___f_4134_, 4, v___x_4133_);
lean_closure_set(v___f_4134_, 5, v___y_4118_);
lean_closure_set(v___f_4134_, 6, v___y_4119_);
v___x_4135_ = l_Lean_Meta_mapErrorImp___redArg(v___f_4134_, v___f_4129_, v___y_4120_, v___y_4121_, v___y_4122_, v___y_4123_);
if (lean_obj_tag(v___x_4135_) == 0)
{
lean_object* v_a_4136_; size_t v___x_4137_; size_t v___x_4138_; 
v_a_4136_ = lean_ctor_get(v___x_4135_, 0);
lean_inc(v_a_4136_);
lean_dec_ref_known(v___x_4135_, 1);
v___x_4137_ = ((size_t)1ULL);
v___x_4138_ = lean_usize_add(v_i_4115_, v___x_4137_);
v_i_4115_ = v___x_4138_;
v_b_4117_ = v_a_4136_;
goto _start;
}
else
{
lean_object* v_a_4140_; lean_object* v___x_4142_; uint8_t v_isShared_4143_; uint8_t v_isSharedCheck_4147_; 
lean_dec_ref(v_docCtx_4113_);
lean_dec_ref(v_names_4112_);
v_a_4140_ = lean_ctor_get(v___x_4135_, 0);
v_isSharedCheck_4147_ = !lean_is_exclusive(v___x_4135_);
if (v_isSharedCheck_4147_ == 0)
{
v___x_4142_ = v___x_4135_;
v_isShared_4143_ = v_isSharedCheck_4147_;
goto v_resetjp_4141_;
}
else
{
lean_inc(v_a_4140_);
lean_dec(v___x_4135_);
v___x_4142_ = lean_box(0);
v_isShared_4143_ = v_isSharedCheck_4147_;
goto v_resetjp_4141_;
}
v_resetjp_4141_:
{
lean_object* v___x_4145_; 
if (v_isShared_4143_ == 0)
{
v___x_4145_ = v___x_4142_;
goto v_reusejp_4144_;
}
else
{
lean_object* v_reuseFailAlloc_4146_; 
v_reuseFailAlloc_4146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4146_, 0, v_a_4140_);
v___x_4145_ = v_reuseFailAlloc_4146_;
goto v_reusejp_4144_;
}
v_reusejp_4144_:
{
return v___x_4145_;
}
}
}
}
else
{
lean_object* v_a_4148_; lean_object* v___x_4150_; uint8_t v_isShared_4151_; uint8_t v_isSharedCheck_4155_; 
lean_dec_ref(v_docCtx_4113_);
lean_dec_ref(v_names_4112_);
v_a_4148_ = lean_ctor_get(v___x_4127_, 0);
v_isSharedCheck_4155_ = !lean_is_exclusive(v___x_4127_);
if (v_isSharedCheck_4155_ == 0)
{
v___x_4150_ = v___x_4127_;
v_isShared_4151_ = v_isSharedCheck_4155_;
goto v_resetjp_4149_;
}
else
{
lean_inc(v_a_4148_);
lean_dec(v___x_4127_);
v___x_4150_ = lean_box(0);
v_isShared_4151_ = v_isSharedCheck_4155_;
goto v_resetjp_4149_;
}
v_resetjp_4149_:
{
lean_object* v___x_4153_; 
if (v_isShared_4151_ == 0)
{
v___x_4153_ = v___x_4150_;
goto v_reusejp_4152_;
}
else
{
lean_object* v_reuseFailAlloc_4154_; 
v_reuseFailAlloc_4154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4154_, 0, v_a_4148_);
v___x_4153_ = v_reuseFailAlloc_4154_;
goto v_reusejp_4152_;
}
v_reusejp_4152_:
{
return v___x_4153_;
}
}
}
}
else
{
lean_object* v___x_4156_; 
lean_dec_ref(v_docCtx_4113_);
lean_dec_ref(v_names_4112_);
v___x_4156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4156_, 0, v_b_4117_);
return v___x_4156_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___boxed(lean_object* v_names_4157_, lean_object* v_docCtx_4158_, lean_object* v_as_4159_, lean_object* v_i_4160_, lean_object* v_stop_4161_, lean_object* v_b_4162_, lean_object* v___y_4163_, lean_object* v___y_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_){
_start:
{
size_t v_i_boxed_4170_; size_t v_stop_boxed_4171_; lean_object* v_res_4172_; 
v_i_boxed_4170_ = lean_unbox_usize(v_i_4160_);
lean_dec(v_i_4160_);
v_stop_boxed_4171_ = lean_unbox_usize(v_stop_4161_);
lean_dec(v_stop_4161_);
v_res_4172_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5(v_names_4157_, v_docCtx_4158_, v_as_4159_, v_i_boxed_4170_, v_stop_boxed_4171_, v_b_4162_, v___y_4163_, v___y_4164_, v___y_4165_, v___y_4166_, v___y_4167_, v___y_4168_);
lean_dec(v___y_4168_);
lean_dec_ref(v___y_4167_);
lean_dec(v___y_4166_);
lean_dec_ref(v___y_4165_);
lean_dec(v___y_4164_);
lean_dec_ref(v___y_4163_);
lean_dec_ref(v_as_4159_);
return v_res_4172_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4___redArg(lean_object* v_as_4173_, size_t v_sz_4174_, size_t v_i_4175_, lean_object* v_b_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_, lean_object* v___y_4180_){
_start:
{
uint8_t v___x_4182_; 
v___x_4182_ = lean_usize_dec_lt(v_i_4175_, v_sz_4174_);
if (v___x_4182_ == 0)
{
lean_object* v___x_4183_; 
v___x_4183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4183_, 0, v_b_4176_);
return v___x_4183_;
}
else
{
lean_object* v_array_4184_; lean_object* v_start_4185_; lean_object* v_stop_4186_; uint8_t v___x_4187_; 
v_array_4184_ = lean_ctor_get(v_b_4176_, 0);
v_start_4185_ = lean_ctor_get(v_b_4176_, 1);
v_stop_4186_ = lean_ctor_get(v_b_4176_, 2);
v___x_4187_ = lean_nat_dec_lt(v_start_4185_, v_stop_4186_);
if (v___x_4187_ == 0)
{
lean_object* v___x_4188_; 
v___x_4188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4188_, 0, v_b_4176_);
return v___x_4188_;
}
else
{
lean_object* v___x_4190_; uint8_t v_isShared_4191_; uint8_t v_isSharedCheck_4211_; 
lean_inc(v_stop_4186_);
lean_inc(v_start_4185_);
lean_inc_ref(v_array_4184_);
v_isSharedCheck_4211_ = !lean_is_exclusive(v_b_4176_);
if (v_isSharedCheck_4211_ == 0)
{
lean_object* v_unused_4212_; lean_object* v_unused_4213_; lean_object* v_unused_4214_; 
v_unused_4212_ = lean_ctor_get(v_b_4176_, 2);
lean_dec(v_unused_4212_);
v_unused_4213_ = lean_ctor_get(v_b_4176_, 1);
lean_dec(v_unused_4213_);
v_unused_4214_ = lean_ctor_get(v_b_4176_, 0);
lean_dec(v_unused_4214_);
v___x_4190_ = v_b_4176_;
v_isShared_4191_ = v_isSharedCheck_4211_;
goto v_resetjp_4189_;
}
else
{
lean_dec(v_b_4176_);
v___x_4190_ = lean_box(0);
v_isShared_4191_ = v_isSharedCheck_4211_;
goto v_resetjp_4189_;
}
v_resetjp_4189_:
{
lean_object* v_a_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4197_; 
v_a_4192_ = lean_array_uget_borrowed(v_as_4173_, v_i_4175_);
v___x_4193_ = lean_array_fget(v_array_4184_, v_start_4185_);
v___x_4194_ = lean_unsigned_to_nat(1u);
v___x_4195_ = lean_nat_add(v_start_4185_, v___x_4194_);
lean_dec(v_start_4185_);
if (v_isShared_4191_ == 0)
{
lean_ctor_set(v___x_4190_, 1, v___x_4195_);
v___x_4197_ = v___x_4190_;
goto v_reusejp_4196_;
}
else
{
lean_object* v_reuseFailAlloc_4210_; 
v_reuseFailAlloc_4210_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4210_, 0, v_array_4184_);
lean_ctor_set(v_reuseFailAlloc_4210_, 1, v___x_4195_);
lean_ctor_set(v_reuseFailAlloc_4210_, 2, v_stop_4186_);
v___x_4197_ = v_reuseFailAlloc_4210_;
goto v_reusejp_4196_;
}
v_reusejp_4196_:
{
lean_object* v___x_4198_; 
lean_inc(v_a_4192_);
v___x_4198_ = l_Lean_Elab_Structural_reportTermMeasure(v___x_4193_, v_a_4192_, v___y_4177_, v___y_4178_, v___y_4179_, v___y_4180_);
if (lean_obj_tag(v___x_4198_) == 0)
{
size_t v___x_4199_; size_t v___x_4200_; 
lean_dec_ref_known(v___x_4198_, 1);
v___x_4199_ = ((size_t)1ULL);
v___x_4200_ = lean_usize_add(v_i_4175_, v___x_4199_);
v_i_4175_ = v___x_4200_;
v_b_4176_ = v___x_4197_;
goto _start;
}
else
{
lean_object* v_a_4202_; lean_object* v___x_4204_; uint8_t v_isShared_4205_; uint8_t v_isSharedCheck_4209_; 
lean_dec_ref(v___x_4197_);
v_a_4202_ = lean_ctor_get(v___x_4198_, 0);
v_isSharedCheck_4209_ = !lean_is_exclusive(v___x_4198_);
if (v_isSharedCheck_4209_ == 0)
{
v___x_4204_ = v___x_4198_;
v_isShared_4205_ = v_isSharedCheck_4209_;
goto v_resetjp_4203_;
}
else
{
lean_inc(v_a_4202_);
lean_dec(v___x_4198_);
v___x_4204_ = lean_box(0);
v_isShared_4205_ = v_isSharedCheck_4209_;
goto v_resetjp_4203_;
}
v_resetjp_4203_:
{
lean_object* v___x_4207_; 
if (v_isShared_4205_ == 0)
{
v___x_4207_ = v___x_4204_;
goto v_reusejp_4206_;
}
else
{
lean_object* v_reuseFailAlloc_4208_; 
v_reuseFailAlloc_4208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4208_, 0, v_a_4202_);
v___x_4207_ = v_reuseFailAlloc_4208_;
goto v_reusejp_4206_;
}
v_reusejp_4206_:
{
return v___x_4207_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4___redArg___boxed(lean_object* v_as_4215_, lean_object* v_sz_4216_, lean_object* v_i_4217_, lean_object* v_b_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_){
_start:
{
size_t v_sz_boxed_4224_; size_t v_i_boxed_4225_; lean_object* v_res_4226_; 
v_sz_boxed_4224_ = lean_unbox_usize(v_sz_4216_);
lean_dec(v_sz_4216_);
v_i_boxed_4225_ = lean_unbox_usize(v_i_4217_);
lean_dec(v_i_4217_);
v_res_4226_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4___redArg(v_as_4215_, v_sz_boxed_4224_, v_i_boxed_4225_, v_b_4218_, v___y_4219_, v___y_4220_, v___y_4221_, v___y_4222_);
lean_dec(v___y_4222_);
lean_dec_ref(v___y_4221_);
lean_dec(v___y_4220_);
lean_dec_ref(v___y_4219_);
lean_dec_ref(v_as_4215_);
return v_res_4226_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___redArg(size_t v_sz_4227_, size_t v_i_4228_, lean_object* v_bs_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_){
_start:
{
uint8_t v___x_4233_; 
v___x_4233_ = lean_usize_dec_lt(v_i_4228_, v_sz_4227_);
if (v___x_4233_ == 0)
{
lean_object* v___x_4234_; 
v___x_4234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4234_, 0, v_bs_4229_);
return v___x_4234_;
}
else
{
lean_object* v_v_4235_; lean_object* v___x_4236_; lean_object* v_bs_x27_4237_; lean_object* v___x_4238_; 
v_v_4235_ = lean_array_uget(v_bs_4229_, v_i_4228_);
v___x_4236_ = lean_unsigned_to_nat(0u);
v_bs_x27_4237_ = lean_array_uset(v_bs_4229_, v_i_4228_, v___x_4236_);
v___x_4238_ = l_Lean_Elab_eraseRecAppSyntax(v_v_4235_, v___y_4230_, v___y_4231_);
if (lean_obj_tag(v___x_4238_) == 0)
{
lean_object* v_a_4239_; size_t v___x_4240_; size_t v___x_4241_; lean_object* v___x_4242_; 
v_a_4239_ = lean_ctor_get(v___x_4238_, 0);
lean_inc(v_a_4239_);
lean_dec_ref_known(v___x_4238_, 1);
v___x_4240_ = ((size_t)1ULL);
v___x_4241_ = lean_usize_add(v_i_4228_, v___x_4240_);
v___x_4242_ = lean_array_uset(v_bs_x27_4237_, v_i_4228_, v_a_4239_);
v_i_4228_ = v___x_4241_;
v_bs_4229_ = v___x_4242_;
goto _start;
}
else
{
lean_object* v_a_4244_; lean_object* v___x_4246_; uint8_t v_isShared_4247_; uint8_t v_isSharedCheck_4251_; 
lean_dec_ref(v_bs_x27_4237_);
v_a_4244_ = lean_ctor_get(v___x_4238_, 0);
v_isSharedCheck_4251_ = !lean_is_exclusive(v___x_4238_);
if (v_isSharedCheck_4251_ == 0)
{
v___x_4246_ = v___x_4238_;
v_isShared_4247_ = v_isSharedCheck_4251_;
goto v_resetjp_4245_;
}
else
{
lean_inc(v_a_4244_);
lean_dec(v___x_4238_);
v___x_4246_ = lean_box(0);
v_isShared_4247_ = v_isSharedCheck_4251_;
goto v_resetjp_4245_;
}
v_resetjp_4245_:
{
lean_object* v___x_4249_; 
if (v_isShared_4247_ == 0)
{
v___x_4249_ = v___x_4246_;
goto v_reusejp_4248_;
}
else
{
lean_object* v_reuseFailAlloc_4250_; 
v_reuseFailAlloc_4250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4250_, 0, v_a_4244_);
v___x_4249_ = v_reuseFailAlloc_4250_;
goto v_reusejp_4248_;
}
v_reusejp_4248_:
{
return v___x_4249_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___redArg___boxed(lean_object* v_sz_4252_, lean_object* v_i_4253_, lean_object* v_bs_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_){
_start:
{
size_t v_sz_boxed_4258_; size_t v_i_boxed_4259_; lean_object* v_res_4260_; 
v_sz_boxed_4258_ = lean_unbox_usize(v_sz_4252_);
lean_dec(v_sz_4252_);
v_i_boxed_4259_ = lean_unbox_usize(v_i_4253_);
lean_dec(v_i_4253_);
v_res_4260_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___redArg(v_sz_boxed_4258_, v_i_boxed_4259_, v_bs_4254_, v___y_4255_, v___y_4256_);
lean_dec(v___y_4256_);
lean_dec_ref(v___y_4255_);
return v_res_4260_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___redArg(lean_object* v_as_4261_, size_t v_sz_4262_, size_t v_i_4263_, lean_object* v_b_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_){
_start:
{
uint8_t v___x_4268_; 
v___x_4268_ = lean_usize_dec_lt(v_i_4263_, v_sz_4262_);
if (v___x_4268_ == 0)
{
lean_object* v___x_4269_; 
v___x_4269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4269_, 0, v_b_4264_);
return v___x_4269_;
}
else
{
lean_object* v_a_4270_; lean_object* v_declName_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; 
v_a_4270_ = lean_array_uget_borrowed(v_as_4261_, v_i_4263_);
v_declName_4271_ = lean_ctor_get(v_a_4270_, 3);
v___x_4272_ = lean_box(0);
lean_inc(v_declName_4271_);
v___x_4273_ = l_Lean_enableRealizationsForConst(v_declName_4271_, v___y_4265_, v___y_4266_);
if (lean_obj_tag(v___x_4273_) == 0)
{
size_t v___x_4274_; size_t v___x_4275_; 
lean_dec_ref_known(v___x_4273_, 1);
v___x_4274_ = ((size_t)1ULL);
v___x_4275_ = lean_usize_add(v_i_4263_, v___x_4274_);
v_i_4263_ = v___x_4275_;
v_b_4264_ = v___x_4272_;
goto _start;
}
else
{
return v___x_4273_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___redArg___boxed(lean_object* v_as_4277_, lean_object* v_sz_4278_, lean_object* v_i_4279_, lean_object* v_b_4280_, lean_object* v___y_4281_, lean_object* v___y_4282_, lean_object* v___y_4283_){
_start:
{
size_t v_sz_boxed_4284_; size_t v_i_boxed_4285_; lean_object* v_res_4286_; 
v_sz_boxed_4284_ = lean_unbox_usize(v_sz_4278_);
lean_dec(v_sz_4278_);
v_i_boxed_4285_ = lean_unbox_usize(v_i_4279_);
lean_dec(v_i_4279_);
v_res_4286_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___redArg(v_as_4277_, v_sz_boxed_4284_, v_i_boxed_4285_, v_b_4280_, v___y_4281_, v___y_4282_);
lean_dec(v___y_4282_);
lean_dec_ref(v___y_4281_);
lean_dec_ref(v_as_4277_);
return v_res_4286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_structuralRecursion(lean_object* v_docCtx_4287_, lean_object* v_preDefs_4288_, lean_object* v_termMeasure_x3fs_4289_, lean_object* v_a_4290_, lean_object* v_a_4291_, lean_object* v_a_4292_, lean_object* v_a_4293_, lean_object* v_a_4294_, lean_object* v_a_4295_){
_start:
{
size_t v_sz_4297_; size_t v___x_4298_; lean_object* v_names_4299_; lean_object* v___x_4300_; 
v_sz_4297_ = lean_array_size(v_preDefs_4288_);
v___x_4298_ = ((size_t)0ULL);
lean_inc_ref_n(v_preDefs_4288_, 2);
v_names_4299_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16(v_sz_4297_, v___x_4298_, v_preDefs_4288_);
v___x_4300_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos(v_preDefs_4288_, v_termMeasure_x3fs_4289_, v_a_4292_, v_a_4293_, v_a_4294_, v_a_4295_);
if (lean_obj_tag(v___x_4300_) == 0)
{
lean_object* v_a_4301_; lean_object* v_snd_4302_; lean_object* v_fst_4303_; lean_object* v_fst_4304_; lean_object* v_snd_4305_; lean_object* v___x_4336_; lean_object* v___x_4337_; lean_object* v___x_4338_; size_t v_sz_4339_; lean_object* v___x_4340_; 
v_a_4301_ = lean_ctor_get(v___x_4300_, 0);
lean_inc(v_a_4301_);
lean_dec_ref_known(v___x_4300_, 1);
v_snd_4302_ = lean_ctor_get(v_a_4301_, 1);
lean_inc(v_snd_4302_);
v_fst_4303_ = lean_ctor_get(v_a_4301_, 0);
lean_inc(v_fst_4303_);
lean_dec(v_a_4301_);
v_fst_4304_ = lean_ctor_get(v_snd_4302_, 0);
lean_inc(v_fst_4304_);
v_snd_4305_ = lean_ctor_get(v_snd_4302_, 1);
lean_inc(v_snd_4305_);
lean_dec(v_snd_4302_);
v___x_4336_ = lean_unsigned_to_nat(0u);
v___x_4337_ = lean_array_get_size(v_preDefs_4288_);
lean_inc_ref(v_preDefs_4288_);
v___x_4338_ = l_Array_toSubarray___redArg(v_preDefs_4288_, v___x_4336_, v___x_4337_);
v_sz_4339_ = lean_array_size(v_fst_4303_);
v___x_4340_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4___redArg(v_fst_4303_, v_sz_4339_, v___x_4298_, v___x_4338_, v_a_4292_, v_a_4293_, v_a_4294_, v_a_4295_);
if (lean_obj_tag(v___x_4340_) == 0)
{
lean_object* v___x_4341_; uint8_t v___x_4342_; 
lean_dec_ref_known(v___x_4340_, 1);
v___x_4341_ = lean_array_get_size(v_fst_4304_);
v___x_4342_ = lean_nat_dec_lt(v___x_4336_, v___x_4341_);
if (v___x_4342_ == 0)
{
lean_dec_ref(v_names_4299_);
goto v___jp_4306_;
}
else
{
lean_object* v___x_4343_; size_t v___x_4344_; lean_object* v___x_4345_; 
v___x_4343_ = lean_box(0);
v___x_4344_ = lean_usize_of_nat(v___x_4341_);
lean_inc_ref(v_docCtx_4287_);
v___x_4345_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5(v_names_4299_, v_docCtx_4287_, v_fst_4304_, v___x_4298_, v___x_4344_, v___x_4343_, v_a_4290_, v_a_4291_, v_a_4292_, v_a_4293_, v_a_4294_, v_a_4295_);
if (lean_obj_tag(v___x_4345_) == 0)
{
lean_dec_ref_known(v___x_4345_, 1);
goto v___jp_4306_;
}
else
{
lean_dec(v_snd_4305_);
lean_dec(v_fst_4304_);
lean_dec(v_fst_4303_);
lean_dec_ref(v_preDefs_4288_);
lean_dec_ref(v_docCtx_4287_);
return v___x_4345_;
}
}
}
else
{
lean_object* v_a_4346_; lean_object* v___x_4348_; uint8_t v_isShared_4349_; uint8_t v_isSharedCheck_4353_; 
lean_dec(v_snd_4305_);
lean_dec(v_fst_4304_);
lean_dec(v_fst_4303_);
lean_dec_ref(v_names_4299_);
lean_dec_ref(v_preDefs_4288_);
lean_dec_ref(v_docCtx_4287_);
v_a_4346_ = lean_ctor_get(v___x_4340_, 0);
v_isSharedCheck_4353_ = !lean_is_exclusive(v___x_4340_);
if (v_isSharedCheck_4353_ == 0)
{
v___x_4348_ = v___x_4340_;
v_isShared_4349_ = v_isSharedCheck_4353_;
goto v_resetjp_4347_;
}
else
{
lean_inc(v_a_4346_);
lean_dec(v___x_4340_);
v___x_4348_ = lean_box(0);
v_isShared_4349_ = v_isSharedCheck_4353_;
goto v_resetjp_4347_;
}
v_resetjp_4347_:
{
lean_object* v___x_4351_; 
if (v_isShared_4349_ == 0)
{
v___x_4351_ = v___x_4348_;
goto v_reusejp_4350_;
}
else
{
lean_object* v_reuseFailAlloc_4352_; 
v_reuseFailAlloc_4352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4352_, 0, v_a_4346_);
v___x_4351_ = v_reuseFailAlloc_4352_;
goto v_reusejp_4350_;
}
v_reusejp_4350_:
{
return v___x_4351_;
}
}
}
v___jp_4306_:
{
lean_object* v___x_4307_; 
v___x_4307_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___redArg(v_sz_4297_, v___x_4298_, v_preDefs_4288_, v_a_4294_, v_a_4295_);
if (lean_obj_tag(v___x_4307_) == 0)
{
lean_object* v_a_4308_; lean_object* v___x_4309_; 
v_a_4308_ = lean_ctor_get(v___x_4307_, 0);
lean_inc_n(v_a_4308_, 2);
lean_dec_ref_known(v___x_4307_, 1);
lean_inc_ref(v_docCtx_4287_);
v___x_4309_ = l_Lean_Elab_addAndCompilePartialRec(v_docCtx_4287_, v_a_4308_, v_a_4290_, v_a_4291_, v_a_4292_, v_a_4293_, v_a_4294_, v_a_4295_);
if (lean_obj_tag(v___x_4309_) == 0)
{
lean_object* v___x_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; size_t v_sz_4313_; lean_object* v___x_4314_; 
lean_dec_ref_known(v___x_4309_, 1);
v___x_4310_ = lean_unsigned_to_nat(0u);
v___x_4311_ = lean_array_get_size(v_fst_4303_);
lean_inc(v_fst_4303_);
v___x_4312_ = l_Array_toSubarray___redArg(v_fst_4303_, v___x_4310_, v___x_4311_);
v_sz_4313_ = lean_array_size(v_a_4308_);
lean_inc(v_a_4308_);
v___x_4314_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__1(v_a_4308_, v_fst_4303_, v_docCtx_4287_, v_snd_4305_, v_a_4308_, v_sz_4313_, v___x_4298_, v___x_4312_, v_a_4290_, v_a_4291_, v_a_4292_, v_a_4293_, v_a_4294_, v_a_4295_);
lean_dec(v_fst_4303_);
if (lean_obj_tag(v___x_4314_) == 0)
{
lean_object* v___x_4315_; lean_object* v___x_4316_; 
lean_dec_ref_known(v___x_4314_, 1);
v___x_4315_ = lean_box(0);
v___x_4316_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___redArg(v_a_4308_, v_sz_4313_, v___x_4298_, v___x_4315_, v_a_4292_, v_a_4293_, v_a_4294_, v_a_4295_);
if (lean_obj_tag(v___x_4316_) == 0)
{
lean_object* v___x_4317_; 
lean_dec_ref_known(v___x_4316_, 1);
v___x_4317_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___redArg(v_a_4308_, v_sz_4313_, v___x_4298_, v___x_4315_, v_a_4294_, v_a_4295_);
lean_dec(v_a_4308_);
if (lean_obj_tag(v___x_4317_) == 0)
{
uint8_t v___x_4318_; lean_object* v___x_4319_; 
lean_dec_ref_known(v___x_4317_, 1);
v___x_4318_ = 1;
v___x_4319_ = l_Lean_Elab_applyAttributesOf(v_fst_4304_, v___x_4318_, v_a_4290_, v_a_4291_, v_a_4292_, v_a_4293_, v_a_4294_, v_a_4295_);
lean_dec(v_fst_4304_);
return v___x_4319_;
}
else
{
lean_dec(v_fst_4304_);
return v___x_4317_;
}
}
else
{
lean_dec(v_a_4308_);
lean_dec(v_fst_4304_);
return v___x_4316_;
}
}
else
{
lean_object* v_a_4320_; lean_object* v___x_4322_; uint8_t v_isShared_4323_; uint8_t v_isSharedCheck_4327_; 
lean_dec(v_a_4308_);
lean_dec(v_fst_4304_);
v_a_4320_ = lean_ctor_get(v___x_4314_, 0);
v_isSharedCheck_4327_ = !lean_is_exclusive(v___x_4314_);
if (v_isSharedCheck_4327_ == 0)
{
v___x_4322_ = v___x_4314_;
v_isShared_4323_ = v_isSharedCheck_4327_;
goto v_resetjp_4321_;
}
else
{
lean_inc(v_a_4320_);
lean_dec(v___x_4314_);
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
}
else
{
lean_dec(v_a_4308_);
lean_dec(v_snd_4305_);
lean_dec(v_fst_4304_);
lean_dec(v_fst_4303_);
lean_dec_ref(v_docCtx_4287_);
return v___x_4309_;
}
}
else
{
lean_object* v_a_4328_; lean_object* v___x_4330_; uint8_t v_isShared_4331_; uint8_t v_isSharedCheck_4335_; 
lean_dec(v_snd_4305_);
lean_dec(v_fst_4304_);
lean_dec(v_fst_4303_);
lean_dec_ref(v_docCtx_4287_);
v_a_4328_ = lean_ctor_get(v___x_4307_, 0);
v_isSharedCheck_4335_ = !lean_is_exclusive(v___x_4307_);
if (v_isSharedCheck_4335_ == 0)
{
v___x_4330_ = v___x_4307_;
v_isShared_4331_ = v_isSharedCheck_4335_;
goto v_resetjp_4329_;
}
else
{
lean_inc(v_a_4328_);
lean_dec(v___x_4307_);
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
else
{
lean_object* v_a_4354_; lean_object* v___x_4356_; uint8_t v_isShared_4357_; uint8_t v_isSharedCheck_4361_; 
lean_dec_ref(v_names_4299_);
lean_dec_ref(v_preDefs_4288_);
lean_dec_ref(v_docCtx_4287_);
v_a_4354_ = lean_ctor_get(v___x_4300_, 0);
v_isSharedCheck_4361_ = !lean_is_exclusive(v___x_4300_);
if (v_isSharedCheck_4361_ == 0)
{
v___x_4356_ = v___x_4300_;
v_isShared_4357_ = v_isSharedCheck_4361_;
goto v_resetjp_4355_;
}
else
{
lean_inc(v_a_4354_);
lean_dec(v___x_4300_);
v___x_4356_ = lean_box(0);
v_isShared_4357_ = v_isSharedCheck_4361_;
goto v_resetjp_4355_;
}
v_resetjp_4355_:
{
lean_object* v___x_4359_; 
if (v_isShared_4357_ == 0)
{
v___x_4359_ = v___x_4356_;
goto v_reusejp_4358_;
}
else
{
lean_object* v_reuseFailAlloc_4360_; 
v_reuseFailAlloc_4360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4360_, 0, v_a_4354_);
v___x_4359_ = v_reuseFailAlloc_4360_;
goto v_reusejp_4358_;
}
v_reusejp_4358_:
{
return v___x_4359_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_structuralRecursion___boxed(lean_object* v_docCtx_4362_, lean_object* v_preDefs_4363_, lean_object* v_termMeasure_x3fs_4364_, lean_object* v_a_4365_, lean_object* v_a_4366_, lean_object* v_a_4367_, lean_object* v_a_4368_, lean_object* v_a_4369_, lean_object* v_a_4370_, lean_object* v_a_4371_){
_start:
{
lean_object* v_res_4372_; 
v_res_4372_ = l_Lean_Elab_Structural_structuralRecursion(v_docCtx_4362_, v_preDefs_4363_, v_termMeasure_x3fs_4364_, v_a_4365_, v_a_4366_, v_a_4367_, v_a_4368_, v_a_4369_, v_a_4370_);
lean_dec(v_a_4370_);
lean_dec_ref(v_a_4369_);
lean_dec(v_a_4368_);
lean_dec_ref(v_a_4367_);
lean_dec(v_a_4366_);
lean_dec_ref(v_a_4365_);
return v_res_4372_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0(size_t v_sz_4373_, size_t v_i_4374_, lean_object* v_bs_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_, lean_object* v___y_4378_, lean_object* v___y_4379_, lean_object* v___y_4380_, lean_object* v___y_4381_){
_start:
{
lean_object* v___x_4383_; 
v___x_4383_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___redArg(v_sz_4373_, v_i_4374_, v_bs_4375_, v___y_4380_, v___y_4381_);
return v___x_4383_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___boxed(lean_object* v_sz_4384_, lean_object* v_i_4385_, lean_object* v_bs_4386_, lean_object* v___y_4387_, lean_object* v___y_4388_, lean_object* v___y_4389_, lean_object* v___y_4390_, lean_object* v___y_4391_, lean_object* v___y_4392_, lean_object* v___y_4393_){
_start:
{
size_t v_sz_boxed_4394_; size_t v_i_boxed_4395_; lean_object* v_res_4396_; 
v_sz_boxed_4394_ = lean_unbox_usize(v_sz_4384_);
lean_dec(v_sz_4384_);
v_i_boxed_4395_ = lean_unbox_usize(v_i_4385_);
lean_dec(v_i_4385_);
v_res_4396_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0(v_sz_boxed_4394_, v_i_boxed_4395_, v_bs_4386_, v___y_4387_, v___y_4388_, v___y_4389_, v___y_4390_, v___y_4391_, v___y_4392_);
lean_dec(v___y_4392_);
lean_dec_ref(v___y_4391_);
lean_dec(v___y_4390_);
lean_dec_ref(v___y_4389_);
lean_dec(v___y_4388_);
lean_dec_ref(v___y_4387_);
return v_res_4396_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2(lean_object* v_as_4397_, size_t v_sz_4398_, size_t v_i_4399_, lean_object* v_b_4400_, lean_object* v___y_4401_, lean_object* v___y_4402_, lean_object* v___y_4403_, lean_object* v___y_4404_, lean_object* v___y_4405_, lean_object* v___y_4406_){
_start:
{
lean_object* v___x_4408_; 
v___x_4408_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___redArg(v_as_4397_, v_sz_4398_, v_i_4399_, v_b_4400_, v___y_4403_, v___y_4404_, v___y_4405_, v___y_4406_);
return v___x_4408_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___boxed(lean_object* v_as_4409_, lean_object* v_sz_4410_, lean_object* v_i_4411_, lean_object* v_b_4412_, lean_object* v___y_4413_, lean_object* v___y_4414_, lean_object* v___y_4415_, lean_object* v___y_4416_, lean_object* v___y_4417_, lean_object* v___y_4418_, lean_object* v___y_4419_){
_start:
{
size_t v_sz_boxed_4420_; size_t v_i_boxed_4421_; lean_object* v_res_4422_; 
v_sz_boxed_4420_ = lean_unbox_usize(v_sz_4410_);
lean_dec(v_sz_4410_);
v_i_boxed_4421_ = lean_unbox_usize(v_i_4411_);
lean_dec(v_i_4411_);
v_res_4422_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2(v_as_4409_, v_sz_boxed_4420_, v_i_boxed_4421_, v_b_4412_, v___y_4413_, v___y_4414_, v___y_4415_, v___y_4416_, v___y_4417_, v___y_4418_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3(lean_object* v_as_4423_, size_t v_sz_4424_, size_t v_i_4425_, lean_object* v_b_4426_, lean_object* v___y_4427_, lean_object* v___y_4428_, lean_object* v___y_4429_, lean_object* v___y_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_){
_start:
{
lean_object* v___x_4434_; 
v___x_4434_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___redArg(v_as_4423_, v_sz_4424_, v_i_4425_, v_b_4426_, v___y_4431_, v___y_4432_);
return v___x_4434_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___boxed(lean_object* v_as_4435_, lean_object* v_sz_4436_, lean_object* v_i_4437_, lean_object* v_b_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_, lean_object* v___y_4441_, lean_object* v___y_4442_, lean_object* v___y_4443_, lean_object* v___y_4444_, lean_object* v___y_4445_){
_start:
{
size_t v_sz_boxed_4446_; size_t v_i_boxed_4447_; lean_object* v_res_4448_; 
v_sz_boxed_4446_ = lean_unbox_usize(v_sz_4436_);
lean_dec(v_sz_4436_);
v_i_boxed_4447_ = lean_unbox_usize(v_i_4437_);
lean_dec(v_i_4437_);
v_res_4448_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3(v_as_4435_, v_sz_boxed_4446_, v_i_boxed_4447_, v_b_4438_, v___y_4439_, v___y_4440_, v___y_4441_, v___y_4442_, v___y_4443_, v___y_4444_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4(lean_object* v_as_4449_, size_t v_sz_4450_, size_t v_i_4451_, lean_object* v_b_4452_, lean_object* v___y_4453_, lean_object* v___y_4454_, lean_object* v___y_4455_, lean_object* v___y_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_){
_start:
{
lean_object* v___x_4460_; 
v___x_4460_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4___redArg(v_as_4449_, v_sz_4450_, v_i_4451_, v_b_4452_, v___y_4455_, v___y_4456_, v___y_4457_, v___y_4458_);
return v___x_4460_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4___boxed(lean_object* v_as_4461_, lean_object* v_sz_4462_, lean_object* v_i_4463_, lean_object* v_b_4464_, lean_object* v___y_4465_, lean_object* v___y_4466_, lean_object* v___y_4467_, lean_object* v___y_4468_, lean_object* v___y_4469_, lean_object* v___y_4470_, lean_object* v___y_4471_){
_start:
{
size_t v_sz_boxed_4472_; size_t v_i_boxed_4473_; lean_object* v_res_4474_; 
v_sz_boxed_4472_ = lean_unbox_usize(v_sz_4462_);
lean_dec(v_sz_4462_);
v_i_boxed_4473_ = lean_unbox_usize(v_i_4463_);
lean_dec(v_i_4463_);
v_res_4474_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4(v_as_4461_, v_sz_boxed_4472_, v_i_boxed_4473_, v_b_4464_, v___y_4465_, v___y_4466_, v___y_4467_, v___y_4468_, v___y_4469_, v___y_4470_);
lean_dec(v___y_4470_);
lean_dec_ref(v___y_4469_);
lean_dec(v___y_4468_);
lean_dec_ref(v___y_4467_);
lean_dec(v___y_4466_);
lean_dec_ref(v___y_4465_);
lean_dec_ref(v_as_4461_);
return v_res_4474_;
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
