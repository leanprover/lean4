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
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_mkBRecOnF(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_mkIndPredBRecOnF(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Lean_Elab_Structural_mkBRecOnApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Elab_TerminationMeasure_delab(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVarOf(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_instMonadEST(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
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
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_Elab_Structural_RecArgInfo_indicesAndRecArgPos(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Elab_FixedParamPerm_instantiateLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Structural_instInhabitedRecArgInfo_default;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isInductiveCore_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_PProdN_mkLambdas(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_InductiveVal_numTypeFormers(lean_object*);
lean_object* l_Array_range(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Nat_blt___boxed(lean_object*, lean_object*);
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInductivePredicate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_zip___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_FixedParamPerm_buildArgs___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_beta(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferArgumentTypesN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_Positions_numIndices(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_mkBRecOnConst(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_mkBRecOnMotive(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_mkIndPredBRecOnMotive(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_withFunTypes___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Elab_addNonRec(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalInstances___redArg(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* lean_local_ctx_erase(lean_object*, lean_object*);
lean_object* l_Lean_Elab_FixedParamPerms_erase(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_tryAllArgs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_addSmartUnfoldingDef(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_DefKind_isTheorem(uint8_t);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_abstractNestedProofs(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_registerEqnsInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_preprocess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getFixedParamPerms(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addAsAxiom___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_enableRealizationsForConst(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_generateEagerEqns(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_eraseRecAppSyntax(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_instInhabitedPreDefinition_default;
lean_object* l_Lean_Environment_unlockAsync(lean_object*);
lean_object* l_Lean_Elab_Structural_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addAndCompilePartialRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_applyAttributesOf(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Meta_mapErrorImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__14___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__16___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__0;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9___redArg___closed__0;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Nat_blt___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__11(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8_spec__9___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8_spec__9___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8_spec__9___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8_spec__9___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__7___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__7___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__7(lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "Lean.Elab.Structural.Positions.groupAndSort"};
static const lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___redArg___closed__0_value;
static const lean_string_object l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "assertion violation: Array.range xs.size == positions.flatten.qsort Nat.blt\n  "};
static const lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___redArg___closed__2;
static const lean_array_object l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___redArg___closed__3 = (const lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__15(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___closed__0 = (const lean_object*)&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___closed__0_value;
static lean_once_cell_t l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___closed__1;
static const lean_string_object l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "` is not an inductive type"};
static const lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___closed__2 = (const lean_object*)&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___closed__2_value;
static lean_once_cell_t l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___closed__3;
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__4 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__4_value;
static const lean_closure_object l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___boxed(lean_object**);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__14(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___redArg___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___redArg___closed__0 = (const lean_object*)&l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___redArg___closed__0_value;
static lean_once_cell_t l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___redArg___closed__1;
static lean_once_cell_t l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__14_spec__17_spec__24(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5_spec__5_spec__8(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5_spec__7(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5_spec__6___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5_spec__6___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5_spec__8(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 61, .m_capacity = 61, .m_length = 60, .m_data = "its type is an inductive datatype and the datatype parameter"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "\ndepends on the function parameter"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7___closed__3;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 137, .m_capacity = 137, .m_length = 136, .m_data = "\nwhich cannot be fixed as it is an index or depends on an index, and indices cannot be fixed parameters when using structural recursion."};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7___closed__4_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7___closed__5;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__2(lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__14___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__3___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + sizeof(size_t)*1, .m_other = 0, .m_tag = 0}, .m_objs = {(lean_object*)(size_t)(0ULL)}};
LEAN_EXPORT const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__3___boxed__const__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__3___boxed__const__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__15_spec__21___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__15_spec__21___redArg___closed__0;
static lean_once_cell_t l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__15_spec__21___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__15_spec__21___redArg___closed__1;
static lean_once_cell_t l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__15_spec__21___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__15_spec__21___redArg___closed__2;
static lean_once_cell_t l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__15_spec__21___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__15_spec__21___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__15_spec__21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__15_spec__21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__15(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__14(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__15_spec__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__15_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_reportTermMeasure_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_reportTermMeasure_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_reportTermMeasure_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_reportTermMeasure_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_reportTermMeasure_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_reportTermMeasure_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_Structural_structuralRecursion___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Structural_structuralRecursion___closed__0 = (const lean_object*)&l_Lean_Elab_Structural_structuralRecursion___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_structuralRecursion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_structuralRecursion___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg___lam__0(lean_object* v_k_1_, lean_object* v___y_2_, lean_object* v_b_3_, lean_object* v_c_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = lean_apply_8(v_k_1_, v_b_3_, v_c_4_, v___y_2_, v___y_5_, v___y_6_, v___y_7_, v___y_8_, lean_box(0));
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg___lam__0___boxed(lean_object* v_k_11_, lean_object* v___y_12_, lean_object* v_b_13_, lean_object* v_c_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg___lam__0(v_k_11_, v___y_12_, v_b_13_, v_c_14_, v___y_15_, v___y_16_, v___y_17_, v___y_18_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg(lean_object* v_e_21_, lean_object* v_k_22_, uint8_t v_cleanupAnnotations_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_){
_start:
{
lean_object* v___f_30_; uint8_t v___x_31_; uint8_t v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; 
v___f_30_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg___lam__0___boxed), 9, 2);
lean_closure_set(v___f_30_, 0, v_k_22_);
lean_closure_set(v___f_30_, 1, v___y_24_);
v___x_31_ = 1;
v___x_32_ = 0;
v___x_33_ = lean_box(0);
v___x_34_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_21_, v___x_31_, v___x_32_, v___x_31_, v___x_32_, v___x_33_, v___f_30_, v_cleanupAnnotations_23_, v___y_25_, v___y_26_, v___y_27_, v___y_28_);
if (lean_obj_tag(v___x_34_) == 0)
{
return v___x_34_;
}
else
{
lean_object* v_a_35_; lean_object* v___x_37_; uint8_t v_isShared_38_; uint8_t v_isSharedCheck_42_; 
v_a_35_ = lean_ctor_get(v___x_34_, 0);
v_isSharedCheck_42_ = !lean_is_exclusive(v___x_34_);
if (v_isSharedCheck_42_ == 0)
{
v___x_37_ = v___x_34_;
v_isShared_38_ = v_isSharedCheck_42_;
goto v_resetjp_36_;
}
else
{
lean_inc(v_a_35_);
lean_dec(v___x_34_);
v___x_37_ = lean_box(0);
v_isShared_38_ = v_isSharedCheck_42_;
goto v_resetjp_36_;
}
v_resetjp_36_:
{
lean_object* v___x_40_; 
if (v_isShared_38_ == 0)
{
v___x_40_ = v___x_37_;
goto v_reusejp_39_;
}
else
{
lean_object* v_reuseFailAlloc_41_; 
v_reuseFailAlloc_41_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_41_, 0, v_a_35_);
v___x_40_ = v_reuseFailAlloc_41_;
goto v_reusejp_39_;
}
v_reusejp_39_:
{
return v___x_40_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg___boxed(lean_object* v_e_43_, lean_object* v_k_44_, lean_object* v_cleanupAnnotations_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_52_; lean_object* v_res_53_; 
v_cleanupAnnotations_boxed_52_ = lean_unbox(v_cleanupAnnotations_45_);
v_res_53_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg(v_e_43_, v_k_44_, v_cleanupAnnotations_boxed_52_, v___y_46_, v___y_47_, v___y_48_, v___y_49_, v___y_50_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1(lean_object* v_00_u03b1_54_, lean_object* v_e_55_, lean_object* v_k_56_, uint8_t v_cleanupAnnotations_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg(v_e_55_, v_k_56_, v_cleanupAnnotations_57_, v___y_58_, v___y_59_, v___y_60_, v___y_61_, v___y_62_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___boxed(lean_object* v_00_u03b1_65_, lean_object* v_e_66_, lean_object* v_k_67_, lean_object* v_cleanupAnnotations_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_75_; lean_object* v_res_76_; 
v_cleanupAnnotations_boxed_75_ = lean_unbox(v_cleanupAnnotations_68_);
v_res_76_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1(v_00_u03b1_65_, v_e_66_, v_k_67_, v_cleanupAnnotations_boxed_75_, v___y_69_, v___y_70_, v___y_71_, v___y_72_, v___y_73_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___redArg(lean_object* v_cls_80_, lean_object* v___y_81_){
_start:
{
lean_object* v_options_83_; uint8_t v_hasTrace_84_; 
v_options_83_ = lean_ctor_get(v___y_81_, 2);
v_hasTrace_84_ = lean_ctor_get_uint8(v_options_83_, sizeof(void*)*1);
if (v_hasTrace_84_ == 0)
{
lean_object* v___x_85_; lean_object* v___x_86_; 
lean_dec(v_cls_80_);
v___x_85_ = lean_box(v_hasTrace_84_);
v___x_86_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_86_, 0, v___x_85_);
return v___x_86_;
}
else
{
lean_object* v_inheritedTraceOptions_87_; lean_object* v___x_88_; lean_object* v___x_89_; uint8_t v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v_inheritedTraceOptions_87_ = lean_ctor_get(v___y_81_, 13);
v___x_88_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___redArg___closed__1));
v___x_89_ = l_Lean_Name_append(v___x_88_, v_cls_80_);
v___x_90_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_87_, v_options_83_, v___x_89_);
lean_dec(v___x_89_);
v___x_91_ = lean_box(v___x_90_);
v___x_92_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_92_, 0, v___x_91_);
return v___x_92_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___redArg___boxed(lean_object* v_cls_93_, lean_object* v___y_94_, lean_object* v___y_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___redArg(v_cls_93_, v___y_94_);
lean_dec_ref(v___y_94_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4(lean_object* v_cls_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___redArg(v_cls_97_, v___y_101_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___boxed(lean_object* v_cls_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4(v_cls_105_, v___y_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_);
lean_dec(v___y_110_);
lean_dec_ref(v___y_109_);
lean_dec(v___y_108_);
lean_dec_ref(v___y_107_);
lean_dec(v___y_106_);
return v_res_112_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0(lean_object* v_x_113_){
_start:
{
lean_object* v_indIdx_114_; 
v_indIdx_114_ = lean_ctor_get(v_x_113_, 5);
lean_inc(v_indIdx_114_);
return v_indIdx_114_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0___boxed(lean_object* v_x_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0(v_x_115_);
lean_dec_ref(v_x_115_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1(lean_object* v_x1_117_, lean_object* v_x2_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_){
_start:
{
lean_object* v___x_125_; 
v___x_125_ = l_Lean_Meta_PProdN_mkLambdas(v_x1_117_, v_x2_118_, v___y_120_, v___y_121_, v___y_122_, v___y_123_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___boxed(lean_object* v_x1_126_, lean_object* v_x2_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1(v_x1_126_, v_x2_127_, v___y_128_, v___y_129_, v___y_130_, v___y_131_, v___y_132_);
lean_dec(v___y_128_);
return v_res_134_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__15___redArg___closed__0(void){
_start:
{
lean_object* v___x_135_; 
v___x_135_ = l_instMonadEST(lean_box(0), lean_box(0));
return v___x_135_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__15___redArg___closed__5(void){
_start:
{
lean_object* v___x_140_; 
v___x_140_ = l_Array_instInhabited(lean_box(0));
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__15___redArg(lean_object* v_msg_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_){
_start:
{
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v_toApplicative_150_; lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_212_; 
v___x_148_ = lean_obj_once(&l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__15___redArg___closed__0, &l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__15___redArg___closed__0_once, _init_l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__15___redArg___closed__0);
v___x_149_ = l_ReaderT_instMonad___redArg(v___x_148_);
v_toApplicative_150_ = lean_ctor_get(v___x_149_, 0);
v_isSharedCheck_212_ = !lean_is_exclusive(v___x_149_);
if (v_isSharedCheck_212_ == 0)
{
lean_object* v_unused_213_; 
v_unused_213_ = lean_ctor_get(v___x_149_, 1);
lean_dec(v_unused_213_);
v___x_152_ = v___x_149_;
v_isShared_153_ = v_isSharedCheck_212_;
goto v_resetjp_151_;
}
else
{
lean_inc(v_toApplicative_150_);
lean_dec(v___x_149_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_212_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
lean_object* v_toFunctor_154_; lean_object* v_toSeq_155_; lean_object* v_toSeqLeft_156_; lean_object* v_toSeqRight_157_; lean_object* v___x_159_; uint8_t v_isShared_160_; uint8_t v_isSharedCheck_210_; 
v_toFunctor_154_ = lean_ctor_get(v_toApplicative_150_, 0);
v_toSeq_155_ = lean_ctor_get(v_toApplicative_150_, 2);
v_toSeqLeft_156_ = lean_ctor_get(v_toApplicative_150_, 3);
v_toSeqRight_157_ = lean_ctor_get(v_toApplicative_150_, 4);
v_isSharedCheck_210_ = !lean_is_exclusive(v_toApplicative_150_);
if (v_isSharedCheck_210_ == 0)
{
lean_object* v_unused_211_; 
v_unused_211_ = lean_ctor_get(v_toApplicative_150_, 1);
lean_dec(v_unused_211_);
v___x_159_ = v_toApplicative_150_;
v_isShared_160_ = v_isSharedCheck_210_;
goto v_resetjp_158_;
}
else
{
lean_inc(v_toSeqRight_157_);
lean_inc(v_toSeqLeft_156_);
lean_inc(v_toSeq_155_);
lean_inc(v_toFunctor_154_);
lean_dec(v_toApplicative_150_);
v___x_159_ = lean_box(0);
v_isShared_160_ = v_isSharedCheck_210_;
goto v_resetjp_158_;
}
v_resetjp_158_:
{
lean_object* v___f_161_; lean_object* v___f_162_; lean_object* v___f_163_; lean_object* v___f_164_; lean_object* v___x_165_; lean_object* v___f_166_; lean_object* v___f_167_; lean_object* v___f_168_; lean_object* v___x_170_; 
v___f_161_ = ((lean_object*)(l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__15___redArg___closed__1));
v___f_162_ = ((lean_object*)(l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__15___redArg___closed__2));
lean_inc_ref(v_toFunctor_154_);
v___f_163_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_163_, 0, v_toFunctor_154_);
v___f_164_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_164_, 0, v_toFunctor_154_);
v___x_165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_165_, 0, v___f_163_);
lean_ctor_set(v___x_165_, 1, v___f_164_);
v___f_166_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_166_, 0, v_toSeqRight_157_);
v___f_167_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_167_, 0, v_toSeqLeft_156_);
v___f_168_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_168_, 0, v_toSeq_155_);
if (v_isShared_160_ == 0)
{
lean_ctor_set(v___x_159_, 4, v___f_166_);
lean_ctor_set(v___x_159_, 3, v___f_167_);
lean_ctor_set(v___x_159_, 2, v___f_168_);
lean_ctor_set(v___x_159_, 1, v___f_161_);
lean_ctor_set(v___x_159_, 0, v___x_165_);
v___x_170_ = v___x_159_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v___x_165_);
lean_ctor_set(v_reuseFailAlloc_209_, 1, v___f_161_);
lean_ctor_set(v_reuseFailAlloc_209_, 2, v___f_168_);
lean_ctor_set(v_reuseFailAlloc_209_, 3, v___f_167_);
lean_ctor_set(v_reuseFailAlloc_209_, 4, v___f_166_);
v___x_170_ = v_reuseFailAlloc_209_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
lean_object* v___x_172_; 
if (v_isShared_153_ == 0)
{
lean_ctor_set(v___x_152_, 1, v___f_162_);
lean_ctor_set(v___x_152_, 0, v___x_170_);
v___x_172_ = v___x_152_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v___x_170_);
lean_ctor_set(v_reuseFailAlloc_208_, 1, v___f_162_);
v___x_172_ = v_reuseFailAlloc_208_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
lean_object* v___x_173_; lean_object* v_toApplicative_174_; lean_object* v___x_176_; uint8_t v_isShared_177_; uint8_t v_isSharedCheck_206_; 
v___x_173_ = l_ReaderT_instMonad___redArg(v___x_172_);
v_toApplicative_174_ = lean_ctor_get(v___x_173_, 0);
v_isSharedCheck_206_ = !lean_is_exclusive(v___x_173_);
if (v_isSharedCheck_206_ == 0)
{
lean_object* v_unused_207_; 
v_unused_207_ = lean_ctor_get(v___x_173_, 1);
lean_dec(v_unused_207_);
v___x_176_ = v___x_173_;
v_isShared_177_ = v_isSharedCheck_206_;
goto v_resetjp_175_;
}
else
{
lean_inc(v_toApplicative_174_);
lean_dec(v___x_173_);
v___x_176_ = lean_box(0);
v_isShared_177_ = v_isSharedCheck_206_;
goto v_resetjp_175_;
}
v_resetjp_175_:
{
lean_object* v_toFunctor_178_; lean_object* v_toSeq_179_; lean_object* v_toSeqLeft_180_; lean_object* v_toSeqRight_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_204_; 
v_toFunctor_178_ = lean_ctor_get(v_toApplicative_174_, 0);
v_toSeq_179_ = lean_ctor_get(v_toApplicative_174_, 2);
v_toSeqLeft_180_ = lean_ctor_get(v_toApplicative_174_, 3);
v_toSeqRight_181_ = lean_ctor_get(v_toApplicative_174_, 4);
v_isSharedCheck_204_ = !lean_is_exclusive(v_toApplicative_174_);
if (v_isSharedCheck_204_ == 0)
{
lean_object* v_unused_205_; 
v_unused_205_ = lean_ctor_get(v_toApplicative_174_, 1);
lean_dec(v_unused_205_);
v___x_183_ = v_toApplicative_174_;
v_isShared_184_ = v_isSharedCheck_204_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_toSeqRight_181_);
lean_inc(v_toSeqLeft_180_);
lean_inc(v_toSeq_179_);
lean_inc(v_toFunctor_178_);
lean_dec(v_toApplicative_174_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_204_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v___f_185_; lean_object* v___f_186_; lean_object* v___f_187_; lean_object* v___f_188_; lean_object* v___x_189_; lean_object* v___f_190_; lean_object* v___f_191_; lean_object* v___f_192_; lean_object* v___x_194_; 
v___f_185_ = ((lean_object*)(l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__15___redArg___closed__3));
v___f_186_ = ((lean_object*)(l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__15___redArg___closed__4));
lean_inc_ref(v_toFunctor_178_);
v___f_187_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_187_, 0, v_toFunctor_178_);
v___f_188_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_188_, 0, v_toFunctor_178_);
v___x_189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_189_, 0, v___f_187_);
lean_ctor_set(v___x_189_, 1, v___f_188_);
v___f_190_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_190_, 0, v_toSeqRight_181_);
v___f_191_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_191_, 0, v_toSeqLeft_180_);
v___f_192_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_192_, 0, v_toSeq_179_);
if (v_isShared_184_ == 0)
{
lean_ctor_set(v___x_183_, 4, v___f_190_);
lean_ctor_set(v___x_183_, 3, v___f_191_);
lean_ctor_set(v___x_183_, 2, v___f_192_);
lean_ctor_set(v___x_183_, 1, v___f_185_);
lean_ctor_set(v___x_183_, 0, v___x_189_);
v___x_194_ = v___x_183_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v___x_189_);
lean_ctor_set(v_reuseFailAlloc_203_, 1, v___f_185_);
lean_ctor_set(v_reuseFailAlloc_203_, 2, v___f_192_);
lean_ctor_set(v_reuseFailAlloc_203_, 3, v___f_191_);
lean_ctor_set(v_reuseFailAlloc_203_, 4, v___f_190_);
v___x_194_ = v_reuseFailAlloc_203_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
lean_object* v___x_196_; 
if (v_isShared_177_ == 0)
{
lean_ctor_set(v___x_176_, 1, v___f_186_);
lean_ctor_set(v___x_176_, 0, v___x_194_);
v___x_196_ = v___x_176_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v___x_194_);
lean_ctor_set(v_reuseFailAlloc_202_, 1, v___f_186_);
v___x_196_ = v_reuseFailAlloc_202_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_25087__overap_200_; lean_object* v___x_201_; 
v___x_197_ = l_ReaderT_instMonad___redArg(v___x_196_);
v___x_198_ = lean_obj_once(&l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__15___redArg___closed__5, &l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__15___redArg___closed__5_once, _init_l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__15___redArg___closed__5);
v___x_199_ = l_instInhabitedOfMonad___redArg(v___x_197_, v___x_198_);
v___x_25087__overap_200_ = lean_panic_fn(v___x_199_, v_msg_141_);
v___x_201_ = lean_apply_6(v___x_25087__overap_200_, v___y_142_, v___y_143_, v___y_144_, v___y_145_, v___y_146_, lean_box(0));
return v___x_201_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__15___redArg___boxed(lean_object* v_msg_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__15___redArg(v_msg_214_, v___y_215_, v___y_216_, v___y_217_, v___y_218_, v___y_219_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__14___redArg(lean_object* v_inst_222_, lean_object* v_xs_223_, size_t v_sz_224_, size_t v_i_225_, lean_object* v_bs_226_){
_start:
{
uint8_t v___x_227_; 
v___x_227_ = lean_usize_dec_lt(v_i_225_, v_sz_224_);
if (v___x_227_ == 0)
{
lean_dec(v_inst_222_);
return v_bs_226_;
}
else
{
lean_object* v_v_228_; lean_object* v___x_229_; lean_object* v_bs_x27_230_; lean_object* v___x_231_; size_t v___x_232_; size_t v___x_233_; lean_object* v___x_234_; 
v_v_228_ = lean_array_uget(v_bs_226_, v_i_225_);
v___x_229_ = lean_unsigned_to_nat(0u);
v_bs_x27_230_ = lean_array_uset(v_bs_226_, v_i_225_, v___x_229_);
lean_inc(v_inst_222_);
v___x_231_ = lean_array_get_borrowed(v_inst_222_, v_xs_223_, v_v_228_);
lean_dec(v_v_228_);
v___x_232_ = ((size_t)1ULL);
v___x_233_ = lean_usize_add(v_i_225_, v___x_232_);
lean_inc(v___x_231_);
v___x_234_ = lean_array_uset(v_bs_x27_230_, v_i_225_, v___x_231_);
v_i_225_ = v___x_233_;
v_bs_226_ = v___x_234_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__14___redArg___boxed(lean_object* v_inst_236_, lean_object* v_xs_237_, lean_object* v_sz_238_, lean_object* v_i_239_, lean_object* v_bs_240_){
_start:
{
size_t v_sz_boxed_241_; size_t v_i_boxed_242_; lean_object* v_res_243_; 
v_sz_boxed_241_ = lean_unbox_usize(v_sz_238_);
lean_dec(v_sz_238_);
v_i_boxed_242_ = lean_unbox_usize(v_i_239_);
lean_dec(v_i_239_);
v_res_243_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__14___redArg(v_inst_236_, v_xs_237_, v_sz_boxed_241_, v_i_boxed_242_, v_bs_240_);
lean_dec_ref(v_xs_237_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__16___redArg(lean_object* v_inst_244_, lean_object* v_xs_245_, lean_object* v_f_246_, lean_object* v_as_247_, lean_object* v_bs_248_, lean_object* v_i_249_, lean_object* v_cs_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_){
_start:
{
lean_object* v___x_257_; uint8_t v___x_258_; 
v___x_257_ = lean_array_get_size(v_as_247_);
v___x_258_ = lean_nat_dec_lt(v_i_249_, v___x_257_);
if (v___x_258_ == 0)
{
lean_object* v___x_259_; 
lean_dec(v___y_255_);
lean_dec_ref(v___y_254_);
lean_dec(v___y_253_);
lean_dec_ref(v___y_252_);
lean_dec(v___y_251_);
lean_dec(v_i_249_);
lean_dec_ref(v_f_246_);
lean_dec(v_inst_244_);
v___x_259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_259_, 0, v_cs_250_);
return v___x_259_;
}
else
{
lean_object* v___x_260_; uint8_t v___x_261_; 
v___x_260_ = lean_array_get_size(v_bs_248_);
v___x_261_ = lean_nat_dec_lt(v_i_249_, v___x_260_);
if (v___x_261_ == 0)
{
lean_object* v___x_262_; 
lean_dec(v___y_255_);
lean_dec_ref(v___y_254_);
lean_dec(v___y_253_);
lean_dec_ref(v___y_252_);
lean_dec(v___y_251_);
lean_dec(v_i_249_);
lean_dec_ref(v_f_246_);
lean_dec(v_inst_244_);
v___x_262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_262_, 0, v_cs_250_);
return v___x_262_;
}
else
{
lean_object* v_a_263_; lean_object* v_b_264_; size_t v_sz_265_; size_t v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v_a_263_ = lean_array_fget_borrowed(v_as_247_, v_i_249_);
v_b_264_ = lean_array_fget_borrowed(v_bs_248_, v_i_249_);
v_sz_265_ = lean_array_size(v_b_264_);
v___x_266_ = ((size_t)0ULL);
lean_inc(v_b_264_);
lean_inc(v_inst_244_);
v___x_267_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__14___redArg(v_inst_244_, v_xs_245_, v_sz_265_, v___x_266_, v_b_264_);
lean_inc_ref(v_f_246_);
lean_inc(v___y_255_);
lean_inc_ref(v___y_254_);
lean_inc(v___y_253_);
lean_inc_ref(v___y_252_);
lean_inc(v___y_251_);
lean_inc(v_a_263_);
v___x_268_ = lean_apply_8(v_f_246_, v_a_263_, v___x_267_, v___y_251_, v___y_252_, v___y_253_, v___y_254_, v___y_255_, lean_box(0));
if (lean_obj_tag(v___x_268_) == 0)
{
lean_object* v_a_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v_a_269_ = lean_ctor_get(v___x_268_, 0);
lean_inc(v_a_269_);
lean_dec_ref(v___x_268_);
v___x_270_ = lean_unsigned_to_nat(1u);
v___x_271_ = lean_nat_add(v_i_249_, v___x_270_);
lean_dec(v_i_249_);
v___x_272_ = lean_array_push(v_cs_250_, v_a_269_);
v_i_249_ = v___x_271_;
v_cs_250_ = v___x_272_;
goto _start;
}
else
{
lean_object* v_a_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_281_; 
lean_dec(v___y_255_);
lean_dec_ref(v___y_254_);
lean_dec(v___y_253_);
lean_dec_ref(v___y_252_);
lean_dec(v___y_251_);
lean_dec_ref(v_cs_250_);
lean_dec(v_i_249_);
lean_dec_ref(v_f_246_);
lean_dec(v_inst_244_);
v_a_274_ = lean_ctor_get(v___x_268_, 0);
v_isSharedCheck_281_ = !lean_is_exclusive(v___x_268_);
if (v_isSharedCheck_281_ == 0)
{
v___x_276_ = v___x_268_;
v_isShared_277_ = v_isSharedCheck_281_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_a_274_);
lean_dec(v___x_268_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_281_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v___x_279_; 
if (v_isShared_277_ == 0)
{
v___x_279_ = v___x_276_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v_a_274_);
v___x_279_ = v_reuseFailAlloc_280_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
return v___x_279_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__16___redArg___boxed(lean_object* v_inst_282_, lean_object* v_xs_283_, lean_object* v_f_284_, lean_object* v_as_285_, lean_object* v_bs_286_, lean_object* v_i_287_, lean_object* v_cs_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__16___redArg(v_inst_282_, v_xs_283_, v_f_284_, v_as_285_, v_bs_286_, v_i_287_, v_cs_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_);
lean_dec_ref(v_bs_286_);
lean_dec_ref(v_as_285_);
lean_dec_ref(v_xs_283_);
return v_res_295_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_299_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg___closed__2));
v___x_300_ = lean_unsigned_to_nat(2u);
v___x_301_ = lean_unsigned_to_nat(89u);
v___x_302_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg___closed__1));
v___x_303_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg___closed__0));
v___x_304_ = l_mkPanicMessageWithDecl(v___x_303_, v___x_302_, v___x_301_, v___x_300_, v___x_299_);
return v___x_304_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_306_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg___closed__4));
v___x_307_ = lean_unsigned_to_nat(2u);
v___x_308_ = lean_unsigned_to_nat(90u);
v___x_309_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg___closed__1));
v___x_310_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg___closed__0));
v___x_311_ = l_mkPanicMessageWithDecl(v___x_310_, v___x_309_, v___x_308_, v___x_307_, v___x_306_);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg(lean_object* v_inst_314_, lean_object* v_f_315_, lean_object* v_positions_316_, lean_object* v_ys_317_, lean_object* v_xs_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_){
_start:
{
lean_object* v___x_325_; lean_object* v___x_326_; uint8_t v___x_327_; 
v___x_325_ = lean_array_get_size(v_positions_316_);
v___x_326_ = lean_array_get_size(v_ys_317_);
v___x_327_ = lean_nat_dec_eq(v___x_325_, v___x_326_);
if (v___x_327_ == 0)
{
lean_object* v___x_328_; lean_object* v___x_329_; 
lean_dec_ref(v_f_315_);
lean_dec(v_inst_314_);
v___x_328_ = lean_obj_once(&l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg___closed__3, &l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg___closed__3_once, _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg___closed__3);
v___x_329_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__15___redArg(v___x_328_, v___y_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_);
return v___x_329_;
}
else
{
lean_object* v___x_330_; lean_object* v___x_331_; uint8_t v___x_332_; 
v___x_330_ = l_Lean_Elab_Structural_Positions_numIndices(v_positions_316_);
v___x_331_ = lean_array_get_size(v_xs_318_);
v___x_332_ = lean_nat_dec_eq(v___x_330_, v___x_331_);
lean_dec(v___x_330_);
if (v___x_332_ == 0)
{
lean_object* v___x_333_; lean_object* v___x_334_; 
lean_dec_ref(v_f_315_);
lean_dec(v_inst_314_);
v___x_333_ = lean_obj_once(&l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg___closed__5, &l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg___closed__5_once, _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg___closed__5);
v___x_334_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__15___redArg(v___x_333_, v___y_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_);
return v___x_334_;
}
else
{
lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_335_ = lean_unsigned_to_nat(0u);
v___x_336_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg___closed__6));
v___x_337_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__16___redArg(v_inst_314_, v_xs_318_, v_f_315_, v_ys_317_, v_positions_316_, v___x_335_, v___x_336_, v___y_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_);
return v___x_337_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg___boxed(lean_object* v_inst_338_, lean_object* v_f_339_, lean_object* v_positions_340_, lean_object* v_ys_341_, lean_object* v_xs_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg(v_inst_338_, v_f_339_, v_positions_340_, v_ys_341_, v_xs_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_);
lean_dec_ref(v_xs_342_);
lean_dec_ref(v_ys_341_);
lean_dec_ref(v_positions_340_);
return v_res_349_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_350_; lean_object* v_dummy_351_; 
v___x_350_ = lean_box(0);
v_dummy_351_ = l_Lean_Expr_sort___override(v___x_350_);
return v_dummy_351_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg(lean_object* v_a_352_, lean_object* v_a_353_, uint8_t v_a_354_, lean_object* v_recArgInfos_355_, lean_object* v___x_356_, lean_object* v_a_357_, lean_object* v_as_358_, lean_object* v_i_359_, lean_object* v_j_360_, lean_object* v_bs_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_){
_start:
{
lean_object* v_zero_368_; uint8_t v_isZero_369_; 
v_zero_368_ = lean_unsigned_to_nat(0u);
v_isZero_369_ = lean_nat_dec_eq(v_i_359_, v_zero_368_);
if (v_isZero_369_ == 1)
{
lean_object* v___x_370_; 
lean_dec(v___y_366_);
lean_dec_ref(v___y_365_);
lean_dec(v___y_364_);
lean_dec_ref(v___y_363_);
lean_dec(v___y_362_);
lean_dec(v_j_360_);
lean_dec(v_i_359_);
lean_dec_ref(v_a_357_);
lean_dec_ref(v___x_356_);
lean_dec_ref(v_recArgInfos_355_);
v___x_370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_370_, 0, v_bs_361_);
return v___x_370_;
}
else
{
lean_object* v___x_371_; lean_object* v_one_372_; lean_object* v_n_373_; lean_object* v___y_375_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_371_ = l_Lean_instInhabitedExpr;
v_one_372_ = lean_unsigned_to_nat(1u);
v_n_373_ = lean_nat_sub(v_i_359_, v_one_372_);
lean_dec(v_i_359_);
v___x_388_ = lean_array_fget_borrowed(v_as_358_, v_j_360_);
v___x_389_ = lean_array_get_borrowed(v___x_371_, v_a_352_, v_j_360_);
v___x_390_ = lean_array_get_borrowed(v___x_371_, v_a_353_, v_j_360_);
if (v_a_354_ == 0)
{
lean_object* v___x_391_; 
lean_inc(v___y_366_);
lean_inc_ref(v___y_365_);
lean_inc(v___y_364_);
lean_inc_ref(v___y_363_);
lean_inc(v___y_362_);
lean_inc(v___x_390_);
lean_inc(v___x_389_);
lean_inc(v___x_388_);
lean_inc_ref(v___x_356_);
lean_inc_ref(v_recArgInfos_355_);
v___x_391_ = l_Lean_Elab_Structural_mkBRecOnF(v_recArgInfos_355_, v___x_356_, v___x_388_, v___x_389_, v___x_390_, v___y_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_);
v___y_375_ = v___x_391_;
goto v___jp_374_;
}
else
{
lean_object* v___x_392_; lean_object* v_dummy_393_; lean_object* v_nargs_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
lean_inc_ref(v_a_357_);
v___x_392_ = lean_apply_1(v_a_357_, v_zero_368_);
v_dummy_393_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__0, &l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__0_once, _init_l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__0);
v_nargs_394_ = l_Lean_Expr_getAppNumArgs(v___x_392_);
lean_inc(v_nargs_394_);
v___x_395_ = lean_mk_array(v_nargs_394_, v_dummy_393_);
v___x_396_ = lean_nat_sub(v_nargs_394_, v_one_372_);
lean_dec(v_nargs_394_);
v___x_397_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___x_392_, v___x_395_, v___x_396_);
lean_inc(v___y_366_);
lean_inc_ref(v___y_365_);
lean_inc(v___y_364_);
lean_inc_ref(v___y_363_);
lean_inc(v___y_362_);
lean_inc(v___x_390_);
lean_inc(v___x_389_);
lean_inc(v___x_388_);
lean_inc_ref(v___x_356_);
lean_inc_ref(v_recArgInfos_355_);
v___x_398_ = l_Lean_Elab_Structural_mkIndPredBRecOnF(v_recArgInfos_355_, v___x_356_, v___x_388_, v___x_389_, v___x_390_, v___x_397_, v___y_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_);
v___y_375_ = v___x_398_;
goto v___jp_374_;
}
v___jp_374_:
{
if (lean_obj_tag(v___y_375_) == 0)
{
lean_object* v_a_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
v_a_376_ = lean_ctor_get(v___y_375_, 0);
lean_inc(v_a_376_);
lean_dec_ref(v___y_375_);
v___x_377_ = lean_nat_add(v_j_360_, v_one_372_);
lean_dec(v_j_360_);
v___x_378_ = lean_array_push(v_bs_361_, v_a_376_);
v_i_359_ = v_n_373_;
v_j_360_ = v___x_377_;
v_bs_361_ = v___x_378_;
goto _start;
}
else
{
lean_object* v_a_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_387_; 
lean_dec(v_n_373_);
lean_dec(v___y_366_);
lean_dec_ref(v___y_365_);
lean_dec(v___y_364_);
lean_dec_ref(v___y_363_);
lean_dec(v___y_362_);
lean_dec_ref(v_bs_361_);
lean_dec(v_j_360_);
lean_dec_ref(v_a_357_);
lean_dec_ref(v___x_356_);
lean_dec_ref(v_recArgInfos_355_);
v_a_380_ = lean_ctor_get(v___y_375_, 0);
v_isSharedCheck_387_ = !lean_is_exclusive(v___y_375_);
if (v_isSharedCheck_387_ == 0)
{
v___x_382_ = v___y_375_;
v_isShared_383_ = v_isSharedCheck_387_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_a_380_);
lean_dec(v___y_375_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_387_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v___x_385_; 
if (v_isShared_383_ == 0)
{
v___x_385_ = v___x_382_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v_a_380_);
v___x_385_ = v_reuseFailAlloc_386_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
return v___x_385_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___boxed(lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_recArgInfos_402_, lean_object* v___x_403_, lean_object* v_a_404_, lean_object* v_as_405_, lean_object* v_i_406_, lean_object* v_j_407_, lean_object* v_bs_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_){
_start:
{
uint8_t v_a_27112__boxed_415_; lean_object* v_res_416_; 
v_a_27112__boxed_415_ = lean_unbox(v_a_401_);
v_res_416_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg(v_a_399_, v_a_400_, v_a_27112__boxed_415_, v_recArgInfos_402_, v___x_403_, v_a_404_, v_as_405_, v_i_406_, v_j_407_, v_bs_408_, v___y_409_, v___y_410_, v___y_411_, v___y_412_, v___y_413_);
lean_dec_ref(v_as_405_);
lean_dec_ref(v_a_400_);
lean_dec_ref(v_a_399_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg(lean_object* v___x_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_funTypes_420_, lean_object* v_as_421_, lean_object* v_i_422_, lean_object* v_j_423_, lean_object* v_bs_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_){
_start:
{
lean_object* v_zero_430_; uint8_t v_isZero_431_; 
v_zero_430_ = lean_unsigned_to_nat(0u);
v_isZero_431_ = lean_nat_dec_eq(v_i_422_, v_zero_430_);
if (v_isZero_431_ == 1)
{
lean_object* v___x_432_; 
lean_dec(v___y_428_);
lean_dec_ref(v___y_427_);
lean_dec(v___y_426_);
lean_dec_ref(v___y_425_);
lean_dec(v_j_423_);
lean_dec(v_i_422_);
lean_dec_ref(v_funTypes_420_);
lean_dec_ref(v_a_419_);
lean_dec_ref(v_a_418_);
lean_dec_ref(v___x_417_);
v___x_432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_432_, 0, v_bs_424_);
return v___x_432_;
}
else
{
lean_object* v___x_433_; lean_object* v_fst_434_; lean_object* v_snd_435_; lean_object* v___x_436_; 
v___x_433_ = lean_array_fget_borrowed(v_as_421_, v_j_423_);
v_fst_434_ = lean_ctor_get(v___x_433_, 0);
v_snd_435_ = lean_ctor_get(v___x_433_, 1);
lean_inc(v___y_428_);
lean_inc_ref(v___y_427_);
lean_inc(v___y_426_);
lean_inc_ref(v___y_425_);
lean_inc(v_snd_435_);
lean_inc(v_fst_434_);
lean_inc_ref(v_funTypes_420_);
lean_inc_ref(v_a_419_);
lean_inc_ref(v_a_418_);
lean_inc(v_j_423_);
lean_inc_ref(v___x_417_);
v___x_436_ = l_Lean_Elab_Structural_mkBRecOnApp(v___x_417_, v_j_423_, v_a_418_, v_a_419_, v_funTypes_420_, v_fst_434_, v_snd_435_, v___y_425_, v___y_426_, v___y_427_, v___y_428_);
if (lean_obj_tag(v___x_436_) == 0)
{
lean_object* v_a_437_; lean_object* v_one_438_; lean_object* v_n_439_; lean_object* v___x_440_; lean_object* v___x_441_; 
v_a_437_ = lean_ctor_get(v___x_436_, 0);
lean_inc(v_a_437_);
lean_dec_ref(v___x_436_);
v_one_438_ = lean_unsigned_to_nat(1u);
v_n_439_ = lean_nat_sub(v_i_422_, v_one_438_);
lean_dec(v_i_422_);
v___x_440_ = lean_nat_add(v_j_423_, v_one_438_);
lean_dec(v_j_423_);
v___x_441_ = lean_array_push(v_bs_424_, v_a_437_);
v_i_422_ = v_n_439_;
v_j_423_ = v___x_440_;
v_bs_424_ = v___x_441_;
goto _start;
}
else
{
lean_object* v_a_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_450_; 
lean_dec(v___y_428_);
lean_dec_ref(v___y_427_);
lean_dec(v___y_426_);
lean_dec_ref(v___y_425_);
lean_dec_ref(v_bs_424_);
lean_dec(v_j_423_);
lean_dec(v_i_422_);
lean_dec_ref(v_funTypes_420_);
lean_dec_ref(v_a_419_);
lean_dec_ref(v_a_418_);
lean_dec_ref(v___x_417_);
v_a_443_ = lean_ctor_get(v___x_436_, 0);
v_isSharedCheck_450_ = !lean_is_exclusive(v___x_436_);
if (v_isSharedCheck_450_ == 0)
{
v___x_445_ = v___x_436_;
v_isShared_446_ = v_isSharedCheck_450_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_a_443_);
lean_dec(v___x_436_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_450_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v___x_448_; 
if (v_isShared_446_ == 0)
{
v___x_448_ = v___x_445_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v_a_443_);
v___x_448_ = v_reuseFailAlloc_449_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
return v___x_448_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___boxed(lean_object* v___x_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_funTypes_454_, lean_object* v_as_455_, lean_object* v_i_456_, lean_object* v_j_457_, lean_object* v_bs_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_){
_start:
{
lean_object* v_res_464_; 
v_res_464_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg(v___x_451_, v_a_452_, v_a_453_, v_funTypes_454_, v_as_455_, v_i_456_, v_j_457_, v_bs_458_, v___y_459_, v___y_460_, v___y_461_, v___y_462_);
lean_dec_ref(v_as_455_);
return v_res_464_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__22(lean_object* v_msgData_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_){
_start:
{
lean_object* v___x_471_; lean_object* v_env_472_; lean_object* v___x_473_; lean_object* v_mctx_474_; lean_object* v_lctx_475_; lean_object* v_options_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_471_ = lean_st_ref_get(v___y_469_);
v_env_472_ = lean_ctor_get(v___x_471_, 0);
lean_inc_ref(v_env_472_);
lean_dec(v___x_471_);
v___x_473_ = lean_st_ref_get(v___y_467_);
v_mctx_474_ = lean_ctor_get(v___x_473_, 0);
lean_inc_ref(v_mctx_474_);
lean_dec(v___x_473_);
v_lctx_475_ = lean_ctor_get(v___y_466_, 2);
v_options_476_ = lean_ctor_get(v___y_468_, 2);
lean_inc_ref(v_options_476_);
lean_inc_ref(v_lctx_475_);
v___x_477_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_477_, 0, v_env_472_);
lean_ctor_set(v___x_477_, 1, v_mctx_474_);
lean_ctor_set(v___x_477_, 2, v_lctx_475_);
lean_ctor_set(v___x_477_, 3, v_options_476_);
v___x_478_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_478_, 0, v___x_477_);
lean_ctor_set(v___x_478_, 1, v_msgData_465_);
v___x_479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_479_, 0, v___x_478_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__22___boxed(lean_object* v_msgData_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__22(v_msgData_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_);
lean_dec(v___y_484_);
lean_dec_ref(v___y_483_);
lean_dec(v___y_482_);
lean_dec_ref(v___y_481_);
return v_res_486_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___closed__0(void){
_start:
{
lean_object* v___x_487_; double v___x_488_; 
v___x_487_ = lean_unsigned_to_nat(0u);
v___x_488_ = lean_float_of_nat(v___x_487_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(lean_object* v_cls_492_, lean_object* v_msg_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_){
_start:
{
lean_object* v_ref_499_; lean_object* v___x_500_; lean_object* v_a_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_545_; 
v_ref_499_ = lean_ctor_get(v___y_496_, 5);
v___x_500_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__22(v_msg_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_);
v_a_501_ = lean_ctor_get(v___x_500_, 0);
v_isSharedCheck_545_ = !lean_is_exclusive(v___x_500_);
if (v_isSharedCheck_545_ == 0)
{
v___x_503_ = v___x_500_;
v_isShared_504_ = v_isSharedCheck_545_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_a_501_);
lean_dec(v___x_500_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_545_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v___x_505_; lean_object* v_traceState_506_; lean_object* v_env_507_; lean_object* v_nextMacroScope_508_; lean_object* v_ngen_509_; lean_object* v_auxDeclNGen_510_; lean_object* v_cache_511_; lean_object* v_messages_512_; lean_object* v_infoState_513_; lean_object* v_snapshotTasks_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_544_; 
v___x_505_ = lean_st_ref_take(v___y_497_);
v_traceState_506_ = lean_ctor_get(v___x_505_, 4);
v_env_507_ = lean_ctor_get(v___x_505_, 0);
v_nextMacroScope_508_ = lean_ctor_get(v___x_505_, 1);
v_ngen_509_ = lean_ctor_get(v___x_505_, 2);
v_auxDeclNGen_510_ = lean_ctor_get(v___x_505_, 3);
v_cache_511_ = lean_ctor_get(v___x_505_, 5);
v_messages_512_ = lean_ctor_get(v___x_505_, 6);
v_infoState_513_ = lean_ctor_get(v___x_505_, 7);
v_snapshotTasks_514_ = lean_ctor_get(v___x_505_, 8);
v_isSharedCheck_544_ = !lean_is_exclusive(v___x_505_);
if (v_isSharedCheck_544_ == 0)
{
v___x_516_ = v___x_505_;
v_isShared_517_ = v_isSharedCheck_544_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_snapshotTasks_514_);
lean_inc(v_infoState_513_);
lean_inc(v_messages_512_);
lean_inc(v_cache_511_);
lean_inc(v_traceState_506_);
lean_inc(v_auxDeclNGen_510_);
lean_inc(v_ngen_509_);
lean_inc(v_nextMacroScope_508_);
lean_inc(v_env_507_);
lean_dec(v___x_505_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_544_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
uint64_t v_tid_518_; lean_object* v_traces_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_543_; 
v_tid_518_ = lean_ctor_get_uint64(v_traceState_506_, sizeof(void*)*1);
v_traces_519_ = lean_ctor_get(v_traceState_506_, 0);
v_isSharedCheck_543_ = !lean_is_exclusive(v_traceState_506_);
if (v_isSharedCheck_543_ == 0)
{
v___x_521_ = v_traceState_506_;
v_isShared_522_ = v_isSharedCheck_543_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_traces_519_);
lean_dec(v_traceState_506_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_543_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_523_; double v___x_524_; uint8_t v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_533_; 
v___x_523_ = lean_box(0);
v___x_524_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___closed__0);
v___x_525_ = 0;
v___x_526_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___closed__1));
v___x_527_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_527_, 0, v_cls_492_);
lean_ctor_set(v___x_527_, 1, v___x_523_);
lean_ctor_set(v___x_527_, 2, v___x_526_);
lean_ctor_set_float(v___x_527_, sizeof(void*)*3, v___x_524_);
lean_ctor_set_float(v___x_527_, sizeof(void*)*3 + 8, v___x_524_);
lean_ctor_set_uint8(v___x_527_, sizeof(void*)*3 + 16, v___x_525_);
v___x_528_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___closed__2));
v___x_529_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_529_, 0, v___x_527_);
lean_ctor_set(v___x_529_, 1, v_a_501_);
lean_ctor_set(v___x_529_, 2, v___x_528_);
lean_inc(v_ref_499_);
v___x_530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_530_, 0, v_ref_499_);
lean_ctor_set(v___x_530_, 1, v___x_529_);
v___x_531_ = l_Lean_PersistentArray_push___redArg(v_traces_519_, v___x_530_);
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 0, v___x_531_);
v___x_533_ = v___x_521_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v___x_531_);
lean_ctor_set_uint64(v_reuseFailAlloc_542_, sizeof(void*)*1, v_tid_518_);
v___x_533_ = v_reuseFailAlloc_542_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
lean_object* v___x_535_; 
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 4, v___x_533_);
v___x_535_ = v___x_516_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v_env_507_);
lean_ctor_set(v_reuseFailAlloc_541_, 1, v_nextMacroScope_508_);
lean_ctor_set(v_reuseFailAlloc_541_, 2, v_ngen_509_);
lean_ctor_set(v_reuseFailAlloc_541_, 3, v_auxDeclNGen_510_);
lean_ctor_set(v_reuseFailAlloc_541_, 4, v___x_533_);
lean_ctor_set(v_reuseFailAlloc_541_, 5, v_cache_511_);
lean_ctor_set(v_reuseFailAlloc_541_, 6, v_messages_512_);
lean_ctor_set(v_reuseFailAlloc_541_, 7, v_infoState_513_);
lean_ctor_set(v_reuseFailAlloc_541_, 8, v_snapshotTasks_514_);
v___x_535_ = v_reuseFailAlloc_541_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_539_; 
v___x_536_ = lean_st_ref_set(v___y_497_, v___x_535_);
v___x_537_ = lean_box(0);
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 0, v___x_537_);
v___x_539_ = v___x_503_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v___x_537_);
v___x_539_ = v_reuseFailAlloc_540_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
return v___x_539_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___boxed(lean_object* v_cls_546_, lean_object* v_msg_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v_cls_546_, v_msg_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_);
lean_dec(v___y_551_);
lean_dec_ref(v___y_550_);
lean_dec(v___y_549_);
lean_dec_ref(v___y_548_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9___redArg___lam__0(lean_object* v_fixedParamPerms_554_, lean_object* v___x_555_, lean_object* v_j_556_, lean_object* v_xs_557_, lean_object* v_snd_558_, uint8_t v_isZero_559_, lean_object* v_ys_560_, lean_object* v_x_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_){
_start:
{
lean_object* v_perms_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; uint8_t v___x_572_; uint8_t v___x_573_; lean_object* v___x_574_; 
v_perms_568_ = lean_ctor_get(v_fixedParamPerms_554_, 1);
v___x_569_ = lean_array_get_borrowed(v___x_555_, v_perms_568_, v_j_556_);
lean_inc_ref(v_ys_560_);
lean_inc(v___x_569_);
v___x_570_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v___x_569_, v_xs_557_, v_ys_560_);
v___x_571_ = l_Lean_Expr_beta(v_snd_558_, v_ys_560_);
v___x_572_ = 1;
v___x_573_ = 1;
v___x_574_ = l_Lean_Meta_mkLambdaFVars(v___x_570_, v___x_571_, v_isZero_559_, v___x_572_, v_isZero_559_, v___x_572_, v___x_573_, v___y_563_, v___y_564_, v___y_565_, v___y_566_);
lean_dec_ref(v___x_570_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9___redArg___lam__0___boxed(lean_object* v_fixedParamPerms_575_, lean_object* v___x_576_, lean_object* v_j_577_, lean_object* v_xs_578_, lean_object* v_snd_579_, lean_object* v_isZero_580_, lean_object* v_ys_581_, lean_object* v_x_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_){
_start:
{
uint8_t v_isZero_boxed_589_; lean_object* v_res_590_; 
v_isZero_boxed_589_ = lean_unbox(v_isZero_580_);
v_res_590_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9___redArg___lam__0(v_fixedParamPerms_575_, v___x_576_, v_j_577_, v_xs_578_, v_snd_579_, v_isZero_boxed_589_, v_ys_581_, v_x_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_);
lean_dec(v___y_587_);
lean_dec_ref(v___y_586_);
lean_dec(v___y_585_);
lean_dec_ref(v___y_584_);
lean_dec(v___y_583_);
lean_dec_ref(v_x_582_);
lean_dec_ref(v_xs_578_);
lean_dec(v_j_577_);
lean_dec_ref(v_fixedParamPerms_575_);
return v_res_590_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_591_; 
v___x_591_ = l_Array_instInhabited(lean_box(0));
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9___redArg(lean_object* v_fixedParamPerms_592_, lean_object* v_xs_593_, lean_object* v_as_594_, lean_object* v_i_595_, lean_object* v_j_596_, lean_object* v_bs_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_){
_start:
{
lean_object* v_zero_604_; uint8_t v_isZero_605_; 
v_zero_604_ = lean_unsigned_to_nat(0u);
v_isZero_605_ = lean_nat_dec_eq(v_i_595_, v_zero_604_);
if (v_isZero_605_ == 1)
{
lean_object* v___x_606_; 
lean_dec(v___y_602_);
lean_dec_ref(v___y_601_);
lean_dec(v___y_600_);
lean_dec_ref(v___y_599_);
lean_dec(v___y_598_);
lean_dec(v_j_596_);
lean_dec(v_i_595_);
lean_dec_ref(v_xs_593_);
lean_dec_ref(v_fixedParamPerms_592_);
v___x_606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_606_, 0, v_bs_597_);
return v___x_606_;
}
else
{
lean_object* v___x_607_; lean_object* v_fst_608_; lean_object* v_snd_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___f_612_; lean_object* v___x_613_; 
v___x_607_ = lean_array_fget_borrowed(v_as_594_, v_j_596_);
v_fst_608_ = lean_ctor_get(v___x_607_, 0);
v_snd_609_ = lean_ctor_get(v___x_607_, 1);
v___x_610_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9___redArg___closed__0, &l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9___redArg___closed__0_once, _init_l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9___redArg___closed__0);
v___x_611_ = lean_box(v_isZero_605_);
lean_inc(v_snd_609_);
lean_inc_ref(v_xs_593_);
lean_inc(v_j_596_);
lean_inc_ref(v_fixedParamPerms_592_);
v___f_612_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9___redArg___lam__0___boxed), 14, 6);
lean_closure_set(v___f_612_, 0, v_fixedParamPerms_592_);
lean_closure_set(v___f_612_, 1, v___x_610_);
lean_closure_set(v___f_612_, 2, v_j_596_);
lean_closure_set(v___f_612_, 3, v_xs_593_);
lean_closure_set(v___f_612_, 4, v_snd_609_);
lean_closure_set(v___f_612_, 5, v___x_611_);
lean_inc(v___y_602_);
lean_inc_ref(v___y_601_);
lean_inc(v___y_600_);
lean_inc_ref(v___y_599_);
lean_inc(v___y_598_);
lean_inc(v_fst_608_);
v___x_613_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg(v_fst_608_, v___f_612_, v_isZero_605_, v___y_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_);
if (lean_obj_tag(v___x_613_) == 0)
{
lean_object* v_a_614_; lean_object* v_one_615_; lean_object* v_n_616_; lean_object* v___x_617_; lean_object* v___x_618_; 
v_a_614_ = lean_ctor_get(v___x_613_, 0);
lean_inc(v_a_614_);
lean_dec_ref(v___x_613_);
v_one_615_ = lean_unsigned_to_nat(1u);
v_n_616_ = lean_nat_sub(v_i_595_, v_one_615_);
lean_dec(v_i_595_);
v___x_617_ = lean_nat_add(v_j_596_, v_one_615_);
lean_dec(v_j_596_);
v___x_618_ = lean_array_push(v_bs_597_, v_a_614_);
v_i_595_ = v_n_616_;
v_j_596_ = v___x_617_;
v_bs_597_ = v___x_618_;
goto _start;
}
else
{
lean_object* v_a_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_627_; 
lean_dec(v___y_602_);
lean_dec_ref(v___y_601_);
lean_dec(v___y_600_);
lean_dec_ref(v___y_599_);
lean_dec(v___y_598_);
lean_dec_ref(v_bs_597_);
lean_dec(v_j_596_);
lean_dec(v_i_595_);
lean_dec_ref(v_xs_593_);
lean_dec_ref(v_fixedParamPerms_592_);
v_a_620_ = lean_ctor_get(v___x_613_, 0);
v_isSharedCheck_627_ = !lean_is_exclusive(v___x_613_);
if (v_isSharedCheck_627_ == 0)
{
v___x_622_ = v___x_613_;
v_isShared_623_ = v_isSharedCheck_627_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_a_620_);
lean_dec(v___x_613_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_627_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v___x_625_; 
if (v_isShared_623_ == 0)
{
v___x_625_ = v___x_622_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v_a_620_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
return v___x_625_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9___redArg___boxed(lean_object* v_fixedParamPerms_628_, lean_object* v_xs_629_, lean_object* v_as_630_, lean_object* v_i_631_, lean_object* v_j_632_, lean_object* v_bs_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9___redArg(v_fixedParamPerms_628_, v_xs_629_, v_as_630_, v_i_631_, v_j_632_, v_bs_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_);
lean_dec_ref(v_as_630_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(lean_object* v_a_641_, lean_object* v_a_642_){
_start:
{
if (lean_obj_tag(v_a_641_) == 0)
{
lean_object* v___x_643_; 
v___x_643_ = l_List_reverse___redArg(v_a_642_);
return v___x_643_;
}
else
{
lean_object* v_head_644_; lean_object* v_tail_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_654_; 
v_head_644_ = lean_ctor_get(v_a_641_, 0);
v_tail_645_ = lean_ctor_get(v_a_641_, 1);
v_isSharedCheck_654_ = !lean_is_exclusive(v_a_641_);
if (v_isSharedCheck_654_ == 0)
{
v___x_647_ = v_a_641_;
v_isShared_648_ = v_isSharedCheck_654_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_tail_645_);
lean_inc(v_head_644_);
lean_dec(v_a_641_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_654_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
lean_object* v___x_649_; lean_object* v___x_651_; 
v___x_649_ = l_Lean_MessageData_ofExpr(v_head_644_);
if (v_isShared_648_ == 0)
{
lean_ctor_set(v___x_647_, 1, v_a_642_);
lean_ctor_set(v___x_647_, 0, v___x_649_);
v___x_651_ = v___x_647_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v___x_649_);
lean_ctor_set(v_reuseFailAlloc_653_, 1, v_a_642_);
v___x_651_ = v_reuseFailAlloc_653_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
v_a_641_ = v_tail_645_;
v_a_642_ = v___x_651_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(lean_object* v_as_655_, lean_object* v_bs_656_, lean_object* v_i_657_, lean_object* v_cs_658_){
_start:
{
lean_object* v___x_659_; uint8_t v___x_660_; 
v___x_659_ = lean_array_get_size(v_as_655_);
v___x_660_ = lean_nat_dec_lt(v_i_657_, v___x_659_);
if (v___x_660_ == 0)
{
lean_dec(v_i_657_);
return v_cs_658_;
}
else
{
lean_object* v___x_661_; uint8_t v___x_662_; 
v___x_661_ = lean_array_get_size(v_bs_656_);
v___x_662_ = lean_nat_dec_lt(v_i_657_, v___x_661_);
if (v___x_662_ == 0)
{
lean_dec(v_i_657_);
return v_cs_658_;
}
else
{
lean_object* v_a_663_; lean_object* v_ref_664_; uint8_t v_kind_665_; lean_object* v_levelParams_666_; lean_object* v_modifiers_667_; lean_object* v_declName_668_; lean_object* v_binders_669_; lean_object* v_numSectionVars_670_; lean_object* v_type_671_; lean_object* v_termination_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_684_; 
v_a_663_ = lean_array_fget(v_as_655_, v_i_657_);
v_ref_664_ = lean_ctor_get(v_a_663_, 0);
v_kind_665_ = lean_ctor_get_uint8(v_a_663_, sizeof(void*)*9);
v_levelParams_666_ = lean_ctor_get(v_a_663_, 1);
v_modifiers_667_ = lean_ctor_get(v_a_663_, 2);
v_declName_668_ = lean_ctor_get(v_a_663_, 3);
v_binders_669_ = lean_ctor_get(v_a_663_, 4);
v_numSectionVars_670_ = lean_ctor_get(v_a_663_, 5);
v_type_671_ = lean_ctor_get(v_a_663_, 6);
v_termination_672_ = lean_ctor_get(v_a_663_, 8);
v_isSharedCheck_684_ = !lean_is_exclusive(v_a_663_);
if (v_isSharedCheck_684_ == 0)
{
lean_object* v_unused_685_; 
v_unused_685_ = lean_ctor_get(v_a_663_, 7);
lean_dec(v_unused_685_);
v___x_674_ = v_a_663_;
v_isShared_675_ = v_isSharedCheck_684_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_termination_672_);
lean_inc(v_type_671_);
lean_inc(v_numSectionVars_670_);
lean_inc(v_binders_669_);
lean_inc(v_declName_668_);
lean_inc(v_modifiers_667_);
lean_inc(v_levelParams_666_);
lean_inc(v_ref_664_);
lean_dec(v_a_663_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_684_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v_b_676_; lean_object* v___x_678_; 
v_b_676_ = lean_array_fget_borrowed(v_bs_656_, v_i_657_);
lean_inc(v_b_676_);
if (v_isShared_675_ == 0)
{
lean_ctor_set(v___x_674_, 7, v_b_676_);
v___x_678_ = v___x_674_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v_ref_664_);
lean_ctor_set(v_reuseFailAlloc_683_, 1, v_levelParams_666_);
lean_ctor_set(v_reuseFailAlloc_683_, 2, v_modifiers_667_);
lean_ctor_set(v_reuseFailAlloc_683_, 3, v_declName_668_);
lean_ctor_set(v_reuseFailAlloc_683_, 4, v_binders_669_);
lean_ctor_set(v_reuseFailAlloc_683_, 5, v_numSectionVars_670_);
lean_ctor_set(v_reuseFailAlloc_683_, 6, v_type_671_);
lean_ctor_set(v_reuseFailAlloc_683_, 7, v_b_676_);
lean_ctor_set(v_reuseFailAlloc_683_, 8, v_termination_672_);
lean_ctor_set_uint8(v_reuseFailAlloc_683_, sizeof(void*)*9, v_kind_665_);
v___x_678_ = v_reuseFailAlloc_683_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_679_ = lean_unsigned_to_nat(1u);
v___x_680_ = lean_nat_add(v_i_657_, v___x_679_);
lean_dec(v_i_657_);
v___x_681_ = lean_array_push(v_cs_658_, v___x_678_);
v_i_657_ = v___x_680_;
v_cs_658_ = v___x_681_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10___boxed(lean_object* v_as_686_, lean_object* v_bs_687_, lean_object* v_i_688_, lean_object* v_cs_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v_as_686_, v_bs_687_, v_i_688_, v_cs_689_);
lean_dec_ref(v_bs_687_);
lean_dec_ref(v_as_686_);
return v_res_690_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__2(void){
_start:
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_694_ = lean_box(0);
v___x_695_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__1));
v___x_696_ = l_Lean_Expr_const___override(v___x_695_, v___x_694_);
return v___x_696_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__4(void){
_start:
{
lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_698_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__3));
v___x_699_ = l_Lean_stringToMessageData(v___x_698_);
return v___x_699_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__6(void){
_start:
{
lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_701_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__5));
v___x_702_ = l_Lean_stringToMessageData(v___x_701_);
return v___x_702_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__8(void){
_start:
{
lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_704_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__7));
v___x_705_ = l_Lean_stringToMessageData(v___x_704_);
return v___x_705_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__10(void){
_start:
{
lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_707_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__9));
v___x_708_ = l_Lean_stringToMessageData(v___x_707_);
return v___x_708_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__12(void){
_start:
{
lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_710_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__11));
v___x_711_ = l_Lean_stringToMessageData(v___x_710_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2(lean_object* v___x_712_, lean_object* v_recArgInfos_713_, lean_object* v_a_714_, lean_object* v___x_715_, lean_object* v___x_716_, lean_object* v_fixedParamPerms_717_, lean_object* v_xs_718_, lean_object* v_preDefs_719_, lean_object* v_numIndices_720_, lean_object* v___x_721_, lean_object* v___f_722_, uint8_t v_a_723_, lean_object* v_funTypes_724_, lean_object* v_motives_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_){
_start:
{
lean_object* v___y_733_; lean_object* v___y_734_; lean_object* v___y_735_; lean_object* v___y_736_; lean_object* v___y_737_; lean_object* v___y_738_; lean_object* v___y_739_; lean_object* v___y_776_; lean_object* v___y_777_; lean_object* v___y_778_; lean_object* v___y_779_; lean_object* v___y_780_; lean_object* v___y_781_; lean_object* v___y_782_; lean_object* v___y_829_; lean_object* v___y_830_; lean_object* v___y_831_; lean_object* v___y_832_; lean_object* v___y_833_; lean_object* v___y_834_; lean_object* v___y_835_; lean_object* v___y_867_; lean_object* v___y_868_; lean_object* v___y_869_; lean_object* v___y_870_; lean_object* v___y_871_; lean_object* v___x_910_; lean_object* v_a_911_; uint8_t v___x_912_; 
lean_inc(v___x_712_);
v___x_910_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___redArg(v___x_712_, v___y_729_);
v_a_911_ = lean_ctor_get(v___x_910_, 0);
lean_inc(v_a_911_);
lean_dec_ref(v___x_910_);
v___x_912_ = lean_unbox(v_a_911_);
lean_dec(v_a_911_);
if (v___x_912_ == 0)
{
v___y_867_ = v___y_726_;
v___y_868_ = v___y_727_;
v___y_869_ = v___y_728_;
v___y_870_ = v___y_729_;
v___y_871_ = v___y_730_;
goto v___jp_866_;
}
else
{
lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; 
v___x_913_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__10, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__10);
lean_inc_ref(v_funTypes_724_);
v___x_914_ = lean_array_to_list(v_funTypes_724_);
v___x_915_ = lean_box(0);
v___x_916_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_914_, v___x_915_);
v___x_917_ = l_Lean_MessageData_ofList(v___x_916_);
v___x_918_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_918_, 0, v___x_913_);
lean_ctor_set(v___x_918_, 1, v___x_917_);
v___x_919_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__12, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__12_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__12);
v___x_920_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_920_, 0, v___x_918_);
lean_ctor_set(v___x_920_, 1, v___x_919_);
lean_inc_ref(v_motives_725_);
v___x_921_ = lean_array_to_list(v_motives_725_);
v___x_922_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_921_, v___x_915_);
v___x_923_ = l_Lean_MessageData_ofList(v___x_922_);
v___x_924_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_924_, 0, v___x_920_);
lean_ctor_set(v___x_924_, 1, v___x_923_);
lean_inc(v___x_712_);
v___x_925_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v___x_712_, v___x_924_, v___y_727_, v___y_728_, v___y_729_, v___y_730_);
if (lean_obj_tag(v___x_925_) == 0)
{
lean_dec_ref(v___x_925_);
v___y_867_ = v___y_726_;
v___y_868_ = v___y_727_;
v___y_869_ = v___y_728_;
v___y_870_ = v___y_729_;
v___y_871_ = v___y_730_;
goto v___jp_866_;
}
else
{
lean_object* v_a_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_933_; 
lean_dec(v___y_730_);
lean_dec_ref(v___y_729_);
lean_dec(v___y_728_);
lean_dec_ref(v___y_727_);
lean_dec(v___y_726_);
lean_dec_ref(v_motives_725_);
lean_dec_ref(v_funTypes_724_);
lean_dec_ref(v___f_722_);
lean_dec_ref(v___x_721_);
lean_dec_ref(v_xs_718_);
lean_dec_ref(v_fixedParamPerms_717_);
lean_dec(v___x_716_);
lean_dec_ref(v___x_715_);
lean_dec_ref(v_recArgInfos_713_);
lean_dec(v___x_712_);
v_a_926_ = lean_ctor_get(v___x_925_, 0);
v_isSharedCheck_933_ = !lean_is_exclusive(v___x_925_);
if (v_isSharedCheck_933_ == 0)
{
v___x_928_ = v___x_925_;
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_a_926_);
lean_dec(v___x_925_);
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
v___jp_732_:
{
lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_740_ = l_Array_zip___redArg(v_recArgInfos_713_, v_a_714_);
lean_dec_ref(v_recArgInfos_713_);
v___x_741_ = lean_array_get_size(v___x_740_);
v___x_742_ = lean_mk_empty_array_with_capacity(v___x_741_);
lean_inc(v___y_739_);
lean_inc_ref(v___y_738_);
lean_inc(v___y_737_);
lean_inc_ref(v___y_736_);
lean_inc(v___x_716_);
v___x_743_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg(v___x_715_, v___y_734_, v___y_733_, v_funTypes_724_, v___x_740_, v___x_741_, v___x_716_, v___x_742_, v___y_736_, v___y_737_, v___y_738_, v___y_739_);
lean_dec_ref(v___x_740_);
if (lean_obj_tag(v___x_743_) == 0)
{
lean_object* v_a_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; 
v_a_744_ = lean_ctor_get(v___x_743_, 0);
lean_inc(v_a_744_);
lean_dec_ref(v___x_743_);
v___x_745_ = l_Array_zip___redArg(v_a_714_, v_a_744_);
lean_dec(v_a_744_);
v___x_746_ = lean_array_get_size(v___x_745_);
v___x_747_ = lean_mk_empty_array_with_capacity(v___x_746_);
lean_inc(v___x_716_);
v___x_748_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9___redArg(v_fixedParamPerms_717_, v_xs_718_, v___x_745_, v___x_746_, v___x_716_, v___x_747_, v___y_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_);
lean_dec_ref(v___x_745_);
if (lean_obj_tag(v___x_748_) == 0)
{
lean_object* v_a_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_758_; 
v_a_749_ = lean_ctor_get(v___x_748_, 0);
v_isSharedCheck_758_ = !lean_is_exclusive(v___x_748_);
if (v_isSharedCheck_758_ == 0)
{
v___x_751_ = v___x_748_;
v_isShared_752_ = v_isSharedCheck_758_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_a_749_);
lean_dec(v___x_748_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_758_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_756_; 
v___x_753_ = lean_mk_empty_array_with_capacity(v___x_716_);
v___x_754_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v_preDefs_719_, v_a_749_, v___x_716_, v___x_753_);
lean_dec(v_a_749_);
if (v_isShared_752_ == 0)
{
lean_ctor_set(v___x_751_, 0, v___x_754_);
v___x_756_ = v___x_751_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v___x_754_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
}
}
}
else
{
lean_object* v_a_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_766_; 
lean_dec(v___x_716_);
v_a_759_ = lean_ctor_get(v___x_748_, 0);
v_isSharedCheck_766_ = !lean_is_exclusive(v___x_748_);
if (v_isSharedCheck_766_ == 0)
{
v___x_761_ = v___x_748_;
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_a_759_);
lean_dec(v___x_748_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v___x_764_; 
if (v_isShared_762_ == 0)
{
v___x_764_ = v___x_761_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v_a_759_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
return v___x_764_;
}
}
}
}
else
{
lean_object* v_a_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_774_; 
lean_dec(v___y_739_);
lean_dec_ref(v___y_738_);
lean_dec(v___y_737_);
lean_dec_ref(v___y_736_);
lean_dec(v___y_735_);
lean_dec_ref(v_xs_718_);
lean_dec_ref(v_fixedParamPerms_717_);
lean_dec(v___x_716_);
v_a_767_ = lean_ctor_get(v___x_743_, 0);
v_isSharedCheck_774_ = !lean_is_exclusive(v___x_743_);
if (v_isSharedCheck_774_ == 0)
{
v___x_769_ = v___x_743_;
v_isShared_770_ = v_isSharedCheck_774_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_a_767_);
lean_dec(v___x_743_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_774_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v___x_772_; 
if (v_isShared_770_ == 0)
{
v___x_772_ = v___x_769_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v_a_767_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
return v___x_772_;
}
}
}
}
v___jp_775_:
{
lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; 
lean_inc_ref(v___y_776_);
lean_inc(v___x_716_);
v___x_783_ = lean_apply_1(v___y_776_, v___x_716_);
v___x_784_ = lean_unsigned_to_nat(1u);
v___x_785_ = lean_nat_add(v_numIndices_720_, v___x_784_);
v___x_786_ = lean_box(0);
v___x_787_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__2);
v___x_788_ = lean_mk_array(v___x_785_, v___x_787_);
v___x_789_ = l_Lean_mkAppN(v___x_783_, v___x_788_);
lean_dec_ref(v___x_788_);
v___x_790_ = lean_array_get_size(v___x_715_);
lean_inc(v___y_782_);
lean_inc_ref(v___y_781_);
lean_inc(v___y_780_);
lean_inc_ref(v___y_779_);
v___x_791_ = l_Lean_Meta_inferArgumentTypesN(v___x_790_, v___x_789_, v___y_779_, v___y_780_, v___y_781_, v___y_782_);
if (lean_obj_tag(v___x_791_) == 0)
{
lean_object* v_a_792_; lean_object* v___x_793_; 
v_a_792_ = lean_ctor_get(v___x_791_, 0);
lean_inc(v_a_792_);
lean_dec_ref(v___x_791_);
lean_inc(v___y_782_);
lean_inc_ref(v___y_781_);
lean_inc(v___y_780_);
lean_inc_ref(v___y_779_);
lean_inc(v___y_778_);
v___x_793_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg(v___x_721_, v___f_722_, v___x_715_, v_a_792_, v___y_777_, v___y_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_);
lean_dec_ref(v___y_777_);
lean_dec(v_a_792_);
if (lean_obj_tag(v___x_793_) == 0)
{
lean_object* v_a_794_; lean_object* v___x_795_; lean_object* v_a_796_; uint8_t v___x_797_; 
v_a_794_ = lean_ctor_get(v___x_793_, 0);
lean_inc(v_a_794_);
lean_dec_ref(v___x_793_);
lean_inc(v___x_712_);
v___x_795_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___redArg(v___x_712_, v___y_781_);
v_a_796_ = lean_ctor_get(v___x_795_, 0);
lean_inc(v_a_796_);
lean_dec_ref(v___x_795_);
v___x_797_ = lean_unbox(v_a_796_);
lean_dec(v_a_796_);
if (v___x_797_ == 0)
{
lean_dec(v___x_712_);
v___y_733_ = v_a_794_;
v___y_734_ = v___y_776_;
v___y_735_ = v___y_778_;
v___y_736_ = v___y_779_;
v___y_737_ = v___y_780_;
v___y_738_ = v___y_781_;
v___y_739_ = v___y_782_;
goto v___jp_732_;
}
else
{
lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_798_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__4);
lean_inc(v_a_794_);
v___x_799_ = lean_array_to_list(v_a_794_);
v___x_800_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_799_, v___x_786_);
v___x_801_ = l_Lean_MessageData_ofList(v___x_800_);
v___x_802_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_802_, 0, v___x_798_);
lean_ctor_set(v___x_802_, 1, v___x_801_);
v___x_803_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v___x_712_, v___x_802_, v___y_779_, v___y_780_, v___y_781_, v___y_782_);
if (lean_obj_tag(v___x_803_) == 0)
{
lean_dec_ref(v___x_803_);
v___y_733_ = v_a_794_;
v___y_734_ = v___y_776_;
v___y_735_ = v___y_778_;
v___y_736_ = v___y_779_;
v___y_737_ = v___y_780_;
v___y_738_ = v___y_781_;
v___y_739_ = v___y_782_;
goto v___jp_732_;
}
else
{
lean_object* v_a_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_811_; 
lean_dec(v_a_794_);
lean_dec(v___y_782_);
lean_dec_ref(v___y_781_);
lean_dec(v___y_780_);
lean_dec_ref(v___y_779_);
lean_dec(v___y_778_);
lean_dec_ref(v___y_776_);
lean_dec_ref(v_funTypes_724_);
lean_dec_ref(v_xs_718_);
lean_dec_ref(v_fixedParamPerms_717_);
lean_dec(v___x_716_);
lean_dec_ref(v___x_715_);
lean_dec_ref(v_recArgInfos_713_);
v_a_804_ = lean_ctor_get(v___x_803_, 0);
v_isSharedCheck_811_ = !lean_is_exclusive(v___x_803_);
if (v_isSharedCheck_811_ == 0)
{
v___x_806_ = v___x_803_;
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_a_804_);
lean_dec(v___x_803_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v___x_809_; 
if (v_isShared_807_ == 0)
{
v___x_809_ = v___x_806_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v_a_804_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
return v___x_809_;
}
}
}
}
}
else
{
lean_object* v_a_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_819_; 
lean_dec(v___y_782_);
lean_dec_ref(v___y_781_);
lean_dec(v___y_780_);
lean_dec_ref(v___y_779_);
lean_dec(v___y_778_);
lean_dec_ref(v___y_776_);
lean_dec_ref(v_funTypes_724_);
lean_dec_ref(v_xs_718_);
lean_dec_ref(v_fixedParamPerms_717_);
lean_dec(v___x_716_);
lean_dec_ref(v___x_715_);
lean_dec_ref(v_recArgInfos_713_);
lean_dec(v___x_712_);
v_a_812_ = lean_ctor_get(v___x_793_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v___x_793_);
if (v_isSharedCheck_819_ == 0)
{
v___x_814_ = v___x_793_;
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_a_812_);
lean_dec(v___x_793_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_817_; 
if (v_isShared_815_ == 0)
{
v___x_817_ = v___x_814_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_a_812_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
}
}
else
{
lean_object* v_a_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_827_; 
lean_dec(v___y_782_);
lean_dec_ref(v___y_781_);
lean_dec(v___y_780_);
lean_dec_ref(v___y_779_);
lean_dec(v___y_778_);
lean_dec_ref(v___y_777_);
lean_dec_ref(v___y_776_);
lean_dec_ref(v_funTypes_724_);
lean_dec_ref(v___f_722_);
lean_dec_ref(v___x_721_);
lean_dec_ref(v_xs_718_);
lean_dec_ref(v_fixedParamPerms_717_);
lean_dec(v___x_716_);
lean_dec_ref(v___x_715_);
lean_dec_ref(v_recArgInfos_713_);
lean_dec(v___x_712_);
v_a_820_ = lean_ctor_get(v___x_791_, 0);
v_isSharedCheck_827_ = !lean_is_exclusive(v___x_791_);
if (v_isSharedCheck_827_ == 0)
{
v___x_822_ = v___x_791_;
v_isShared_823_ = v_isSharedCheck_827_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_a_820_);
lean_dec(v___x_791_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_827_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v___x_825_; 
if (v_isShared_823_ == 0)
{
v___x_825_ = v___x_822_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v_a_820_);
v___x_825_ = v_reuseFailAlloc_826_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
return v___x_825_;
}
}
}
}
v___jp_828_:
{
lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_836_ = lean_array_get_size(v_recArgInfos_713_);
v___x_837_ = lean_mk_empty_array_with_capacity(v___x_836_);
lean_inc(v___y_835_);
lean_inc_ref(v___y_834_);
lean_inc(v___y_833_);
lean_inc_ref(v___y_832_);
lean_inc(v___y_831_);
lean_inc(v___x_716_);
lean_inc_ref(v___y_830_);
lean_inc_ref(v___x_715_);
lean_inc_ref(v_recArgInfos_713_);
v___x_838_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg(v_a_714_, v___y_829_, v_a_723_, v_recArgInfos_713_, v___x_715_, v___y_830_, v_recArgInfos_713_, v___x_836_, v___x_716_, v___x_837_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_);
lean_dec_ref(v___y_829_);
if (lean_obj_tag(v___x_838_) == 0)
{
lean_object* v_a_839_; lean_object* v___x_840_; lean_object* v_a_841_; uint8_t v___x_842_; 
v_a_839_ = lean_ctor_get(v___x_838_, 0);
lean_inc(v_a_839_);
lean_dec_ref(v___x_838_);
lean_inc(v___x_712_);
v___x_840_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___redArg(v___x_712_, v___y_834_);
v_a_841_ = lean_ctor_get(v___x_840_, 0);
lean_inc(v_a_841_);
lean_dec_ref(v___x_840_);
v___x_842_ = lean_unbox(v_a_841_);
lean_dec(v_a_841_);
if (v___x_842_ == 0)
{
v___y_776_ = v___y_830_;
v___y_777_ = v_a_839_;
v___y_778_ = v___y_831_;
v___y_779_ = v___y_832_;
v___y_780_ = v___y_833_;
v___y_781_ = v___y_834_;
v___y_782_ = v___y_835_;
goto v___jp_775_;
}
else
{
lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; 
v___x_843_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__6, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__6);
lean_inc(v_a_839_);
v___x_844_ = lean_array_to_list(v_a_839_);
v___x_845_ = lean_box(0);
v___x_846_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_844_, v___x_845_);
v___x_847_ = l_Lean_MessageData_ofList(v___x_846_);
v___x_848_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_848_, 0, v___x_843_);
lean_ctor_set(v___x_848_, 1, v___x_847_);
lean_inc(v___x_712_);
v___x_849_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v___x_712_, v___x_848_, v___y_832_, v___y_833_, v___y_834_, v___y_835_);
if (lean_obj_tag(v___x_849_) == 0)
{
lean_dec_ref(v___x_849_);
v___y_776_ = v___y_830_;
v___y_777_ = v_a_839_;
v___y_778_ = v___y_831_;
v___y_779_ = v___y_832_;
v___y_780_ = v___y_833_;
v___y_781_ = v___y_834_;
v___y_782_ = v___y_835_;
goto v___jp_775_;
}
else
{
lean_object* v_a_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_857_; 
lean_dec(v_a_839_);
lean_dec(v___y_835_);
lean_dec_ref(v___y_834_);
lean_dec(v___y_833_);
lean_dec_ref(v___y_832_);
lean_dec(v___y_831_);
lean_dec_ref(v___y_830_);
lean_dec_ref(v_funTypes_724_);
lean_dec_ref(v___f_722_);
lean_dec_ref(v___x_721_);
lean_dec_ref(v_xs_718_);
lean_dec_ref(v_fixedParamPerms_717_);
lean_dec(v___x_716_);
lean_dec_ref(v___x_715_);
lean_dec_ref(v_recArgInfos_713_);
lean_dec(v___x_712_);
v_a_850_ = lean_ctor_get(v___x_849_, 0);
v_isSharedCheck_857_ = !lean_is_exclusive(v___x_849_);
if (v_isSharedCheck_857_ == 0)
{
v___x_852_ = v___x_849_;
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_a_850_);
lean_dec(v___x_849_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v___x_855_; 
if (v_isShared_853_ == 0)
{
v___x_855_ = v___x_852_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v_a_850_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
return v___x_855_;
}
}
}
}
}
else
{
lean_object* v_a_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_865_; 
lean_dec(v___y_835_);
lean_dec_ref(v___y_834_);
lean_dec(v___y_833_);
lean_dec_ref(v___y_832_);
lean_dec(v___y_831_);
lean_dec_ref(v___y_830_);
lean_dec_ref(v_funTypes_724_);
lean_dec_ref(v___f_722_);
lean_dec_ref(v___x_721_);
lean_dec_ref(v_xs_718_);
lean_dec_ref(v_fixedParamPerms_717_);
lean_dec(v___x_716_);
lean_dec_ref(v___x_715_);
lean_dec_ref(v_recArgInfos_713_);
lean_dec(v___x_712_);
v_a_858_ = lean_ctor_get(v___x_838_, 0);
v_isSharedCheck_865_ = !lean_is_exclusive(v___x_838_);
if (v_isSharedCheck_865_ == 0)
{
v___x_860_ = v___x_838_;
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_a_858_);
lean_dec(v___x_838_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
lean_object* v___x_863_; 
if (v_isShared_861_ == 0)
{
v___x_863_ = v___x_860_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v_a_858_);
v___x_863_ = v_reuseFailAlloc_864_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
return v___x_863_;
}
}
}
}
v___jp_866_:
{
lean_object* v___x_872_; 
lean_inc(v___y_871_);
lean_inc_ref(v___y_870_);
lean_inc(v___y_869_);
lean_inc_ref(v___y_868_);
v___x_872_ = l_Lean_Elab_Structural_mkBRecOnConst(v_recArgInfos_713_, v___x_715_, v_motives_725_, v_a_723_, v___y_868_, v___y_869_, v___y_870_, v___y_871_);
lean_dec_ref(v_motives_725_);
if (lean_obj_tag(v___x_872_) == 0)
{
lean_object* v_a_873_; lean_object* v___x_874_; 
v_a_873_ = lean_ctor_get(v___x_872_, 0);
lean_inc(v_a_873_);
lean_dec_ref(v___x_872_);
lean_inc(v___y_871_);
lean_inc_ref(v___y_870_);
lean_inc(v___y_869_);
lean_inc_ref(v___y_868_);
lean_inc(v_a_873_);
lean_inc_ref(v___x_715_);
v___x_874_ = l_Lean_Elab_Structural_inferBRecOnFTypes(v_recArgInfos_713_, v___x_715_, v_a_873_, v___y_868_, v___y_869_, v___y_870_, v___y_871_);
if (lean_obj_tag(v___x_874_) == 0)
{
lean_object* v_a_875_; lean_object* v___x_876_; lean_object* v_a_877_; uint8_t v___x_878_; 
v_a_875_ = lean_ctor_get(v___x_874_, 0);
lean_inc(v_a_875_);
lean_dec_ref(v___x_874_);
lean_inc(v___x_712_);
v___x_876_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___redArg(v___x_712_, v___y_870_);
v_a_877_ = lean_ctor_get(v___x_876_, 0);
lean_inc(v_a_877_);
lean_dec_ref(v___x_876_);
v___x_878_ = lean_unbox(v_a_877_);
lean_dec(v_a_877_);
if (v___x_878_ == 0)
{
v___y_829_ = v_a_875_;
v___y_830_ = v_a_873_;
v___y_831_ = v___y_867_;
v___y_832_ = v___y_868_;
v___y_833_ = v___y_869_;
v___y_834_ = v___y_870_;
v___y_835_ = v___y_871_;
goto v___jp_828_;
}
else
{
lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_879_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__8);
lean_inc(v_a_875_);
v___x_880_ = lean_array_to_list(v_a_875_);
v___x_881_ = lean_box(0);
v___x_882_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_880_, v___x_881_);
v___x_883_ = l_Lean_MessageData_ofList(v___x_882_);
v___x_884_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_884_, 0, v___x_879_);
lean_ctor_set(v___x_884_, 1, v___x_883_);
lean_inc(v___x_712_);
v___x_885_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v___x_712_, v___x_884_, v___y_868_, v___y_869_, v___y_870_, v___y_871_);
if (lean_obj_tag(v___x_885_) == 0)
{
lean_dec_ref(v___x_885_);
v___y_829_ = v_a_875_;
v___y_830_ = v_a_873_;
v___y_831_ = v___y_867_;
v___y_832_ = v___y_868_;
v___y_833_ = v___y_869_;
v___y_834_ = v___y_870_;
v___y_835_ = v___y_871_;
goto v___jp_828_;
}
else
{
lean_object* v_a_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_893_; 
lean_dec(v_a_875_);
lean_dec(v_a_873_);
lean_dec(v___y_871_);
lean_dec_ref(v___y_870_);
lean_dec(v___y_869_);
lean_dec_ref(v___y_868_);
lean_dec(v___y_867_);
lean_dec_ref(v_funTypes_724_);
lean_dec_ref(v___f_722_);
lean_dec_ref(v___x_721_);
lean_dec_ref(v_xs_718_);
lean_dec_ref(v_fixedParamPerms_717_);
lean_dec(v___x_716_);
lean_dec_ref(v___x_715_);
lean_dec_ref(v_recArgInfos_713_);
lean_dec(v___x_712_);
v_a_886_ = lean_ctor_get(v___x_885_, 0);
v_isSharedCheck_893_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_893_ == 0)
{
v___x_888_ = v___x_885_;
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_a_886_);
lean_dec(v___x_885_);
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
else
{
lean_object* v_a_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_901_; 
lean_dec(v_a_873_);
lean_dec(v___y_871_);
lean_dec_ref(v___y_870_);
lean_dec(v___y_869_);
lean_dec_ref(v___y_868_);
lean_dec(v___y_867_);
lean_dec_ref(v_funTypes_724_);
lean_dec_ref(v___f_722_);
lean_dec_ref(v___x_721_);
lean_dec_ref(v_xs_718_);
lean_dec_ref(v_fixedParamPerms_717_);
lean_dec(v___x_716_);
lean_dec_ref(v___x_715_);
lean_dec_ref(v_recArgInfos_713_);
lean_dec(v___x_712_);
v_a_894_ = lean_ctor_get(v___x_874_, 0);
v_isSharedCheck_901_ = !lean_is_exclusive(v___x_874_);
if (v_isSharedCheck_901_ == 0)
{
v___x_896_ = v___x_874_;
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_a_894_);
lean_dec(v___x_874_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v___x_899_; 
if (v_isShared_897_ == 0)
{
v___x_899_ = v___x_896_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v_a_894_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
return v___x_899_;
}
}
}
}
else
{
lean_object* v_a_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_909_; 
lean_dec(v___y_871_);
lean_dec_ref(v___y_870_);
lean_dec(v___y_869_);
lean_dec_ref(v___y_868_);
lean_dec(v___y_867_);
lean_dec_ref(v_funTypes_724_);
lean_dec_ref(v___f_722_);
lean_dec_ref(v___x_721_);
lean_dec_ref(v_xs_718_);
lean_dec_ref(v_fixedParamPerms_717_);
lean_dec(v___x_716_);
lean_dec_ref(v___x_715_);
lean_dec_ref(v_recArgInfos_713_);
lean_dec(v___x_712_);
v_a_902_ = lean_ctor_get(v___x_872_, 0);
v_isSharedCheck_909_ = !lean_is_exclusive(v___x_872_);
if (v_isSharedCheck_909_ == 0)
{
v___x_904_ = v___x_872_;
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_a_902_);
lean_dec(v___x_872_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_907_; 
if (v_isShared_905_ == 0)
{
v___x_907_ = v___x_904_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v_a_902_);
v___x_907_ = v_reuseFailAlloc_908_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
return v___x_907_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___boxed(lean_object** _args){
lean_object* v___x_934_ = _args[0];
lean_object* v_recArgInfos_935_ = _args[1];
lean_object* v_a_936_ = _args[2];
lean_object* v___x_937_ = _args[3];
lean_object* v___x_938_ = _args[4];
lean_object* v_fixedParamPerms_939_ = _args[5];
lean_object* v_xs_940_ = _args[6];
lean_object* v_preDefs_941_ = _args[7];
lean_object* v_numIndices_942_ = _args[8];
lean_object* v___x_943_ = _args[9];
lean_object* v___f_944_ = _args[10];
lean_object* v_a_945_ = _args[11];
lean_object* v_funTypes_946_ = _args[12];
lean_object* v_motives_947_ = _args[13];
lean_object* v___y_948_ = _args[14];
lean_object* v___y_949_ = _args[15];
lean_object* v___y_950_ = _args[16];
lean_object* v___y_951_ = _args[17];
lean_object* v___y_952_ = _args[18];
lean_object* v___y_953_ = _args[19];
_start:
{
uint8_t v_a_27592__boxed_954_; lean_object* v_res_955_; 
v_a_27592__boxed_954_ = lean_unbox(v_a_945_);
v_res_955_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2(v___x_934_, v_recArgInfos_935_, v_a_936_, v___x_937_, v___x_938_, v_fixedParamPerms_939_, v_xs_940_, v_preDefs_941_, v_numIndices_942_, v___x_943_, v___f_944_, v_a_27592__boxed_954_, v_funTypes_946_, v_motives_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_);
lean_dec(v_numIndices_942_);
lean_dec_ref(v_preDefs_941_);
lean_dec_ref(v_a_936_);
return v_res_955_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13___redArg(lean_object* v_a_956_, lean_object* v_funTypes_957_, lean_object* v_as_958_, lean_object* v_i_959_, lean_object* v_j_960_, lean_object* v_bs_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_){
_start:
{
lean_object* v_zero_968_; uint8_t v_isZero_969_; 
v_zero_968_ = lean_unsigned_to_nat(0u);
v_isZero_969_ = lean_nat_dec_eq(v_i_959_, v_zero_968_);
if (v_isZero_969_ == 1)
{
lean_object* v___x_970_; 
lean_dec(v___y_966_);
lean_dec_ref(v___y_965_);
lean_dec(v___y_964_);
lean_dec_ref(v___y_963_);
lean_dec(v___y_962_);
lean_dec(v_j_960_);
lean_dec(v_i_959_);
v___x_970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_970_, 0, v_bs_961_);
return v___x_970_;
}
else
{
lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_971_ = l_Lean_instInhabitedExpr;
v___x_972_ = lean_array_fget_borrowed(v_as_958_, v_j_960_);
v___x_973_ = lean_array_get_borrowed(v___x_971_, v_a_956_, v_j_960_);
v___x_974_ = lean_array_get_borrowed(v___x_971_, v_funTypes_957_, v_j_960_);
lean_inc(v___y_966_);
lean_inc_ref(v___y_965_);
lean_inc(v___y_964_);
lean_inc_ref(v___y_963_);
lean_inc(v___y_962_);
lean_inc(v___x_974_);
lean_inc(v___x_973_);
lean_inc(v___x_972_);
v___x_975_ = l_Lean_Elab_Structural_mkIndPredBRecOnMotive(v___x_972_, v___x_973_, v___x_974_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_);
if (lean_obj_tag(v___x_975_) == 0)
{
lean_object* v_a_976_; lean_object* v_one_977_; lean_object* v_n_978_; lean_object* v___x_979_; lean_object* v___x_980_; 
v_a_976_ = lean_ctor_get(v___x_975_, 0);
lean_inc(v_a_976_);
lean_dec_ref(v___x_975_);
v_one_977_ = lean_unsigned_to_nat(1u);
v_n_978_ = lean_nat_sub(v_i_959_, v_one_977_);
lean_dec(v_i_959_);
v___x_979_ = lean_nat_add(v_j_960_, v_one_977_);
lean_dec(v_j_960_);
v___x_980_ = lean_array_push(v_bs_961_, v_a_976_);
v_i_959_ = v_n_978_;
v_j_960_ = v___x_979_;
v_bs_961_ = v___x_980_;
goto _start;
}
else
{
lean_object* v_a_982_; lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_989_; 
lean_dec(v___y_966_);
lean_dec_ref(v___y_965_);
lean_dec(v___y_964_);
lean_dec_ref(v___y_963_);
lean_dec(v___y_962_);
lean_dec_ref(v_bs_961_);
lean_dec(v_j_960_);
lean_dec(v_i_959_);
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
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13___redArg___boxed(lean_object* v_a_990_, lean_object* v_funTypes_991_, lean_object* v_as_992_, lean_object* v_i_993_, lean_object* v_j_994_, lean_object* v_bs_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_){
_start:
{
lean_object* v_res_1002_; 
v_res_1002_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13___redArg(v_a_990_, v_funTypes_991_, v_as_992_, v_i_993_, v_j_994_, v_bs_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_);
lean_dec_ref(v_as_992_);
lean_dec_ref(v_funTypes_991_);
lean_dec_ref(v_a_990_);
return v_res_1002_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__3(lean_object* v_recArgInfos_1003_, lean_object* v_a_1004_, lean_object* v___x_1005_, lean_object* v___f_1006_, lean_object* v_funTypes_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_){
_start:
{
lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1014_ = lean_array_get_size(v_recArgInfos_1003_);
v___x_1015_ = lean_mk_empty_array_with_capacity(v___x_1014_);
lean_inc(v___y_1012_);
lean_inc_ref(v___y_1011_);
lean_inc(v___y_1010_);
lean_inc_ref(v___y_1009_);
lean_inc(v___y_1008_);
v___x_1016_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13___redArg(v_a_1004_, v_funTypes_1007_, v_recArgInfos_1003_, v___x_1014_, v___x_1005_, v___x_1015_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_);
if (lean_obj_tag(v___x_1016_) == 0)
{
lean_object* v_a_1017_; lean_object* v___x_1018_; 
v_a_1017_ = lean_ctor_get(v___x_1016_, 0);
lean_inc(v_a_1017_);
lean_dec_ref(v___x_1016_);
v___x_1018_ = lean_apply_8(v___f_1006_, v_funTypes_1007_, v_a_1017_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, lean_box(0));
return v___x_1018_;
}
else
{
lean_object* v_a_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1026_; 
lean_dec(v___y_1012_);
lean_dec_ref(v___y_1011_);
lean_dec(v___y_1010_);
lean_dec_ref(v___y_1009_);
lean_dec(v___y_1008_);
lean_dec_ref(v_funTypes_1007_);
lean_dec_ref(v___f_1006_);
v_a_1019_ = lean_ctor_get(v___x_1016_, 0);
v_isSharedCheck_1026_ = !lean_is_exclusive(v___x_1016_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_1021_ = v___x_1016_;
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_a_1019_);
lean_dec(v___x_1016_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v___x_1024_; 
if (v_isShared_1022_ == 0)
{
v___x_1024_ = v___x_1021_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v_a_1019_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__3___boxed(lean_object* v_recArgInfos_1027_, lean_object* v_a_1028_, lean_object* v___x_1029_, lean_object* v___f_1030_, lean_object* v_funTypes_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_){
_start:
{
lean_object* v_res_1038_; 
v_res_1038_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__3(v_recArgInfos_1027_, v_a_1028_, v___x_1029_, v___f_1030_, v_funTypes_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_);
lean_dec_ref(v_a_1028_);
lean_dec_ref(v_recArgInfos_1027_);
return v_res_1038_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg(lean_object* v_as_1040_, lean_object* v_lo_1041_, lean_object* v_hi_1042_){
_start:
{
uint8_t v___x_1043_; 
v___x_1043_ = lean_nat_dec_lt(v_lo_1041_, v_hi_1042_);
if (v___x_1043_ == 0)
{
lean_dec(v_lo_1041_);
return v_as_1040_;
}
else
{
lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v_fst_1046_; lean_object* v_snd_1047_; uint8_t v___x_1048_; 
v___x_1044_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg___closed__0));
lean_inc(v_lo_1041_);
v___x_1045_ = l_Array_qpartition___redArg(v_as_1040_, v___x_1044_, v_lo_1041_, v_hi_1042_);
v_fst_1046_ = lean_ctor_get(v___x_1045_, 0);
lean_inc(v_fst_1046_);
v_snd_1047_ = lean_ctor_get(v___x_1045_, 1);
lean_inc(v_snd_1047_);
lean_dec_ref(v___x_1045_);
v___x_1048_ = lean_nat_dec_le(v_hi_1042_, v_fst_1046_);
if (v___x_1048_ == 0)
{
lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; 
v___x_1049_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg(v_snd_1047_, v_lo_1041_, v_fst_1046_);
v___x_1050_ = lean_unsigned_to_nat(1u);
v___x_1051_ = lean_nat_add(v_fst_1046_, v___x_1050_);
lean_dec(v_fst_1046_);
v_as_1040_ = v___x_1049_;
v_lo_1041_ = v___x_1051_;
goto _start;
}
else
{
lean_dec(v_fst_1046_);
lean_dec(v_lo_1041_);
return v_snd_1047_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg___boxed(lean_object* v_as_1053_, lean_object* v_lo_1054_, lean_object* v_hi_1055_){
_start:
{
lean_object* v_res_1056_; 
v_res_1056_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg(v_as_1053_, v_lo_1054_, v_hi_1055_);
lean_dec(v_hi_1055_);
return v_res_1056_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__11(lean_object* v_as_1057_, size_t v_i_1058_, size_t v_stop_1059_, lean_object* v_b_1060_){
_start:
{
uint8_t v___x_1061_; 
v___x_1061_ = lean_usize_dec_eq(v_i_1058_, v_stop_1059_);
if (v___x_1061_ == 0)
{
lean_object* v___x_1062_; lean_object* v___x_1063_; size_t v___x_1064_; size_t v___x_1065_; 
v___x_1062_ = lean_array_uget_borrowed(v_as_1057_, v_i_1058_);
v___x_1063_ = l_Array_append___redArg(v_b_1060_, v___x_1062_);
v___x_1064_ = ((size_t)1ULL);
v___x_1065_ = lean_usize_add(v_i_1058_, v___x_1064_);
v_i_1058_ = v___x_1065_;
v_b_1060_ = v___x_1063_;
goto _start;
}
else
{
return v_b_1060_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__11___boxed(lean_object* v_as_1067_, lean_object* v_i_1068_, lean_object* v_stop_1069_, lean_object* v_b_1070_){
_start:
{
size_t v_i_boxed_1071_; size_t v_stop_boxed_1072_; lean_object* v_res_1073_; 
v_i_boxed_1071_ = lean_unbox_usize(v_i_1068_);
lean_dec(v_i_1068_);
v_stop_boxed_1072_ = lean_unbox_usize(v_stop_1069_);
lean_dec(v_stop_1069_);
v_res_1073_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__11(v_as_1067_, v_i_boxed_1071_, v_stop_boxed_1072_, v_b_1070_);
lean_dec_ref(v_as_1067_);
return v_res_1073_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__6___redArg(lean_object* v_inst_1074_, lean_object* v_xs_1075_, lean_object* v_f_1076_, lean_object* v_x_1077_, lean_object* v_as_1078_, size_t v_i_1079_, size_t v_stop_1080_, lean_object* v_b_1081_){
_start:
{
lean_object* v___y_1083_; uint8_t v___x_1087_; 
v___x_1087_ = lean_usize_dec_eq(v_i_1079_, v_stop_1080_);
if (v___x_1087_ == 0)
{
lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; uint8_t v___x_1091_; 
v___x_1088_ = lean_array_uget_borrowed(v_as_1078_, v_i_1079_);
lean_inc(v_inst_1074_);
v___x_1089_ = lean_array_get_borrowed(v_inst_1074_, v_xs_1075_, v___x_1088_);
lean_inc_ref(v_f_1076_);
lean_inc(v___x_1089_);
v___x_1090_ = lean_apply_1(v_f_1076_, v___x_1089_);
v___x_1091_ = lean_nat_dec_eq(v___x_1090_, v_x_1077_);
lean_dec(v___x_1090_);
if (v___x_1091_ == 0)
{
v___y_1083_ = v_b_1081_;
goto v___jp_1082_;
}
else
{
lean_object* v___x_1092_; 
lean_inc(v___x_1088_);
v___x_1092_ = lean_array_push(v_b_1081_, v___x_1088_);
v___y_1083_ = v___x_1092_;
goto v___jp_1082_;
}
}
else
{
lean_dec_ref(v_f_1076_);
lean_dec(v_inst_1074_);
return v_b_1081_;
}
v___jp_1082_:
{
size_t v___x_1084_; size_t v___x_1085_; 
v___x_1084_ = ((size_t)1ULL);
v___x_1085_ = lean_usize_add(v_i_1079_, v___x_1084_);
v_i_1079_ = v___x_1085_;
v_b_1081_ = v___y_1083_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__6___redArg___boxed(lean_object* v_inst_1093_, lean_object* v_xs_1094_, lean_object* v_f_1095_, lean_object* v_x_1096_, lean_object* v_as_1097_, lean_object* v_i_1098_, lean_object* v_stop_1099_, lean_object* v_b_1100_){
_start:
{
size_t v_i_boxed_1101_; size_t v_stop_boxed_1102_; lean_object* v_res_1103_; 
v_i_boxed_1101_ = lean_unbox_usize(v_i_1098_);
lean_dec(v_i_1098_);
v_stop_boxed_1102_ = lean_unbox_usize(v_stop_1099_);
lean_dec(v_stop_1099_);
v_res_1103_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__6___redArg(v_inst_1093_, v_xs_1094_, v_f_1095_, v_x_1096_, v_as_1097_, v_i_boxed_1101_, v_stop_boxed_1102_, v_b_1100_);
lean_dec_ref(v_as_1097_);
lean_dec(v_x_1096_);
lean_dec_ref(v_xs_1094_);
return v_res_1103_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8_spec__9___redArg(lean_object* v_xs_1106_, lean_object* v_inst_1107_, lean_object* v_f_1108_, size_t v_sz_1109_, size_t v_i_1110_, lean_object* v_bs_1111_){
_start:
{
uint8_t v___x_1112_; 
v___x_1112_ = lean_usize_dec_lt(v_i_1110_, v_sz_1109_);
if (v___x_1112_ == 0)
{
lean_dec_ref(v_f_1108_);
lean_dec(v_inst_1107_);
return v_bs_1111_;
}
else
{
lean_object* v_v_1113_; lean_object* v___x_1114_; lean_object* v_bs_x27_1115_; lean_object* v___y_1117_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; uint8_t v___x_1126_; 
v_v_1113_ = lean_array_uget(v_bs_1111_, v_i_1110_);
v___x_1114_ = lean_unsigned_to_nat(0u);
v_bs_x27_1115_ = lean_array_uset(v_bs_1111_, v_i_1110_, v___x_1114_);
v___x_1122_ = lean_array_get_size(v_xs_1106_);
v___x_1123_ = l_Array_range(v___x_1122_);
v___x_1124_ = lean_array_get_size(v___x_1123_);
v___x_1125_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8_spec__9___redArg___closed__0));
v___x_1126_ = lean_nat_dec_lt(v___x_1114_, v___x_1124_);
if (v___x_1126_ == 0)
{
lean_dec_ref(v___x_1123_);
lean_dec(v_v_1113_);
v___y_1117_ = v___x_1125_;
goto v___jp_1116_;
}
else
{
uint8_t v___x_1127_; 
v___x_1127_ = lean_nat_dec_le(v___x_1124_, v___x_1124_);
if (v___x_1127_ == 0)
{
if (v___x_1126_ == 0)
{
lean_dec_ref(v___x_1123_);
lean_dec(v_v_1113_);
v___y_1117_ = v___x_1125_;
goto v___jp_1116_;
}
else
{
size_t v___x_1128_; size_t v___x_1129_; lean_object* v___x_1130_; 
v___x_1128_ = ((size_t)0ULL);
v___x_1129_ = lean_usize_of_nat(v___x_1124_);
lean_inc_ref(v_f_1108_);
lean_inc(v_inst_1107_);
v___x_1130_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__6___redArg(v_inst_1107_, v_xs_1106_, v_f_1108_, v_v_1113_, v___x_1123_, v___x_1128_, v___x_1129_, v___x_1125_);
lean_dec_ref(v___x_1123_);
lean_dec(v_v_1113_);
v___y_1117_ = v___x_1130_;
goto v___jp_1116_;
}
}
else
{
size_t v___x_1131_; size_t v___x_1132_; lean_object* v___x_1133_; 
v___x_1131_ = ((size_t)0ULL);
v___x_1132_ = lean_usize_of_nat(v___x_1124_);
lean_inc_ref(v_f_1108_);
lean_inc(v_inst_1107_);
v___x_1133_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__6___redArg(v_inst_1107_, v_xs_1106_, v_f_1108_, v_v_1113_, v___x_1123_, v___x_1131_, v___x_1132_, v___x_1125_);
lean_dec_ref(v___x_1123_);
lean_dec(v_v_1113_);
v___y_1117_ = v___x_1133_;
goto v___jp_1116_;
}
}
v___jp_1116_:
{
size_t v___x_1118_; size_t v___x_1119_; lean_object* v___x_1120_; 
v___x_1118_ = ((size_t)1ULL);
v___x_1119_ = lean_usize_add(v_i_1110_, v___x_1118_);
v___x_1120_ = lean_array_uset(v_bs_x27_1115_, v_i_1110_, v___y_1117_);
v_i_1110_ = v___x_1119_;
v_bs_1111_ = v___x_1120_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8_spec__9___redArg___boxed(lean_object* v_xs_1134_, lean_object* v_inst_1135_, lean_object* v_f_1136_, lean_object* v_sz_1137_, lean_object* v_i_1138_, lean_object* v_bs_1139_){
_start:
{
size_t v_sz_boxed_1140_; size_t v_i_boxed_1141_; lean_object* v_res_1142_; 
v_sz_boxed_1140_ = lean_unbox_usize(v_sz_1137_);
lean_dec(v_sz_1137_);
v_i_boxed_1141_ = lean_unbox_usize(v_i_1138_);
lean_dec(v_i_1138_);
v_res_1142_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8_spec__9___redArg(v_xs_1134_, v_inst_1135_, v_f_1136_, v_sz_boxed_1140_, v_i_boxed_1141_, v_bs_1139_);
lean_dec_ref(v_xs_1134_);
return v_res_1142_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8___redArg(lean_object* v_inst_1143_, lean_object* v_xs_1144_, lean_object* v_f_1145_, size_t v_sz_1146_, size_t v_i_1147_, lean_object* v_bs_1148_){
_start:
{
uint8_t v___x_1149_; 
v___x_1149_ = lean_usize_dec_lt(v_i_1147_, v_sz_1146_);
if (v___x_1149_ == 0)
{
lean_dec_ref(v_f_1145_);
lean_dec(v_inst_1143_);
return v_bs_1148_;
}
else
{
lean_object* v_v_1150_; lean_object* v___x_1151_; lean_object* v_bs_x27_1152_; lean_object* v___y_1154_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; uint8_t v___x_1163_; 
v_v_1150_ = lean_array_uget(v_bs_1148_, v_i_1147_);
v___x_1151_ = lean_unsigned_to_nat(0u);
v_bs_x27_1152_ = lean_array_uset(v_bs_1148_, v_i_1147_, v___x_1151_);
v___x_1159_ = lean_array_get_size(v_xs_1144_);
v___x_1160_ = l_Array_range(v___x_1159_);
v___x_1161_ = lean_array_get_size(v___x_1160_);
v___x_1162_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8_spec__9___redArg___closed__0));
v___x_1163_ = lean_nat_dec_lt(v___x_1151_, v___x_1161_);
if (v___x_1163_ == 0)
{
lean_dec_ref(v___x_1160_);
lean_dec(v_v_1150_);
v___y_1154_ = v___x_1162_;
goto v___jp_1153_;
}
else
{
uint8_t v___x_1164_; 
v___x_1164_ = lean_nat_dec_le(v___x_1161_, v___x_1161_);
if (v___x_1164_ == 0)
{
if (v___x_1163_ == 0)
{
lean_dec_ref(v___x_1160_);
lean_dec(v_v_1150_);
v___y_1154_ = v___x_1162_;
goto v___jp_1153_;
}
else
{
size_t v___x_1165_; size_t v___x_1166_; lean_object* v___x_1167_; 
v___x_1165_ = ((size_t)0ULL);
v___x_1166_ = lean_usize_of_nat(v___x_1161_);
lean_inc_ref(v_f_1145_);
lean_inc(v_inst_1143_);
v___x_1167_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__6___redArg(v_inst_1143_, v_xs_1144_, v_f_1145_, v_v_1150_, v___x_1160_, v___x_1165_, v___x_1166_, v___x_1162_);
lean_dec_ref(v___x_1160_);
lean_dec(v_v_1150_);
v___y_1154_ = v___x_1167_;
goto v___jp_1153_;
}
}
else
{
size_t v___x_1168_; size_t v___x_1169_; lean_object* v___x_1170_; 
v___x_1168_ = ((size_t)0ULL);
v___x_1169_ = lean_usize_of_nat(v___x_1161_);
lean_inc_ref(v_f_1145_);
lean_inc(v_inst_1143_);
v___x_1170_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__6___redArg(v_inst_1143_, v_xs_1144_, v_f_1145_, v_v_1150_, v___x_1160_, v___x_1168_, v___x_1169_, v___x_1162_);
lean_dec_ref(v___x_1160_);
lean_dec(v_v_1150_);
v___y_1154_ = v___x_1170_;
goto v___jp_1153_;
}
}
v___jp_1153_:
{
size_t v___x_1155_; size_t v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1155_ = ((size_t)1ULL);
v___x_1156_ = lean_usize_add(v_i_1147_, v___x_1155_);
v___x_1157_ = lean_array_uset(v_bs_x27_1152_, v_i_1147_, v___y_1154_);
v___x_1158_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8_spec__9___redArg(v_xs_1144_, v_inst_1143_, v_f_1145_, v_sz_1146_, v___x_1156_, v___x_1157_);
return v___x_1158_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8___redArg___boxed(lean_object* v_inst_1171_, lean_object* v_xs_1172_, lean_object* v_f_1173_, lean_object* v_sz_1174_, lean_object* v_i_1175_, lean_object* v_bs_1176_){
_start:
{
size_t v_sz_boxed_1177_; size_t v_i_boxed_1178_; lean_object* v_res_1179_; 
v_sz_boxed_1177_ = lean_unbox_usize(v_sz_1174_);
lean_dec(v_sz_1174_);
v_i_boxed_1178_ = lean_unbox_usize(v_i_1175_);
lean_dec(v_i_1175_);
v_res_1179_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8___redArg(v_inst_1171_, v_xs_1172_, v_f_1173_, v_sz_boxed_1177_, v_i_boxed_1178_, v_bs_1176_);
lean_dec_ref(v_xs_1172_);
return v_res_1179_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__7___closed__0(void){
_start:
{
lean_object* v___x_1180_; 
v___x_1180_ = l_Array_instInhabited(lean_box(0));
return v___x_1180_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__7(lean_object* v_msg_1181_){
_start:
{
lean_object* v___x_1182_; lean_object* v___x_1183_; 
v___x_1182_ = lean_obj_once(&l_panic___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__7___closed__0, &l_panic___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__7___closed__0_once, _init_l_panic___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__7___closed__0);
v___x_1183_ = lean_panic_fn(v___x_1182_, v_msg_1181_);
return v___x_1183_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9___redArg(lean_object* v_xs_1184_, lean_object* v_ys_1185_, lean_object* v_x_1186_){
_start:
{
lean_object* v_zero_1187_; uint8_t v_isZero_1188_; 
v_zero_1187_ = lean_unsigned_to_nat(0u);
v_isZero_1188_ = lean_nat_dec_eq(v_x_1186_, v_zero_1187_);
if (v_isZero_1188_ == 1)
{
lean_dec(v_x_1186_);
return v_isZero_1188_;
}
else
{
lean_object* v_one_1189_; lean_object* v_n_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; uint8_t v___x_1193_; 
v_one_1189_ = lean_unsigned_to_nat(1u);
v_n_1190_ = lean_nat_sub(v_x_1186_, v_one_1189_);
lean_dec(v_x_1186_);
v___x_1191_ = lean_array_fget_borrowed(v_xs_1184_, v_n_1190_);
v___x_1192_ = lean_array_fget_borrowed(v_ys_1185_, v_n_1190_);
v___x_1193_ = lean_nat_dec_eq(v___x_1191_, v___x_1192_);
if (v___x_1193_ == 0)
{
lean_dec(v_n_1190_);
return v___x_1193_;
}
else
{
v_x_1186_ = v_n_1190_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9___redArg___boxed(lean_object* v_xs_1195_, lean_object* v_ys_1196_, lean_object* v_x_1197_){
_start:
{
uint8_t v_res_1198_; lean_object* v_r_1199_; 
v_res_1198_ = l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9___redArg(v_xs_1195_, v_ys_1196_, v_x_1197_);
lean_dec_ref(v_ys_1196_);
lean_dec_ref(v_xs_1195_);
v_r_1199_ = lean_box(v_res_1198_);
return v_r_1199_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; 
v___x_1202_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___redArg___closed__1));
v___x_1203_ = lean_unsigned_to_nat(2u);
v___x_1204_ = lean_unsigned_to_nat(79u);
v___x_1205_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___redArg___closed__0));
v___x_1206_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg___closed__0));
v___x_1207_ = l_mkPanicMessageWithDecl(v___x_1206_, v___x_1205_, v___x_1204_, v___x_1203_, v___x_1202_);
return v___x_1207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___redArg(lean_object* v_inst_1210_, lean_object* v_f_1211_, lean_object* v_xs_1212_, lean_object* v_ys_1213_){
_start:
{
size_t v_sz_1217_; size_t v___x_1218_; lean_object* v_positions_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___y_1223_; lean_object* v___y_1229_; lean_object* v___y_1230_; lean_object* v___y_1231_; lean_object* v___y_1232_; lean_object* v___y_1235_; lean_object* v___y_1236_; lean_object* v___y_1237_; lean_object* v___y_1238_; lean_object* v___y_1241_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; uint8_t v___x_1251_; 
v_sz_1217_ = lean_array_size(v_ys_1213_);
v___x_1218_ = ((size_t)0ULL);
v_positions_1219_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8___redArg(v_inst_1210_, v_xs_1212_, v_f_1211_, v_sz_1217_, v___x_1218_, v_ys_1213_);
v___x_1220_ = lean_array_get_size(v_xs_1212_);
v___x_1221_ = l_Array_range(v___x_1220_);
v___x_1248_ = lean_unsigned_to_nat(0u);
v___x_1249_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___redArg___closed__3));
v___x_1250_ = lean_array_get_size(v_positions_1219_);
v___x_1251_ = lean_nat_dec_lt(v___x_1248_, v___x_1250_);
if (v___x_1251_ == 0)
{
v___y_1241_ = v___x_1249_;
goto v___jp_1240_;
}
else
{
uint8_t v___x_1252_; 
v___x_1252_ = lean_nat_dec_le(v___x_1250_, v___x_1250_);
if (v___x_1252_ == 0)
{
if (v___x_1251_ == 0)
{
v___y_1241_ = v___x_1249_;
goto v___jp_1240_;
}
else
{
size_t v___x_1253_; lean_object* v___x_1254_; 
v___x_1253_ = lean_usize_of_nat(v___x_1250_);
v___x_1254_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__11(v_positions_1219_, v___x_1218_, v___x_1253_, v___x_1249_);
v___y_1241_ = v___x_1254_;
goto v___jp_1240_;
}
}
else
{
size_t v___x_1255_; lean_object* v___x_1256_; 
v___x_1255_ = lean_usize_of_nat(v___x_1250_);
v___x_1256_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__11(v_positions_1219_, v___x_1218_, v___x_1255_, v___x_1249_);
v___y_1241_ = v___x_1256_;
goto v___jp_1240_;
}
}
v___jp_1214_:
{
lean_object* v___x_1215_; lean_object* v___x_1216_; 
v___x_1215_ = lean_obj_once(&l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___redArg___closed__2, &l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___redArg___closed__2_once, _init_l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___redArg___closed__2);
v___x_1216_ = l_panic___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__7(v___x_1215_);
return v___x_1216_;
}
v___jp_1222_:
{
lean_object* v___x_1224_; lean_object* v___x_1225_; uint8_t v___x_1226_; 
v___x_1224_ = lean_array_get_size(v___x_1221_);
v___x_1225_ = lean_array_get_size(v___y_1223_);
v___x_1226_ = lean_nat_dec_eq(v___x_1224_, v___x_1225_);
if (v___x_1226_ == 0)
{
lean_dec_ref(v___y_1223_);
lean_dec_ref(v___x_1221_);
lean_dec_ref(v_positions_1219_);
goto v___jp_1214_;
}
else
{
uint8_t v___x_1227_; 
v___x_1227_ = l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9___redArg(v___x_1221_, v___y_1223_, v___x_1224_);
lean_dec_ref(v___y_1223_);
lean_dec_ref(v___x_1221_);
if (v___x_1227_ == 0)
{
lean_dec_ref(v_positions_1219_);
goto v___jp_1214_;
}
else
{
return v_positions_1219_;
}
}
}
v___jp_1228_:
{
lean_object* v___x_1233_; 
lean_dec(v___y_1229_);
v___x_1233_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg(v___y_1230_, v___y_1231_, v___y_1232_);
lean_dec(v___y_1232_);
v___y_1223_ = v___x_1233_;
goto v___jp_1222_;
}
v___jp_1234_:
{
uint8_t v___x_1239_; 
v___x_1239_ = lean_nat_dec_le(v___y_1238_, v___y_1236_);
if (v___x_1239_ == 0)
{
lean_dec(v___y_1236_);
lean_inc(v___y_1238_);
v___y_1229_ = v___y_1235_;
v___y_1230_ = v___y_1237_;
v___y_1231_ = v___y_1238_;
v___y_1232_ = v___y_1238_;
goto v___jp_1228_;
}
else
{
v___y_1229_ = v___y_1235_;
v___y_1230_ = v___y_1237_;
v___y_1231_ = v___y_1238_;
v___y_1232_ = v___y_1236_;
goto v___jp_1228_;
}
}
v___jp_1240_:
{
lean_object* v___x_1242_; lean_object* v___x_1243_; uint8_t v___x_1244_; 
v___x_1242_ = lean_array_get_size(v___y_1241_);
v___x_1243_ = lean_unsigned_to_nat(0u);
v___x_1244_ = lean_nat_dec_eq(v___x_1242_, v___x_1243_);
if (v___x_1244_ == 0)
{
lean_object* v___x_1245_; lean_object* v___x_1246_; uint8_t v___x_1247_; 
v___x_1245_ = lean_unsigned_to_nat(1u);
v___x_1246_ = lean_nat_sub(v___x_1242_, v___x_1245_);
v___x_1247_ = lean_nat_dec_le(v___x_1243_, v___x_1246_);
if (v___x_1247_ == 0)
{
lean_inc(v___x_1246_);
v___y_1235_ = v___x_1242_;
v___y_1236_ = v___x_1246_;
v___y_1237_ = v___y_1241_;
v___y_1238_ = v___x_1246_;
goto v___jp_1234_;
}
else
{
v___y_1235_ = v___x_1242_;
v___y_1236_ = v___x_1246_;
v___y_1237_ = v___y_1241_;
v___y_1238_ = v___x_1243_;
goto v___jp_1234_;
}
}
else
{
v___y_1223_ = v___y_1241_;
goto v___jp_1222_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___redArg___boxed(lean_object* v_inst_1257_, lean_object* v_f_1258_, lean_object* v_xs_1259_, lean_object* v_ys_1260_){
_start:
{
lean_object* v_res_1261_; 
v_res_1261_ = l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___redArg(v_inst_1257_, v_f_1258_, v_xs_1259_, v_ys_1260_);
lean_dec_ref(v_xs_1259_);
return v_res_1261_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__0(lean_object* v_a_1262_, lean_object* v_a_1263_){
_start:
{
if (lean_obj_tag(v_a_1262_) == 0)
{
lean_object* v___x_1264_; 
v___x_1264_ = l_List_reverse___redArg(v_a_1263_);
return v___x_1264_;
}
else
{
lean_object* v_head_1265_; lean_object* v_tail_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1277_; 
v_head_1265_ = lean_ctor_get(v_a_1262_, 0);
v_tail_1266_ = lean_ctor_get(v_a_1262_, 1);
v_isSharedCheck_1277_ = !lean_is_exclusive(v_a_1262_);
if (v_isSharedCheck_1277_ == 0)
{
v___x_1268_ = v_a_1262_;
v_isShared_1269_ = v_isSharedCheck_1277_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_tail_1266_);
lean_inc(v_head_1265_);
lean_dec(v_a_1262_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1277_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1274_; 
v___x_1270_ = l_Nat_reprFast(v_head_1265_);
v___x_1271_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1271_, 0, v___x_1270_);
v___x_1272_ = l_Lean_MessageData_ofFormat(v___x_1271_);
if (v_isShared_1269_ == 0)
{
lean_ctor_set(v___x_1268_, 1, v_a_1263_);
lean_ctor_set(v___x_1268_, 0, v___x_1272_);
v___x_1274_ = v___x_1268_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v___x_1272_);
lean_ctor_set(v_reuseFailAlloc_1276_, 1, v_a_1263_);
v___x_1274_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
v_a_1262_ = v_tail_1266_;
v_a_1263_ = v___x_1274_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__15(lean_object* v_a_1278_, lean_object* v_a_1279_){
_start:
{
if (lean_obj_tag(v_a_1278_) == 0)
{
lean_object* v___x_1280_; 
v___x_1280_ = l_List_reverse___redArg(v_a_1279_);
return v___x_1280_;
}
else
{
lean_object* v_head_1281_; lean_object* v_tail_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1294_; 
v_head_1281_ = lean_ctor_get(v_a_1278_, 0);
v_tail_1282_ = lean_ctor_get(v_a_1278_, 1);
v_isSharedCheck_1294_ = !lean_is_exclusive(v_a_1278_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1284_ = v_a_1278_;
v_isShared_1285_ = v_isSharedCheck_1294_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_tail_1282_);
lean_inc(v_head_1281_);
lean_dec(v_a_1278_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1294_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1291_; 
v___x_1286_ = lean_array_to_list(v_head_1281_);
v___x_1287_ = lean_box(0);
v___x_1288_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__0(v___x_1286_, v___x_1287_);
v___x_1289_ = l_Lean_MessageData_ofList(v___x_1288_);
if (v_isShared_1285_ == 0)
{
lean_ctor_set(v___x_1284_, 1, v_a_1279_);
lean_ctor_set(v___x_1284_, 0, v___x_1289_);
v___x_1291_ = v___x_1284_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v___x_1289_);
lean_ctor_set(v_reuseFailAlloc_1293_, 1, v_a_1279_);
v___x_1291_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
v_a_1278_ = v_tail_1282_;
v_a_1279_ = v___x_1291_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___redArg(lean_object* v_fixedParamPerms_1295_, lean_object* v_xs_1296_, lean_object* v_as_1297_, lean_object* v_i_1298_, lean_object* v_j_1299_, lean_object* v_bs_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_){
_start:
{
lean_object* v_zero_1306_; uint8_t v_isZero_1307_; 
v_zero_1306_ = lean_unsigned_to_nat(0u);
v_isZero_1307_ = lean_nat_dec_eq(v_i_1298_, v_zero_1306_);
if (v_isZero_1307_ == 1)
{
lean_object* v___x_1308_; 
lean_dec(v___y_1304_);
lean_dec_ref(v___y_1303_);
lean_dec(v___y_1302_);
lean_dec_ref(v___y_1301_);
lean_dec(v_j_1299_);
lean_dec(v_i_1298_);
lean_dec_ref(v_xs_1296_);
v___x_1308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1308_, 0, v_bs_1300_);
return v___x_1308_;
}
else
{
lean_object* v_perms_1309_; lean_object* v___x_1310_; lean_object* v_value_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; 
v_perms_1309_ = lean_ctor_get(v_fixedParamPerms_1295_, 1);
v___x_1310_ = lean_array_fget_borrowed(v_as_1297_, v_j_1299_);
v_value_1311_ = lean_ctor_get(v___x_1310_, 7);
v___x_1312_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9___redArg___closed__0, &l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9___redArg___closed__0_once, _init_l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9___redArg___closed__0);
v___x_1313_ = lean_array_get_borrowed(v___x_1312_, v_perms_1309_, v_j_1299_);
lean_inc(v___y_1304_);
lean_inc_ref(v___y_1303_);
lean_inc(v___y_1302_);
lean_inc_ref(v___y_1301_);
lean_inc_ref(v_xs_1296_);
lean_inc_ref(v_value_1311_);
lean_inc(v___x_1313_);
v___x_1314_ = l_Lean_Elab_FixedParamPerm_instantiateLambda(v___x_1313_, v_value_1311_, v_xs_1296_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_);
if (lean_obj_tag(v___x_1314_) == 0)
{
lean_object* v_a_1315_; lean_object* v_one_1316_; lean_object* v_n_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; 
v_a_1315_ = lean_ctor_get(v___x_1314_, 0);
lean_inc(v_a_1315_);
lean_dec_ref(v___x_1314_);
v_one_1316_ = lean_unsigned_to_nat(1u);
v_n_1317_ = lean_nat_sub(v_i_1298_, v_one_1316_);
lean_dec(v_i_1298_);
v___x_1318_ = lean_nat_add(v_j_1299_, v_one_1316_);
lean_dec(v_j_1299_);
v___x_1319_ = lean_array_push(v_bs_1300_, v_a_1315_);
v_i_1298_ = v_n_1317_;
v_j_1299_ = v___x_1318_;
v_bs_1300_ = v___x_1319_;
goto _start;
}
else
{
lean_object* v_a_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1328_; 
lean_dec(v___y_1304_);
lean_dec_ref(v___y_1303_);
lean_dec(v___y_1302_);
lean_dec_ref(v___y_1301_);
lean_dec_ref(v_bs_1300_);
lean_dec(v_j_1299_);
lean_dec(v_i_1298_);
lean_dec_ref(v_xs_1296_);
v_a_1321_ = lean_ctor_get(v___x_1314_, 0);
v_isSharedCheck_1328_ = !lean_is_exclusive(v___x_1314_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1323_ = v___x_1314_;
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_a_1321_);
lean_dec(v___x_1314_);
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
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___redArg___boxed(lean_object* v_fixedParamPerms_1329_, lean_object* v_xs_1330_, lean_object* v_as_1331_, lean_object* v_i_1332_, lean_object* v_j_1333_, lean_object* v_bs_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_){
_start:
{
lean_object* v_res_1340_; 
v_res_1340_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___redArg(v_fixedParamPerms_1329_, v_xs_1330_, v_as_1331_, v_i_1332_, v_j_1333_, v_bs_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_);
lean_dec_ref(v_as_1331_);
lean_dec_ref(v_fixedParamPerms_1329_);
return v_res_1340_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14(lean_object* v_as_1341_, lean_object* v_bs_1342_, lean_object* v_i_1343_, lean_object* v_cs_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_){
_start:
{
lean_object* v___x_1351_; uint8_t v___x_1352_; 
v___x_1351_ = lean_array_get_size(v_as_1341_);
v___x_1352_ = lean_nat_dec_lt(v_i_1343_, v___x_1351_);
if (v___x_1352_ == 0)
{
lean_object* v___x_1353_; 
lean_dec(v___y_1349_);
lean_dec_ref(v___y_1348_);
lean_dec(v___y_1347_);
lean_dec_ref(v___y_1346_);
lean_dec(v___y_1345_);
lean_dec(v_i_1343_);
v___x_1353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1353_, 0, v_cs_1344_);
return v___x_1353_;
}
else
{
lean_object* v___x_1354_; uint8_t v___x_1355_; 
v___x_1354_ = lean_array_get_size(v_bs_1342_);
v___x_1355_ = lean_nat_dec_lt(v_i_1343_, v___x_1354_);
if (v___x_1355_ == 0)
{
lean_object* v___x_1356_; 
lean_dec(v___y_1349_);
lean_dec_ref(v___y_1348_);
lean_dec(v___y_1347_);
lean_dec_ref(v___y_1346_);
lean_dec(v___y_1345_);
lean_dec(v_i_1343_);
v___x_1356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1356_, 0, v_cs_1344_);
return v___x_1356_;
}
else
{
lean_object* v_a_1357_; lean_object* v_b_1358_; lean_object* v___x_1359_; 
v_a_1357_ = lean_array_fget_borrowed(v_as_1341_, v_i_1343_);
v_b_1358_ = lean_array_fget_borrowed(v_bs_1342_, v_i_1343_);
lean_inc(v___y_1349_);
lean_inc_ref(v___y_1348_);
lean_inc(v___y_1347_);
lean_inc_ref(v___y_1346_);
lean_inc(v___y_1345_);
lean_inc(v_b_1358_);
lean_inc(v_a_1357_);
v___x_1359_ = l_Lean_Elab_Structural_mkBRecOnMotive(v_a_1357_, v_b_1358_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_);
if (lean_obj_tag(v___x_1359_) == 0)
{
lean_object* v_a_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; 
v_a_1360_ = lean_ctor_get(v___x_1359_, 0);
lean_inc(v_a_1360_);
lean_dec_ref(v___x_1359_);
v___x_1361_ = lean_unsigned_to_nat(1u);
v___x_1362_ = lean_nat_add(v_i_1343_, v___x_1361_);
lean_dec(v_i_1343_);
v___x_1363_ = lean_array_push(v_cs_1344_, v_a_1360_);
v_i_1343_ = v___x_1362_;
v_cs_1344_ = v___x_1363_;
goto _start;
}
else
{
lean_object* v_a_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1372_; 
lean_dec(v___y_1349_);
lean_dec_ref(v___y_1348_);
lean_dec(v___y_1347_);
lean_dec_ref(v___y_1346_);
lean_dec(v___y_1345_);
lean_dec_ref(v_cs_1344_);
lean_dec(v_i_1343_);
v_a_1365_ = lean_ctor_get(v___x_1359_, 0);
v_isSharedCheck_1372_ = !lean_is_exclusive(v___x_1359_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1367_ = v___x_1359_;
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_a_1365_);
lean_dec(v___x_1359_);
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
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___boxed(lean_object* v_as_1373_, lean_object* v_bs_1374_, lean_object* v_i_1375_, lean_object* v_cs_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_){
_start:
{
lean_object* v_res_1383_; 
v_res_1383_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14(v_as_1373_, v_bs_1374_, v_i_1375_, v_cs_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_);
lean_dec_ref(v_bs_1374_);
lean_dec_ref(v_as_1373_);
return v_res_1383_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3_spec__3___redArg(lean_object* v_msg_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_){
_start:
{
lean_object* v_ref_1390_; lean_object* v___x_1391_; lean_object* v_a_1392_; lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1400_; 
v_ref_1390_ = lean_ctor_get(v___y_1387_, 5);
v___x_1391_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__22(v_msg_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_);
v_a_1392_ = lean_ctor_get(v___x_1391_, 0);
v_isSharedCheck_1400_ = !lean_is_exclusive(v___x_1391_);
if (v_isSharedCheck_1400_ == 0)
{
v___x_1394_ = v___x_1391_;
v_isShared_1395_ = v_isSharedCheck_1400_;
goto v_resetjp_1393_;
}
else
{
lean_inc(v_a_1392_);
lean_dec(v___x_1391_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1400_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
lean_object* v___x_1396_; lean_object* v___x_1398_; 
lean_inc(v_ref_1390_);
v___x_1396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1396_, 0, v_ref_1390_);
lean_ctor_set(v___x_1396_, 1, v_a_1392_);
if (v_isShared_1395_ == 0)
{
lean_ctor_set_tag(v___x_1394_, 1);
lean_ctor_set(v___x_1394_, 0, v___x_1396_);
v___x_1398_ = v___x_1394_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v___x_1396_);
v___x_1398_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
return v___x_1398_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3_spec__3___redArg___boxed(lean_object* v_msg_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_){
_start:
{
lean_object* v_res_1407_; 
v_res_1407_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3_spec__3___redArg(v_msg_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_);
lean_dec(v___y_1405_);
lean_dec_ref(v___y_1404_);
lean_dec(v___y_1403_);
lean_dec_ref(v___y_1402_);
return v_res_1407_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___closed__1(void){
_start:
{
lean_object* v___x_1409_; lean_object* v___x_1410_; 
v___x_1409_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___closed__0));
v___x_1410_ = l_Lean_stringToMessageData(v___x_1409_);
return v___x_1410_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___closed__3(void){
_start:
{
lean_object* v___x_1412_; lean_object* v___x_1413_; 
v___x_1412_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___closed__2));
v___x_1413_ = l_Lean_stringToMessageData(v___x_1412_);
return v___x_1413_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3(lean_object* v_constName_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_){
_start:
{
lean_object* v___x_1421_; lean_object* v_env_1422_; lean_object* v___x_1423_; 
v___x_1421_ = lean_st_ref_get(v___y_1419_);
v_env_1422_ = lean_ctor_get(v___x_1421_, 0);
lean_inc_ref(v_env_1422_);
lean_dec(v___x_1421_);
lean_inc(v_constName_1414_);
v___x_1423_ = l_Lean_isInductiveCore_x3f(v_env_1422_, v_constName_1414_);
if (lean_obj_tag(v___x_1423_) == 0)
{
lean_object* v___x_1424_; uint8_t v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; 
v___x_1424_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___closed__1, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___closed__1);
v___x_1425_ = 0;
v___x_1426_ = l_Lean_MessageData_ofConstName(v_constName_1414_, v___x_1425_);
v___x_1427_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1427_, 0, v___x_1424_);
lean_ctor_set(v___x_1427_, 1, v___x_1426_);
v___x_1428_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___closed__3, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___closed__3_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___closed__3);
v___x_1429_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1429_, 0, v___x_1427_);
lean_ctor_set(v___x_1429_, 1, v___x_1428_);
v___x_1430_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3_spec__3___redArg(v___x_1429_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_);
return v___x_1430_;
}
else
{
lean_object* v_val_1431_; lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1438_; 
lean_dec(v_constName_1414_);
v_val_1431_ = lean_ctor_get(v___x_1423_, 0);
v_isSharedCheck_1438_ = !lean_is_exclusive(v___x_1423_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1433_ = v___x_1423_;
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
else
{
lean_inc(v_val_1431_);
lean_dec(v___x_1423_);
v___x_1433_ = lean_box(0);
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
lean_object* v___x_1436_; 
if (v_isShared_1434_ == 0)
{
lean_ctor_set_tag(v___x_1433_, 0);
v___x_1436_ = v___x_1433_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v_val_1431_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
return v___x_1436_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___boxed(lean_object* v_constName_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_){
_start:
{
lean_object* v_res_1446_; 
v_res_1446_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3(v_constName_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_);
lean_dec(v___y_1444_);
lean_dec_ref(v___y_1443_);
lean_dec(v___y_1442_);
lean_dec_ref(v___y_1441_);
lean_dec(v___y_1440_);
return v_res_1446_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__8(void){
_start:
{
lean_object* v___x_1459_; lean_object* v___x_1460_; 
v___x_1459_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__7));
v___x_1460_ = l_Lean_stringToMessageData(v___x_1459_);
return v___x_1460_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__10(void){
_start:
{
lean_object* v___x_1462_; lean_object* v___x_1463_; 
v___x_1462_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__9));
v___x_1463_ = l_Lean_stringToMessageData(v___x_1462_);
return v___x_1463_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion(lean_object* v_preDefs_1464_, lean_object* v_fixedParamPerms_1465_, lean_object* v_xs_1466_, lean_object* v_recArgInfos_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_){
_start:
{
lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; 
v___x_1474_ = lean_array_get_size(v_preDefs_1464_);
v___x_1475_ = lean_unsigned_to_nat(0u);
v___x_1476_ = lean_mk_empty_array_with_capacity(v___x_1474_);
lean_inc(v_a_1472_);
lean_inc_ref(v_a_1471_);
lean_inc(v_a_1470_);
lean_inc_ref(v_a_1469_);
lean_inc_ref(v_xs_1466_);
v___x_1477_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___redArg(v_fixedParamPerms_1465_, v_xs_1466_, v_preDefs_1464_, v___x_1474_, v___x_1475_, v___x_1476_, v_a_1469_, v_a_1470_, v_a_1471_, v_a_1472_);
if (lean_obj_tag(v___x_1477_) == 0)
{
lean_object* v_a_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v_indGroupInst_1481_; lean_object* v_toIndGroupInfo_1482_; lean_object* v_all_1483_; lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1568_; 
v_a_1478_ = lean_ctor_get(v___x_1477_, 0);
lean_inc(v_a_1478_);
lean_dec_ref(v___x_1477_);
v___x_1479_ = l_Lean_Elab_Structural_instInhabitedRecArgInfo_default;
v___x_1480_ = lean_array_get_borrowed(v___x_1479_, v_recArgInfos_1467_, v___x_1475_);
v_indGroupInst_1481_ = lean_ctor_get(v___x_1480_, 4);
v_toIndGroupInfo_1482_ = lean_ctor_get(v_indGroupInst_1481_, 0);
lean_inc_ref(v_toIndGroupInfo_1482_);
v_all_1483_ = lean_ctor_get(v_toIndGroupInfo_1482_, 0);
v_isSharedCheck_1568_ = !lean_is_exclusive(v_toIndGroupInfo_1482_);
if (v_isSharedCheck_1568_ == 0)
{
lean_object* v_unused_1569_; 
v_unused_1569_ = lean_ctor_get(v_toIndGroupInfo_1482_, 1);
lean_dec(v_unused_1569_);
v___x_1485_ = v_toIndGroupInfo_1482_;
v_isShared_1486_ = v_isSharedCheck_1568_;
goto v_resetjp_1484_;
}
else
{
lean_inc(v_all_1483_);
lean_dec(v_toIndGroupInfo_1482_);
v___x_1485_ = lean_box(0);
v_isShared_1486_ = v_isSharedCheck_1568_;
goto v_resetjp_1484_;
}
v_resetjp_1484_:
{
lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; 
v___x_1487_ = lean_box(0);
v___x_1488_ = lean_array_get(v___x_1487_, v_all_1483_, v___x_1475_);
lean_dec_ref(v_all_1483_);
v___x_1489_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3(v___x_1488_, v_a_1468_, v_a_1469_, v_a_1470_, v_a_1471_, v_a_1472_);
if (lean_obj_tag(v___x_1489_) == 0)
{
lean_object* v_a_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v_a_1493_; lean_object* v___f_1494_; lean_object* v___f_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___y_1501_; lean_object* v___y_1502_; lean_object* v___y_1503_; lean_object* v___y_1504_; lean_object* v___y_1505_; uint8_t v___x_1536_; 
v_a_1490_ = lean_ctor_get(v___x_1489_, 0);
lean_inc(v_a_1490_);
lean_dec_ref(v___x_1489_);
v___x_1491_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__3));
v___x_1492_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___redArg(v___x_1491_, v_a_1471_);
v_a_1493_ = lean_ctor_get(v___x_1492_, 0);
lean_inc(v_a_1493_);
lean_dec_ref(v___x_1492_);
v___f_1494_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__4));
v___f_1495_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__5));
v___x_1496_ = l_Lean_instInhabitedExpr;
v___x_1497_ = l_Lean_InductiveVal_numTypeFormers(v_a_1490_);
v___x_1498_ = l_Array_range(v___x_1497_);
v___x_1499_ = l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___redArg(v___x_1479_, v___f_1494_, v_recArgInfos_1467_, v___x_1498_);
v___x_1536_ = lean_unbox(v_a_1493_);
lean_dec(v_a_1493_);
if (v___x_1536_ == 0)
{
lean_del_object(v___x_1485_);
v___y_1501_ = v_a_1468_;
v___y_1502_ = v_a_1469_;
v___y_1503_ = v_a_1470_;
v___y_1504_ = v_a_1471_;
v___y_1505_ = v_a_1472_;
goto v___jp_1500_;
}
else
{
lean_object* v_toConstantVal_1537_; lean_object* v_name_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1542_; 
v_toConstantVal_1537_ = lean_ctor_get(v_a_1490_, 0);
v_name_1538_ = lean_ctor_get(v_toConstantVal_1537_, 0);
v___x_1539_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__8);
lean_inc(v_name_1538_);
v___x_1540_ = l_Lean_MessageData_ofName(v_name_1538_);
if (v_isShared_1486_ == 0)
{
lean_ctor_set_tag(v___x_1485_, 7);
lean_ctor_set(v___x_1485_, 1, v___x_1540_);
lean_ctor_set(v___x_1485_, 0, v___x_1539_);
v___x_1542_ = v___x_1485_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v___x_1539_);
lean_ctor_set(v_reuseFailAlloc_1559_, 1, v___x_1540_);
v___x_1542_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; 
v___x_1543_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__10, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__10);
v___x_1544_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1544_, 0, v___x_1542_);
lean_ctor_set(v___x_1544_, 1, v___x_1543_);
lean_inc_ref(v___x_1499_);
v___x_1545_ = lean_array_to_list(v___x_1499_);
v___x_1546_ = lean_box(0);
v___x_1547_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__15(v___x_1545_, v___x_1546_);
v___x_1548_ = l_Lean_MessageData_ofList(v___x_1547_);
v___x_1549_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1549_, 0, v___x_1544_);
lean_ctor_set(v___x_1549_, 1, v___x_1548_);
v___x_1550_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v___x_1491_, v___x_1549_, v_a_1469_, v_a_1470_, v_a_1471_, v_a_1472_);
if (lean_obj_tag(v___x_1550_) == 0)
{
lean_dec_ref(v___x_1550_);
v___y_1501_ = v_a_1468_;
v___y_1502_ = v_a_1469_;
v___y_1503_ = v_a_1470_;
v___y_1504_ = v_a_1471_;
v___y_1505_ = v_a_1472_;
goto v___jp_1500_;
}
else
{
lean_object* v_a_1551_; lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1558_; 
lean_dec_ref(v___x_1499_);
lean_dec(v_a_1490_);
lean_dec(v_a_1478_);
lean_dec(v_a_1472_);
lean_dec_ref(v_a_1471_);
lean_dec(v_a_1470_);
lean_dec_ref(v_a_1469_);
lean_dec(v_a_1468_);
lean_dec_ref(v_recArgInfos_1467_);
lean_dec_ref(v_xs_1466_);
lean_dec_ref(v_fixedParamPerms_1465_);
lean_dec_ref(v_preDefs_1464_);
v_a_1551_ = lean_ctor_get(v___x_1550_, 0);
v_isSharedCheck_1558_ = !lean_is_exclusive(v___x_1550_);
if (v_isSharedCheck_1558_ == 0)
{
v___x_1553_ = v___x_1550_;
v_isShared_1554_ = v_isSharedCheck_1558_;
goto v_resetjp_1552_;
}
else
{
lean_inc(v_a_1551_);
lean_dec(v___x_1550_);
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
v___jp_1500_:
{
lean_object* v_toConstantVal_1506_; lean_object* v_numIndices_1507_; lean_object* v_name_1508_; lean_object* v___x_1509_; 
v_toConstantVal_1506_ = lean_ctor_get(v_a_1490_, 0);
lean_inc_ref(v_toConstantVal_1506_);
v_numIndices_1507_ = lean_ctor_get(v_a_1490_, 2);
lean_inc(v_numIndices_1507_);
lean_dec(v_a_1490_);
v_name_1508_ = lean_ctor_get(v_toConstantVal_1506_, 0);
lean_inc(v_name_1508_);
lean_dec_ref(v_toConstantVal_1506_);
lean_inc(v___y_1505_);
lean_inc_ref(v___y_1504_);
lean_inc(v___y_1503_);
lean_inc_ref(v___y_1502_);
v___x_1509_ = l_Lean_Meta_isInductivePredicate(v_name_1508_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_);
if (lean_obj_tag(v___x_1509_) == 0)
{
lean_object* v_a_1510_; lean_object* v___f_1511_; uint8_t v___x_1512_; 
v_a_1510_ = lean_ctor_get(v___x_1509_, 0);
lean_inc(v_a_1510_);
lean_dec_ref(v___x_1509_);
lean_inc(v_a_1510_);
lean_inc(v_numIndices_1507_);
lean_inc_ref(v_preDefs_1464_);
lean_inc_ref(v_xs_1466_);
lean_inc_ref(v_fixedParamPerms_1465_);
lean_inc_ref(v___x_1499_);
lean_inc(v_a_1478_);
lean_inc_ref(v_recArgInfos_1467_);
v___f_1511_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___boxed), 20, 12);
lean_closure_set(v___f_1511_, 0, v___x_1491_);
lean_closure_set(v___f_1511_, 1, v_recArgInfos_1467_);
lean_closure_set(v___f_1511_, 2, v_a_1478_);
lean_closure_set(v___f_1511_, 3, v___x_1499_);
lean_closure_set(v___f_1511_, 4, v___x_1475_);
lean_closure_set(v___f_1511_, 5, v_fixedParamPerms_1465_);
lean_closure_set(v___f_1511_, 6, v_xs_1466_);
lean_closure_set(v___f_1511_, 7, v_preDefs_1464_);
lean_closure_set(v___f_1511_, 8, v_numIndices_1507_);
lean_closure_set(v___f_1511_, 9, v___x_1496_);
lean_closure_set(v___f_1511_, 10, v___f_1495_);
lean_closure_set(v___f_1511_, 11, v_a_1510_);
v___x_1512_ = lean_unbox(v_a_1510_);
if (v___x_1512_ == 0)
{
lean_object* v___x_1513_; lean_object* v___x_1514_; 
lean_dec_ref(v___f_1511_);
v___x_1513_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__6));
lean_inc(v___y_1505_);
lean_inc_ref(v___y_1504_);
lean_inc(v___y_1503_);
lean_inc_ref(v___y_1502_);
lean_inc(v___y_1501_);
v___x_1514_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14(v_recArgInfos_1467_, v_a_1478_, v___x_1475_, v___x_1513_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_);
if (lean_obj_tag(v___x_1514_) == 0)
{
lean_object* v_a_1515_; uint8_t v___x_1516_; lean_object* v___x_1517_; 
v_a_1515_ = lean_ctor_get(v___x_1514_, 0);
lean_inc(v_a_1515_);
lean_dec_ref(v___x_1514_);
v___x_1516_ = lean_unbox(v_a_1510_);
lean_dec(v_a_1510_);
v___x_1517_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2(v___x_1491_, v_recArgInfos_1467_, v_a_1478_, v___x_1499_, v___x_1475_, v_fixedParamPerms_1465_, v_xs_1466_, v_preDefs_1464_, v_numIndices_1507_, v___x_1496_, v___f_1495_, v___x_1516_, v___x_1513_, v_a_1515_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_);
lean_dec(v_numIndices_1507_);
lean_dec_ref(v_preDefs_1464_);
lean_dec(v_a_1478_);
return v___x_1517_;
}
else
{
lean_object* v_a_1518_; lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1525_; 
lean_dec(v_a_1510_);
lean_dec(v_numIndices_1507_);
lean_dec(v___y_1505_);
lean_dec_ref(v___y_1504_);
lean_dec(v___y_1503_);
lean_dec_ref(v___y_1502_);
lean_dec(v___y_1501_);
lean_dec_ref(v___x_1499_);
lean_dec(v_a_1478_);
lean_dec_ref(v_recArgInfos_1467_);
lean_dec_ref(v_xs_1466_);
lean_dec_ref(v_fixedParamPerms_1465_);
lean_dec_ref(v_preDefs_1464_);
v_a_1518_ = lean_ctor_get(v___x_1514_, 0);
v_isSharedCheck_1525_ = !lean_is_exclusive(v___x_1514_);
if (v_isSharedCheck_1525_ == 0)
{
v___x_1520_ = v___x_1514_;
v_isShared_1521_ = v_isSharedCheck_1525_;
goto v_resetjp_1519_;
}
else
{
lean_inc(v_a_1518_);
lean_dec(v___x_1514_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1525_;
goto v_resetjp_1519_;
}
v_resetjp_1519_:
{
lean_object* v___x_1523_; 
if (v_isShared_1521_ == 0)
{
v___x_1523_ = v___x_1520_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v_a_1518_);
v___x_1523_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
return v___x_1523_;
}
}
}
}
else
{
lean_object* v___f_1526_; lean_object* v___x_1527_; 
lean_dec(v_a_1510_);
lean_dec(v_numIndices_1507_);
lean_dec_ref(v___x_1499_);
lean_dec_ref(v_xs_1466_);
lean_dec_ref(v_fixedParamPerms_1465_);
lean_dec_ref(v_preDefs_1464_);
lean_inc(v_a_1478_);
v___f_1526_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__3___boxed), 11, 4);
lean_closure_set(v___f_1526_, 0, v_recArgInfos_1467_);
lean_closure_set(v___f_1526_, 1, v_a_1478_);
lean_closure_set(v___f_1526_, 2, v___x_1475_);
lean_closure_set(v___f_1526_, 3, v___f_1511_);
v___x_1527_ = l_Lean_Elab_Structural_withFunTypes___redArg(v_a_1478_, v___f_1526_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_);
return v___x_1527_;
}
}
else
{
lean_object* v_a_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1535_; 
lean_dec(v_numIndices_1507_);
lean_dec(v___y_1505_);
lean_dec_ref(v___y_1504_);
lean_dec(v___y_1503_);
lean_dec_ref(v___y_1502_);
lean_dec(v___y_1501_);
lean_dec_ref(v___x_1499_);
lean_dec(v_a_1478_);
lean_dec_ref(v_recArgInfos_1467_);
lean_dec_ref(v_xs_1466_);
lean_dec_ref(v_fixedParamPerms_1465_);
lean_dec_ref(v_preDefs_1464_);
v_a_1528_ = lean_ctor_get(v___x_1509_, 0);
v_isSharedCheck_1535_ = !lean_is_exclusive(v___x_1509_);
if (v_isSharedCheck_1535_ == 0)
{
v___x_1530_ = v___x_1509_;
v_isShared_1531_ = v_isSharedCheck_1535_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_a_1528_);
lean_dec(v___x_1509_);
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
lean_object* v_a_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1567_; 
lean_del_object(v___x_1485_);
lean_dec(v_a_1478_);
lean_dec(v_a_1472_);
lean_dec_ref(v_a_1471_);
lean_dec(v_a_1470_);
lean_dec_ref(v_a_1469_);
lean_dec(v_a_1468_);
lean_dec_ref(v_recArgInfos_1467_);
lean_dec_ref(v_xs_1466_);
lean_dec_ref(v_fixedParamPerms_1465_);
lean_dec_ref(v_preDefs_1464_);
v_a_1560_ = lean_ctor_get(v___x_1489_, 0);
v_isSharedCheck_1567_ = !lean_is_exclusive(v___x_1489_);
if (v_isSharedCheck_1567_ == 0)
{
v___x_1562_ = v___x_1489_;
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_a_1560_);
lean_dec(v___x_1489_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___x_1565_; 
if (v_isShared_1563_ == 0)
{
v___x_1565_ = v___x_1562_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v_a_1560_);
v___x_1565_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
return v___x_1565_;
}
}
}
}
}
else
{
lean_object* v_a_1570_; lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1577_; 
lean_dec(v_a_1472_);
lean_dec_ref(v_a_1471_);
lean_dec(v_a_1470_);
lean_dec_ref(v_a_1469_);
lean_dec(v_a_1468_);
lean_dec_ref(v_recArgInfos_1467_);
lean_dec_ref(v_xs_1466_);
lean_dec_ref(v_fixedParamPerms_1465_);
lean_dec_ref(v_preDefs_1464_);
v_a_1570_ = lean_ctor_get(v___x_1477_, 0);
v_isSharedCheck_1577_ = !lean_is_exclusive(v___x_1477_);
if (v_isSharedCheck_1577_ == 0)
{
v___x_1572_ = v___x_1477_;
v_isShared_1573_ = v_isSharedCheck_1577_;
goto v_resetjp_1571_;
}
else
{
lean_inc(v_a_1570_);
lean_dec(v___x_1477_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1577_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
lean_object* v___x_1575_; 
if (v_isShared_1573_ == 0)
{
v___x_1575_ = v___x_1572_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v_a_1570_);
v___x_1575_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
return v___x_1575_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___boxed(lean_object* v_preDefs_1578_, lean_object* v_fixedParamPerms_1579_, lean_object* v_xs_1580_, lean_object* v_recArgInfos_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_){
_start:
{
lean_object* v_res_1588_; 
v_res_1588_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion(v_preDefs_1578_, v_fixedParamPerms_1579_, v_xs_1580_, v_recArgInfos_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_, v_a_1586_);
return v_res_1588_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2(lean_object* v_fixedParamPerms_1589_, lean_object* v_xs_1590_, lean_object* v_as_1591_, lean_object* v_i_1592_, lean_object* v_j_1593_, lean_object* v_inv_1594_, lean_object* v_bs_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_){
_start:
{
lean_object* v___x_1602_; 
v___x_1602_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___redArg(v_fixedParamPerms_1589_, v_xs_1590_, v_as_1591_, v_i_1592_, v_j_1593_, v_bs_1595_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_);
return v___x_1602_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___boxed(lean_object* v_fixedParamPerms_1603_, lean_object* v_xs_1604_, lean_object* v_as_1605_, lean_object* v_i_1606_, lean_object* v_j_1607_, lean_object* v_inv_1608_, lean_object* v_bs_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_){
_start:
{
lean_object* v_res_1616_; 
v_res_1616_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2(v_fixedParamPerms_1603_, v_xs_1604_, v_as_1605_, v_i_1606_, v_j_1607_, v_inv_1608_, v_bs_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_);
lean_dec(v___y_1610_);
lean_dec_ref(v_as_1605_);
lean_dec_ref(v_fixedParamPerms_1603_);
return v_res_1616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5(lean_object* v_00_u03b1_1617_, lean_object* v_inst_1618_, lean_object* v_f_1619_, lean_object* v_xs_1620_, lean_object* v_ys_1621_){
_start:
{
lean_object* v___x_1622_; 
v___x_1622_ = l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___redArg(v_inst_1618_, v_f_1619_, v_xs_1620_, v_ys_1621_);
return v___x_1622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___boxed(lean_object* v_00_u03b1_1623_, lean_object* v_inst_1624_, lean_object* v_f_1625_, lean_object* v_xs_1626_, lean_object* v_ys_1627_){
_start:
{
lean_object* v_res_1628_; 
v_res_1628_ = l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5(v_00_u03b1_1623_, v_inst_1624_, v_f_1625_, v_xs_1626_, v_ys_1627_);
lean_dec_ref(v_xs_1626_);
return v_res_1628_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6(lean_object* v_a_1629_, lean_object* v_a_1630_, uint8_t v_a_1631_, lean_object* v_recArgInfos_1632_, lean_object* v___x_1633_, lean_object* v_a_1634_, lean_object* v_as_1635_, lean_object* v_i_1636_, lean_object* v_j_1637_, lean_object* v_inv_1638_, lean_object* v_bs_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_){
_start:
{
lean_object* v___x_1646_; 
v___x_1646_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg(v_a_1629_, v_a_1630_, v_a_1631_, v_recArgInfos_1632_, v___x_1633_, v_a_1634_, v_as_1635_, v_i_1636_, v_j_1637_, v_bs_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_);
return v___x_1646_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___boxed(lean_object** _args){
lean_object* v_a_1647_ = _args[0];
lean_object* v_a_1648_ = _args[1];
lean_object* v_a_1649_ = _args[2];
lean_object* v_recArgInfos_1650_ = _args[3];
lean_object* v___x_1651_ = _args[4];
lean_object* v_a_1652_ = _args[5];
lean_object* v_as_1653_ = _args[6];
lean_object* v_i_1654_ = _args[7];
lean_object* v_j_1655_ = _args[8];
lean_object* v_inv_1656_ = _args[9];
lean_object* v_bs_1657_ = _args[10];
lean_object* v___y_1658_ = _args[11];
lean_object* v___y_1659_ = _args[12];
lean_object* v___y_1660_ = _args[13];
lean_object* v___y_1661_ = _args[14];
lean_object* v___y_1662_ = _args[15];
lean_object* v___y_1663_ = _args[16];
_start:
{
uint8_t v_a_29035__boxed_1664_; lean_object* v_res_1665_; 
v_a_29035__boxed_1664_ = lean_unbox(v_a_1649_);
v_res_1665_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6(v_a_1647_, v_a_1648_, v_a_29035__boxed_1664_, v_recArgInfos_1650_, v___x_1651_, v_a_1652_, v_as_1653_, v_i_1654_, v_j_1655_, v_inv_1656_, v_bs_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_);
lean_dec_ref(v_as_1653_);
lean_dec_ref(v_a_1648_);
lean_dec_ref(v_a_1647_);
return v_res_1665_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__15(lean_object* v_00_u03b3_1666_, lean_object* v_msg_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_){
_start:
{
lean_object* v___x_1674_; 
v___x_1674_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__15___redArg(v_msg_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_);
return v___x_1674_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__15___boxed(lean_object* v_00_u03b3_1675_, lean_object* v_msg_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_){
_start:
{
lean_object* v_res_1683_; 
v_res_1683_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__15(v_00_u03b3_1675_, v_msg_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_);
return v_res_1683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7(lean_object* v_00_u03b3_1684_, lean_object* v_00_u03b1_1685_, lean_object* v_00_u03b2_1686_, lean_object* v_inst_1687_, lean_object* v_f_1688_, lean_object* v_positions_1689_, lean_object* v_ys_1690_, lean_object* v_xs_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_){
_start:
{
lean_object* v___x_1698_; 
v___x_1698_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg(v_inst_1687_, v_f_1688_, v_positions_1689_, v_ys_1690_, v_xs_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_);
return v___x_1698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___boxed(lean_object* v_00_u03b3_1699_, lean_object* v_00_u03b1_1700_, lean_object* v_00_u03b2_1701_, lean_object* v_inst_1702_, lean_object* v_f_1703_, lean_object* v_positions_1704_, lean_object* v_ys_1705_, lean_object* v_xs_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_){
_start:
{
lean_object* v_res_1713_; 
v_res_1713_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7(v_00_u03b3_1699_, v_00_u03b1_1700_, v_00_u03b2_1701_, v_inst_1702_, v_f_1703_, v_positions_1704_, v_ys_1705_, v_xs_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_);
lean_dec_ref(v_xs_1706_);
lean_dec_ref(v_ys_1705_);
lean_dec_ref(v_positions_1704_);
return v_res_1713_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8(lean_object* v___x_1714_, lean_object* v_a_1715_, lean_object* v_a_1716_, lean_object* v_funTypes_1717_, lean_object* v_as_1718_, lean_object* v_i_1719_, lean_object* v_j_1720_, lean_object* v_inv_1721_, lean_object* v_bs_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_){
_start:
{
lean_object* v___x_1729_; 
v___x_1729_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg(v___x_1714_, v_a_1715_, v_a_1716_, v_funTypes_1717_, v_as_1718_, v_i_1719_, v_j_1720_, v_bs_1722_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_);
return v___x_1729_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___boxed(lean_object* v___x_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_, lean_object* v_funTypes_1733_, lean_object* v_as_1734_, lean_object* v_i_1735_, lean_object* v_j_1736_, lean_object* v_inv_1737_, lean_object* v_bs_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_){
_start:
{
lean_object* v_res_1745_; 
v_res_1745_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8(v___x_1730_, v_a_1731_, v_a_1732_, v_funTypes_1733_, v_as_1734_, v_i_1735_, v_j_1736_, v_inv_1737_, v_bs_1738_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_);
lean_dec(v___y_1739_);
lean_dec_ref(v_as_1734_);
return v_res_1745_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9(lean_object* v_fixedParamPerms_1746_, lean_object* v_xs_1747_, lean_object* v_as_1748_, lean_object* v_i_1749_, lean_object* v_j_1750_, lean_object* v_inv_1751_, lean_object* v_bs_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_){
_start:
{
lean_object* v___x_1759_; 
v___x_1759_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9___redArg(v_fixedParamPerms_1746_, v_xs_1747_, v_as_1748_, v_i_1749_, v_j_1750_, v_bs_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_);
return v___x_1759_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9___boxed(lean_object* v_fixedParamPerms_1760_, lean_object* v_xs_1761_, lean_object* v_as_1762_, lean_object* v_i_1763_, lean_object* v_j_1764_, lean_object* v_inv_1765_, lean_object* v_bs_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_){
_start:
{
lean_object* v_res_1773_; 
v_res_1773_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9(v_fixedParamPerms_1760_, v_xs_1761_, v_as_1762_, v_i_1763_, v_j_1764_, v_inv_1765_, v_bs_1766_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_);
lean_dec_ref(v_as_1762_);
return v_res_1773_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12(lean_object* v_cls_1774_, lean_object* v_msg_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_){
_start:
{
lean_object* v___x_1782_; 
v___x_1782_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v_cls_1774_, v_msg_1775_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_);
return v___x_1782_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___boxed(lean_object* v_cls_1783_, lean_object* v_msg_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_){
_start:
{
lean_object* v_res_1791_; 
v_res_1791_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12(v_cls_1783_, v_msg_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_);
lean_dec(v___y_1789_);
lean_dec_ref(v___y_1788_);
lean_dec(v___y_1787_);
lean_dec_ref(v___y_1786_);
lean_dec(v___y_1785_);
return v_res_1791_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13(lean_object* v_a_1792_, lean_object* v_funTypes_1793_, lean_object* v_as_1794_, lean_object* v_i_1795_, lean_object* v_j_1796_, lean_object* v_inv_1797_, lean_object* v_bs_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_){
_start:
{
lean_object* v___x_1805_; 
v___x_1805_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13___redArg(v_a_1792_, v_funTypes_1793_, v_as_1794_, v_i_1795_, v_j_1796_, v_bs_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_);
return v___x_1805_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13___boxed(lean_object* v_a_1806_, lean_object* v_funTypes_1807_, lean_object* v_as_1808_, lean_object* v_i_1809_, lean_object* v_j_1810_, lean_object* v_inv_1811_, lean_object* v_bs_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_){
_start:
{
lean_object* v_res_1819_; 
v_res_1819_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13(v_a_1806_, v_funTypes_1807_, v_as_1808_, v_i_1809_, v_j_1810_, v_inv_1811_, v_bs_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_);
lean_dec_ref(v_as_1808_);
lean_dec_ref(v_funTypes_1807_);
lean_dec_ref(v_a_1806_);
return v_res_1819_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3_spec__3(lean_object* v_00_u03b1_1820_, lean_object* v_msg_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_){
_start:
{
lean_object* v___x_1828_; 
v___x_1828_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3_spec__3___redArg(v_msg_1821_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_);
return v___x_1828_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3_spec__3___boxed(lean_object* v_00_u03b1_1829_, lean_object* v_msg_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_){
_start:
{
lean_object* v_res_1837_; 
v_res_1837_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3_spec__3(v_00_u03b1_1829_, v_msg_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_);
lean_dec(v___y_1835_);
lean_dec_ref(v___y_1834_);
lean_dec(v___y_1833_);
lean_dec_ref(v___y_1832_);
lean_dec(v___y_1831_);
return v_res_1837_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__6(lean_object* v_00_u03b1_1838_, lean_object* v_inst_1839_, lean_object* v_xs_1840_, lean_object* v_f_1841_, lean_object* v_x_1842_, lean_object* v_as_1843_, size_t v_i_1844_, size_t v_stop_1845_, lean_object* v_b_1846_){
_start:
{
lean_object* v___x_1847_; 
v___x_1847_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__6___redArg(v_inst_1839_, v_xs_1840_, v_f_1841_, v_x_1842_, v_as_1843_, v_i_1844_, v_stop_1845_, v_b_1846_);
return v___x_1847_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__6___boxed(lean_object* v_00_u03b1_1848_, lean_object* v_inst_1849_, lean_object* v_xs_1850_, lean_object* v_f_1851_, lean_object* v_x_1852_, lean_object* v_as_1853_, lean_object* v_i_1854_, lean_object* v_stop_1855_, lean_object* v_b_1856_){
_start:
{
size_t v_i_boxed_1857_; size_t v_stop_boxed_1858_; lean_object* v_res_1859_; 
v_i_boxed_1857_ = lean_unbox_usize(v_i_1854_);
lean_dec(v_i_1854_);
v_stop_boxed_1858_ = lean_unbox_usize(v_stop_1855_);
lean_dec(v_stop_1855_);
v_res_1859_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__6(v_00_u03b1_1848_, v_inst_1849_, v_xs_1850_, v_f_1851_, v_x_1852_, v_as_1853_, v_i_boxed_1857_, v_stop_boxed_1858_, v_b_1856_);
lean_dec_ref(v_as_1853_);
lean_dec(v_x_1852_);
lean_dec_ref(v_xs_1850_);
return v_res_1859_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8(lean_object* v_00_u03b1_1860_, lean_object* v_inst_1861_, lean_object* v_xs_1862_, lean_object* v_f_1863_, size_t v_sz_1864_, size_t v_i_1865_, lean_object* v_bs_1866_){
_start:
{
lean_object* v___x_1867_; 
v___x_1867_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8___redArg(v_inst_1861_, v_xs_1862_, v_f_1863_, v_sz_1864_, v_i_1865_, v_bs_1866_);
return v___x_1867_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8___boxed(lean_object* v_00_u03b1_1868_, lean_object* v_inst_1869_, lean_object* v_xs_1870_, lean_object* v_f_1871_, lean_object* v_sz_1872_, lean_object* v_i_1873_, lean_object* v_bs_1874_){
_start:
{
size_t v_sz_boxed_1875_; size_t v_i_boxed_1876_; lean_object* v_res_1877_; 
v_sz_boxed_1875_ = lean_unbox_usize(v_sz_1872_);
lean_dec(v_sz_1872_);
v_i_boxed_1876_ = lean_unbox_usize(v_i_1873_);
lean_dec(v_i_1873_);
v_res_1877_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8(v_00_u03b1_1868_, v_inst_1869_, v_xs_1870_, v_f_1871_, v_sz_boxed_1875_, v_i_boxed_1876_, v_bs_1874_);
lean_dec_ref(v_xs_1870_);
return v_res_1877_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9(lean_object* v_xs_1878_, lean_object* v_ys_1879_, lean_object* v_hsz_1880_, lean_object* v_x_1881_, lean_object* v_x_1882_){
_start:
{
uint8_t v___x_1883_; 
v___x_1883_ = l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9___redArg(v_xs_1878_, v_ys_1879_, v_x_1881_);
return v___x_1883_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9___boxed(lean_object* v_xs_1884_, lean_object* v_ys_1885_, lean_object* v_hsz_1886_, lean_object* v_x_1887_, lean_object* v_x_1888_){
_start:
{
uint8_t v_res_1889_; lean_object* v_r_1890_; 
v_res_1889_ = l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9(v_xs_1884_, v_ys_1885_, v_hsz_1886_, v_x_1887_, v_x_1888_);
lean_dec_ref(v_ys_1885_);
lean_dec_ref(v_xs_1884_);
v_r_1890_ = lean_box(v_res_1889_);
return v_r_1890_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10(lean_object* v_n_1891_, lean_object* v_as_1892_, lean_object* v_lo_1893_, lean_object* v_hi_1894_, lean_object* v_w_1895_, lean_object* v_hlo_1896_, lean_object* v_hhi_1897_){
_start:
{
lean_object* v___x_1898_; 
v___x_1898_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg(v_as_1892_, v_lo_1893_, v_hi_1894_);
return v___x_1898_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___boxed(lean_object* v_n_1899_, lean_object* v_as_1900_, lean_object* v_lo_1901_, lean_object* v_hi_1902_, lean_object* v_w_1903_, lean_object* v_hlo_1904_, lean_object* v_hhi_1905_){
_start:
{
lean_object* v_res_1906_; 
v_res_1906_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10(v_n_1899_, v_as_1900_, v_lo_1901_, v_hi_1902_, v_w_1903_, v_hlo_1904_, v_hhi_1905_);
lean_dec(v_hi_1902_);
lean_dec(v_n_1899_);
return v_res_1906_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__14(lean_object* v_00_u03b2_1907_, lean_object* v_inst_1908_, lean_object* v_xs_1909_, size_t v_sz_1910_, size_t v_i_1911_, lean_object* v_bs_1912_){
_start:
{
lean_object* v___x_1913_; 
v___x_1913_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__14___redArg(v_inst_1908_, v_xs_1909_, v_sz_1910_, v_i_1911_, v_bs_1912_);
return v___x_1913_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__14___boxed(lean_object* v_00_u03b2_1914_, lean_object* v_inst_1915_, lean_object* v_xs_1916_, lean_object* v_sz_1917_, lean_object* v_i_1918_, lean_object* v_bs_1919_){
_start:
{
size_t v_sz_boxed_1920_; size_t v_i_boxed_1921_; lean_object* v_res_1922_; 
v_sz_boxed_1920_ = lean_unbox_usize(v_sz_1917_);
lean_dec(v_sz_1917_);
v_i_boxed_1921_ = lean_unbox_usize(v_i_1918_);
lean_dec(v_i_1918_);
v_res_1922_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__14(v_00_u03b2_1914_, v_inst_1915_, v_xs_1916_, v_sz_boxed_1920_, v_i_boxed_1921_, v_bs_1919_);
lean_dec_ref(v_xs_1916_);
return v_res_1922_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__16(lean_object* v_00_u03b1_1923_, lean_object* v_00_u03b3_1924_, lean_object* v_00_u03b2_1925_, lean_object* v_inst_1926_, lean_object* v_xs_1927_, lean_object* v_f_1928_, lean_object* v_as_1929_, lean_object* v_bs_1930_, lean_object* v_i_1931_, lean_object* v_cs_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_){
_start:
{
lean_object* v___x_1939_; 
v___x_1939_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__16___redArg(v_inst_1926_, v_xs_1927_, v_f_1928_, v_as_1929_, v_bs_1930_, v_i_1931_, v_cs_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_);
return v___x_1939_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__16___boxed(lean_object* v_00_u03b1_1940_, lean_object* v_00_u03b3_1941_, lean_object* v_00_u03b2_1942_, lean_object* v_inst_1943_, lean_object* v_xs_1944_, lean_object* v_f_1945_, lean_object* v_as_1946_, lean_object* v_bs_1947_, lean_object* v_i_1948_, lean_object* v_cs_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_){
_start:
{
lean_object* v_res_1956_; 
v_res_1956_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7_spec__16(v_00_u03b1_1940_, v_00_u03b3_1941_, v_00_u03b2_1942_, v_inst_1943_, v_xs_1944_, v_f_1945_, v_as_1946_, v_bs_1947_, v_i_1948_, v_cs_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_);
lean_dec_ref(v_bs_1947_);
lean_dec_ref(v_as_1946_);
lean_dec_ref(v_xs_1944_);
return v_res_1956_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8_spec__9(lean_object* v_00_u03b1_1957_, lean_object* v_xs_1958_, lean_object* v_inst_1959_, lean_object* v_f_1960_, size_t v_sz_1961_, size_t v_i_1962_, lean_object* v_bs_1963_){
_start:
{
lean_object* v___x_1964_; 
v___x_1964_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8_spec__9___redArg(v_xs_1958_, v_inst_1959_, v_f_1960_, v_sz_1961_, v_i_1962_, v_bs_1963_);
return v___x_1964_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8_spec__9___boxed(lean_object* v_00_u03b1_1965_, lean_object* v_xs_1966_, lean_object* v_inst_1967_, lean_object* v_f_1968_, lean_object* v_sz_1969_, lean_object* v_i_1970_, lean_object* v_bs_1971_){
_start:
{
size_t v_sz_boxed_1972_; size_t v_i_boxed_1973_; lean_object* v_res_1974_; 
v_sz_boxed_1972_ = lean_unbox_usize(v_sz_1969_);
lean_dec(v_sz_1969_);
v_i_boxed_1973_ = lean_unbox_usize(v_i_1970_);
lean_dec(v_i_1970_);
v_res_1974_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8_spec__9(v_00_u03b1_1965_, v_xs_1966_, v_inst_1967_, v_f_1968_, v_sz_boxed_1972_, v_i_boxed_1973_, v_bs_1971_);
lean_dec_ref(v_xs_1966_);
return v_res_1974_;
}
}
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___redArg___lam__0(lean_object* v_x_1975_){
_start:
{
uint8_t v___x_1976_; 
v___x_1976_ = 0;
return v___x_1976_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___redArg___lam__0___boxed(lean_object* v_x_1977_){
_start:
{
uint8_t v_res_1978_; lean_object* v_r_1979_; 
v_res_1978_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___redArg___lam__0(v_x_1977_);
lean_dec(v_x_1977_);
v_r_1979_ = lean_box(v_res_1978_);
return v_r_1979_;
}
}
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___redArg___lam__1(lean_object* v_fvarId_1980_, lean_object* v_x_1981_){
_start:
{
uint8_t v___x_1982_; 
v___x_1982_ = l_Lean_instBEqFVarId_beq(v_fvarId_1980_, v_x_1981_);
return v___x_1982_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___redArg___lam__1___boxed(lean_object* v_fvarId_1983_, lean_object* v_x_1984_){
_start:
{
uint8_t v_res_1985_; lean_object* v_r_1986_; 
v_res_1985_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___redArg___lam__1(v_fvarId_1983_, v_x_1984_);
lean_dec(v_x_1984_);
lean_dec(v_fvarId_1983_);
v_r_1986_ = lean_box(v_res_1985_);
return v_r_1986_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; 
v___x_1988_ = lean_box(0);
v___x_1989_ = lean_unsigned_to_nat(16u);
v___x_1990_ = lean_mk_array(v___x_1989_, v___x_1988_);
return v___x_1990_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; 
v___x_1991_ = lean_obj_once(&l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___redArg___closed__1, &l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___redArg___closed__1_once, _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___redArg___closed__1);
v___x_1992_ = lean_unsigned_to_nat(0u);
v___x_1993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1993_, 0, v___x_1992_);
lean_ctor_set(v___x_1993_, 1, v___x_1991_);
return v___x_1993_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___redArg(lean_object* v_e_1994_, lean_object* v_fvarId_1995_, lean_object* v___y_1996_){
_start:
{
lean_object* v___x_1998_; uint8_t v_fst_2000_; lean_object* v_mctx_2001_; lean_object* v___y_2019_; lean_object* v_mctx_2024_; lean_object* v___f_2025_; lean_object* v___f_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; uint8_t v___x_2029_; 
v___x_1998_ = lean_st_ref_get(v___y_1996_);
v_mctx_2024_ = lean_ctor_get(v___x_1998_, 0);
lean_inc_ref(v_mctx_2024_);
lean_dec(v___x_1998_);
v___f_2025_ = ((lean_object*)(l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___redArg___closed__0));
v___f_2026_ = lean_alloc_closure((void*)(l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_2026_, 0, v_fvarId_1995_);
v___x_2027_ = lean_obj_once(&l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___redArg___closed__2, &l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___redArg___closed__2_once, _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___redArg___closed__2);
lean_inc_ref(v_mctx_2024_);
v___x_2028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2028_, 0, v___x_2027_);
lean_ctor_set(v___x_2028_, 1, v_mctx_2024_);
v___x_2029_ = l_Lean_Expr_hasFVar(v_e_1994_);
if (v___x_2029_ == 0)
{
uint8_t v___x_2030_; 
v___x_2030_ = l_Lean_Expr_hasMVar(v_e_1994_);
if (v___x_2030_ == 0)
{
lean_dec_ref(v___x_2028_);
lean_dec_ref(v___f_2026_);
lean_dec_ref(v_e_1994_);
v_fst_2000_ = v___x_2030_;
v_mctx_2001_ = v_mctx_2024_;
goto v___jp_1999_;
}
else
{
lean_object* v___x_2031_; 
lean_dec_ref(v_mctx_2024_);
v___x_2031_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2026_, v___f_2025_, v_e_1994_, v___x_2028_);
v___y_2019_ = v___x_2031_;
goto v___jp_2018_;
}
}
else
{
lean_object* v___x_2032_; 
lean_dec_ref(v_mctx_2024_);
v___x_2032_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2026_, v___f_2025_, v_e_1994_, v___x_2028_);
v___y_2019_ = v___x_2032_;
goto v___jp_2018_;
}
v___jp_1999_:
{
lean_object* v___x_2002_; lean_object* v_cache_2003_; lean_object* v_zetaDeltaFVarIds_2004_; lean_object* v_postponed_2005_; lean_object* v_diag_2006_; lean_object* v___x_2008_; uint8_t v_isShared_2009_; uint8_t v_isSharedCheck_2016_; 
v___x_2002_ = lean_st_ref_take(v___y_1996_);
v_cache_2003_ = lean_ctor_get(v___x_2002_, 1);
v_zetaDeltaFVarIds_2004_ = lean_ctor_get(v___x_2002_, 2);
v_postponed_2005_ = lean_ctor_get(v___x_2002_, 3);
v_diag_2006_ = lean_ctor_get(v___x_2002_, 4);
v_isSharedCheck_2016_ = !lean_is_exclusive(v___x_2002_);
if (v_isSharedCheck_2016_ == 0)
{
lean_object* v_unused_2017_; 
v_unused_2017_ = lean_ctor_get(v___x_2002_, 0);
lean_dec(v_unused_2017_);
v___x_2008_ = v___x_2002_;
v_isShared_2009_ = v_isSharedCheck_2016_;
goto v_resetjp_2007_;
}
else
{
lean_inc(v_diag_2006_);
lean_inc(v_postponed_2005_);
lean_inc(v_zetaDeltaFVarIds_2004_);
lean_inc(v_cache_2003_);
lean_dec(v___x_2002_);
v___x_2008_ = lean_box(0);
v_isShared_2009_ = v_isSharedCheck_2016_;
goto v_resetjp_2007_;
}
v_resetjp_2007_:
{
lean_object* v___x_2011_; 
if (v_isShared_2009_ == 0)
{
lean_ctor_set(v___x_2008_, 0, v_mctx_2001_);
v___x_2011_ = v___x_2008_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v_mctx_2001_);
lean_ctor_set(v_reuseFailAlloc_2015_, 1, v_cache_2003_);
lean_ctor_set(v_reuseFailAlloc_2015_, 2, v_zetaDeltaFVarIds_2004_);
lean_ctor_set(v_reuseFailAlloc_2015_, 3, v_postponed_2005_);
lean_ctor_set(v_reuseFailAlloc_2015_, 4, v_diag_2006_);
v___x_2011_ = v_reuseFailAlloc_2015_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; 
v___x_2012_ = lean_st_ref_set(v___y_1996_, v___x_2011_);
v___x_2013_ = lean_box(v_fst_2000_);
v___x_2014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2014_, 0, v___x_2013_);
return v___x_2014_;
}
}
}
v___jp_2018_:
{
lean_object* v_snd_2020_; lean_object* v_fst_2021_; lean_object* v_mctx_2022_; uint8_t v___x_2023_; 
v_snd_2020_ = lean_ctor_get(v___y_2019_, 1);
lean_inc(v_snd_2020_);
v_fst_2021_ = lean_ctor_get(v___y_2019_, 0);
lean_inc(v_fst_2021_);
lean_dec_ref(v___y_2019_);
v_mctx_2022_ = lean_ctor_get(v_snd_2020_, 1);
lean_inc_ref(v_mctx_2022_);
lean_dec(v_snd_2020_);
v___x_2023_ = lean_unbox(v_fst_2021_);
lean_dec(v_fst_2021_);
v_fst_2000_ = v___x_2023_;
v_mctx_2001_ = v_mctx_2022_;
goto v___jp_1999_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___redArg___boxed(lean_object* v_e_2033_, lean_object* v_fvarId_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_){
_start:
{
lean_object* v_res_2037_; 
v_res_2037_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___redArg(v_e_2033_, v_fvarId_2034_, v___y_2035_);
lean_dec(v___y_2035_);
return v_res_2037_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6(lean_object* v_e_2038_, lean_object* v_fvarId_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_){
_start:
{
lean_object* v___x_2046_; 
v___x_2046_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___redArg(v_e_2038_, v_fvarId_2039_, v___y_2042_);
return v___x_2046_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___boxed(lean_object* v_e_2047_, lean_object* v_fvarId_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_){
_start:
{
lean_object* v_res_2055_; 
v_res_2055_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6(v_e_2047_, v_fvarId_2048_, v___y_2049_, v___y_2050_, v___y_2051_, v___y_2052_, v___y_2053_);
lean_dec(v___y_2053_);
lean_dec_ref(v___y_2052_);
lean_dec(v___y_2051_);
lean_dec_ref(v___y_2050_);
lean_dec(v___y_2049_);
return v_res_2055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg___lam__0(lean_object* v_k_2056_, lean_object* v___y_2057_, lean_object* v_b_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_){
_start:
{
lean_object* v___x_2064_; 
v___x_2064_ = lean_apply_7(v_k_2056_, v_b_2058_, v___y_2057_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_, lean_box(0));
return v___x_2064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg___lam__0___boxed(lean_object* v_k_2065_, lean_object* v___y_2066_, lean_object* v_b_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_){
_start:
{
lean_object* v_res_2073_; 
v_res_2073_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg___lam__0(v_k_2065_, v___y_2066_, v_b_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_);
return v_res_2073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg(lean_object* v_perm_2074_, lean_object* v_type_2075_, lean_object* v_k_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_){
_start:
{
lean_object* v___f_2083_; lean_object* v___x_2084_; 
v___f_2083_ = lean_alloc_closure((void*)(l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2083_, 0, v_k_2076_);
lean_closure_set(v___f_2083_, 1, v___y_2077_);
v___x_2084_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl(lean_box(0), v_perm_2074_, v_type_2075_, v___f_2083_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_);
if (lean_obj_tag(v___x_2084_) == 0)
{
return v___x_2084_;
}
else
{
lean_object* v_a_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2092_; 
v_a_2085_ = lean_ctor_get(v___x_2084_, 0);
v_isSharedCheck_2092_ = !lean_is_exclusive(v___x_2084_);
if (v_isSharedCheck_2092_ == 0)
{
v___x_2087_ = v___x_2084_;
v_isShared_2088_ = v_isSharedCheck_2092_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_a_2085_);
lean_dec(v___x_2084_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2092_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
lean_object* v___x_2090_; 
if (v_isShared_2088_ == 0)
{
v___x_2090_ = v___x_2087_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v_a_2085_);
v___x_2090_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
return v___x_2090_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg___boxed(lean_object* v_perm_2093_, lean_object* v_type_2094_, lean_object* v_k_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_){
_start:
{
lean_object* v_res_2102_; 
v_res_2102_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg(v_perm_2093_, v_type_2094_, v_k_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_);
return v_res_2102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13(lean_object* v_00_u03b1_2103_, lean_object* v_perm_2104_, lean_object* v_type_2105_, lean_object* v_k_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_){
_start:
{
lean_object* v___x_2113_; 
v___x_2113_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg(v_perm_2104_, v_type_2105_, v_k_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_);
return v___x_2113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___boxed(lean_object* v_00_u03b1_2114_, lean_object* v_perm_2115_, lean_object* v_type_2116_, lean_object* v_k_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_){
_start:
{
lean_object* v_res_2124_; 
v_res_2124_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13(v_00_u03b1_2114_, v_perm_2115_, v_type_2116_, v_k_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_);
return v_res_2124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0(lean_object* v_a_2125_, lean_object* v_fst_2126_, lean_object* v_fst_2127_, lean_object* v___x_2128_, lean_object* v___x_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_){
_start:
{
lean_object* v___x_2136_; 
lean_inc_ref(v_fst_2126_);
v___x_2136_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion(v_a_2125_, v_fst_2126_, v_fst_2127_, v___x_2128_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_);
if (lean_obj_tag(v___x_2136_) == 0)
{
lean_object* v_a_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2146_; 
v_a_2137_ = lean_ctor_get(v___x_2136_, 0);
v_isSharedCheck_2146_ = !lean_is_exclusive(v___x_2136_);
if (v_isSharedCheck_2146_ == 0)
{
v___x_2139_ = v___x_2136_;
v_isShared_2140_ = v_isSharedCheck_2146_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_a_2137_);
lean_dec(v___x_2136_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2146_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2144_; 
v___x_2141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2141_, 0, v_a_2137_);
lean_ctor_set(v___x_2141_, 1, v_fst_2126_);
v___x_2142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2142_, 0, v___x_2129_);
lean_ctor_set(v___x_2142_, 1, v___x_2141_);
if (v_isShared_2140_ == 0)
{
lean_ctor_set(v___x_2139_, 0, v___x_2142_);
v___x_2144_ = v___x_2139_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v___x_2142_);
v___x_2144_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2143_;
}
v_reusejp_2143_:
{
return v___x_2144_;
}
}
}
else
{
lean_object* v_a_2147_; lean_object* v___x_2149_; uint8_t v_isShared_2150_; uint8_t v_isSharedCheck_2154_; 
lean_dec_ref(v___x_2129_);
lean_dec_ref(v_fst_2126_);
v_a_2147_ = lean_ctor_get(v___x_2136_, 0);
v_isSharedCheck_2154_ = !lean_is_exclusive(v___x_2136_);
if (v_isSharedCheck_2154_ == 0)
{
v___x_2149_ = v___x_2136_;
v_isShared_2150_ = v_isSharedCheck_2154_;
goto v_resetjp_2148_;
}
else
{
lean_inc(v_a_2147_);
lean_dec(v___x_2136_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___boxed(lean_object* v_a_2155_, lean_object* v_fst_2156_, lean_object* v_fst_2157_, lean_object* v___x_2158_, lean_object* v___x_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_){
_start:
{
lean_object* v_res_2166_; 
v_res_2166_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0(v_a_2155_, v_fst_2156_, v_fst_2157_, v___x_2158_, v___x_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_);
return v_res_2166_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__3(size_t v_sz_2167_, size_t v_i_2168_, lean_object* v_bs_2169_){
_start:
{
uint8_t v___x_2170_; 
v___x_2170_ = lean_usize_dec_lt(v_i_2168_, v_sz_2167_);
if (v___x_2170_ == 0)
{
return v_bs_2169_;
}
else
{
lean_object* v_v_2171_; lean_object* v___x_2172_; lean_object* v_bs_x27_2173_; lean_object* v___x_2174_; size_t v___x_2175_; size_t v___x_2176_; lean_object* v___x_2177_; 
v_v_2171_ = lean_array_uget(v_bs_2169_, v_i_2168_);
v___x_2172_ = lean_unsigned_to_nat(0u);
v_bs_x27_2173_ = lean_array_uset(v_bs_2169_, v_i_2168_, v___x_2172_);
v___x_2174_ = l_Lean_Elab_Structural_RecArgInfo_indicesAndRecArgPos(v_v_2171_);
v___x_2175_ = ((size_t)1ULL);
v___x_2176_ = lean_usize_add(v_i_2168_, v___x_2175_);
v___x_2177_ = lean_array_uset(v_bs_x27_2173_, v_i_2168_, v___x_2174_);
v_i_2168_ = v___x_2176_;
v_bs_2169_ = v___x_2177_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__3___boxed(lean_object* v_sz_2179_, lean_object* v_i_2180_, lean_object* v_bs_2181_){
_start:
{
size_t v_sz_boxed_2182_; size_t v_i_boxed_2183_; lean_object* v_res_2184_; 
v_sz_boxed_2182_ = lean_unbox_usize(v_sz_2179_);
lean_dec(v_sz_2179_);
v_i_boxed_2183_ = lean_unbox_usize(v_i_2180_);
lean_dec(v_i_2180_);
v_res_2184_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__3(v_sz_boxed_2182_, v_i_boxed_2183_, v_bs_2181_);
return v_res_2184_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__14_spec__17_spec__24(lean_object* v_x_2185_, lean_object* v_x_2186_, lean_object* v_x_2187_){
_start:
{
if (lean_obj_tag(v_x_2187_) == 0)
{
lean_dec(v_x_2185_);
return v_x_2186_;
}
else
{
lean_object* v_head_2188_; lean_object* v_tail_2189_; lean_object* v___x_2191_; uint8_t v_isShared_2192_; uint8_t v_isSharedCheck_2199_; 
v_head_2188_ = lean_ctor_get(v_x_2187_, 0);
v_tail_2189_ = lean_ctor_get(v_x_2187_, 1);
v_isSharedCheck_2199_ = !lean_is_exclusive(v_x_2187_);
if (v_isSharedCheck_2199_ == 0)
{
v___x_2191_ = v_x_2187_;
v_isShared_2192_ = v_isSharedCheck_2199_;
goto v_resetjp_2190_;
}
else
{
lean_inc(v_tail_2189_);
lean_inc(v_head_2188_);
lean_dec(v_x_2187_);
v___x_2191_ = lean_box(0);
v_isShared_2192_ = v_isSharedCheck_2199_;
goto v_resetjp_2190_;
}
v_resetjp_2190_:
{
lean_object* v___x_2194_; 
lean_inc(v_x_2185_);
if (v_isShared_2192_ == 0)
{
lean_ctor_set_tag(v___x_2191_, 5);
lean_ctor_set(v___x_2191_, 1, v_x_2185_);
lean_ctor_set(v___x_2191_, 0, v_x_2186_);
v___x_2194_ = v___x_2191_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v_x_2186_);
lean_ctor_set(v_reuseFailAlloc_2198_, 1, v_x_2185_);
v___x_2194_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2193_;
}
v_reusejp_2193_:
{
lean_object* v___x_2195_; lean_object* v___x_2196_; 
v___x_2195_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(v_head_2188_);
v___x_2196_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2196_, 0, v___x_2194_);
lean_ctor_set(v___x_2196_, 1, v___x_2195_);
v_x_2186_ = v___x_2196_;
v_x_2187_ = v_tail_2189_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__14_spec__17(lean_object* v_x_2200_, lean_object* v_x_2201_, lean_object* v_x_2202_){
_start:
{
if (lean_obj_tag(v_x_2202_) == 0)
{
lean_dec(v_x_2200_);
return v_x_2201_;
}
else
{
lean_object* v_head_2203_; lean_object* v_tail_2204_; lean_object* v___x_2206_; uint8_t v_isShared_2207_; uint8_t v_isSharedCheck_2214_; 
v_head_2203_ = lean_ctor_get(v_x_2202_, 0);
v_tail_2204_ = lean_ctor_get(v_x_2202_, 1);
v_isSharedCheck_2214_ = !lean_is_exclusive(v_x_2202_);
if (v_isSharedCheck_2214_ == 0)
{
v___x_2206_ = v_x_2202_;
v_isShared_2207_ = v_isSharedCheck_2214_;
goto v_resetjp_2205_;
}
else
{
lean_inc(v_tail_2204_);
lean_inc(v_head_2203_);
lean_dec(v_x_2202_);
v___x_2206_ = lean_box(0);
v_isShared_2207_ = v_isSharedCheck_2214_;
goto v_resetjp_2205_;
}
v_resetjp_2205_:
{
lean_object* v___x_2209_; 
lean_inc(v_x_2200_);
if (v_isShared_2207_ == 0)
{
lean_ctor_set_tag(v___x_2206_, 5);
lean_ctor_set(v___x_2206_, 1, v_x_2200_);
lean_ctor_set(v___x_2206_, 0, v_x_2201_);
v___x_2209_ = v___x_2206_;
goto v_reusejp_2208_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v_x_2201_);
lean_ctor_set(v_reuseFailAlloc_2213_, 1, v_x_2200_);
v___x_2209_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2208_;
}
v_reusejp_2208_:
{
lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; 
v___x_2210_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(v_head_2203_);
v___x_2211_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2211_, 0, v___x_2209_);
lean_ctor_set(v___x_2211_, 1, v___x_2210_);
v___x_2212_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__14_spec__17_spec__24(v_x_2200_, v___x_2211_, v_tail_2204_);
return v___x_2212_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__14(lean_object* v_x_2215_, lean_object* v_x_2216_){
_start:
{
if (lean_obj_tag(v_x_2215_) == 0)
{
lean_object* v___x_2217_; 
lean_dec(v_x_2216_);
v___x_2217_ = lean_box(0);
return v___x_2217_;
}
else
{
lean_object* v_tail_2218_; 
v_tail_2218_ = lean_ctor_get(v_x_2215_, 1);
if (lean_obj_tag(v_tail_2218_) == 0)
{
lean_object* v_head_2219_; lean_object* v___x_2220_; 
lean_dec(v_x_2216_);
v_head_2219_ = lean_ctor_get(v_x_2215_, 0);
lean_inc(v_head_2219_);
lean_dec_ref(v_x_2215_);
v___x_2220_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(v_head_2219_);
return v___x_2220_;
}
else
{
lean_object* v_head_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; 
lean_inc(v_tail_2218_);
v_head_2221_ = lean_ctor_get(v_x_2215_, 0);
lean_inc(v_head_2221_);
lean_dec_ref(v_x_2215_);
v___x_2222_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(v_head_2221_);
v___x_2223_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__14_spec__17(v_x_2216_, v___x_2222_, v_tail_2218_);
return v___x_2223_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__5(void){
_start:
{
lean_object* v___x_2232_; lean_object* v___x_2233_; 
v___x_2232_ = ((lean_object*)(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__0));
v___x_2233_ = lean_string_length(v___x_2232_);
return v___x_2233_;
}
}
static lean_object* _init_l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__6(void){
_start:
{
lean_object* v___x_2234_; lean_object* v___x_2235_; 
v___x_2234_ = lean_obj_once(&l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__5, &l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__5_once, _init_l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__5);
v___x_2235_ = lean_nat_to_int(v___x_2234_);
return v___x_2235_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10(lean_object* v_xs_2243_){
_start:
{
lean_object* v___x_2244_; lean_object* v___x_2245_; uint8_t v___x_2246_; 
v___x_2244_ = lean_array_get_size(v_xs_2243_);
v___x_2245_ = lean_unsigned_to_nat(0u);
v___x_2246_ = lean_nat_dec_eq(v___x_2244_, v___x_2245_);
if (v___x_2246_ == 0)
{
lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; 
v___x_2247_ = lean_array_to_list(v_xs_2243_);
v___x_2248_ = ((lean_object*)(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__3));
v___x_2249_ = l_Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__14(v___x_2247_, v___x_2248_);
v___x_2250_ = lean_obj_once(&l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__6, &l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__6_once, _init_l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__6);
v___x_2251_ = ((lean_object*)(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__7));
v___x_2252_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2252_, 0, v___x_2251_);
lean_ctor_set(v___x_2252_, 1, v___x_2249_);
v___x_2253_ = ((lean_object*)(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__8));
v___x_2254_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2254_, 0, v___x_2252_);
lean_ctor_set(v___x_2254_, 1, v___x_2253_);
v___x_2255_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2255_, 0, v___x_2250_);
lean_ctor_set(v___x_2255_, 1, v___x_2254_);
v___x_2256_ = l_Std_Format_fill(v___x_2255_);
return v___x_2256_;
}
else
{
lean_object* v___x_2257_; 
lean_dec_ref(v_xs_2243_);
v___x_2257_ = ((lean_object*)(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__10));
return v___x_2257_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__11(size_t v_sz_2258_, size_t v_i_2259_, lean_object* v_bs_2260_){
_start:
{
uint8_t v___x_2261_; 
v___x_2261_ = lean_usize_dec_lt(v_i_2259_, v_sz_2258_);
if (v___x_2261_ == 0)
{
return v_bs_2260_;
}
else
{
lean_object* v_v_2262_; lean_object* v___x_2263_; lean_object* v_bs_x27_2264_; lean_object* v___x_2265_; size_t v___x_2266_; size_t v___x_2267_; lean_object* v___x_2268_; 
v_v_2262_ = lean_array_uget(v_bs_2260_, v_i_2259_);
v___x_2263_ = lean_unsigned_to_nat(0u);
v_bs_x27_2264_ = lean_array_uset(v_bs_2260_, v_i_2259_, v___x_2263_);
v___x_2265_ = l_Lean_mkFVar(v_v_2262_);
v___x_2266_ = ((size_t)1ULL);
v___x_2267_ = lean_usize_add(v_i_2259_, v___x_2266_);
v___x_2268_ = lean_array_uset(v_bs_x27_2264_, v_i_2259_, v___x_2265_);
v_i_2259_ = v___x_2267_;
v_bs_2260_ = v___x_2268_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__11___boxed(lean_object* v_sz_2270_, lean_object* v_i_2271_, lean_object* v_bs_2272_){
_start:
{
size_t v_sz_boxed_2273_; size_t v_i_boxed_2274_; lean_object* v_res_2275_; 
v_sz_boxed_2273_ = lean_unbox_usize(v_sz_2270_);
lean_dec(v_sz_2270_);
v_i_boxed_2274_ = lean_unbox_usize(v_i_2271_);
lean_dec(v_i_2271_);
v_res_2275_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__11(v_sz_boxed_2273_, v_i_boxed_2274_, v_bs_2272_);
return v_res_2275_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5_spec__5_spec__8(lean_object* v_a_2276_, lean_object* v_as_2277_, size_t v_i_2278_, size_t v_stop_2279_){
_start:
{
uint8_t v___x_2280_; 
v___x_2280_ = lean_usize_dec_eq(v_i_2278_, v_stop_2279_);
if (v___x_2280_ == 0)
{
lean_object* v___x_2281_; uint8_t v___x_2282_; 
v___x_2281_ = lean_array_uget_borrowed(v_as_2277_, v_i_2278_);
v___x_2282_ = l_Lean_instBEqFVarId_beq(v_a_2276_, v___x_2281_);
if (v___x_2282_ == 0)
{
size_t v___x_2283_; size_t v___x_2284_; 
v___x_2283_ = ((size_t)1ULL);
v___x_2284_ = lean_usize_add(v_i_2278_, v___x_2283_);
v_i_2278_ = v___x_2284_;
goto _start;
}
else
{
return v___x_2282_;
}
}
else
{
uint8_t v___x_2286_; 
v___x_2286_ = 0;
return v___x_2286_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5_spec__5_spec__8___boxed(lean_object* v_a_2287_, lean_object* v_as_2288_, lean_object* v_i_2289_, lean_object* v_stop_2290_){
_start:
{
size_t v_i_boxed_2291_; size_t v_stop_boxed_2292_; uint8_t v_res_2293_; lean_object* v_r_2294_; 
v_i_boxed_2291_ = lean_unbox_usize(v_i_2289_);
lean_dec(v_i_2289_);
v_stop_boxed_2292_ = lean_unbox_usize(v_stop_2290_);
lean_dec(v_stop_2290_);
v_res_2293_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5_spec__5_spec__8(v_a_2287_, v_as_2288_, v_i_boxed_2291_, v_stop_boxed_2292_);
lean_dec_ref(v_as_2288_);
lean_dec(v_a_2287_);
v_r_2294_ = lean_box(v_res_2293_);
return v_r_2294_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5_spec__5(lean_object* v_as_2295_, lean_object* v_a_2296_){
_start:
{
lean_object* v___x_2297_; lean_object* v___x_2298_; uint8_t v___x_2299_; 
v___x_2297_ = lean_unsigned_to_nat(0u);
v___x_2298_ = lean_array_get_size(v_as_2295_);
v___x_2299_ = lean_nat_dec_lt(v___x_2297_, v___x_2298_);
if (v___x_2299_ == 0)
{
return v___x_2299_;
}
else
{
if (v___x_2299_ == 0)
{
return v___x_2299_;
}
else
{
size_t v___x_2300_; size_t v___x_2301_; uint8_t v___x_2302_; 
v___x_2300_ = ((size_t)0ULL);
v___x_2301_ = lean_usize_of_nat(v___x_2298_);
v___x_2302_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5_spec__5_spec__8(v_a_2296_, v_as_2295_, v___x_2300_, v___x_2301_);
return v___x_2302_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5_spec__5___boxed(lean_object* v_as_2303_, lean_object* v_a_2304_){
_start:
{
uint8_t v_res_2305_; lean_object* v_r_2306_; 
v_res_2305_ = l_Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5_spec__5(v_as_2303_, v_a_2304_);
lean_dec(v_a_2304_);
lean_dec_ref(v_as_2303_);
v_r_2306_ = lean_box(v_res_2305_);
return v_r_2306_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5_spec__7(lean_object* v_fvarIds_2307_, lean_object* v_as_2308_, size_t v_i_2309_, size_t v_stop_2310_, lean_object* v_b_2311_){
_start:
{
lean_object* v___y_2313_; uint8_t v___x_2317_; 
v___x_2317_ = lean_usize_dec_eq(v_i_2309_, v_stop_2310_);
if (v___x_2317_ == 0)
{
lean_object* v___x_2318_; lean_object* v_fvar_2319_; lean_object* v___x_2320_; uint8_t v___x_2321_; 
v___x_2318_ = lean_array_uget_borrowed(v_as_2308_, v_i_2309_);
v_fvar_2319_ = lean_ctor_get(v___x_2318_, 1);
v___x_2320_ = l_Lean_Expr_fvarId_x21(v_fvar_2319_);
v___x_2321_ = l_Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5_spec__5(v_fvarIds_2307_, v___x_2320_);
lean_dec(v___x_2320_);
if (v___x_2321_ == 0)
{
lean_object* v___x_2322_; 
lean_inc(v___x_2318_);
v___x_2322_ = lean_array_push(v_b_2311_, v___x_2318_);
v___y_2313_ = v___x_2322_;
goto v___jp_2312_;
}
else
{
v___y_2313_ = v_b_2311_;
goto v___jp_2312_;
}
}
else
{
return v_b_2311_;
}
v___jp_2312_:
{
size_t v___x_2314_; size_t v___x_2315_; 
v___x_2314_ = ((size_t)1ULL);
v___x_2315_ = lean_usize_add(v_i_2309_, v___x_2314_);
v_i_2309_ = v___x_2315_;
v_b_2311_ = v___y_2313_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5_spec__7___boxed(lean_object* v_fvarIds_2323_, lean_object* v_as_2324_, lean_object* v_i_2325_, lean_object* v_stop_2326_, lean_object* v_b_2327_){
_start:
{
size_t v_i_boxed_2328_; size_t v_stop_boxed_2329_; lean_object* v_res_2330_; 
v_i_boxed_2328_ = lean_unbox_usize(v_i_2325_);
lean_dec(v_i_2325_);
v_stop_boxed_2329_ = lean_unbox_usize(v_stop_2326_);
lean_dec(v_stop_2326_);
v_res_2330_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5_spec__7(v_fvarIds_2323_, v_as_2324_, v_i_boxed_2328_, v_stop_boxed_2329_, v_b_2327_);
lean_dec_ref(v_as_2324_);
lean_dec_ref(v_fvarIds_2323_);
return v_res_2330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5_spec__6___redArg___lam__0(lean_object* v_x_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_){
_start:
{
lean_object* v___x_2338_; 
v___x_2338_ = lean_apply_6(v_x_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_, lean_box(0));
return v___x_2338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5_spec__6___redArg___lam__0___boxed(lean_object* v_x_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_){
_start:
{
lean_object* v_res_2346_; 
v_res_2346_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5_spec__6___redArg___lam__0(v_x_2339_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_);
return v_res_2346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5_spec__6___redArg(lean_object* v_lctx_2347_, lean_object* v_localInsts_2348_, lean_object* v_x_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_){
_start:
{
lean_object* v___f_2356_; lean_object* v___x_2357_; 
v___f_2356_ = lean_alloc_closure((void*)(l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5_spec__6___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2356_, 0, v_x_2349_);
lean_closure_set(v___f_2356_, 1, v___y_2350_);
v___x_2357_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_2347_, v_localInsts_2348_, v___f_2356_, v___y_2351_, v___y_2352_, v___y_2353_, v___y_2354_);
if (lean_obj_tag(v___x_2357_) == 0)
{
return v___x_2357_;
}
else
{
lean_object* v_a_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2365_; 
v_a_2358_ = lean_ctor_get(v___x_2357_, 0);
v_isSharedCheck_2365_ = !lean_is_exclusive(v___x_2357_);
if (v_isSharedCheck_2365_ == 0)
{
v___x_2360_ = v___x_2357_;
v_isShared_2361_ = v_isSharedCheck_2365_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_a_2358_);
lean_dec(v___x_2357_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2365_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
lean_object* v___x_2363_; 
if (v_isShared_2361_ == 0)
{
v___x_2363_ = v___x_2360_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v_a_2358_);
v___x_2363_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
return v___x_2363_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5_spec__6___redArg___boxed(lean_object* v_lctx_2366_, lean_object* v_localInsts_2367_, lean_object* v_x_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_){
_start:
{
lean_object* v_res_2375_; 
v_res_2375_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5_spec__6___redArg(v_lctx_2366_, v_localInsts_2367_, v_x_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_);
return v_res_2375_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5_spec__8(lean_object* v_as_2376_, size_t v_i_2377_, size_t v_stop_2378_, lean_object* v_b_2379_){
_start:
{
uint8_t v___x_2380_; 
v___x_2380_ = lean_usize_dec_eq(v_i_2377_, v_stop_2378_);
if (v___x_2380_ == 0)
{
lean_object* v___x_2381_; lean_object* v___x_2382_; size_t v___x_2383_; size_t v___x_2384_; 
v___x_2381_ = lean_array_uget_borrowed(v_as_2376_, v_i_2377_);
lean_inc(v___x_2381_);
v___x_2382_ = lean_local_ctx_erase(v_b_2379_, v___x_2381_);
v___x_2383_ = ((size_t)1ULL);
v___x_2384_ = lean_usize_add(v_i_2377_, v___x_2383_);
v_i_2377_ = v___x_2384_;
v_b_2379_ = v___x_2382_;
goto _start;
}
else
{
return v_b_2379_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5_spec__8___boxed(lean_object* v_as_2386_, lean_object* v_i_2387_, lean_object* v_stop_2388_, lean_object* v_b_2389_){
_start:
{
size_t v_i_boxed_2390_; size_t v_stop_boxed_2391_; lean_object* v_res_2392_; 
v_i_boxed_2390_ = lean_unbox_usize(v_i_2387_);
lean_dec(v_i_2387_);
v_stop_boxed_2391_ = lean_unbox_usize(v_stop_2388_);
lean_dec(v_stop_2388_);
v_res_2392_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5_spec__8(v_as_2386_, v_i_boxed_2390_, v_stop_boxed_2391_, v_b_2389_);
lean_dec_ref(v_as_2386_);
return v_res_2392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg(lean_object* v_fvarIds_2395_, lean_object* v_k_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_){
_start:
{
lean_object* v_lctx_2403_; lean_object* v___x_2404_; 
v_lctx_2403_ = lean_ctor_get(v___y_2398_, 2);
v___x_2404_ = l_Lean_Meta_getLocalInstances___redArg(v___y_2398_);
if (lean_obj_tag(v___x_2404_) == 0)
{
lean_object* v_a_2405_; lean_object* v___x_2406_; lean_object* v___y_2408_; lean_object* v___x_2423_; uint8_t v___x_2424_; 
v_a_2405_ = lean_ctor_get(v___x_2404_, 0);
lean_inc(v_a_2405_);
lean_dec_ref(v___x_2404_);
v___x_2406_ = lean_unsigned_to_nat(0u);
v___x_2423_ = lean_array_get_size(v_fvarIds_2395_);
v___x_2424_ = lean_nat_dec_lt(v___x_2406_, v___x_2423_);
if (v___x_2424_ == 0)
{
lean_inc_ref(v_lctx_2403_);
v___y_2408_ = v_lctx_2403_;
goto v___jp_2407_;
}
else
{
uint8_t v___x_2425_; 
v___x_2425_ = lean_nat_dec_le(v___x_2423_, v___x_2423_);
if (v___x_2425_ == 0)
{
if (v___x_2424_ == 0)
{
lean_inc_ref(v_lctx_2403_);
v___y_2408_ = v_lctx_2403_;
goto v___jp_2407_;
}
else
{
size_t v___x_2426_; size_t v___x_2427_; lean_object* v___x_2428_; 
v___x_2426_ = ((size_t)0ULL);
v___x_2427_ = lean_usize_of_nat(v___x_2423_);
lean_inc_ref(v_lctx_2403_);
v___x_2428_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5_spec__8(v_fvarIds_2395_, v___x_2426_, v___x_2427_, v_lctx_2403_);
v___y_2408_ = v___x_2428_;
goto v___jp_2407_;
}
}
else
{
size_t v___x_2429_; size_t v___x_2430_; lean_object* v___x_2431_; 
v___x_2429_ = ((size_t)0ULL);
v___x_2430_ = lean_usize_of_nat(v___x_2423_);
lean_inc_ref(v_lctx_2403_);
v___x_2431_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5_spec__8(v_fvarIds_2395_, v___x_2429_, v___x_2430_, v_lctx_2403_);
v___y_2408_ = v___x_2431_;
goto v___jp_2407_;
}
}
v___jp_2407_:
{
lean_object* v___x_2409_; lean_object* v___x_2410_; uint8_t v___x_2411_; 
v___x_2409_ = lean_array_get_size(v_a_2405_);
v___x_2410_ = ((lean_object*)(l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__0));
v___x_2411_ = lean_nat_dec_lt(v___x_2406_, v___x_2409_);
if (v___x_2411_ == 0)
{
lean_object* v___x_2412_; 
lean_dec(v_a_2405_);
v___x_2412_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5_spec__6___redArg(v___y_2408_, v___x_2410_, v_k_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_);
return v___x_2412_;
}
else
{
uint8_t v___x_2413_; 
v___x_2413_ = lean_nat_dec_le(v___x_2409_, v___x_2409_);
if (v___x_2413_ == 0)
{
if (v___x_2411_ == 0)
{
lean_object* v___x_2414_; 
lean_dec(v_a_2405_);
v___x_2414_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5_spec__6___redArg(v___y_2408_, v___x_2410_, v_k_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_);
return v___x_2414_;
}
else
{
size_t v___x_2415_; size_t v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; 
v___x_2415_ = ((size_t)0ULL);
v___x_2416_ = lean_usize_of_nat(v___x_2409_);
v___x_2417_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5_spec__7(v_fvarIds_2395_, v_a_2405_, v___x_2415_, v___x_2416_, v___x_2410_);
lean_dec(v_a_2405_);
v___x_2418_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5_spec__6___redArg(v___y_2408_, v___x_2417_, v_k_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_);
return v___x_2418_;
}
}
else
{
size_t v___x_2419_; size_t v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; 
v___x_2419_ = ((size_t)0ULL);
v___x_2420_ = lean_usize_of_nat(v___x_2409_);
v___x_2421_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5_spec__7(v_fvarIds_2395_, v_a_2405_, v___x_2419_, v___x_2420_, v___x_2410_);
lean_dec(v_a_2405_);
v___x_2422_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5_spec__6___redArg(v___y_2408_, v___x_2421_, v_k_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_);
return v___x_2422_;
}
}
}
}
else
{
lean_object* v_a_2432_; lean_object* v___x_2434_; uint8_t v_isShared_2435_; uint8_t v_isSharedCheck_2439_; 
lean_dec(v___y_2401_);
lean_dec_ref(v___y_2400_);
lean_dec(v___y_2399_);
lean_dec_ref(v___y_2398_);
lean_dec(v___y_2397_);
lean_dec_ref(v_k_2396_);
v_a_2432_ = lean_ctor_get(v___x_2404_, 0);
v_isSharedCheck_2439_ = !lean_is_exclusive(v___x_2404_);
if (v_isSharedCheck_2439_ == 0)
{
v___x_2434_ = v___x_2404_;
v_isShared_2435_ = v_isSharedCheck_2439_;
goto v_resetjp_2433_;
}
else
{
lean_inc(v_a_2432_);
lean_dec(v___x_2404_);
v___x_2434_ = lean_box(0);
v_isShared_2435_ = v_isSharedCheck_2439_;
goto v_resetjp_2433_;
}
v_resetjp_2433_:
{
lean_object* v___x_2437_; 
if (v_isShared_2435_ == 0)
{
v___x_2437_ = v___x_2434_;
goto v_reusejp_2436_;
}
else
{
lean_object* v_reuseFailAlloc_2438_; 
v_reuseFailAlloc_2438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2438_, 0, v_a_2432_);
v___x_2437_ = v_reuseFailAlloc_2438_;
goto v_reusejp_2436_;
}
v_reusejp_2436_:
{
return v___x_2437_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___boxed(lean_object* v_fvarIds_2440_, lean_object* v_k_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_){
_start:
{
lean_object* v_res_2448_; 
v_res_2448_ = l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg(v_fvarIds_2440_, v_k_2441_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_);
lean_dec_ref(v_fvarIds_2440_);
return v_res_2448_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg(lean_object* v_fst_2449_, lean_object* v_as_2450_, lean_object* v_i_2451_, lean_object* v_j_2452_, lean_object* v_bs_2453_){
_start:
{
lean_object* v_zero_2454_; uint8_t v_isZero_2455_; 
v_zero_2454_ = lean_unsigned_to_nat(0u);
v_isZero_2455_ = lean_nat_dec_eq(v_i_2451_, v_zero_2454_);
if (v_isZero_2455_ == 1)
{
lean_dec(v_j_2452_);
lean_dec(v_i_2451_);
return v_bs_2453_;
}
else
{
lean_object* v___x_2456_; lean_object* v_fnName_2457_; lean_object* v_recArgPos_2458_; lean_object* v_indicesPos_2459_; lean_object* v_indGroupInst_2460_; lean_object* v_indIdx_2461_; lean_object* v___x_2463_; uint8_t v_isShared_2464_; uint8_t v_isSharedCheck_2476_; 
v___x_2456_ = lean_array_fget(v_as_2450_, v_j_2452_);
v_fnName_2457_ = lean_ctor_get(v___x_2456_, 0);
v_recArgPos_2458_ = lean_ctor_get(v___x_2456_, 2);
v_indicesPos_2459_ = lean_ctor_get(v___x_2456_, 3);
v_indGroupInst_2460_ = lean_ctor_get(v___x_2456_, 4);
v_indIdx_2461_ = lean_ctor_get(v___x_2456_, 5);
v_isSharedCheck_2476_ = !lean_is_exclusive(v___x_2456_);
if (v_isSharedCheck_2476_ == 0)
{
lean_object* v_unused_2477_; 
v_unused_2477_ = lean_ctor_get(v___x_2456_, 1);
lean_dec(v_unused_2477_);
v___x_2463_ = v___x_2456_;
v_isShared_2464_ = v_isSharedCheck_2476_;
goto v_resetjp_2462_;
}
else
{
lean_inc(v_indIdx_2461_);
lean_inc(v_indGroupInst_2460_);
lean_inc(v_indicesPos_2459_);
lean_inc(v_recArgPos_2458_);
lean_inc(v_fnName_2457_);
lean_dec(v___x_2456_);
v___x_2463_ = lean_box(0);
v_isShared_2464_ = v_isSharedCheck_2476_;
goto v_resetjp_2462_;
}
v_resetjp_2462_:
{
lean_object* v_perms_2465_; lean_object* v___x_2466_; lean_object* v_one_2467_; lean_object* v_n_2468_; lean_object* v___x_2469_; lean_object* v___x_2471_; 
v_perms_2465_ = lean_ctor_get(v_fst_2449_, 1);
v___x_2466_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9___redArg___closed__0, &l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9___redArg___closed__0_once, _init_l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9___redArg___closed__0);
v_one_2467_ = lean_unsigned_to_nat(1u);
v_n_2468_ = lean_nat_sub(v_i_2451_, v_one_2467_);
lean_dec(v_i_2451_);
v___x_2469_ = lean_array_get_borrowed(v___x_2466_, v_perms_2465_, v_j_2452_);
lean_inc(v___x_2469_);
if (v_isShared_2464_ == 0)
{
lean_ctor_set(v___x_2463_, 1, v___x_2469_);
v___x_2471_ = v___x_2463_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v_fnName_2457_);
lean_ctor_set(v_reuseFailAlloc_2475_, 1, v___x_2469_);
lean_ctor_set(v_reuseFailAlloc_2475_, 2, v_recArgPos_2458_);
lean_ctor_set(v_reuseFailAlloc_2475_, 3, v_indicesPos_2459_);
lean_ctor_set(v_reuseFailAlloc_2475_, 4, v_indGroupInst_2460_);
lean_ctor_set(v_reuseFailAlloc_2475_, 5, v_indIdx_2461_);
v___x_2471_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
lean_object* v___x_2472_; lean_object* v___x_2473_; 
v___x_2472_ = lean_nat_add(v_j_2452_, v_one_2467_);
lean_dec(v_j_2452_);
v___x_2473_ = lean_array_push(v_bs_2453_, v___x_2471_);
v_i_2451_ = v_n_2468_;
v_j_2452_ = v___x_2472_;
v_bs_2453_ = v___x_2473_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg___boxed(lean_object* v_fst_2478_, lean_object* v_as_2479_, lean_object* v_i_2480_, lean_object* v_j_2481_, lean_object* v_bs_2482_){
_start:
{
lean_object* v_res_2483_; 
v_res_2483_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg(v_fst_2478_, v_as_2479_, v_i_2480_, v_j_2481_, v_bs_2482_);
lean_dec_ref(v_as_2479_);
lean_dec_ref(v_fst_2478_);
return v_res_2483_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__2(size_t v_sz_2484_, size_t v_i_2485_, lean_object* v_bs_2486_){
_start:
{
uint8_t v___x_2487_; 
v___x_2487_ = lean_usize_dec_lt(v_i_2485_, v_sz_2484_);
if (v___x_2487_ == 0)
{
return v_bs_2486_;
}
else
{
lean_object* v_v_2488_; lean_object* v_recArgPos_2489_; lean_object* v___x_2490_; lean_object* v_bs_x27_2491_; size_t v___x_2492_; size_t v___x_2493_; lean_object* v___x_2494_; 
v_v_2488_ = lean_array_uget_borrowed(v_bs_2486_, v_i_2485_);
v_recArgPos_2489_ = lean_ctor_get(v_v_2488_, 2);
lean_inc(v_recArgPos_2489_);
v___x_2490_ = lean_unsigned_to_nat(0u);
v_bs_x27_2491_ = lean_array_uset(v_bs_2486_, v_i_2485_, v___x_2490_);
v___x_2492_ = ((size_t)1ULL);
v___x_2493_ = lean_usize_add(v_i_2485_, v___x_2492_);
v___x_2494_ = lean_array_uset(v_bs_x27_2491_, v_i_2485_, v_recArgPos_2489_);
v_i_2485_ = v___x_2493_;
v_bs_2486_ = v___x_2494_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__2___boxed(lean_object* v_sz_2496_, lean_object* v_i_2497_, lean_object* v_bs_2498_){
_start:
{
size_t v_sz_boxed_2499_; size_t v_i_boxed_2500_; lean_object* v_res_2501_; 
v_sz_boxed_2499_ = lean_unbox_usize(v_sz_2496_);
lean_dec(v_sz_2496_);
v_i_boxed_2500_ = lean_unbox_usize(v_i_2497_);
lean_dec(v_i_2497_);
v_res_2501_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__2(v_sz_boxed_2499_, v_i_boxed_2500_, v_bs_2498_);
return v_res_2501_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7___closed__1(void){
_start:
{
lean_object* v___x_2503_; lean_object* v___x_2504_; 
v___x_2503_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7___closed__0));
v___x_2504_ = l_Lean_stringToMessageData(v___x_2503_);
return v___x_2504_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7___closed__3(void){
_start:
{
lean_object* v___x_2506_; lean_object* v___x_2507_; 
v___x_2506_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7___closed__2));
v___x_2507_ = l_Lean_stringToMessageData(v___x_2506_);
return v___x_2507_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7___closed__5(void){
_start:
{
lean_object* v___x_2509_; lean_object* v___x_2510_; 
v___x_2509_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7___closed__4));
v___x_2510_ = l_Lean_stringToMessageData(v___x_2509_);
return v___x_2510_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7(lean_object* v_a_2511_, lean_object* v_as_2512_, size_t v_sz_2513_, size_t v_i_2514_, lean_object* v_b_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_){
_start:
{
lean_object* v_a_2523_; uint8_t v___x_2527_; 
v___x_2527_ = lean_usize_dec_lt(v_i_2514_, v_sz_2513_);
if (v___x_2527_ == 0)
{
lean_object* v___x_2528_; 
lean_dec_ref(v_a_2511_);
v___x_2528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2528_, 0, v_b_2515_);
return v___x_2528_;
}
else
{
lean_object* v_a_2529_; lean_object* v___x_2530_; 
v_a_2529_ = lean_array_uget_borrowed(v_as_2512_, v_i_2514_);
lean_inc(v_a_2529_);
lean_inc_ref(v_a_2511_);
v___x_2530_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___redArg(v_a_2511_, v_a_2529_, v___y_2518_);
if (lean_obj_tag(v___x_2530_) == 0)
{
lean_object* v_a_2531_; lean_object* v___x_2532_; uint8_t v___x_2533_; 
v_a_2531_ = lean_ctor_get(v___x_2530_, 0);
lean_inc(v_a_2531_);
lean_dec_ref(v___x_2530_);
v___x_2532_ = lean_box(0);
v___x_2533_ = lean_unbox(v_a_2531_);
lean_dec(v_a_2531_);
if (v___x_2533_ == 0)
{
v_a_2523_ = v___x_2532_;
goto v___jp_2522_;
}
else
{
uint8_t v___x_2534_; 
v___x_2534_ = l_Lean_Expr_isFVarOf(v_a_2511_, v_a_2529_);
if (v___x_2534_ == 0)
{
lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; 
v___x_2535_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7___closed__1);
lean_inc_ref(v_a_2511_);
v___x_2536_ = l_Lean_indentExpr(v_a_2511_);
v___x_2537_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2537_, 0, v___x_2535_);
lean_ctor_set(v___x_2537_, 1, v___x_2536_);
v___x_2538_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7___closed__3);
v___x_2539_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2539_, 0, v___x_2537_);
lean_ctor_set(v___x_2539_, 1, v___x_2538_);
lean_inc(v_a_2529_);
v___x_2540_ = l_Lean_mkFVar(v_a_2529_);
v___x_2541_ = l_Lean_indentExpr(v___x_2540_);
v___x_2542_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2542_, 0, v___x_2539_);
lean_ctor_set(v___x_2542_, 1, v___x_2541_);
v___x_2543_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7___closed__5);
v___x_2544_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2544_, 0, v___x_2542_);
lean_ctor_set(v___x_2544_, 1, v___x_2543_);
v___x_2545_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3_spec__3___redArg(v___x_2544_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_);
if (lean_obj_tag(v___x_2545_) == 0)
{
lean_dec_ref(v___x_2545_);
v_a_2523_ = v___x_2532_;
goto v___jp_2522_;
}
else
{
lean_dec_ref(v_a_2511_);
return v___x_2545_;
}
}
else
{
lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; 
v___x_2546_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7___closed__1);
lean_inc_ref(v_a_2511_);
v___x_2547_ = l_Lean_indentExpr(v_a_2511_);
v___x_2548_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2548_, 0, v___x_2546_);
lean_ctor_set(v___x_2548_, 1, v___x_2547_);
v___x_2549_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7___closed__5);
v___x_2550_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2550_, 0, v___x_2548_);
lean_ctor_set(v___x_2550_, 1, v___x_2549_);
v___x_2551_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3_spec__3___redArg(v___x_2550_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_);
if (lean_obj_tag(v___x_2551_) == 0)
{
lean_dec_ref(v___x_2551_);
v_a_2523_ = v___x_2532_;
goto v___jp_2522_;
}
else
{
lean_dec_ref(v_a_2511_);
return v___x_2551_;
}
}
}
}
else
{
lean_object* v_a_2552_; lean_object* v___x_2554_; uint8_t v_isShared_2555_; uint8_t v_isSharedCheck_2559_; 
lean_dec_ref(v_a_2511_);
v_a_2552_ = lean_ctor_get(v___x_2530_, 0);
v_isSharedCheck_2559_ = !lean_is_exclusive(v___x_2530_);
if (v_isSharedCheck_2559_ == 0)
{
v___x_2554_ = v___x_2530_;
v_isShared_2555_ = v_isSharedCheck_2559_;
goto v_resetjp_2553_;
}
else
{
lean_inc(v_a_2552_);
lean_dec(v___x_2530_);
v___x_2554_ = lean_box(0);
v_isShared_2555_ = v_isSharedCheck_2559_;
goto v_resetjp_2553_;
}
v_resetjp_2553_:
{
lean_object* v___x_2557_; 
if (v_isShared_2555_ == 0)
{
v___x_2557_ = v___x_2554_;
goto v_reusejp_2556_;
}
else
{
lean_object* v_reuseFailAlloc_2558_; 
v_reuseFailAlloc_2558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2558_, 0, v_a_2552_);
v___x_2557_ = v_reuseFailAlloc_2558_;
goto v_reusejp_2556_;
}
v_reusejp_2556_:
{
return v___x_2557_;
}
}
}
}
v___jp_2522_:
{
size_t v___x_2524_; size_t v___x_2525_; 
v___x_2524_ = ((size_t)1ULL);
v___x_2525_ = lean_usize_add(v_i_2514_, v___x_2524_);
v_i_2514_ = v___x_2525_;
v_b_2515_ = v_a_2523_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7___boxed(lean_object* v_a_2560_, lean_object* v_as_2561_, lean_object* v_sz_2562_, lean_object* v_i_2563_, lean_object* v_b_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_){
_start:
{
size_t v_sz_boxed_2571_; size_t v_i_boxed_2572_; lean_object* v_res_2573_; 
v_sz_boxed_2571_ = lean_unbox_usize(v_sz_2562_);
lean_dec(v_sz_2562_);
v_i_boxed_2572_ = lean_unbox_usize(v_i_2563_);
lean_dec(v_i_2563_);
v_res_2573_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7(v_a_2560_, v_as_2561_, v_sz_boxed_2571_, v_i_boxed_2572_, v_b_2564_, v___y_2565_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_);
lean_dec(v___y_2569_);
lean_dec_ref(v___y_2568_);
lean_dec(v___y_2567_);
lean_dec_ref(v___y_2566_);
lean_dec(v___y_2565_);
lean_dec_ref(v_as_2561_);
return v_res_2573_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8(lean_object* v_snd_2574_, lean_object* v_as_2575_, size_t v_sz_2576_, size_t v_i_2577_, lean_object* v_b_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_){
_start:
{
uint8_t v___x_2585_; 
v___x_2585_ = lean_usize_dec_lt(v_i_2577_, v_sz_2576_);
if (v___x_2585_ == 0)
{
lean_object* v___x_2586_; 
v___x_2586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2586_, 0, v_b_2578_);
return v___x_2586_;
}
else
{
lean_object* v___x_2587_; lean_object* v_a_2588_; size_t v_sz_2589_; size_t v___x_2590_; lean_object* v___x_2591_; 
v___x_2587_ = lean_box(0);
v_a_2588_ = lean_array_uget_borrowed(v_as_2575_, v_i_2577_);
v_sz_2589_ = lean_array_size(v_snd_2574_);
v___x_2590_ = ((size_t)0ULL);
lean_inc(v_a_2588_);
v___x_2591_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7(v_a_2588_, v_snd_2574_, v_sz_2589_, v___x_2590_, v___x_2587_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_);
if (lean_obj_tag(v___x_2591_) == 0)
{
size_t v___x_2592_; size_t v___x_2593_; 
lean_dec_ref(v___x_2591_);
v___x_2592_ = ((size_t)1ULL);
v___x_2593_ = lean_usize_add(v_i_2577_, v___x_2592_);
v_i_2577_ = v___x_2593_;
v_b_2578_ = v___x_2587_;
goto _start;
}
else
{
return v___x_2591_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8___boxed(lean_object* v_snd_2595_, lean_object* v_as_2596_, lean_object* v_sz_2597_, lean_object* v_i_2598_, lean_object* v_b_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_){
_start:
{
size_t v_sz_boxed_2606_; size_t v_i_boxed_2607_; lean_object* v_res_2608_; 
v_sz_boxed_2606_ = lean_unbox_usize(v_sz_2597_);
lean_dec(v_sz_2597_);
v_i_boxed_2607_ = lean_unbox_usize(v_i_2598_);
lean_dec(v_i_2598_);
v_res_2608_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8(v_snd_2595_, v_as_2596_, v_sz_boxed_2606_, v_i_boxed_2607_, v_b_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_);
lean_dec(v___y_2604_);
lean_dec_ref(v___y_2603_);
lean_dec(v___y_2602_);
lean_dec_ref(v___y_2601_);
lean_dec(v___y_2600_);
lean_dec_ref(v_as_2596_);
lean_dec_ref(v_snd_2595_);
return v_res_2608_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9(lean_object* v_snd_2609_, lean_object* v_as_2610_, size_t v_sz_2611_, size_t v_i_2612_, lean_object* v_b_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_){
_start:
{
uint8_t v___x_2620_; 
v___x_2620_ = lean_usize_dec_lt(v_i_2612_, v_sz_2611_);
if (v___x_2620_ == 0)
{
lean_object* v___x_2621_; 
v___x_2621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2621_, 0, v_b_2613_);
return v___x_2621_;
}
else
{
lean_object* v_a_2622_; lean_object* v_indGroupInst_2623_; lean_object* v_params_2624_; lean_object* v___x_2625_; size_t v_sz_2626_; size_t v___x_2627_; lean_object* v___x_2628_; 
v_a_2622_ = lean_array_uget_borrowed(v_as_2610_, v_i_2612_);
v_indGroupInst_2623_ = lean_ctor_get(v_a_2622_, 4);
v_params_2624_ = lean_ctor_get(v_indGroupInst_2623_, 2);
v___x_2625_ = lean_box(0);
v_sz_2626_ = lean_array_size(v_params_2624_);
v___x_2627_ = ((size_t)0ULL);
v___x_2628_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8(v_snd_2609_, v_params_2624_, v_sz_2626_, v___x_2627_, v___x_2625_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_);
if (lean_obj_tag(v___x_2628_) == 0)
{
size_t v___x_2629_; size_t v___x_2630_; 
lean_dec_ref(v___x_2628_);
v___x_2629_ = ((size_t)1ULL);
v___x_2630_ = lean_usize_add(v_i_2612_, v___x_2629_);
v_i_2612_ = v___x_2630_;
v_b_2613_ = v___x_2625_;
goto _start;
}
else
{
return v___x_2628_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___boxed(lean_object* v_snd_2632_, lean_object* v_as_2633_, lean_object* v_sz_2634_, lean_object* v_i_2635_, lean_object* v_b_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_){
_start:
{
size_t v_sz_boxed_2643_; size_t v_i_boxed_2644_; lean_object* v_res_2645_; 
v_sz_boxed_2643_ = lean_unbox_usize(v_sz_2634_);
lean_dec(v_sz_2634_);
v_i_boxed_2644_ = lean_unbox_usize(v_i_2635_);
lean_dec(v_i_2635_);
v_res_2645_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9(v_snd_2632_, v_as_2633_, v_sz_boxed_2643_, v_i_boxed_2644_, v_b_2636_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_);
lean_dec(v___y_2641_);
lean_dec_ref(v___y_2640_);
lean_dec(v___y_2639_);
lean_dec_ref(v___y_2638_);
lean_dec(v___y_2637_);
lean_dec_ref(v_as_2633_);
lean_dec_ref(v_snd_2632_);
return v_res_2645_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2647_; lean_object* v___x_2648_; 
v___x_2647_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___closed__0));
v___x_2648_ = l_Lean_stringToMessageData(v___x_2647_);
return v___x_2648_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2650_; lean_object* v___x_2651_; 
v___x_2650_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___closed__2));
v___x_2651_ = l_Lean_stringToMessageData(v___x_2650_);
return v___x_2651_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___closed__5(void){
_start:
{
lean_object* v___x_2653_; lean_object* v___x_2654_; 
v___x_2653_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___closed__4));
v___x_2654_ = l_Lean_stringToMessageData(v___x_2653_);
return v___x_2654_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___closed__7(void){
_start:
{
lean_object* v___x_2656_; lean_object* v___x_2657_; 
v___x_2656_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___closed__6));
v___x_2657_ = l_Lean_stringToMessageData(v___x_2656_);
return v___x_2657_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___closed__9(void){
_start:
{
lean_object* v___x_2659_; lean_object* v___x_2660_; 
v___x_2659_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___closed__8));
v___x_2660_ = l_Lean_stringToMessageData(v___x_2659_);
return v___x_2660_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1(size_t v___x_2661_, lean_object* v_a_2662_, lean_object* v_xs_2663_, lean_object* v___x_2664_, lean_object* v_a_2665_, lean_object* v_recArgInfos_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_){
_start:
{
lean_object* v___y_2674_; lean_object* v___y_2675_; lean_object* v___y_2676_; lean_object* v___y_2677_; lean_object* v___y_2678_; lean_object* v___y_2679_; lean_object* v___y_2680_; lean_object* v___y_2681_; lean_object* v___x_2694_; lean_object* v___y_2696_; lean_object* v___y_2697_; lean_object* v___y_2698_; lean_object* v___y_2699_; lean_object* v___y_2700_; lean_object* v___y_2701_; lean_object* v___y_2702_; lean_object* v___y_2703_; lean_object* v___x_2720_; lean_object* v_a_2721_; size_t v_sz_2722_; lean_object* v___x_2723_; lean_object* v___y_2725_; lean_object* v___y_2726_; lean_object* v___y_2727_; lean_object* v___y_2728_; lean_object* v___y_2729_; uint8_t v___x_2788_; 
v___x_2694_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__3));
v___x_2720_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___redArg(v___x_2694_, v___y_2670_);
v_a_2721_ = lean_ctor_get(v___x_2720_, 0);
lean_inc(v_a_2721_);
lean_dec_ref(v___x_2720_);
v_sz_2722_ = lean_array_size(v_recArgInfos_2666_);
lean_inc_ref(v_recArgInfos_2666_);
v___x_2723_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__2(v_sz_2722_, v___x_2661_, v_recArgInfos_2666_);
v___x_2788_ = lean_unbox(v_a_2721_);
lean_dec(v_a_2721_);
if (v___x_2788_ == 0)
{
v___y_2725_ = v___y_2667_;
v___y_2726_ = v___y_2668_;
v___y_2727_ = v___y_2669_;
v___y_2728_ = v___y_2670_;
v___y_2729_ = v___y_2671_;
goto v___jp_2724_;
}
else
{
lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; 
v___x_2789_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___closed__9, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___closed__9_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___closed__9);
lean_inc_ref(v___x_2723_);
v___x_2790_ = lean_array_to_list(v___x_2723_);
v___x_2791_ = lean_box(0);
v___x_2792_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__0(v___x_2790_, v___x_2791_);
v___x_2793_ = l_Lean_MessageData_ofList(v___x_2792_);
v___x_2794_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2794_, 0, v___x_2789_);
lean_ctor_set(v___x_2794_, 1, v___x_2793_);
v___x_2795_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v___x_2694_, v___x_2794_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_);
if (lean_obj_tag(v___x_2795_) == 0)
{
lean_dec_ref(v___x_2795_);
v___y_2725_ = v___y_2667_;
v___y_2726_ = v___y_2668_;
v___y_2727_ = v___y_2669_;
v___y_2728_ = v___y_2670_;
v___y_2729_ = v___y_2671_;
goto v___jp_2724_;
}
else
{
lean_object* v_a_2796_; lean_object* v___x_2798_; uint8_t v_isShared_2799_; uint8_t v_isSharedCheck_2803_; 
lean_dec_ref(v___x_2723_);
lean_dec(v___y_2671_);
lean_dec_ref(v___y_2670_);
lean_dec(v___y_2669_);
lean_dec_ref(v___y_2668_);
lean_dec(v___y_2667_);
lean_dec_ref(v_recArgInfos_2666_);
lean_dec_ref(v_a_2665_);
lean_dec(v___x_2664_);
lean_dec_ref(v_xs_2663_);
lean_dec_ref(v_a_2662_);
v_a_2796_ = lean_ctor_get(v___x_2795_, 0);
v_isSharedCheck_2803_ = !lean_is_exclusive(v___x_2795_);
if (v_isSharedCheck_2803_ == 0)
{
v___x_2798_ = v___x_2795_;
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
else
{
lean_inc(v_a_2796_);
lean_dec(v___x_2795_);
v___x_2798_ = lean_box(0);
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
v_resetjp_2797_:
{
lean_object* v___x_2801_; 
if (v_isShared_2799_ == 0)
{
v___x_2801_ = v___x_2798_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2802_; 
v_reuseFailAlloc_2802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2802_, 0, v_a_2796_);
v___x_2801_ = v_reuseFailAlloc_2802_;
goto v_reusejp_2800_;
}
v_reusejp_2800_:
{
return v___x_2801_;
}
}
}
}
v___jp_2673_:
{
lean_object* v___x_2682_; size_t v_sz_2683_; lean_object* v___x_2684_; 
v___x_2682_ = lean_box(0);
v_sz_2683_ = lean_array_size(v___y_2676_);
v___x_2684_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9(v___y_2675_, v___y_2676_, v_sz_2683_, v___x_2661_, v___x_2682_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_);
lean_dec_ref(v___y_2676_);
if (lean_obj_tag(v___x_2684_) == 0)
{
lean_object* v___x_2685_; 
lean_dec_ref(v___x_2684_);
v___x_2685_ = l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg(v___y_2675_, v___y_2674_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_);
lean_dec_ref(v___y_2675_);
return v___x_2685_;
}
else
{
lean_object* v_a_2686_; lean_object* v___x_2688_; uint8_t v_isShared_2689_; uint8_t v_isSharedCheck_2693_; 
lean_dec(v___y_2681_);
lean_dec_ref(v___y_2680_);
lean_dec(v___y_2679_);
lean_dec_ref(v___y_2678_);
lean_dec(v___y_2677_);
lean_dec_ref(v___y_2675_);
lean_dec_ref(v___y_2674_);
v_a_2686_ = lean_ctor_get(v___x_2684_, 0);
v_isSharedCheck_2693_ = !lean_is_exclusive(v___x_2684_);
if (v_isSharedCheck_2693_ == 0)
{
v___x_2688_ = v___x_2684_;
v_isShared_2689_ = v_isSharedCheck_2693_;
goto v_resetjp_2687_;
}
else
{
lean_inc(v_a_2686_);
lean_dec(v___x_2684_);
v___x_2688_ = lean_box(0);
v_isShared_2689_ = v_isSharedCheck_2693_;
goto v_resetjp_2687_;
}
v_resetjp_2687_:
{
lean_object* v___x_2691_; 
if (v_isShared_2689_ == 0)
{
v___x_2691_ = v___x_2688_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2692_; 
v_reuseFailAlloc_2692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2692_, 0, v_a_2686_);
v___x_2691_ = v_reuseFailAlloc_2692_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
return v___x_2691_;
}
}
}
}
v___jp_2695_:
{
lean_object* v___x_2704_; lean_object* v_a_2705_; uint8_t v___x_2706_; 
v___x_2704_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___redArg(v___x_2694_, v___y_2702_);
v_a_2705_ = lean_ctor_get(v___x_2704_, 0);
lean_inc(v_a_2705_);
lean_dec_ref(v___x_2704_);
v___x_2706_ = lean_unbox(v_a_2705_);
lean_dec(v_a_2705_);
if (v___x_2706_ == 0)
{
v___y_2674_ = v___y_2696_;
v___y_2675_ = v___y_2697_;
v___y_2676_ = v___y_2698_;
v___y_2677_ = v___y_2699_;
v___y_2678_ = v___y_2700_;
v___y_2679_ = v___y_2701_;
v___y_2680_ = v___y_2702_;
v___y_2681_ = v___y_2703_;
goto v___jp_2673_;
}
else
{
lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; 
v___x_2707_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___closed__1);
lean_inc_ref(v___y_2698_);
v___x_2708_ = l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10(v___y_2698_);
v___x_2709_ = l_Lean_MessageData_ofFormat(v___x_2708_);
v___x_2710_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2710_, 0, v___x_2707_);
lean_ctor_set(v___x_2710_, 1, v___x_2709_);
v___x_2711_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v___x_2694_, v___x_2710_, v___y_2700_, v___y_2701_, v___y_2702_, v___y_2703_);
if (lean_obj_tag(v___x_2711_) == 0)
{
lean_dec_ref(v___x_2711_);
v___y_2674_ = v___y_2696_;
v___y_2675_ = v___y_2697_;
v___y_2676_ = v___y_2698_;
v___y_2677_ = v___y_2699_;
v___y_2678_ = v___y_2700_;
v___y_2679_ = v___y_2701_;
v___y_2680_ = v___y_2702_;
v___y_2681_ = v___y_2703_;
goto v___jp_2673_;
}
else
{
lean_object* v_a_2712_; lean_object* v___x_2714_; uint8_t v_isShared_2715_; uint8_t v_isSharedCheck_2719_; 
lean_dec(v___y_2703_);
lean_dec_ref(v___y_2702_);
lean_dec(v___y_2701_);
lean_dec_ref(v___y_2700_);
lean_dec(v___y_2699_);
lean_dec_ref(v___y_2698_);
lean_dec_ref(v___y_2697_);
lean_dec_ref(v___y_2696_);
v_a_2712_ = lean_ctor_get(v___x_2711_, 0);
v_isSharedCheck_2719_ = !lean_is_exclusive(v___x_2711_);
if (v_isSharedCheck_2719_ == 0)
{
v___x_2714_ = v___x_2711_;
v_isShared_2715_ = v_isSharedCheck_2719_;
goto v_resetjp_2713_;
}
else
{
lean_inc(v_a_2712_);
lean_dec(v___x_2711_);
v___x_2714_ = lean_box(0);
v_isShared_2715_ = v_isSharedCheck_2719_;
goto v_resetjp_2713_;
}
v_resetjp_2713_:
{
lean_object* v___x_2717_; 
if (v_isShared_2715_ == 0)
{
v___x_2717_ = v___x_2714_;
goto v_reusejp_2716_;
}
else
{
lean_object* v_reuseFailAlloc_2718_; 
v_reuseFailAlloc_2718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2718_, 0, v_a_2712_);
v___x_2717_ = v_reuseFailAlloc_2718_;
goto v_reusejp_2716_;
}
v_reusejp_2716_:
{
return v___x_2717_;
}
}
}
}
}
v___jp_2724_:
{
lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v_snd_2732_; lean_object* v_fst_2733_; lean_object* v___x_2735_; uint8_t v_isShared_2736_; uint8_t v_isSharedCheck_2787_; 
lean_inc_ref(v_recArgInfos_2666_);
v___x_2730_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__3(v_sz_2722_, v___x_2661_, v_recArgInfos_2666_);
lean_inc_ref(v_xs_2663_);
v___x_2731_ = l_Lean_Elab_FixedParamPerms_erase(v_a_2662_, v_xs_2663_, v___x_2730_);
v_snd_2732_ = lean_ctor_get(v___x_2731_, 1);
v_fst_2733_ = lean_ctor_get(v___x_2731_, 0);
v_isSharedCheck_2787_ = !lean_is_exclusive(v___x_2731_);
if (v_isSharedCheck_2787_ == 0)
{
v___x_2735_ = v___x_2731_;
v_isShared_2736_ = v_isSharedCheck_2787_;
goto v_resetjp_2734_;
}
else
{
lean_inc(v_snd_2732_);
lean_inc(v_fst_2733_);
lean_dec(v___x_2731_);
v___x_2735_ = lean_box(0);
v_isShared_2736_ = v_isSharedCheck_2787_;
goto v_resetjp_2734_;
}
v_resetjp_2734_:
{
lean_object* v_fst_2737_; lean_object* v_snd_2738_; lean_object* v___x_2740_; uint8_t v_isShared_2741_; uint8_t v_isSharedCheck_2786_; 
v_fst_2737_ = lean_ctor_get(v_snd_2732_, 0);
v_snd_2738_ = lean_ctor_get(v_snd_2732_, 1);
v_isSharedCheck_2786_ = !lean_is_exclusive(v_snd_2732_);
if (v_isSharedCheck_2786_ == 0)
{
v___x_2740_ = v_snd_2732_;
v_isShared_2741_ = v_isSharedCheck_2786_;
goto v_resetjp_2739_;
}
else
{
lean_inc(v_snd_2738_);
lean_inc(v_fst_2737_);
lean_dec(v_snd_2732_);
v___x_2740_ = lean_box(0);
v_isShared_2741_ = v_isSharedCheck_2786_;
goto v_resetjp_2739_;
}
v_resetjp_2739_:
{
lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___f_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; uint8_t v___x_2748_; 
v___x_2742_ = lean_array_get_size(v_recArgInfos_2666_);
v___x_2743_ = lean_mk_empty_array_with_capacity(v___x_2742_);
v___x_2744_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg(v_fst_2733_, v_recArgInfos_2666_, v___x_2742_, v___x_2664_, v___x_2743_);
lean_dec_ref(v_recArgInfos_2666_);
lean_inc_ref(v___x_2744_);
lean_inc(v_fst_2737_);
v___f_2745_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___boxed), 11, 5);
lean_closure_set(v___f_2745_, 0, v_a_2665_);
lean_closure_set(v___f_2745_, 1, v_fst_2733_);
lean_closure_set(v___f_2745_, 2, v_fst_2737_);
lean_closure_set(v___f_2745_, 3, v___x_2744_);
lean_closure_set(v___f_2745_, 4, v___x_2723_);
v___x_2746_ = lean_array_get_size(v_fst_2737_);
v___x_2747_ = lean_array_get_size(v_xs_2663_);
v___x_2748_ = lean_nat_dec_eq(v___x_2746_, v___x_2747_);
if (v___x_2748_ == 0)
{
lean_object* v___x_2749_; lean_object* v_a_2750_; uint8_t v___x_2751_; 
v___x_2749_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___redArg(v___x_2694_, v___y_2728_);
v_a_2750_ = lean_ctor_get(v___x_2749_, 0);
lean_inc(v_a_2750_);
lean_dec_ref(v___x_2749_);
v___x_2751_ = lean_unbox(v_a_2750_);
lean_dec(v_a_2750_);
if (v___x_2751_ == 0)
{
lean_del_object(v___x_2740_);
lean_dec(v_fst_2737_);
lean_del_object(v___x_2735_);
lean_dec_ref(v_xs_2663_);
v___y_2696_ = v___f_2745_;
v___y_2697_ = v_snd_2738_;
v___y_2698_ = v___x_2744_;
v___y_2699_ = v___y_2725_;
v___y_2700_ = v___y_2726_;
v___y_2701_ = v___y_2727_;
v___y_2702_ = v___y_2728_;
v___y_2703_ = v___y_2729_;
goto v___jp_2695_;
}
else
{
lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2758_; 
v___x_2752_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___closed__3, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___closed__3);
v___x_2753_ = lean_array_to_list(v_xs_2663_);
v___x_2754_ = lean_box(0);
v___x_2755_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_2753_, v___x_2754_);
v___x_2756_ = l_Lean_MessageData_ofList(v___x_2755_);
if (v_isShared_2741_ == 0)
{
lean_ctor_set_tag(v___x_2740_, 7);
lean_ctor_set(v___x_2740_, 1, v___x_2756_);
lean_ctor_set(v___x_2740_, 0, v___x_2752_);
v___x_2758_ = v___x_2740_;
goto v_reusejp_2757_;
}
else
{
lean_object* v_reuseFailAlloc_2784_; 
v_reuseFailAlloc_2784_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2784_, 0, v___x_2752_);
lean_ctor_set(v_reuseFailAlloc_2784_, 1, v___x_2756_);
v___x_2758_ = v_reuseFailAlloc_2784_;
goto v_reusejp_2757_;
}
v_reusejp_2757_:
{
lean_object* v___x_2759_; lean_object* v___x_2761_; 
v___x_2759_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___closed__5, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___closed__5);
if (v_isShared_2736_ == 0)
{
lean_ctor_set_tag(v___x_2735_, 7);
lean_ctor_set(v___x_2735_, 1, v___x_2759_);
lean_ctor_set(v___x_2735_, 0, v___x_2758_);
v___x_2761_ = v___x_2735_;
goto v_reusejp_2760_;
}
else
{
lean_object* v_reuseFailAlloc_2783_; 
v_reuseFailAlloc_2783_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2783_, 0, v___x_2758_);
lean_ctor_set(v_reuseFailAlloc_2783_, 1, v___x_2759_);
v___x_2761_ = v_reuseFailAlloc_2783_;
goto v_reusejp_2760_;
}
v_reusejp_2760_:
{
lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; size_t v_sz_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; 
v___x_2762_ = lean_array_to_list(v_fst_2737_);
v___x_2763_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_2762_, v___x_2754_);
v___x_2764_ = l_Lean_MessageData_ofList(v___x_2763_);
v___x_2765_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2765_, 0, v___x_2761_);
lean_ctor_set(v___x_2765_, 1, v___x_2764_);
v___x_2766_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___closed__7, &l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___closed__7);
v___x_2767_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2767_, 0, v___x_2765_);
lean_ctor_set(v___x_2767_, 1, v___x_2766_);
v_sz_2768_ = lean_array_size(v_snd_2738_);
lean_inc(v_snd_2738_);
v___x_2769_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__11(v_sz_2768_, v___x_2661_, v_snd_2738_);
v___x_2770_ = lean_array_to_list(v___x_2769_);
v___x_2771_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_2770_, v___x_2754_);
v___x_2772_ = l_Lean_MessageData_ofList(v___x_2771_);
v___x_2773_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2773_, 0, v___x_2767_);
lean_ctor_set(v___x_2773_, 1, v___x_2772_);
v___x_2774_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v___x_2694_, v___x_2773_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_);
if (lean_obj_tag(v___x_2774_) == 0)
{
lean_dec_ref(v___x_2774_);
v___y_2696_ = v___f_2745_;
v___y_2697_ = v_snd_2738_;
v___y_2698_ = v___x_2744_;
v___y_2699_ = v___y_2725_;
v___y_2700_ = v___y_2726_;
v___y_2701_ = v___y_2727_;
v___y_2702_ = v___y_2728_;
v___y_2703_ = v___y_2729_;
goto v___jp_2695_;
}
else
{
lean_object* v_a_2775_; lean_object* v___x_2777_; uint8_t v_isShared_2778_; uint8_t v_isSharedCheck_2782_; 
lean_dec_ref(v___f_2745_);
lean_dec_ref(v___x_2744_);
lean_dec(v_snd_2738_);
lean_dec(v___y_2729_);
lean_dec_ref(v___y_2728_);
lean_dec(v___y_2727_);
lean_dec_ref(v___y_2726_);
lean_dec(v___y_2725_);
v_a_2775_ = lean_ctor_get(v___x_2774_, 0);
v_isSharedCheck_2782_ = !lean_is_exclusive(v___x_2774_);
if (v_isSharedCheck_2782_ == 0)
{
v___x_2777_ = v___x_2774_;
v_isShared_2778_ = v_isSharedCheck_2782_;
goto v_resetjp_2776_;
}
else
{
lean_inc(v_a_2775_);
lean_dec(v___x_2774_);
v___x_2777_ = lean_box(0);
v_isShared_2778_ = v_isSharedCheck_2782_;
goto v_resetjp_2776_;
}
v_resetjp_2776_:
{
lean_object* v___x_2780_; 
if (v_isShared_2778_ == 0)
{
v___x_2780_ = v___x_2777_;
goto v_reusejp_2779_;
}
else
{
lean_object* v_reuseFailAlloc_2781_; 
v_reuseFailAlloc_2781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2781_, 0, v_a_2775_);
v___x_2780_ = v_reuseFailAlloc_2781_;
goto v_reusejp_2779_;
}
v_reusejp_2779_:
{
return v___x_2780_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2785_; 
lean_dec_ref(v___x_2744_);
lean_del_object(v___x_2740_);
lean_dec(v_fst_2737_);
lean_del_object(v___x_2735_);
lean_dec_ref(v_xs_2663_);
v___x_2785_ = l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg(v_snd_2738_, v___f_2745_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_);
lean_dec(v_snd_2738_);
return v___x_2785_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___boxed(lean_object* v___x_2804_, lean_object* v_a_2805_, lean_object* v_xs_2806_, lean_object* v___x_2807_, lean_object* v_a_2808_, lean_object* v_recArgInfos_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_){
_start:
{
size_t v___x_26093__boxed_2816_; lean_object* v_res_2817_; 
v___x_26093__boxed_2816_ = lean_unbox_usize(v___x_2804_);
lean_dec(v___x_2804_);
v_res_2817_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1(v___x_26093__boxed_2816_, v_a_2805_, v_xs_2806_, v___x_2807_, v_a_2808_, v_recArgInfos_2809_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_);
return v_res_2817_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg(lean_object* v___x_2818_, lean_object* v_xs_2819_, lean_object* v_as_2820_, lean_object* v_i_2821_, lean_object* v_j_2822_, lean_object* v_bs_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_){
_start:
{
lean_object* v_zero_2829_; uint8_t v_isZero_2830_; 
v_zero_2829_ = lean_unsigned_to_nat(0u);
v_isZero_2830_ = lean_nat_dec_eq(v_i_2821_, v_zero_2829_);
if (v_isZero_2830_ == 1)
{
lean_object* v___x_2831_; 
lean_dec(v___y_2827_);
lean_dec_ref(v___y_2826_);
lean_dec(v___y_2825_);
lean_dec_ref(v___y_2824_);
lean_dec(v_j_2822_);
lean_dec(v_i_2821_);
lean_dec_ref(v_xs_2819_);
v___x_2831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2831_, 0, v_bs_2823_);
return v___x_2831_;
}
else
{
lean_object* v___x_2832_; lean_object* v_value_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; 
v___x_2832_ = lean_array_fget_borrowed(v_as_2820_, v_j_2822_);
v_value_2833_ = lean_ctor_get(v___x_2832_, 7);
v___x_2834_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9___redArg___closed__0, &l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9___redArg___closed__0_once, _init_l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9___redArg___closed__0);
v___x_2835_ = lean_array_get_borrowed(v___x_2834_, v___x_2818_, v_j_2822_);
lean_inc(v___y_2827_);
lean_inc_ref(v___y_2826_);
lean_inc(v___y_2825_);
lean_inc_ref(v___y_2824_);
lean_inc_ref(v_xs_2819_);
lean_inc_ref(v_value_2833_);
lean_inc(v___x_2835_);
v___x_2836_ = l_Lean_Elab_FixedParamPerm_instantiateLambda(v___x_2835_, v_value_2833_, v_xs_2819_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_);
if (lean_obj_tag(v___x_2836_) == 0)
{
lean_object* v_a_2837_; lean_object* v_one_2838_; lean_object* v_n_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; 
v_a_2837_ = lean_ctor_get(v___x_2836_, 0);
lean_inc(v_a_2837_);
lean_dec_ref(v___x_2836_);
v_one_2838_ = lean_unsigned_to_nat(1u);
v_n_2839_ = lean_nat_sub(v_i_2821_, v_one_2838_);
lean_dec(v_i_2821_);
v___x_2840_ = lean_nat_add(v_j_2822_, v_one_2838_);
lean_dec(v_j_2822_);
v___x_2841_ = lean_array_push(v_bs_2823_, v_a_2837_);
v_i_2821_ = v_n_2839_;
v_j_2822_ = v___x_2840_;
v_bs_2823_ = v___x_2841_;
goto _start;
}
else
{
lean_object* v_a_2843_; lean_object* v___x_2845_; uint8_t v_isShared_2846_; uint8_t v_isSharedCheck_2850_; 
lean_dec(v___y_2827_);
lean_dec_ref(v___y_2826_);
lean_dec(v___y_2825_);
lean_dec_ref(v___y_2824_);
lean_dec_ref(v_bs_2823_);
lean_dec(v_j_2822_);
lean_dec(v_i_2821_);
lean_dec_ref(v_xs_2819_);
v_a_2843_ = lean_ctor_get(v___x_2836_, 0);
v_isSharedCheck_2850_ = !lean_is_exclusive(v___x_2836_);
if (v_isSharedCheck_2850_ == 0)
{
v___x_2845_ = v___x_2836_;
v_isShared_2846_ = v_isSharedCheck_2850_;
goto v_resetjp_2844_;
}
else
{
lean_inc(v_a_2843_);
lean_dec(v___x_2836_);
v___x_2845_ = lean_box(0);
v_isShared_2846_ = v_isSharedCheck_2850_;
goto v_resetjp_2844_;
}
v_resetjp_2844_:
{
lean_object* v___x_2848_; 
if (v_isShared_2846_ == 0)
{
v___x_2848_ = v___x_2845_;
goto v_reusejp_2847_;
}
else
{
lean_object* v_reuseFailAlloc_2849_; 
v_reuseFailAlloc_2849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2849_, 0, v_a_2843_);
v___x_2848_ = v_reuseFailAlloc_2849_;
goto v_reusejp_2847_;
}
v_reusejp_2847_:
{
return v___x_2848_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg___boxed(lean_object* v___x_2851_, lean_object* v_xs_2852_, lean_object* v_as_2853_, lean_object* v_i_2854_, lean_object* v_j_2855_, lean_object* v_bs_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_){
_start:
{
lean_object* v_res_2862_; 
v_res_2862_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg(v___x_2851_, v_xs_2852_, v_as_2853_, v_i_2854_, v_j_2855_, v_bs_2856_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_);
lean_dec_ref(v_as_2853_);
lean_dec_ref(v___x_2851_);
return v_res_2862_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__2(lean_object* v_a_2863_, lean_object* v_perms_2864_, lean_object* v___x_2865_, size_t v___x_2866_, lean_object* v_a_2867_, lean_object* v_fnNames_2868_, lean_object* v_termMeasure_x3fs_2869_, lean_object* v_xs_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_){
_start:
{
lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; 
v___x_2877_ = lean_array_get_size(v_a_2863_);
v___x_2878_ = lean_mk_empty_array_with_capacity(v___x_2877_);
lean_inc(v___y_2875_);
lean_inc_ref(v___y_2874_);
lean_inc(v___y_2873_);
lean_inc_ref(v___y_2872_);
lean_inc(v___x_2865_);
lean_inc_ref(v_xs_2870_);
v___x_2879_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg(v_perms_2864_, v_xs_2870_, v_a_2863_, v___x_2877_, v___x_2865_, v___x_2878_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_);
if (lean_obj_tag(v___x_2879_) == 0)
{
lean_object* v_a_2880_; lean_object* v___x_2881_; lean_object* v___f_2882_; lean_object* v___x_2883_; 
v_a_2880_ = lean_ctor_get(v___x_2879_, 0);
lean_inc(v_a_2880_);
lean_dec_ref(v___x_2879_);
v___x_2881_ = lean_box_usize(v___x_2866_);
lean_inc_ref(v_xs_2870_);
lean_inc_ref(v_a_2867_);
v___f_2882_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___boxed), 12, 5);
lean_closure_set(v___f_2882_, 0, v___x_2881_);
lean_closure_set(v___f_2882_, 1, v_a_2867_);
lean_closure_set(v___f_2882_, 2, v_xs_2870_);
lean_closure_set(v___f_2882_, 3, v___x_2865_);
lean_closure_set(v___f_2882_, 4, v_a_2863_);
v___x_2883_ = l_Lean_Elab_Structural_tryAllArgs___redArg(v_fnNames_2868_, v_a_2867_, v_xs_2870_, v_a_2880_, v_termMeasure_x3fs_2869_, v___f_2882_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_);
return v___x_2883_;
}
else
{
lean_object* v_a_2884_; lean_object* v___x_2886_; uint8_t v_isShared_2887_; uint8_t v_isSharedCheck_2891_; 
lean_dec(v___y_2875_);
lean_dec_ref(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec_ref(v___y_2872_);
lean_dec(v___y_2871_);
lean_dec_ref(v_xs_2870_);
lean_dec_ref(v_termMeasure_x3fs_2869_);
lean_dec_ref(v_a_2867_);
lean_dec(v___x_2865_);
lean_dec_ref(v_a_2863_);
v_a_2884_ = lean_ctor_get(v___x_2879_, 0);
v_isSharedCheck_2891_ = !lean_is_exclusive(v___x_2879_);
if (v_isSharedCheck_2891_ == 0)
{
v___x_2886_ = v___x_2879_;
v_isShared_2887_ = v_isSharedCheck_2891_;
goto v_resetjp_2885_;
}
else
{
lean_inc(v_a_2884_);
lean_dec(v___x_2879_);
v___x_2886_ = lean_box(0);
v_isShared_2887_ = v_isSharedCheck_2891_;
goto v_resetjp_2885_;
}
v_resetjp_2885_:
{
lean_object* v___x_2889_; 
if (v_isShared_2887_ == 0)
{
v___x_2889_ = v___x_2886_;
goto v_reusejp_2888_;
}
else
{
lean_object* v_reuseFailAlloc_2890_; 
v_reuseFailAlloc_2890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2890_, 0, v_a_2884_);
v___x_2889_ = v_reuseFailAlloc_2890_;
goto v_reusejp_2888_;
}
v_reusejp_2888_:
{
return v___x_2889_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__2___boxed(lean_object* v_a_2892_, lean_object* v_perms_2893_, lean_object* v___x_2894_, lean_object* v___x_2895_, lean_object* v_a_2896_, lean_object* v_fnNames_2897_, lean_object* v_termMeasure_x3fs_2898_, lean_object* v_xs_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_){
_start:
{
size_t v___x_26458__boxed_2906_; lean_object* v_res_2907_; 
v___x_26458__boxed_2906_ = lean_unbox_usize(v___x_2895_);
lean_dec(v___x_2895_);
v_res_2907_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__2(v_a_2892_, v_perms_2893_, v___x_2894_, v___x_26458__boxed_2906_, v_a_2896_, v_fnNames_2897_, v_termMeasure_x3fs_2898_, v_xs_2899_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_, v___y_2904_);
lean_dec_ref(v_fnNames_2897_);
lean_dec_ref(v_perms_2893_);
return v_res_2907_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__14___redArg(lean_object* v_as_2908_, size_t v_i_2909_, size_t v_stop_2910_, lean_object* v_b_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_){
_start:
{
uint8_t v___x_2915_; 
v___x_2915_ = lean_usize_dec_eq(v_i_2909_, v_stop_2910_);
if (v___x_2915_ == 0)
{
lean_object* v___x_2916_; lean_object* v___x_2917_; 
v___x_2916_ = lean_array_uget_borrowed(v_as_2908_, v_i_2909_);
lean_inc(v___y_2913_);
lean_inc_ref(v___y_2912_);
v___x_2917_ = l_Lean_Elab_addAsAxiom___redArg(v___x_2916_, v___y_2912_, v___y_2913_);
if (lean_obj_tag(v___x_2917_) == 0)
{
lean_object* v_a_2918_; size_t v___x_2919_; size_t v___x_2920_; 
v_a_2918_ = lean_ctor_get(v___x_2917_, 0);
lean_inc(v_a_2918_);
lean_dec_ref(v___x_2917_);
v___x_2919_ = ((size_t)1ULL);
v___x_2920_ = lean_usize_add(v_i_2909_, v___x_2919_);
v_i_2909_ = v___x_2920_;
v_b_2911_ = v_a_2918_;
goto _start;
}
else
{
lean_dec(v___y_2913_);
lean_dec_ref(v___y_2912_);
return v___x_2917_;
}
}
else
{
lean_object* v___x_2922_; 
lean_dec(v___y_2913_);
lean_dec_ref(v___y_2912_);
v___x_2922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2922_, 0, v_b_2911_);
return v___x_2922_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__14___redArg___boxed(lean_object* v_as_2923_, lean_object* v_i_2924_, lean_object* v_stop_2925_, lean_object* v_b_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_){
_start:
{
size_t v_i_boxed_2930_; size_t v_stop_boxed_2931_; lean_object* v_res_2932_; 
v_i_boxed_2930_ = lean_unbox_usize(v_i_2924_);
lean_dec(v_i_2924_);
v_stop_boxed_2931_ = lean_unbox_usize(v_stop_2925_);
lean_dec(v_stop_2925_);
v_res_2932_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__14___redArg(v_as_2923_, v_i_boxed_2930_, v_stop_boxed_2931_, v_b_2926_, v___y_2927_, v___y_2928_);
lean_dec_ref(v_as_2923_);
return v_res_2932_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1___redArg(lean_object* v_fnNames_2933_, lean_object* v_numSectionVars_2934_, size_t v_sz_2935_, size_t v_i_2936_, lean_object* v_bs_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_){
_start:
{
uint8_t v___x_2941_; 
v___x_2941_ = lean_usize_dec_lt(v_i_2936_, v_sz_2935_);
if (v___x_2941_ == 0)
{
lean_object* v___x_2942_; 
lean_dec(v___y_2939_);
lean_dec_ref(v___y_2938_);
lean_dec(v_numSectionVars_2934_);
lean_dec_ref(v_fnNames_2933_);
v___x_2942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2942_, 0, v_bs_2937_);
return v___x_2942_;
}
else
{
lean_object* v_v_2943_; lean_object* v_ref_2944_; uint8_t v_kind_2945_; lean_object* v_levelParams_2946_; lean_object* v_modifiers_2947_; lean_object* v_declName_2948_; lean_object* v_binders_2949_; lean_object* v_numSectionVars_2950_; lean_object* v_type_2951_; lean_object* v_value_2952_; lean_object* v_termination_2953_; lean_object* v___x_2955_; uint8_t v_isShared_2956_; uint8_t v_isSharedCheck_2976_; 
v_v_2943_ = lean_array_uget(v_bs_2937_, v_i_2936_);
v_ref_2944_ = lean_ctor_get(v_v_2943_, 0);
v_kind_2945_ = lean_ctor_get_uint8(v_v_2943_, sizeof(void*)*9);
v_levelParams_2946_ = lean_ctor_get(v_v_2943_, 1);
v_modifiers_2947_ = lean_ctor_get(v_v_2943_, 2);
v_declName_2948_ = lean_ctor_get(v_v_2943_, 3);
v_binders_2949_ = lean_ctor_get(v_v_2943_, 4);
v_numSectionVars_2950_ = lean_ctor_get(v_v_2943_, 5);
v_type_2951_ = lean_ctor_get(v_v_2943_, 6);
v_value_2952_ = lean_ctor_get(v_v_2943_, 7);
v_termination_2953_ = lean_ctor_get(v_v_2943_, 8);
v_isSharedCheck_2976_ = !lean_is_exclusive(v_v_2943_);
if (v_isSharedCheck_2976_ == 0)
{
v___x_2955_ = v_v_2943_;
v_isShared_2956_ = v_isSharedCheck_2976_;
goto v_resetjp_2954_;
}
else
{
lean_inc(v_termination_2953_);
lean_inc(v_value_2952_);
lean_inc(v_type_2951_);
lean_inc(v_numSectionVars_2950_);
lean_inc(v_binders_2949_);
lean_inc(v_declName_2948_);
lean_inc(v_modifiers_2947_);
lean_inc(v_levelParams_2946_);
lean_inc(v_ref_2944_);
lean_dec(v_v_2943_);
v___x_2955_ = lean_box(0);
v_isShared_2956_ = v_isSharedCheck_2976_;
goto v_resetjp_2954_;
}
v_resetjp_2954_:
{
lean_object* v___x_2957_; 
lean_inc(v___y_2939_);
lean_inc_ref(v___y_2938_);
lean_inc(v_numSectionVars_2934_);
lean_inc_ref(v_fnNames_2933_);
v___x_2957_ = l_Lean_Elab_Structural_preprocess(v_value_2952_, v_fnNames_2933_, v_numSectionVars_2934_, v___y_2938_, v___y_2939_);
if (lean_obj_tag(v___x_2957_) == 0)
{
lean_object* v_a_2958_; lean_object* v___x_2959_; lean_object* v_bs_x27_2960_; lean_object* v___x_2962_; 
v_a_2958_ = lean_ctor_get(v___x_2957_, 0);
lean_inc(v_a_2958_);
lean_dec_ref(v___x_2957_);
v___x_2959_ = lean_unsigned_to_nat(0u);
v_bs_x27_2960_ = lean_array_uset(v_bs_2937_, v_i_2936_, v___x_2959_);
if (v_isShared_2956_ == 0)
{
lean_ctor_set(v___x_2955_, 7, v_a_2958_);
v___x_2962_ = v___x_2955_;
goto v_reusejp_2961_;
}
else
{
lean_object* v_reuseFailAlloc_2967_; 
v_reuseFailAlloc_2967_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_2967_, 0, v_ref_2944_);
lean_ctor_set(v_reuseFailAlloc_2967_, 1, v_levelParams_2946_);
lean_ctor_set(v_reuseFailAlloc_2967_, 2, v_modifiers_2947_);
lean_ctor_set(v_reuseFailAlloc_2967_, 3, v_declName_2948_);
lean_ctor_set(v_reuseFailAlloc_2967_, 4, v_binders_2949_);
lean_ctor_set(v_reuseFailAlloc_2967_, 5, v_numSectionVars_2950_);
lean_ctor_set(v_reuseFailAlloc_2967_, 6, v_type_2951_);
lean_ctor_set(v_reuseFailAlloc_2967_, 7, v_a_2958_);
lean_ctor_set(v_reuseFailAlloc_2967_, 8, v_termination_2953_);
lean_ctor_set_uint8(v_reuseFailAlloc_2967_, sizeof(void*)*9, v_kind_2945_);
v___x_2962_ = v_reuseFailAlloc_2967_;
goto v_reusejp_2961_;
}
v_reusejp_2961_:
{
size_t v___x_2963_; size_t v___x_2964_; lean_object* v___x_2965_; 
v___x_2963_ = ((size_t)1ULL);
v___x_2964_ = lean_usize_add(v_i_2936_, v___x_2963_);
v___x_2965_ = lean_array_uset(v_bs_x27_2960_, v_i_2936_, v___x_2962_);
v_i_2936_ = v___x_2964_;
v_bs_2937_ = v___x_2965_;
goto _start;
}
}
else
{
lean_object* v_a_2968_; lean_object* v___x_2970_; uint8_t v_isShared_2971_; uint8_t v_isSharedCheck_2975_; 
lean_del_object(v___x_2955_);
lean_dec_ref(v_termination_2953_);
lean_dec_ref(v_type_2951_);
lean_dec(v_numSectionVars_2950_);
lean_dec(v_binders_2949_);
lean_dec(v_declName_2948_);
lean_dec_ref(v_modifiers_2947_);
lean_dec(v_levelParams_2946_);
lean_dec(v_ref_2944_);
lean_dec(v___y_2939_);
lean_dec_ref(v___y_2938_);
lean_dec_ref(v_bs_2937_);
lean_dec(v_numSectionVars_2934_);
lean_dec_ref(v_fnNames_2933_);
v_a_2968_ = lean_ctor_get(v___x_2957_, 0);
v_isSharedCheck_2975_ = !lean_is_exclusive(v___x_2957_);
if (v_isSharedCheck_2975_ == 0)
{
v___x_2970_ = v___x_2957_;
v_isShared_2971_ = v_isSharedCheck_2975_;
goto v_resetjp_2969_;
}
else
{
lean_inc(v_a_2968_);
lean_dec(v___x_2957_);
v___x_2970_ = lean_box(0);
v_isShared_2971_ = v_isSharedCheck_2975_;
goto v_resetjp_2969_;
}
v_resetjp_2969_:
{
lean_object* v___x_2973_; 
if (v_isShared_2971_ == 0)
{
v___x_2973_ = v___x_2970_;
goto v_reusejp_2972_;
}
else
{
lean_object* v_reuseFailAlloc_2974_; 
v_reuseFailAlloc_2974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2974_, 0, v_a_2968_);
v___x_2973_ = v_reuseFailAlloc_2974_;
goto v_reusejp_2972_;
}
v_reusejp_2972_:
{
return v___x_2973_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1___redArg___boxed(lean_object* v_fnNames_2977_, lean_object* v_numSectionVars_2978_, lean_object* v_sz_2979_, lean_object* v_i_2980_, lean_object* v_bs_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_){
_start:
{
size_t v_sz_boxed_2985_; size_t v_i_boxed_2986_; lean_object* v_res_2987_; 
v_sz_boxed_2985_ = lean_unbox_usize(v_sz_2979_);
lean_dec(v_sz_2979_);
v_i_boxed_2986_ = lean_unbox_usize(v_i_2980_);
lean_dec(v_i_2980_);
v_res_2987_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1___redArg(v_fnNames_2977_, v_numSectionVars_2978_, v_sz_boxed_2985_, v_i_boxed_2986_, v_bs_2981_, v___y_2982_, v___y_2983_);
return v_res_2987_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0(size_t v_sz_2988_, size_t v_i_2989_, lean_object* v_bs_2990_){
_start:
{
uint8_t v___x_2991_; 
v___x_2991_ = lean_usize_dec_lt(v_i_2989_, v_sz_2988_);
if (v___x_2991_ == 0)
{
return v_bs_2990_;
}
else
{
lean_object* v_v_2992_; lean_object* v_declName_2993_; lean_object* v___x_2994_; lean_object* v_bs_x27_2995_; size_t v___x_2996_; size_t v___x_2997_; lean_object* v___x_2998_; 
v_v_2992_ = lean_array_uget_borrowed(v_bs_2990_, v_i_2989_);
v_declName_2993_ = lean_ctor_get(v_v_2992_, 3);
lean_inc(v_declName_2993_);
v___x_2994_ = lean_unsigned_to_nat(0u);
v_bs_x27_2995_ = lean_array_uset(v_bs_2990_, v_i_2989_, v___x_2994_);
v___x_2996_ = ((size_t)1ULL);
v___x_2997_ = lean_usize_add(v_i_2989_, v___x_2996_);
v___x_2998_ = lean_array_uset(v_bs_x27_2995_, v_i_2989_, v_declName_2993_);
v_i_2989_ = v___x_2997_;
v_bs_2990_ = v___x_2998_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0___boxed(lean_object* v_sz_3000_, lean_object* v_i_3001_, lean_object* v_bs_3002_){
_start:
{
size_t v_sz_boxed_3003_; size_t v_i_boxed_3004_; lean_object* v_res_3005_; 
v_sz_boxed_3003_ = lean_unbox_usize(v_sz_3000_);
lean_dec(v_sz_3000_);
v_i_boxed_3004_ = lean_unbox_usize(v_i_3001_);
lean_dec(v_i_3001_);
v_res_3005_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0(v_sz_boxed_3003_, v_i_boxed_3004_, v_bs_3002_);
return v_res_3005_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__3(lean_object* v___x_3008_, lean_object* v_preDefs_3009_, lean_object* v___x_3010_, lean_object* v_termMeasure_x3fs_3011_, lean_object* v___x_3012_, lean_object* v___x_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_){
_start:
{
lean_object* v___y_3054_; uint8_t v___x_3063_; 
v___x_3063_ = lean_nat_dec_lt(v___x_3010_, v___x_3013_);
if (v___x_3063_ == 0)
{
goto v___jp_3020_;
}
else
{
lean_object* v___x_3064_; uint8_t v___x_3065_; 
v___x_3064_ = lean_box(0);
v___x_3065_ = lean_nat_dec_le(v___x_3013_, v___x_3013_);
if (v___x_3065_ == 0)
{
if (v___x_3063_ == 0)
{
goto v___jp_3020_;
}
else
{
size_t v___x_3066_; size_t v___x_3067_; lean_object* v___x_3068_; 
v___x_3066_ = ((size_t)0ULL);
v___x_3067_ = lean_usize_of_nat(v___x_3013_);
lean_inc(v___y_3018_);
lean_inc_ref(v___y_3017_);
v___x_3068_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__14___redArg(v_preDefs_3009_, v___x_3066_, v___x_3067_, v___x_3064_, v___y_3017_, v___y_3018_);
v___y_3054_ = v___x_3068_;
goto v___jp_3053_;
}
}
else
{
size_t v___x_3069_; size_t v___x_3070_; lean_object* v___x_3071_; 
v___x_3069_ = ((size_t)0ULL);
v___x_3070_ = lean_usize_of_nat(v___x_3013_);
lean_inc(v___y_3018_);
lean_inc_ref(v___y_3017_);
v___x_3071_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__14___redArg(v_preDefs_3009_, v___x_3069_, v___x_3070_, v___x_3064_, v___y_3017_, v___y_3018_);
v___y_3054_ = v___x_3071_;
goto v___jp_3053_;
}
}
v___jp_3020_:
{
lean_object* v___x_3021_; lean_object* v_numSectionVars_3022_; size_t v_sz_3023_; size_t v___x_3024_; lean_object* v_fnNames_3025_; lean_object* v___x_3026_; 
lean_inc_ref(v___x_3008_);
v___x_3021_ = lean_array_get_borrowed(v___x_3008_, v_preDefs_3009_, v___x_3010_);
v_numSectionVars_3022_ = lean_ctor_get(v___x_3021_, 5);
lean_inc(v_numSectionVars_3022_);
v_sz_3023_ = lean_array_size(v_preDefs_3009_);
v___x_3024_ = ((size_t)0ULL);
lean_inc_ref(v_preDefs_3009_);
v_fnNames_3025_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0(v_sz_3023_, v___x_3024_, v_preDefs_3009_);
lean_inc(v___y_3018_);
lean_inc_ref(v___y_3017_);
lean_inc_ref(v_fnNames_3025_);
v___x_3026_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1___redArg(v_fnNames_3025_, v_numSectionVars_3022_, v_sz_3023_, v___x_3024_, v_preDefs_3009_, v___y_3017_, v___y_3018_);
if (lean_obj_tag(v___x_3026_) == 0)
{
lean_object* v_a_3027_; lean_object* v___x_3028_; 
v_a_3027_ = lean_ctor_get(v___x_3026_, 0);
lean_inc(v_a_3027_);
lean_dec_ref(v___x_3026_);
lean_inc(v___y_3018_);
lean_inc_ref(v___y_3017_);
lean_inc(v___y_3016_);
lean_inc_ref(v___y_3015_);
lean_inc(v_a_3027_);
v___x_3028_ = l_Lean_Elab_getFixedParamPerms(v_a_3027_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_);
if (lean_obj_tag(v___x_3028_) == 0)
{
lean_object* v_a_3029_; lean_object* v_perms_3030_; lean_object* v___x_3031_; lean_object* v_type_3032_; lean_object* v___x_3033_; lean_object* v___f_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; 
v_a_3029_ = lean_ctor_get(v___x_3028_, 0);
lean_inc(v_a_3029_);
lean_dec_ref(v___x_3028_);
v_perms_3030_ = lean_ctor_get(v_a_3029_, 1);
lean_inc_ref(v_perms_3030_);
v___x_3031_ = lean_array_get_borrowed(v___x_3008_, v_a_3027_, v___x_3010_);
v_type_3032_ = lean_ctor_get(v___x_3031_, 6);
lean_inc_ref(v_type_3032_);
v___x_3033_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__3___boxed__const__1));
lean_inc(v___x_3010_);
lean_inc_ref(v_perms_3030_);
v___f_3034_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__2___boxed), 14, 7);
lean_closure_set(v___f_3034_, 0, v_a_3027_);
lean_closure_set(v___f_3034_, 1, v_perms_3030_);
lean_closure_set(v___f_3034_, 2, v___x_3010_);
lean_closure_set(v___f_3034_, 3, v___x_3033_);
lean_closure_set(v___f_3034_, 4, v_a_3029_);
lean_closure_set(v___f_3034_, 5, v_fnNames_3025_);
lean_closure_set(v___f_3034_, 6, v_termMeasure_x3fs_3011_);
v___x_3035_ = lean_array_get(v___x_3012_, v_perms_3030_, v___x_3010_);
lean_dec(v___x_3010_);
lean_dec_ref(v_perms_3030_);
v___x_3036_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg(v___x_3035_, v_type_3032_, v___f_3034_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_);
return v___x_3036_;
}
else
{
lean_object* v_a_3037_; lean_object* v___x_3039_; uint8_t v_isShared_3040_; uint8_t v_isSharedCheck_3044_; 
lean_dec(v_a_3027_);
lean_dec_ref(v_fnNames_3025_);
lean_dec(v___y_3018_);
lean_dec_ref(v___y_3017_);
lean_dec(v___y_3016_);
lean_dec_ref(v___y_3015_);
lean_dec(v___y_3014_);
lean_dec_ref(v___x_3012_);
lean_dec_ref(v_termMeasure_x3fs_3011_);
lean_dec(v___x_3010_);
lean_dec_ref(v___x_3008_);
v_a_3037_ = lean_ctor_get(v___x_3028_, 0);
v_isSharedCheck_3044_ = !lean_is_exclusive(v___x_3028_);
if (v_isSharedCheck_3044_ == 0)
{
v___x_3039_ = v___x_3028_;
v_isShared_3040_ = v_isSharedCheck_3044_;
goto v_resetjp_3038_;
}
else
{
lean_inc(v_a_3037_);
lean_dec(v___x_3028_);
v___x_3039_ = lean_box(0);
v_isShared_3040_ = v_isSharedCheck_3044_;
goto v_resetjp_3038_;
}
v_resetjp_3038_:
{
lean_object* v___x_3042_; 
if (v_isShared_3040_ == 0)
{
v___x_3042_ = v___x_3039_;
goto v_reusejp_3041_;
}
else
{
lean_object* v_reuseFailAlloc_3043_; 
v_reuseFailAlloc_3043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3043_, 0, v_a_3037_);
v___x_3042_ = v_reuseFailAlloc_3043_;
goto v_reusejp_3041_;
}
v_reusejp_3041_:
{
return v___x_3042_;
}
}
}
}
else
{
lean_object* v_a_3045_; lean_object* v___x_3047_; uint8_t v_isShared_3048_; uint8_t v_isSharedCheck_3052_; 
lean_dec_ref(v_fnNames_3025_);
lean_dec(v___y_3018_);
lean_dec_ref(v___y_3017_);
lean_dec(v___y_3016_);
lean_dec_ref(v___y_3015_);
lean_dec(v___y_3014_);
lean_dec_ref(v___x_3012_);
lean_dec_ref(v_termMeasure_x3fs_3011_);
lean_dec(v___x_3010_);
lean_dec_ref(v___x_3008_);
v_a_3045_ = lean_ctor_get(v___x_3026_, 0);
v_isSharedCheck_3052_ = !lean_is_exclusive(v___x_3026_);
if (v_isSharedCheck_3052_ == 0)
{
v___x_3047_ = v___x_3026_;
v_isShared_3048_ = v_isSharedCheck_3052_;
goto v_resetjp_3046_;
}
else
{
lean_inc(v_a_3045_);
lean_dec(v___x_3026_);
v___x_3047_ = lean_box(0);
v_isShared_3048_ = v_isSharedCheck_3052_;
goto v_resetjp_3046_;
}
v_resetjp_3046_:
{
lean_object* v___x_3050_; 
if (v_isShared_3048_ == 0)
{
v___x_3050_ = v___x_3047_;
goto v_reusejp_3049_;
}
else
{
lean_object* v_reuseFailAlloc_3051_; 
v_reuseFailAlloc_3051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3051_, 0, v_a_3045_);
v___x_3050_ = v_reuseFailAlloc_3051_;
goto v_reusejp_3049_;
}
v_reusejp_3049_:
{
return v___x_3050_;
}
}
}
}
v___jp_3053_:
{
if (lean_obj_tag(v___y_3054_) == 0)
{
lean_dec_ref(v___y_3054_);
goto v___jp_3020_;
}
else
{
lean_object* v_a_3055_; lean_object* v___x_3057_; uint8_t v_isShared_3058_; uint8_t v_isSharedCheck_3062_; 
lean_dec(v___y_3018_);
lean_dec_ref(v___y_3017_);
lean_dec(v___y_3016_);
lean_dec_ref(v___y_3015_);
lean_dec(v___y_3014_);
lean_dec_ref(v___x_3012_);
lean_dec_ref(v_termMeasure_x3fs_3011_);
lean_dec(v___x_3010_);
lean_dec_ref(v_preDefs_3009_);
lean_dec_ref(v___x_3008_);
v_a_3055_ = lean_ctor_get(v___y_3054_, 0);
v_isSharedCheck_3062_ = !lean_is_exclusive(v___y_3054_);
if (v_isSharedCheck_3062_ == 0)
{
v___x_3057_ = v___y_3054_;
v_isShared_3058_ = v_isSharedCheck_3062_;
goto v_resetjp_3056_;
}
else
{
lean_inc(v_a_3055_);
lean_dec(v___y_3054_);
v___x_3057_ = lean_box(0);
v_isShared_3058_ = v_isSharedCheck_3062_;
goto v_resetjp_3056_;
}
v_resetjp_3056_:
{
lean_object* v___x_3060_; 
if (v_isShared_3058_ == 0)
{
v___x_3060_ = v___x_3057_;
goto v_reusejp_3059_;
}
else
{
lean_object* v_reuseFailAlloc_3061_; 
v_reuseFailAlloc_3061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3061_, 0, v_a_3055_);
v___x_3060_ = v_reuseFailAlloc_3061_;
goto v_reusejp_3059_;
}
v_reusejp_3059_:
{
return v___x_3060_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__3___boxed(lean_object* v___x_3072_, lean_object* v_preDefs_3073_, lean_object* v___x_3074_, lean_object* v_termMeasure_x3fs_3075_, lean_object* v___x_3076_, lean_object* v___x_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_){
_start:
{
lean_object* v_res_3084_; 
v_res_3084_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__3(v___x_3072_, v_preDefs_3073_, v___x_3074_, v_termMeasure_x3fs_3075_, v___x_3076_, v___x_3077_, v___y_3078_, v___y_3079_, v___y_3080_, v___y_3081_, v___y_3082_);
lean_dec(v___x_3077_);
return v_res_3084_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__15_spec__21___redArg___closed__0(void){
_start:
{
lean_object* v___x_3085_; 
v___x_3085_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3085_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__15_spec__21___redArg___closed__1(void){
_start:
{
lean_object* v___x_3086_; lean_object* v___x_3087_; 
v___x_3086_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__15_spec__21___redArg___closed__0, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__15_spec__21___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__15_spec__21___redArg___closed__0);
v___x_3087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3087_, 0, v___x_3086_);
return v___x_3087_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__15_spec__21___redArg___closed__2(void){
_start:
{
lean_object* v___x_3088_; lean_object* v___x_3089_; 
v___x_3088_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__15_spec__21___redArg___closed__1, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__15_spec__21___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__15_spec__21___redArg___closed__1);
v___x_3089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3089_, 0, v___x_3088_);
lean_ctor_set(v___x_3089_, 1, v___x_3088_);
return v___x_3089_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__15_spec__21___redArg___closed__3(void){
_start:
{
lean_object* v___x_3090_; lean_object* v___x_3091_; 
v___x_3090_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__15_spec__21___redArg___closed__1, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__15_spec__21___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__15_spec__21___redArg___closed__1);
v___x_3091_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3091_, 0, v___x_3090_);
lean_ctor_set(v___x_3091_, 1, v___x_3090_);
lean_ctor_set(v___x_3091_, 2, v___x_3090_);
lean_ctor_set(v___x_3091_, 3, v___x_3090_);
lean_ctor_set(v___x_3091_, 4, v___x_3090_);
lean_ctor_set(v___x_3091_, 5, v___x_3090_);
return v___x_3091_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__15_spec__21___redArg(lean_object* v_env_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_){
_start:
{
lean_object* v___x_3096_; lean_object* v_nextMacroScope_3097_; lean_object* v_ngen_3098_; lean_object* v_auxDeclNGen_3099_; lean_object* v_traceState_3100_; lean_object* v_messages_3101_; lean_object* v_infoState_3102_; lean_object* v_snapshotTasks_3103_; lean_object* v___x_3105_; uint8_t v_isShared_3106_; uint8_t v_isSharedCheck_3129_; 
v___x_3096_ = lean_st_ref_take(v___y_3094_);
v_nextMacroScope_3097_ = lean_ctor_get(v___x_3096_, 1);
v_ngen_3098_ = lean_ctor_get(v___x_3096_, 2);
v_auxDeclNGen_3099_ = lean_ctor_get(v___x_3096_, 3);
v_traceState_3100_ = lean_ctor_get(v___x_3096_, 4);
v_messages_3101_ = lean_ctor_get(v___x_3096_, 6);
v_infoState_3102_ = lean_ctor_get(v___x_3096_, 7);
v_snapshotTasks_3103_ = lean_ctor_get(v___x_3096_, 8);
v_isSharedCheck_3129_ = !lean_is_exclusive(v___x_3096_);
if (v_isSharedCheck_3129_ == 0)
{
lean_object* v_unused_3130_; lean_object* v_unused_3131_; 
v_unused_3130_ = lean_ctor_get(v___x_3096_, 5);
lean_dec(v_unused_3130_);
v_unused_3131_ = lean_ctor_get(v___x_3096_, 0);
lean_dec(v_unused_3131_);
v___x_3105_ = v___x_3096_;
v_isShared_3106_ = v_isSharedCheck_3129_;
goto v_resetjp_3104_;
}
else
{
lean_inc(v_snapshotTasks_3103_);
lean_inc(v_infoState_3102_);
lean_inc(v_messages_3101_);
lean_inc(v_traceState_3100_);
lean_inc(v_auxDeclNGen_3099_);
lean_inc(v_ngen_3098_);
lean_inc(v_nextMacroScope_3097_);
lean_dec(v___x_3096_);
v___x_3105_ = lean_box(0);
v_isShared_3106_ = v_isSharedCheck_3129_;
goto v_resetjp_3104_;
}
v_resetjp_3104_:
{
lean_object* v___x_3107_; lean_object* v___x_3109_; 
v___x_3107_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__15_spec__21___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__15_spec__21___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__15_spec__21___redArg___closed__2);
if (v_isShared_3106_ == 0)
{
lean_ctor_set(v___x_3105_, 5, v___x_3107_);
lean_ctor_set(v___x_3105_, 0, v_env_3092_);
v___x_3109_ = v___x_3105_;
goto v_reusejp_3108_;
}
else
{
lean_object* v_reuseFailAlloc_3128_; 
v_reuseFailAlloc_3128_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3128_, 0, v_env_3092_);
lean_ctor_set(v_reuseFailAlloc_3128_, 1, v_nextMacroScope_3097_);
lean_ctor_set(v_reuseFailAlloc_3128_, 2, v_ngen_3098_);
lean_ctor_set(v_reuseFailAlloc_3128_, 3, v_auxDeclNGen_3099_);
lean_ctor_set(v_reuseFailAlloc_3128_, 4, v_traceState_3100_);
lean_ctor_set(v_reuseFailAlloc_3128_, 5, v___x_3107_);
lean_ctor_set(v_reuseFailAlloc_3128_, 6, v_messages_3101_);
lean_ctor_set(v_reuseFailAlloc_3128_, 7, v_infoState_3102_);
lean_ctor_set(v_reuseFailAlloc_3128_, 8, v_snapshotTasks_3103_);
v___x_3109_ = v_reuseFailAlloc_3128_;
goto v_reusejp_3108_;
}
v_reusejp_3108_:
{
lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v_mctx_3112_; lean_object* v_zetaDeltaFVarIds_3113_; lean_object* v_postponed_3114_; lean_object* v_diag_3115_; lean_object* v___x_3117_; uint8_t v_isShared_3118_; uint8_t v_isSharedCheck_3126_; 
v___x_3110_ = lean_st_ref_set(v___y_3094_, v___x_3109_);
v___x_3111_ = lean_st_ref_take(v___y_3093_);
v_mctx_3112_ = lean_ctor_get(v___x_3111_, 0);
v_zetaDeltaFVarIds_3113_ = lean_ctor_get(v___x_3111_, 2);
v_postponed_3114_ = lean_ctor_get(v___x_3111_, 3);
v_diag_3115_ = lean_ctor_get(v___x_3111_, 4);
v_isSharedCheck_3126_ = !lean_is_exclusive(v___x_3111_);
if (v_isSharedCheck_3126_ == 0)
{
lean_object* v_unused_3127_; 
v_unused_3127_ = lean_ctor_get(v___x_3111_, 1);
lean_dec(v_unused_3127_);
v___x_3117_ = v___x_3111_;
v_isShared_3118_ = v_isSharedCheck_3126_;
goto v_resetjp_3116_;
}
else
{
lean_inc(v_diag_3115_);
lean_inc(v_postponed_3114_);
lean_inc(v_zetaDeltaFVarIds_3113_);
lean_inc(v_mctx_3112_);
lean_dec(v___x_3111_);
v___x_3117_ = lean_box(0);
v_isShared_3118_ = v_isSharedCheck_3126_;
goto v_resetjp_3116_;
}
v_resetjp_3116_:
{
lean_object* v___x_3119_; lean_object* v___x_3121_; 
v___x_3119_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__15_spec__21___redArg___closed__3, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__15_spec__21___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__15_spec__21___redArg___closed__3);
if (v_isShared_3118_ == 0)
{
lean_ctor_set(v___x_3117_, 1, v___x_3119_);
v___x_3121_ = v___x_3117_;
goto v_reusejp_3120_;
}
else
{
lean_object* v_reuseFailAlloc_3125_; 
v_reuseFailAlloc_3125_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3125_, 0, v_mctx_3112_);
lean_ctor_set(v_reuseFailAlloc_3125_, 1, v___x_3119_);
lean_ctor_set(v_reuseFailAlloc_3125_, 2, v_zetaDeltaFVarIds_3113_);
lean_ctor_set(v_reuseFailAlloc_3125_, 3, v_postponed_3114_);
lean_ctor_set(v_reuseFailAlloc_3125_, 4, v_diag_3115_);
v___x_3121_ = v_reuseFailAlloc_3125_;
goto v_reusejp_3120_;
}
v_reusejp_3120_:
{
lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; 
v___x_3122_ = lean_st_ref_set(v___y_3093_, v___x_3121_);
v___x_3123_ = lean_box(0);
v___x_3124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3124_, 0, v___x_3123_);
return v___x_3124_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__15_spec__21___redArg___boxed(lean_object* v_env_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_){
_start:
{
lean_object* v_res_3136_; 
v_res_3136_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__15_spec__21___redArg(v_env_3132_, v___y_3133_, v___y_3134_);
lean_dec(v___y_3134_);
lean_dec(v___y_3133_);
return v_res_3136_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__15___redArg(lean_object* v_env_3137_, lean_object* v_x_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_){
_start:
{
lean_object* v___x_3145_; lean_object* v_env_3146_; lean_object* v_a_3148_; lean_object* v___x_3158_; lean_object* v___x_3159_; 
v___x_3145_ = lean_st_ref_get(v___y_3143_);
v_env_3146_ = lean_ctor_get(v___x_3145_, 0);
lean_inc_ref(v_env_3146_);
lean_dec(v___x_3145_);
v___x_3158_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__15_spec__21___redArg(v_env_3137_, v___y_3141_, v___y_3143_);
lean_dec_ref(v___x_3158_);
lean_inc(v___y_3143_);
lean_inc(v___y_3141_);
v___x_3159_ = lean_apply_6(v_x_3138_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_, lean_box(0));
if (lean_obj_tag(v___x_3159_) == 0)
{
lean_object* v_a_3160_; lean_object* v___x_3161_; lean_object* v___x_3163_; uint8_t v_isShared_3164_; uint8_t v_isSharedCheck_3168_; 
v_a_3160_ = lean_ctor_get(v___x_3159_, 0);
lean_inc(v_a_3160_);
lean_dec_ref(v___x_3159_);
v___x_3161_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__15_spec__21___redArg(v_env_3146_, v___y_3141_, v___y_3143_);
lean_dec(v___y_3143_);
lean_dec(v___y_3141_);
v_isSharedCheck_3168_ = !lean_is_exclusive(v___x_3161_);
if (v_isSharedCheck_3168_ == 0)
{
lean_object* v_unused_3169_; 
v_unused_3169_ = lean_ctor_get(v___x_3161_, 0);
lean_dec(v_unused_3169_);
v___x_3163_ = v___x_3161_;
v_isShared_3164_ = v_isSharedCheck_3168_;
goto v_resetjp_3162_;
}
else
{
lean_dec(v___x_3161_);
v___x_3163_ = lean_box(0);
v_isShared_3164_ = v_isSharedCheck_3168_;
goto v_resetjp_3162_;
}
v_resetjp_3162_:
{
lean_object* v___x_3166_; 
if (v_isShared_3164_ == 0)
{
lean_ctor_set(v___x_3163_, 0, v_a_3160_);
v___x_3166_ = v___x_3163_;
goto v_reusejp_3165_;
}
else
{
lean_object* v_reuseFailAlloc_3167_; 
v_reuseFailAlloc_3167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3167_, 0, v_a_3160_);
v___x_3166_ = v_reuseFailAlloc_3167_;
goto v_reusejp_3165_;
}
v_reusejp_3165_:
{
return v___x_3166_;
}
}
}
else
{
lean_object* v_a_3170_; 
v_a_3170_ = lean_ctor_get(v___x_3159_, 0);
lean_inc(v_a_3170_);
lean_dec_ref(v___x_3159_);
v_a_3148_ = v_a_3170_;
goto v___jp_3147_;
}
v___jp_3147_:
{
lean_object* v___x_3149_; lean_object* v___x_3151_; uint8_t v_isShared_3152_; uint8_t v_isSharedCheck_3156_; 
v___x_3149_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__15_spec__21___redArg(v_env_3146_, v___y_3141_, v___y_3143_);
lean_dec(v___y_3143_);
lean_dec(v___y_3141_);
v_isSharedCheck_3156_ = !lean_is_exclusive(v___x_3149_);
if (v_isSharedCheck_3156_ == 0)
{
lean_object* v_unused_3157_; 
v_unused_3157_ = lean_ctor_get(v___x_3149_, 0);
lean_dec(v_unused_3157_);
v___x_3151_ = v___x_3149_;
v_isShared_3152_ = v_isSharedCheck_3156_;
goto v_resetjp_3150_;
}
else
{
lean_dec(v___x_3149_);
v___x_3151_ = lean_box(0);
v_isShared_3152_ = v_isSharedCheck_3156_;
goto v_resetjp_3150_;
}
v_resetjp_3150_:
{
lean_object* v___x_3154_; 
if (v_isShared_3152_ == 0)
{
lean_ctor_set_tag(v___x_3151_, 1);
lean_ctor_set(v___x_3151_, 0, v_a_3148_);
v___x_3154_ = v___x_3151_;
goto v_reusejp_3153_;
}
else
{
lean_object* v_reuseFailAlloc_3155_; 
v_reuseFailAlloc_3155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3155_, 0, v_a_3148_);
v___x_3154_ = v_reuseFailAlloc_3155_;
goto v_reusejp_3153_;
}
v_reusejp_3153_:
{
return v___x_3154_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__15___redArg___boxed(lean_object* v_env_3171_, lean_object* v_x_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_){
_start:
{
lean_object* v_res_3179_; 
v_res_3179_ = l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__15___redArg(v_env_3171_, v_x_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_);
return v_res_3179_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos(lean_object* v_preDefs_3180_, lean_object* v_termMeasure_x3fs_3181_, lean_object* v_a_3182_, lean_object* v_a_3183_, lean_object* v_a_3184_, lean_object* v_a_3185_, lean_object* v_a_3186_){
_start:
{
lean_object* v___x_3188_; lean_object* v_env_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___f_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; 
v___x_3188_ = lean_st_ref_get(v_a_3186_);
v_env_3189_ = lean_ctor_get(v___x_3188_, 0);
lean_inc_ref(v_env_3189_);
lean_dec(v___x_3188_);
v___x_3190_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_3191_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9___redArg___closed__0, &l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9___redArg___closed__0_once, _init_l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9___redArg___closed__0);
v___x_3192_ = lean_unsigned_to_nat(0u);
v___x_3193_ = lean_array_get_size(v_preDefs_3180_);
v___f_3194_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__3___boxed), 12, 6);
lean_closure_set(v___f_3194_, 0, v___x_3190_);
lean_closure_set(v___f_3194_, 1, v_preDefs_3180_);
lean_closure_set(v___f_3194_, 2, v___x_3192_);
lean_closure_set(v___f_3194_, 3, v_termMeasure_x3fs_3181_);
lean_closure_set(v___f_3194_, 4, v___x_3191_);
lean_closure_set(v___f_3194_, 5, v___x_3193_);
v___x_3195_ = l_Lean_Environment_unlockAsync(v_env_3189_);
v___x_3196_ = l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__15___redArg(v___x_3195_, v___f_3194_, v_a_3182_, v_a_3183_, v_a_3184_, v_a_3185_, v_a_3186_);
return v___x_3196_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___boxed(lean_object* v_preDefs_3197_, lean_object* v_termMeasure_x3fs_3198_, lean_object* v_a_3199_, lean_object* v_a_3200_, lean_object* v_a_3201_, lean_object* v_a_3202_, lean_object* v_a_3203_, lean_object* v_a_3204_){
_start:
{
lean_object* v_res_3205_; 
v_res_3205_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos(v_preDefs_3197_, v_termMeasure_x3fs_3198_, v_a_3199_, v_a_3200_, v_a_3201_, v_a_3202_, v_a_3203_);
return v_res_3205_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1(lean_object* v_fnNames_3206_, lean_object* v_numSectionVars_3207_, size_t v_sz_3208_, size_t v_i_3209_, lean_object* v_bs_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_){
_start:
{
lean_object* v___x_3217_; 
v___x_3217_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1___redArg(v_fnNames_3206_, v_numSectionVars_3207_, v_sz_3208_, v_i_3209_, v_bs_3210_, v___y_3214_, v___y_3215_);
return v___x_3217_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1___boxed(lean_object* v_fnNames_3218_, lean_object* v_numSectionVars_3219_, lean_object* v_sz_3220_, lean_object* v_i_3221_, lean_object* v_bs_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_){
_start:
{
size_t v_sz_boxed_3229_; size_t v_i_boxed_3230_; lean_object* v_res_3231_; 
v_sz_boxed_3229_ = lean_unbox_usize(v_sz_3220_);
lean_dec(v_sz_3220_);
v_i_boxed_3230_ = lean_unbox_usize(v_i_3221_);
lean_dec(v_i_3221_);
v_res_3231_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1(v_fnNames_3218_, v_numSectionVars_3219_, v_sz_boxed_3229_, v_i_boxed_3230_, v_bs_3222_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_, v___y_3227_);
lean_dec(v___y_3225_);
lean_dec_ref(v___y_3224_);
lean_dec(v___y_3223_);
return v_res_3231_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4(lean_object* v_fst_3232_, lean_object* v_as_3233_, lean_object* v_i_3234_, lean_object* v_j_3235_, lean_object* v_inv_3236_, lean_object* v_bs_3237_){
_start:
{
lean_object* v___x_3238_; 
v___x_3238_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg(v_fst_3232_, v_as_3233_, v_i_3234_, v_j_3235_, v_bs_3237_);
return v___x_3238_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___boxed(lean_object* v_fst_3239_, lean_object* v_as_3240_, lean_object* v_i_3241_, lean_object* v_j_3242_, lean_object* v_inv_3243_, lean_object* v_bs_3244_){
_start:
{
lean_object* v_res_3245_; 
v_res_3245_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4(v_fst_3239_, v_as_3240_, v_i_3241_, v_j_3242_, v_inv_3243_, v_bs_3244_);
lean_dec_ref(v_as_3240_);
lean_dec_ref(v_fst_3239_);
return v_res_3245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5_spec__6(lean_object* v_00_u03b1_3246_, lean_object* v_lctx_3247_, lean_object* v_localInsts_3248_, lean_object* v_x_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_){
_start:
{
lean_object* v___x_3256_; 
v___x_3256_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5_spec__6___redArg(v_lctx_3247_, v_localInsts_3248_, v_x_3249_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_, v___y_3254_);
return v___x_3256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5_spec__6___boxed(lean_object* v_00_u03b1_3257_, lean_object* v_lctx_3258_, lean_object* v_localInsts_3259_, lean_object* v_x_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_){
_start:
{
lean_object* v_res_3267_; 
v_res_3267_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5_spec__6(v_00_u03b1_3257_, v_lctx_3258_, v_localInsts_3259_, v_x_3260_, v___y_3261_, v___y_3262_, v___y_3263_, v___y_3264_, v___y_3265_);
return v_res_3267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5(lean_object* v_00_u03b1_3268_, lean_object* v_fvarIds_3269_, lean_object* v_k_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_){
_start:
{
lean_object* v___x_3277_; 
v___x_3277_ = l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg(v_fvarIds_3269_, v_k_3270_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_, v___y_3275_);
return v___x_3277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___boxed(lean_object* v_00_u03b1_3278_, lean_object* v_fvarIds_3279_, lean_object* v_k_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_){
_start:
{
lean_object* v_res_3287_; 
v_res_3287_ = l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5(v_00_u03b1_3278_, v_fvarIds_3279_, v_k_3280_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_, v___y_3285_);
lean_dec_ref(v_fvarIds_3279_);
return v_res_3287_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__15(lean_object* v_a_3288_){
_start:
{
lean_object* v___x_3289_; 
v___x_3289_ = lean_nat_to_int(v_a_3288_);
return v___x_3289_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12(lean_object* v___x_3290_, lean_object* v_xs_3291_, lean_object* v_as_3292_, lean_object* v_i_3293_, lean_object* v_j_3294_, lean_object* v_inv_3295_, lean_object* v_bs_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_){
_start:
{
lean_object* v___x_3303_; 
v___x_3303_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg(v___x_3290_, v_xs_3291_, v_as_3292_, v_i_3293_, v_j_3294_, v_bs_3296_, v___y_3298_, v___y_3299_, v___y_3300_, v___y_3301_);
return v___x_3303_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___boxed(lean_object* v___x_3304_, lean_object* v_xs_3305_, lean_object* v_as_3306_, lean_object* v_i_3307_, lean_object* v_j_3308_, lean_object* v_inv_3309_, lean_object* v_bs_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_){
_start:
{
lean_object* v_res_3317_; 
v_res_3317_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12(v___x_3304_, v_xs_3305_, v_as_3306_, v_i_3307_, v_j_3308_, v_inv_3309_, v_bs_3310_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_);
lean_dec(v___y_3311_);
lean_dec_ref(v_as_3306_);
lean_dec_ref(v___x_3304_);
return v_res_3317_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__14(lean_object* v_as_3318_, size_t v_i_3319_, size_t v_stop_3320_, lean_object* v_b_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_){
_start:
{
lean_object* v___x_3328_; 
v___x_3328_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__14___redArg(v_as_3318_, v_i_3319_, v_stop_3320_, v_b_3321_, v___y_3325_, v___y_3326_);
return v___x_3328_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__14___boxed(lean_object* v_as_3329_, lean_object* v_i_3330_, lean_object* v_stop_3331_, lean_object* v_b_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_){
_start:
{
size_t v_i_boxed_3339_; size_t v_stop_boxed_3340_; lean_object* v_res_3341_; 
v_i_boxed_3339_ = lean_unbox_usize(v_i_3330_);
lean_dec(v_i_3330_);
v_stop_boxed_3340_ = lean_unbox_usize(v_stop_3331_);
lean_dec(v_stop_3331_);
v_res_3341_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__14(v_as_3329_, v_i_boxed_3339_, v_stop_boxed_3340_, v_b_3332_, v___y_3333_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_);
lean_dec(v___y_3335_);
lean_dec_ref(v___y_3334_);
lean_dec(v___y_3333_);
lean_dec_ref(v_as_3329_);
return v_res_3341_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__15_spec__21(lean_object* v_env_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_){
_start:
{
lean_object* v___x_3349_; 
v___x_3349_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__15_spec__21___redArg(v_env_3342_, v___y_3345_, v___y_3347_);
return v___x_3349_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__15_spec__21___boxed(lean_object* v_env_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_){
_start:
{
lean_object* v_res_3357_; 
v_res_3357_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__15_spec__21(v_env_3350_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_);
lean_dec(v___y_3355_);
lean_dec_ref(v___y_3354_);
lean_dec(v___y_3353_);
lean_dec_ref(v___y_3352_);
lean_dec(v___y_3351_);
return v_res_3357_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__15(lean_object* v_00_u03b1_3358_, lean_object* v_env_3359_, lean_object* v_x_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_){
_start:
{
lean_object* v___x_3367_; 
v___x_3367_ = l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__15___redArg(v_env_3359_, v_x_3360_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_);
return v___x_3367_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__15___boxed(lean_object* v_00_u03b1_3368_, lean_object* v_env_3369_, lean_object* v_x_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_){
_start:
{
lean_object* v_res_3377_; 
v_res_3377_ = l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__15(v_00_u03b1_3368_, v_env_3369_, v_x_3370_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_);
return v_res_3377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_reportTermMeasure_spec__0___redArg___lam__0(lean_object* v_k_3378_, lean_object* v_b_3379_, lean_object* v_c_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_){
_start:
{
lean_object* v___x_3386_; 
v___x_3386_ = lean_apply_7(v_k_3378_, v_b_3379_, v_c_3380_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_, lean_box(0));
return v___x_3386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_reportTermMeasure_spec__0___redArg___lam__0___boxed(lean_object* v_k_3387_, lean_object* v_b_3388_, lean_object* v_c_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_){
_start:
{
lean_object* v_res_3395_; 
v_res_3395_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_reportTermMeasure_spec__0___redArg___lam__0(v_k_3387_, v_b_3388_, v_c_3389_, v___y_3390_, v___y_3391_, v___y_3392_, v___y_3393_);
return v_res_3395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_reportTermMeasure_spec__0___redArg(lean_object* v_e_3396_, lean_object* v_k_3397_, uint8_t v_cleanupAnnotations_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_){
_start:
{
lean_object* v___f_3404_; uint8_t v___x_3405_; uint8_t v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; 
v___f_3404_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_reportTermMeasure_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3404_, 0, v_k_3397_);
v___x_3405_ = 1;
v___x_3406_ = 0;
v___x_3407_ = lean_box(0);
v___x_3408_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_3396_, v___x_3405_, v___x_3406_, v___x_3405_, v___x_3406_, v___x_3407_, v___f_3404_, v_cleanupAnnotations_3398_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_);
if (lean_obj_tag(v___x_3408_) == 0)
{
lean_object* v_a_3409_; lean_object* v___x_3411_; uint8_t v_isShared_3412_; uint8_t v_isSharedCheck_3416_; 
v_a_3409_ = lean_ctor_get(v___x_3408_, 0);
v_isSharedCheck_3416_ = !lean_is_exclusive(v___x_3408_);
if (v_isSharedCheck_3416_ == 0)
{
v___x_3411_ = v___x_3408_;
v_isShared_3412_ = v_isSharedCheck_3416_;
goto v_resetjp_3410_;
}
else
{
lean_inc(v_a_3409_);
lean_dec(v___x_3408_);
v___x_3411_ = lean_box(0);
v_isShared_3412_ = v_isSharedCheck_3416_;
goto v_resetjp_3410_;
}
v_resetjp_3410_:
{
lean_object* v___x_3414_; 
if (v_isShared_3412_ == 0)
{
v___x_3414_ = v___x_3411_;
goto v_reusejp_3413_;
}
else
{
lean_object* v_reuseFailAlloc_3415_; 
v_reuseFailAlloc_3415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3415_, 0, v_a_3409_);
v___x_3414_ = v_reuseFailAlloc_3415_;
goto v_reusejp_3413_;
}
v_reusejp_3413_:
{
return v___x_3414_;
}
}
}
else
{
lean_object* v_a_3417_; lean_object* v___x_3419_; uint8_t v_isShared_3420_; uint8_t v_isSharedCheck_3424_; 
v_a_3417_ = lean_ctor_get(v___x_3408_, 0);
v_isSharedCheck_3424_ = !lean_is_exclusive(v___x_3408_);
if (v_isSharedCheck_3424_ == 0)
{
v___x_3419_ = v___x_3408_;
v_isShared_3420_ = v_isSharedCheck_3424_;
goto v_resetjp_3418_;
}
else
{
lean_inc(v_a_3417_);
lean_dec(v___x_3408_);
v___x_3419_ = lean_box(0);
v_isShared_3420_ = v_isSharedCheck_3424_;
goto v_resetjp_3418_;
}
v_resetjp_3418_:
{
lean_object* v___x_3422_; 
if (v_isShared_3420_ == 0)
{
v___x_3422_ = v___x_3419_;
goto v_reusejp_3421_;
}
else
{
lean_object* v_reuseFailAlloc_3423_; 
v_reuseFailAlloc_3423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3423_, 0, v_a_3417_);
v___x_3422_ = v_reuseFailAlloc_3423_;
goto v_reusejp_3421_;
}
v_reusejp_3421_:
{
return v___x_3422_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_reportTermMeasure_spec__0___redArg___boxed(lean_object* v_e_3425_, lean_object* v_k_3426_, lean_object* v_cleanupAnnotations_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3433_; lean_object* v_res_3434_; 
v_cleanupAnnotations_boxed_3433_ = lean_unbox(v_cleanupAnnotations_3427_);
v_res_3434_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_reportTermMeasure_spec__0___redArg(v_e_3425_, v_k_3426_, v_cleanupAnnotations_boxed_3433_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_);
return v_res_3434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_reportTermMeasure_spec__0(lean_object* v_00_u03b1_3435_, lean_object* v_e_3436_, lean_object* v_k_3437_, uint8_t v_cleanupAnnotations_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_){
_start:
{
lean_object* v___x_3444_; 
v___x_3444_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_reportTermMeasure_spec__0___redArg(v_e_3436_, v_k_3437_, v_cleanupAnnotations_3438_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_);
return v___x_3444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_reportTermMeasure_spec__0___boxed(lean_object* v_00_u03b1_3445_, lean_object* v_e_3446_, lean_object* v_k_3447_, lean_object* v_cleanupAnnotations_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3454_; lean_object* v_res_3455_; 
v_cleanupAnnotations_boxed_3454_ = lean_unbox(v_cleanupAnnotations_3448_);
v_res_3455_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_reportTermMeasure_spec__0(v_00_u03b1_3445_, v_e_3446_, v_k_3447_, v_cleanupAnnotations_boxed_3454_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_);
return v_res_3455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure___lam__0(lean_object* v___x_3456_, lean_object* v_recArgPos_3457_, lean_object* v_xs_3458_, lean_object* v_x_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_){
_start:
{
lean_object* v___x_3465_; uint8_t v___x_3466_; uint8_t v___x_3467_; uint8_t v___x_3468_; lean_object* v___x_3469_; 
v___x_3465_ = lean_array_get_borrowed(v___x_3456_, v_xs_3458_, v_recArgPos_3457_);
v___x_3466_ = 0;
v___x_3467_ = 1;
v___x_3468_ = 1;
lean_inc(v___x_3465_);
v___x_3469_ = l_Lean_Meta_mkLambdaFVars(v_xs_3458_, v___x_3465_, v___x_3466_, v___x_3467_, v___x_3466_, v___x_3467_, v___x_3468_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_);
return v___x_3469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure___lam__0___boxed(lean_object* v___x_3470_, lean_object* v_recArgPos_3471_, lean_object* v_xs_3472_, lean_object* v_x_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_){
_start:
{
lean_object* v_res_3479_; 
v_res_3479_ = l_Lean_Elab_Structural_reportTermMeasure___lam__0(v___x_3470_, v_recArgPos_3471_, v_xs_3472_, v_x_3473_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_);
lean_dec(v___y_3477_);
lean_dec_ref(v___y_3476_);
lean_dec(v___y_3475_);
lean_dec_ref(v___y_3474_);
lean_dec_ref(v_x_3473_);
lean_dec_ref(v_xs_3472_);
lean_dec(v_recArgPos_3471_);
return v_res_3479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure___lam__1(lean_object* v_xs_3480_, lean_object* v_x_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_){
_start:
{
lean_object* v___x_3487_; lean_object* v___x_3488_; 
v___x_3487_ = lean_array_get_size(v_xs_3480_);
v___x_3488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3488_, 0, v___x_3487_);
return v___x_3488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure___lam__1___boxed(lean_object* v_xs_3489_, lean_object* v_x_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_){
_start:
{
lean_object* v_res_3496_; 
v_res_3496_ = l_Lean_Elab_Structural_reportTermMeasure___lam__1(v_xs_3489_, v_x_3490_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_);
lean_dec(v___y_3494_);
lean_dec_ref(v___y_3493_);
lean_dec(v___y_3492_);
lean_dec_ref(v___y_3491_);
lean_dec_ref(v_x_3490_);
lean_dec_ref(v_xs_3489_);
return v_res_3496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure(lean_object* v_preDef_3508_, lean_object* v_recArgPos_3509_, lean_object* v_a_3510_, lean_object* v_a_3511_, lean_object* v_a_3512_, lean_object* v_a_3513_){
_start:
{
lean_object* v_termination_3515_; lean_object* v_terminationBy_x3f_x3f_3516_; 
v_termination_3515_ = lean_ctor_get(v_preDef_3508_, 8);
lean_inc_ref(v_termination_3515_);
v_terminationBy_x3f_x3f_3516_ = lean_ctor_get(v_termination_3515_, 1);
lean_inc(v_terminationBy_x3f_x3f_3516_);
if (lean_obj_tag(v_terminationBy_x3f_x3f_3516_) == 1)
{
lean_object* v_value_3517_; lean_object* v_extraParams_3518_; lean_object* v___x_3520_; uint8_t v_isShared_3521_; uint8_t v_isSharedCheck_3569_; 
v_value_3517_ = lean_ctor_get(v_preDef_3508_, 7);
lean_inc_ref(v_value_3517_);
lean_dec_ref(v_preDef_3508_);
v_extraParams_3518_ = lean_ctor_get(v_termination_3515_, 5);
v_isSharedCheck_3569_ = !lean_is_exclusive(v_termination_3515_);
if (v_isSharedCheck_3569_ == 0)
{
lean_object* v_unused_3570_; lean_object* v_unused_3571_; lean_object* v_unused_3572_; lean_object* v_unused_3573_; lean_object* v_unused_3574_; 
v_unused_3570_ = lean_ctor_get(v_termination_3515_, 4);
lean_dec(v_unused_3570_);
v_unused_3571_ = lean_ctor_get(v_termination_3515_, 3);
lean_dec(v_unused_3571_);
v_unused_3572_ = lean_ctor_get(v_termination_3515_, 2);
lean_dec(v_unused_3572_);
v_unused_3573_ = lean_ctor_get(v_termination_3515_, 1);
lean_dec(v_unused_3573_);
v_unused_3574_ = lean_ctor_get(v_termination_3515_, 0);
lean_dec(v_unused_3574_);
v___x_3520_ = v_termination_3515_;
v_isShared_3521_ = v_isSharedCheck_3569_;
goto v_resetjp_3519_;
}
else
{
lean_inc(v_extraParams_3518_);
lean_dec(v_termination_3515_);
v___x_3520_ = lean_box(0);
v_isShared_3521_ = v_isSharedCheck_3569_;
goto v_resetjp_3519_;
}
v_resetjp_3519_:
{
lean_object* v_val_3522_; lean_object* v___x_3523_; lean_object* v___f_3524_; uint8_t v___x_3525_; lean_object* v___x_3526_; 
v_val_3522_ = lean_ctor_get(v_terminationBy_x3f_x3f_3516_, 0);
lean_inc(v_val_3522_);
lean_dec_ref(v_terminationBy_x3f_x3f_3516_);
v___x_3523_ = l_Lean_instInhabitedExpr;
v___f_3524_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_reportTermMeasure___lam__0___boxed), 9, 2);
lean_closure_set(v___f_3524_, 0, v___x_3523_);
lean_closure_set(v___f_3524_, 1, v_recArgPos_3509_);
v___x_3525_ = 0;
lean_inc(v_a_3513_);
lean_inc_ref(v_a_3512_);
lean_inc(v_a_3511_);
lean_inc_ref(v_a_3510_);
lean_inc_ref(v_value_3517_);
v___x_3526_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_reportTermMeasure_spec__0___redArg(v_value_3517_, v___f_3524_, v___x_3525_, v_a_3510_, v_a_3511_, v_a_3512_, v_a_3513_);
if (lean_obj_tag(v___x_3526_) == 0)
{
lean_object* v_a_3527_; lean_object* v___f_3528_; lean_object* v___x_3529_; 
v_a_3527_ = lean_ctor_get(v___x_3526_, 0);
lean_inc(v_a_3527_);
lean_dec_ref(v___x_3526_);
v___f_3528_ = ((lean_object*)(l_Lean_Elab_Structural_reportTermMeasure___closed__0));
lean_inc(v_a_3513_);
lean_inc_ref(v_a_3512_);
lean_inc(v_a_3511_);
lean_inc_ref(v_a_3510_);
v___x_3529_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_reportTermMeasure_spec__0___redArg(v_value_3517_, v___f_3528_, v___x_3525_, v_a_3510_, v_a_3511_, v_a_3512_, v_a_3513_);
if (lean_obj_tag(v___x_3529_) == 0)
{
lean_object* v_a_3530_; lean_object* v___x_3531_; uint8_t v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; 
v_a_3530_ = lean_ctor_get(v___x_3529_, 0);
lean_inc(v_a_3530_);
lean_dec_ref(v___x_3529_);
v___x_3531_ = lean_box(0);
v___x_3532_ = 1;
v___x_3533_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3533_, 0, v___x_3531_);
lean_ctor_set(v___x_3533_, 1, v_a_3527_);
lean_ctor_set_uint8(v___x_3533_, sizeof(void*)*2, v___x_3532_);
lean_inc(v_a_3513_);
lean_inc_ref(v_a_3512_);
v___x_3534_ = l_Lean_Elab_TerminationMeasure_delab(v_a_3530_, v_extraParams_3518_, v___x_3533_, v_a_3510_, v_a_3511_, v_a_3512_, v_a_3513_);
lean_dec(v_a_3530_);
if (lean_obj_tag(v___x_3534_) == 0)
{
lean_object* v_a_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3540_; 
v_a_3535_ = lean_ctor_get(v___x_3534_, 0);
lean_inc(v_a_3535_);
lean_dec_ref(v___x_3534_);
v___x_3536_ = ((lean_object*)(l_Lean_Elab_Structural_reportTermMeasure___closed__5));
v___x_3537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3537_, 0, v___x_3536_);
lean_ctor_set(v___x_3537_, 1, v_a_3535_);
v___x_3538_ = lean_box(0);
if (v_isShared_3521_ == 0)
{
lean_ctor_set(v___x_3520_, 5, v___x_3538_);
lean_ctor_set(v___x_3520_, 4, v___x_3538_);
lean_ctor_set(v___x_3520_, 3, v___x_3538_);
lean_ctor_set(v___x_3520_, 2, v___x_3538_);
lean_ctor_set(v___x_3520_, 1, v___x_3538_);
lean_ctor_set(v___x_3520_, 0, v___x_3537_);
v___x_3540_ = v___x_3520_;
goto v_reusejp_3539_;
}
else
{
lean_object* v_reuseFailAlloc_3544_; 
v_reuseFailAlloc_3544_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3544_, 0, v___x_3537_);
lean_ctor_set(v_reuseFailAlloc_3544_, 1, v___x_3538_);
lean_ctor_set(v_reuseFailAlloc_3544_, 2, v___x_3538_);
lean_ctor_set(v_reuseFailAlloc_3544_, 3, v___x_3538_);
lean_ctor_set(v_reuseFailAlloc_3544_, 4, v___x_3538_);
lean_ctor_set(v_reuseFailAlloc_3544_, 5, v___x_3538_);
v___x_3540_ = v_reuseFailAlloc_3544_;
goto v_reusejp_3539_;
}
v_reusejp_3539_:
{
lean_object* v___x_3541_; uint8_t v___x_3542_; lean_object* v___x_3543_; 
v___x_3541_ = ((lean_object*)(l_Lean_Elab_Structural_reportTermMeasure___closed__6));
v___x_3542_ = 4;
v___x_3543_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_val_3522_, v___x_3540_, v___x_3538_, v___x_3541_, v___x_3538_, v___x_3542_, v_a_3512_, v_a_3513_);
return v___x_3543_;
}
}
else
{
lean_object* v_a_3545_; lean_object* v___x_3547_; uint8_t v_isShared_3548_; uint8_t v_isSharedCheck_3552_; 
lean_dec(v_val_3522_);
lean_del_object(v___x_3520_);
lean_dec(v_a_3513_);
lean_dec_ref(v_a_3512_);
v_a_3545_ = lean_ctor_get(v___x_3534_, 0);
v_isSharedCheck_3552_ = !lean_is_exclusive(v___x_3534_);
if (v_isSharedCheck_3552_ == 0)
{
v___x_3547_ = v___x_3534_;
v_isShared_3548_ = v_isSharedCheck_3552_;
goto v_resetjp_3546_;
}
else
{
lean_inc(v_a_3545_);
lean_dec(v___x_3534_);
v___x_3547_ = lean_box(0);
v_isShared_3548_ = v_isSharedCheck_3552_;
goto v_resetjp_3546_;
}
v_resetjp_3546_:
{
lean_object* v___x_3550_; 
if (v_isShared_3548_ == 0)
{
v___x_3550_ = v___x_3547_;
goto v_reusejp_3549_;
}
else
{
lean_object* v_reuseFailAlloc_3551_; 
v_reuseFailAlloc_3551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3551_, 0, v_a_3545_);
v___x_3550_ = v_reuseFailAlloc_3551_;
goto v_reusejp_3549_;
}
v_reusejp_3549_:
{
return v___x_3550_;
}
}
}
}
else
{
lean_object* v_a_3553_; lean_object* v___x_3555_; uint8_t v_isShared_3556_; uint8_t v_isSharedCheck_3560_; 
lean_dec(v_a_3527_);
lean_dec(v_val_3522_);
lean_del_object(v___x_3520_);
lean_dec(v_extraParams_3518_);
lean_dec(v_a_3513_);
lean_dec_ref(v_a_3512_);
lean_dec(v_a_3511_);
lean_dec_ref(v_a_3510_);
v_a_3553_ = lean_ctor_get(v___x_3529_, 0);
v_isSharedCheck_3560_ = !lean_is_exclusive(v___x_3529_);
if (v_isSharedCheck_3560_ == 0)
{
v___x_3555_ = v___x_3529_;
v_isShared_3556_ = v_isSharedCheck_3560_;
goto v_resetjp_3554_;
}
else
{
lean_inc(v_a_3553_);
lean_dec(v___x_3529_);
v___x_3555_ = lean_box(0);
v_isShared_3556_ = v_isSharedCheck_3560_;
goto v_resetjp_3554_;
}
v_resetjp_3554_:
{
lean_object* v___x_3558_; 
if (v_isShared_3556_ == 0)
{
v___x_3558_ = v___x_3555_;
goto v_reusejp_3557_;
}
else
{
lean_object* v_reuseFailAlloc_3559_; 
v_reuseFailAlloc_3559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3559_, 0, v_a_3553_);
v___x_3558_ = v_reuseFailAlloc_3559_;
goto v_reusejp_3557_;
}
v_reusejp_3557_:
{
return v___x_3558_;
}
}
}
}
else
{
lean_object* v_a_3561_; lean_object* v___x_3563_; uint8_t v_isShared_3564_; uint8_t v_isSharedCheck_3568_; 
lean_dec(v_val_3522_);
lean_del_object(v___x_3520_);
lean_dec(v_extraParams_3518_);
lean_dec_ref(v_value_3517_);
lean_dec(v_a_3513_);
lean_dec_ref(v_a_3512_);
lean_dec(v_a_3511_);
lean_dec_ref(v_a_3510_);
v_a_3561_ = lean_ctor_get(v___x_3526_, 0);
v_isSharedCheck_3568_ = !lean_is_exclusive(v___x_3526_);
if (v_isSharedCheck_3568_ == 0)
{
v___x_3563_ = v___x_3526_;
v_isShared_3564_ = v_isSharedCheck_3568_;
goto v_resetjp_3562_;
}
else
{
lean_inc(v_a_3561_);
lean_dec(v___x_3526_);
v___x_3563_ = lean_box(0);
v_isShared_3564_ = v_isSharedCheck_3568_;
goto v_resetjp_3562_;
}
v_resetjp_3562_:
{
lean_object* v___x_3566_; 
if (v_isShared_3564_ == 0)
{
v___x_3566_ = v___x_3563_;
goto v_reusejp_3565_;
}
else
{
lean_object* v_reuseFailAlloc_3567_; 
v_reuseFailAlloc_3567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3567_, 0, v_a_3561_);
v___x_3566_ = v_reuseFailAlloc_3567_;
goto v_reusejp_3565_;
}
v_reusejp_3565_:
{
return v___x_3566_;
}
}
}
}
}
else
{
lean_object* v___x_3575_; lean_object* v___x_3576_; 
lean_dec(v_terminationBy_x3f_x3f_3516_);
lean_dec_ref(v_termination_3515_);
lean_dec(v_a_3513_);
lean_dec_ref(v_a_3512_);
lean_dec(v_a_3511_);
lean_dec_ref(v_a_3510_);
lean_dec(v_recArgPos_3509_);
lean_dec_ref(v_preDef_3508_);
v___x_3575_ = lean_box(0);
v___x_3576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3576_, 0, v___x_3575_);
return v___x_3576_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reportTermMeasure___boxed(lean_object* v_preDef_3577_, lean_object* v_recArgPos_3578_, lean_object* v_a_3579_, lean_object* v_a_3580_, lean_object* v_a_3581_, lean_object* v_a_3582_, lean_object* v_a_3583_){
_start:
{
lean_object* v_res_3584_; 
v_res_3584_ = l_Lean_Elab_Structural_reportTermMeasure(v_preDef_3577_, v_recArgPos_3578_, v_a_3579_, v_a_3580_, v_a_3581_, v_a_3582_);
return v_res_3584_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___redArg(lean_object* v_as_3585_, size_t v_sz_3586_, size_t v_i_3587_, lean_object* v_b_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_){
_start:
{
uint8_t v___x_3594_; 
v___x_3594_ = lean_usize_dec_lt(v_i_3587_, v_sz_3586_);
if (v___x_3594_ == 0)
{
lean_object* v___x_3595_; 
lean_dec(v___y_3592_);
lean_dec_ref(v___y_3591_);
lean_dec(v___y_3590_);
lean_dec_ref(v___y_3589_);
v___x_3595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3595_, 0, v_b_3588_);
return v___x_3595_;
}
else
{
lean_object* v_a_3596_; lean_object* v_declName_3597_; lean_object* v___x_3598_; 
v_a_3596_ = lean_array_uget_borrowed(v_as_3585_, v_i_3587_);
v_declName_3597_ = lean_ctor_get(v_a_3596_, 3);
lean_inc_ref(v___y_3591_);
lean_inc(v_declName_3597_);
v___x_3598_ = l_Lean_enableRealizationsForConst(v_declName_3597_, v___y_3591_, v___y_3592_);
if (lean_obj_tag(v___x_3598_) == 0)
{
lean_object* v___x_3599_; 
lean_dec_ref(v___x_3598_);
lean_inc(v___y_3592_);
lean_inc_ref(v___y_3591_);
lean_inc(v___y_3590_);
lean_inc_ref(v___y_3589_);
lean_inc(v_declName_3597_);
v___x_3599_ = l_Lean_Meta_generateEagerEqns(v_declName_3597_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_);
if (lean_obj_tag(v___x_3599_) == 0)
{
lean_object* v___x_3600_; size_t v___x_3601_; size_t v___x_3602_; 
lean_dec_ref(v___x_3599_);
v___x_3600_ = lean_box(0);
v___x_3601_ = ((size_t)1ULL);
v___x_3602_ = lean_usize_add(v_i_3587_, v___x_3601_);
v_i_3587_ = v___x_3602_;
v_b_3588_ = v___x_3600_;
goto _start;
}
else
{
lean_dec(v___y_3592_);
lean_dec_ref(v___y_3591_);
lean_dec(v___y_3590_);
lean_dec_ref(v___y_3589_);
return v___x_3599_;
}
}
else
{
lean_dec(v___y_3592_);
lean_dec_ref(v___y_3591_);
lean_dec(v___y_3590_);
lean_dec_ref(v___y_3589_);
return v___x_3598_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___redArg___boxed(lean_object* v_as_3604_, lean_object* v_sz_3605_, lean_object* v_i_3606_, lean_object* v_b_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_){
_start:
{
size_t v_sz_boxed_3613_; size_t v_i_boxed_3614_; lean_object* v_res_3615_; 
v_sz_boxed_3613_ = lean_unbox_usize(v_sz_3605_);
lean_dec(v_sz_3605_);
v_i_boxed_3614_ = lean_unbox_usize(v_i_3606_);
lean_dec(v_i_3606_);
v_res_3615_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___redArg(v_as_3604_, v_sz_boxed_3613_, v_i_boxed_3614_, v_b_3607_, v___y_3608_, v___y_3609_, v___y_3610_, v___y_3611_);
lean_dec_ref(v_as_3604_);
return v_res_3615_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4___lam__0(lean_object* v___x_3616_, lean_object* v_e_3617_){
_start:
{
lean_object* v___x_3618_; lean_object* v___x_3619_; 
v___x_3618_ = l_Lean_indentD(v_e_3617_);
v___x_3619_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3619_, 0, v___x_3616_);
lean_ctor_set(v___x_3619_, 1, v___x_3618_);
return v___x_3619_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4___lam__1(lean_object* v_docCtx_3620_, lean_object* v_a_3621_, uint8_t v___x_3622_, lean_object* v___x_3623_, uint8_t v___x_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_){
_start:
{
lean_object* v___x_3632_; 
v___x_3632_ = l_Lean_Elab_addNonRec(v_docCtx_3620_, v_a_3621_, v___x_3622_, v___x_3623_, v___x_3624_, v___x_3622_, v___x_3624_, v___y_3625_, v___y_3626_, v___y_3627_, v___y_3628_, v___y_3629_, v___y_3630_);
return v___x_3632_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4___lam__1___boxed(lean_object* v_docCtx_3633_, lean_object* v_a_3634_, lean_object* v___x_3635_, lean_object* v___x_3636_, lean_object* v___x_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_){
_start:
{
uint8_t v___x_10136__boxed_3645_; uint8_t v___x_10138__boxed_3646_; lean_object* v_res_3647_; 
v___x_10136__boxed_3645_ = lean_unbox(v___x_3635_);
v___x_10138__boxed_3646_ = lean_unbox(v___x_3637_);
v_res_3647_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4___lam__1(v_docCtx_3633_, v_a_3634_, v___x_10136__boxed_3645_, v___x_3636_, v___x_10138__boxed_3646_, v___y_3638_, v___y_3639_, v___y_3640_, v___y_3641_, v___y_3642_, v___y_3643_);
return v_res_3647_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4___closed__1(void){
_start:
{
lean_object* v___x_3649_; lean_object* v___x_3650_; 
v___x_3649_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4___closed__0));
v___x_3650_ = l_Lean_stringToMessageData(v___x_3649_);
return v___x_3650_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4___closed__2(void){
_start:
{
lean_object* v___x_3651_; lean_object* v___f_3652_; 
v___x_3651_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4___closed__1);
v___f_3652_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4___lam__0), 2, 1);
lean_closure_set(v___f_3652_, 0, v___x_3651_);
return v___f_3652_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4(lean_object* v_names_3653_, lean_object* v_docCtx_3654_, lean_object* v_as_3655_, size_t v_i_3656_, size_t v_stop_3657_, lean_object* v_b_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_, lean_object* v___y_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_){
_start:
{
uint8_t v___x_3666_; 
v___x_3666_ = lean_usize_dec_eq(v_i_3656_, v_stop_3657_);
if (v___x_3666_ == 0)
{
lean_object* v___x_3667_; lean_object* v___x_3668_; 
v___x_3667_ = lean_array_uget_borrowed(v_as_3655_, v_i_3656_);
lean_inc(v___y_3664_);
lean_inc_ref(v___y_3663_);
lean_inc(v___x_3667_);
v___x_3668_ = l_Lean_Elab_eraseRecAppSyntax(v___x_3667_, v___y_3663_, v___y_3664_);
if (lean_obj_tag(v___x_3668_) == 0)
{
lean_object* v_a_3669_; lean_object* v___f_3670_; lean_object* v___x_3671_; uint8_t v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___f_3675_; lean_object* v___x_3676_; 
v_a_3669_ = lean_ctor_get(v___x_3668_, 0);
lean_inc(v_a_3669_);
lean_dec_ref(v___x_3668_);
v___f_3670_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4___closed__2, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4___closed__2);
lean_inc_ref(v_names_3653_);
v___x_3671_ = lean_array_to_list(v_names_3653_);
v___x_3672_ = 1;
v___x_3673_ = lean_box(v___x_3666_);
v___x_3674_ = lean_box(v___x_3672_);
lean_inc(v___y_3660_);
lean_inc_ref(v___y_3659_);
lean_inc_ref(v_docCtx_3654_);
v___f_3675_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4___lam__1___boxed), 12, 7);
lean_closure_set(v___f_3675_, 0, v_docCtx_3654_);
lean_closure_set(v___f_3675_, 1, v_a_3669_);
lean_closure_set(v___f_3675_, 2, v___x_3673_);
lean_closure_set(v___f_3675_, 3, v___x_3671_);
lean_closure_set(v___f_3675_, 4, v___x_3674_);
lean_closure_set(v___f_3675_, 5, v___y_3659_);
lean_closure_set(v___f_3675_, 6, v___y_3660_);
lean_inc(v___y_3664_);
lean_inc_ref(v___y_3663_);
lean_inc(v___y_3662_);
lean_inc_ref(v___y_3661_);
v___x_3676_ = l_Lean_Meta_mapErrorImp___redArg(v___f_3675_, v___f_3670_, v___y_3661_, v___y_3662_, v___y_3663_, v___y_3664_);
if (lean_obj_tag(v___x_3676_) == 0)
{
if (lean_obj_tag(v___x_3676_) == 0)
{
lean_object* v_a_3677_; size_t v___x_3678_; size_t v___x_3679_; 
v_a_3677_ = lean_ctor_get(v___x_3676_, 0);
lean_inc(v_a_3677_);
lean_dec_ref(v___x_3676_);
v___x_3678_ = ((size_t)1ULL);
v___x_3679_ = lean_usize_add(v_i_3656_, v___x_3678_);
v_i_3656_ = v___x_3679_;
v_b_3658_ = v_a_3677_;
goto _start;
}
else
{
lean_dec(v___y_3664_);
lean_dec_ref(v___y_3663_);
lean_dec(v___y_3662_);
lean_dec_ref(v___y_3661_);
lean_dec(v___y_3660_);
lean_dec_ref(v___y_3659_);
lean_dec_ref(v_docCtx_3654_);
lean_dec_ref(v_names_3653_);
return v___x_3676_;
}
}
else
{
lean_object* v_a_3681_; lean_object* v___x_3683_; uint8_t v_isShared_3684_; uint8_t v_isSharedCheck_3688_; 
lean_dec(v___y_3664_);
lean_dec_ref(v___y_3663_);
lean_dec(v___y_3662_);
lean_dec_ref(v___y_3661_);
lean_dec(v___y_3660_);
lean_dec_ref(v___y_3659_);
lean_dec_ref(v_docCtx_3654_);
lean_dec_ref(v_names_3653_);
v_a_3681_ = lean_ctor_get(v___x_3676_, 0);
v_isSharedCheck_3688_ = !lean_is_exclusive(v___x_3676_);
if (v_isSharedCheck_3688_ == 0)
{
v___x_3683_ = v___x_3676_;
v_isShared_3684_ = v_isSharedCheck_3688_;
goto v_resetjp_3682_;
}
else
{
lean_inc(v_a_3681_);
lean_dec(v___x_3676_);
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
else
{
lean_object* v_a_3689_; lean_object* v___x_3691_; uint8_t v_isShared_3692_; uint8_t v_isSharedCheck_3696_; 
lean_dec(v___y_3664_);
lean_dec_ref(v___y_3663_);
lean_dec(v___y_3662_);
lean_dec_ref(v___y_3661_);
lean_dec(v___y_3660_);
lean_dec_ref(v___y_3659_);
lean_dec_ref(v_docCtx_3654_);
lean_dec_ref(v_names_3653_);
v_a_3689_ = lean_ctor_get(v___x_3668_, 0);
v_isSharedCheck_3696_ = !lean_is_exclusive(v___x_3668_);
if (v_isSharedCheck_3696_ == 0)
{
v___x_3691_ = v___x_3668_;
v_isShared_3692_ = v_isSharedCheck_3696_;
goto v_resetjp_3690_;
}
else
{
lean_inc(v_a_3689_);
lean_dec(v___x_3668_);
v___x_3691_ = lean_box(0);
v_isShared_3692_ = v_isSharedCheck_3696_;
goto v_resetjp_3690_;
}
v_resetjp_3690_:
{
lean_object* v___x_3694_; 
if (v_isShared_3692_ == 0)
{
v___x_3694_ = v___x_3691_;
goto v_reusejp_3693_;
}
else
{
lean_object* v_reuseFailAlloc_3695_; 
v_reuseFailAlloc_3695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3695_, 0, v_a_3689_);
v___x_3694_ = v_reuseFailAlloc_3695_;
goto v_reusejp_3693_;
}
v_reusejp_3693_:
{
return v___x_3694_;
}
}
}
}
else
{
lean_object* v___x_3697_; 
lean_dec(v___y_3664_);
lean_dec_ref(v___y_3663_);
lean_dec(v___y_3662_);
lean_dec_ref(v___y_3661_);
lean_dec(v___y_3660_);
lean_dec_ref(v___y_3659_);
lean_dec_ref(v_docCtx_3654_);
lean_dec_ref(v_names_3653_);
v___x_3697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3697_, 0, v_b_3658_);
return v___x_3697_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4___boxed(lean_object* v_names_3698_, lean_object* v_docCtx_3699_, lean_object* v_as_3700_, lean_object* v_i_3701_, lean_object* v_stop_3702_, lean_object* v_b_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_){
_start:
{
size_t v_i_boxed_3711_; size_t v_stop_boxed_3712_; lean_object* v_res_3713_; 
v_i_boxed_3711_ = lean_unbox_usize(v_i_3701_);
lean_dec(v_i_3701_);
v_stop_boxed_3712_ = lean_unbox_usize(v_stop_3702_);
lean_dec(v_stop_3702_);
v_res_3713_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4(v_names_3698_, v_docCtx_3699_, v_as_3700_, v_i_boxed_3711_, v_stop_boxed_3712_, v_b_3703_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3707_, v___y_3708_, v___y_3709_);
lean_dec_ref(v_as_3700_);
return v_res_3713_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__1(lean_object* v_docCtx_3714_, lean_object* v_a_3715_, lean_object* v_snd_3716_, lean_object* v_as_3717_, size_t v_sz_3718_, size_t v_i_3719_, lean_object* v_b_3720_, lean_object* v___y_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_){
_start:
{
uint8_t v___x_3728_; 
v___x_3728_ = lean_usize_dec_lt(v_i_3719_, v_sz_3718_);
if (v___x_3728_ == 0)
{
lean_object* v___x_3729_; 
lean_dec(v___y_3726_);
lean_dec_ref(v___y_3725_);
lean_dec(v___y_3724_);
lean_dec_ref(v___y_3723_);
lean_dec(v___y_3722_);
lean_dec_ref(v___y_3721_);
lean_dec_ref(v_snd_3716_);
lean_dec_ref(v_a_3715_);
lean_dec_ref(v_docCtx_3714_);
v___x_3729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3729_, 0, v_b_3720_);
return v___x_3729_;
}
else
{
lean_object* v_array_3730_; lean_object* v_start_3731_; lean_object* v_stop_3732_; uint8_t v___x_3733_; 
v_array_3730_ = lean_ctor_get(v_b_3720_, 0);
v_start_3731_ = lean_ctor_get(v_b_3720_, 1);
v_stop_3732_ = lean_ctor_get(v_b_3720_, 2);
v___x_3733_ = lean_nat_dec_lt(v_start_3731_, v_stop_3732_);
if (v___x_3733_ == 0)
{
lean_object* v___x_3734_; 
lean_dec(v___y_3726_);
lean_dec_ref(v___y_3725_);
lean_dec(v___y_3724_);
lean_dec_ref(v___y_3723_);
lean_dec(v___y_3722_);
lean_dec_ref(v___y_3721_);
lean_dec_ref(v_snd_3716_);
lean_dec_ref(v_a_3715_);
lean_dec_ref(v_docCtx_3714_);
v___x_3734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3734_, 0, v_b_3720_);
return v___x_3734_;
}
else
{
lean_object* v___x_3736_; uint8_t v_isShared_3737_; uint8_t v_isSharedCheck_3801_; 
lean_inc(v_stop_3732_);
lean_inc(v_start_3731_);
lean_inc_ref(v_array_3730_);
v_isSharedCheck_3801_ = !lean_is_exclusive(v_b_3720_);
if (v_isSharedCheck_3801_ == 0)
{
lean_object* v_unused_3802_; lean_object* v_unused_3803_; lean_object* v_unused_3804_; 
v_unused_3802_ = lean_ctor_get(v_b_3720_, 2);
lean_dec(v_unused_3802_);
v_unused_3803_ = lean_ctor_get(v_b_3720_, 1);
lean_dec(v_unused_3803_);
v_unused_3804_ = lean_ctor_get(v_b_3720_, 0);
lean_dec(v_unused_3804_);
v___x_3736_ = v_b_3720_;
v_isShared_3737_ = v_isSharedCheck_3801_;
goto v_resetjp_3735_;
}
else
{
lean_dec(v_b_3720_);
v___x_3736_ = lean_box(0);
v_isShared_3737_ = v_isSharedCheck_3801_;
goto v_resetjp_3735_;
}
v_resetjp_3735_:
{
lean_object* v_a_3738_; uint8_t v_kind_3739_; lean_object* v_type_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3745_; 
v_a_3738_ = lean_array_uget_borrowed(v_as_3717_, v_i_3719_);
v_kind_3739_ = lean_ctor_get_uint8(v_a_3738_, sizeof(void*)*9);
v_type_3740_ = lean_ctor_get(v_a_3738_, 6);
v___x_3741_ = lean_array_fget(v_array_3730_, v_start_3731_);
v___x_3742_ = lean_unsigned_to_nat(1u);
v___x_3743_ = lean_nat_add(v_start_3731_, v___x_3742_);
lean_dec(v_start_3731_);
if (v_isShared_3737_ == 0)
{
lean_ctor_set(v___x_3736_, 1, v___x_3743_);
v___x_3745_ = v___x_3736_;
goto v_reusejp_3744_;
}
else
{
lean_object* v_reuseFailAlloc_3800_; 
v_reuseFailAlloc_3800_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3800_, 0, v_array_3730_);
lean_ctor_set(v_reuseFailAlloc_3800_, 1, v___x_3743_);
lean_ctor_set(v_reuseFailAlloc_3800_, 2, v_stop_3732_);
v___x_3745_ = v_reuseFailAlloc_3800_;
goto v_reusejp_3744_;
}
v_reusejp_3744_:
{
lean_object* v_preDef_3747_; lean_object* v___y_3748_; lean_object* v___y_3749_; lean_object* v___y_3750_; lean_object* v___y_3751_; lean_object* v___y_3752_; lean_object* v___y_3753_; uint8_t v___x_3766_; 
v___x_3766_ = l_Lean_Elab_DefKind_isTheorem(v_kind_3739_);
if (v___x_3766_ == 0)
{
lean_object* v___x_3767_; 
lean_inc(v___y_3726_);
lean_inc_ref(v___y_3725_);
lean_inc(v___y_3724_);
lean_inc_ref(v___y_3723_);
lean_inc_ref(v_type_3740_);
v___x_3767_ = l_Lean_Meta_isProp(v_type_3740_, v___y_3723_, v___y_3724_, v___y_3725_, v___y_3726_);
if (lean_obj_tag(v___x_3767_) == 0)
{
lean_object* v_a_3768_; uint8_t v___x_3769_; 
v_a_3768_ = lean_ctor_get(v___x_3767_, 0);
lean_inc(v_a_3768_);
lean_dec_ref(v___x_3767_);
v___x_3769_ = lean_unbox(v_a_3768_);
lean_dec(v_a_3768_);
if (v___x_3769_ == 0)
{
lean_object* v___x_3770_; 
lean_inc(v___y_3726_);
lean_inc_ref(v___y_3725_);
lean_inc(v___y_3724_);
lean_inc_ref(v___y_3723_);
lean_inc(v_a_3738_);
v___x_3770_ = l_Lean_Elab_abstractNestedProofs(v_a_3738_, v___x_3733_, v___y_3723_, v___y_3724_, v___y_3725_, v___y_3726_);
if (lean_obj_tag(v___x_3770_) == 0)
{
lean_object* v_a_3771_; size_t v_sz_3772_; size_t v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; 
v_a_3771_ = lean_ctor_get(v___x_3770_, 0);
lean_inc(v_a_3771_);
lean_dec_ref(v___x_3770_);
v_sz_3772_ = lean_array_size(v_a_3715_);
v___x_3773_ = ((size_t)0ULL);
lean_inc_ref(v_a_3715_);
v___x_3774_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0(v_sz_3772_, v___x_3773_, v_a_3715_);
lean_inc_ref(v_snd_3716_);
lean_inc(v___x_3741_);
lean_inc(v_a_3771_);
v___x_3775_ = l_Lean_Elab_Structural_registerEqnsInfo(v_a_3771_, v___x_3774_, v___x_3741_, v_snd_3716_, v___y_3725_, v___y_3726_);
if (lean_obj_tag(v___x_3775_) == 0)
{
lean_dec_ref(v___x_3775_);
lean_inc(v___y_3726_);
lean_inc_ref(v___y_3725_);
lean_inc(v___y_3724_);
lean_inc_ref(v___y_3723_);
lean_inc(v___y_3722_);
lean_inc_ref(v___y_3721_);
v_preDef_3747_ = v_a_3771_;
v___y_3748_ = v___y_3721_;
v___y_3749_ = v___y_3722_;
v___y_3750_ = v___y_3723_;
v___y_3751_ = v___y_3724_;
v___y_3752_ = v___y_3725_;
v___y_3753_ = v___y_3726_;
goto v___jp_3746_;
}
else
{
lean_object* v_a_3776_; lean_object* v___x_3778_; uint8_t v_isShared_3779_; uint8_t v_isSharedCheck_3783_; 
lean_dec(v_a_3771_);
lean_dec_ref(v___x_3745_);
lean_dec(v___x_3741_);
lean_dec(v___y_3726_);
lean_dec_ref(v___y_3725_);
lean_dec(v___y_3724_);
lean_dec_ref(v___y_3723_);
lean_dec(v___y_3722_);
lean_dec_ref(v___y_3721_);
lean_dec_ref(v_snd_3716_);
lean_dec_ref(v_a_3715_);
lean_dec_ref(v_docCtx_3714_);
v_a_3776_ = lean_ctor_get(v___x_3775_, 0);
v_isSharedCheck_3783_ = !lean_is_exclusive(v___x_3775_);
if (v_isSharedCheck_3783_ == 0)
{
v___x_3778_ = v___x_3775_;
v_isShared_3779_ = v_isSharedCheck_3783_;
goto v_resetjp_3777_;
}
else
{
lean_inc(v_a_3776_);
lean_dec(v___x_3775_);
v___x_3778_ = lean_box(0);
v_isShared_3779_ = v_isSharedCheck_3783_;
goto v_resetjp_3777_;
}
v_resetjp_3777_:
{
lean_object* v___x_3781_; 
if (v_isShared_3779_ == 0)
{
v___x_3781_ = v___x_3778_;
goto v_reusejp_3780_;
}
else
{
lean_object* v_reuseFailAlloc_3782_; 
v_reuseFailAlloc_3782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3782_, 0, v_a_3776_);
v___x_3781_ = v_reuseFailAlloc_3782_;
goto v_reusejp_3780_;
}
v_reusejp_3780_:
{
return v___x_3781_;
}
}
}
}
else
{
lean_object* v_a_3784_; lean_object* v___x_3786_; uint8_t v_isShared_3787_; uint8_t v_isSharedCheck_3791_; 
lean_dec_ref(v___x_3745_);
lean_dec(v___x_3741_);
lean_dec(v___y_3726_);
lean_dec_ref(v___y_3725_);
lean_dec(v___y_3724_);
lean_dec_ref(v___y_3723_);
lean_dec(v___y_3722_);
lean_dec_ref(v___y_3721_);
lean_dec_ref(v_snd_3716_);
lean_dec_ref(v_a_3715_);
lean_dec_ref(v_docCtx_3714_);
v_a_3784_ = lean_ctor_get(v___x_3770_, 0);
v_isSharedCheck_3791_ = !lean_is_exclusive(v___x_3770_);
if (v_isSharedCheck_3791_ == 0)
{
v___x_3786_ = v___x_3770_;
v_isShared_3787_ = v_isSharedCheck_3791_;
goto v_resetjp_3785_;
}
else
{
lean_inc(v_a_3784_);
lean_dec(v___x_3770_);
v___x_3786_ = lean_box(0);
v_isShared_3787_ = v_isSharedCheck_3791_;
goto v_resetjp_3785_;
}
v_resetjp_3785_:
{
lean_object* v___x_3789_; 
if (v_isShared_3787_ == 0)
{
v___x_3789_ = v___x_3786_;
goto v_reusejp_3788_;
}
else
{
lean_object* v_reuseFailAlloc_3790_; 
v_reuseFailAlloc_3790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3790_, 0, v_a_3784_);
v___x_3789_ = v_reuseFailAlloc_3790_;
goto v_reusejp_3788_;
}
v_reusejp_3788_:
{
return v___x_3789_;
}
}
}
}
else
{
lean_inc(v___y_3726_);
lean_inc_ref(v___y_3725_);
lean_inc(v___y_3724_);
lean_inc_ref(v___y_3723_);
lean_inc(v___y_3722_);
lean_inc_ref(v___y_3721_);
lean_inc(v_a_3738_);
v_preDef_3747_ = v_a_3738_;
v___y_3748_ = v___y_3721_;
v___y_3749_ = v___y_3722_;
v___y_3750_ = v___y_3723_;
v___y_3751_ = v___y_3724_;
v___y_3752_ = v___y_3725_;
v___y_3753_ = v___y_3726_;
goto v___jp_3746_;
}
}
else
{
lean_object* v_a_3792_; lean_object* v___x_3794_; uint8_t v_isShared_3795_; uint8_t v_isSharedCheck_3799_; 
lean_dec_ref(v___x_3745_);
lean_dec(v___x_3741_);
lean_dec(v___y_3726_);
lean_dec_ref(v___y_3725_);
lean_dec(v___y_3724_);
lean_dec_ref(v___y_3723_);
lean_dec(v___y_3722_);
lean_dec_ref(v___y_3721_);
lean_dec_ref(v_snd_3716_);
lean_dec_ref(v_a_3715_);
lean_dec_ref(v_docCtx_3714_);
v_a_3792_ = lean_ctor_get(v___x_3767_, 0);
v_isSharedCheck_3799_ = !lean_is_exclusive(v___x_3767_);
if (v_isSharedCheck_3799_ == 0)
{
v___x_3794_ = v___x_3767_;
v_isShared_3795_ = v_isSharedCheck_3799_;
goto v_resetjp_3793_;
}
else
{
lean_inc(v_a_3792_);
lean_dec(v___x_3767_);
v___x_3794_ = lean_box(0);
v_isShared_3795_ = v_isSharedCheck_3799_;
goto v_resetjp_3793_;
}
v_resetjp_3793_:
{
lean_object* v___x_3797_; 
if (v_isShared_3795_ == 0)
{
v___x_3797_ = v___x_3794_;
goto v_reusejp_3796_;
}
else
{
lean_object* v_reuseFailAlloc_3798_; 
v_reuseFailAlloc_3798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3798_, 0, v_a_3792_);
v___x_3797_ = v_reuseFailAlloc_3798_;
goto v_reusejp_3796_;
}
v_reusejp_3796_:
{
return v___x_3797_;
}
}
}
}
else
{
lean_inc(v___y_3726_);
lean_inc_ref(v___y_3725_);
lean_inc(v___y_3724_);
lean_inc_ref(v___y_3723_);
lean_inc(v___y_3722_);
lean_inc_ref(v___y_3721_);
lean_inc(v_a_3738_);
v_preDef_3747_ = v_a_3738_;
v___y_3748_ = v___y_3721_;
v___y_3749_ = v___y_3722_;
v___y_3750_ = v___y_3723_;
v___y_3751_ = v___y_3724_;
v___y_3752_ = v___y_3725_;
v___y_3753_ = v___y_3726_;
goto v___jp_3746_;
}
v___jp_3746_:
{
lean_object* v___x_3754_; 
lean_inc_ref(v_docCtx_3714_);
v___x_3754_ = l_Lean_Elab_Structural_addSmartUnfoldingDef(v_docCtx_3714_, v_preDef_3747_, v___x_3741_, v___y_3748_, v___y_3749_, v___y_3750_, v___y_3751_, v___y_3752_, v___y_3753_);
if (lean_obj_tag(v___x_3754_) == 0)
{
size_t v___x_3755_; size_t v___x_3756_; 
lean_dec_ref(v___x_3754_);
v___x_3755_ = ((size_t)1ULL);
v___x_3756_ = lean_usize_add(v_i_3719_, v___x_3755_);
v_i_3719_ = v___x_3756_;
v_b_3720_ = v___x_3745_;
goto _start;
}
else
{
lean_object* v_a_3758_; lean_object* v___x_3760_; uint8_t v_isShared_3761_; uint8_t v_isSharedCheck_3765_; 
lean_dec_ref(v___x_3745_);
lean_dec(v___y_3726_);
lean_dec_ref(v___y_3725_);
lean_dec(v___y_3724_);
lean_dec_ref(v___y_3723_);
lean_dec(v___y_3722_);
lean_dec_ref(v___y_3721_);
lean_dec_ref(v_snd_3716_);
lean_dec_ref(v_a_3715_);
lean_dec_ref(v_docCtx_3714_);
v_a_3758_ = lean_ctor_get(v___x_3754_, 0);
v_isSharedCheck_3765_ = !lean_is_exclusive(v___x_3754_);
if (v_isSharedCheck_3765_ == 0)
{
v___x_3760_ = v___x_3754_;
v_isShared_3761_ = v_isSharedCheck_3765_;
goto v_resetjp_3759_;
}
else
{
lean_inc(v_a_3758_);
lean_dec(v___x_3754_);
v___x_3760_ = lean_box(0);
v_isShared_3761_ = v_isSharedCheck_3765_;
goto v_resetjp_3759_;
}
v_resetjp_3759_:
{
lean_object* v___x_3763_; 
if (v_isShared_3761_ == 0)
{
v___x_3763_ = v___x_3760_;
goto v_reusejp_3762_;
}
else
{
lean_object* v_reuseFailAlloc_3764_; 
v_reuseFailAlloc_3764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3764_, 0, v_a_3758_);
v___x_3763_ = v_reuseFailAlloc_3764_;
goto v_reusejp_3762_;
}
v_reusejp_3762_:
{
return v___x_3763_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__1___boxed(lean_object* v_docCtx_3805_, lean_object* v_a_3806_, lean_object* v_snd_3807_, lean_object* v_as_3808_, lean_object* v_sz_3809_, lean_object* v_i_3810_, lean_object* v_b_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_){
_start:
{
size_t v_sz_boxed_3819_; size_t v_i_boxed_3820_; lean_object* v_res_3821_; 
v_sz_boxed_3819_ = lean_unbox_usize(v_sz_3809_);
lean_dec(v_sz_3809_);
v_i_boxed_3820_ = lean_unbox_usize(v_i_3810_);
lean_dec(v_i_3810_);
v_res_3821_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__1(v_docCtx_3805_, v_a_3806_, v_snd_3807_, v_as_3808_, v_sz_boxed_3819_, v_i_boxed_3820_, v_b_3811_, v___y_3812_, v___y_3813_, v___y_3814_, v___y_3815_, v___y_3816_, v___y_3817_);
lean_dec_ref(v_as_3808_);
return v_res_3821_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___redArg(size_t v_sz_3822_, size_t v_i_3823_, lean_object* v_bs_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_){
_start:
{
uint8_t v___x_3828_; 
v___x_3828_ = lean_usize_dec_lt(v_i_3823_, v_sz_3822_);
if (v___x_3828_ == 0)
{
lean_object* v___x_3829_; 
lean_dec(v___y_3826_);
lean_dec_ref(v___y_3825_);
v___x_3829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3829_, 0, v_bs_3824_);
return v___x_3829_;
}
else
{
lean_object* v_v_3830_; lean_object* v___x_3831_; 
v_v_3830_ = lean_array_uget_borrowed(v_bs_3824_, v_i_3823_);
lean_inc(v___y_3826_);
lean_inc_ref(v___y_3825_);
lean_inc(v_v_3830_);
v___x_3831_ = l_Lean_Elab_eraseRecAppSyntax(v_v_3830_, v___y_3825_, v___y_3826_);
if (lean_obj_tag(v___x_3831_) == 0)
{
lean_object* v_a_3832_; lean_object* v___x_3833_; lean_object* v_bs_x27_3834_; size_t v___x_3835_; size_t v___x_3836_; lean_object* v___x_3837_; 
v_a_3832_ = lean_ctor_get(v___x_3831_, 0);
lean_inc(v_a_3832_);
lean_dec_ref(v___x_3831_);
v___x_3833_ = lean_unsigned_to_nat(0u);
v_bs_x27_3834_ = lean_array_uset(v_bs_3824_, v_i_3823_, v___x_3833_);
v___x_3835_ = ((size_t)1ULL);
v___x_3836_ = lean_usize_add(v_i_3823_, v___x_3835_);
v___x_3837_ = lean_array_uset(v_bs_x27_3834_, v_i_3823_, v_a_3832_);
v_i_3823_ = v___x_3836_;
v_bs_3824_ = v___x_3837_;
goto _start;
}
else
{
lean_object* v_a_3839_; lean_object* v___x_3841_; uint8_t v_isShared_3842_; uint8_t v_isSharedCheck_3846_; 
lean_dec(v___y_3826_);
lean_dec_ref(v___y_3825_);
lean_dec_ref(v_bs_3824_);
v_a_3839_ = lean_ctor_get(v___x_3831_, 0);
v_isSharedCheck_3846_ = !lean_is_exclusive(v___x_3831_);
if (v_isSharedCheck_3846_ == 0)
{
v___x_3841_ = v___x_3831_;
v_isShared_3842_ = v_isSharedCheck_3846_;
goto v_resetjp_3840_;
}
else
{
lean_inc(v_a_3839_);
lean_dec(v___x_3831_);
v___x_3841_ = lean_box(0);
v_isShared_3842_ = v_isSharedCheck_3846_;
goto v_resetjp_3840_;
}
v_resetjp_3840_:
{
lean_object* v___x_3844_; 
if (v_isShared_3842_ == 0)
{
v___x_3844_ = v___x_3841_;
goto v_reusejp_3843_;
}
else
{
lean_object* v_reuseFailAlloc_3845_; 
v_reuseFailAlloc_3845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3845_, 0, v_a_3839_);
v___x_3844_ = v_reuseFailAlloc_3845_;
goto v_reusejp_3843_;
}
v_reusejp_3843_:
{
return v___x_3844_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___redArg___boxed(lean_object* v_sz_3847_, lean_object* v_i_3848_, lean_object* v_bs_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_){
_start:
{
size_t v_sz_boxed_3853_; size_t v_i_boxed_3854_; lean_object* v_res_3855_; 
v_sz_boxed_3853_ = lean_unbox_usize(v_sz_3847_);
lean_dec(v_sz_3847_);
v_i_boxed_3854_ = lean_unbox_usize(v_i_3848_);
lean_dec(v_i_3848_);
v_res_3855_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___redArg(v_sz_boxed_3853_, v_i_boxed_3854_, v_bs_3849_, v___y_3850_, v___y_3851_);
return v_res_3855_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___redArg(lean_object* v_as_3856_, size_t v_i_3857_, size_t v_stop_3858_, lean_object* v_b_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_){
_start:
{
uint8_t v___x_3865_; 
v___x_3865_ = lean_usize_dec_eq(v_i_3857_, v_stop_3858_);
if (v___x_3865_ == 0)
{
lean_object* v___x_9810__overap_3866_; lean_object* v___x_3867_; 
v___x_9810__overap_3866_ = lean_array_uget_borrowed(v_as_3856_, v_i_3857_);
lean_inc(v___x_9810__overap_3866_);
lean_inc(v___y_3863_);
lean_inc_ref(v___y_3862_);
lean_inc(v___y_3861_);
lean_inc_ref(v___y_3860_);
v___x_3867_ = lean_apply_5(v___x_9810__overap_3866_, v___y_3860_, v___y_3861_, v___y_3862_, v___y_3863_, lean_box(0));
if (lean_obj_tag(v___x_3867_) == 0)
{
lean_object* v_a_3868_; size_t v___x_3869_; size_t v___x_3870_; 
v_a_3868_ = lean_ctor_get(v___x_3867_, 0);
lean_inc(v_a_3868_);
lean_dec_ref(v___x_3867_);
v___x_3869_ = ((size_t)1ULL);
v___x_3870_ = lean_usize_add(v_i_3857_, v___x_3869_);
v_i_3857_ = v___x_3870_;
v_b_3859_ = v_a_3868_;
goto _start;
}
else
{
lean_dec(v___y_3863_);
lean_dec_ref(v___y_3862_);
lean_dec(v___y_3861_);
lean_dec_ref(v___y_3860_);
return v___x_3867_;
}
}
else
{
lean_object* v___x_3872_; 
lean_dec(v___y_3863_);
lean_dec_ref(v___y_3862_);
lean_dec(v___y_3861_);
lean_dec_ref(v___y_3860_);
v___x_3872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3872_, 0, v_b_3859_);
return v___x_3872_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___redArg___boxed(lean_object* v_as_3873_, lean_object* v_i_3874_, lean_object* v_stop_3875_, lean_object* v_b_3876_, lean_object* v___y_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_){
_start:
{
size_t v_i_boxed_3882_; size_t v_stop_boxed_3883_; lean_object* v_res_3884_; 
v_i_boxed_3882_ = lean_unbox_usize(v_i_3874_);
lean_dec(v_i_3874_);
v_stop_boxed_3883_ = lean_unbox_usize(v_stop_3875_);
lean_dec(v_stop_3875_);
v_res_3884_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___redArg(v_as_3873_, v_i_boxed_3882_, v_stop_boxed_3883_, v_b_3876_, v___y_3877_, v___y_3878_, v___y_3879_, v___y_3880_);
lean_dec_ref(v_as_3873_);
return v_res_3884_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___redArg(lean_object* v_as_3885_, size_t v_sz_3886_, size_t v_i_3887_, lean_object* v_b_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_){
_start:
{
uint8_t v___x_3894_; 
v___x_3894_ = lean_usize_dec_lt(v_i_3887_, v_sz_3886_);
if (v___x_3894_ == 0)
{
lean_object* v___x_3895_; 
lean_dec(v___y_3892_);
lean_dec_ref(v___y_3891_);
lean_dec(v___y_3890_);
lean_dec_ref(v___y_3889_);
v___x_3895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3895_, 0, v_b_3888_);
return v___x_3895_;
}
else
{
lean_object* v_array_3896_; lean_object* v_start_3897_; lean_object* v_stop_3898_; uint8_t v___x_3899_; 
v_array_3896_ = lean_ctor_get(v_b_3888_, 0);
v_start_3897_ = lean_ctor_get(v_b_3888_, 1);
v_stop_3898_ = lean_ctor_get(v_b_3888_, 2);
v___x_3899_ = lean_nat_dec_lt(v_start_3897_, v_stop_3898_);
if (v___x_3899_ == 0)
{
lean_object* v___x_3900_; 
lean_dec(v___y_3892_);
lean_dec_ref(v___y_3891_);
lean_dec(v___y_3890_);
lean_dec_ref(v___y_3889_);
v___x_3900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3900_, 0, v_b_3888_);
return v___x_3900_;
}
else
{
lean_object* v___x_3902_; uint8_t v_isShared_3903_; uint8_t v_isSharedCheck_3923_; 
lean_inc(v_stop_3898_);
lean_inc(v_start_3897_);
lean_inc_ref(v_array_3896_);
v_isSharedCheck_3923_ = !lean_is_exclusive(v_b_3888_);
if (v_isSharedCheck_3923_ == 0)
{
lean_object* v_unused_3924_; lean_object* v_unused_3925_; lean_object* v_unused_3926_; 
v_unused_3924_ = lean_ctor_get(v_b_3888_, 2);
lean_dec(v_unused_3924_);
v_unused_3925_ = lean_ctor_get(v_b_3888_, 1);
lean_dec(v_unused_3925_);
v_unused_3926_ = lean_ctor_get(v_b_3888_, 0);
lean_dec(v_unused_3926_);
v___x_3902_ = v_b_3888_;
v_isShared_3903_ = v_isSharedCheck_3923_;
goto v_resetjp_3901_;
}
else
{
lean_dec(v_b_3888_);
v___x_3902_ = lean_box(0);
v_isShared_3903_ = v_isSharedCheck_3923_;
goto v_resetjp_3901_;
}
v_resetjp_3901_:
{
lean_object* v_a_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; 
v_a_3904_ = lean_array_uget_borrowed(v_as_3885_, v_i_3887_);
v___x_3905_ = lean_array_fget_borrowed(v_array_3896_, v_start_3897_);
lean_inc(v___y_3892_);
lean_inc_ref(v___y_3891_);
lean_inc(v___y_3890_);
lean_inc_ref(v___y_3889_);
lean_inc(v_a_3904_);
lean_inc(v___x_3905_);
v___x_3906_ = l_Lean_Elab_Structural_reportTermMeasure(v___x_3905_, v_a_3904_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_);
if (lean_obj_tag(v___x_3906_) == 0)
{
lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3910_; 
lean_dec_ref(v___x_3906_);
v___x_3907_ = lean_unsigned_to_nat(1u);
v___x_3908_ = lean_nat_add(v_start_3897_, v___x_3907_);
lean_dec(v_start_3897_);
if (v_isShared_3903_ == 0)
{
lean_ctor_set(v___x_3902_, 1, v___x_3908_);
v___x_3910_ = v___x_3902_;
goto v_reusejp_3909_;
}
else
{
lean_object* v_reuseFailAlloc_3914_; 
v_reuseFailAlloc_3914_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3914_, 0, v_array_3896_);
lean_ctor_set(v_reuseFailAlloc_3914_, 1, v___x_3908_);
lean_ctor_set(v_reuseFailAlloc_3914_, 2, v_stop_3898_);
v___x_3910_ = v_reuseFailAlloc_3914_;
goto v_reusejp_3909_;
}
v_reusejp_3909_:
{
size_t v___x_3911_; size_t v___x_3912_; 
v___x_3911_ = ((size_t)1ULL);
v___x_3912_ = lean_usize_add(v_i_3887_, v___x_3911_);
v_i_3887_ = v___x_3912_;
v_b_3888_ = v___x_3910_;
goto _start;
}
}
else
{
lean_object* v_a_3915_; lean_object* v___x_3917_; uint8_t v_isShared_3918_; uint8_t v_isSharedCheck_3922_; 
lean_del_object(v___x_3902_);
lean_dec(v_stop_3898_);
lean_dec(v_start_3897_);
lean_dec_ref(v_array_3896_);
lean_dec(v___y_3892_);
lean_dec_ref(v___y_3891_);
lean_dec(v___y_3890_);
lean_dec_ref(v___y_3889_);
v_a_3915_ = lean_ctor_get(v___x_3906_, 0);
v_isSharedCheck_3922_ = !lean_is_exclusive(v___x_3906_);
if (v_isSharedCheck_3922_ == 0)
{
v___x_3917_ = v___x_3906_;
v_isShared_3918_ = v_isSharedCheck_3922_;
goto v_resetjp_3916_;
}
else
{
lean_inc(v_a_3915_);
lean_dec(v___x_3906_);
v___x_3917_ = lean_box(0);
v_isShared_3918_ = v_isSharedCheck_3922_;
goto v_resetjp_3916_;
}
v_resetjp_3916_:
{
lean_object* v___x_3920_; 
if (v_isShared_3918_ == 0)
{
v___x_3920_ = v___x_3917_;
goto v_reusejp_3919_;
}
else
{
lean_object* v_reuseFailAlloc_3921_; 
v_reuseFailAlloc_3921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3921_, 0, v_a_3915_);
v___x_3920_ = v_reuseFailAlloc_3921_;
goto v_reusejp_3919_;
}
v_reusejp_3919_:
{
return v___x_3920_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___redArg___boxed(lean_object* v_as_3927_, lean_object* v_sz_3928_, lean_object* v_i_3929_, lean_object* v_b_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_){
_start:
{
size_t v_sz_boxed_3936_; size_t v_i_boxed_3937_; lean_object* v_res_3938_; 
v_sz_boxed_3936_ = lean_unbox_usize(v_sz_3928_);
lean_dec(v_sz_3928_);
v_i_boxed_3937_ = lean_unbox_usize(v_i_3929_);
lean_dec(v_i_3929_);
v_res_3938_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___redArg(v_as_3927_, v_sz_boxed_3936_, v_i_boxed_3937_, v_b_3930_, v___y_3931_, v___y_3932_, v___y_3933_, v___y_3934_);
lean_dec_ref(v_as_3927_);
return v_res_3938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_structuralRecursion(lean_object* v_docCtx_3941_, lean_object* v_preDefs_3942_, lean_object* v_termMeasure_x3fs_3943_, lean_object* v_a_3944_, lean_object* v_a_3945_, lean_object* v_a_3946_, lean_object* v_a_3947_, lean_object* v_a_3948_, lean_object* v_a_3949_){
_start:
{
size_t v_sz_3951_; size_t v___x_3952_; lean_object* v_names_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; 
v_sz_3951_ = lean_array_size(v_preDefs_3942_);
v___x_3952_ = ((size_t)0ULL);
lean_inc_ref(v_preDefs_3942_);
v_names_3953_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0(v_sz_3951_, v___x_3952_, v_preDefs_3942_);
lean_inc_ref(v_preDefs_3942_);
v___x_3954_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___boxed), 8, 2);
lean_closure_set(v___x_3954_, 0, v_preDefs_3942_);
lean_closure_set(v___x_3954_, 1, v_termMeasure_x3fs_3943_);
v___x_3955_ = lean_unsigned_to_nat(0u);
v___x_3956_ = ((lean_object*)(l_Lean_Elab_Structural_structuralRecursion___closed__0));
lean_inc(v_a_3949_);
lean_inc_ref(v_a_3948_);
lean_inc(v_a_3947_);
lean_inc_ref(v_a_3946_);
v___x_3957_ = l_Lean_Elab_Structural_run___redArg(v___x_3954_, v___x_3956_, v_a_3946_, v_a_3947_, v_a_3948_, v_a_3949_);
if (lean_obj_tag(v___x_3957_) == 0)
{
lean_object* v_a_3958_; lean_object* v_fst_3959_; lean_object* v_snd_3960_; lean_object* v_snd_3961_; lean_object* v_fst_3962_; lean_object* v_fst_3963_; lean_object* v_snd_3964_; lean_object* v___y_3994_; lean_object* v___y_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; size_t v_sz_4008_; lean_object* v___x_4009_; 
v_a_3958_ = lean_ctor_get(v___x_3957_, 0);
lean_inc(v_a_3958_);
lean_dec_ref(v___x_3957_);
v_fst_3959_ = lean_ctor_get(v_a_3958_, 0);
lean_inc(v_fst_3959_);
v_snd_3960_ = lean_ctor_get(v_fst_3959_, 1);
lean_inc(v_snd_3960_);
v_snd_3961_ = lean_ctor_get(v_a_3958_, 1);
lean_inc(v_snd_3961_);
lean_dec(v_a_3958_);
v_fst_3962_ = lean_ctor_get(v_fst_3959_, 0);
lean_inc(v_fst_3962_);
lean_dec(v_fst_3959_);
v_fst_3963_ = lean_ctor_get(v_snd_3960_, 0);
lean_inc(v_fst_3963_);
v_snd_3964_ = lean_ctor_get(v_snd_3960_, 1);
lean_inc(v_snd_3964_);
lean_dec(v_snd_3960_);
v___x_4006_ = lean_array_get_size(v_preDefs_3942_);
lean_inc_ref(v_preDefs_3942_);
v___x_4007_ = l_Array_toSubarray___redArg(v_preDefs_3942_, v___x_3955_, v___x_4006_);
v_sz_4008_ = lean_array_size(v_fst_3962_);
lean_inc(v_a_3949_);
lean_inc_ref(v_a_3948_);
lean_inc(v_a_3947_);
lean_inc_ref(v_a_3946_);
v___x_4009_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___redArg(v_fst_3962_, v_sz_4008_, v___x_3952_, v___x_4007_, v_a_3946_, v_a_3947_, v_a_3948_, v_a_3949_);
if (lean_obj_tag(v___x_4009_) == 0)
{
lean_object* v___x_4010_; uint8_t v___x_4011_; 
lean_dec_ref(v___x_4009_);
v___x_4010_ = lean_array_get_size(v_snd_3961_);
v___x_4011_ = lean_nat_dec_lt(v___x_3955_, v___x_4010_);
if (v___x_4011_ == 0)
{
lean_dec(v_snd_3961_);
goto v___jp_3995_;
}
else
{
lean_object* v___x_4012_; uint8_t v___x_4013_; 
v___x_4012_ = lean_box(0);
v___x_4013_ = lean_nat_dec_le(v___x_4010_, v___x_4010_);
if (v___x_4013_ == 0)
{
if (v___x_4011_ == 0)
{
lean_dec(v_snd_3961_);
goto v___jp_3995_;
}
else
{
size_t v___x_4014_; lean_object* v___x_4015_; 
v___x_4014_ = lean_usize_of_nat(v___x_4010_);
lean_inc(v_a_3949_);
lean_inc_ref(v_a_3948_);
lean_inc(v_a_3947_);
lean_inc_ref(v_a_3946_);
v___x_4015_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___redArg(v_snd_3961_, v___x_3952_, v___x_4014_, v___x_4012_, v_a_3946_, v_a_3947_, v_a_3948_, v_a_3949_);
lean_dec(v_snd_3961_);
v___y_4005_ = v___x_4015_;
goto v___jp_4004_;
}
}
else
{
size_t v___x_4016_; lean_object* v___x_4017_; 
v___x_4016_ = lean_usize_of_nat(v___x_4010_);
lean_inc(v_a_3949_);
lean_inc_ref(v_a_3948_);
lean_inc(v_a_3947_);
lean_inc_ref(v_a_3946_);
v___x_4017_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___redArg(v_snd_3961_, v___x_3952_, v___x_4016_, v___x_4012_, v_a_3946_, v_a_3947_, v_a_3948_, v_a_3949_);
lean_dec(v_snd_3961_);
v___y_4005_ = v___x_4017_;
goto v___jp_4004_;
}
}
}
else
{
lean_object* v_a_4018_; lean_object* v___x_4020_; uint8_t v_isShared_4021_; uint8_t v_isSharedCheck_4025_; 
lean_dec(v_snd_3964_);
lean_dec(v_fst_3963_);
lean_dec(v_fst_3962_);
lean_dec(v_snd_3961_);
lean_dec_ref(v_names_3953_);
lean_dec(v_a_3949_);
lean_dec_ref(v_a_3948_);
lean_dec(v_a_3947_);
lean_dec_ref(v_a_3946_);
lean_dec(v_a_3945_);
lean_dec_ref(v_a_3944_);
lean_dec_ref(v_preDefs_3942_);
lean_dec_ref(v_docCtx_3941_);
v_a_4018_ = lean_ctor_get(v___x_4009_, 0);
v_isSharedCheck_4025_ = !lean_is_exclusive(v___x_4009_);
if (v_isSharedCheck_4025_ == 0)
{
v___x_4020_ = v___x_4009_;
v_isShared_4021_ = v_isSharedCheck_4025_;
goto v_resetjp_4019_;
}
else
{
lean_inc(v_a_4018_);
lean_dec(v___x_4009_);
v___x_4020_ = lean_box(0);
v_isShared_4021_ = v_isSharedCheck_4025_;
goto v_resetjp_4019_;
}
v_resetjp_4019_:
{
lean_object* v___x_4023_; 
if (v_isShared_4021_ == 0)
{
v___x_4023_ = v___x_4020_;
goto v_reusejp_4022_;
}
else
{
lean_object* v_reuseFailAlloc_4024_; 
v_reuseFailAlloc_4024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4024_, 0, v_a_4018_);
v___x_4023_ = v_reuseFailAlloc_4024_;
goto v_reusejp_4022_;
}
v_reusejp_4022_:
{
return v___x_4023_;
}
}
}
v___jp_3965_:
{
lean_object* v___x_3966_; 
lean_inc(v_a_3949_);
lean_inc_ref(v_a_3948_);
v___x_3966_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___redArg(v_sz_3951_, v___x_3952_, v_preDefs_3942_, v_a_3948_, v_a_3949_);
if (lean_obj_tag(v___x_3966_) == 0)
{
lean_object* v_a_3967_; lean_object* v___x_3968_; 
v_a_3967_ = lean_ctor_get(v___x_3966_, 0);
lean_inc(v_a_3967_);
lean_dec_ref(v___x_3966_);
lean_inc(v_a_3949_);
lean_inc_ref(v_a_3948_);
lean_inc(v_a_3947_);
lean_inc_ref(v_a_3946_);
lean_inc(v_a_3945_);
lean_inc_ref(v_a_3944_);
lean_inc(v_a_3967_);
lean_inc_ref(v_docCtx_3941_);
v___x_3968_ = l_Lean_Elab_addAndCompilePartialRec(v_docCtx_3941_, v_a_3967_, v_a_3944_, v_a_3945_, v_a_3946_, v_a_3947_, v_a_3948_, v_a_3949_);
if (lean_obj_tag(v___x_3968_) == 0)
{
lean_object* v___x_3969_; lean_object* v___x_3970_; size_t v_sz_3971_; lean_object* v___x_3972_; 
lean_dec_ref(v___x_3968_);
v___x_3969_ = lean_array_get_size(v_fst_3962_);
v___x_3970_ = l_Array_toSubarray___redArg(v_fst_3962_, v___x_3955_, v___x_3969_);
v_sz_3971_ = lean_array_size(v_a_3967_);
lean_inc(v_a_3949_);
lean_inc_ref(v_a_3948_);
lean_inc(v_a_3947_);
lean_inc_ref(v_a_3946_);
lean_inc(v_a_3945_);
lean_inc_ref(v_a_3944_);
lean_inc(v_a_3967_);
v___x_3972_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__1(v_docCtx_3941_, v_a_3967_, v_snd_3964_, v_a_3967_, v_sz_3971_, v___x_3952_, v___x_3970_, v_a_3944_, v_a_3945_, v_a_3946_, v_a_3947_, v_a_3948_, v_a_3949_);
if (lean_obj_tag(v___x_3972_) == 0)
{
lean_object* v___x_3973_; lean_object* v___x_3974_; 
lean_dec_ref(v___x_3972_);
v___x_3973_ = lean_box(0);
lean_inc(v_a_3949_);
lean_inc_ref(v_a_3948_);
lean_inc(v_a_3947_);
lean_inc_ref(v_a_3946_);
v___x_3974_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___redArg(v_a_3967_, v_sz_3971_, v___x_3952_, v___x_3973_, v_a_3946_, v_a_3947_, v_a_3948_, v_a_3949_);
lean_dec(v_a_3967_);
if (lean_obj_tag(v___x_3974_) == 0)
{
uint8_t v___x_3975_; lean_object* v___x_3976_; 
lean_dec_ref(v___x_3974_);
v___x_3975_ = 1;
v___x_3976_ = l_Lean_Elab_applyAttributesOf(v_fst_3963_, v___x_3975_, v_a_3944_, v_a_3945_, v_a_3946_, v_a_3947_, v_a_3948_, v_a_3949_);
lean_dec(v_fst_3963_);
return v___x_3976_;
}
else
{
lean_dec(v_fst_3963_);
lean_dec(v_a_3949_);
lean_dec_ref(v_a_3948_);
lean_dec(v_a_3947_);
lean_dec_ref(v_a_3946_);
lean_dec(v_a_3945_);
lean_dec_ref(v_a_3944_);
return v___x_3974_;
}
}
else
{
lean_object* v_a_3977_; lean_object* v___x_3979_; uint8_t v_isShared_3980_; uint8_t v_isSharedCheck_3984_; 
lean_dec(v_a_3967_);
lean_dec(v_fst_3963_);
lean_dec(v_a_3949_);
lean_dec_ref(v_a_3948_);
lean_dec(v_a_3947_);
lean_dec_ref(v_a_3946_);
lean_dec(v_a_3945_);
lean_dec_ref(v_a_3944_);
v_a_3977_ = lean_ctor_get(v___x_3972_, 0);
v_isSharedCheck_3984_ = !lean_is_exclusive(v___x_3972_);
if (v_isSharedCheck_3984_ == 0)
{
v___x_3979_ = v___x_3972_;
v_isShared_3980_ = v_isSharedCheck_3984_;
goto v_resetjp_3978_;
}
else
{
lean_inc(v_a_3977_);
lean_dec(v___x_3972_);
v___x_3979_ = lean_box(0);
v_isShared_3980_ = v_isSharedCheck_3984_;
goto v_resetjp_3978_;
}
v_resetjp_3978_:
{
lean_object* v___x_3982_; 
if (v_isShared_3980_ == 0)
{
v___x_3982_ = v___x_3979_;
goto v_reusejp_3981_;
}
else
{
lean_object* v_reuseFailAlloc_3983_; 
v_reuseFailAlloc_3983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3983_, 0, v_a_3977_);
v___x_3982_ = v_reuseFailAlloc_3983_;
goto v_reusejp_3981_;
}
v_reusejp_3981_:
{
return v___x_3982_;
}
}
}
}
else
{
lean_dec(v_a_3967_);
lean_dec(v_snd_3964_);
lean_dec(v_fst_3963_);
lean_dec(v_fst_3962_);
lean_dec(v_a_3949_);
lean_dec_ref(v_a_3948_);
lean_dec(v_a_3947_);
lean_dec_ref(v_a_3946_);
lean_dec(v_a_3945_);
lean_dec_ref(v_a_3944_);
lean_dec_ref(v_docCtx_3941_);
return v___x_3968_;
}
}
else
{
lean_object* v_a_3985_; lean_object* v___x_3987_; uint8_t v_isShared_3988_; uint8_t v_isSharedCheck_3992_; 
lean_dec(v_snd_3964_);
lean_dec(v_fst_3963_);
lean_dec(v_fst_3962_);
lean_dec(v_a_3949_);
lean_dec_ref(v_a_3948_);
lean_dec(v_a_3947_);
lean_dec_ref(v_a_3946_);
lean_dec(v_a_3945_);
lean_dec_ref(v_a_3944_);
lean_dec_ref(v_docCtx_3941_);
v_a_3985_ = lean_ctor_get(v___x_3966_, 0);
v_isSharedCheck_3992_ = !lean_is_exclusive(v___x_3966_);
if (v_isSharedCheck_3992_ == 0)
{
v___x_3987_ = v___x_3966_;
v_isShared_3988_ = v_isSharedCheck_3992_;
goto v_resetjp_3986_;
}
else
{
lean_inc(v_a_3985_);
lean_dec(v___x_3966_);
v___x_3987_ = lean_box(0);
v_isShared_3988_ = v_isSharedCheck_3992_;
goto v_resetjp_3986_;
}
v_resetjp_3986_:
{
lean_object* v___x_3990_; 
if (v_isShared_3988_ == 0)
{
v___x_3990_ = v___x_3987_;
goto v_reusejp_3989_;
}
else
{
lean_object* v_reuseFailAlloc_3991_; 
v_reuseFailAlloc_3991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3991_, 0, v_a_3985_);
v___x_3990_ = v_reuseFailAlloc_3991_;
goto v_reusejp_3989_;
}
v_reusejp_3989_:
{
return v___x_3990_;
}
}
}
}
v___jp_3993_:
{
if (lean_obj_tag(v___y_3994_) == 0)
{
lean_dec_ref(v___y_3994_);
goto v___jp_3965_;
}
else
{
lean_dec(v_snd_3964_);
lean_dec(v_fst_3963_);
lean_dec(v_fst_3962_);
lean_dec(v_a_3949_);
lean_dec_ref(v_a_3948_);
lean_dec(v_a_3947_);
lean_dec_ref(v_a_3946_);
lean_dec(v_a_3945_);
lean_dec_ref(v_a_3944_);
lean_dec_ref(v_preDefs_3942_);
lean_dec_ref(v_docCtx_3941_);
return v___y_3994_;
}
}
v___jp_3995_:
{
lean_object* v___x_3996_; uint8_t v___x_3997_; 
v___x_3996_ = lean_array_get_size(v_fst_3963_);
v___x_3997_ = lean_nat_dec_lt(v___x_3955_, v___x_3996_);
if (v___x_3997_ == 0)
{
lean_dec_ref(v_names_3953_);
goto v___jp_3965_;
}
else
{
lean_object* v___x_3998_; uint8_t v___x_3999_; 
v___x_3998_ = lean_box(0);
v___x_3999_ = lean_nat_dec_le(v___x_3996_, v___x_3996_);
if (v___x_3999_ == 0)
{
if (v___x_3997_ == 0)
{
lean_dec_ref(v_names_3953_);
goto v___jp_3965_;
}
else
{
size_t v___x_4000_; lean_object* v___x_4001_; 
v___x_4000_ = lean_usize_of_nat(v___x_3996_);
lean_inc(v_a_3949_);
lean_inc_ref(v_a_3948_);
lean_inc(v_a_3947_);
lean_inc_ref(v_a_3946_);
lean_inc(v_a_3945_);
lean_inc_ref(v_a_3944_);
lean_inc_ref(v_docCtx_3941_);
v___x_4001_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4(v_names_3953_, v_docCtx_3941_, v_fst_3963_, v___x_3952_, v___x_4000_, v___x_3998_, v_a_3944_, v_a_3945_, v_a_3946_, v_a_3947_, v_a_3948_, v_a_3949_);
v___y_3994_ = v___x_4001_;
goto v___jp_3993_;
}
}
else
{
size_t v___x_4002_; lean_object* v___x_4003_; 
v___x_4002_ = lean_usize_of_nat(v___x_3996_);
lean_inc(v_a_3949_);
lean_inc_ref(v_a_3948_);
lean_inc(v_a_3947_);
lean_inc_ref(v_a_3946_);
lean_inc(v_a_3945_);
lean_inc_ref(v_a_3944_);
lean_inc_ref(v_docCtx_3941_);
v___x_4003_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__4(v_names_3953_, v_docCtx_3941_, v_fst_3963_, v___x_3952_, v___x_4002_, v___x_3998_, v_a_3944_, v_a_3945_, v_a_3946_, v_a_3947_, v_a_3948_, v_a_3949_);
v___y_3994_ = v___x_4003_;
goto v___jp_3993_;
}
}
}
v___jp_4004_:
{
if (lean_obj_tag(v___y_4005_) == 0)
{
lean_dec_ref(v___y_4005_);
goto v___jp_3995_;
}
else
{
lean_dec(v_snd_3964_);
lean_dec(v_fst_3963_);
lean_dec(v_fst_3962_);
lean_dec_ref(v_names_3953_);
lean_dec(v_a_3949_);
lean_dec_ref(v_a_3948_);
lean_dec(v_a_3947_);
lean_dec_ref(v_a_3946_);
lean_dec(v_a_3945_);
lean_dec_ref(v_a_3944_);
lean_dec_ref(v_preDefs_3942_);
lean_dec_ref(v_docCtx_3941_);
return v___y_4005_;
}
}
}
else
{
lean_object* v_a_4026_; lean_object* v___x_4028_; uint8_t v_isShared_4029_; uint8_t v_isSharedCheck_4033_; 
lean_dec_ref(v_names_3953_);
lean_dec(v_a_3949_);
lean_dec_ref(v_a_3948_);
lean_dec(v_a_3947_);
lean_dec_ref(v_a_3946_);
lean_dec(v_a_3945_);
lean_dec_ref(v_a_3944_);
lean_dec_ref(v_preDefs_3942_);
lean_dec_ref(v_docCtx_3941_);
v_a_4026_ = lean_ctor_get(v___x_3957_, 0);
v_isSharedCheck_4033_ = !lean_is_exclusive(v___x_3957_);
if (v_isSharedCheck_4033_ == 0)
{
v___x_4028_ = v___x_3957_;
v_isShared_4029_ = v_isSharedCheck_4033_;
goto v_resetjp_4027_;
}
else
{
lean_inc(v_a_4026_);
lean_dec(v___x_3957_);
v___x_4028_ = lean_box(0);
v_isShared_4029_ = v_isSharedCheck_4033_;
goto v_resetjp_4027_;
}
v_resetjp_4027_:
{
lean_object* v___x_4031_; 
if (v_isShared_4029_ == 0)
{
v___x_4031_ = v___x_4028_;
goto v_reusejp_4030_;
}
else
{
lean_object* v_reuseFailAlloc_4032_; 
v_reuseFailAlloc_4032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4032_, 0, v_a_4026_);
v___x_4031_ = v_reuseFailAlloc_4032_;
goto v_reusejp_4030_;
}
v_reusejp_4030_:
{
return v___x_4031_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_structuralRecursion___boxed(lean_object* v_docCtx_4034_, lean_object* v_preDefs_4035_, lean_object* v_termMeasure_x3fs_4036_, lean_object* v_a_4037_, lean_object* v_a_4038_, lean_object* v_a_4039_, lean_object* v_a_4040_, lean_object* v_a_4041_, lean_object* v_a_4042_, lean_object* v_a_4043_){
_start:
{
lean_object* v_res_4044_; 
v_res_4044_ = l_Lean_Elab_Structural_structuralRecursion(v_docCtx_4034_, v_preDefs_4035_, v_termMeasure_x3fs_4036_, v_a_4037_, v_a_4038_, v_a_4039_, v_a_4040_, v_a_4041_, v_a_4042_);
return v_res_4044_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0(size_t v_sz_4045_, size_t v_i_4046_, lean_object* v_bs_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_, lean_object* v___y_4053_){
_start:
{
lean_object* v___x_4055_; 
v___x_4055_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___redArg(v_sz_4045_, v_i_4046_, v_bs_4047_, v___y_4052_, v___y_4053_);
return v___x_4055_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___boxed(lean_object* v_sz_4056_, lean_object* v_i_4057_, lean_object* v_bs_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_){
_start:
{
size_t v_sz_boxed_4066_; size_t v_i_boxed_4067_; lean_object* v_res_4068_; 
v_sz_boxed_4066_ = lean_unbox_usize(v_sz_4056_);
lean_dec(v_sz_4056_);
v_i_boxed_4067_ = lean_unbox_usize(v_i_4057_);
lean_dec(v_i_4057_);
v_res_4068_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0(v_sz_boxed_4066_, v_i_boxed_4067_, v_bs_4058_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_, v___y_4063_, v___y_4064_);
lean_dec(v___y_4062_);
lean_dec_ref(v___y_4061_);
lean_dec(v___y_4060_);
lean_dec_ref(v___y_4059_);
return v_res_4068_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2(lean_object* v_as_4069_, size_t v_sz_4070_, size_t v_i_4071_, lean_object* v_b_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_){
_start:
{
lean_object* v___x_4080_; 
v___x_4080_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___redArg(v_as_4069_, v_sz_4070_, v_i_4071_, v_b_4072_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_);
return v___x_4080_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___boxed(lean_object* v_as_4081_, lean_object* v_sz_4082_, lean_object* v_i_4083_, lean_object* v_b_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_){
_start:
{
size_t v_sz_boxed_4092_; size_t v_i_boxed_4093_; lean_object* v_res_4094_; 
v_sz_boxed_4092_ = lean_unbox_usize(v_sz_4082_);
lean_dec(v_sz_4082_);
v_i_boxed_4093_ = lean_unbox_usize(v_i_4083_);
lean_dec(v_i_4083_);
v_res_4094_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2(v_as_4081_, v_sz_boxed_4092_, v_i_boxed_4093_, v_b_4084_, v___y_4085_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_, v___y_4090_);
lean_dec(v___y_4086_);
lean_dec_ref(v___y_4085_);
lean_dec_ref(v_as_4081_);
return v_res_4094_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3(lean_object* v_as_4095_, size_t v_sz_4096_, size_t v_i_4097_, lean_object* v_b_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_){
_start:
{
lean_object* v___x_4106_; 
v___x_4106_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___redArg(v_as_4095_, v_sz_4096_, v_i_4097_, v_b_4098_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_);
return v___x_4106_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___boxed(lean_object* v_as_4107_, lean_object* v_sz_4108_, lean_object* v_i_4109_, lean_object* v_b_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_){
_start:
{
size_t v_sz_boxed_4118_; size_t v_i_boxed_4119_; lean_object* v_res_4120_; 
v_sz_boxed_4118_ = lean_unbox_usize(v_sz_4108_);
lean_dec(v_sz_4108_);
v_i_boxed_4119_ = lean_unbox_usize(v_i_4109_);
lean_dec(v_i_4109_);
v_res_4120_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3(v_as_4107_, v_sz_boxed_4118_, v_i_boxed_4119_, v_b_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_);
lean_dec(v___y_4112_);
lean_dec_ref(v___y_4111_);
lean_dec_ref(v_as_4107_);
return v_res_4120_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5(lean_object* v_as_4121_, size_t v_i_4122_, size_t v_stop_4123_, lean_object* v_b_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_){
_start:
{
lean_object* v___x_4132_; 
v___x_4132_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___redArg(v_as_4121_, v_i_4122_, v_stop_4123_, v_b_4124_, v___y_4127_, v___y_4128_, v___y_4129_, v___y_4130_);
return v___x_4132_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___boxed(lean_object* v_as_4133_, lean_object* v_i_4134_, lean_object* v_stop_4135_, lean_object* v_b_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_){
_start:
{
size_t v_i_boxed_4144_; size_t v_stop_boxed_4145_; lean_object* v_res_4146_; 
v_i_boxed_4144_ = lean_unbox_usize(v_i_4134_);
lean_dec(v_i_4134_);
v_stop_boxed_4145_ = lean_unbox_usize(v_stop_4135_);
lean_dec(v_stop_4135_);
v_res_4146_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5(v_as_4133_, v_i_boxed_4144_, v_stop_boxed_4145_, v_b_4136_, v___y_4137_, v___y_4138_, v___y_4139_, v___y_4140_, v___y_4141_, v___y_4142_);
lean_dec(v___y_4138_);
lean_dec_ref(v___y_4137_);
lean_dec_ref(v_as_4133_);
return v_res_4146_;
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
