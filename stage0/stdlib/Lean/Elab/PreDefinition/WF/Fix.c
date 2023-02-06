// Lean compiler output
// Module: Lean.Elab.PreDefinition.WF.Fix
// Imports: Init Lean.Util.HasConstCache Lean.Meta.CasesOn Lean.Meta.Match.Match Lean.Meta.Tactic.Simp.Main Lean.Meta.Tactic.Cleanup Lean.Elab.Tactic.Basic Lean.Elab.RecAppSyntax Lean.Elab.PreDefinition.Basic Lean.Elab.PreDefinition.Structural.Basic Lean.Elab.PreDefinition.Structural.BRecOn
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__outOfBounds___rarg(lean_object*);
lean_object* l_Lean_Meta_CasesOnApp_toExpr(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__11___rarg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__5___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lambda__1___closed__1;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__4;
lean_object* l_Lean_Meta_mkAppOptM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_mkFix___closed__1;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__2;
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__5;
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lambda__1___closed__2;
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getRecAppSyntax_x3f(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_arity(lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lambda__1___closed__3;
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__1;
static lean_object* l_Lean_Elab_WF_mkFix___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Elab_Term_withAuxDecl___spec__1___rarg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__2;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___lambda__2___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__12___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__9___lambda__2___closed__2;
lean_object* l_Lean_Elab_Term_instInhabitedTermElabM(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_containsRecFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__11___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_mkDecreasingProof___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lambda__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isLambda(lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__4;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___lambda__2___closed__2;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_mkDecreasingProof___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_mkDecreasingProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__4___boxed(lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__5___lambda__2___closed__2;
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(lean_object*, lean_object*);
lean_object* l_Array_zip___rarg(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lambda__2___closed__3;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp___rarg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__12___rarg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___spec__1(lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__1;
lean_object* l_Lean_Meta_forallBoundedTelescope___at_Lean_Elab_Term_addAutoBoundImplicits_x27___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_runTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__9___lambda__2___closed__1;
lean_object* l_Lean_Meta_Match_MatcherInfo_numAlts(lean_object*);
uint8_t l_Lean_Elab_Structural_recArgHasLooseBVarsAt(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__7___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_mkFix___lambda__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__4___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__6;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lambda__2___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lambda__2___closed__1;
lean_object* l_Lean_Expr_replaceFVar(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__11___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_levelZero;
extern lean_object* l_Lean_instInhabitedExpr;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__3;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__6;
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__3(lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__5;
lean_object* l_Lean_HasConstCache_containsUnsafe(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_CasesOnApp_addArg_x3f(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_setUserName(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__5___lambda__2___closed__6;
lean_object* l_Lean_Elab_pushInfoTree___at_Lean_Elab_Term_addDotCompletionInfo___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_reportUnsolvedGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lambda__2___closed__2;
static lean_object* l_Lean_Elab_WF_mkFix___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__7___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__5___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__7(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* l_Array_extract___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__8___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__8___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__8;
lean_object* l_Lean_isTracingEnabledFor___at_Lean_Elab_Term_traceAtCmdPos___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__13___rarg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__4;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__9___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_refinedArgType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__5___lambda__2___closed__3;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_mkFix___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__13___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_MatcherApp_addArg_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__5___lambda__2___closed__5;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getUserName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__7___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_MatcherApp_toExpr(lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_containsRecFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__11___boxed(lean_object*, lean_object*);
lean_object* l_Lean_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__13___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ofSubarray___rarg(lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__3;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lambda__2___closed__4;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__5___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkHashMapImp___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Elab_ensureNoRecFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__6;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___lambda__1___closed__1;
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__12(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___closed__1;
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__5___lambda__2___closed__4;
lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
lean_object* l_List_redLength___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__2___boxed(lean_object*);
lean_object* l_Lean_Meta_toCasesOnApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__8(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__3;
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__12___boxed(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__9___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__3___boxed(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Expr_beta(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__5___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__9___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__13(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateForallAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_mkFix___closed__2;
static lean_object* l_Lean_Elab_WF_mkFix___lambda__1___closed__3;
lean_object* l_List_toArrayAux___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_etaExpand(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__9___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_box(0);
lean_ctor_set(x_1, 1, x_13);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_14 = l_Lean_Elab_Term_reportUnsolvedGoals(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_1 = x_12;
x_8 = x_15;
goto _start;
}
else
{
uint8_t x_17; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_14, 0);
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_14);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_1, 0);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_1);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_25 = l_Lean_Elab_Term_reportUnsolvedGoals(x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_1 = x_22;
x_8 = x_26;
goto _start;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_22);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_28 = lean_ctor_get(x_25, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_30 = x_25;
} else {
 lean_dec_ref(x_25);
 x_30 = lean_box(0);
}
if (lean_is_scalar(x_30)) {
 x_31 = lean_alloc_ctor(1, 2, 0);
} else {
 x_31 = x_30;
}
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("tacticDecreasing_tactic", 23);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lambda__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("decreasing_tactic", 17);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_10 = lean_ctor_get(x_7, 5);
lean_inc(x_10);
x_11 = 0;
x_12 = l_Lean_SourceInfo_fromRef(x_10, x_11);
x_13 = lean_st_ref_get(x_8, x_9);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lambda__1___closed__3;
lean_inc(x_12);
x_16 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_15);
x_17 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lambda__1___closed__2;
x_18 = l_Lean_Syntax_node1(x_12, x_17, x_16);
x_19 = l_Lean_Elab_Tactic_evalTactic(x_18, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_14);
return x_19;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lambda__1), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___closed__1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_10 = l_Lean_Elab_Tactic_run(x_1, x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_List_forM___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___spec__1(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 0);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_10);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_forM___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_mkDecreasingProof___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_mkDecreasingProof(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_box(0);
lean_inc(x_5);
x_11 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_1, x_10, x_5, x_6, x_7, x_8, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_12);
x_14 = l_Lean_Expr_mvarId_x21(x_12);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_15 = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore(x_14, x_5, x_6, x_7, x_8, x_13);
if (lean_obj_tag(x_15) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_18 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic(x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_18, 0);
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_18);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_15, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_15, 1);
lean_inc(x_26);
lean_dec(x_15);
x_27 = lean_ctor_get(x_2, 0);
lean_inc(x_27);
lean_dec(x_2);
lean_inc(x_25);
x_28 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_28, 0, x_25);
x_29 = l_Lean_Elab_pushInfoTree___at_Lean_Elab_Term_addDotCompletionInfo___spec__3(x_28, x_3, x_4, x_5, x_6, x_7, x_8, x_26);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_31 = l_Lean_Elab_Term_runTactic(x_25, x_27, x_3, x_4, x_5, x_6, x_7, x_8, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_32);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_33;
}
else
{
uint8_t x_34; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_34 = !lean_is_exclusive(x_31);
if (x_34 == 0)
{
return x_31;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_31, 0);
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_31);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_38 = !lean_is_exclusive(x_15);
if (x_38 == 0)
{
return x_15;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_15, 0);
x_40 = lean_ctor_get(x_15, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_15);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_mkDecreasingProof___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_mkDecreasingProof___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_containsRecFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_11 = lean_st_ref_take(x_3, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_HasConstCache_containsUnsafe(x_1, x_2, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_st_ref_set(x_3, x_16, x_13);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_15);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_containsRecFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_containsRecFn(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
x_16 = lean_usize_dec_lt(x_6, x_5);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_array_uget(x_7, x_6);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_array_uset(x_7, x_6, x_19);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_21 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(x_1, x_2, x_3, x_4, x_18, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = 1;
x_25 = lean_usize_add(x_6, x_24);
x_26 = lean_array_uset(x_20, x_6, x_22);
x_6 = x_25;
x_7 = x_26;
x_15 = x_23;
goto _start;
}
else
{
uint8_t x_28; 
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_21);
if (x_28 == 0)
{
return x_21;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_21, 0);
x_30 = lean_ctor_get(x_21, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_21);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
x_16 = lean_usize_dec_lt(x_6, x_5);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_array_uget(x_7, x_6);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_array_uset(x_7, x_6, x_19);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_21 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(x_1, x_2, x_3, x_4, x_18, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = 1;
x_25 = lean_usize_add(x_6, x_24);
x_26 = lean_array_uset(x_20, x_6, x_22);
x_6 = x_25;
x_7 = x_26;
x_15 = x_23;
goto _start;
}
else
{
uint8_t x_28; 
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_21);
if (x_28 == 0)
{
return x_21;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_21, 0);
x_30 = lean_ctor_get(x_21, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_21);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_5, x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_2, x_16);
x_18 = lean_nat_dec_lt(x_15, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_19 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1;
lean_inc(x_15);
x_20 = lean_mk_array(x_15, x_19);
x_21 = lean_nat_sub(x_15, x_16);
lean_dec(x_15);
x_22 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_5, x_20, x_21);
x_23 = lean_array_get_size(x_22);
x_24 = lean_nat_dec_lt(x_2, x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = l_Lean_instInhabitedExpr;
x_26 = l___private_Init_Util_0__outOfBounds___rarg(x_25);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_27 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(x_1, x_2, x_3, x_4, x_26, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
lean_inc(x_4);
x_30 = l_Lean_Expr_app___override(x_4, x_28);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_30);
x_31 = lean_infer_type(x_30, x_9, x_10, x_11, x_12, x_29);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_34 = lean_whnf(x_32, x_9, x_10, x_11, x_12, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_Expr_bindingDomain_x21(x_35);
lean_dec(x_35);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_3);
x_38 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_mkDecreasingProof(x_37, x_3, x_7, x_8, x_9, x_10, x_11, x_12, x_36);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; size_t x_46; size_t x_47; lean_object* x_48; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_Expr_app___override(x_30, x_39);
x_42 = lean_array_get_size(x_22);
x_43 = l_Array_toSubarray___rarg(x_22, x_17, x_42);
x_44 = l_Array_ofSubarray___rarg(x_43);
x_45 = lean_array_get_size(x_44);
x_46 = lean_usize_of_nat(x_45);
lean_dec(x_45);
x_47 = 0;
x_48 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___spec__1(x_1, x_2, x_3, x_4, x_46, x_47, x_44, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_40);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_48, 0);
x_51 = l_Lean_mkAppN(x_41, x_50);
lean_ctor_set(x_48, 0, x_51);
return x_48;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_48, 0);
x_53 = lean_ctor_get(x_48, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_48);
x_54 = l_Lean_mkAppN(x_41, x_52);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
else
{
uint8_t x_56; 
lean_dec(x_41);
x_56 = !lean_is_exclusive(x_48);
if (x_56 == 0)
{
return x_48;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_48, 0);
x_58 = lean_ctor_get(x_48, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_48);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_30);
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_60 = !lean_is_exclusive(x_38);
if (x_60 == 0)
{
return x_38;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_38, 0);
x_62 = lean_ctor_get(x_38, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_38);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_30);
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_34);
if (x_64 == 0)
{
return x_34;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_34, 0);
x_66 = lean_ctor_get(x_34, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_34);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_30);
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_31);
if (x_68 == 0)
{
return x_31;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_31, 0);
x_70 = lean_ctor_get(x_31, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_31);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_72 = !lean_is_exclusive(x_27);
if (x_72 == 0)
{
return x_27;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_27, 0);
x_74 = lean_ctor_get(x_27, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_27);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
else
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_array_fget(x_22, x_2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_77 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(x_1, x_2, x_3, x_4, x_76, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
lean_inc(x_4);
x_80 = l_Lean_Expr_app___override(x_4, x_78);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_80);
x_81 = lean_infer_type(x_80, x_9, x_10, x_11, x_12, x_79);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_84 = lean_whnf(x_82, x_9, x_10, x_11, x_12, x_83);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = l_Lean_Expr_bindingDomain_x21(x_85);
lean_dec(x_85);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_3);
x_88 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_mkDecreasingProof(x_87, x_3, x_7, x_8, x_9, x_10, x_11, x_12, x_86);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; size_t x_96; size_t x_97; lean_object* x_98; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_91 = l_Lean_Expr_app___override(x_80, x_89);
x_92 = lean_array_get_size(x_22);
x_93 = l_Array_toSubarray___rarg(x_22, x_17, x_92);
x_94 = l_Array_ofSubarray___rarg(x_93);
x_95 = lean_array_get_size(x_94);
x_96 = lean_usize_of_nat(x_95);
lean_dec(x_95);
x_97 = 0;
x_98 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___spec__2(x_1, x_2, x_3, x_4, x_96, x_97, x_94, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_90);
if (lean_obj_tag(x_98) == 0)
{
uint8_t x_99; 
x_99 = !lean_is_exclusive(x_98);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_98, 0);
x_101 = l_Lean_mkAppN(x_91, x_100);
lean_ctor_set(x_98, 0, x_101);
return x_98;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_102 = lean_ctor_get(x_98, 0);
x_103 = lean_ctor_get(x_98, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_98);
x_104 = l_Lean_mkAppN(x_91, x_102);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_103);
return x_105;
}
}
else
{
uint8_t x_106; 
lean_dec(x_91);
x_106 = !lean_is_exclusive(x_98);
if (x_106 == 0)
{
return x_98;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_98, 0);
x_108 = lean_ctor_get(x_98, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_98);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
else
{
uint8_t x_110; 
lean_dec(x_80);
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_110 = !lean_is_exclusive(x_88);
if (x_110 == 0)
{
return x_88;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_88, 0);
x_112 = lean_ctor_get(x_88, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_88);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
else
{
uint8_t x_114; 
lean_dec(x_80);
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_114 = !lean_is_exclusive(x_84);
if (x_114 == 0)
{
return x_84;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_84, 0);
x_116 = lean_ctor_get(x_84, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_84);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
else
{
uint8_t x_118; 
lean_dec(x_80);
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_118 = !lean_is_exclusive(x_81);
if (x_118 == 0)
{
return x_81;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_81, 0);
x_120 = lean_ctor_get(x_81, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_81);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
}
else
{
uint8_t x_122; 
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_122 = !lean_is_exclusive(x_77);
if (x_122 == 0)
{
return x_77;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_77, 0);
x_124 = lean_ctor_get(x_77, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_77);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
}
}
else
{
lean_object* x_126; 
lean_dec(x_17);
lean_dec(x_15);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_126 = l_Lean_Meta_etaExpand(x_5, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
x_129 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(x_1, x_2, x_3, x_4, x_127, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_128);
return x_129;
}
else
{
uint8_t x_130; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_130 = !lean_is_exclusive(x_126);
if (x_130 == 0)
{
return x_126;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_126, 0);
x_132 = lean_ctor_get(x_126, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_126);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
return x_133;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_st_ref_get(x_8, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(x_13, x_1);
lean_ctor_set(x_10, 0, x_14);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_10, 0);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_10);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(x_17, x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_16);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_getMatcherInfo_x3f___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__2___rarg___boxed), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Expr_getAppFn(x_2);
if (lean_obj_tag(x_11) == 4)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_12);
x_14 = l_Lean_Meta_getMatcherInfo_x3f___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__2___rarg(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_2);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 0);
lean_dec(x_17);
x_18 = lean_box(0);
lean_ctor_set(x_14, 0, x_18);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_14);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_14, 0);
lean_dec(x_23);
x_24 = !lean_is_exclusive(x_15);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_25 = lean_ctor_get(x_15, 0);
x_26 = lean_unsigned_to_nat(0u);
x_27 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_2, x_26);
x_28 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1;
lean_inc(x_27);
x_29 = lean_mk_array(x_27, x_28);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_sub(x_27, x_30);
lean_dec(x_27);
x_32 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_2, x_29, x_31);
x_33 = lean_array_get_size(x_32);
x_34 = l_Lean_Meta_Match_MatcherInfo_arity(x_25);
x_35 = lean_nat_dec_lt(x_33, x_34);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_36 = l_List_redLength___rarg(x_13);
x_37 = lean_mk_empty_array_with_capacity(x_36);
lean_dec(x_36);
x_38 = l_List_toArrayAux___rarg(x_13, x_37);
x_39 = lean_ctor_get(x_25, 3);
lean_inc(x_39);
x_40 = lean_ctor_get(x_25, 0);
lean_inc(x_40);
lean_inc(x_40);
lean_inc(x_32);
x_41 = l_Array_extract___rarg(x_32, x_26, x_40);
x_42 = lean_nat_dec_lt(x_40, x_33);
x_43 = lean_nat_add(x_40, x_30);
x_44 = lean_ctor_get(x_25, 1);
lean_inc(x_44);
x_45 = lean_nat_add(x_43, x_44);
lean_dec(x_44);
lean_inc(x_45);
lean_inc(x_32);
x_46 = l_Array_toSubarray___rarg(x_32, x_43, x_45);
x_47 = l_Array_ofSubarray___rarg(x_46);
x_48 = lean_ctor_get(x_25, 2);
lean_inc(x_48);
x_49 = l_Lean_Meta_Match_MatcherInfo_numAlts(x_25);
lean_dec(x_25);
x_50 = lean_nat_add(x_45, x_49);
lean_dec(x_49);
lean_inc(x_50);
lean_inc(x_32);
x_51 = l_Array_toSubarray___rarg(x_32, x_45, x_50);
x_52 = l_Array_ofSubarray___rarg(x_51);
lean_inc(x_32);
x_53 = l_Array_toSubarray___rarg(x_32, x_50, x_33);
x_54 = l_Array_ofSubarray___rarg(x_53);
if (x_42 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_40);
lean_dec(x_32);
x_55 = l_Lean_instInhabitedExpr;
x_56 = l___private_Init_Util_0__outOfBounds___rarg(x_55);
x_57 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_57, 0, x_12);
lean_ctor_set(x_57, 1, x_38);
lean_ctor_set(x_57, 2, x_39);
lean_ctor_set(x_57, 3, x_41);
lean_ctor_set(x_57, 4, x_56);
lean_ctor_set(x_57, 5, x_47);
lean_ctor_set(x_57, 6, x_48);
lean_ctor_set(x_57, 7, x_52);
lean_ctor_set(x_57, 8, x_54);
lean_ctor_set(x_15, 0, x_57);
return x_14;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_array_fget(x_32, x_40);
lean_dec(x_40);
lean_dec(x_32);
x_59 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_59, 0, x_12);
lean_ctor_set(x_59, 1, x_38);
lean_ctor_set(x_59, 2, x_39);
lean_ctor_set(x_59, 3, x_41);
lean_ctor_set(x_59, 4, x_58);
lean_ctor_set(x_59, 5, x_47);
lean_ctor_set(x_59, 6, x_48);
lean_ctor_set(x_59, 7, x_52);
lean_ctor_set(x_59, 8, x_54);
lean_ctor_set(x_15, 0, x_59);
return x_14;
}
}
else
{
lean_object* x_60; 
lean_dec(x_33);
lean_dec(x_32);
lean_free_object(x_15);
lean_dec(x_25);
lean_dec(x_13);
lean_dec(x_12);
x_60 = lean_box(0);
lean_ctor_set(x_14, 0, x_60);
return x_14;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_61 = lean_ctor_get(x_15, 0);
lean_inc(x_61);
lean_dec(x_15);
x_62 = lean_unsigned_to_nat(0u);
x_63 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_2, x_62);
x_64 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1;
lean_inc(x_63);
x_65 = lean_mk_array(x_63, x_64);
x_66 = lean_unsigned_to_nat(1u);
x_67 = lean_nat_sub(x_63, x_66);
lean_dec(x_63);
x_68 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_2, x_65, x_67);
x_69 = lean_array_get_size(x_68);
x_70 = l_Lean_Meta_Match_MatcherInfo_arity(x_61);
x_71 = lean_nat_dec_lt(x_69, x_70);
lean_dec(x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_72 = l_List_redLength___rarg(x_13);
x_73 = lean_mk_empty_array_with_capacity(x_72);
lean_dec(x_72);
x_74 = l_List_toArrayAux___rarg(x_13, x_73);
x_75 = lean_ctor_get(x_61, 3);
lean_inc(x_75);
x_76 = lean_ctor_get(x_61, 0);
lean_inc(x_76);
lean_inc(x_76);
lean_inc(x_68);
x_77 = l_Array_extract___rarg(x_68, x_62, x_76);
x_78 = lean_nat_dec_lt(x_76, x_69);
x_79 = lean_nat_add(x_76, x_66);
x_80 = lean_ctor_get(x_61, 1);
lean_inc(x_80);
x_81 = lean_nat_add(x_79, x_80);
lean_dec(x_80);
lean_inc(x_81);
lean_inc(x_68);
x_82 = l_Array_toSubarray___rarg(x_68, x_79, x_81);
x_83 = l_Array_ofSubarray___rarg(x_82);
x_84 = lean_ctor_get(x_61, 2);
lean_inc(x_84);
x_85 = l_Lean_Meta_Match_MatcherInfo_numAlts(x_61);
lean_dec(x_61);
x_86 = lean_nat_add(x_81, x_85);
lean_dec(x_85);
lean_inc(x_86);
lean_inc(x_68);
x_87 = l_Array_toSubarray___rarg(x_68, x_81, x_86);
x_88 = l_Array_ofSubarray___rarg(x_87);
lean_inc(x_68);
x_89 = l_Array_toSubarray___rarg(x_68, x_86, x_69);
x_90 = l_Array_ofSubarray___rarg(x_89);
if (x_78 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_76);
lean_dec(x_68);
x_91 = l_Lean_instInhabitedExpr;
x_92 = l___private_Init_Util_0__outOfBounds___rarg(x_91);
x_93 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_93, 0, x_12);
lean_ctor_set(x_93, 1, x_74);
lean_ctor_set(x_93, 2, x_75);
lean_ctor_set(x_93, 3, x_77);
lean_ctor_set(x_93, 4, x_92);
lean_ctor_set(x_93, 5, x_83);
lean_ctor_set(x_93, 6, x_84);
lean_ctor_set(x_93, 7, x_88);
lean_ctor_set(x_93, 8, x_90);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_14, 0, x_94);
return x_14;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_array_fget(x_68, x_76);
lean_dec(x_76);
lean_dec(x_68);
x_96 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_96, 0, x_12);
lean_ctor_set(x_96, 1, x_74);
lean_ctor_set(x_96, 2, x_75);
lean_ctor_set(x_96, 3, x_77);
lean_ctor_set(x_96, 4, x_95);
lean_ctor_set(x_96, 5, x_83);
lean_ctor_set(x_96, 6, x_84);
lean_ctor_set(x_96, 7, x_88);
lean_ctor_set(x_96, 8, x_90);
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_14, 0, x_97);
return x_14;
}
}
else
{
lean_object* x_98; 
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_61);
lean_dec(x_13);
lean_dec(x_12);
x_98 = lean_box(0);
lean_ctor_set(x_14, 0, x_98);
return x_14;
}
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_99 = lean_ctor_get(x_14, 1);
lean_inc(x_99);
lean_dec(x_14);
x_100 = lean_ctor_get(x_15, 0);
lean_inc(x_100);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 x_101 = x_15;
} else {
 lean_dec_ref(x_15);
 x_101 = lean_box(0);
}
x_102 = lean_unsigned_to_nat(0u);
x_103 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_2, x_102);
x_104 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1;
lean_inc(x_103);
x_105 = lean_mk_array(x_103, x_104);
x_106 = lean_unsigned_to_nat(1u);
x_107 = lean_nat_sub(x_103, x_106);
lean_dec(x_103);
x_108 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_2, x_105, x_107);
x_109 = lean_array_get_size(x_108);
x_110 = l_Lean_Meta_Match_MatcherInfo_arity(x_100);
x_111 = lean_nat_dec_lt(x_109, x_110);
lean_dec(x_110);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_112 = l_List_redLength___rarg(x_13);
x_113 = lean_mk_empty_array_with_capacity(x_112);
lean_dec(x_112);
x_114 = l_List_toArrayAux___rarg(x_13, x_113);
x_115 = lean_ctor_get(x_100, 3);
lean_inc(x_115);
x_116 = lean_ctor_get(x_100, 0);
lean_inc(x_116);
lean_inc(x_116);
lean_inc(x_108);
x_117 = l_Array_extract___rarg(x_108, x_102, x_116);
x_118 = lean_nat_dec_lt(x_116, x_109);
x_119 = lean_nat_add(x_116, x_106);
x_120 = lean_ctor_get(x_100, 1);
lean_inc(x_120);
x_121 = lean_nat_add(x_119, x_120);
lean_dec(x_120);
lean_inc(x_121);
lean_inc(x_108);
x_122 = l_Array_toSubarray___rarg(x_108, x_119, x_121);
x_123 = l_Array_ofSubarray___rarg(x_122);
x_124 = lean_ctor_get(x_100, 2);
lean_inc(x_124);
x_125 = l_Lean_Meta_Match_MatcherInfo_numAlts(x_100);
lean_dec(x_100);
x_126 = lean_nat_add(x_121, x_125);
lean_dec(x_125);
lean_inc(x_126);
lean_inc(x_108);
x_127 = l_Array_toSubarray___rarg(x_108, x_121, x_126);
x_128 = l_Array_ofSubarray___rarg(x_127);
lean_inc(x_108);
x_129 = l_Array_toSubarray___rarg(x_108, x_126, x_109);
x_130 = l_Array_ofSubarray___rarg(x_129);
if (x_118 == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_116);
lean_dec(x_108);
x_131 = l_Lean_instInhabitedExpr;
x_132 = l___private_Init_Util_0__outOfBounds___rarg(x_131);
x_133 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_133, 0, x_12);
lean_ctor_set(x_133, 1, x_114);
lean_ctor_set(x_133, 2, x_115);
lean_ctor_set(x_133, 3, x_117);
lean_ctor_set(x_133, 4, x_132);
lean_ctor_set(x_133, 5, x_123);
lean_ctor_set(x_133, 6, x_124);
lean_ctor_set(x_133, 7, x_128);
lean_ctor_set(x_133, 8, x_130);
if (lean_is_scalar(x_101)) {
 x_134 = lean_alloc_ctor(1, 1, 0);
} else {
 x_134 = x_101;
}
lean_ctor_set(x_134, 0, x_133);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_99);
return x_135;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_136 = lean_array_fget(x_108, x_116);
lean_dec(x_116);
lean_dec(x_108);
x_137 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_137, 0, x_12);
lean_ctor_set(x_137, 1, x_114);
lean_ctor_set(x_137, 2, x_115);
lean_ctor_set(x_137, 3, x_117);
lean_ctor_set(x_137, 4, x_136);
lean_ctor_set(x_137, 5, x_123);
lean_ctor_set(x_137, 6, x_124);
lean_ctor_set(x_137, 7, x_128);
lean_ctor_set(x_137, 8, x_130);
if (lean_is_scalar(x_101)) {
 x_138 = lean_alloc_ctor(1, 1, 0);
} else {
 x_138 = x_101;
}
lean_ctor_set(x_138, 0, x_137);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_99);
return x_139;
}
}
else
{
lean_object* x_140; lean_object* x_141; 
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_13);
lean_dec(x_12);
x_140 = lean_box(0);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_99);
return x_141;
}
}
}
}
else
{
lean_object* x_142; lean_object* x_143; 
lean_dec(x_11);
lean_dec(x_2);
x_142 = lean_box(0);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_10);
return x_143;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_7, 5);
x_11 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_5, x_6, x_7, x_8, x_9);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_11);
lean_inc(x_10);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__3___rarg___boxed), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__4___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = lean_apply_10(x_1, x_5, x_6, x_2, x_3, x_4, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__4___rarg___lambda__1), 11, 4);
lean_closure_set(x_11, 0, x_2);
lean_closure_set(x_11, 1, x_3);
lean_closure_set(x_11, 2, x_4);
lean_closure_set(x_11, 3, x_5);
x_12 = 0;
x_13 = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___rarg(x_1, x_12, x_11, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
return x_13;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_13, 0);
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_13);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__4___rarg), 10, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__5___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_array_get_size(x_1);
x_17 = lean_nat_dec_lt(x_2, x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = l_Lean_instInhabitedExpr;
x_19 = l___private_Init_Util_0__outOfBounds___rarg(x_18);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_20 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(x_3, x_4, x_5, x_19, x_6, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = 0;
x_24 = 1;
x_25 = 1;
x_26 = l_Lean_Meta_mkLambdaFVars(x_1, x_21, x_23, x_24, x_25, x_11, x_12, x_13, x_14, x_22);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_20);
if (x_27 == 0)
{
return x_20;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_20, 0);
x_29 = lean_ctor_get(x_20, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_20);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_array_fget(x_1, x_2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_32 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(x_3, x_4, x_5, x_31, x_6, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = 0;
x_36 = 1;
x_37 = 1;
x_38 = l_Lean_Meta_mkLambdaFVars(x_1, x_33, x_35, x_36, x_37, x_11, x_12, x_13, x_14, x_34);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
return x_38;
}
else
{
uint8_t x_39; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_32);
if (x_39 == 0)
{
return x_32;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_32, 0);
x_41 = lean_ctor_get(x_32, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_32);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__5___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unexpected `casesOn` application alternative", 44);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__5___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__5___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__5___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\nat application", 15);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__5___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__5___lambda__2___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__5___lambda__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__5___lambda__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__5___lambda__2___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__5___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_array_get_size(x_7);
x_18 = lean_nat_dec_le(x_1, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_19 = l_Lean_indentExpr(x_5);
x_20 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__5___lambda__2___closed__2;
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__5___lambda__2___closed__4;
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_indentExpr(x_6);
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__5___lambda__2___closed__6;
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_throwError___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__3___rarg(x_27, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
return x_28;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_28);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_6);
lean_dec(x_5);
x_33 = lean_box(0);
x_34 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__5___lambda__1(x_7, x_1, x_2, x_3, x_4, x_8, x_33, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_1);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
x_16 = lean_usize_dec_lt(x_6, x_5);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_array_uget(x_7, x_6);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_array_uset(x_7, x_6, x_19);
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
lean_inc(x_4);
lean_inc(x_21);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_23 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__5___lambda__2), 16, 6);
lean_closure_set(x_23, 0, x_22);
lean_closure_set(x_23, 1, x_1);
lean_closure_set(x_23, 2, x_2);
lean_closure_set(x_23, 3, x_3);
lean_closure_set(x_23, 4, x_21);
lean_closure_set(x_23, 5, x_4);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_24 = l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__4___rarg(x_21, x_23, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = 1;
x_28 = lean_usize_add(x_6, x_27);
x_29 = lean_array_uset(x_20, x_6, x_25);
x_6 = x_28;
x_7 = x_29;
x_15 = x_26;
goto _start;
}
else
{
uint8_t x_31; 
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_24);
if (x_31 == 0)
{
return x_24;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_24, 0);
x_33 = lean_ctor_get(x_24, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_24);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
x_16 = lean_usize_dec_lt(x_6, x_5);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_array_uget(x_7, x_6);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_array_uset(x_7, x_6, x_19);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_21 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(x_1, x_2, x_3, x_4, x_18, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = 1;
x_25 = lean_usize_add(x_6, x_24);
x_26 = lean_array_uset(x_20, x_6, x_22);
x_6 = x_25;
x_7 = x_26;
x_15 = x_23;
goto _start;
}
else
{
uint8_t x_28; 
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_21);
if (x_28 == 0)
{
return x_21;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_21, 0);
x_30 = lean_ctor_get(x_21, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_21);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__7___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_7, 5);
x_11 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_5, x_6, x_7, x_8, x_9);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_11);
lean_inc(x_10);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__7(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__7___rarg___boxed), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__8___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__4___rarg___lambda__1), 11, 4);
lean_closure_set(x_11, 0, x_2);
lean_closure_set(x_11, 1, x_3);
lean_closure_set(x_11, 2, x_4);
lean_closure_set(x_11, 3, x_5);
x_12 = 0;
x_13 = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___rarg(x_1, x_12, x_11, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
return x_13;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_13, 0);
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_13);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__8(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__8___rarg), 10, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__9___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_1, x_16);
x_18 = lean_array_get_size(x_2);
x_19 = lean_nat_dec_lt(x_17, x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_17);
x_20 = l_Lean_instInhabitedExpr;
x_21 = l___private_Init_Util_0__outOfBounds___rarg(x_20);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_22 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(x_3, x_4, x_5, x_21, x_6, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = 0;
x_26 = 1;
x_27 = 1;
x_28 = l_Lean_Meta_mkLambdaFVars(x_2, x_23, x_25, x_26, x_27, x_11, x_12, x_13, x_14, x_24);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
return x_28;
}
else
{
uint8_t x_29; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_22);
if (x_29 == 0)
{
return x_22;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_22, 0);
x_31 = lean_ctor_get(x_22, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_22);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_array_fget(x_2, x_17);
lean_dec(x_17);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_34 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(x_3, x_4, x_5, x_33, x_6, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = 0;
x_38 = 1;
x_39 = 1;
x_40 = l_Lean_Meta_mkLambdaFVars(x_2, x_35, x_37, x_38, x_39, x_11, x_12, x_13, x_14, x_36);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
return x_40;
}
else
{
uint8_t x_41; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_2);
x_41 = !lean_is_exclusive(x_34);
if (x_41 == 0)
{
return x_34;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_34, 0);
x_43 = lean_ctor_get(x_34, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_34);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__9___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unexpected matcher application alternative", 42);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__9___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__9___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__9___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_array_get_size(x_7);
x_18 = lean_nat_dec_le(x_1, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_19 = l_Lean_indentExpr(x_5);
x_20 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__9___lambda__2___closed__2;
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__5___lambda__2___closed__4;
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_indentExpr(x_6);
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__5___lambda__2___closed__6;
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_throwError___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__7___rarg(x_27, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
return x_28;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_28);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_6);
lean_dec(x_5);
x_33 = lean_box(0);
x_34 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__9___lambda__1(x_1, x_7, x_2, x_3, x_4, x_8, x_33, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
x_16 = lean_usize_dec_lt(x_6, x_5);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_array_uget(x_7, x_6);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_array_uset(x_7, x_6, x_19);
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
lean_inc(x_4);
lean_inc(x_21);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_23 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__9___lambda__2___boxed), 16, 6);
lean_closure_set(x_23, 0, x_22);
lean_closure_set(x_23, 1, x_1);
lean_closure_set(x_23, 2, x_2);
lean_closure_set(x_23, 3, x_3);
lean_closure_set(x_23, 4, x_21);
lean_closure_set(x_23, 5, x_4);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_24 = l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__8___rarg(x_21, x_23, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = 1;
x_28 = lean_usize_add(x_6, x_27);
x_29 = lean_array_uset(x_20, x_6, x_25);
x_6 = x_28;
x_7 = x_29;
x_15 = x_26;
goto _start;
}
else
{
uint8_t x_31; 
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_24);
if (x_31 == 0)
{
return x_24;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_24, 0);
x_33 = lean_ctor_get(x_24, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_24);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
x_16 = lean_usize_dec_lt(x_6, x_5);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_array_uget(x_7, x_6);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_array_uset(x_7, x_6, x_19);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_21 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(x_1, x_2, x_3, x_4, x_18, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = 1;
x_25 = lean_usize_add(x_6, x_24);
x_26 = lean_array_uset(x_20, x_6, x_22);
x_6 = x_25;
x_7 = x_26;
x_15 = x_23;
goto _start;
}
else
{
uint8_t x_28; 
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_21);
if (x_28 == 0)
{
return x_21;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_21, 0);
x_30 = lean_ctor_get(x_21, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_21);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__11___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = lean_apply_9(x_1, x_5, x_2, x_3, x_4, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__11___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__11___rarg___lambda__1), 10, 4);
lean_closure_set(x_14, 0, x_4);
lean_closure_set(x_14, 1, x_6);
lean_closure_set(x_14, 2, x_7);
lean_closure_set(x_14, 3, x_8);
x_15 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp___rarg(x_1, x_2, x_3, x_14, x_5, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
return x_15;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_15);
if (x_20 == 0)
{
return x_15;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_15, 0);
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_15);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__11(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__11___rarg___boxed), 13, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__12___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__11___rarg___lambda__1), 10, 4);
lean_closure_set(x_14, 0, x_4);
lean_closure_set(x_14, 1, x_6);
lean_closure_set(x_14, 2, x_7);
lean_closure_set(x_14, 3, x_8);
x_15 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp___rarg(x_1, x_2, x_3, x_14, x_5, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
return x_15;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_15);
if (x_20 == 0)
{
return x_15;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_15, 0);
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_15);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__12(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__12___rarg___boxed), 13, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__13___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__11___rarg___lambda__1), 10, 4);
lean_closure_set(x_14, 0, x_4);
lean_closure_set(x_14, 1, x_6);
lean_closure_set(x_14, 2, x_7);
lean_closure_set(x_14, 3, x_8);
x_15 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp___rarg(x_1, x_2, x_3, x_14, x_5, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
return x_15;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_15);
if (x_20 == 0)
{
return x_15;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_15, 0);
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_15);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__13(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__13___rarg___boxed), 13, 0);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_expr_instantiate1(x_1, x_6);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_16 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(x_2, x_3, x_4, x_5, x_15, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lambda__1___closed__1;
x_20 = lean_array_push(x_19, x_6);
x_21 = 0;
x_22 = 1;
x_23 = 1;
x_24 = l_Lean_Meta_mkLambdaFVars(x_20, x_17, x_21, x_22, x_23, x_10, x_11, x_12, x_13, x_18);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
x_25 = !lean_is_exclusive(x_16);
if (x_25 == 0)
{
return x_16;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_16, 0);
x_27 = lean_ctor_get(x_16, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_16);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_expr_instantiate1(x_1, x_6);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_16 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(x_2, x_3, x_4, x_5, x_15, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lambda__1___closed__1;
x_20 = lean_array_push(x_19, x_6);
x_21 = 0;
x_22 = 1;
x_23 = 1;
x_24 = l_Lean_Meta_mkForallFVars(x_20, x_17, x_21, x_22, x_23, x_10, x_11, x_12, x_13, x_18);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
x_25 = !lean_is_exclusive(x_16);
if (x_25 == 0)
{
return x_16;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_16, 0);
x_27 = lean_ctor_get(x_16, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_16);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_expr_instantiate1(x_1, x_6);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_16 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(x_2, x_3, x_4, x_5, x_15, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lambda__1___closed__1;
x_20 = lean_array_push(x_19, x_6);
x_21 = 0;
x_22 = 1;
x_23 = l_Lean_Meta_mkLambdaFVars(x_20, x_17, x_21, x_21, x_22, x_10, x_11, x_12, x_13, x_18);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
x_24 = !lean_is_exclusive(x_16);
if (x_24 == 0)
{
return x_16;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_16, 0);
x_26 = lean_ctor_get(x_16, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_16);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_dec(x_6);
switch (lean_obj_tag(x_1)) {
case 4:
{
uint8_t x_15; 
x_15 = l_Lean_Expr_isConstOf(x_1, x_2);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
lean_object* x_17; 
x_17 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec(x_2, x_3, x_4, x_5, x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_17;
}
}
case 5:
{
lean_object* x_18; lean_object* x_19; 
lean_inc(x_1);
x_18 = l_Lean_Meta_matchMatcherApp_x3f___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__1(x_2, x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_1);
x_21 = l_Lean_Meta_toCasesOnApp_x3f(x_1, x_10, x_11, x_12, x_13, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp(x_2, x_3, x_4, x_5, x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_23);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_81; 
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
x_26 = lean_ctor_get(x_22, 0);
lean_inc(x_26);
lean_dec(x_22);
lean_inc(x_1);
lean_inc(x_3);
lean_inc(x_2);
x_81 = l_Lean_Elab_Structural_recArgHasLooseBVarsAt(x_2, x_3, x_1);
if (x_81 == 0)
{
uint8_t x_82; 
x_82 = 1;
x_27 = x_82;
goto block_80;
}
else
{
uint8_t x_83; 
x_83 = 0;
x_27 = x_83;
goto block_80;
}
block_80:
{
if (x_27 == 0)
{
uint8_t x_28; lean_object* x_29; lean_object* x_30; 
x_28 = 1;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_5);
x_29 = l_Lean_Meta_CasesOnApp_addArg_x3f(x_26, x_5, x_28, x_10, x_11, x_12, x_13, x_25);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp(x_2, x_3, x_4, x_5, x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_31);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; size_t x_39; size_t x_40; lean_object* x_41; 
x_33 = lean_ctor_get(x_29, 1);
lean_inc(x_33);
lean_dec(x_29);
x_34 = lean_ctor_get(x_30, 0);
lean_inc(x_34);
lean_dec(x_30);
x_35 = lean_ctor_get(x_34, 6);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 7);
lean_inc(x_36);
x_37 = l_Array_zip___rarg(x_35, x_36);
lean_dec(x_35);
x_38 = lean_array_get_size(x_37);
x_39 = lean_usize_of_nat(x_38);
lean_dec(x_38);
x_40 = 0;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_41 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__5(x_2, x_3, x_4, x_1, x_39, x_40, x_37, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_33);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; size_t x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_ctor_get(x_34, 8);
lean_inc(x_44);
x_45 = lean_array_get_size(x_44);
x_46 = lean_usize_of_nat(x_45);
lean_dec(x_45);
x_47 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__6(x_2, x_3, x_4, x_5, x_46, x_40, x_44, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_43);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; 
x_49 = lean_ctor_get(x_47, 0);
x_50 = lean_ctor_get(x_34, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_34, 1);
lean_inc(x_51);
x_52 = lean_ctor_get(x_34, 2);
lean_inc(x_52);
x_53 = lean_ctor_get(x_34, 3);
lean_inc(x_53);
x_54 = lean_ctor_get(x_34, 4);
lean_inc(x_54);
x_55 = lean_ctor_get(x_34, 5);
lean_inc(x_55);
x_56 = lean_ctor_get_uint8(x_34, sizeof(void*)*9);
lean_dec(x_34);
x_57 = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(x_57, 0, x_50);
lean_ctor_set(x_57, 1, x_51);
lean_ctor_set(x_57, 2, x_52);
lean_ctor_set(x_57, 3, x_53);
lean_ctor_set(x_57, 4, x_54);
lean_ctor_set(x_57, 5, x_55);
lean_ctor_set(x_57, 6, x_42);
lean_ctor_set(x_57, 7, x_36);
lean_ctor_set(x_57, 8, x_49);
lean_ctor_set_uint8(x_57, sizeof(void*)*9, x_56);
x_58 = l_Lean_Meta_CasesOnApp_toExpr(x_57);
lean_ctor_set(x_47, 0, x_58);
return x_47;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_59 = lean_ctor_get(x_47, 0);
x_60 = lean_ctor_get(x_47, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_47);
x_61 = lean_ctor_get(x_34, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_34, 1);
lean_inc(x_62);
x_63 = lean_ctor_get(x_34, 2);
lean_inc(x_63);
x_64 = lean_ctor_get(x_34, 3);
lean_inc(x_64);
x_65 = lean_ctor_get(x_34, 4);
lean_inc(x_65);
x_66 = lean_ctor_get(x_34, 5);
lean_inc(x_66);
x_67 = lean_ctor_get_uint8(x_34, sizeof(void*)*9);
lean_dec(x_34);
x_68 = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(x_68, 0, x_61);
lean_ctor_set(x_68, 1, x_62);
lean_ctor_set(x_68, 2, x_63);
lean_ctor_set(x_68, 3, x_64);
lean_ctor_set(x_68, 4, x_65);
lean_ctor_set(x_68, 5, x_66);
lean_ctor_set(x_68, 6, x_42);
lean_ctor_set(x_68, 7, x_36);
lean_ctor_set(x_68, 8, x_59);
lean_ctor_set_uint8(x_68, sizeof(void*)*9, x_67);
x_69 = l_Lean_Meta_CasesOnApp_toExpr(x_68);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_60);
return x_70;
}
}
else
{
uint8_t x_71; 
lean_dec(x_42);
lean_dec(x_36);
lean_dec(x_34);
x_71 = !lean_is_exclusive(x_47);
if (x_71 == 0)
{
return x_47;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_47, 0);
x_73 = lean_ctor_get(x_47, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_47);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_36);
lean_dec(x_34);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_75 = !lean_is_exclusive(x_41);
if (x_75 == 0)
{
return x_41;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_41, 0);
x_77 = lean_ctor_get(x_41, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_41);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
}
else
{
lean_object* x_79; 
lean_dec(x_26);
x_79 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp(x_2, x_3, x_4, x_5, x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_25);
return x_79;
}
}
}
}
else
{
uint8_t x_84; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_84 = !lean_is_exclusive(x_21);
if (x_84 == 0)
{
return x_21;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_21, 0);
x_86 = lean_ctor_get(x_21, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_21);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
else
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; uint8_t x_154; 
x_88 = lean_ctor_get(x_18, 1);
lean_inc(x_88);
lean_dec(x_18);
x_89 = lean_ctor_get(x_19, 0);
lean_inc(x_89);
lean_dec(x_19);
lean_inc(x_1);
lean_inc(x_3);
lean_inc(x_2);
x_154 = l_Lean_Elab_Structural_recArgHasLooseBVarsAt(x_2, x_3, x_1);
if (x_154 == 0)
{
uint8_t x_155; 
x_155 = 1;
x_90 = x_155;
goto block_153;
}
else
{
uint8_t x_156; 
x_156 = 0;
x_90 = x_156;
goto block_153;
}
block_153:
{
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_5);
x_91 = l_Lean_Meta_MatcherApp_addArg_x3f(x_89, x_5, x_10, x_11, x_12, x_13, x_88);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp(x_2, x_3, x_4, x_5, x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_93);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_91, 1);
lean_inc(x_95);
lean_dec(x_91);
x_96 = lean_ctor_get(x_92, 0);
lean_inc(x_96);
lean_dec(x_92);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_5);
lean_inc(x_96);
x_97 = l_Lean_Elab_Structural_refinedArgType(x_96, x_5, x_10, x_11, x_12, x_13, x_95);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; uint8_t x_100; uint8_t x_145; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
x_145 = lean_unbox(x_98);
lean_dec(x_98);
if (x_145 == 0)
{
uint8_t x_146; 
x_146 = 1;
x_100 = x_146;
goto block_144;
}
else
{
uint8_t x_147; 
x_147 = 0;
x_100 = x_147;
goto block_144;
}
block_144:
{
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; size_t x_105; size_t x_106; lean_object* x_107; 
x_101 = lean_ctor_get(x_96, 7);
lean_inc(x_101);
x_102 = lean_ctor_get(x_96, 6);
lean_inc(x_102);
x_103 = l_Array_zip___rarg(x_101, x_102);
lean_dec(x_101);
x_104 = lean_array_get_size(x_103);
x_105 = lean_usize_of_nat(x_104);
lean_dec(x_104);
x_106 = 0;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_107 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__9(x_2, x_3, x_4, x_1, x_105, x_106, x_103, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_99);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; size_t x_112; lean_object* x_113; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = lean_ctor_get(x_96, 5);
lean_inc(x_110);
x_111 = lean_array_get_size(x_110);
x_112 = lean_usize_of_nat(x_111);
lean_dec(x_111);
x_113 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__10(x_2, x_3, x_4, x_5, x_112, x_106, x_110, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_109);
if (lean_obj_tag(x_113) == 0)
{
uint8_t x_114; 
x_114 = !lean_is_exclusive(x_113);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_115 = lean_ctor_get(x_113, 0);
x_116 = lean_ctor_get(x_96, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_96, 1);
lean_inc(x_117);
x_118 = lean_ctor_get(x_96, 2);
lean_inc(x_118);
x_119 = lean_ctor_get(x_96, 3);
lean_inc(x_119);
x_120 = lean_ctor_get(x_96, 4);
lean_inc(x_120);
x_121 = lean_ctor_get(x_96, 8);
lean_inc(x_121);
lean_dec(x_96);
x_122 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_122, 0, x_116);
lean_ctor_set(x_122, 1, x_117);
lean_ctor_set(x_122, 2, x_118);
lean_ctor_set(x_122, 3, x_119);
lean_ctor_set(x_122, 4, x_120);
lean_ctor_set(x_122, 5, x_115);
lean_ctor_set(x_122, 6, x_102);
lean_ctor_set(x_122, 7, x_108);
lean_ctor_set(x_122, 8, x_121);
x_123 = l_Lean_Meta_MatcherApp_toExpr(x_122);
lean_ctor_set(x_113, 0, x_123);
return x_113;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_124 = lean_ctor_get(x_113, 0);
x_125 = lean_ctor_get(x_113, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_113);
x_126 = lean_ctor_get(x_96, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_96, 1);
lean_inc(x_127);
x_128 = lean_ctor_get(x_96, 2);
lean_inc(x_128);
x_129 = lean_ctor_get(x_96, 3);
lean_inc(x_129);
x_130 = lean_ctor_get(x_96, 4);
lean_inc(x_130);
x_131 = lean_ctor_get(x_96, 8);
lean_inc(x_131);
lean_dec(x_96);
x_132 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_132, 0, x_126);
lean_ctor_set(x_132, 1, x_127);
lean_ctor_set(x_132, 2, x_128);
lean_ctor_set(x_132, 3, x_129);
lean_ctor_set(x_132, 4, x_130);
lean_ctor_set(x_132, 5, x_124);
lean_ctor_set(x_132, 6, x_102);
lean_ctor_set(x_132, 7, x_108);
lean_ctor_set(x_132, 8, x_131);
x_133 = l_Lean_Meta_MatcherApp_toExpr(x_132);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_125);
return x_134;
}
}
else
{
uint8_t x_135; 
lean_dec(x_108);
lean_dec(x_102);
lean_dec(x_96);
x_135 = !lean_is_exclusive(x_113);
if (x_135 == 0)
{
return x_113;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_113, 0);
x_137 = lean_ctor_get(x_113, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_113);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
return x_138;
}
}
}
else
{
uint8_t x_139; 
lean_dec(x_102);
lean_dec(x_96);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_139 = !lean_is_exclusive(x_107);
if (x_139 == 0)
{
return x_107;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_107, 0);
x_141 = lean_ctor_get(x_107, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_107);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
return x_142;
}
}
}
else
{
lean_object* x_143; 
lean_dec(x_96);
x_143 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp(x_2, x_3, x_4, x_5, x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_99);
return x_143;
}
}
}
else
{
uint8_t x_148; 
lean_dec(x_96);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_148 = !lean_is_exclusive(x_97);
if (x_148 == 0)
{
return x_97;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_97, 0);
x_150 = lean_ctor_get(x_97, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_97);
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
return x_151;
}
}
}
}
else
{
lean_object* x_152; 
lean_dec(x_89);
x_152 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp(x_2, x_3, x_4, x_5, x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_88);
return x_152;
}
}
}
}
case 6:
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; lean_object* x_161; 
x_157 = lean_ctor_get(x_1, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_1, 1);
lean_inc(x_158);
x_159 = lean_ctor_get(x_1, 2);
lean_inc(x_159);
x_160 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_161 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(x_2, x_3, x_4, x_5, x_158, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; lean_object* x_166; 
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_161, 1);
lean_inc(x_163);
lean_dec(x_161);
x_164 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lambda__1___boxed), 14, 5);
lean_closure_set(x_164, 0, x_159);
lean_closure_set(x_164, 1, x_2);
lean_closure_set(x_164, 2, x_3);
lean_closure_set(x_164, 3, x_4);
lean_closure_set(x_164, 4, x_5);
x_165 = 0;
x_166 = l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__11___rarg(x_157, x_160, x_162, x_164, x_165, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_163);
return x_166;
}
else
{
uint8_t x_167; 
lean_dec(x_159);
lean_dec(x_157);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_167 = !lean_is_exclusive(x_161);
if (x_167 == 0)
{
return x_161;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = lean_ctor_get(x_161, 0);
x_169 = lean_ctor_get(x_161, 1);
lean_inc(x_169);
lean_inc(x_168);
lean_dec(x_161);
x_170 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_170, 0, x_168);
lean_ctor_set(x_170, 1, x_169);
return x_170;
}
}
}
case 7:
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; lean_object* x_175; 
x_171 = lean_ctor_get(x_1, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_1, 1);
lean_inc(x_172);
x_173 = lean_ctor_get(x_1, 2);
lean_inc(x_173);
x_174 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_175 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(x_2, x_3, x_4, x_5, x_172, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; uint8_t x_179; lean_object* x_180; 
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
lean_dec(x_175);
x_178 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lambda__2___boxed), 14, 5);
lean_closure_set(x_178, 0, x_173);
lean_closure_set(x_178, 1, x_2);
lean_closure_set(x_178, 2, x_3);
lean_closure_set(x_178, 3, x_4);
lean_closure_set(x_178, 4, x_5);
x_179 = 0;
x_180 = l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__12___rarg(x_171, x_174, x_176, x_178, x_179, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_177);
return x_180;
}
else
{
uint8_t x_181; 
lean_dec(x_173);
lean_dec(x_171);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_181 = !lean_is_exclusive(x_175);
if (x_181 == 0)
{
return x_175;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_182 = lean_ctor_get(x_175, 0);
x_183 = lean_ctor_get(x_175, 1);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_175);
x_184 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_184, 0, x_182);
lean_ctor_set(x_184, 1, x_183);
return x_184;
}
}
}
case 8:
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_185 = lean_ctor_get(x_1, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_1, 1);
lean_inc(x_186);
x_187 = lean_ctor_get(x_1, 2);
lean_inc(x_187);
x_188 = lean_ctor_get(x_1, 3);
lean_inc(x_188);
lean_dec(x_1);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_189 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(x_2, x_3, x_4, x_5, x_186, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_189, 1);
lean_inc(x_191);
lean_dec(x_189);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_192 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(x_2, x_3, x_4, x_5, x_187, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_191);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; uint8_t x_196; lean_object* x_197; 
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_192, 1);
lean_inc(x_194);
lean_dec(x_192);
x_195 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lambda__3___boxed), 14, 5);
lean_closure_set(x_195, 0, x_188);
lean_closure_set(x_195, 1, x_2);
lean_closure_set(x_195, 2, x_3);
lean_closure_set(x_195, 3, x_4);
lean_closure_set(x_195, 4, x_5);
x_196 = 0;
x_197 = l_Lean_Meta_withLetDecl___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__13___rarg(x_185, x_190, x_193, x_195, x_196, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_194);
return x_197;
}
else
{
uint8_t x_198; 
lean_dec(x_190);
lean_dec(x_188);
lean_dec(x_185);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_198 = !lean_is_exclusive(x_192);
if (x_198 == 0)
{
return x_192;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_199 = lean_ctor_get(x_192, 0);
x_200 = lean_ctor_get(x_192, 1);
lean_inc(x_200);
lean_inc(x_199);
lean_dec(x_192);
x_201 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_200);
return x_201;
}
}
}
else
{
uint8_t x_202; 
lean_dec(x_188);
lean_dec(x_187);
lean_dec(x_185);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_202 = !lean_is_exclusive(x_189);
if (x_202 == 0)
{
return x_189;
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_203 = lean_ctor_get(x_189, 0);
x_204 = lean_ctor_get(x_189, 1);
lean_inc(x_204);
lean_inc(x_203);
lean_dec(x_189);
x_205 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_205, 0, x_203);
lean_ctor_set(x_205, 1, x_204);
return x_205;
}
}
}
case 10:
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_206 = lean_ctor_get(x_1, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_1, 1);
lean_inc(x_207);
x_208 = l_Lean_getRecAppSyntax_x3f(x_1);
lean_dec(x_1);
if (lean_obj_tag(x_208) == 0)
{
lean_object* x_209; 
x_209 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(x_2, x_3, x_4, x_5, x_207, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_209) == 0)
{
uint8_t x_210; 
x_210 = !lean_is_exclusive(x_209);
if (x_210 == 0)
{
lean_object* x_211; lean_object* x_212; 
x_211 = lean_ctor_get(x_209, 0);
x_212 = l_Lean_Expr_mdata___override(x_206, x_211);
lean_ctor_set(x_209, 0, x_212);
return x_209;
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_213 = lean_ctor_get(x_209, 0);
x_214 = lean_ctor_get(x_209, 1);
lean_inc(x_214);
lean_inc(x_213);
lean_dec(x_209);
x_215 = l_Lean_Expr_mdata___override(x_206, x_213);
x_216 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_214);
return x_216;
}
}
else
{
uint8_t x_217; 
lean_dec(x_206);
x_217 = !lean_is_exclusive(x_209);
if (x_217 == 0)
{
return x_209;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_218 = lean_ctor_get(x_209, 0);
x_219 = lean_ctor_get(x_209, 1);
lean_inc(x_219);
lean_inc(x_218);
lean_dec(x_209);
x_220 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_220, 0, x_218);
lean_ctor_set(x_220, 1, x_219);
return x_220;
}
}
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
lean_dec(x_206);
x_221 = lean_ctor_get(x_208, 0);
lean_inc(x_221);
lean_dec(x_208);
x_222 = lean_ctor_get(x_12, 5);
lean_inc(x_222);
x_223 = l_Lean_replaceRef(x_221, x_222);
lean_dec(x_222);
lean_dec(x_221);
x_224 = lean_ctor_get(x_12, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_12, 1);
lean_inc(x_225);
x_226 = lean_ctor_get(x_12, 2);
lean_inc(x_226);
x_227 = lean_ctor_get(x_12, 3);
lean_inc(x_227);
x_228 = lean_ctor_get(x_12, 4);
lean_inc(x_228);
x_229 = lean_ctor_get(x_12, 6);
lean_inc(x_229);
x_230 = lean_ctor_get(x_12, 7);
lean_inc(x_230);
x_231 = lean_ctor_get(x_12, 8);
lean_inc(x_231);
x_232 = lean_ctor_get(x_12, 9);
lean_inc(x_232);
x_233 = lean_ctor_get(x_12, 10);
lean_inc(x_233);
lean_dec(x_12);
x_234 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_234, 0, x_224);
lean_ctor_set(x_234, 1, x_225);
lean_ctor_set(x_234, 2, x_226);
lean_ctor_set(x_234, 3, x_227);
lean_ctor_set(x_234, 4, x_228);
lean_ctor_set(x_234, 5, x_223);
lean_ctor_set(x_234, 6, x_229);
lean_ctor_set(x_234, 7, x_230);
lean_ctor_set(x_234, 8, x_231);
lean_ctor_set(x_234, 9, x_232);
lean_ctor_set(x_234, 10, x_233);
x_235 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(x_2, x_3, x_4, x_5, x_207, x_7, x_8, x_9, x_10, x_11, x_234, x_13, x_14);
return x_235;
}
}
case 11:
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_236 = lean_ctor_get(x_1, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_1, 1);
lean_inc(x_237);
x_238 = lean_ctor_get(x_1, 2);
lean_inc(x_238);
lean_dec(x_1);
x_239 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(x_2, x_3, x_4, x_5, x_238, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_239) == 0)
{
uint8_t x_240; 
x_240 = !lean_is_exclusive(x_239);
if (x_240 == 0)
{
lean_object* x_241; lean_object* x_242; 
x_241 = lean_ctor_get(x_239, 0);
x_242 = l_Lean_Expr_proj___override(x_236, x_237, x_241);
lean_ctor_set(x_239, 0, x_242);
return x_239;
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_243 = lean_ctor_get(x_239, 0);
x_244 = lean_ctor_get(x_239, 1);
lean_inc(x_244);
lean_inc(x_243);
lean_dec(x_239);
x_245 = l_Lean_Expr_proj___override(x_236, x_237, x_243);
x_246 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_246, 0, x_245);
lean_ctor_set(x_246, 1, x_244);
return x_246;
}
}
else
{
uint8_t x_247; 
lean_dec(x_237);
lean_dec(x_236);
x_247 = !lean_is_exclusive(x_239);
if (x_247 == 0)
{
return x_239;
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_248 = lean_ctor_get(x_239, 0);
x_249 = lean_ctor_get(x_239, 1);
lean_inc(x_249);
lean_inc(x_248);
lean_dec(x_239);
x_250 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_250, 0, x_248);
lean_ctor_set(x_250, 1, x_249);
return x_250;
}
}
}
default: 
{
lean_object* x_251; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_251 = l_Lean_Elab_ensureNoRecFn(x_2, x_1, x_10, x_11, x_12, x_13, x_14);
return x_251;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
lean_inc(x_5);
x_14 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_containsRecFn(x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_14, 0);
lean_dec(x_18);
lean_ctor_set(x_14, 0, x_5);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_5);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_dec(x_14);
x_22 = lean_box(0);
x_23 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lambda__4(x_5, x_1, x_2, x_3, x_4, x_22, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_21);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
x_16 = lean_usize_dec_lt(x_6, x_5);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_array_uget(x_7, x_6);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_array_uset(x_7, x_6, x_19);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_21 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(x_1, x_2, x_3, x_4, x_18, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = 1;
x_25 = lean_usize_add(x_6, x_24);
x_26 = lean_array_uset(x_20, x_6, x_22);
x_6 = x_25;
x_7 = x_26;
x_15 = x_23;
goto _start;
}
else
{
uint8_t x_28; 
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_21);
if (x_28 == 0)
{
return x_21;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_21, 0);
x_30 = lean_ctor_get(x_21, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_21);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
if (lean_obj_tag(x_5) == 5)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_5, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_5, 1);
lean_inc(x_17);
lean_dec(x_5);
x_18 = lean_array_set(x_6, x_7, x_17);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_7, x_19);
lean_dec(x_7);
x_5 = x_16;
x_6 = x_18;
x_7 = x_20;
goto _start;
}
else
{
lean_object* x_22; 
lean_dec(x_7);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_22 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(x_1, x_2, x_3, x_4, x_5, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_array_get_size(x_6);
x_26 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_27 = 0;
x_28 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp___spec__1(x_1, x_2, x_3, x_4, x_26, x_27, x_6, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_24);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = l_Lean_mkAppN(x_23, x_30);
lean_ctor_set(x_28, 0, x_31);
return x_28;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_28, 0);
x_33 = lean_ctor_get(x_28, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_28);
x_34 = l_Lean_mkAppN(x_23, x_32);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_23);
x_36 = !lean_is_exclusive(x_28);
if (x_36 == 0)
{
return x_28;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_28, 0);
x_38 = lean_ctor_get(x_28, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_28);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_22);
if (x_40 == 0)
{
return x_22;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_22, 0);
x_42 = lean_ctor_get(x_22, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_22);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = l_Lean_Expr_isAppOf(x_5, x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_unsigned_to_nat(0u);
x_16 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_5, x_15);
x_17 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1;
lean_inc(x_16);
x_18 = lean_mk_array(x_16, x_17);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_16, x_19);
lean_dec(x_16);
x_21 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp___spec__2(x_1, x_2, x_3, x_4, x_5, x_18, x_20, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_21;
}
else
{
lean_object* x_22; 
x_22 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_17 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_18 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___spec__1(x_1, x_2, x_3, x_4, x_16, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_17 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_18 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___spec__2(x_1, x_2, x_3, x_4, x_16, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_getMatcherInfo_x3f___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_getMatcherInfo_x3f___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__2(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_matchMatcherApp_x3f___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__3___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_throwError___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__3(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__4(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__5___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__5___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_7);
lean_dec(x_2);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_17 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_18 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__5(x_1, x_2, x_3, x_4, x_16, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_17 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_18 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__6(x_1, x_2, x_3, x_4, x_16, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__7___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__7___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__7___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_throwError___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__7(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__8___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__8(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__9___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__9___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_7);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__9___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__9___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_17 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_18 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__9(x_1, x_2, x_3, x_4, x_16, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_17 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_18 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__10(x_1, x_2, x_3, x_4, x_16, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__11___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_2);
lean_dec(x_2);
x_15 = lean_unbox(x_5);
lean_dec(x_5);
x_16 = l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__11___rarg(x_1, x_14, x_3, x_4, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__11___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__11(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__12___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_2);
lean_dec(x_2);
x_15 = lean_unbox(x_5);
lean_dec(x_5);
x_16 = l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__12___rarg(x_1, x_14, x_3, x_4, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__12___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__12(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__13___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_5);
lean_dec(x_5);
x_15 = l_Lean_Meta_withLetDecl___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__13___rarg(x_1, x_2, x_3, x_4, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__13___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_withLetDecl___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__13(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_17 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_18 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp___spec__1(x_1, x_2, x_3, x_4, x_16, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_18;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Lean_mkHashMapImp___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___lambda__1___closed__1;
x_15 = lean_st_mk_ref(x_14, x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_16);
x_18 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(x_1, x_2, x_3, x_4, x_5, x_16, x_7, x_8, x_9, x_10, x_11, x_12, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_st_ref_get(x_16, x_20);
lean_dec(x_16);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_19);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_16);
x_26 = !lean_is_exclusive(x_18);
if (x_26 == 0)
{
return x_18;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_18, 0);
x_28 = lean_ctor_get(x_18, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_18);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" : ", 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_dec(x_7);
lean_inc(x_1);
x_15 = l_Lean_isTracingEnabledFor___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_1, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_1);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_box(0);
x_20 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___lambda__1(x_2, x_3, x_4, x_5, x_6, x_19, x_8, x_9, x_10, x_11, x_12, x_13, x_18);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_dec(x_15);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_5);
x_22 = lean_infer_type(x_5, x_10, x_11, x_12, x_13, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_5);
x_25 = l_Lean_MessageData_ofExpr(x_5);
x_26 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__5___lambda__2___closed__6;
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___lambda__2___closed__2;
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_MessageData_ofExpr(x_23);
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_26);
x_33 = l_Lean_addTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__2(x_1, x_32, x_8, x_9, x_10, x_11, x_12, x_13, x_24);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___lambda__1(x_2, x_3, x_4, x_5, x_6, x_34, x_8, x_9, x_10, x_11, x_12, x_13, x_35);
lean_dec(x_34);
return x_36;
}
else
{
uint8_t x_37; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_22);
if (x_37 == 0)
{
return x_22;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_22, 0);
x_39 = lean_ctor_get(x_22, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_22);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Elab", 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("definition", 10);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("wf", 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__1;
x_2 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__2;
x_3 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__3;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("replaceRecApps:", 15);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__4;
x_14 = l_Lean_isTracingEnabledFor___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_13, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_box(0);
x_19 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___lambda__2(x_13, x_1, x_2, x_3, x_4, x_5, x_18, x_6, x_7, x_8, x_9, x_10, x_11, x_17);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_dec(x_14);
lean_inc(x_5);
x_21 = l_Lean_indentExpr(x_5);
x_22 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__6;
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__5___lambda__2___closed__6;
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_addTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__2(x_13, x_25, x_6, x_7, x_8, x_9, x_10, x_11, x_20);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___lambda__2(x_13, x_1, x_2, x_3, x_4, x_5, x_27, x_6, x_7, x_8, x_9, x_10, x_11, x_28);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_6);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___spec__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = lean_apply_9(x_1, x_4, x_5, x_2, x_3, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___spec__1___rarg___lambda__1), 10, 3);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_3);
lean_closure_set(x_10, 2, x_4);
x_11 = 0;
x_12 = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___rarg(x_1, x_11, x_10, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_12);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___spec__1___rarg), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = l_Lean_LocalDecl_type(x_1);
x_13 = lean_array_get_size(x_3);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_lt(x_14, x_13);
lean_dec(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; lean_object* x_25; 
x_16 = l_Lean_instInhabitedExpr;
x_17 = l___private_Init_Util_0__outOfBounds___rarg(x_16);
x_18 = l_Lean_Expr_replaceFVar(x_12, x_2, x_17);
lean_dec(x_17);
lean_dec(x_12);
x_19 = l_Lean_mkArrow(x_18, x_4, x_9, x_10, x_11);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = 0;
x_23 = 1;
x_24 = 1;
lean_inc(x_20);
x_25 = l_Lean_Meta_mkLambdaFVars(x_3, x_20, x_22, x_23, x_24, x_7, x_8, x_9, x_10, x_21);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_Meta_getLevel(x_20, x_7, x_8, x_9, x_10, x_27);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_28, 0, x_31);
return x_28;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_28, 0);
x_33 = lean_ctor_get(x_28, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_28);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_26);
lean_ctor_set(x_34, 1, x_32);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_26);
x_36 = !lean_is_exclusive(x_28);
if (x_36 == 0)
{
return x_28;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_28, 0);
x_38 = lean_ctor_get(x_28, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_28);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_20);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_40 = !lean_is_exclusive(x_25);
if (x_40 == 0)
{
return x_25;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_25, 0);
x_42 = lean_ctor_get(x_25, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_25);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; lean_object* x_52; 
x_44 = lean_array_fget(x_3, x_14);
x_45 = l_Lean_Expr_replaceFVar(x_12, x_2, x_44);
lean_dec(x_44);
lean_dec(x_12);
x_46 = l_Lean_mkArrow(x_45, x_4, x_9, x_10, x_11);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = 0;
x_50 = 1;
x_51 = 1;
lean_inc(x_47);
x_52 = l_Lean_Meta_mkLambdaFVars(x_3, x_47, x_49, x_50, x_51, x_7, x_8, x_9, x_10, x_48);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = l_Lean_Meta_getLevel(x_47, x_7, x_8, x_9, x_10, x_54);
if (lean_obj_tag(x_55) == 0)
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_55, 0);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_53);
lean_ctor_set(x_58, 1, x_57);
lean_ctor_set(x_55, 0, x_58);
return x_55;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_55, 0);
x_60 = lean_ctor_get(x_55, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_55);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_53);
lean_ctor_set(x_61, 1, x_59);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
else
{
uint8_t x_63; 
lean_dec(x_53);
x_63 = !lean_is_exclusive(x_55);
if (x_63 == 0)
{
return x_55;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_55, 0);
x_65 = lean_ctor_get(x_55, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_55);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_47);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_67 = !lean_is_exclusive(x_52);
if (x_67 == 0)
{
return x_52;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_52, 0);
x_69 = lean_ctor_get(x_52, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_52);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_4);
lean_inc(x_1);
x_12 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn(x_1, x_4, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lambda__2___closed__1;
x_16 = lean_array_push(x_15, x_1);
x_17 = lean_array_push(x_16, x_4);
x_18 = 0;
x_19 = 1;
x_20 = 1;
x_21 = l_Lean_Meta_mkLambdaFVars(x_17, x_13, x_18, x_19, x_20, x_7, x_8, x_9, x_10, x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_12);
if (x_22 == 0)
{
return x_12;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_12, 0);
x_24 = lean_ctor_get(x_12, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_12);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lambda__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; lean_object* x_51; 
x_41 = lean_array_get_size(x_7);
x_42 = lean_unsigned_to_nat(0u);
x_43 = lean_nat_dec_lt(x_42, x_41);
lean_dec(x_41);
x_44 = lean_array_get_size(x_7);
x_45 = lean_unsigned_to_nat(1u);
lean_inc(x_7);
x_46 = l_Array_toSubarray___rarg(x_7, x_45, x_44);
x_47 = l_Array_ofSubarray___rarg(x_46);
x_48 = 0;
x_49 = 1;
x_50 = 1;
x_51 = l_Lean_Meta_mkLambdaFVars(x_47, x_8, x_48, x_49, x_50, x_11, x_12, x_13, x_14, x_15);
if (x_43 == 0)
{
lean_dec(x_7);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = l_Lean_instInhabitedExpr;
x_55 = l___private_Init_Util_0__outOfBounds___rarg(x_54);
x_16 = x_55;
x_17 = x_52;
x_18 = x_53;
goto block_40;
}
else
{
uint8_t x_56; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_51);
if (x_56 == 0)
{
return x_51;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_51, 0);
x_58 = lean_ctor_get(x_51, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_51);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_51, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_51, 1);
lean_inc(x_61);
lean_dec(x_51);
x_62 = lean_array_fget(x_7, x_42);
lean_dec(x_7);
x_16 = x_62;
x_17 = x_60;
x_18 = x_61;
goto block_40;
}
else
{
uint8_t x_63; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_63 = !lean_is_exclusive(x_51);
if (x_63 == 0)
{
return x_51;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_51, 0);
x_65 = lean_ctor_get(x_51, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_51);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
block_40:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_1);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_2);
lean_inc(x_16);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_16);
x_22 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lambda__3___closed__1;
x_23 = lean_array_push(x_22, x_19);
x_24 = lean_array_push(x_23, x_20);
x_25 = lean_array_push(x_24, x_21);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_26 = l_Lean_Meta_mkAppOptM(x_3, x_25, x_11, x_12, x_13, x_14, x_18);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_34; lean_object* x_35; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_LocalDecl_type(x_4);
x_30 = l_Lean_Expr_replaceFVar(x_29, x_5, x_27);
lean_dec(x_27);
lean_dec(x_29);
x_31 = l_Lean_LocalDecl_userName(x_4);
x_32 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lambda__2), 11, 3);
lean_closure_set(x_32, 0, x_16);
lean_closure_set(x_32, 1, x_17);
lean_closure_set(x_32, 2, x_6);
x_33 = 0;
x_34 = 0;
x_35 = l_Lean_Meta_withLocalDecl___at_Lean_Elab_Term_withAuxDecl___spec__1___rarg(x_31, x_33, x_30, x_32, x_34, x_9, x_10, x_11, x_12, x_13, x_14, x_28);
return x_35;
}
else
{
uint8_t x_36; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
x_36 = !lean_is_exclusive(x_26);
if (x_36 == 0)
{
return x_26;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_26, 0);
x_38 = lean_ctor_get(x_26, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_26);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("PSum", 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("inl", 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__1;
x_2 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("inr", 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__1;
x_2 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__4;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("casesOn", 7);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__1;
x_2 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__6;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(7u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_139; 
x_139 = l_Lean_Expr_isFVar(x_1);
if (x_139 == 0)
{
uint8_t x_140; 
x_140 = 0;
x_12 = x_140;
goto block_138;
}
else
{
lean_object* x_141; lean_object* x_142; uint8_t x_143; 
x_141 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__7;
x_142 = lean_unsigned_to_nat(6u);
x_143 = l_Lean_Expr_isAppOfArity(x_3, x_141, x_142);
if (x_143 == 0)
{
uint8_t x_144; 
x_144 = 0;
x_12 = x_144;
goto block_138;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; 
x_145 = lean_unsigned_to_nat(0u);
x_146 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_3, x_145);
x_147 = lean_unsigned_to_nat(3u);
x_148 = lean_nat_sub(x_146, x_147);
x_149 = lean_unsigned_to_nat(1u);
x_150 = lean_nat_sub(x_148, x_149);
lean_dec(x_148);
lean_inc(x_3);
x_151 = l_Lean_Expr_getRevArg_x21(x_3, x_150);
x_152 = lean_expr_eqv(x_151, x_1);
lean_dec(x_151);
if (x_152 == 0)
{
uint8_t x_153; 
lean_dec(x_146);
x_153 = 0;
x_12 = x_153;
goto block_138;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; 
x_154 = lean_unsigned_to_nat(4u);
x_155 = lean_nat_sub(x_146, x_154);
x_156 = lean_nat_sub(x_155, x_149);
lean_dec(x_155);
lean_inc(x_3);
x_157 = l_Lean_Expr_getRevArg_x21(x_3, x_156);
x_158 = l_Lean_Expr_isLambda(x_157);
lean_dec(x_157);
if (x_158 == 0)
{
uint8_t x_159; 
lean_dec(x_146);
x_159 = 0;
x_12 = x_159;
goto block_138;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; 
x_160 = lean_unsigned_to_nat(5u);
x_161 = lean_nat_sub(x_146, x_160);
lean_dec(x_146);
x_162 = lean_nat_sub(x_161, x_149);
lean_dec(x_161);
lean_inc(x_3);
x_163 = l_Lean_Expr_getRevArg_x21(x_3, x_162);
x_164 = l_Lean_Expr_isLambda(x_163);
lean_dec(x_163);
x_12 = x_164;
goto block_138;
}
}
}
}
block_138:
{
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_apply_10(x_4, x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_3, x_14);
x_16 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1;
lean_inc(x_15);
x_17 = lean_mk_array(x_15, x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_15, x_18);
lean_dec(x_15);
x_20 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_3, x_17, x_19);
x_21 = lean_array_get_size(x_20);
x_22 = lean_nat_dec_lt(x_14, x_21);
x_23 = lean_nat_dec_lt(x_18, x_21);
lean_inc(x_2);
x_24 = l_Lean_Expr_fvarId_x21(x_2);
if (x_22 == 0)
{
lean_object* x_135; lean_object* x_136; 
x_135 = l_Lean_instInhabitedExpr;
x_136 = l___private_Init_Util_0__outOfBounds___rarg(x_135);
x_25 = x_136;
goto block_134;
}
else
{
lean_object* x_137; 
x_137 = lean_array_fget(x_20, x_14);
x_25 = x_137;
goto block_134;
}
block_134:
{
lean_object* x_26; 
if (x_23 == 0)
{
lean_object* x_131; lean_object* x_132; 
x_131 = l_Lean_instInhabitedExpr;
x_132 = l___private_Init_Util_0__outOfBounds___rarg(x_131);
x_26 = x_132;
goto block_130;
}
else
{
lean_object* x_133; 
x_133 = lean_array_fget(x_20, x_18);
x_26 = x_133;
goto block_130;
}
block_130:
{
lean_object* x_27; 
lean_inc(x_7);
x_27 = l_Lean_FVarId_getDecl(x_24, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_unsigned_to_nat(2u);
x_31 = lean_nat_dec_lt(x_30, x_21);
lean_inc(x_1);
lean_inc(x_28);
x_32 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lambda__1___boxed), 11, 2);
lean_closure_set(x_32, 0, x_28);
lean_closure_set(x_32, 1, x_1);
if (x_31 == 0)
{
lean_object* x_123; lean_object* x_124; 
x_123 = l_Lean_instInhabitedExpr;
x_124 = l___private_Init_Util_0__outOfBounds___rarg(x_123);
x_33 = x_124;
goto block_122;
}
else
{
lean_object* x_125; 
x_125 = lean_array_fget(x_20, x_30);
x_33 = x_125;
goto block_122;
}
block_122:
{
lean_object* x_34; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_34 = l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___spec__1___rarg(x_33, x_32, x_5, x_6, x_7, x_8, x_9, x_10, x_29);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_unsigned_to_nat(4u);
x_40 = lean_nat_dec_lt(x_39, x_21);
x_41 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__3;
lean_inc(x_4);
lean_inc(x_1);
lean_inc(x_28);
lean_inc(x_26);
lean_inc(x_25);
x_42 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lambda__3___boxed), 15, 6);
lean_closure_set(x_42, 0, x_25);
lean_closure_set(x_42, 1, x_26);
lean_closure_set(x_42, 2, x_41);
lean_closure_set(x_42, 3, x_28);
lean_closure_set(x_42, 4, x_1);
lean_closure_set(x_42, 5, x_4);
if (x_40 == 0)
{
lean_object* x_115; lean_object* x_116; 
x_115 = l_Lean_instInhabitedExpr;
x_116 = l___private_Init_Util_0__outOfBounds___rarg(x_115);
x_43 = x_116;
goto block_114;
}
else
{
lean_object* x_117; 
x_117 = lean_array_fget(x_20, x_39);
x_43 = x_117;
goto block_114;
}
block_114:
{
lean_object* x_44; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_44 = l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___spec__1___rarg(x_43, x_42, x_5, x_6, x_7, x_8, x_9, x_10, x_36);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_unsigned_to_nat(5u);
x_48 = lean_nat_dec_lt(x_47, x_21);
lean_dec(x_21);
x_49 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__5;
lean_inc(x_1);
lean_inc(x_26);
lean_inc(x_25);
x_50 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lambda__3___boxed), 15, 6);
lean_closure_set(x_50, 0, x_25);
lean_closure_set(x_50, 1, x_26);
lean_closure_set(x_50, 2, x_49);
lean_closure_set(x_50, 3, x_28);
lean_closure_set(x_50, 4, x_1);
lean_closure_set(x_50, 5, x_4);
if (x_48 == 0)
{
lean_object* x_107; lean_object* x_108; 
lean_dec(x_20);
x_107 = l_Lean_instInhabitedExpr;
x_108 = l___private_Init_Util_0__outOfBounds___rarg(x_107);
x_51 = x_108;
goto block_106;
}
else
{
lean_object* x_109; 
x_109 = lean_array_fget(x_20, x_47);
lean_dec(x_20);
x_51 = x_109;
goto block_106;
}
block_106:
{
lean_object* x_52; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_52 = l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___spec__1___rarg(x_51, x_50, x_5, x_6, x_7, x_8, x_9, x_10, x_46);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_25);
x_55 = l_Lean_Meta_getLevel(x_25, x_7, x_8, x_9, x_10, x_54);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
lean_inc(x_26);
x_58 = l_Lean_Meta_getLevel(x_26, x_7, x_8, x_9, x_10, x_57);
if (lean_obj_tag(x_58) == 0)
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_60 = lean_ctor_get(x_58, 0);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_56);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_38);
lean_ctor_set(x_64, 1, x_63);
x_65 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__7;
x_66 = l_Lean_Expr_const___override(x_65, x_64);
x_67 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__8;
x_68 = lean_array_push(x_67, x_25);
x_69 = lean_array_push(x_68, x_26);
x_70 = lean_array_push(x_69, x_37);
x_71 = lean_array_push(x_70, x_1);
x_72 = lean_array_push(x_71, x_45);
x_73 = lean_array_push(x_72, x_53);
x_74 = lean_array_push(x_73, x_2);
x_75 = l_Lean_mkAppN(x_66, x_74);
lean_ctor_set(x_58, 0, x_75);
return x_58;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_76 = lean_ctor_get(x_58, 0);
x_77 = lean_ctor_get(x_58, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_58);
x_78 = lean_box(0);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_76);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_56);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_38);
lean_ctor_set(x_81, 1, x_80);
x_82 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__7;
x_83 = l_Lean_Expr_const___override(x_82, x_81);
x_84 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__8;
x_85 = lean_array_push(x_84, x_25);
x_86 = lean_array_push(x_85, x_26);
x_87 = lean_array_push(x_86, x_37);
x_88 = lean_array_push(x_87, x_1);
x_89 = lean_array_push(x_88, x_45);
x_90 = lean_array_push(x_89, x_53);
x_91 = lean_array_push(x_90, x_2);
x_92 = l_Lean_mkAppN(x_83, x_91);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_77);
return x_93;
}
}
else
{
uint8_t x_94; 
lean_dec(x_56);
lean_dec(x_53);
lean_dec(x_45);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_2);
lean_dec(x_1);
x_94 = !lean_is_exclusive(x_58);
if (x_94 == 0)
{
return x_58;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_58, 0);
x_96 = lean_ctor_get(x_58, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_58);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
else
{
uint8_t x_98; 
lean_dec(x_53);
lean_dec(x_45);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_98 = !lean_is_exclusive(x_55);
if (x_98 == 0)
{
return x_55;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_55, 0);
x_100 = lean_ctor_get(x_55, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_55);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
else
{
uint8_t x_102; 
lean_dec(x_45);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_102 = !lean_is_exclusive(x_52);
if (x_102 == 0)
{
return x_52;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_52, 0);
x_104 = lean_ctor_get(x_52, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_52);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
}
else
{
uint8_t x_110; 
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_110 = !lean_is_exclusive(x_44);
if (x_110 == 0)
{
return x_44;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_44, 0);
x_112 = lean_ctor_get(x_44, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_44);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
}
else
{
uint8_t x_118; 
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_118 = !lean_is_exclusive(x_34);
if (x_118 == 0)
{
return x_34;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_34, 0);
x_120 = lean_ctor_get(x_34, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_34);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
}
}
else
{
uint8_t x_126; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_126 = !lean_is_exclusive(x_27);
if (x_126 == 0)
{
return x_27;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_27, 0);
x_128 = lean_ctor_get(x_27, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_27);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_4);
return x_16;
}
}
static lean_object* _init_l_panic___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_instInhabitedTermElabM(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_panic___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___spec__1___closed__1;
x_10 = lean_panic_fn(x_9, x_1);
x_11 = lean_apply_7(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_5);
lean_inc(x_1);
x_13 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn(x_1, x_5, x_2, x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lambda__3___closed__1;
x_17 = lean_array_push(x_16, x_4);
x_18 = lean_array_push(x_17, x_1);
x_19 = lean_array_push(x_18, x_5);
x_20 = 0;
x_21 = 1;
x_22 = 1;
x_23 = l_Lean_Meta_mkLambdaFVars(x_19, x_14, x_20, x_21, x_22, x_8, x_9, x_10, x_11, x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_13);
if (x_24 == 0)
{
return x_13;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_13, 0);
x_26 = lean_ctor_get(x_13, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_13);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("PSigma", 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("mk", 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lambda__2___closed__1;
x_2 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lambda__2___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_15 = lean_array_get_size(x_6);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_lt(x_16, x_15);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_dec_lt(x_18, x_15);
lean_dec(x_15);
x_20 = lean_array_get_size(x_6);
x_21 = lean_unsigned_to_nat(2u);
lean_inc(x_6);
x_22 = l_Array_toSubarray___rarg(x_6, x_21, x_20);
x_23 = l_Array_ofSubarray___rarg(x_22);
x_24 = 0;
x_25 = 1;
x_26 = 1;
x_27 = l_Lean_Meta_mkLambdaFVars(x_23, x_7, x_24, x_25, x_26, x_10, x_11, x_12, x_13, x_14);
if (x_17 == 0)
{
lean_object* x_73; lean_object* x_74; 
x_73 = l_Lean_instInhabitedExpr;
x_74 = l___private_Init_Util_0__outOfBounds___rarg(x_73);
x_28 = x_74;
goto block_72;
}
else
{
lean_object* x_75; 
x_75 = lean_array_fget(x_6, x_16);
x_28 = x_75;
goto block_72;
}
block_72:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
if (x_19 == 0)
{
lean_dec(x_6);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_27, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_27, 1);
lean_inc(x_58);
lean_dec(x_27);
x_59 = l_Lean_instInhabitedExpr;
x_60 = l___private_Init_Util_0__outOfBounds___rarg(x_59);
x_29 = x_60;
x_30 = x_57;
x_31 = x_58;
goto block_56;
}
else
{
uint8_t x_61; 
lean_dec(x_28);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_27);
if (x_61 == 0)
{
return x_27;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_27, 0);
x_63 = lean_ctor_get(x_27, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_27);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_27, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_27, 1);
lean_inc(x_66);
lean_dec(x_27);
x_67 = lean_array_fget(x_6, x_18);
lean_dec(x_6);
x_29 = x_67;
x_30 = x_65;
x_31 = x_66;
goto block_56;
}
else
{
uint8_t x_68; 
lean_dec(x_28);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_27);
if (x_68 == 0)
{
return x_27;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_27, 0);
x_70 = lean_ctor_get(x_27, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_27);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
block_56:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_1);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_2);
lean_inc(x_28);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_28);
lean_inc(x_29);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_29);
x_36 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lambda__2___closed__4;
x_37 = lean_array_push(x_36, x_32);
x_38 = lean_array_push(x_37, x_33);
x_39 = lean_array_push(x_38, x_34);
x_40 = lean_array_push(x_39, x_35);
x_41 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lambda__2___closed__3;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_42 = l_Lean_Meta_mkAppOptM(x_41, x_40, x_10, x_11, x_12, x_13, x_31);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_50; lean_object* x_51; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l_Lean_LocalDecl_type(x_3);
x_46 = l_Lean_Expr_replaceFVar(x_45, x_4, x_43);
lean_dec(x_43);
lean_dec(x_45);
x_47 = l_Lean_LocalDecl_userName(x_3);
x_48 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lambda__1), 12, 4);
lean_closure_set(x_48, 0, x_29);
lean_closure_set(x_48, 1, x_30);
lean_closure_set(x_48, 2, x_5);
lean_closure_set(x_48, 3, x_28);
x_49 = 0;
x_50 = 0;
x_51 = l_Lean_Meta_withLocalDecl___at_Lean_Elab_Term_withAuxDecl___spec__1___rarg(x_47, x_49, x_46, x_48, x_50, x_8, x_9, x_10, x_11, x_12, x_13, x_44);
return x_51;
}
else
{
uint8_t x_52; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
x_52 = !lean_is_exclusive(x_42);
if (x_52 == 0)
{
return x_42;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_42, 0);
x_54 = lean_ctor_get(x_42, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_42);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Elab.PreDefinition.WF.Fix", 30);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_private.Lean.Elab.PreDefinition.WF.Fix.0.Lean.Elab.WF.processPSigmaCasesOn", 75);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unreachable code has been reached", 33);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__1;
x_2 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__2;
x_3 = lean_unsigned_to_nat(147u);
x_4 = lean_unsigned_to_nat(49u);
x_5 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lambda__2___closed__1;
x_2 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__6;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(6u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_160; 
x_160 = l_Lean_Expr_isFVar(x_1);
if (x_160 == 0)
{
uint8_t x_161; 
x_161 = 0;
x_12 = x_161;
goto block_159;
}
else
{
lean_object* x_162; lean_object* x_163; uint8_t x_164; 
x_162 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__5;
x_163 = lean_unsigned_to_nat(5u);
x_164 = l_Lean_Expr_isAppOfArity(x_3, x_162, x_163);
if (x_164 == 0)
{
uint8_t x_165; 
x_165 = 0;
x_12 = x_165;
goto block_159;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; 
x_166 = lean_unsigned_to_nat(0u);
x_167 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_3, x_166);
x_168 = lean_unsigned_to_nat(3u);
x_169 = lean_nat_sub(x_167, x_168);
x_170 = lean_unsigned_to_nat(1u);
x_171 = lean_nat_sub(x_169, x_170);
lean_dec(x_169);
lean_inc(x_3);
x_172 = l_Lean_Expr_getRevArg_x21(x_3, x_171);
x_173 = lean_expr_eqv(x_172, x_1);
lean_dec(x_172);
if (x_173 == 0)
{
uint8_t x_174; 
lean_dec(x_167);
x_174 = 0;
x_12 = x_174;
goto block_159;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; uint8_t x_179; 
x_175 = lean_unsigned_to_nat(4u);
x_176 = lean_nat_sub(x_167, x_175);
lean_dec(x_167);
x_177 = lean_nat_sub(x_176, x_170);
lean_dec(x_176);
lean_inc(x_3);
x_178 = l_Lean_Expr_getRevArg_x21(x_3, x_177);
x_179 = l_Lean_Expr_isLambda(x_178);
if (x_179 == 0)
{
uint8_t x_180; 
lean_dec(x_178);
x_180 = 0;
x_12 = x_180;
goto block_159;
}
else
{
lean_object* x_181; uint8_t x_182; 
x_181 = l_Lean_Expr_bindingBody_x21(x_178);
lean_dec(x_178);
x_182 = l_Lean_Expr_isLambda(x_181);
lean_dec(x_181);
x_12 = x_182;
goto block_159;
}
}
}
}
block_159:
{
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_1);
x_13 = lean_apply_9(x_4, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_3, x_14);
x_16 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1;
lean_inc(x_15);
x_17 = lean_mk_array(x_15, x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_15, x_18);
lean_dec(x_15);
lean_inc(x_3);
x_20 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_3, x_17, x_19);
x_21 = l_Lean_Expr_getAppFn(x_3);
lean_dec(x_3);
x_22 = l_Lean_Expr_constLevels_x21(x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_20);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_23 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__4;
x_24 = l_panic___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___spec__1(x_23, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_26 = x_22;
} else {
 lean_dec_ref(x_22);
 x_26 = lean_box(0);
}
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_26);
lean_dec(x_20);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_27 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__4;
x_28 = l_panic___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___spec__1(x_27, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_28;
}
else
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_20);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_30 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__4;
x_31 = l_panic___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___spec__1(x_30, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_31;
}
else
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; 
x_33 = lean_ctor_get(x_25, 0);
lean_inc(x_33);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_34 = x_25;
} else {
 lean_dec_ref(x_25);
 x_34 = lean_box(0);
}
x_35 = lean_ctor_get(x_29, 0);
lean_inc(x_35);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_36 = x_29;
} else {
 lean_dec_ref(x_29);
 x_36 = lean_box(0);
}
x_37 = lean_array_get_size(x_20);
x_38 = lean_nat_dec_lt(x_14, x_37);
x_39 = lean_nat_dec_lt(x_18, x_37);
lean_inc(x_2);
x_40 = l_Lean_Expr_fvarId_x21(x_2);
if (x_38 == 0)
{
lean_object* x_154; lean_object* x_155; 
x_154 = l_Lean_instInhabitedExpr;
x_155 = l___private_Init_Util_0__outOfBounds___rarg(x_154);
x_41 = x_155;
goto block_153;
}
else
{
lean_object* x_156; 
x_156 = lean_array_fget(x_20, x_14);
x_41 = x_156;
goto block_153;
}
block_153:
{
lean_object* x_42; 
if (x_39 == 0)
{
lean_object* x_150; lean_object* x_151; 
x_150 = l_Lean_instInhabitedExpr;
x_151 = l___private_Init_Util_0__outOfBounds___rarg(x_150);
x_42 = x_151;
goto block_149;
}
else
{
lean_object* x_152; 
x_152 = lean_array_fget(x_20, x_18);
x_42 = x_152;
goto block_149;
}
block_149:
{
lean_object* x_43; 
lean_inc(x_7);
x_43 = l_Lean_FVarId_getDecl(x_40, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_unsigned_to_nat(2u);
x_47 = lean_nat_dec_lt(x_46, x_37);
lean_inc(x_1);
lean_inc(x_44);
x_48 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lambda__1___boxed), 11, 2);
lean_closure_set(x_48, 0, x_44);
lean_closure_set(x_48, 1, x_1);
if (x_47 == 0)
{
lean_object* x_142; lean_object* x_143; 
x_142 = l_Lean_instInhabitedExpr;
x_143 = l___private_Init_Util_0__outOfBounds___rarg(x_142);
x_49 = x_143;
goto block_141;
}
else
{
lean_object* x_144; 
x_144 = lean_array_fget(x_20, x_46);
x_49 = x_144;
goto block_141;
}
block_141:
{
lean_object* x_50; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_50 = l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___spec__1___rarg(x_49, x_48, x_5, x_6, x_7, x_8, x_9, x_10, x_45);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_ctor_get(x_51, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_dec(x_51);
x_55 = lean_unsigned_to_nat(4u);
x_56 = lean_nat_dec_lt(x_55, x_37);
lean_dec(x_37);
lean_inc(x_1);
lean_inc(x_42);
lean_inc(x_41);
x_57 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lambda__2___boxed), 14, 5);
lean_closure_set(x_57, 0, x_41);
lean_closure_set(x_57, 1, x_42);
lean_closure_set(x_57, 2, x_44);
lean_closure_set(x_57, 3, x_1);
lean_closure_set(x_57, 4, x_4);
if (x_56 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_20);
x_58 = l_Lean_instInhabitedExpr;
x_59 = l___private_Init_Util_0__outOfBounds___rarg(x_58);
x_60 = l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___spec__1___rarg(x_59, x_57, x_5, x_6, x_7, x_8, x_9, x_10, x_52);
if (lean_obj_tag(x_60) == 0)
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_62 = lean_ctor_get(x_60, 0);
x_63 = lean_box(0);
if (lean_is_scalar(x_36)) {
 x_64 = lean_alloc_ctor(1, 2, 0);
} else {
 x_64 = x_36;
}
lean_ctor_set(x_64, 0, x_35);
lean_ctor_set(x_64, 1, x_63);
if (lean_is_scalar(x_34)) {
 x_65 = lean_alloc_ctor(1, 2, 0);
} else {
 x_65 = x_34;
}
lean_ctor_set(x_65, 0, x_33);
lean_ctor_set(x_65, 1, x_64);
if (lean_is_scalar(x_26)) {
 x_66 = lean_alloc_ctor(1, 2, 0);
} else {
 x_66 = x_26;
}
lean_ctor_set(x_66, 0, x_54);
lean_ctor_set(x_66, 1, x_65);
x_67 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__5;
x_68 = l_Lean_Expr_const___override(x_67, x_66);
x_69 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__6;
x_70 = lean_array_push(x_69, x_41);
x_71 = lean_array_push(x_70, x_42);
x_72 = lean_array_push(x_71, x_53);
x_73 = lean_array_push(x_72, x_1);
x_74 = lean_array_push(x_73, x_62);
x_75 = lean_array_push(x_74, x_2);
x_76 = l_Lean_mkAppN(x_68, x_75);
lean_ctor_set(x_60, 0, x_76);
return x_60;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_77 = lean_ctor_get(x_60, 0);
x_78 = lean_ctor_get(x_60, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_60);
x_79 = lean_box(0);
if (lean_is_scalar(x_36)) {
 x_80 = lean_alloc_ctor(1, 2, 0);
} else {
 x_80 = x_36;
}
lean_ctor_set(x_80, 0, x_35);
lean_ctor_set(x_80, 1, x_79);
if (lean_is_scalar(x_34)) {
 x_81 = lean_alloc_ctor(1, 2, 0);
} else {
 x_81 = x_34;
}
lean_ctor_set(x_81, 0, x_33);
lean_ctor_set(x_81, 1, x_80);
if (lean_is_scalar(x_26)) {
 x_82 = lean_alloc_ctor(1, 2, 0);
} else {
 x_82 = x_26;
}
lean_ctor_set(x_82, 0, x_54);
lean_ctor_set(x_82, 1, x_81);
x_83 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__5;
x_84 = l_Lean_Expr_const___override(x_83, x_82);
x_85 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__6;
x_86 = lean_array_push(x_85, x_41);
x_87 = lean_array_push(x_86, x_42);
x_88 = lean_array_push(x_87, x_53);
x_89 = lean_array_push(x_88, x_1);
x_90 = lean_array_push(x_89, x_77);
x_91 = lean_array_push(x_90, x_2);
x_92 = l_Lean_mkAppN(x_84, x_91);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_78);
return x_93;
}
}
else
{
uint8_t x_94; 
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_26);
lean_dec(x_2);
lean_dec(x_1);
x_94 = !lean_is_exclusive(x_60);
if (x_94 == 0)
{
return x_60;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_60, 0);
x_96 = lean_ctor_get(x_60, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_60);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
else
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_array_fget(x_20, x_55);
lean_dec(x_20);
x_99 = l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___spec__1___rarg(x_98, x_57, x_5, x_6, x_7, x_8, x_9, x_10, x_52);
if (lean_obj_tag(x_99) == 0)
{
uint8_t x_100; 
x_100 = !lean_is_exclusive(x_99);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_101 = lean_ctor_get(x_99, 0);
x_102 = lean_box(0);
if (lean_is_scalar(x_36)) {
 x_103 = lean_alloc_ctor(1, 2, 0);
} else {
 x_103 = x_36;
}
lean_ctor_set(x_103, 0, x_35);
lean_ctor_set(x_103, 1, x_102);
if (lean_is_scalar(x_34)) {
 x_104 = lean_alloc_ctor(1, 2, 0);
} else {
 x_104 = x_34;
}
lean_ctor_set(x_104, 0, x_33);
lean_ctor_set(x_104, 1, x_103);
if (lean_is_scalar(x_26)) {
 x_105 = lean_alloc_ctor(1, 2, 0);
} else {
 x_105 = x_26;
}
lean_ctor_set(x_105, 0, x_54);
lean_ctor_set(x_105, 1, x_104);
x_106 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__5;
x_107 = l_Lean_Expr_const___override(x_106, x_105);
x_108 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__6;
x_109 = lean_array_push(x_108, x_41);
x_110 = lean_array_push(x_109, x_42);
x_111 = lean_array_push(x_110, x_53);
x_112 = lean_array_push(x_111, x_1);
x_113 = lean_array_push(x_112, x_101);
x_114 = lean_array_push(x_113, x_2);
x_115 = l_Lean_mkAppN(x_107, x_114);
lean_ctor_set(x_99, 0, x_115);
return x_99;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_116 = lean_ctor_get(x_99, 0);
x_117 = lean_ctor_get(x_99, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_99);
x_118 = lean_box(0);
if (lean_is_scalar(x_36)) {
 x_119 = lean_alloc_ctor(1, 2, 0);
} else {
 x_119 = x_36;
}
lean_ctor_set(x_119, 0, x_35);
lean_ctor_set(x_119, 1, x_118);
if (lean_is_scalar(x_34)) {
 x_120 = lean_alloc_ctor(1, 2, 0);
} else {
 x_120 = x_34;
}
lean_ctor_set(x_120, 0, x_33);
lean_ctor_set(x_120, 1, x_119);
if (lean_is_scalar(x_26)) {
 x_121 = lean_alloc_ctor(1, 2, 0);
} else {
 x_121 = x_26;
}
lean_ctor_set(x_121, 0, x_54);
lean_ctor_set(x_121, 1, x_120);
x_122 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__5;
x_123 = l_Lean_Expr_const___override(x_122, x_121);
x_124 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__6;
x_125 = lean_array_push(x_124, x_41);
x_126 = lean_array_push(x_125, x_42);
x_127 = lean_array_push(x_126, x_53);
x_128 = lean_array_push(x_127, x_1);
x_129 = lean_array_push(x_128, x_116);
x_130 = lean_array_push(x_129, x_2);
x_131 = l_Lean_mkAppN(x_123, x_130);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_117);
return x_132;
}
}
else
{
uint8_t x_133; 
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_26);
lean_dec(x_2);
lean_dec(x_1);
x_133 = !lean_is_exclusive(x_99);
if (x_133 == 0)
{
return x_99;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_99, 0);
x_135 = lean_ctor_get(x_99, 1);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_99);
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
return x_136;
}
}
}
}
else
{
uint8_t x_137; 
lean_dec(x_44);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_26);
lean_dec(x_20);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_137 = !lean_is_exclusive(x_50);
if (x_137 == 0)
{
return x_50;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_50, 0);
x_139 = lean_ctor_get(x_50, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_50);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
return x_140;
}
}
}
}
else
{
uint8_t x_145; 
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_26);
lean_dec(x_20);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_145 = !lean_is_exclusive(x_43);
if (x_145 == 0)
{
return x_43;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_43, 0);
x_147 = lean_ctor_get(x_43, 1);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_43);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
return x_148;
}
}
}
}
}
else
{
lean_object* x_157; lean_object* x_158; 
lean_dec(x_32);
lean_dec(x_29);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_20);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_157 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__4;
x_158 = l_panic___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___spec__1(x_157, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_158;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_3);
return x_15;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkFix___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("WellFoundedRelation", 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkFix___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_WF_mkFix___lambda__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkFix___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("WellFounded", 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkFix___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("fix", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkFix___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_WF_mkFix___lambda__1___closed__3;
x_2 = l_Lean_Elab_WF_mkFix___lambda__1___closed__4;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_76 = lean_array_get_size(x_2);
x_77 = lean_unsigned_to_nat(0u);
x_78 = lean_nat_dec_lt(x_77, x_76);
lean_dec(x_76);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
x_79 = l_Lean_instInhabitedExpr;
x_80 = l___private_Init_Util_0__outOfBounds___rarg(x_79);
x_11 = x_80;
goto block_75;
}
else
{
lean_object* x_81; 
x_81 = lean_array_fget(x_2, x_77);
x_11 = x_81;
goto block_75;
}
block_75:
{
lean_object* x_12; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_11);
x_12 = lean_infer_type(x_11, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_13);
x_15 = l_Lean_Meta_getLevel(x_13, x_6, x_7, x_8, x_9, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_3);
x_18 = l_Lean_Meta_getLevel(x_3, x_6, x_7, x_8, x_9, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lambda__1___closed__1;
lean_inc(x_11);
x_22 = lean_array_push(x_21, x_11);
x_23 = 0;
x_24 = 1;
x_25 = 1;
x_26 = l_Lean_Meta_mkLambdaFVars(x_22, x_3, x_23, x_24, x_25, x_6, x_7, x_8, x_9, x_20);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_Elab_WF_mkFix___lambda__1___closed__2;
x_30 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_31 = l_Lean_Expr_proj___override(x_29, x_30, x_1);
x_32 = lean_unsigned_to_nat(1u);
x_33 = l_Lean_Expr_proj___override(x_29, x_32, x_1);
x_34 = l_Lean_Expr_fvarId_x21(x_11);
x_35 = l_Lean_FVarId_getUserName(x_34, x_6, x_7, x_8, x_9, x_28);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_19);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_16);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lean_Elab_WF_mkFix___lambda__1___closed__5;
x_42 = l_Lean_Expr_const___override(x_41, x_40);
x_43 = l_Lean_mkApp4(x_42, x_13, x_27, x_31, x_33);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_37);
lean_ctor_set(x_35, 0, x_44);
return x_35;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_45 = lean_ctor_get(x_35, 0);
x_46 = lean_ctor_get(x_35, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_35);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_19);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_16);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Lean_Elab_WF_mkFix___lambda__1___closed__5;
x_51 = l_Lean_Expr_const___override(x_50, x_49);
x_52 = l_Lean_mkApp4(x_51, x_13, x_27, x_31, x_33);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_45);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_46);
return x_54;
}
}
else
{
uint8_t x_55; 
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_27);
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_13);
x_55 = !lean_is_exclusive(x_35);
if (x_55 == 0)
{
return x_35;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_35, 0);
x_57 = lean_ctor_get(x_35, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_35);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_26);
if (x_59 == 0)
{
return x_26;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_26, 0);
x_61 = lean_ctor_get(x_26, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_26);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_63 = !lean_is_exclusive(x_18);
if (x_63 == 0)
{
return x_18;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_18, 0);
x_65 = lean_ctor_get(x_18, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_18);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_15);
if (x_67 == 0)
{
return x_15;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_15, 0);
x_69 = lean_ctor_get(x_15, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_15);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_71 = !lean_is_exclusive(x_12);
if (x_71 == 0)
{
return x_12;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_12, 0);
x_73 = lean_ctor_get(x_12, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_12);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_1, 3);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_array_get_size(x_2);
x_16 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps), 12, 3);
lean_closure_set(x_16, 0, x_14);
lean_closure_set(x_16, 1, x_15);
lean_closure_set(x_16, 2, x_3);
x_17 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn(x_4, x_5, x_6, x_16, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_15 = lean_array_get_size(x_6);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_lt(x_16, x_15);
x_18 = lean_ctor_get(x_10, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_10, 2);
lean_inc(x_20);
x_21 = lean_ctor_get(x_10, 3);
lean_inc(x_21);
x_22 = lean_ctor_get(x_10, 4);
lean_inc(x_22);
x_23 = lean_ctor_get(x_10, 5);
lean_inc(x_23);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 lean_ctor_release(x_10, 2);
 lean_ctor_release(x_10, 3);
 lean_ctor_release(x_10, 4);
 lean_ctor_release(x_10, 5);
 x_24 = x_10;
} else {
 lean_dec_ref(x_10);
 x_24 = lean_box(0);
}
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_dec_lt(x_25, x_15);
lean_dec(x_15);
x_27 = lean_ctor_get(x_1, 5);
lean_inc(x_27);
lean_inc(x_2);
x_28 = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkFix___lambda__2___boxed), 13, 3);
lean_closure_set(x_28, 0, x_1);
lean_closure_set(x_28, 1, x_2);
lean_closure_set(x_28, 2, x_3);
if (x_17 == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = l_Lean_instInhabitedExpr;
x_84 = l___private_Init_Util_0__outOfBounds___rarg(x_83);
x_29 = x_84;
goto block_82;
}
else
{
lean_object* x_85; 
x_85 = lean_array_fget(x_6, x_16);
x_29 = x_85;
goto block_82;
}
block_82:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_inc(x_29);
x_30 = l_Lean_Expr_fvarId_x21(x_29);
x_31 = l_Lean_LocalContext_setUserName(x_19, x_30, x_4);
lean_inc(x_29);
lean_inc(x_2);
x_32 = lean_array_push(x_2, x_29);
x_33 = l_Lean_Expr_beta(x_27, x_32);
if (lean_is_scalar(x_24)) {
 x_34 = lean_alloc_ctor(0, 6, 0);
} else {
 x_34 = x_24;
}
lean_ctor_set(x_34, 0, x_18);
lean_ctor_set(x_34, 1, x_31);
lean_ctor_set(x_34, 2, x_20);
lean_ctor_set(x_34, 3, x_21);
lean_ctor_set(x_34, 4, x_22);
lean_ctor_set(x_34, 5, x_23);
if (x_26 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = l_Lean_instInhabitedExpr;
x_36 = l___private_Init_Util_0__outOfBounds___rarg(x_35);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_34);
lean_inc(x_36);
lean_inc(x_29);
x_37 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn(x_29, x_36, x_33, x_28, x_8, x_9, x_34, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; lean_object* x_46; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lambda__2___closed__1;
x_41 = lean_array_push(x_40, x_29);
x_42 = lean_array_push(x_41, x_36);
x_43 = 0;
x_44 = 1;
x_45 = 1;
x_46 = l_Lean_Meta_mkLambdaFVars(x_42, x_38, x_43, x_44, x_45, x_34, x_11, x_12, x_13, x_39);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = l_Lean_Expr_app___override(x_5, x_47);
x_50 = l_Lean_Meta_mkLambdaFVars(x_2, x_49, x_43, x_44, x_45, x_34, x_11, x_12, x_13, x_48);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_34);
return x_50;
}
else
{
uint8_t x_51; 
lean_dec(x_34);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_2);
x_51 = !lean_is_exclusive(x_46);
if (x_51 == 0)
{
return x_46;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_46, 0);
x_53 = lean_ctor_get(x_46, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_46);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_36);
lean_dec(x_34);
lean_dec(x_29);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_2);
x_55 = !lean_is_exclusive(x_37);
if (x_55 == 0)
{
return x_37;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_37, 0);
x_57 = lean_ctor_get(x_37, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_37);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_array_fget(x_6, x_25);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_34);
lean_inc(x_59);
lean_inc(x_29);
x_60 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn(x_29, x_59, x_33, x_28, x_8, x_9, x_34, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; lean_object* x_69; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lambda__2___closed__1;
x_64 = lean_array_push(x_63, x_29);
x_65 = lean_array_push(x_64, x_59);
x_66 = 0;
x_67 = 1;
x_68 = 1;
x_69 = l_Lean_Meta_mkLambdaFVars(x_65, x_61, x_66, x_67, x_68, x_34, x_11, x_12, x_13, x_62);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = l_Lean_Expr_app___override(x_5, x_70);
x_73 = l_Lean_Meta_mkLambdaFVars(x_2, x_72, x_66, x_67, x_68, x_34, x_11, x_12, x_13, x_71);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_34);
return x_73;
}
else
{
uint8_t x_74; 
lean_dec(x_34);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_2);
x_74 = !lean_is_exclusive(x_69);
if (x_74 == 0)
{
return x_69;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_69, 0);
x_76 = lean_ctor_get(x_69, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_69);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_59);
lean_dec(x_34);
lean_dec(x_29);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_2);
x_78 = !lean_is_exclusive(x_60);
if (x_78 == 0)
{
return x_60;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_60, 0);
x_80 = lean_ctor_get(x_60, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_60);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_WF_mkFix___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkFix___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_1, 4);
lean_inc(x_12);
x_13 = lean_unsigned_to_nat(0u);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_14 = l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateForallAux(x_2, x_13, x_12, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkFix___lambda__1___boxed), 10, 1);
lean_closure_set(x_17, 0, x_3);
x_18 = l_Lean_Elab_WF_mkFix___closed__1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_19 = l_Lean_Meta_forallBoundedTelescope___at_Lean_Elab_Term_addAutoBoundImplicits_x27___spec__1___rarg(x_15, x_18, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_16);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_22);
x_24 = lean_infer_type(x_22, x_7, x_8, x_9, x_10, x_21);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_27 = lean_whnf(x_25, x_7, x_8, x_9, x_10, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Expr_bindingDomain_x21(x_28);
lean_dec(x_28);
x_31 = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkFix___lambda__3___boxed), 14, 5);
lean_closure_set(x_31, 0, x_1);
lean_closure_set(x_31, 1, x_2);
lean_closure_set(x_31, 2, x_4);
lean_closure_set(x_31, 3, x_23);
lean_closure_set(x_31, 4, x_22);
x_32 = l_Lean_Elab_WF_mkFix___closed__2;
x_33 = l_Lean_Meta_forallBoundedTelescope___at_Lean_Elab_Term_addAutoBoundImplicits_x27___spec__1___rarg(x_30, x_32, x_31, x_5, x_6, x_7, x_8, x_9, x_10, x_29);
return x_33;
}
else
{
uint8_t x_34; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_27);
if (x_34 == 0)
{
return x_27;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_27, 0);
x_36 = lean_ctor_get(x_27, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_27);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_24);
if (x_38 == 0)
{
return x_24;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_24, 0);
x_40 = lean_ctor_get(x_24, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_24);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_19);
if (x_42 == 0)
{
return x_19;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_19, 0);
x_44 = lean_ctor_get(x_19, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_19);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_14);
if (x_46 == 0)
{
return x_14;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_14, 0);
x_48 = lean_ctor_get(x_14, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_14);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_WF_mkFix___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Elab_WF_mkFix___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Elab_WF_mkFix___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_7);
lean_dec(x_6);
return x_15;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_HasConstCache(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_CasesOn(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Match_Match(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_Main(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Cleanup(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_RecAppSyntax(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_Structural_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_Structural_BRecOn(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_PreDefinition_WF_Fix(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_HasConstCache(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_CasesOn(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_Match(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Main(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Cleanup(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_RecAppSyntax(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_Structural_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_Structural_BRecOn(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lambda__1___closed__1 = _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lambda__1___closed__1);
l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lambda__1___closed__2 = _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lambda__1___closed__2);
l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lambda__1___closed__3 = _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lambda__1___closed__3();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lambda__1___closed__3);
l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___closed__1 = _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___closed__1);
l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1 = _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__5___lambda__2___closed__1 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__5___lambda__2___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__5___lambda__2___closed__1);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__5___lambda__2___closed__2 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__5___lambda__2___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__5___lambda__2___closed__2);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__5___lambda__2___closed__3 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__5___lambda__2___closed__3();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__5___lambda__2___closed__3);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__5___lambda__2___closed__4 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__5___lambda__2___closed__4();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__5___lambda__2___closed__4);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__5___lambda__2___closed__5 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__5___lambda__2___closed__5();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__5___lambda__2___closed__5);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__5___lambda__2___closed__6 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__5___lambda__2___closed__6();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__5___lambda__2___closed__6);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__9___lambda__2___closed__1 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__9___lambda__2___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__9___lambda__2___closed__1);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__9___lambda__2___closed__2 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__9___lambda__2___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__9___lambda__2___closed__2);
l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lambda__1___closed__1 = _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lambda__1___closed__1);
l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___lambda__1___closed__1 = _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___lambda__1___closed__1);
l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___lambda__2___closed__1 = _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___lambda__2___closed__1);
l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___lambda__2___closed__2 = _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___lambda__2___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___lambda__2___closed__2);
l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__1 = _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__1);
l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__2 = _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__2);
l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__3 = _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__3();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__3);
l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__4 = _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__4();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__4);
l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__5 = _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__5();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__5);
l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__6 = _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__6();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__6);
l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lambda__2___closed__1 = _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lambda__2___closed__1);
l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lambda__3___closed__1 = _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lambda__3___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lambda__3___closed__1);
l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__1 = _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__1);
l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__2 = _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__2);
l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__3 = _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__3();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__3);
l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__4 = _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__4();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__4);
l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__5 = _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__5();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__5);
l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__6 = _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__6();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__6);
l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__7 = _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__7();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__7);
l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__8 = _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__8();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__8);
l_panic___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___spec__1___closed__1 = _init_l_panic___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___spec__1___closed__1();
lean_mark_persistent(l_panic___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___spec__1___closed__1);
l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lambda__2___closed__1 = _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lambda__2___closed__1);
l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lambda__2___closed__2 = _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lambda__2___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lambda__2___closed__2);
l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lambda__2___closed__3 = _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lambda__2___closed__3();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lambda__2___closed__3);
l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lambda__2___closed__4 = _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lambda__2___closed__4();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lambda__2___closed__4);
l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__1 = _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__1);
l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__2 = _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__2);
l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__3 = _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__3();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__3);
l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__4 = _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__4();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__4);
l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__5 = _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__5();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__5);
l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__6 = _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__6();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__6);
l_Lean_Elab_WF_mkFix___lambda__1___closed__1 = _init_l_Lean_Elab_WF_mkFix___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_WF_mkFix___lambda__1___closed__1);
l_Lean_Elab_WF_mkFix___lambda__1___closed__2 = _init_l_Lean_Elab_WF_mkFix___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_WF_mkFix___lambda__1___closed__2);
l_Lean_Elab_WF_mkFix___lambda__1___closed__3 = _init_l_Lean_Elab_WF_mkFix___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_WF_mkFix___lambda__1___closed__3);
l_Lean_Elab_WF_mkFix___lambda__1___closed__4 = _init_l_Lean_Elab_WF_mkFix___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Elab_WF_mkFix___lambda__1___closed__4);
l_Lean_Elab_WF_mkFix___lambda__1___closed__5 = _init_l_Lean_Elab_WF_mkFix___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Elab_WF_mkFix___lambda__1___closed__5);
l_Lean_Elab_WF_mkFix___closed__1 = _init_l_Lean_Elab_WF_mkFix___closed__1();
lean_mark_persistent(l_Lean_Elab_WF_mkFix___closed__1);
l_Lean_Elab_WF_mkFix___closed__2 = _init_l_Lean_Elab_WF_mkFix___closed__2();
lean_mark_persistent(l_Lean_Elab_WF_mkFix___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
