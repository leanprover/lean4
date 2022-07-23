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
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__11___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__13___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__7___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__8;
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_tryCoe___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_HasConstCache_containsUnsafe(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Elab_WF_mkFix___lambda__1___closed__1;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lambda__2___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__2(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__5;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lambda__1___closed__2;
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__3___boxed(lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__7___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__5;
lean_object* l_Lean_SourceInfo_fromRef(lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__4;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__5___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4;
lean_object* l_Array_extract___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_CasesOnApp_addArg_x3f(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getRecAppSyntax_x3f(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__3;
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
uint8_t l_Lean_Elab_Structural_recArgHasLooseBVarsAt(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__9___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_mkFix___lambda__1___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__11___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__7;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__5___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Elab_Term_withAuxDecl___spec__3___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__8(lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__5___lambda__2___closed__5;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_mkFix___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__5___lambda__2___closed__3;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instInhabitedTermElabM(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__12___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_mkDecreasingProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lambda__1___closed__1;
lean_object* l_Lean_Meta_mkAppOptM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__7___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__5;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___lambda__1___closed__1;
extern lean_object* l_Lean_levelZero;
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_mkDecreasingProof___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__5___lambda__2___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_zip___rarg(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__5___lambda__2___closed__4;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__9___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_cleanup(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__6;
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_mkDecreasingProof___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lambda__3___closed__1;
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__9;
lean_object* l_Lean_Expr_replaceFVar(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__8;
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__4___boxed(lean_object*, lean_object*);
lean_object* l_Std_mkHashMapImp___rarg(lean_object*);
static lean_object* l_Lean_Elab_WF_mkFix___closed__1;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__4;
lean_object* l_panic___at_Lean_Expr_getRevArg_x21___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__4___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_mkFix___lambda__1___closed__4;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__1;
lean_object* l_Lean_Meta_CasesOnApp_toExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__7;
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__5___lambda__2___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__8;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__4;
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__9___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__13___boxed(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__13(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_MatcherApp_addArg_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__9___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__9___lambda__2___closed__1;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isLambda(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_runTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__7(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_Meta_etaExpand(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__3(lean_object*);
static lean_object* l_Lean_Elab_WF_mkFix___lambda__1___closed__3;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__6;
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__9___lambda__2___closed__2;
lean_object* l_List_redLength___rarg(lean_object*);
lean_object* l_Lean_Elab_pushInfoTree___at_Lean_Elab_Term_addDotCompletionInfo___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallBoundedTelescope___at_Lean_Elab_Term_addAutoBoundImplicits_x27___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lambda__2___closed__2;
static lean_object* l_Lean_Elab_WF_mkFix___closed__2;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Expr_beta(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_containsRecFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__11___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateForallAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_containsRecFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_MatcherApp_toExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_mkFix___lambda__1___closed__5;
lean_object* l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ofSubarray___rarg(lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__12(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_List_toArrayAux___rarg(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Meta_toCasesOnApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__8___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_arity(lean_object*);
lean_object* l_Lean_Elab_Term_reportUnsolvedGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__12___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_ensureNoRecFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__12___boxed(lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_setUserName(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_tryCoe___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__5___lambda__2___closed__6;
lean_object* l_Lean_Meta_Match_MatcherInfo_numAlts(lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__11___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lambda__1___closed__3;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__5___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__2;
lean_object* l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__5;
lean_object* l_Lean_Elab_Structural_refinedArgType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__8___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 5);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Lean_SourceInfo_fromRef(x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_closure((void*)(l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___spec__1___rarg___boxed), 3, 0);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_inc(x_3);
lean_inc(x_2);
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
lean_dec(x_3);
lean_dec(x_2);
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
lean_inc(x_3);
lean_inc(x_2);
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
lean_dec(x_3);
lean_dec(x_2);
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
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_inc(x_7);
x_10 = l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___spec__1___rarg(x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_get(x_8, x_12);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lambda__1___closed__3;
x_16 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_15);
x_17 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lambda__1___closed__4;
x_18 = lean_array_push(x_17, x_16);
x_19 = lean_box(2);
x_20 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lambda__1___closed__2;
x_21 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_21, 2, x_18);
x_22 = l_Lean_Elab_Tactic_evalTactic(x_21, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_14);
return x_22;
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
x_13 = l_List_forM___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___spec__2(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
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
LEAN_EXPORT lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___spec__1___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
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
x_14 = l_Lean_Expr_mvarId_x21(x_12);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_15 = l_Lean_Meta_cleanup(x_14, x_5, x_6, x_7, x_8, x_13);
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_11 = lean_st_ref_get(x_9, x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_st_ref_take(x_3, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_HasConstCache_containsUnsafe(x_1, x_2, x_14);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_st_ref_set(x_3, x_18, x_15);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_17);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_22);
return x_23;
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
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Init.Util", 9);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("getElem!", 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("index out of bounds", 19);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__2;
x_2 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__3;
x_3 = lean_unsigned_to_nat(70u);
x_4 = lean_unsigned_to_nat(36u);
x_5 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
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
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_74; uint8_t x_75; 
x_19 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1;
lean_inc(x_15);
x_20 = lean_mk_array(x_15, x_19);
x_21 = lean_nat_sub(x_15, x_16);
lean_dec(x_15);
x_22 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_5, x_20, x_21);
x_74 = lean_array_get_size(x_22);
x_75 = lean_nat_dec_lt(x_2, x_74);
lean_dec(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__5;
x_77 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_76);
x_23 = x_77;
goto block_73;
}
else
{
lean_object* x_78; 
x_78 = lean_array_fget(x_22, x_2);
x_23 = x_78;
goto block_73;
}
block_73:
{
lean_object* x_24; 
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
x_24 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(x_1, x_2, x_3, x_4, x_23, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_4);
x_27 = l_Lean_Expr_app___override(x_4, x_25);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_27);
x_28 = lean_infer_type(x_27, x_9, x_10, x_11, x_12, x_26);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_31 = lean_whnf(x_29, x_9, x_10, x_11, x_12, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_Expr_bindingDomain_x21(x_32);
lean_dec(x_32);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_3);
x_35 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_mkDecreasingProof(x_34, x_3, x_7, x_8, x_9, x_10, x_11, x_12, x_33);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; size_t x_43; size_t x_44; lean_object* x_45; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_Expr_app___override(x_27, x_36);
x_39 = lean_array_get_size(x_22);
x_40 = l_Array_toSubarray___rarg(x_22, x_17, x_39);
x_41 = l_Array_ofSubarray___rarg(x_40);
x_42 = lean_array_get_size(x_41);
x_43 = lean_usize_of_nat(x_42);
lean_dec(x_42);
x_44 = 0;
x_45 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___spec__1(x_1, x_2, x_3, x_4, x_43, x_44, x_41, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_37);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_45, 0);
x_48 = l_Lean_mkAppN(x_38, x_47);
lean_ctor_set(x_45, 0, x_48);
return x_45;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_45, 0);
x_50 = lean_ctor_get(x_45, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_45);
x_51 = l_Lean_mkAppN(x_38, x_49);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
else
{
uint8_t x_53; 
lean_dec(x_38);
x_53 = !lean_is_exclusive(x_45);
if (x_53 == 0)
{
return x_45;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_45, 0);
x_55 = lean_ctor_get(x_45, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_45);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_27);
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
x_57 = !lean_is_exclusive(x_35);
if (x_57 == 0)
{
return x_35;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_35, 0);
x_59 = lean_ctor_get(x_35, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_35);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_27);
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
x_61 = !lean_is_exclusive(x_31);
if (x_61 == 0)
{
return x_31;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_31, 0);
x_63 = lean_ctor_get(x_31, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_31);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_27);
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
x_65 = !lean_is_exclusive(x_28);
if (x_65 == 0)
{
return x_28;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_28, 0);
x_67 = lean_ctor_get(x_28, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_28);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
uint8_t x_69; 
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
x_69 = !lean_is_exclusive(x_24);
if (x_69 == 0)
{
return x_24;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_24, 0);
x_71 = lean_ctor_get(x_24, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_24);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
}
else
{
lean_object* x_79; 
lean_dec(x_17);
lean_dec(x_15);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_79 = l_Lean_Meta_etaExpand(x_5, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(x_1, x_2, x_3, x_4, x_80, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_81);
return x_82;
}
else
{
uint8_t x_83; 
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
x_83 = !lean_is_exclusive(x_79);
if (x_83 == 0)
{
return x_79;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_79, 0);
x_85 = lean_ctor_get(x_79, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_79);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
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
x_55 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__5;
x_56 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_55);
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
x_91 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__5;
x_92 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_91);
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
x_131 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__5;
x_132 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_131);
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
x_18 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__5;
x_19 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_18);
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
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__5___lambda__2___closed__4;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_indentExpr(x_6);
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__5___lambda__2___closed__6;
x_27 = lean_alloc_ctor(10, 2, 0);
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
x_20 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__5;
x_21 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_20);
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
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__5___lambda__2___closed__4;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_indentExpr(x_6);
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__5___lambda__2___closed__6;
x_27 = lean_alloc_ctor(10, 2, 0);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__11___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__11___rarg___lambda__1), 10, 4);
lean_closure_set(x_13, 0, x_4);
lean_closure_set(x_13, 1, x_5);
lean_closure_set(x_13, 2, x_6);
lean_closure_set(x_13, 3, x_7);
x_14 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp___rarg(x_1, x_2, x_3, x_13, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
return x_14;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_14);
if (x_19 == 0)
{
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_14, 0);
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_14);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__11(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__11___rarg___boxed), 12, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__12___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__11___rarg___lambda__1), 10, 4);
lean_closure_set(x_13, 0, x_4);
lean_closure_set(x_13, 1, x_5);
lean_closure_set(x_13, 2, x_6);
lean_closure_set(x_13, 3, x_7);
x_14 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp___rarg(x_1, x_2, x_3, x_13, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
return x_14;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_14);
if (x_19 == 0)
{
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_14, 0);
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_14);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__12(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__12___rarg___boxed), 12, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__13___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__11___rarg___lambda__1), 10, 4);
lean_closure_set(x_13, 0, x_4);
lean_closure_set(x_13, 1, x_5);
lean_closure_set(x_13, 2, x_6);
lean_closure_set(x_13, 3, x_7);
x_14 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp___rarg(x_1, x_2, x_3, x_13, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
return x_14;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_14);
if (x_19 == 0)
{
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_14, 0);
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_14);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__13(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__13___rarg), 12, 0);
return x_3;
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
x_19 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lambda__1___closed__4;
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
x_19 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lambda__1___closed__4;
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
x_19 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lambda__1___closed__4;
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
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
x_26 = lean_ctor_get(x_22, 0);
lean_inc(x_26);
lean_dec(x_22);
lean_inc(x_1);
lean_inc(x_3);
lean_inc(x_2);
x_27 = l_Lean_Elab_Structural_recArgHasLooseBVarsAt(x_2, x_3, x_1);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_26);
x_28 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp(x_2, x_3, x_4, x_5, x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_25);
return x_28;
}
else
{
uint8_t x_29; lean_object* x_30; lean_object* x_31; 
x_29 = 1;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_5);
x_30 = l_Lean_Meta_CasesOnApp_addArg_x3f(x_26, x_5, x_29, x_10, x_11, x_12, x_13, x_25);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp(x_2, x_3, x_4, x_5, x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_32);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; size_t x_40; size_t x_41; lean_object* x_42; 
x_34 = lean_ctor_get(x_30, 1);
lean_inc(x_34);
lean_dec(x_30);
x_35 = lean_ctor_get(x_31, 0);
lean_inc(x_35);
lean_dec(x_31);
x_36 = lean_ctor_get(x_35, 6);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 7);
lean_inc(x_37);
x_38 = l_Array_zip___rarg(x_36, x_37);
lean_dec(x_36);
x_39 = lean_array_get_size(x_38);
x_40 = lean_usize_of_nat(x_39);
lean_dec(x_39);
x_41 = 0;
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
x_42 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__5(x_2, x_3, x_4, x_1, x_40, x_41, x_38, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_34);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; size_t x_47; lean_object* x_48; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_ctor_get(x_35, 8);
lean_inc(x_45);
x_46 = lean_array_get_size(x_45);
x_47 = lean_usize_of_nat(x_46);
lean_dec(x_46);
x_48 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__6(x_2, x_3, x_4, x_5, x_47, x_41, x_45, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_44);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; 
x_50 = lean_ctor_get(x_48, 0);
x_51 = lean_ctor_get(x_35, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_35, 1);
lean_inc(x_52);
x_53 = lean_ctor_get(x_35, 2);
lean_inc(x_53);
x_54 = lean_ctor_get(x_35, 3);
lean_inc(x_54);
x_55 = lean_ctor_get(x_35, 4);
lean_inc(x_55);
x_56 = lean_ctor_get(x_35, 5);
lean_inc(x_56);
x_57 = lean_ctor_get_uint8(x_35, sizeof(void*)*9);
lean_dec(x_35);
x_58 = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(x_58, 0, x_51);
lean_ctor_set(x_58, 1, x_52);
lean_ctor_set(x_58, 2, x_53);
lean_ctor_set(x_58, 3, x_54);
lean_ctor_set(x_58, 4, x_55);
lean_ctor_set(x_58, 5, x_56);
lean_ctor_set(x_58, 6, x_43);
lean_ctor_set(x_58, 7, x_37);
lean_ctor_set(x_58, 8, x_50);
lean_ctor_set_uint8(x_58, sizeof(void*)*9, x_57);
x_59 = l_Lean_Meta_CasesOnApp_toExpr(x_58);
lean_ctor_set(x_48, 0, x_59);
return x_48;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_60 = lean_ctor_get(x_48, 0);
x_61 = lean_ctor_get(x_48, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_48);
x_62 = lean_ctor_get(x_35, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_35, 1);
lean_inc(x_63);
x_64 = lean_ctor_get(x_35, 2);
lean_inc(x_64);
x_65 = lean_ctor_get(x_35, 3);
lean_inc(x_65);
x_66 = lean_ctor_get(x_35, 4);
lean_inc(x_66);
x_67 = lean_ctor_get(x_35, 5);
lean_inc(x_67);
x_68 = lean_ctor_get_uint8(x_35, sizeof(void*)*9);
lean_dec(x_35);
x_69 = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(x_69, 0, x_62);
lean_ctor_set(x_69, 1, x_63);
lean_ctor_set(x_69, 2, x_64);
lean_ctor_set(x_69, 3, x_65);
lean_ctor_set(x_69, 4, x_66);
lean_ctor_set(x_69, 5, x_67);
lean_ctor_set(x_69, 6, x_43);
lean_ctor_set(x_69, 7, x_37);
lean_ctor_set(x_69, 8, x_60);
lean_ctor_set_uint8(x_69, sizeof(void*)*9, x_68);
x_70 = l_Lean_Meta_CasesOnApp_toExpr(x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_61);
return x_71;
}
}
else
{
uint8_t x_72; 
lean_dec(x_43);
lean_dec(x_37);
lean_dec(x_35);
x_72 = !lean_is_exclusive(x_48);
if (x_72 == 0)
{
return x_48;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_48, 0);
x_74 = lean_ctor_get(x_48, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_48);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_37);
lean_dec(x_35);
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
x_76 = !lean_is_exclusive(x_42);
if (x_76 == 0)
{
return x_42;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_42, 0);
x_78 = lean_ctor_get(x_42, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_42);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
}
}
}
else
{
uint8_t x_80; 
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
x_80 = !lean_is_exclusive(x_21);
if (x_80 == 0)
{
return x_21;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_21, 0);
x_82 = lean_ctor_get(x_21, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_21);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
else
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_84 = lean_ctor_get(x_18, 1);
lean_inc(x_84);
lean_dec(x_18);
x_85 = lean_ctor_get(x_19, 0);
lean_inc(x_85);
lean_dec(x_19);
lean_inc(x_1);
lean_inc(x_3);
lean_inc(x_2);
x_86 = l_Lean_Elab_Structural_recArgHasLooseBVarsAt(x_2, x_3, x_1);
if (x_86 == 0)
{
lean_object* x_87; 
lean_dec(x_85);
x_87 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp(x_2, x_3, x_4, x_5, x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_84);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_5);
x_88 = l_Lean_Meta_MatcherApp_addArg_x3f(x_85, x_5, x_10, x_11, x_12, x_13, x_84);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_91 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp(x_2, x_3, x_4, x_5, x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_90);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_88, 1);
lean_inc(x_92);
lean_dec(x_88);
x_93 = lean_ctor_get(x_89, 0);
lean_inc(x_93);
lean_dec(x_89);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_5);
lean_inc(x_93);
x_94 = l_Lean_Elab_Structural_refinedArgType(x_93, x_5, x_10, x_11, x_12, x_13, x_92);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; uint8_t x_96; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_unbox(x_95);
lean_dec(x_95);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; 
lean_dec(x_93);
x_97 = lean_ctor_get(x_94, 1);
lean_inc(x_97);
lean_dec(x_94);
x_98 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp(x_2, x_3, x_4, x_5, x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_97);
return x_98;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; size_t x_104; size_t x_105; lean_object* x_106; 
x_99 = lean_ctor_get(x_94, 1);
lean_inc(x_99);
lean_dec(x_94);
x_100 = lean_ctor_get(x_93, 7);
lean_inc(x_100);
x_101 = lean_ctor_get(x_93, 6);
lean_inc(x_101);
x_102 = l_Array_zip___rarg(x_100, x_101);
lean_dec(x_100);
x_103 = lean_array_get_size(x_102);
x_104 = lean_usize_of_nat(x_103);
lean_dec(x_103);
x_105 = 0;
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
x_106 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__9(x_2, x_3, x_4, x_1, x_104, x_105, x_102, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_99);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; size_t x_111; lean_object* x_112; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
x_109 = lean_ctor_get(x_93, 5);
lean_inc(x_109);
x_110 = lean_array_get_size(x_109);
x_111 = lean_usize_of_nat(x_110);
lean_dec(x_110);
x_112 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__10(x_2, x_3, x_4, x_5, x_111, x_105, x_109, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_108);
if (lean_obj_tag(x_112) == 0)
{
uint8_t x_113; 
x_113 = !lean_is_exclusive(x_112);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_114 = lean_ctor_get(x_112, 0);
x_115 = lean_ctor_get(x_93, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_93, 1);
lean_inc(x_116);
x_117 = lean_ctor_get(x_93, 2);
lean_inc(x_117);
x_118 = lean_ctor_get(x_93, 3);
lean_inc(x_118);
x_119 = lean_ctor_get(x_93, 4);
lean_inc(x_119);
x_120 = lean_ctor_get(x_93, 8);
lean_inc(x_120);
lean_dec(x_93);
x_121 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_121, 0, x_115);
lean_ctor_set(x_121, 1, x_116);
lean_ctor_set(x_121, 2, x_117);
lean_ctor_set(x_121, 3, x_118);
lean_ctor_set(x_121, 4, x_119);
lean_ctor_set(x_121, 5, x_114);
lean_ctor_set(x_121, 6, x_101);
lean_ctor_set(x_121, 7, x_107);
lean_ctor_set(x_121, 8, x_120);
x_122 = l_Lean_Meta_MatcherApp_toExpr(x_121);
lean_ctor_set(x_112, 0, x_122);
return x_112;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_123 = lean_ctor_get(x_112, 0);
x_124 = lean_ctor_get(x_112, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_112);
x_125 = lean_ctor_get(x_93, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_93, 1);
lean_inc(x_126);
x_127 = lean_ctor_get(x_93, 2);
lean_inc(x_127);
x_128 = lean_ctor_get(x_93, 3);
lean_inc(x_128);
x_129 = lean_ctor_get(x_93, 4);
lean_inc(x_129);
x_130 = lean_ctor_get(x_93, 8);
lean_inc(x_130);
lean_dec(x_93);
x_131 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_131, 0, x_125);
lean_ctor_set(x_131, 1, x_126);
lean_ctor_set(x_131, 2, x_127);
lean_ctor_set(x_131, 3, x_128);
lean_ctor_set(x_131, 4, x_129);
lean_ctor_set(x_131, 5, x_123);
lean_ctor_set(x_131, 6, x_101);
lean_ctor_set(x_131, 7, x_107);
lean_ctor_set(x_131, 8, x_130);
x_132 = l_Lean_Meta_MatcherApp_toExpr(x_131);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_124);
return x_133;
}
}
else
{
uint8_t x_134; 
lean_dec(x_107);
lean_dec(x_101);
lean_dec(x_93);
x_134 = !lean_is_exclusive(x_112);
if (x_134 == 0)
{
return x_112;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_112, 0);
x_136 = lean_ctor_get(x_112, 1);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_112);
x_137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
return x_137;
}
}
}
else
{
uint8_t x_138; 
lean_dec(x_101);
lean_dec(x_93);
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
x_138 = !lean_is_exclusive(x_106);
if (x_138 == 0)
{
return x_106;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_106, 0);
x_140 = lean_ctor_get(x_106, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_106);
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
return x_141;
}
}
}
}
else
{
uint8_t x_142; 
lean_dec(x_93);
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
x_142 = !lean_is_exclusive(x_94);
if (x_142 == 0)
{
return x_94;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_94, 0);
x_144 = lean_ctor_get(x_94, 1);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_94);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
return x_145;
}
}
}
}
}
}
case 6:
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; lean_object* x_150; 
x_146 = lean_ctor_get(x_1, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_1, 1);
lean_inc(x_147);
x_148 = lean_ctor_get(x_1, 2);
lean_inc(x_148);
x_149 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
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
x_150 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(x_2, x_3, x_4, x_5, x_147, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
lean_dec(x_150);
x_153 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lambda__1___boxed), 14, 5);
lean_closure_set(x_153, 0, x_148);
lean_closure_set(x_153, 1, x_2);
lean_closure_set(x_153, 2, x_3);
lean_closure_set(x_153, 3, x_4);
lean_closure_set(x_153, 4, x_5);
x_154 = l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__11___rarg(x_146, x_149, x_151, x_153, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_152);
return x_154;
}
else
{
uint8_t x_155; 
lean_dec(x_148);
lean_dec(x_146);
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
x_155 = !lean_is_exclusive(x_150);
if (x_155 == 0)
{
return x_150;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = lean_ctor_get(x_150, 0);
x_157 = lean_ctor_get(x_150, 1);
lean_inc(x_157);
lean_inc(x_156);
lean_dec(x_150);
x_158 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_158, 0, x_156);
lean_ctor_set(x_158, 1, x_157);
return x_158;
}
}
}
case 7:
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; lean_object* x_163; 
x_159 = lean_ctor_get(x_1, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_1, 1);
lean_inc(x_160);
x_161 = lean_ctor_get(x_1, 2);
lean_inc(x_161);
x_162 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
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
x_163 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(x_2, x_3, x_4, x_5, x_160, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec(x_163);
x_166 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lambda__2___boxed), 14, 5);
lean_closure_set(x_166, 0, x_161);
lean_closure_set(x_166, 1, x_2);
lean_closure_set(x_166, 2, x_3);
lean_closure_set(x_166, 3, x_4);
lean_closure_set(x_166, 4, x_5);
x_167 = l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__12___rarg(x_159, x_162, x_164, x_166, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_165);
return x_167;
}
else
{
uint8_t x_168; 
lean_dec(x_161);
lean_dec(x_159);
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
x_168 = !lean_is_exclusive(x_163);
if (x_168 == 0)
{
return x_163;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_ctor_get(x_163, 0);
x_170 = lean_ctor_get(x_163, 1);
lean_inc(x_170);
lean_inc(x_169);
lean_dec(x_163);
x_171 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_171, 0, x_169);
lean_ctor_set(x_171, 1, x_170);
return x_171;
}
}
}
case 8:
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_172 = lean_ctor_get(x_1, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_1, 1);
lean_inc(x_173);
x_174 = lean_ctor_get(x_1, 2);
lean_inc(x_174);
x_175 = lean_ctor_get(x_1, 3);
lean_inc(x_175);
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
x_176 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(x_2, x_3, x_4, x_5, x_173, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_176, 1);
lean_inc(x_178);
lean_dec(x_176);
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
x_179 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(x_2, x_3, x_4, x_5, x_174, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_178);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
lean_dec(x_179);
x_182 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lambda__3___boxed), 14, 5);
lean_closure_set(x_182, 0, x_175);
lean_closure_set(x_182, 1, x_2);
lean_closure_set(x_182, 2, x_3);
lean_closure_set(x_182, 3, x_4);
lean_closure_set(x_182, 4, x_5);
x_183 = l_Lean_Meta_withLetDecl___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__13___rarg(x_172, x_177, x_180, x_182, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_181);
return x_183;
}
else
{
uint8_t x_184; 
lean_dec(x_177);
lean_dec(x_175);
lean_dec(x_172);
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
x_184 = !lean_is_exclusive(x_179);
if (x_184 == 0)
{
return x_179;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_185 = lean_ctor_get(x_179, 0);
x_186 = lean_ctor_get(x_179, 1);
lean_inc(x_186);
lean_inc(x_185);
lean_dec(x_179);
x_187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_187, 0, x_185);
lean_ctor_set(x_187, 1, x_186);
return x_187;
}
}
}
else
{
uint8_t x_188; 
lean_dec(x_175);
lean_dec(x_174);
lean_dec(x_172);
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
x_188 = !lean_is_exclusive(x_176);
if (x_188 == 0)
{
return x_176;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_189 = lean_ctor_get(x_176, 0);
x_190 = lean_ctor_get(x_176, 1);
lean_inc(x_190);
lean_inc(x_189);
lean_dec(x_176);
x_191 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_191, 0, x_189);
lean_ctor_set(x_191, 1, x_190);
return x_191;
}
}
}
case 10:
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_192 = lean_ctor_get(x_1, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_1, 1);
lean_inc(x_193);
x_194 = l_Lean_getRecAppSyntax_x3f(x_1);
lean_dec(x_1);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; 
x_195 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(x_2, x_3, x_4, x_5, x_193, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_195) == 0)
{
uint8_t x_196; 
x_196 = !lean_is_exclusive(x_195);
if (x_196 == 0)
{
lean_object* x_197; lean_object* x_198; 
x_197 = lean_ctor_get(x_195, 0);
x_198 = l_Lean_Expr_mdata___override(x_192, x_197);
lean_ctor_set(x_195, 0, x_198);
return x_195;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_199 = lean_ctor_get(x_195, 0);
x_200 = lean_ctor_get(x_195, 1);
lean_inc(x_200);
lean_inc(x_199);
lean_dec(x_195);
x_201 = l_Lean_Expr_mdata___override(x_192, x_199);
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_201);
lean_ctor_set(x_202, 1, x_200);
return x_202;
}
}
else
{
uint8_t x_203; 
lean_dec(x_192);
x_203 = !lean_is_exclusive(x_195);
if (x_203 == 0)
{
return x_195;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_204 = lean_ctor_get(x_195, 0);
x_205 = lean_ctor_get(x_195, 1);
lean_inc(x_205);
lean_inc(x_204);
lean_dec(x_195);
x_206 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_206, 0, x_204);
lean_ctor_set(x_206, 1, x_205);
return x_206;
}
}
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
lean_dec(x_192);
x_207 = lean_ctor_get(x_194, 0);
lean_inc(x_207);
lean_dec(x_194);
x_208 = lean_ctor_get(x_12, 5);
lean_inc(x_208);
x_209 = l_Lean_replaceRef(x_207, x_208);
lean_dec(x_208);
lean_dec(x_207);
x_210 = lean_ctor_get(x_12, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_12, 1);
lean_inc(x_211);
x_212 = lean_ctor_get(x_12, 2);
lean_inc(x_212);
x_213 = lean_ctor_get(x_12, 3);
lean_inc(x_213);
x_214 = lean_ctor_get(x_12, 4);
lean_inc(x_214);
x_215 = lean_ctor_get(x_12, 6);
lean_inc(x_215);
x_216 = lean_ctor_get(x_12, 7);
lean_inc(x_216);
x_217 = lean_ctor_get(x_12, 8);
lean_inc(x_217);
x_218 = lean_ctor_get(x_12, 9);
lean_inc(x_218);
x_219 = lean_ctor_get(x_12, 10);
lean_inc(x_219);
lean_dec(x_12);
x_220 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_220, 0, x_210);
lean_ctor_set(x_220, 1, x_211);
lean_ctor_set(x_220, 2, x_212);
lean_ctor_set(x_220, 3, x_213);
lean_ctor_set(x_220, 4, x_214);
lean_ctor_set(x_220, 5, x_209);
lean_ctor_set(x_220, 6, x_215);
lean_ctor_set(x_220, 7, x_216);
lean_ctor_set(x_220, 8, x_217);
lean_ctor_set(x_220, 9, x_218);
lean_ctor_set(x_220, 10, x_219);
x_221 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(x_2, x_3, x_4, x_5, x_193, x_7, x_8, x_9, x_10, x_11, x_220, x_13, x_14);
return x_221;
}
}
case 11:
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_222 = lean_ctor_get(x_1, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_1, 1);
lean_inc(x_223);
x_224 = lean_ctor_get(x_1, 2);
lean_inc(x_224);
lean_dec(x_1);
x_225 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(x_2, x_3, x_4, x_5, x_224, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_225) == 0)
{
uint8_t x_226; 
x_226 = !lean_is_exclusive(x_225);
if (x_226 == 0)
{
lean_object* x_227; lean_object* x_228; 
x_227 = lean_ctor_get(x_225, 0);
x_228 = l_Lean_Expr_proj___override(x_222, x_223, x_227);
lean_ctor_set(x_225, 0, x_228);
return x_225;
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_229 = lean_ctor_get(x_225, 0);
x_230 = lean_ctor_get(x_225, 1);
lean_inc(x_230);
lean_inc(x_229);
lean_dec(x_225);
x_231 = l_Lean_Expr_proj___override(x_222, x_223, x_229);
x_232 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_232, 0, x_231);
lean_ctor_set(x_232, 1, x_230);
return x_232;
}
}
else
{
uint8_t x_233; 
lean_dec(x_223);
lean_dec(x_222);
x_233 = !lean_is_exclusive(x_225);
if (x_233 == 0)
{
return x_225;
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_234 = lean_ctor_get(x_225, 0);
x_235 = lean_ctor_get(x_225, 1);
lean_inc(x_235);
lean_inc(x_234);
lean_dec(x_225);
x_236 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_236, 0, x_234);
lean_ctor_set(x_236, 1, x_235);
return x_236;
}
}
}
default: 
{
lean_object* x_237; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_237 = l_Lean_Elab_ensureNoRecFn(x_2, x_1, x_10, x_11, x_12, x_13, x_14);
return x_237;
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__11___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__11___rarg(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__12___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__12___rarg(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
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
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_st_ref_get(x_12, x_13);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___lambda__1___closed__1;
x_17 = lean_st_mk_ref(x_16, x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_12);
lean_inc(x_18);
x_20 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(x_1, x_2, x_3, x_4, x_5, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_st_ref_get(x_12, x_22);
lean_dec(x_12);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_st_ref_get(x_18, x_24);
lean_dec(x_18);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
lean_ctor_set(x_25, 0, x_21);
return x_25;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_21);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_18);
lean_dec(x_12);
x_30 = !lean_is_exclusive(x_20);
if (x_30 == 0)
{
return x_20;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_20, 0);
x_32 = lean_ctor_get(x_20, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_20);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
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
uint8_t x_15; lean_object* x_16; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
lean_dec(x_7);
x_39 = lean_st_ref_get(x_13, x_14);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_40, 3);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_ctor_get_uint8(x_41, sizeof(void*)*1);
lean_dec(x_41);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_39, 1);
lean_inc(x_43);
lean_dec(x_39);
x_44 = 0;
x_15 = x_44;
x_16 = x_43;
goto block_38;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_45 = lean_ctor_get(x_39, 1);
lean_inc(x_45);
lean_dec(x_39);
lean_inc(x_6);
x_46 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_tryCoe___spec__2(x_6, x_8, x_9, x_10, x_11, x_12, x_13, x_45);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_unbox(x_47);
lean_dec(x_47);
x_15 = x_49;
x_16 = x_48;
goto block_38;
}
block_38:
{
if (x_15 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_6);
x_17 = lean_box(0);
x_18 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___lambda__1(x_1, x_2, x_3, x_4, x_5, x_17, x_8, x_9, x_10, x_11, x_12, x_13, x_16);
return x_18;
}
else
{
lean_object* x_19; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_4);
x_19 = lean_infer_type(x_4, x_10, x_11, x_12, x_13, x_16);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_4);
x_22 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_22, 0, x_4);
x_23 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__5___lambda__2___closed__6;
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___lambda__2___closed__2;
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_27, 0, x_20);
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_23);
x_30 = l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_tryCoe___spec__1(x_6, x_29, x_8, x_9, x_10, x_11, x_12, x_13, x_21);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___lambda__1(x_1, x_2, x_3, x_4, x_5, x_31, x_8, x_9, x_10, x_11, x_12, x_13, x_32);
lean_dec(x_31);
return x_33;
}
else
{
uint8_t x_34; 
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
x_34 = !lean_is_exclusive(x_19);
if (x_34 == 0)
{
return x_19;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_19, 0);
x_36 = lean_ctor_get(x_19, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_19);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("definition", 10);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__2;
x_2 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("wf", 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__4;
x_2 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("replaceRecApps:", 15);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_13 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__6;
x_28 = lean_st_ref_get(x_11, x_12);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_29, 3);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_ctor_get_uint8(x_30, sizeof(void*)*1);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
lean_dec(x_28);
x_33 = 0;
x_14 = x_33;
x_15 = x_32;
goto block_27;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
lean_dec(x_28);
x_35 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_tryCoe___spec__2(x_13, x_6, x_7, x_8, x_9, x_10, x_11, x_34);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_unbox(x_36);
lean_dec(x_36);
x_14 = x_38;
x_15 = x_37;
goto block_27;
}
block_27:
{
if (x_14 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_box(0);
x_17 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___lambda__2(x_1, x_2, x_3, x_4, x_5, x_13, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_15);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_inc(x_5);
x_18 = l_Lean_indentExpr(x_5);
x_19 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__8;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__5___lambda__2___closed__6;
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_tryCoe___spec__1(x_13, x_22, x_6, x_7, x_8, x_9, x_10, x_11, x_15);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___lambda__2(x_1, x_2, x_3, x_4, x_5, x_13, x_24, x_6, x_7, x_8, x_9, x_10, x_11, x_25);
return x_26;
}
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
x_16 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__5;
x_17 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_16);
x_18 = l_Lean_Expr_replaceFVar(x_12, x_2, x_17);
lean_dec(x_17);
lean_dec(x_12);
x_19 = l_Lean_Meta_mkArrow(x_18, x_4, x_7, x_8, x_9, x_10, x_11);
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
x_46 = l_Lean_Meta_mkArrow(x_45, x_4, x_7, x_8, x_9, x_10, x_11);
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
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; lean_object* x_50; 
x_40 = lean_array_get_size(x_7);
x_41 = lean_unsigned_to_nat(0u);
x_42 = lean_nat_dec_lt(x_41, x_40);
lean_dec(x_40);
x_43 = lean_array_get_size(x_7);
x_44 = lean_unsigned_to_nat(1u);
lean_inc(x_7);
x_45 = l_Array_toSubarray___rarg(x_7, x_44, x_43);
x_46 = l_Array_ofSubarray___rarg(x_45);
x_47 = 0;
x_48 = 1;
x_49 = 1;
x_50 = l_Lean_Meta_mkLambdaFVars(x_46, x_8, x_47, x_48, x_49, x_11, x_12, x_13, x_14, x_15);
if (x_42 == 0)
{
lean_dec(x_7);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__5;
x_54 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_53);
x_16 = x_54;
x_17 = x_51;
x_18 = x_52;
goto block_39;
}
else
{
uint8_t x_55; 
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
x_55 = !lean_is_exclusive(x_50);
if (x_55 == 0)
{
return x_50;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_50, 0);
x_57 = lean_ctor_get(x_50, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_50);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_50, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_50, 1);
lean_inc(x_60);
lean_dec(x_50);
x_61 = lean_array_fget(x_7, x_41);
lean_dec(x_7);
x_16 = x_61;
x_17 = x_59;
x_18 = x_60;
goto block_39;
}
else
{
uint8_t x_62; 
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
x_62 = !lean_is_exclusive(x_50);
if (x_62 == 0)
{
return x_50;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_50, 0);
x_64 = lean_ctor_get(x_50, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_50);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
block_39:
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
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; 
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
x_34 = l_Lean_Meta_withLocalDecl___at_Lean_Elab_Term_withAuxDecl___spec__3___rarg(x_31, x_33, x_30, x_32, x_9, x_10, x_11, x_12, x_13, x_14, x_28);
return x_34;
}
else
{
uint8_t x_35; 
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
x_35 = !lean_is_exclusive(x_26);
if (x_35 == 0)
{
return x_26;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_26, 0);
x_37 = lean_ctor_get(x_26, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_26);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("casesOn", 7);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__2;
x_2 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("inl", 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__2;
x_2 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("inr", 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__2;
x_2 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__9() {
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
uint8_t x_12; 
x_12 = l_Lean_Expr_isFVar(x_1);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_apply_10(x_4, x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__4;
x_15 = lean_unsigned_to_nat(6u);
x_16 = l_Lean_Expr_isAppOfArity(x_3, x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_apply_10(x_4, x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_18 = lean_unsigned_to_nat(0u);
x_19 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_3, x_18);
x_20 = lean_unsigned_to_nat(3u);
x_21 = lean_nat_sub(x_19, x_20);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_sub(x_21, x_22);
lean_dec(x_21);
lean_inc(x_3);
x_24 = l_Lean_Expr_getRevArg_x21(x_3, x_23);
x_25 = lean_expr_eqv(x_24, x_1);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_19);
x_26 = lean_apply_10(x_4, x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_unsigned_to_nat(4u);
x_28 = lean_nat_sub(x_19, x_27);
x_29 = lean_nat_sub(x_28, x_22);
lean_dec(x_28);
lean_inc(x_3);
x_30 = l_Lean_Expr_getRevArg_x21(x_3, x_29);
x_31 = l_Lean_Expr_isLambda(x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_19);
x_32 = lean_apply_10(x_4, x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_33 = lean_unsigned_to_nat(5u);
x_34 = lean_nat_sub(x_19, x_33);
x_35 = lean_nat_sub(x_34, x_22);
lean_dec(x_34);
lean_inc(x_3);
x_36 = l_Lean_Expr_getRevArg_x21(x_3, x_35);
x_37 = l_Lean_Expr_isLambda(x_36);
lean_dec(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_19);
x_38 = lean_apply_10(x_4, x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_39 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1;
lean_inc(x_19);
x_40 = lean_mk_array(x_19, x_39);
x_41 = lean_nat_sub(x_19, x_22);
lean_dec(x_19);
x_42 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_3, x_40, x_41);
x_43 = lean_array_get_size(x_42);
x_44 = lean_nat_dec_lt(x_18, x_43);
x_45 = lean_nat_dec_lt(x_22, x_43);
lean_inc(x_2);
x_46 = l_Lean_Expr_fvarId_x21(x_2);
lean_inc(x_7);
x_47 = l_Lean_Meta_getLocalDecl(x_46, x_7, x_8, x_9, x_10, x_11);
if (x_44 == 0)
{
lean_object* x_161; lean_object* x_162; 
x_161 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__5;
x_162 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_161);
x_48 = x_162;
goto block_160;
}
else
{
lean_object* x_163; 
x_163 = lean_array_fget(x_42, x_18);
x_48 = x_163;
goto block_160;
}
block_160:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
if (x_45 == 0)
{
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_145 = lean_ctor_get(x_47, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_47, 1);
lean_inc(x_146);
lean_dec(x_47);
x_147 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__5;
x_148 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_147);
x_49 = x_148;
x_50 = x_145;
x_51 = x_146;
goto block_144;
}
else
{
uint8_t x_149; 
lean_dec(x_48);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_149 = !lean_is_exclusive(x_47);
if (x_149 == 0)
{
return x_47;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_47, 0);
x_151 = lean_ctor_get(x_47, 1);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_47);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
}
}
else
{
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_47, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_47, 1);
lean_inc(x_154);
lean_dec(x_47);
x_155 = lean_array_fget(x_42, x_22);
x_49 = x_155;
x_50 = x_153;
x_51 = x_154;
goto block_144;
}
else
{
uint8_t x_156; 
lean_dec(x_48);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_156 = !lean_is_exclusive(x_47);
if (x_156 == 0)
{
return x_47;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_157 = lean_ctor_get(x_47, 0);
x_158 = lean_ctor_get(x_47, 1);
lean_inc(x_158);
lean_inc(x_157);
lean_dec(x_47);
x_159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_158);
return x_159;
}
}
}
block_144:
{
lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_unsigned_to_nat(2u);
x_53 = lean_nat_dec_lt(x_52, x_43);
lean_inc(x_1);
lean_inc(x_50);
x_54 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lambda__1___boxed), 11, 2);
lean_closure_set(x_54, 0, x_50);
lean_closure_set(x_54, 1, x_1);
if (x_53 == 0)
{
lean_object* x_141; lean_object* x_142; 
x_141 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__5;
x_142 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_141);
x_55 = x_142;
goto block_140;
}
else
{
lean_object* x_143; 
x_143 = lean_array_fget(x_42, x_52);
x_55 = x_143;
goto block_140;
}
block_140:
{
lean_object* x_56; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_56 = l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___spec__1___rarg(x_55, x_54, x_5, x_6, x_7, x_8, x_9, x_10, x_51);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_ctor_get(x_57, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec(x_57);
x_61 = lean_nat_dec_lt(x_27, x_43);
x_62 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__6;
lean_inc(x_4);
lean_inc(x_1);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
x_63 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lambda__3___boxed), 15, 6);
lean_closure_set(x_63, 0, x_48);
lean_closure_set(x_63, 1, x_49);
lean_closure_set(x_63, 2, x_62);
lean_closure_set(x_63, 3, x_50);
lean_closure_set(x_63, 4, x_1);
lean_closure_set(x_63, 5, x_4);
if (x_61 == 0)
{
lean_object* x_133; lean_object* x_134; 
x_133 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__5;
x_134 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_133);
x_64 = x_134;
goto block_132;
}
else
{
lean_object* x_135; 
x_135 = lean_array_fget(x_42, x_27);
x_64 = x_135;
goto block_132;
}
block_132:
{
lean_object* x_65; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_65 = l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___spec__1___rarg(x_64, x_63, x_5, x_6, x_7, x_8, x_9, x_10, x_58);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_nat_dec_lt(x_33, x_43);
lean_dec(x_43);
x_69 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__8;
lean_inc(x_1);
lean_inc(x_49);
lean_inc(x_48);
x_70 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lambda__3___boxed), 15, 6);
lean_closure_set(x_70, 0, x_48);
lean_closure_set(x_70, 1, x_49);
lean_closure_set(x_70, 2, x_69);
lean_closure_set(x_70, 3, x_50);
lean_closure_set(x_70, 4, x_1);
lean_closure_set(x_70, 5, x_4);
if (x_68 == 0)
{
lean_object* x_125; lean_object* x_126; 
lean_dec(x_42);
x_125 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__5;
x_126 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_125);
x_71 = x_126;
goto block_124;
}
else
{
lean_object* x_127; 
x_127 = lean_array_fget(x_42, x_33);
lean_dec(x_42);
x_71 = x_127;
goto block_124;
}
block_124:
{
lean_object* x_72; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_72 = l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___spec__1___rarg(x_71, x_70, x_5, x_6, x_7, x_8, x_9, x_10, x_67);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_48);
x_75 = l_Lean_Meta_getLevel(x_48, x_7, x_8, x_9, x_10, x_74);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
lean_inc(x_49);
x_78 = l_Lean_Meta_getLevel(x_49, x_7, x_8, x_9, x_10, x_77);
if (lean_obj_tag(x_78) == 0)
{
uint8_t x_79; 
x_79 = !lean_is_exclusive(x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_80 = lean_ctor_get(x_78, 0);
x_81 = lean_box(0);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_76);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_60);
lean_ctor_set(x_84, 1, x_83);
x_85 = l_Lean_Expr_const___override(x_14, x_84);
x_86 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__9;
x_87 = lean_array_push(x_86, x_48);
x_88 = lean_array_push(x_87, x_49);
x_89 = lean_array_push(x_88, x_59);
x_90 = lean_array_push(x_89, x_1);
x_91 = lean_array_push(x_90, x_66);
x_92 = lean_array_push(x_91, x_73);
x_93 = lean_array_push(x_92, x_2);
x_94 = l_Lean_mkAppN(x_85, x_93);
lean_ctor_set(x_78, 0, x_94);
return x_78;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_95 = lean_ctor_get(x_78, 0);
x_96 = lean_ctor_get(x_78, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_78);
x_97 = lean_box(0);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_95);
lean_ctor_set(x_98, 1, x_97);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_76);
lean_ctor_set(x_99, 1, x_98);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_60);
lean_ctor_set(x_100, 1, x_99);
x_101 = l_Lean_Expr_const___override(x_14, x_100);
x_102 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__9;
x_103 = lean_array_push(x_102, x_48);
x_104 = lean_array_push(x_103, x_49);
x_105 = lean_array_push(x_104, x_59);
x_106 = lean_array_push(x_105, x_1);
x_107 = lean_array_push(x_106, x_66);
x_108 = lean_array_push(x_107, x_73);
x_109 = lean_array_push(x_108, x_2);
x_110 = l_Lean_mkAppN(x_101, x_109);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_96);
return x_111;
}
}
else
{
uint8_t x_112; 
lean_dec(x_76);
lean_dec(x_73);
lean_dec(x_66);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_2);
lean_dec(x_1);
x_112 = !lean_is_exclusive(x_78);
if (x_112 == 0)
{
return x_78;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_78, 0);
x_114 = lean_ctor_get(x_78, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_78);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
else
{
uint8_t x_116; 
lean_dec(x_73);
lean_dec(x_66);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_116 = !lean_is_exclusive(x_75);
if (x_116 == 0)
{
return x_75;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_75, 0);
x_118 = lean_ctor_get(x_75, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_75);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
}
else
{
uint8_t x_120; 
lean_dec(x_66);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_120 = !lean_is_exclusive(x_72);
if (x_120 == 0)
{
return x_72;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_72, 0);
x_122 = lean_ctor_get(x_72, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_72);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
}
else
{
uint8_t x_128; 
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_128 = !lean_is_exclusive(x_65);
if (x_128 == 0)
{
return x_65;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_65, 0);
x_130 = lean_ctor_get(x_65, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_65);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
}
}
else
{
uint8_t x_136; 
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_136 = !lean_is_exclusive(x_56);
if (x_136 == 0)
{
return x_56;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_56, 0);
x_138 = lean_ctor_get(x_56, 1);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_56);
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
return x_139;
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
x_1 = lean_mk_string_from_bytes("mk", 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; 
x_16 = lean_array_get_size(x_7);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_lt(x_17, x_16);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_dec_lt(x_19, x_16);
lean_dec(x_16);
x_21 = lean_array_get_size(x_7);
x_22 = lean_unsigned_to_nat(2u);
lean_inc(x_7);
x_23 = l_Array_toSubarray___rarg(x_7, x_22, x_21);
x_24 = l_Array_ofSubarray___rarg(x_23);
x_25 = 0;
x_26 = 1;
x_27 = 1;
x_28 = l_Lean_Meta_mkLambdaFVars(x_24, x_8, x_25, x_26, x_27, x_11, x_12, x_13, x_14, x_15);
if (x_18 == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__5;
x_75 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_74);
x_29 = x_75;
goto block_73;
}
else
{
lean_object* x_76; 
x_76 = lean_array_fget(x_7, x_17);
x_29 = x_76;
goto block_73;
}
block_73:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
if (x_20 == 0)
{
lean_dec(x_7);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_28, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_28, 1);
lean_inc(x_59);
lean_dec(x_28);
x_60 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__5;
x_61 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_60);
x_30 = x_61;
x_31 = x_58;
x_32 = x_59;
goto block_57;
}
else
{
uint8_t x_62; 
lean_dec(x_29);
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
x_62 = !lean_is_exclusive(x_28);
if (x_62 == 0)
{
return x_28;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_28, 0);
x_64 = lean_ctor_get(x_28, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_28);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_28, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_28, 1);
lean_inc(x_67);
lean_dec(x_28);
x_68 = lean_array_fget(x_7, x_19);
lean_dec(x_7);
x_30 = x_68;
x_31 = x_66;
x_32 = x_67;
goto block_57;
}
else
{
uint8_t x_69; 
lean_dec(x_29);
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
x_69 = !lean_is_exclusive(x_28);
if (x_69 == 0)
{
return x_28;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_28, 0);
x_71 = lean_ctor_get(x_28, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_28);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
block_57:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_33 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lambda__2___closed__1;
x_34 = l_Lean_Name_str___override(x_1, x_33);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_2);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_3);
lean_inc(x_29);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_29);
lean_inc(x_30);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_30);
x_39 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lambda__2___closed__2;
x_40 = lean_array_push(x_39, x_35);
x_41 = lean_array_push(x_40, x_36);
x_42 = lean_array_push(x_41, x_37);
x_43 = lean_array_push(x_42, x_38);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_44 = l_Lean_Meta_mkAppOptM(x_34, x_43, x_11, x_12, x_13, x_14, x_32);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l_Lean_LocalDecl_type(x_4);
x_48 = l_Lean_Expr_replaceFVar(x_47, x_5, x_45);
lean_dec(x_45);
lean_dec(x_47);
x_49 = l_Lean_LocalDecl_userName(x_4);
x_50 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lambda__1), 12, 4);
lean_closure_set(x_50, 0, x_30);
lean_closure_set(x_50, 1, x_31);
lean_closure_set(x_50, 2, x_6);
lean_closure_set(x_50, 3, x_29);
x_51 = 0;
x_52 = l_Lean_Meta_withLocalDecl___at_Lean_Elab_Term_withAuxDecl___spec__3___rarg(x_49, x_51, x_48, x_50, x_9, x_10, x_11, x_12, x_13, x_14, x_46);
return x_52;
}
else
{
uint8_t x_53; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
x_53 = !lean_is_exclusive(x_44);
if (x_53 == 0)
{
return x_44;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_44, 0);
x_55 = lean_ctor_get(x_44, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_44);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
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
x_1 = lean_mk_string_from_bytes("PSigma", 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__2;
x_2 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Elab.PreDefinition.WF.Fix", 30);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_private.Lean.Elab.PreDefinition.WF.Fix.0.Lean.Elab.WF.processPSigmaCasesOn", 75);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unreachable code has been reached", 33);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__4;
x_2 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__5;
x_3 = lean_unsigned_to_nat(147u);
x_4 = lean_unsigned_to_nat(49u);
x_5 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__6;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__8() {
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
uint8_t x_12; 
x_12 = l_Lean_Expr_isFVar(x_1);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_1);
x_13 = lean_apply_9(x_4, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__3;
x_15 = lean_unsigned_to_nat(5u);
x_16 = l_Lean_Expr_isAppOfArity(x_3, x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_1);
x_17 = lean_apply_9(x_4, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_18 = lean_unsigned_to_nat(0u);
x_19 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_3, x_18);
x_20 = lean_unsigned_to_nat(3u);
x_21 = lean_nat_sub(x_19, x_20);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_sub(x_21, x_22);
lean_dec(x_21);
lean_inc(x_3);
x_24 = l_Lean_Expr_getRevArg_x21(x_3, x_23);
x_25 = lean_expr_eqv(x_24, x_1);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_19);
lean_dec(x_1);
x_26 = lean_apply_9(x_4, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_unsigned_to_nat(4u);
x_28 = lean_nat_sub(x_19, x_27);
x_29 = lean_nat_sub(x_28, x_22);
lean_dec(x_28);
lean_inc(x_3);
x_30 = l_Lean_Expr_getRevArg_x21(x_3, x_29);
x_31 = l_Lean_Expr_isLambda(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_30);
lean_dec(x_19);
lean_dec(x_1);
x_32 = lean_apply_9(x_4, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_32;
}
else
{
lean_object* x_33; uint8_t x_34; 
x_33 = l_Lean_Expr_bindingBody_x21(x_30);
lean_dec(x_30);
x_34 = l_Lean_Expr_isLambda(x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec(x_19);
lean_dec(x_1);
x_35 = lean_apply_9(x_4, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1;
lean_inc(x_19);
x_37 = lean_mk_array(x_19, x_36);
x_38 = lean_nat_sub(x_19, x_22);
lean_dec(x_19);
lean_inc(x_3);
x_39 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_3, x_37, x_38);
x_40 = l_Lean_Expr_getAppFn(x_3);
lean_dec(x_3);
x_41 = l_Lean_Expr_constLevels_x21(x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_39);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_42 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__7;
x_43 = l_panic___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___spec__1(x_42, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_45 = x_41;
} else {
 lean_dec_ref(x_41);
 x_45 = lean_box(0);
}
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_45);
lean_dec(x_39);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_46 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__7;
x_47 = l_panic___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___spec__1(x_46, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_47;
}
else
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_44, 1);
lean_inc(x_48);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_39);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_49 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__7;
x_50 = l_panic___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___spec__1(x_49, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_50;
}
else
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; 
x_52 = lean_ctor_get(x_44, 0);
lean_inc(x_52);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_53 = x_44;
} else {
 lean_dec_ref(x_44);
 x_53 = lean_box(0);
}
x_54 = lean_ctor_get(x_48, 0);
lean_inc(x_54);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_55 = x_48;
} else {
 lean_dec_ref(x_48);
 x_55 = lean_box(0);
}
x_56 = lean_array_get_size(x_39);
x_57 = lean_nat_dec_lt(x_18, x_56);
x_58 = lean_nat_dec_lt(x_22, x_56);
lean_inc(x_2);
x_59 = l_Lean_Expr_fvarId_x21(x_2);
if (x_57 == 0)
{
lean_object* x_169; lean_object* x_170; 
x_169 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__5;
x_170 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_169);
x_60 = x_170;
goto block_168;
}
else
{
lean_object* x_171; 
x_171 = lean_array_fget(x_39, x_18);
x_60 = x_171;
goto block_168;
}
block_168:
{
lean_object* x_61; 
if (x_58 == 0)
{
lean_object* x_165; lean_object* x_166; 
x_165 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__5;
x_166 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_165);
x_61 = x_166;
goto block_164;
}
else
{
lean_object* x_167; 
x_167 = lean_array_fget(x_39, x_22);
x_61 = x_167;
goto block_164;
}
block_164:
{
lean_object* x_62; 
lean_inc(x_7);
x_62 = l_Lean_Meta_getLocalDecl(x_59, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = lean_unsigned_to_nat(2u);
x_66 = lean_nat_dec_lt(x_65, x_56);
lean_inc(x_1);
lean_inc(x_63);
x_67 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lambda__1___boxed), 11, 2);
lean_closure_set(x_67, 0, x_63);
lean_closure_set(x_67, 1, x_1);
if (x_66 == 0)
{
lean_object* x_157; lean_object* x_158; 
x_157 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__5;
x_158 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_157);
x_68 = x_158;
goto block_156;
}
else
{
lean_object* x_159; 
x_159 = lean_array_fget(x_39, x_65);
x_68 = x_159;
goto block_156;
}
block_156:
{
lean_object* x_69; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_69 = l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___spec__1___rarg(x_68, x_67, x_5, x_6, x_7, x_8, x_9, x_10, x_64);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_ctor_get(x_70, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
lean_dec(x_70);
x_74 = lean_nat_dec_lt(x_27, x_56);
lean_dec(x_56);
x_75 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__2;
lean_inc(x_1);
lean_inc(x_61);
lean_inc(x_60);
x_76 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lambda__2___boxed), 15, 6);
lean_closure_set(x_76, 0, x_75);
lean_closure_set(x_76, 1, x_60);
lean_closure_set(x_76, 2, x_61);
lean_closure_set(x_76, 3, x_63);
lean_closure_set(x_76, 4, x_1);
lean_closure_set(x_76, 5, x_4);
if (x_74 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_39);
x_77 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__5;
x_78 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_77);
x_79 = l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___spec__1___rarg(x_78, x_76, x_5, x_6, x_7, x_8, x_9, x_10, x_71);
if (lean_obj_tag(x_79) == 0)
{
uint8_t x_80; 
x_80 = !lean_is_exclusive(x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_81 = lean_ctor_get(x_79, 0);
x_82 = lean_box(0);
if (lean_is_scalar(x_55)) {
 x_83 = lean_alloc_ctor(1, 2, 0);
} else {
 x_83 = x_55;
}
lean_ctor_set(x_83, 0, x_54);
lean_ctor_set(x_83, 1, x_82);
if (lean_is_scalar(x_53)) {
 x_84 = lean_alloc_ctor(1, 2, 0);
} else {
 x_84 = x_53;
}
lean_ctor_set(x_84, 0, x_52);
lean_ctor_set(x_84, 1, x_83);
if (lean_is_scalar(x_45)) {
 x_85 = lean_alloc_ctor(1, 2, 0);
} else {
 x_85 = x_45;
}
lean_ctor_set(x_85, 0, x_73);
lean_ctor_set(x_85, 1, x_84);
x_86 = l_Lean_Expr_const___override(x_14, x_85);
x_87 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__8;
x_88 = lean_array_push(x_87, x_60);
x_89 = lean_array_push(x_88, x_61);
x_90 = lean_array_push(x_89, x_72);
x_91 = lean_array_push(x_90, x_1);
x_92 = lean_array_push(x_91, x_81);
x_93 = lean_array_push(x_92, x_2);
x_94 = l_Lean_mkAppN(x_86, x_93);
lean_ctor_set(x_79, 0, x_94);
return x_79;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_95 = lean_ctor_get(x_79, 0);
x_96 = lean_ctor_get(x_79, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_79);
x_97 = lean_box(0);
if (lean_is_scalar(x_55)) {
 x_98 = lean_alloc_ctor(1, 2, 0);
} else {
 x_98 = x_55;
}
lean_ctor_set(x_98, 0, x_54);
lean_ctor_set(x_98, 1, x_97);
if (lean_is_scalar(x_53)) {
 x_99 = lean_alloc_ctor(1, 2, 0);
} else {
 x_99 = x_53;
}
lean_ctor_set(x_99, 0, x_52);
lean_ctor_set(x_99, 1, x_98);
if (lean_is_scalar(x_45)) {
 x_100 = lean_alloc_ctor(1, 2, 0);
} else {
 x_100 = x_45;
}
lean_ctor_set(x_100, 0, x_73);
lean_ctor_set(x_100, 1, x_99);
x_101 = l_Lean_Expr_const___override(x_14, x_100);
x_102 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__8;
x_103 = lean_array_push(x_102, x_60);
x_104 = lean_array_push(x_103, x_61);
x_105 = lean_array_push(x_104, x_72);
x_106 = lean_array_push(x_105, x_1);
x_107 = lean_array_push(x_106, x_95);
x_108 = lean_array_push(x_107, x_2);
x_109 = l_Lean_mkAppN(x_101, x_108);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_96);
return x_110;
}
}
else
{
uint8_t x_111; 
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_45);
lean_dec(x_2);
lean_dec(x_1);
x_111 = !lean_is_exclusive(x_79);
if (x_111 == 0)
{
return x_79;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_79, 0);
x_113 = lean_ctor_get(x_79, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_79);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
}
}
else
{
lean_object* x_115; lean_object* x_116; 
x_115 = lean_array_fget(x_39, x_27);
lean_dec(x_39);
x_116 = l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___spec__1___rarg(x_115, x_76, x_5, x_6, x_7, x_8, x_9, x_10, x_71);
if (lean_obj_tag(x_116) == 0)
{
uint8_t x_117; 
x_117 = !lean_is_exclusive(x_116);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_118 = lean_ctor_get(x_116, 0);
x_119 = lean_box(0);
if (lean_is_scalar(x_55)) {
 x_120 = lean_alloc_ctor(1, 2, 0);
} else {
 x_120 = x_55;
}
lean_ctor_set(x_120, 0, x_54);
lean_ctor_set(x_120, 1, x_119);
if (lean_is_scalar(x_53)) {
 x_121 = lean_alloc_ctor(1, 2, 0);
} else {
 x_121 = x_53;
}
lean_ctor_set(x_121, 0, x_52);
lean_ctor_set(x_121, 1, x_120);
if (lean_is_scalar(x_45)) {
 x_122 = lean_alloc_ctor(1, 2, 0);
} else {
 x_122 = x_45;
}
lean_ctor_set(x_122, 0, x_73);
lean_ctor_set(x_122, 1, x_121);
x_123 = l_Lean_Expr_const___override(x_14, x_122);
x_124 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__8;
x_125 = lean_array_push(x_124, x_60);
x_126 = lean_array_push(x_125, x_61);
x_127 = lean_array_push(x_126, x_72);
x_128 = lean_array_push(x_127, x_1);
x_129 = lean_array_push(x_128, x_118);
x_130 = lean_array_push(x_129, x_2);
x_131 = l_Lean_mkAppN(x_123, x_130);
lean_ctor_set(x_116, 0, x_131);
return x_116;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_132 = lean_ctor_get(x_116, 0);
x_133 = lean_ctor_get(x_116, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_116);
x_134 = lean_box(0);
if (lean_is_scalar(x_55)) {
 x_135 = lean_alloc_ctor(1, 2, 0);
} else {
 x_135 = x_55;
}
lean_ctor_set(x_135, 0, x_54);
lean_ctor_set(x_135, 1, x_134);
if (lean_is_scalar(x_53)) {
 x_136 = lean_alloc_ctor(1, 2, 0);
} else {
 x_136 = x_53;
}
lean_ctor_set(x_136, 0, x_52);
lean_ctor_set(x_136, 1, x_135);
if (lean_is_scalar(x_45)) {
 x_137 = lean_alloc_ctor(1, 2, 0);
} else {
 x_137 = x_45;
}
lean_ctor_set(x_137, 0, x_73);
lean_ctor_set(x_137, 1, x_136);
x_138 = l_Lean_Expr_const___override(x_14, x_137);
x_139 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__8;
x_140 = lean_array_push(x_139, x_60);
x_141 = lean_array_push(x_140, x_61);
x_142 = lean_array_push(x_141, x_72);
x_143 = lean_array_push(x_142, x_1);
x_144 = lean_array_push(x_143, x_132);
x_145 = lean_array_push(x_144, x_2);
x_146 = l_Lean_mkAppN(x_138, x_145);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_133);
return x_147;
}
}
else
{
uint8_t x_148; 
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_45);
lean_dec(x_2);
lean_dec(x_1);
x_148 = !lean_is_exclusive(x_116);
if (x_148 == 0)
{
return x_116;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_116, 0);
x_150 = lean_ctor_get(x_116, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_116);
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
uint8_t x_152; 
lean_dec(x_63);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_45);
lean_dec(x_39);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_152 = !lean_is_exclusive(x_69);
if (x_152 == 0)
{
return x_69;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_69, 0);
x_154 = lean_ctor_get(x_69, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_69);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
}
}
}
else
{
uint8_t x_160; 
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_45);
lean_dec(x_39);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_160 = !lean_is_exclusive(x_62);
if (x_160 == 0)
{
return x_62;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_161 = lean_ctor_get(x_62, 0);
x_162 = lean_ctor_get(x_62, 1);
lean_inc(x_162);
lean_inc(x_161);
lean_dec(x_62);
x_163 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_163, 0, x_161);
lean_ctor_set(x_163, 1, x_162);
return x_163;
}
}
}
}
}
else
{
lean_object* x_172; lean_object* x_173; 
lean_dec(x_51);
lean_dec(x_48);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_39);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_172 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__7;
x_173 = l_panic___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___spec__1(x_172, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_173;
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
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_4);
return x_16;
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_WF_mkFix___lambda__1___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkFix___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("fix", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkFix___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_WF_mkFix___lambda__1___closed__4;
x_2 = l_Lean_Elab_WF_mkFix___lambda__1___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_78 = lean_array_get_size(x_2);
x_79 = lean_unsigned_to_nat(0u);
x_80 = lean_nat_dec_lt(x_79, x_78);
lean_dec(x_78);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
x_81 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__5;
x_82 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_81);
x_11 = x_82;
goto block_77;
}
else
{
lean_object* x_83; 
x_83 = lean_array_fget(x_2, x_79);
x_11 = x_83;
goto block_77;
}
block_77:
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
x_21 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lambda__1___closed__4;
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
x_35 = l_Lean_Meta_getLocalDecl(x_34, x_6, x_7, x_8, x_9, x_28);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = l_Lean_LocalDecl_userName(x_37);
lean_dec(x_37);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_19);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_16);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_Elab_WF_mkFix___lambda__1___closed__6;
x_43 = l_Lean_Expr_const___override(x_42, x_41);
x_44 = l_Lean_mkApp4(x_43, x_13, x_27, x_31, x_33);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_38);
lean_ctor_set(x_35, 0, x_45);
return x_35;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_46 = lean_ctor_get(x_35, 0);
x_47 = lean_ctor_get(x_35, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_35);
x_48 = l_Lean_LocalDecl_userName(x_46);
lean_dec(x_46);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_19);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_16);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Lean_Elab_WF_mkFix___lambda__1___closed__6;
x_53 = l_Lean_Expr_const___override(x_52, x_51);
x_54 = l_Lean_mkApp4(x_53, x_13, x_27, x_31, x_33);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_48);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_47);
return x_56;
}
}
else
{
uint8_t x_57; 
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_27);
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_13);
x_57 = !lean_is_exclusive(x_35);
if (x_57 == 0)
{
return x_35;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_35, 0);
x_59 = lean_ctor_get(x_35, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_35);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_26);
if (x_61 == 0)
{
return x_26;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_26, 0);
x_63 = lean_ctor_get(x_26, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_26);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_18);
if (x_65 == 0)
{
return x_18;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_18, 0);
x_67 = lean_ctor_get(x_18, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_18);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_15);
if (x_69 == 0)
{
return x_15;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_15, 0);
x_71 = lean_ctor_get(x_15, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_15);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_73 = !lean_is_exclusive(x_12);
if (x_73 == 0)
{
return x_12;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_12, 0);
x_75 = lean_ctor_get(x_12, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_12);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
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
x_83 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__5;
x_84 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_83);
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
x_35 = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__5;
x_36 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_35);
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
x_19 = l_Lean_Meta_forallBoundedTelescope___at_Lean_Elab_Term_addAutoBoundImplicits_x27___spec__2___rarg(x_15, x_18, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_16);
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
x_33 = l_Lean_Meta_forallBoundedTelescope___at_Lean_Elab_Term_addAutoBoundImplicits_x27___spec__2___rarg(x_30, x_32, x_31, x_5, x_6, x_7, x_8, x_9, x_10, x_29);
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
l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lambda__1___closed__4 = _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lambda__1___closed__4();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lambda__1___closed__4);
l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___closed__1 = _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___closed__1);
l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1 = _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1);
l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__2 = _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__2);
l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__3 = _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__3();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__3);
l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4 = _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4);
l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__5 = _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__5();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__5);
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
l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__7 = _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__7();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__7);
l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__8 = _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__8();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__8);
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
l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__9 = _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__9();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__9);
l_panic___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___spec__1___closed__1 = _init_l_panic___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___spec__1___closed__1();
lean_mark_persistent(l_panic___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___spec__1___closed__1);
l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lambda__2___closed__1 = _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lambda__2___closed__1);
l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lambda__2___closed__2 = _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lambda__2___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lambda__2___closed__2);
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
l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__7 = _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__7();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__7);
l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__8 = _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__8();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__8);
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
l_Lean_Elab_WF_mkFix___lambda__1___closed__6 = _init_l_Lean_Elab_WF_mkFix___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Elab_WF_mkFix___lambda__1___closed__6);
l_Lean_Elab_WF_mkFix___closed__1 = _init_l_Lean_Elab_WF_mkFix___closed__1();
lean_mark_persistent(l_Lean_Elab_WF_mkFix___closed__1);
l_Lean_Elab_WF_mkFix___closed__2 = _init_l_Lean_Elab_WF_mkFix___closed__2();
lean_mark_persistent(l_Lean_Elab_WF_mkFix___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
